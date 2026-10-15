-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5518
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:07:47.98868+00:00
-- url     : https://prove2.me/submissions/1e6bfc84-3f90-405a-9001-a0119ff849f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 992266187 ≤ n < 992446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 992267437 1250 992266187 992266211
    0x60e030403030909270302030705100204051509280f03030305100e160503100f080319020a110906120313050f03010605010806042c03070209060913150e10 68
    0x200f03032000b401940f1020300804001c4002081e07042d000006404003072641c0310203103041500800c11030714910303130202c240c6000d480136202d004000c0d00988070329030040d40040f03001103503444620308550708200d000300b40342c0c0380f001e003800d041c00341440c40003400d103d2a1070301c003020640800e00c030f0703001d0010340c0300795070115051401d00c10000400d0020f500c80c5901915240c03c0c00700548081c1c186045529441c5800d070f40340e0f40e601220181550150380400c11101c0d40c171802060740003000c8005d00f00110a0200702c0402840382000b00e0f65401d0111001d0300545004001100614240c0e0403d03403c4a0000e06024002000c2d504090441d0f1160380301814990440c0010401c0b400c1600c0c104002003800c0f402005200c3c50000068502000200603501c6180c0d0341c40460164400203445650083c02c0342e42c48143ea40b039003a030300ba80e02c3c0c1c0088020303480340040d00d000074694900090840d100e0a013802c06801144065580c00b5061031500300194030060b2038403120815a1010807940c0030030a035200d00803c82c132403000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 992268687 1250 992267437 992267447
    0xf03060f040c09060503030702121015050f0a0302211c0512090616050d0204080d08040b0c0f0d05041a070e09090102041a0f0904020715051515090a03060e03040303 72
    0x54001c10301c03181003440401250346c020080e01d24180d019a1520680310481c1141410060740b800c103000c1640c9004401400141c00c080c06006079941524a00003071910041080074680e0706200082d07107c40706052805092110344040700e5401544030449040070200d046c200c0c00b07911043d085500003240030850101004484034040e402162140141140381040e51040c41d1030280110084140007001030410034400d843c0c2d040303500400510341070343c80000f60140000c2c03c080c001d03101510001281004110684440d00c201c810040c04500300d940340031002400c080c05008010010b40301c894441020f12550714034005014403c90b100d9883c0c0700d001d0401000c1013030080001e010a511a84148001c2c030074801210303c801c40718091034200544480403548250058402c10403120b81040c0046101c0d003c1210300c108804911f03003c0740c0e0901c1075076a01e0848820a41d0010245680181e01e05201d81c00801c000000700702e8094080e09050000b5225128103080e01d0450074699115032001a0400a255006d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 992269937 1250 992268687 992268689
    0xa1817010507030b01121a1f11010203070915050d1103011701050c0d0b0a090207121209050601030b0a090b190e0303011a0d0e0d090501030b0402090319020f03060f040c 74
    0x1800c04000c000a0a80002c3c03001b850503005c200110342e140c480711070701e01c228401c42003000401002030a00038101400d802e00d145000d020b0301c0114070341282c1042080018001c1ea4811245030b6034045c0a240b91034041185080c0d4003080c1014000104100c10700c01a842c001d4400d82c1c814a10030320303a40d51500d0b808501908202245060030303403521082c84003180f00503003110142a40b61002154142c1610300003402c0c0750b40d5603c400280351000643e041004405200b446d83c0c0109600d4081c100c0c4c905068000940b8400c940040c91504860014000103041c00b220300c0e001100d1070000503101c0d40300c6c2c1c0d901c00c007540d007500c0c04130304820036600141c4159030700c0c01a800f00040705000b075400d41d49040100c1010381c2506618903401a004901000031003040d60190018818110407103c1c40d02d25060003401040a6000d043d000070b0610300341c0301803410036008940706601d001e001801f01c105c030202441c40107070300400100c3e03110b4140096140995420400c1a005504915000c0c0a9003441d1402520780e54103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 992271187 1250 992269937 992269951
    0x140f030a06030c06090e010e0a23060109120209240d03031506050403020307090b040b040f0c0f02030421050a0f29010e06060a03090b01060e0a08010516050a18170105 73
    0xd20024011b180d2980e030124115906c0c520752403a01d8551502d048094207101da640342e0141c00c2411218113001065184a0190500f030703d0f01e02400703458900d40e0116245000b000fa41210107000070420318040c2c02e0b034039a0360300542881c1600c040e50400004000030520441034000940304c0c18000544428010110010622820031920345032959000c02c1e01d44003144114402c0035940c60601d80992100e800c100d48050000344200001c820700d040131401010401d01840003e00c52211490b80107000000712001d84102c03154120a07604c010042c2d0762a031500e40c0c03003100e40b40620102c400c00502c52111010707881e4031a006e4401c0d0044940003041071f001500c0c0d03200e420030101500400200401c01c81c4030f900207005a40702030b07503844c41c0603041d000703411080802083c040c1007900000e100c541c883c4c0c8003400805c045034490031040c1d48140c81c509031801616100c4402800c3c00d1040601401040244500740342e50900c109801085150040941c81e42c1d0b02403c00c0d45403c001d43c00c0348850a110700f03544242 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 992272437 1250 992271187 992271197
    0x5060f070c0f050c040f0c03050702010c120902010509180916060c0b0c09130c1103070b011401091502030d110304050a02061308100e011805060601140f030a06030c06 73
    0x641050001c0405003140c1c405010909030100410070302405002620300385034044e1080c807501c001400f2000c01000c0401003003002a15001c04180e290782706014411600015540d41481d000102103010000d020300c000c00c90500008110703050b010b40b603d81c05100324084000b803001c41440c00c00d9415080c40344e1022180500406400c040c4a0070342c00401c60070b102c41c2c000040910ba0394a0021000c42882024210380e40110a2004c1180700101e03904030301c00300404d6603075038280e0151859a00340e4078011084000c1c2001007800042c429150304804070740381c1010500d820400659529411000e04800e031011900613000050341c00d042c0d9985018042d1201d464452aa02d50301c0c064556903210218003030700a115000c009120006020080080c07805010040180c4100140d6a1620001491402640301c81542043c1c02c3d401c1501040000c0365002d80c11902811007aa0f440c801181e900b60080c190007952602130143c10701503080100658828600d00e01e0003d034103030550502e401181e100703074030a81c100a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 992273687 1250 992272437 992272441
    0x1107150b1f020601150903050307050f0c062a0102130e0f0f010b090d06020408010c050d0b0d020604060e01051902100e011b030f2706050703050f07050d060b03070c05060f 75
    0x542c001612030444103134a43c0800c44004180084988120710382c4003614501c40825040c0c28000c000c1170025041c0708540840d6a5407000905000741405590310107a80e450070310380d1001b186100c40800d0f0300305008036400103140480b5051480d10701c00c6150403003500c0040000811100c0030049600755000064843d0b08501503250041c0700311035100d44c0480501500d203070045a4200002901a58090f0841600900c6903030240c10008241d9000351649031885420000c0300c1c6424202065141700189d006418540352506040041ea8420710700c0b50401d0401c05c0030802104a400c000b0680d6500703544983c09803120340f801103011030076114000072980c642d03403419001c40b0b400c42160b82002c2c01400305042c0803d6140011007900002c1c15140c40d00c242821409284102044403c0041d45c0c145110b88010170068440c0c1104604580c011545070b19032400290104080a01403000b41c0b034141c2da40d1038003064403512455030007170030f030000d54040001c1140800c824040081c1801070641c070203030f000000b803058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 992274937 1250 992273687 992273749
    0x61b0f0806061b1e010b091602030301061404031b03031805090117160b0301180903020303010504020705031c0c2601050d2d0204180f061107150b 64
    0x503c141c40744500301c4410b00c1c07000c00583e0001d01202c4418800b10300c9801c000507500440901a043c0d040c1440d10038058000064a00c154600780005c903035049070f0055007982e0803d90b041c2d80d0f480d40ca0f09c2c80f9841c000103001c00000112400885070b0381c0c00340480e045c00203d2943c038029190030f900403c1484100e640004c00d1206841c3c0e0750081c0d04481e82c042c2d469946140741c00d0120b00b094400000e80c21790981c0a40007140e004a50001141240c080016090614603200e040074103d550740007004005820810040109180c960040c0c41001c1c040c0d0156442c142c1c003c9940c6c00035110041100e29100e450380c001c41c240a801c0034000b0364104401000f801d0b208881c03900e0042008050003000d00c50750303840c2c802c4014015400d11404041d030400b0f030681c081030845101c001a01580c210124455800c002d00343d5071184030b140d000207400f68071203524010041a81d69032409000c648180c5004e492040c0003000204d054454001100b02c0071140000b2064981018402200c4e0032a501d82062140c0410074401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 992276187 1250 992274937 992274949
    0xf0108130b0619120519030801060305180115030b0a060b070f14060103051c050c0a120e10030209130c0c0605090c12032d16020a03061b0f0806 63
    0x290307902010700d150650300c040c0000e4280e81e20b00c1110001c070600c2c480200d01c4228482a07522614050011650404031148190103014030105000f40000c03150801042141d01907006150018110b21200360041030b83c040c2203003110b02d140150400000c1e031039002c00500001c54140c907006508020f041c00464181880031585101d505d01c0280300820602a22090200c1803648000000743e004c00c5c2ea1155941c0d0401556541e0201400b00c070508800c10709800c518050030484030141135100140204448075240c00411452000441007484080f01500c90550364108024800100a441c01a1030741c565806000b2030000052540c200c480c41c0041d0b80c07203c2c6420140701c0000c02c2d40080c001c50b940d62010040750400030301d4007071550801d103205c1054075a001c010020f800c00329403003d03909490b1a160300c00204003500f00c000401c001c1004000c1d00125011080541503682c1c006003000525641d00e560344001c8902c00040e424080c04003a42c2510300941c4400a050356041610300390280742448000514 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 992277437 1250 992276187 992276221
    0x2040b07020906041b020f12120105060c0109060e0d021207021c1103010204090b040e0d0503072d020f12120115020f010504050d0905030604080717040b13050f0108 72
    0xc03144000000250301580c86030485103181c200141c42c00d011414088001e1f646030f10316104011140200203281c0307494076144090b41d4102001543c02001c0741d1a1a01303226956005010590302e1395211200a03010030a1405000380ac030340c0b140c00800115a031000024141460114111075100003000001c000d681e1744888100c0e28240419a01520400b500d04082034418296425416500200707001884000c107521038104c0c49400c1c1c0b410b000b10a620701100340c52340100507044c2e01044091022610302c034403464902515444440c000700c14100741c0e00e5000d001046003250a00107034083d000308004407900780540706c05240500c01c1207003450f090f00c00c1d15002100500490780200d4408119030a0b480c0b0800c00c051058986000820642c1041e043c5241c45003041040306d030124514003000121800c0c00501c062159070012822824241d140d5201c0300550521a507408100b4810b0001041d1620035030018660301c034462003203402d21491301042c8400092403148440c10302651804011000640c0601c1c58 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 992278687 1250 992277437 992277439
    0x3090a260f030f0f04080d0309200a0303030b04020d06030c0302010f02070e0408250b100501111218090f0405060f010510030b0105040b0403080909090105160c020a0b070506160302040b0702 83
    0x962680c8203120759204034021503001d00b945107d024021125541c059102070281e41c0240c26484041425070611000140d2030030407142c01540f01c88040000c07038840d5104007c0440d0060001d032918440c3d0b04a01300b95229070f0005e03109503205090800071903820880c02c410b40407180c0040e241141c900103041d034002000400c0504440d00001d0040d5980500f042440d281402d81204004900c4050070020402c0c81c0446500040a48150022909600079810003c115000c03000400152074480180391880d04114104802c50060101d6810300d5641c400082d403103100c078154583d05034946810800d05d050405009007402c0e500003001400240c0b2681104071706802c441c20301040c001d40100048510388134552040b4114080420040200680c100007031134039903401c903000e0065840f042c86c980e007243d8003650102c0b08040c1e4010070920490080e041e506000e400149400000b995800144207079034030902040b25a41c1090042100ea40905e0740001c0181009140071030a0904201e6084e4461144400103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 992279937 1250 992278687 992278717
    0x5030613170a140a1206050604080307170c0d0c03020601060e0a1203090503060a140c03102304020f0408011a01140f13030f03080109050f01051203090a260f03 70
    0x114a400f4081c503100c0c0b0040204200c1d69980c4c0c021058001c00b10440c80204000d11420301e0380001c2c1c2881c00c0c00645003550801c40203146425000d07a9103c9840d00d5003202c0401405003449604400c017001d01c110401c20000343c03500010307000b00d49002420040d05030458000e2003d15200495241c40b003510601c01d86010081400d60046203040a540312403007070307115a81c180300744d508010130120f03203400a2a0381e48810080701c0050b1030340c1107500b103640400c031000400c0c100e030840d0400c0004104a08000c10403018a64002c1241404003c0360030b07648600c4550400603070001302000845070901c60108080c1544c840000441e020000081c0610800501007100000110300da44021141310116104444a500d80065440d40c0380307080400540301d00410340c0405c14005c000160780e14140507a51283c0310b010364110080c2e0900040003220031404910010500c028005403410703850300d250326006881100d0700d002100b1103250302120010408601e01249401001c4403400d020000416500301c2d228080c61 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 992281187 1250 992279937 992279947
    0x240108070510020f010c0216172e02042310020c2718011103010308190c08030f220f0204180c1707060f02100c03020903010c090503061317 61
    0xf2841c110030801c598106500e04030551a82c0ca4001074440700c06846140c0d05032405940c2c003012440300c440c0040000b59500032441c04442008030f00305031030500040c0951318041c02113008984049030066000344588080c000844240312241c8448800a54802c5480c0b800360703d90008001d4603030440755800c500543c009101c2c4620a0360b80681100011a2090500c803145851801015a01941e0080c241c5139446d00700d010303c0805006040700d06881d0841d04181c640760740700c0411a020b038900c007010000c01c1480000c3d00e000a8040000714007882d210140d8450074100000710416020590402c00301d0c440201c0307140c200140d08a1900442d45030111030025856090f213801c0401c62180000c0246065070b0448042200c3e14181c5c0c609230b0f4080138901b03c42c495921200291a4080d00485141c0541c0c0b0600300c100000803d40c101464107419854054103040c040408603007501e198500c88000f00f8a08001070049003810403c0c0d80e80000302d8101c01c0001c03161600d5503c130003021560b0340c518590300092 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 992282437 1250 992281187 992281219
    0x70f0804051002070b0f011e44010c0201290607080f0c010b2202090d060f0207050c0a0b04030f0618060b0f090c0d0c120e2401080705 59
    0x225201c40070520300e40c155031350300716441c1c80b20551a0458450a0030f003941c2002151000c045040c0c0c00c40b2058603010018001c0c18042e05c81c09862100303441e00c0041c04007038845031450382e07003800c0f80e8040141e81c2c0c0e007400340e0805c40610360700303440402e00034000b1685001d5500d81a603007180c0744040071540681072078803641280004a0b0051003018000741c1544000109040401091360013481d00c811408020031075901c1d201c081001c5600580e80301c008105c0780d115070390346088456000700108840103255000001143e078a6a0550f000505030682403940400e602c4c060203800c3c0024085c45108603545102c25051a8103980785014900028150844c2c0d80d8614040109c1540306812400c00c0060ba0400f1041503d8101d024002d014007550240d009100800c140c1e00348201c1d154090620340710141d0078108410521001041350003c0c000810400b5502c10303338000011702c10a420b40c40c800e401380c540704048070384c1808402001c600c0712600b07400d0103004002c4004080b404109403075080322101c1d410081c110b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 992283687 1250 992282437 992282443
    0x3060503030a051e120a3315081e0903040f0909140a050c04050603030d06031506050303160210121515050a020619090b010605040914070f080405 64
    0x6004690944000180040c50581007800307404a03801415180ca20840d0442c40452039009050503006030244071004100072103c2038105641c503141101008079140d240003014481039820064805201070308140c14000da80300b190140e0b250074040c0c02c01154038102007040303200000301202200849202800071078002881402110000c201e404a049503903911aa8803500500040200300e42d580480c1a103041900e01c04a0344001142c1c2000c09000e00e6440c810901016110007811b0702e41c14001003119040c2d400c42403140748091801a2100b15507a1078500781c50302140c03070070342020340309a0003030200b400c651290450180c800395043d519030324060b000300c0e0240c0300c6043c2c0c4403003650010b0505803545101e2000d0581c0700b04541d64454003201400961405403201e01c5165075507001a0011400901e018080d0104049078281041000070044c0e5030361211480751500b07810010018200040c10015417100d07018076182a6480071039a030050401030360141c105440300c40b81401b800800e20001d001c0c45428 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 992284937 1250 992283687 992283689
    0x15180905030f1c1a01081603110f13050f0a0b0d06030602070b10090b0a050d0503090a030b250e01110c0a090603030815010f11070812040305010f140a0c0306 69
    0x75060162610822000007180045090700c3c0000b20349030a440c04c0e03080500480490b40000181c480d06003d0b10ba1410071040d8002d52501c400a16455010b00707a01d0120b40e200401103482c160214681303600b400d01d5840d210004a45c040c91080d4502060417005507508920360b0304450f4010007140d9030319440c1d4541406003882394009045c82d4400709500c0148130110304e6052040d0060100e040d445501c0360b032201c0484503040f400d04c0d08804051010302c65404d08400444007140184c08a900b40040c0300001007005a0503042110102025405d109941c004d00314980c0c1d410954880c04005004e0450005040600e8a00344904000349544416944034003030080c4090385001401c2d030114540c9407410391000e8030b003e220481c005680c800c0040d4101200489001c240321050303540c502a1450311000302d44000d110b000e074071018081c40c500010000800c003c048840c41c1030a00d40d548a03803850800ba030031a030389045140041418030644643c6041686070341ca0b44400c801d50000348040106d1030031070040140d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 992286187 1250 992284937 992284957
    0x308070f0c17030f100b09010e28030309080a03051207120c050a0212040e010501051c05040614090a020f060a0504030b090c19060807030504020d050a0303050a1518090503 75
    0x298482c603030b00390820180110b00c00d080854107038549480796203945a0041e500e1040300080401400414015889200d81104c9244020045100a03024401d160140048004e91440e003000740075041007019003200801d0014180d01e006008145c0c02510090114821556034502c442d4a840018901c00e01605000040c0496450104400340070040040c126500c02d0900030007504ca100c4906000403844402c4809030b4405903c08503460b442c080040d205034100c516000c05413100981c80855408061040c42d100301d00400c004500c016100c8128450118080c10101041d04007a07280f0b005600d40c1140080e10110075a4840c0c1d6840d03000e6000c440e240a00e800080c00344800c0f105202034000000740c0d06c405020115103140c2014803e4466441900c00d900c20440452600300000345030754026071046502500140c1400340070100c03951070304e080c200d1120045000c41e5458080c400c40c00d11070b2007860003820070460000d2046050982e08860a1811481c52500e02d48900040c000c0110500c01d6428802d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 992287437 1250 992286187 992286203
    0x10f0e06040b04061e1b0801080a0f110a0803130f0501090b031303051b010e2b1119050a030908010e030d0e01020c0105040305071202032503110d0c020f0d0308070f0c 73
    0x210300461b08410040c110400c41c0050701d040008141c0c100081340c48241030303a019400d0016052075175561115071083c14030240d1b001400030340000308400240020455044904c0910010908103c1c020140844a803c40780c10020280014404507070200202c03030700201c5540c0764030800d00d00b502d002c81e818403a41b001411480c0c80080c40025440054018403102c00b0480190350f012055181c0c000c1c66201143c0200c1c600071031101880009078050f07140ba40384c0841180a95080f16005078003040045a0820200c0301544403041141c141a4002c40761405090824001d0180c501001e00039a540e009100d0009282e0307076541d000f040d907100c0c2541100d00d60f00d15080240b0207464281405000303a00715500c04d603480d0b804031204201c042d10220031911030450610300e07110300c400e202c440180368012441c000c0381030240c40039013582d000f0020040781400b07000301d5640780480c50652050280e018030300d00410b4050003c1e48821030000b03400104043e480952498503488160005d9001c03101ba014000024000e41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 992288687 1250 992287437 992287451
    0x51902130302040b06030606120c0c150901050912090f0406080d0206060913022b0c0b090a060c0203072c010305060f011203080601030c050405030f010f0e06040b04061e 74
    0x1548100301030382140e00803102041101040d00030321200344000c80d03e8542c0075504010200004c541d41c0555070b08450045005802c4c07a0b0740e240494a040b00600301d09060f800340c07108118003440e090094a40c04040b110141410850300c0d00d1001c2540200007007144100c0d0300d400103c08945880d480f0720001c0c400c02c8119008500d0410010307489540503900207001303010380000140e0890966008151160340540501041c0c80a06801020056451001c00c100e41d1407481c403e020810842007a00034001c00c89580360b9400c06a001c20107200c200d540403074140404c00305200d006da900440c2000442da50000c80d00401450340040c415104681840000710740000b90010082c0728001880700d2003014900b941c0c0c446642c0741c4110341c1c0d11011b0208010300241041c1c002440e0341d4405e4200319061a16820014101501c510000c2e023000038070010005076a640351342040c1a44118042d10030746c100800003520042c1000e4881c1741c2c8e46480100040c00c51600c0e01c1c0d685c680c0340c204002001801c040a0020860304d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 992289937 1250 992288687 992288707
    0x150402040909020f0d05100b0d150608070510051207020307080a051c09120f05091210050a021201030f0503130605030a0506150921030f03180d0e04051902 68
    0x10000700b02c0603806001049600c800504001188030742175604240184079054806d0a0140545040c02d04990004080d548080c001445e401c46c0e04a4a00c00d06008900e15061000b1507240018a0340003a101d170195901c9a105d03690003a00f21001c401540c98003500a65030318034203900e1486110802000c0e040001001e9202d03540c044094007a605c4030746110300b41070891410203c10750b440e111018100820141e0003e00182c000d507070309202ea91341303410f11905089181c1c00103080403030300c0d540080c43e17600209281c00283d00340e4894554450000d40c5d04508007542a901000740e84414080104083c1c0c0da40b488209025040050f95140400310315422451601d034040148035420503a0000074032401e040c0403440529002c0b0201103910541c042813800d08988208000400d464640203c529075584a41202e00900900c005e2000307500411829981b802d117040c10600d076503014002c01d0b009400c500d04240340c0ca5800705407100f51100480d004035045d11142001084080c0702401c6a00322440000c10f1940 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 992291187 1250 992289937 992289941
    0x150411040f0807140406140618150703030b060315010c06060b0313030f1d060708070203010203131b0f090e03091f0f0c021507081c09060605030f0d081504020409 71
    0x166052141d103c82a250384c0c6041c0401c1d104035001f2454a04481c1c0e80100c5681411f1000d88910080751030410420418400487c1324000600e4212100050014000c2c092640601445801c003505136490362941c50001003a542140813503e4550400008022510a0022941040020341010320910750b4905256000e4606840307038a2084010070142c0d4402581c20b402241540c0d682075042c021069210006410000f2503804803900310341d10303003041c0460805600d0034400786201d040229540c410003046404c2201080564046200c4440d907442424080c007814501040b00b1034000344004202581c156400e039003140074880c0c0c4c40d0782161610f4058030f10003910740f106007800303a101d844d2186505005942112458200c007400ba402c207a0302c100c402c0c2c00f494060028180381d0b02030340d590f44c2403986403090800b550281016120700540c40c3d003c2401070040c1449400001c0c00f0450081031a0000281000d4660000c041510240035500c070000750b840207658038140d030f00c04008004641d82d9440303c0320400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 992292437 1250 992291187 992291189
    0x1d2701050906060a092003071b2a030f1707020d03091701020f071b18050a050f06010c020f040b0a0e0108011b1211090d1415150411040f0807 62
    0x4884e0074565030024010f4400c1c46100383e0040306d03000f2940c42001d820848a6146e0002c1d08079000c01c000149541c500c3c011070012162000c1c45109071003a0300c803018071300d082a080d02c8820340119080c2c030f600400008540e20000300c0e085a108030242d401d000005c0ba00c041501480d000071707410a02c803907080e000300766202d1140740944041203c42c0d000200c0812a1500701e02624626032001e0900b000001e01107042c02c11055686085c02c90701c04c0034991030310385403241e14a007800610710701d036211410310041314154040c8650140300c001340116a480d00707800090080d0a00301d03019024061404420100341c440740c10460031401c000d400500290b0b95050f00707411620f800d215a8245510344111141694900000f41c900303076203a035680c41005448402c44400a100304001103048507810094000a501ca181840e030886001d1160105840f1048000b030341055408100c424940d0811810841900400108409201401c1d100040c8005403444503101501c595004000031010b014070014182c180029480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 992293687 1250 992292437 992292439
    0x40f0605070b31020a1706250e010e042901111203010e0702011806090311060f0c1c090503071704050a09271101091d270105090606 58
    0x40c0e00703a40c0c41070243c94100000000d20200f0080c010079000041c8864411050240010000c001c002d5696043c0c960030403071400d2061264029404214200c0c1400d0183c2d098440b030701c03800340d4003a140114010044c210400c02e840c140041c5241c1c01c096038a0b503500010f01250b140b402016100030b4480b00680c5010401c40b6103001442501d10b4a03840e00001c60350401c41046004000e06603403c180d807841440d003005102008640d0f81cbc44000100041c00401185418090007000910603500d08006040410985000340c40e54031200500600b81c0c005191158010f059215041d280c00500a90b0394051521104d0b0742d02490900c42c06030300340140030006100b1284500031480701c4044030140450075028900c1000ea0103100000200001000c58002540c0c05d0030300c8040b110203994007010321030841c400c1c0c5d9041d80c440d2250b0004001e5540c1000150000e86018100c84014241400c1c0400c10140002d000d003004000800303601090b03400800061205100d520001c3c0f000303103441c02c24203640300d008550706 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 992294937 1250 992293687 992293703
    0x60605091e0603070c030c05151b0c1e151806070c1104200a17070509210c0603041101030609022701090503150603070510051806040f060507 62
    0x8048510200012045540142c603942c15039540138426034122007448021b400b4085407c1d074070030000781d00307101511150710703c0140045142080b03a9070105608200c2120000d1359420800341e100c4040008500c01c4003002d49094100344040b5140ca18144000c2e611002c4614083d5818011200c201c1d080d00381002c44480110352840c0d6911100315410110903802070040f84900b00b03a407415081c540c21481d40200083b82500300100c883c00d805415900910701c02c0300080c2d411034080509c20402c0b012039080f040b9807070180d040060201c0000c071500d584054201c007600a480516580341c40070b002c1010200001003540c0c2d00c0340740c5404c1502041400c440706500080c0380000c04200c0071418800e03141d4a560000104910711a61039081e03506591a0342203506100c1d4400c0005015541048207140240c00c180382141181410b00c1810315228aa4014520075140380c0c05820f42c0d05d0b4020161401d46182640d41c40300c0007a0740011803080d2190350000318000e80074807800306156810030001c014461041400c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 992296187 1250 992294937 992294959
    0x130b1c02160803060d120302030f0105090702190c170729040311010207090c0302040602153303010603060207030f080105060d0f140a0e120c19140106060509 69
    0x1010100c1c40751424221000481c40e01540c0440c400c900515031207140a019064201c500751100184020001c400e0000641c00004220078445504100c600400f81918032046904046c1d2010b910780c5d04100740402100c40140302c58040c81710000c86440140260704d1f204140d480c102c3c160540303d64083c01484031032244c0004000344038407810190003800d0b0420780c40509017411503546c89841f85440304100d04511459002188083c07007403042d40e520880984005075a2844c118010b41004001c001000081280404000d8140d00b01c41210820107100954204e102001c40d55149505204e5800b690b055884d03c0b00200800146170700a2140500035213511940010041c0222030b0302500340241b41d005881803080c2c030001440360b000301c0509641040045a1101c2180d4540e0064008803950000e29880381180749901d039081c0400301c0c840b0b20031101c02e4580508454165074170758511110441a0b03080d601c0070400d01071015648903c0340c0803e030080c801a540e601c0014202e42012091920814403801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 992297437 1250 992296187 992296237
    0xb0103050705092202130b100801090b090402151e070501090c050f0a0603050705070204020c010b1f0f1818061404020711090414070e070806060307081902130b 70
    0x850b48074550303030031541642400081d41c24045018a5111013545454031451803804a640705526200b8800d00342c9c3d140340140d890301179040c094030304402c44d01c2d02801c00300c0c1c14840540c49401c9400d10912100f856107560b43c400451010504d803584c58003124008000c03039140100801908003e00c681c1c05615100e030300a840d2410801941066006a548407410400401c0814000d411803039000d0b40074101542084250740104040e60320100d40245282d658220416162804c2e012a00d450954000740e0000340c1021800980319204c2590035200f40100030090146002c01c8403a64005042e000d0074290168600b01e480c88040e16040c0644048402214180400d0382080c1c820358080540000003410003c1145060141a8501030030568100710400b009817403250007002004020200440010703904d103411680204000030140c4a07600c28001001803046641e03002400c250000550150100c0c0801c0181d020b000a2003008a20040b04510340d030001180c2000c5c0c000313032a54011110700700050001c061 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 992298687 1250 992297437 992297461
    0x8090a1e0e0708062101020a17012c1b07080a031b02100e03070c06080703050f0c0409051314250e0f0a060308030406021c060b0a18030b010305070509 66
    0x11600c00010f00f029002030550314000342d92044005038002101c1042e54074600f80c0e8260f0b03000708107200104881450449620b80d0f04240321b03004041c22030124414440482c2a13000345482c20f134600d01c603a4948400718401c000360740e00c0c50f098440c03c040ea45503241c4c0b40c0c1c644045143c001007040404a450300448100004002c40340c0e200d00051980a80034207404d41c89404010181441e005001d44004c0c070003000000c840540c6c0d64080c16042d00d07a00784502e000b03280182511f1006107200d814025140a00501c404104160360640c0c101020100c0c1964030441e0b03194071120f01c100301505d042803101c440700604030003040210000ca22203030116040740524124040c042c8461003020700b43c4071030b400040c489816501c03800780c100b000340710080369882c0d8a07107400885410036a42524110390005a0241c540d90040080e43d040b0340085051180c60316040c3c0e0070410f8041c03000000180542444001c1d2010f0310710a200c0080c540c4134844892715612820040d940b10440d0080e01c1c0101c0b04640804d80d403121708 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 992299937 1250 992298687 992298691
    0x23070e1513031704030b0c09010906110115090c023912030703080a06090b010903030f030e01060807050102010507020318103b0f0a1208090a1e0e 64
    0x14010030840c0ca203203a00a40c0e103034858460304401c207607900d40100000da44626070060000b15a0000340d1224194185403840100c05002c41403e00d2040002c90302c542d0b00300d10070604407440360510740700e140f009101d01c40c00340042003045048015a07a0020405507010b0f0702031142e0070403070350884c0c8402114a140f0840398224020000010812550060030844003003c6c01c0d405100182c402d840c03105010700e5441c6960480301080700031402c071600f002200411481402c00610640500703016049084001910706021400080c0030045004843d44081d070003a040741200c40360700c5c0000c001c4a55a5907c1d04e40f0351003940102c0340107501301404204c0d0a44000183c6003081400c40b03490b0012407041040041c002c5032001c1d030034240103c403014112103081d55440d405076030401c1198030900129104030300e1210341c06c03041000d01c210380314004c0c0d0b0603640781c000b03110b801da070f171000510428a411400c1c00742d502c0c0a540711166010381e02c0c00012400c110480d908072075070425080e0395201d40d41c464004d00100320003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 992301187 1250 992299937 992299939
    0xc02160f0e040c05060a030606080c0f030f06030f12030103061427120705150c0c0706030b150f0706050c070b06040203040f05010e03040518011a13050423070e 70
    0x182040c00700e40d2001220030b030803900c00c0e210b403801a55900301283c8560422048900400c5c0c1d2080200100340d002003000390301c031055001692800c0010412640c1c10b01018241c003080c100e400c0700180490310b0802491a1401e411400c640d10301e144607103454007a5109020468029091120481d505031100e0749a80c01030010f00f180718448a001d0900b4041ca08650000a20a2081001e002c44c006a52401000305501803c040c01e00362000321300e14a0b1802d80a041581704140400c2045c3c60940041b03100020780e040d9103004110000c500d000038840002c160b2400f1100c500004200300040491001414810300c01c0707109110550358814051054055110003621400049000502a01e8150f00075a032040c420a0f1000b55800b254840c2800c5030750803a5a010a03030320019040c841880d15040e0b030079100400304c001030600d41c100711001411a1550b2400500d4140c0807688403010861244440f0180c41d010b04200140001e007400200d0b18810f112021210514a401040702c2d035204800c1d1002e4124 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 992302437 1250 992301187 992301209
    0xc0f030503041206020909010e0a0b0906030607110a0206030106080f131101050a0c0b0c0301140d022b06110a1218110a05040e010b0a0e1006120b030303040302010c0216 74
    0x442c2280c401a181140f070000c0b600903608001c016035980c0c1d14020280a0a14103154036000d03c2c040c00403104888030900d00b6445020981700b040059607001981c0d59100307040d4503222510710000c810591500303c40c034030025440301001c400031032803075400b5006900c104408500504103807103c0029000c402c19108000c0c20980f40c841c07441c0d2695000ba00102003040344c2e8644401809001d840c0c280e0b10105c20703594110307036001c0000100004c191061550000d54402c59407607000200d141d000036219500600c0e0252840030324018a00d50040343d880c803008443c1c10420600200d50b00004c0014658080c01c8680b022036144c1c100070b2075105182c4110844c4500c076500b40902c142c0c43d5180c5d0741d44011818449580401c1d07030035022400d900c0300e02640c1000300701070002051030640030b010030607451807540012400200c40c004200e881d50030721800c1d00c21243d15080407a000d1030004850f00140006440c1150144400400e12042642c158007104a9441a03401e0310b101c000c80c0041381d070400984e48900c42d000b813 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 992303687 1250 992302437 992302439
    0x30903030513080a060e0615030303041e020a0f06120c0e0f0301020d060305030310050d080d0e030405040507110d08060105040521010507090f0b190c140304120c0f03050304 76
    0x307018030010042c0740720381c0c0c826040d0300d5a545250351410300342950031103e9640301c04413605c810804021494015501c03480c911703d000c4035803000c03944e00d0000030400b4041c06041d0900c00b10030341000000551950b00a094540308503191060112190103a20a00e0002000046e0000704c0892900c204900c800140d6a4000c50030b84000030002082010801c40d40d0555080003e5400300d00d00f8400d00f0015489070004d103883e45000d14900c3c1c900f440c29031202d801502405c0904d00003646180403210b8a50b9200c100064101e240300c4001d00d03500554200a8100c7c1c0b514051000d45034000c010000d200d00b054084134071500581c1001c588140d4182c40382408104144018002d07031400c100e071504000ca00300751680e440c5405020090a580e800da58800204241d884180010520081d003200a801f0400070a490701d4840c2040c007174112400b0078003104200d05803071071600304600c5807800c3d0005003130101140d4413191035090720105d58020b14400c842010500030000b6014860244560489030003801950038a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 992304937 1250 992303687 992303693
    0x307020604050405070e030105070210060503030a0228120804050105160819020c0316022404030f14071403010617060c1c0203130209151e06071505041a0103030903 72
    0x2c2c10000c3d22500901101d502006c8040c0c80034441d02c4c5c400d14440e8000c1c0802d030311560303102c01220000d030440d40c0240c1082041114858001030480c500450b9500c42c12200c010b0f48050f05080c03018040000c1c1402c041007410000c940e4041c08150145011700002c0210751200720000c03d2200642115a002c01c00903030010f00b880700b00d66400340c1e806810790030161900036014003541c110346c00701410b0b06c0c01e00320300d042c59015401c000c0e002c00002140724800e001c15031646135004517103008900c03005080f0700000d14180104a00d140c07500e81d86a50440031240c0442d00c50302c52200650243e00b42ca0702961038900001604484501d00c140d681003040060003498071600d00072201c6910081044030b000070340fa50180c5104c0c1081c03004520481d2082e9a0241c03440c1c5900c1042115900504000600380701c00484100310340e502d0041601d12010380303000300c800b030143d60f000ca09180250003018150034074a0390310340c04030394050300320600c9940710724040c0211042e507038000000b460007804080c0016007105018000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 992306187 1250 992304937 992304941
    0x1b1309200c060429160e0a140d0602070602030709093c09021206010e0711031c06050319020a12050a080915030106032a1715090c03070206010803070206040504 70
    0x5580c11032000f024410a281c4e0715007040d502981c0345d0124108200c0f216061941c81507548109407821244640c40c50320340010150103d480c25071061180c04020356a00c10010194103d032200c50b03200c032082d5280d00e4519409000c0c03d209100710800d4500304044200210211040c1950b0001c00c0d40022807000310410307a40034124a80b18000c00b000d0307644c2980f40051395600303020150041040005003255810554108001100900b0741e17070a12603001e8003030341050740102c1601d240c00b2490b0070704450032518180c0c5801420403a030285426015846102d0100032600d40021282030080d02d02d103000e20388d50544501840a00940985143c1202180b071000818000082001c03090080c60f46003d80e01c0d403001c0c80c815900a0b03101001007940c1c0d5505010819400e102c04074240364040c81c4441494100c0307806003a00703484440d0712201d04240b038002401d0902d048686c040710000274100c135100d8500f0821500580c0d2080e00d105015200748800019004800021100300d01d40c06004281800c2c07801c028800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 992307437 1250 992306187 992306213
    0x9060e0a05040e0304150c0c03030f020a1506140604050114181305061f050306060c0102040e010914010e1e0a0b03010c050904060b121b1309200c0604 66
    0xd4404410540000d9540c0c0318000d80c0d0415560101440c0c0d10351402c14075240d40c2e40410b2081c030521101500306008100441460021a9010709100f900b880c1d90f00012403d08110b47c40081042c681e42c21501c013090044d62114040d50a807100c0e600d501d003a080100895401144034440c00200d640e8454000c02005070060b103810700d400b0a0080130301c5284400101030118803c00c40d200d081e03541007000480d00d0101c031440007400201a8840200d18082801420fa200003442035029100026400094034402d50413280200543c8901064030350b1904042c1c2c010b411402109400707034020400118201ca52160380c14020102d1030005c502744c4c0098110300104940040020000945d200322001c2141c90030b000d0486101d116588103991280d1050400040f1540ea41160b030b80301509100d00980d100a480e070290b0089007aa07484070101042c0f2950180302c4c49620400344042070b0100780020344000c00e4010500030302850014001ca60100380c070f41500ba0050000112441d0b0121300410b01041c0030141040f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 992308687 1250 992307437 992307439
    0xe0d180803070b100504090c0312090e0c0a02061f18090807150e0c0d02040f0912030504050c060a0c0609020f0d0c0f1202090a0c021006090b03071509060e 68
    0x54166684226a40c29a044840e065038034150a2040205007a100303441c50300504422641040b03212101d440760592100d59000040103003811941c0302c00a00e001c1c1000c0b50003442440040030540c54200403088241d04071083c4100988204e2000c281800c07071451400005000020513228058648002c1465060011400301c401c2c560342c804000101791140c0c000d2421138000c00c0d40b00c1c102c210030100e00f000c44202016481050700200c150510542d592468161115012900410340124035001200140300d50b0a0051004203000300701500c0360b416030821031013035000700e0654000300d03480e2090203403a110300300381b402c0054280100c0c440024540d91090b110310b400640840148000d0301d01140105c4401082030706e1a180300030003000420602828080a4a81808040e17000e43c0940e0100701035020191001003100c2d1118100305082e4070800010702400c218030024444299196620401040c021000b80d0090080384e001003070a11141031788441d001050340e240e00d4002e14100d401c0380c500300030030003903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 992309937 1250 992308687 992308727
    0x1051e030417040603050603150105060901050c10020307080708060103050103171b030a0903141b090c07020d0b01150f0f050a090305010e010c09060809070302040b1210050106120e0d 80
    0xb062042d0390b0100a00090000754500080509040b03040628011560103c1020284e0040051065460b0f09085c0d6040c0c000030701345a40c4908488005034148601c0c504801d90070740c804001c018905900c542174074011187c03611005165203c2032300440035603000f4040907150b00400400b00c403408141c8401081d421011504401c02d400c0b04e00708440c00c40d4402000c035030006519903c24030070b00ca400f4014103000081d1034010179002c0e0003041240c4184100c000038038811030110001404802c0b8140842d012107a0040c000c002c01c0c18146000300f038980c02809269071020031001da808005004403022807408125480303076003003034441d400e04443e590b01566a030300400c440500d0000015400b401507240c180c001100205c2c0d00180c82000910403182030380280708003c0701c5001c4c040c0b008130120380c401c15a0340540d408603040c0c43e4400480c4550100324040800b5120b07020108c1038048481d07000906070788460341d6034045c507801c640c040307003e444070303c40050240d230400035000c00024040c82030520210600c0100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 992311187 1250 992309937 992309963
    0x70312110a0b01151202040e07180f090515060a0c11010c020a150206071803020d11090405010c030506030a0503192106060f090602060a0f110715050601051e0304 71
    0x1070604a80b80c20b90003169440184114483c40540064a00004100003441181007a01e4440714100e801c0028100c070041c008402c204800f80e070b102c05d0712640504042c0500300b0f041940d43d814840204402c9599455180030124410641c1c907003030048908000079a600c04c0c0f03541e00a030b1a02200072246004e980e06001a0840200c01a00c0d1260a10000c1c008445051080912240d010707042850045c10f110070000004842103218910051540035617030107032642108034085261440000144030601544150a5000c1008220054120040c03001440d5004e05c0291200000d0540d58003000c5401022500140043d4480010b0300b00c248820410610b403101d4040c0000507403100c0403003642040d41c0c5a1f600c1e40c000348146500700444844140240c038100d00d07440d1800b20000d442c3c40d0080c24070402d484d04d880c030b00c01d02d0320840d4011044128803003000a5545429250000c01e45c0e07080ca054514107401c240c0094540c0d030052003070700c0e801000c2100c0d42d000044881184a803541c03004204464100303003119 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 992312437 1250 992311187 992311193
    0x405010f03240b0c06071404095013020f0a030204090c140609060a031d0f0f1b0d03050a03020c010c0309051903050904020f0c0f0a0b09070312110a 65
    0x101d05401416500e0300c50b5550303c2c20000440c10b0000080080d4180582044107100c0344111800310303411683c03070140c0010000d405250411400925801a9030407410f10a400b40410408a0401006038840d4007112043e12b400b61482d490325000b15040001d043c29000400054106072100c01702011004081400340d40d201d900003401c07030b501c00c4002d03249601c00100500001402d400482e1003c87c040354003900b008002e030000703180c80c41f1f80100201056202c4c2030104003d401c4103503028115400c0d2094981da100105041070fa01c094031025440b451240d40040c2d0800b001d0f03e03110140e04200a880400306842c142c40076a0181c1c4290340580c101030382001441603506007880352103414441d55a012a070316601c2c2c10040c0c80c05000300817030a407039000c000c90b0000007500b00301140c0d60188103035005038844e2001da881c0c1300c10b4001c820b00041c1c00d0041d110007120600001c84d0018036a0b202e40c01d07c007129166501110354450003800010000340801c2c001c0400c450242c800026a80c180300115080c030038080d6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 992313687 1250 992312437 992312501
    0x60f07060207110306010b0708030720070303021f0e07031b0b07061b031503021c0b010801060f15171503011517240603070305120307140405010f03 65
    0x1c00070b032160340f004840040d2501d01030002c20300400d415102e00c0e044c0020b680780d030340552001070300020902072119006601d00003520f60b6061a00790400076600300035034a00700030751104440604030510010f40c41d02e690442c441c0380700e10300408000000400842c0e0171350741d030090b44aa00802d100c008280207400002e000c00320b1801000c07894807403140803e022a5069403051030f2845402030b0020b00d41440c04a20600c00e91b080c012044070f404a503021f02c00c90701d00081040036000950301a2000002d0700000c507151005420003011100d48002e03120403c0e82c0c808401e05998590944080002c1108114140d102da040e400603130002060708100c0c140f4072240d0006030031115034030007900000340e4050f001c01c0014034005043da0181c0780c05000d4a0060101480000205c4000001c16030050900d800b042481c1c40410444010b0350341300003140c0c2e503403801c482e05655680040303400701e000410080030f00213200c07510720030f80342182c4041e183c231880c1c0160901c064006d0124640303640c1c4068180c00d00e0b102e01031906 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 992314937 1250 992313687 992313697
    0x4120302070536071719020a0207030215040608070806040b0d120f0504120204050903070c0e151008130614131401022a0a170c2406060f070602 63
    0x802c124002c4409032458440f075500b40c5070316600303c020541007044112a00140511403800c1007103809016940c131816680358960b81100182c681520224001c17070141d4000500c0002d6a0003198111403909a010f81d00e0102e20480c0140e00c00206014040344225000e000426041180100042107100c4d04101150b441000c3ca0410340d4092069031b98030785c001e42c2014000c842c1e078440e46400c0c1c1c41c00f81010600c5043d10040407000380110341e6040080c1d003200c8184141c07121643d0000c22903021554492080420801c166880418600810045142494200c924164070303100740e2280340059550003200b02101e84450001d46446840742080c0c9044820001c0c0c00d4441c802800c00880850424184800400c4010403001c084c0da03c10060805802500e0700c081015245e4591001da1042e43d490381c0711705107070030b486006101c44200f1096070238620000c0041e00940d91070030308540301c12024102c0b0018071026914204c5d003152440c404594941040340050469200a0030541c0c07520b401c50382c0340c0c0c00303d81c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 992316187 1250 992314937 992314969
    0x50316260d0b01021b060f07020a0b0403030f0c022436040e0604060209150304051b0108100315090c0f06020d08040317060a0b1824041203020705 64
    0x80040c001500907120310540c1d0007500c080c40101080b200c09001141c8510001411510a81001c00c0d00000030028904961041c4d80c00341091a13855901d07405240d0300e8005000883c04a4103010032031100512408600200a8006150300008005880d0080a8180c125142042e84908100341ca16181c0410502180d80314821200c40444854544200000c40081a9a446030b03082407003400f0720000000d0340f9600b150300b111005982d0035a01c0c0001d881242003000e99031440c034001c0100700c2486400309194101011a40300300c1c00400040004450040c6c0881304684070b81d410403810720120701c0b1003005480052143d030300059954520b803a1300301d500f49a544484d1420981c12810306c610340c3d043c4628102d640050030611080c2c103065601400e05500c806401c003510010100017102c0340d840c2e450400080c41c540c50010396400400103004440501c505086000340600d0510f140100034a007107a110ba201c508101a08050901c00b00c060300c0b05941074180c0462242050118540c3c2d50442c1c039446d1018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 992317437 1250 992316187 992316263
    0xe060a11010e1b10020a0809010207050d0b09010506040603120305190608010608071203080c0d0605060f0a1107060c0807020f0910061806081611061005030601050607050316 76
    0xf10610400500d50040d1084600500000025481181e0000f40c1c1108180d80684956114030000300103c0c5042003547c4003640c0440004809414442100c1c2054000d2400100921483d518802403105941c1188030040c54180c16a00040f0003603c40d511640d044828044040081c401e185100c1c405c0d2441c2d03800179280c41e5915002009201c0003008004002e06480c0e441501210b140e45014041500080007078100280016064402c3d40166110030f01400e030050000b500d4104c6c2171401e201035080402c074900814a446084d403aaa400028044201e440581d201700122440d5a08c0007807039001305108980126040c00d00303c98658a4115192280410703880d9064083d01c4c24400902e042e038401300b903070340c4c0400c414800c0c8041644592141da10a06410700404100c0701240100da14001041d07003080701d4010982071000b0b031840c1c00703501310485074100e04840460b40c890003042400d1252401c0246182c0c000c00441d030400d003810801c41c0790680155041c404480f117003909003401107030500100324815 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 992318687 1250 992317437 992317453
    0x906110c1c05040302011d0306010b0405120f0c01030c030e07090b1305010f050105163228050703051506090703050603121c020d06050406150e060a11010e 68
    0x1820030400400d07401c1c80c984240003141e035010030280c6140b149000282c108426503905200d0f09132816225418440042c088411a42e0f482d03100b82c1140c0c101e40121485000d441014000c00307500000d10715544a802c40213402c00c04003400040d0002c04200c46498141a100c0080c0c4c4071000c0240491402410501c2e030200b007013414101001407661014182d581424500001030003440c540f00e400200750b44003800e04a5446900035500050500b00410050128841c0705c255004500808030070303102001061440c0c0f00325001085880d071150710b100140320030300d00084a4030702200500c85042c500700d4000c07420b0318042512500d6807410030b8004420581811064003c0c011103040c410304c082d42c8800740c1c1c682004503081a00001e52241c0f400c00d104408038001042d145000c2558a0504140c00d0640ca01103644e1000b46a1440180c580323032040381d101c5e5103007003c002500c030414940d100f26a41a070780c840b068118000c0c01c200e0300c0d4000203031602c10082014a0072030f5201003480345512004086000340711034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 992319937 1250 992318687 992318707
    0x40302010206072303040809030f0a0b0a0e061303030209060f0a0914060a030510080a240e0303070c03031413020306070e10050304022709060a0c0c060f090611 70
    0x101c180540301408110341c3c0032118404e4901a180e50700700d403180110083c2d51b6125400d0501d41c9002e201c641682c140904640c203109410000b54202d406441380310324007040e90703601c2c0303028003103c00700c0700c0c24001c680255000441c115651304400301014464103005041054110220f10b00da0480d1004078440580040d0340d504103904000b03850000c2160381103043c0e2440f211004150702e406504452030034540c864010076400e020b007001d50f8015100310801c480c2d8005281c01c2c103842c00584880381c002843c9040340240c0c5041c0d804c1c042d4260400c0c03000011440d588850000f180c1e10080d0070415801c141c1e985a100450310080c041d128011404e11415480b0420680101800c0c060702808100038070200f04a10080c94507801880f6005e0989401c107030340c0b030795541e00110361411180b0103140421900302841c0c0a07010f03041c2402030b010300d07035120071100144d55018071282100c0e04207444030041500601280c000a0300c94101e20014190320a011881224554440b81a1180941d030441103800200341640c0c0c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 992321187 1250 992319937 992319943
    0xf0506130b060f0403120e040b01140d0e01151d0124020f0114060f09070923060a03230103080f03180d020c15040b03040809060408160f17060a0f060f0b0403020102 72
    0x84208201c8d4108401c204920001c0c1803812100c90744205100f0115210840000079030002d6040c0c107100c0001c3c043c003070494820351074207401030003840c100d60802c2e10421603c013940301166043e030700315200742c480031a03020115103001c603451ba5034002140300d200c00310f0174811028061904030b01065990020941003800c2000810048410118045d10b030100c20818444e50011642c0c04903071041c00d034440c10700031a44800320102c042c400c640703800c01c4001a80d280d0b555496070141320301e86015101d66104820380d11032100c4030a82844060080801440195102c0803a00000c0d6080100350310142d583c3c000d841405ca09201100a0410141e001b0061402442c10700302001e5140321841d4800744e01d01403c003140030388c440c007000c0c001815207140807861054684800084501a148240482d420594030301403041501919009542d0021100b0744009031805910700c0e03c101c102c070100007034019035a403410814014581ba14107000303001e480f0680002d00192442000c2d003c0e0440364015030340d03035045000280ca = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 992322437 1250 992321187 992321207
    0x30f07090b0909030c0c040c0215010e0403180f0608180a030f030c020f121e222c0919050601031e08120c1b01020702040f0506130b060f040312 63
    0x500d6400c00c0081e201404000b01c1d900c06d051004440006642c1558101213103403e400800c13038202000070a0001c40d04410400c00c2e948901d2080d5900c01785400d100801d040c0b80ca01c5845038001c1080c00e4181402414000d0b50440d51003006c0321103259404407000e0080c0d01d401002d24041d0007186040f0103c81e50640d160160320800e0070035000400c45119101903580c1d507403162045500000c480809d90f44415442412054070000c0460700c000d4450440720020403801d03850342e5001800703040c4100005100251064601044901c40c941d002c444000d008010a41d54130040c0800c9680c000c0c4822518810580e8900c141c00341d000300c004040340d604619000d0a000510218098603810105022001a0030001280d0810025403078102d05501c500d409100d06004041025902018409440c4085a0150301030020203000311424050030946000c0c03241141c0c0c0c15510b2a8218a098a501118120f140c010002410b00581105d151540315464074040d504150000c84c0d02e803039054451001241c0c4801015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 992323687 1250 992322437 992322451
    0x1e090d060b030c031c050c01020c150a06050103050c03041b0315020a12050105150f25030f03151406121305121318020c121317030a030209030f07090b09 67
    0xc120581441031700710342048200103100c200701002452010000c07003034060720800d4081c5800c4408004488591481c00c40007141c05c3d101c4a45480d5001859620030b01820780034510703081d00f8600d50b40355901e9410143e104e001c20741c15441503004000002807030784800811100040d060058813035900213002480d00d00424035480070241060010b01c2166a040d0641407403205c1008216582e4100f5900c0d482c2a00601480700c82440d086a240602540c00c080b07800178140c426600c9800a04411005508503170300808200c1807031601d88001d124001303401564080a880c010981d9003071410300380507140c3ea688101d481e1200303501a10b1a000400c01c08004002c00701d005400440d06080003650b1000400308180f00f2080c10080048000450061030b90464061841c0d5900303a41000300c841d00000700651220511501c64900c0000004401c4500300820035500d0340f08018528150b018101240030750440c0d091580d060040c16454006c0c1e01e02009480010300c00b0080100d2004104810083da00f01c00034000d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 992324937 1250 992323687 992323693
    0xf0a060501211502210f2e060e1503100807060906021b040e0d090f090209010c0b07030b1206070210090b2413200f1e090d060b030c03 59
    0x1c01c00141120043d8500c080203480c01138443c0103000d03d40d100300102c1d40f01841580c443c802884a13545141e9800b51151040420034600c515030080105182100010340d1a03040610170810300a1a114017a08029110000d0015234107445801d9180302e540d0041d90144c03ca08907444040182031004c0c02200028611400c3c20030540c3d01d4240c0181d141c559000c2840d03401c807071071110203010f540c4980c4441684101c42d07040b56a1211000c1000d01124040d0040c0c0314105241c1400003005100740c002c4070404d0340181e48085813055680d48035823110300080e02d25030625840d49a000d00b161540aa00716581404000400b002e05001e000039040405c04450344034024244045a00071485900307585801800b080c202c4482c1c5d10031111200c1d0301c00e600c8c0e40507680c441501070348002d0500c61500402c00c150030348ae03c456210042140003000318411300d60144204042407008180c032760501d92801d800100d84103040c3740780000840019030022580744040b907105a65801070f200904042001c004070880503001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 992326187 1250 992324937 992324999
    0x170309070e0c0715090c08011b030e120f070c090506060708130915031a0906010608090a06020403140105100f150c050d02060402150403080405120f0a060501 69
    0x662035109034000e40100c80c0002000c61002081041203500d025002050000c10050f0000b941001d024940000e50702e00c02c002c4c00c00f094200c01882000400c03005140701c6c503030342c0d0888401500507021892804e03d0f680948c201e02d652030180300000f81002158042078135502c06180c44c100c5992741c92608038039041803810080191907200c14048800c103e4205685075224030980c6500340d901501354000030340c50b0703003040544003115036507001c001c00762071040d2441140d070b070302c00900159200000c652016140e40718900402038140296083d50704408000140c6c1c840003040c3d01c41006036032003503008403810308001315a2010310000703114050304208486000d805841c0740c900c001c461a00240100400c201008100e5085180103010040e00d031503110b0141c075403c0940c0d29001c1e45566003141c081e40140c18220b081c400000b4000e040310b0990307510151f80342c109410a0244060351403080200c00c143c3c4a00d030880310f208902000101c0314144508004229981040c1c03050041c1441c65092040d02c2c1d0000c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 992327437 1250 992326187 992326201
    0xa0b1e0c0409020f09031b040f090203060a02070318030503120106031b05030604140405100b06030708071b060e01061502010c0210051e240109120f051606030204031703 74
    0x108075030840e050b0201c00358813641c00000d80121840b40d03281080e80740c4203061154884500043d03002e4804c0c18211800c0206034512a8501c0968480d05802941a04000300103403405507564041d1000300e02926020b2000801c2c0e040701c80203a9100e40040e2549e84c40030540b604020b1001d48060b02410480c981441212041c074204a07011200d0000c0d2000d000c00400001e601da225613108003500038803855150014201420516203582e254084490883e0030300d0907120860600100302c0c0d0203410709617101026a99250001ca62882c0c6404120881038100707240c40020880a01a80c0c0c01c031110301c400010540e141c07042c02800c0d00120000501564180138030244029000b141a10001c001c000000c50b40b50789d02d48c409903086a61492111100464005020741044140c1c0300240c0021100070b158140c8603481b0056030140ca807442603c3c80820002009800a49250a2205030705d11038011101000083e0781150540944d5421034000030360301040800502003e90240c060340f500e0036103524954108030b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 992328687 1250 992327437 992327461
    0x9030106150c02040c0e03100e12070b130501290f030f030f131e06020d081b1602030601120b0a050c221e090e01060501021902030c030a0b1e 62
    0x302d400791103203039030300c101c180128064241d44010900c0101a83d48404607009407d000b03020500c0390b0000d41c454040c808a0458150b03040380d41d0303582c200c1c03140c0707240ea40d420b002c2c074004420841c1d0880b520b5484000e91001401c0b80b003a80300070658030246910034500b8260910a050307112601703040c407075071180112119001b40803081b10500082103080d01d5070303034101100721180f244107503010714450381544000c995107216001c0b00c402074910b50f03800c1d103034034100e12002240c000000361061424003a084a81d500781102482c001c11504404c501e1582401d142c6400080c1024400d0340002e20581c80b0910704001c00604410855004414000402c40c40c1480011007111340244001035001040081e000d1240001c2ca00820004211b07000c40500b42e5040518400c04140403441074000060419000706107400307042c01404191001a801010240da00400c005110480d001c401e070707014003500d803030007442c2c0e202072100f11803c5018489608060500500142005244075a502440c1c891001800800d00a030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 992329937 1250 992328687 992328707
    0x910090e1c050a090e0c04080f21180a080c0a0603090f1103160f090c020c1f0909020c07080f0304150f121b02010e07050f060c0a0c09020903010615 65
    0x18903005840f20444242038520303000980209070341d00c00081c204400c04036400300800980d4091800c0d10302039100440d2542d6107444c100d2111040030220081117460a004030043c2c2410108086074000c0c1001c5140421141c0030550030800c082c0e04000d201c048181030184408000f01403924080265003803d4540800480c01e02100400c41500c01c202024a95000c201203401c1c0840d8100c00694695185040d440307400c161321817a10114101003200310071900104e400c1101c00800b80c610046030404682011160414060440502801c1c080120b500c1c1041d01c0034140e040d96500090201e1400c0246503450a0781041e640c0009910400c001d01ca045412040c9250001e50390034545142c0011402c2650321850142410b0075591601d0303945c0051054030001120b480100d0b4000f0408101041743d07094541810340642074016034194280c1c206414004000d24110705c3c103000f40c2d004680c0c5640d800d03020950070392000b40e20715004180480749150138440e45006000c5030242d511940c41c1c6030800740541d01c0c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 992331187 1250 992329937 992329993
    0x3100812090f0618030312090601150203190306090c180b130e04050109080313030809060705090d02280303080f060f0d030e0405070f12050c041203030b0910090e 71
    0x10104e00454050020f0b8491159510002c0950352682240f000c00b990984040380e01c0781c0b1038465200001010080024440b1924130182d015516000d802c2c0c2c0b02c580003c0013101404c042681c3c90070000b40709030540c40399440140d900daa520007030043e4018002e940b043c0d81d80250207400d0301001500b03480b015403200d06d021a81d4101c0580055a5075040039401410030700005003203581c0010800110750241400c000c0b4152003074440b07a40039282c005165940781000c4078a8404204104030643d0549880c0182c11030a40c4000d10303500c030400b2291950348088042d000c840e0f130024001030040c010581c01000080d03101c80224041180c600c0c049002811300021058118051192000c0344424144951418150f0081c05841807003d03080c842c0009150761844059140041c801038210082d0840c54000d00380a8415414003500b8241072030000e010750f00500004a06240d51607081410f03580714103e82a10810310080e44501c62407030003201c0c8081d501c0b0032a58a1041c0c12003030040c402c1c1240d0b00c840120441c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 992332437 1250 992331187 992331199
    0x30d17010515120c0d1109011e1b020f0406151119031215030b09190f030513150e181006030f0f02070f0203070e15010f031103100812090f 61
    0x30758000c0344e0394a1040d0300d005042c00f400c107003100b440e021554005050490080e41d48162038550503448284032040c4c41c2501340020f800d0000101900d030140810009030b03000901c0b40342801d031036000180449200f81d10425240810400c24240f030390300090b100c040a0306000c060911260708189424007064480e0004040c0125210401013400f1545d00600f01030300c1c0a42c07901c448c29228181280440421124036032280b00315082d5030f08000c9000700c184140c40c2e10500d075503416282c0365070036035494000310104050a10342c0a00020400120702ca50000145903494001007001c040042c0050f00442802203104543e802052241200c0c460054804490082c81c0c0002d04400b4164a00060004181484031650001c1082d0702441100c030b1240111610031006c0301e00d01550b4200c10030704410b0031200c546d000c0043c20645c60165010314008042d0b07024a2400154110391150440d0441c3c1090b11071184a000b000414005c0c004200641102201c511510506004d150b10004040d0090ba04850703006403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 992333687 1250 992332437 992332441
    0x13140a0305280204140f0a11040e040501140a06050a05041b0f031b080109050f06031203090c09160f08010b0406050c01020c0a0f0c1517060d02030d1701051512 70
    0x3402040e0542c24039500034814020214243c0c4079030003000c819100712880c80c00480c081402041c80740b1a02414103505080b05040510784038400845c1c64000b0f10036038255489071360340e906c00a0241d42440c0704161a44002031a5814038052001404454114a0203103103000c89120888445210254408031245804200e40c0ea50040407400341c076104600d54986400000503480d4075400c0800c50381030328902a0304008540d1112605003240e40240c491a0b0103401c418022413070510340c0704c001c0d03a2040080b412a20840a1708010030760010080700c00096005506004107a0070303900c5004030505440501e041890307541015901d030018030440c40b0380401d10600040c0410b02d21801e40580390107903111026506560380a050101052002ca2411210100d1125001c03a000d41003002020000b00ca07a0703078440e1a15010071402c51505809400325900c800140d07090310069804001c0051240071958440c80481201e20040750002c10607008548664124000d00e102c52104000382d400d02c100001110a0360713 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 992334937 1250 992333687 992333743
    0x111c0e0c12010f050c040b070b04170a0f02160302010801120f050f03040303180b030a0905030c0105161701080a0303110c0601031109070329011413140a0305 69
    0x110400d1590503410032040c015407415600190312600041040c0c81051110340ea9501c10180144150b015441c039200081c01301e140410f8003501001d1703216110b50320b03041103048441e1301d1429075040041c4450000ea51400d4041c2419414007000c90480b02000d010030300c0c4ca0a55001801315081409245031903401240c0300f90600c062240041441604082992001c0c00300d040c00346d440340e10901040c1c4c00f04189c1d140054500400c00c004504841c4030545135400c6480e00c00e80203001c1c4c100701c0c10a035502d00c4240141031402c0c0007132054602038212076194031600910254080c3c0100d4100d8410303980103c400004010b05000417640c504400da1603d000107540e4000c20f0050b8480c0030382c10080c400ca11907100040100881c8140c03c0205c1ca0b012954403c0c01ea4031400c08800742d1303400d4066070034984201c1a5950940717003221200f030f81c07800d414105941c0c001030049542107250844a80b0382d000c02d00011007000011a1070041c00748494060301c4c6d480d09142540c072450343d181e440340400d00442440c00d41071210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 992336187 1250 992334937 992334943
    0x806062701170c040641060306041b0305010311040204060519051612180b0a0e060405100509090106020c0907052a0307050d09120303090c0f030f06111c0e 68
    0x308010130400915884190070520328202c066084140c859901520300c1e48a00320900d40071442600e048451000c00c034000b0b214030381c0c02c003030180fa40043d01c40c1207808c004040d02100503000951640d0001c0d40350324506106807440314806c4510300981c410030041c0501580a012280c540c0801001c4009030451117200301d580303100b044c50044940200c0e110100822500840042070f400055a40104489642c900c0400b200f000d0f05c0b030744142c21000c00c010201e150150301c5a20410034010302c1c160400303a680e40414501d10111402e00c0001c1d00000700a00030307280000c0c02c2409000c9130b10003043e0819526000c6070140c000a0300341030902c000030032101c82442041c01c000308425030000311804640c280aa074603aaa40100408503064080c4508544d07501c4d20030360380082140c1a01588164100341c41d2411341c0200130b502c04c1911102c40710303107001c6000049800c009000b10b00c41c0c20703042d80004071418840204d500c040044060400c0070052844046003841064468403e41440010f00c2890300116603e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 992337437 1250 992336187 992336203
    0x7120e2a060f12060609101808030309010e330c040812120702060c0f1e03010602070503150c0d02030712050f0106020c0603091c18080606270117 64
    0x98000d03400115070b440e000002c4090843d9072120a0040d0f15600c690040100e00c0c012205000d8001e01c1e07102c4240d002a12540001065014140d141101a0384480000f03003594022100c036035050391a0041021000c03000c10503040e400710034550328036042e01811801609018180c0c1d007140e42480d000b012807036114800c4100e03002090a541128981c00d58500010096000080c1c0c10400311748080006002e58000b040042c4101c40c0100801d241407040130808200b85c02040300c0a42482048840c140403010800080d800303804140c00070000b07946000e0030146090000040d034240000320740240001c9400901c10344d1242c030034000380582c40e59620002290401c07080385110400c68101404c0c4004500d03901c0c00c240c181c0b0720541c00d54003001640d0007481035901c07040e11420400d501c0f000d80369146034821110501217038510315117204200f4049215124441e510b800c881e029400c060240211403401c0c0000020b4074000322420701e040b4004c941d092105120522a00702c80c4403160a444542c81010b1101d12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 992338687 1250 992337437 992337439
    0x1b020c041e0b0114030a0b0a0504020703080c2104050c10170103030c15020703181a031f050a180f09020f01031a1c05060603120304060e0a0f060507120e2a 68
    0x117442e171030007900f004080c1c160034420324000c00c610070740031840f030801d0b000700c81c403180d0151620300613070701c070607241d0f03089607200368400c2c1c000306040b00c03510035281d941e094558012400383e401803595428070002c002285580300e041c2801c1c002480b10384070b0b00840580ea40e50450780c00d820329041050fa1030401009000c1801045680303144005a107034200b41d04007100002d020590014009002d0f103c003060412020020002024094240005040d1091803c1e01140d0448a52580c908003030385ca83c0424408101a00040c13101850b400d03806441c0400c41c41058005540d01c142403248142540104149204a05006040585070311035031900070010032540b45c41c000e01408128803030008410402c6c1c0520f00d100c00711568002c03080400d4440c900040d00b250075050030020146103803200e0356950002e0107019440800e90250950f04404909403441c0c48a500340129000b1482d0300d006c02c0018403007150006400f6100386040604c0180400026001c00e411800c40285078081a020b1880394000566014207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 992339937 1250 992338687 992338727
    0x90c081005041a0a3306180323030c0604050c04050403080115020c1302040603060b12130c0302030114160809060711031303050a12031e05060d05011b020c041e0b01 72
    0x8000c1120300c5c4031001007000d60704a21003400c0307512080101c078810214103110042c1d4070010400d002103a0301c0d205407181102d8030041d0407075500c107040c107071803e6822921902e07105811520401080c04401d021403d00740c14211008c11040c03406540142c01140103006000c00c21300c0818004c800e0a00810901e21b60f81d600030603035207410888001480181d8440c1c040c000002e400c107100016a000e4103803d442203000700c50009211551150760044808580000503030307064120380000405a1020712510340303c1d00c4108000e1202d0720f86112164028090181e5101c1048040000c00c601c4074404100c1c241c100203940343c85941510309440081c40c40c00740000e5034002040464000042010014800a9051207424000700200a0b482c1c168221400704410104000902034100d0b400c0c07459910a5510440c020720702d4402940d261034903400c454a000b510325418504180050300c035501048031f40c00d0400110790600c40000303d036502c0c1c2206c61f01020b51031001c47c2c8648040360180c1c0100301c844540f40702c0c0020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 992341187 1250 992339937 992339981
    0x10309050105040506060103110405130b15041d0603060f060f0114030a15060504080a06053103080105040c230408030a080f0c180d060b04090c081005041a0a 69
    0x11031710380c02c05840c031034046850b000030501c1c0280a84240c8045420060006c0592844002840050010759000310341c400302c03492030500c459200c88050300c0509600070140d00f0103076080c408404008009440d4600c640d001004008518461030314055100c10103941c1c11001005540040e0b032440d040514201c0b903d8400300400c05103890590201e030000c000c05a4110010f9502c0ca400e503040c0c4154001c0c00031540040c0c82c800b010600540096400101c402c0070641003004400182070b4400003017400751500d0380716101071014941d1140c8568090001281c003000300c8940003030080c162004030301c020807404000c07072035071030600c003209050300e004013100c600362581e480140320002e080001c00ca034400000d865202c0130406400c68081983d14140c04500c203400300021420401c1108003114a00700d858039102c40900c01c0e191a24020404054403581040c40c00d1424000a282032600d50b0f203007070300102d240c502004040381c500b800302e40380403101900000140e110001e030352003e4600d00d41c0350394605484901c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 992342437 1250 992341187 992341193
    0x60414180c040e0c190b040603020c06060405010e011a13030302010f0b150403390906080c1011010b0a1202010318020d08030c1204031d0102060103170a03020c010c020304030c0f050112020901030905010504 90
    0x12f0550040000c1600c0b6955240b6040208540c401c0c001d25007228203640042c40380040440444280b018400071107410060402090120600203400460050351201003070b0501500f80c1c000c1140c022800c88031000c40440f20744ea9110305019512002d0581e403118508011a035034540c0081c0e815130700d403e00c441210820f51a0b242c040804500c0341c030b25418a050b000040c1d000001c42c01000422000b0121403116844c0c070b0007106c00229040e4280c00719540c0300f450403815560301981e03d008095a41c01c080c520780c1180005000c59001d5121420b000100e80c0605005980f07400d205003005600c40303201502c03510dc8a98000260142e114015040051b1505020074035402c0000c8000d04004441c40070f1050350b0790f900481c0c5450307003844014000c1c81d080fa102900012840090807601c2003500c0d00604002a4400c1c440c01c2d00e03070821600c400b58200090a000340030014480001401110840003041840d04c000245030b0b0301805c610f002001e5001c1071401d0aa8842c0e004406580d0b0010000e00c9281000c1c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 992343687 1250 992342437 992342441
    0xf03030305061e01050d021b0d0305071b0213091a010b1b0316060c05090a0b130f03030e04050403110604110319110603060414180c040e0c190b040603 66
    0x1030b800b42d119000c2400c04414800f80011001820b02c0d040e03481d2400c06036031808500107504040340900b01301c0c940d0a00014403e00c2000521008039050350080342c1410480d0303025009180c025402210001034080c12000352701c5913081d01d0681d01c01c5902c00100300d800c609040c42c9900303041c103000b042c5007074000000448517048000361440030017990a01c803003540d040f92880c0d9070380301c4e4400102d50801145c075202c0106000d035011800751043c0f0b00703110740b80400382800034858402d15044100385035008038296100d81d50b1000044098060301c01042655411500d0140815000b450710350f00c04d50f100c00000b42050b100d206541410300500f0f08541060603e86001000300145841a500911412481c00b405454425022407100d8001c0f06000113000f10905004c0249c2c0010142c035002900c034012901103d00d22a9124404c0c070094003085081040700303031160308008000400500c601c0c1001c1502c0300c0742d000455806c25000088465800c400d00c00c44010040d40501d074801e003020039010900148613a055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 992344937 1250 992343687 992343691
    0x708010b0915090711121b06010602100b03011d0f061005100e04091b061101060308030a021c0204080102040f0801061a03040317040c1d0c220f03030305 67
    0x4000248006000300051140e4000111842650031600145680460800e01c0416401180c0c41c039001e02c062048025140c0f4110b039220441d034100b0800034000c55041c05404e11151101c0840c0040e040552505200030364502031101d203074545a07510414040745586c00d40c89481d5061521003071209640d03415510549039007041700b07803654500880c000240c00c4207415040009403040100b12030394107040c1d0002144c020a00c1001d040c1c00980d226402030110b031103043c0308010701c0d0144a4601d4100d040200042000d0368090399840180e0600d031061000032100360036686e00c90300458005071204280c500084402d040c0c0c032a034401c1c1030310000380480c1102c4107400610036542d20f401024299035032004902c0c200c0310302c1d2007000310140484081c265801510001036400901901c3c10000611648100002064054408882005020340c0c20403001c0e12001e000e11203c60f803000c0401070f518006c240b0850b5842500310b08110a803001e0b0040407086940100384010380071020034250002d45a1030017500404003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 992346187 1250 992344937 992344949
    0x1120b0d031220310308090a09050c0405120a12020319091a16080325020312061c060e1b030604030905060d18031e0c02062d0a0207 58
    0x1000c03a50240b107034442028204280390041e03d985440e00e68441083c9070008403506400d90681401c1040c80e100c0b2100d5400c01460045600715540c0300c00204002070803859521841d491030808042007060640a82568110f0b503050b1190407030318109101550410984100040c2031095818a482c1c0c426800030140c9018450304100583c0e2040301c407000d8448403000d204100c000c1c483e003680d2031203414002c4064003841300f40c00131102003203a15a035030b1000c5403c101e80c1d01141300b03450b800e000c00c64542d601c1500000c4a06002440c40c2110308170450300c001000a0020340100b1034049008442e42e2008003101816412800c20064400300b0301840c1e880c1c81851640d8030b19607030840071140b100d18001ca2030b50301840c0e0580311504203c1c03a010910030f07d5002039000c1c4404030380c2c130004910036106000c24038503030510035940c04040c001c84240b41c036002c800080001d000c21580381c40040068039440304507a400580141c0359103a03028965640b440800012503007400400d0085650a900c5400182c0705099800e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 992347437 1250 992346187 992346191
    0x1609230708040201020712020a0b0a0e0d081312050309010c140703060902090718090e160306020703112d010617070e07050a08070309020d0501060b1c06050f01120b0d0312 75
    0x87d5503201c2e400d0301141d4210281d48200c44410401010b6401c070700a2808144508010b51088000d000040314403a480c042a03449800001d02c46003141c000191403006030418501002c0a00e007161036256481c015005100c0c180410100507006120404800340c8055a282c42210101c5440707242442c054081c0000c101e01640348000418822801180c42c0460202084040a0748514140d5200c0113440003074031602e070501a51001261400949000101030343c0100c10140e614a00c5140050912101140c00680c075006800c50499240e075481000040c90515401c0f02d8064047c0c0003558010102a4800c42a110085510413100c0d4804141e80040716201d90187e60030b0394910700c00742c606103d070040c080c0004030010001200c0e64041d0388501c2180d070000c0e000c04070b040c081d0f03601e0b6400c450407174110000e6403034081141c07180004c2c0740c0a0140e48115180c410700606203030074081034006041b01b2446042c800c102c60b101501003200d0340004684100100940c1c0c1c40000b50a002d0a8209041803a41c40a4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 992348687 1250 992347437 992347439
    0x402190f06121a0d0f05030f040e0612030f07020a080a0b06100e0306061519021608070e0402010c080705011a040b030f120a0203090604090c0305010816092307080402010207 76
    0x54034620680003900400d031546a040c03c0290200140c0c80380c0f03400700712014520f100310a004620108041c0c50040b0080d440141c1d00e03410f20b060799101c8840203140c184a40d0b41012849000f810100c280c1341d80301022000113444010034400111001490307005203406128101103030050110100700b040c0503a00035200384921341440c81d001c4030902c0b0019000380c6c05a200c140420b1950a1034402380c01510b60b50111380c1d080c079844c03483c0c5511040044c202c3c40300503403080c51302c040c00c840d103144428018400c0c2d10003806010701d40004002d507240001c0020b81801040e0380283d003440b0099040350b80146d80007008001c800083c40100c1042d0b104181c0d040e024600e48200d401c183c2c02d0018690b0b280c0080b00000b80300350b038021138181e180c0f40e0000e2200411800188002056501c51070050806003131181e9001c02c00b00300520340202120780c160b0100449174041d50090903952102d04681c010758003541400301d203200c0f401070440400c044480c2402c120940d09010000b026034407001c1540100d01c00d13401e0751501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 992349937 1250 992348687 992348717
    0x608060a03050303040b04080d0f05070e121203090106030b041a010e0f040210021905030403050d050301180b0307030803070305160f0509010818120a0305130c0b030402190f06 77
    0x8000360300000b06564400c00214010403a04c00c1a40c0d8001d21030300040d413521260b00950000d5031030420030a0501740c0c40c2d07010321110079000000748821120513070f00b0803c410795041c05190341d02e0100300c1c81888418000040f50001e10f003900034001540e02700040d14001d050515140300041c030725000840a0744446400032a040b10b200c3c400e18010403402030000456242da400300b08050380310061134402d42c800d180c500e001c0d0b14009940401c4a600800c003440d1034030f16500b0050300f0701140c00100c4081000400040c400024041405401c0b8216950000f42128503030020910703202e0035800180012402104100c0540e9041d0005403003408511940c0c0515120a081075071114a1000701402140081c03104000c107505c162486503210004941c86401c10040b010740f941002c003c1844000402800101c50726420307058001c01350000c1d01400103203858202030319448101c0c40b950140d084500320010124041d550381c95404100c05050b8512140c0aa03514074000b42c1e962005e224840104404000e40c00031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 992351187 1250 992349937 992349949
    0x1e1d1f0f060e070f0c050f0f0f010c230c011a0f0a0312050d20070b070f081305030d1a0f04090809090711030c01050604050c0309150907080f030301060806 68
    0x80791410800e02c03446840f031220642e64111800900400c00480d2611036012500401c412103003450014090075081180c0d000a60400b0110742c4903481680c181400264600c0d4000c10500b0038148030220b96003200e414401e0840c0e40d1041c0440881e40e50700b00042016800000c10304010b0700728045814940c541c8006051182d615203601c40a440c00c840d400c455183c3c540504000c104421002c280080c1e03d804107800c602d1500e925454445d04c0d01000710b00c07001003000c049a02600914035041c081d12854104100401d40c1100404c40300d04403d0785080501001020016240319138814481030260000e4820000503c901c00740c5510b2013800b01e00850f56035410503101d01200f060300203080900c3c0680d803100340088008007501200400c80e20901c2c1e181c4490041c07018000c1403003a0000402d09051080411041da43c0c041c00980000c0403c00c184201d074440001c503060300b401030f90300c2e4184075503d04200781c0c03d1156640c01280c150040789419552030314003100840c180c07082515114119241c47c01407141d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 992352437 1250 992351187 992351189
    0x171b03061f0806130e1534030623060a050415020607120e120f04030203060c04090609050c03070f110d0503090f1c12020409090b0907091e1d1f0f06 65
    0x21701a00503040c04030300145900019a17104410702c0010b0300382c0000321111810041080385c13501c045d50b42000c044920680c10300940700105403100350b440003503101e000e14200c0b443d000c0100c40e10030000042c1502016000d0320540303000300040c20000103070310f2402c20041d440e40c42c01c85400d00014111102c4e468007042912600c1000200301c40240502461105056120741c085c660540c030007001884000010794040207a54070030b40700c0049442d1914074000c1400140c81440d000349041c0b900b8001040b40d19031808050341e500420354608243e00c10070fa8041510b120041c2e07010031107035020300340301d003025923401000841c080c080300c204640e0461f100040d0592100c282006000d100c82001c10f20b000401d01c2810140342c000241c1500506d000d550300c142c1c80451314071450031030b054000d01007009101042442488001c00340003c05100300181100c4002c147e0214410045d070495540d0094030325800624100002142941c040f16400d4208800d206007102c0300300d1014450782e080410b00c00c803c240700e020b420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 992353687 1250 992352437 992352461
    0x203100e0c121c050c010b01230d09020a091401090c0e1210050103030306030201020606030105060f040e0c1008010e070e010804060b0102010e0a03080106171b03061f080613 76
    0x2468030750020041c00030310402090b42540b0595001d081c0195181c542d04448914079111190703203c0d1003108250941e50590300c8a41440200c680303d0351021a010b0040c145066074201c6941c0d1f81c01c601003000c005059105029400a2800001060708170165006c5080c0014640c24001240e0343c2d00720190130b8468116603003001645020481900d407c1c0b650f60812040002d2041e61000320030b01c0901c104954003640168000384c0c0380d60303040045d5601031212030f03005841600248001d14115000c40c0701c0c000c07001c42c814021581c61003013001990080c0800880c40c2402400403900100d14100280141004e000d410300e0240030702d0114081500850000c0751103181070311048000d5840d600d4035002420864102c40c117554981c0b88010300c201f41406050b05c0b05119888011165060440040c80806040410071321400f9240a004d413600135030000b0b08110044030302d03150781c0c0c0d550080071800504c0380c920b00d07850380300c1d10514050300c03603070001207552281c0c4003629100014020b01000070305480d10800c00b8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 992354937 1250 992353687 992353693
    0xf0c031503051c09030f11091f1517130c0e070804060b0f130e12040602070e070509062d03150424090b03010b1f0e010e0a0603090203100e 61
    0x100343c2507080005401070444941040181d2a0b40d03a210301c00d541100400443d042090962000c1c041e00e00010044e07000f0550408040901700300c030f0841d4045010074010501d45443d0090100ea00310304c030f900100c0030b242001c0307054a80ca04000f0342441070a07d80c01c801b1582d08126103004212200d0301401540b0070703840b5540720b4006403160f444080050054502d41600030f0310701c0c1c44100c40358403080401c03014201085000a4000800e00500d420143d070600c100103901c1081108000d1950700052800603105140e0400928ac3c03610070703042d01c0b507124449109422100c0400c00c0c1c00580d91002c04070301400305002d400018031040314490b20301403008882e10010260207a01002080c00c01ea0f010761030b01410100440d910101b14132071b2921a5030b45030f0102009030303100c3c1c0d03224615040030702480e0044201554040110034900715810400c0e0500708290042003071004210010b40e114085034040a0341c05450078202c903072106401009001d942c8404c1c0e0013485030106400c0c00301c01d54428600380e030407040c000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 992356187 1250 992354937 992354953
    0x13020c030c011103061c150e060702010b01020c0a0317091c0c090c09090c0c06050c0a110a03360e01050f0108041509020f090112050f0708150402010507060f0c03150305 74
    0x6102e006c070002910112092a22400c098115206900c505174003400103101070300d0842d00003400d403802124854119042a040c58a05440d00d07001241965401480203040c1182e54000d01e01c54040e019181c1d5011442c40a20030040b203e002c800030002c1e00035000525526141d180f10000d1b1110711032840c0009942800c1046501541c0e40491203401d0b562801d003403000035603110b120680e40c0c1558121014000001c3c51200580c004e0740714052120385002400c1c00d0030841c3c9015005043e507001d8443c10010042030405c0c0c1e10482540086404503c100f90700c02545c1399207482e0002c0100340a482d018189500700380110303600840003d480740d41e215001c2c1402c201d04061481c0503010403a0201e8006045e45040707100da9a42e00c0400d07020700140b500c0b50082e12040c1c1019031400690480e0940203402a800c1404040404201a0300500401c1140742c1c85840c0c1e40b0040314988900e0002500e107603c0c01c86107541c0c00308107400c00d241d2840650340c00d001c0782c032846981c1940f103151031000400540c08040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 992357437 1250 992356187 992356219
    0x608040203280201050a030906060308040f1a0d020a0c0b01080114070513090e0102040906030542180307031d0a0503070509040c211b03120c0213020c030c01110306 72
    0x4022140440c68045182c00940c1d4440c40ad503162030b0070840b80d49101207018040c254100c004400201050f01c0103951901100313460a80c203214014246410b5500007480443c140e0051000300e0240c1c4c0d11040c1300d0070a60351820154024244d070001c48096241400102c0e40040c07090701507400002d07100107a103000030300d07040c035500062840c042400c0f03840d5002c4c400091821417912683c0000d60298001d024184c040108480c030417410041d00d4281d00300c8054000420342c079261400b003248082e02d0315035440e0340c50f14003581c44041e08002c1541e00794440090500e0815902c001c020b81249442e50088103142c20500c108058203256014558043e0710106080000f441c004459540203070080c0790385941c450721450340300e0060454441d02c81c00d001ca44c03510401040303400f00c0f4188602070f40002404074035085035039101000080c070a0440170006004040401d554a440480d1801920450110740c5c0318484405243ca94000740c3c441c031455441d10503009030a40c20f441c100d9100d298006c0c0305012207a8204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 992358687 1250 992357437 992357447
    0x606030f042d0b060a12060203040c030f03050a0305060906101419021b090c04030201030207140d03060e13050c0904060e0d09170f10090812010608040203280201 71
    0x10000d8030001084001c080789030340005554101001ca82603050354003241d60920b0b040d110800784c041809800c2006003001101c8107000d10403101c1c4d91211001d6a2a10355050684c0f85d4222904050001c2c641c00880d00205600280103048060b115142800036a8820040150b044422142150030a2204801124903032003642d55200e12141d0040642c10a807a0b114a00c9280864120a00c0568000c80d1300141a2101140e0480381200840300d441280c40c060740c60400c00d005600c0028141038010805a040107501585070304240302060495420034400f41c4020042d0515119801004860002013400e410400d0503400c480d51b0000c00070725402e000c80b018420001c20040083d5081c035070b50401da02241505001c4a03035942640e58640ad40c0a06092036880c2e8500c0003041c8064035404600d25035448000858a401d82c8000c07a400050410000d0074503041520603210a4000508100008215a074000c0943d0307004900039001c617441210400c48134007401c4400d0b504900c62196081107640150302ca6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 992359937 1250 992358687 992358691
    0x70f021c0201060b040e180304030218070e04050a150b071122052502011a0105180402070803010e0906070c12171003020f0414150a0e2d0606030f 64
    0xa84000500169140b01d01d0610b81c000343c101c5c180207083c0c06e0910010300c03200790f01d01850202890140d4542803961b0b0000720341c6044204030520121040e0002000c55000c1c03204490f100001a20912542c58608441070050a01c1112540070107222540451001455020b499220750b0201c82e480d4031f4900b80b0104900d0f10302481010344000c40d40008840700002500400d07000e5448180301d5038000c1101004400030001c25081c031403c5a2401440000040301c80c042c6080e901e40a0a007950f41d241c054410801d8400a4901c0c01d80082c000903855040140e10030042d4100c6925600184058a41084c3d40e52900c0c425914080000c9044481c1c00200307208054180b0035001d07605000340320075044011115120022a411580703640c0024080040d800e08591440c0c0032581258200300344040c84106001103032010384000700d80d00e11031940c4919902c4e401401c10140a035012540000e280c5001d042800c2007244018000010000c008803000c0c2c40700340360b0240910001814941140d1390750f80d14002041740 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 992361187 1250 992359937 992359993
    0x60c08030a0e030a02300703030507030608070e04110a0807062a03020607140f1803070314030418091109072d0215070203030610030902040f0e06070f02 67
    0x1e68079141d142c1150400003031090021030b4003d09056020800c980c041126070760390751b60b00400404a4a64100c003d5401c48111035814100001c5548510000318010010790700b12904500c00e154010428900b195500c0340315920030022605420500014450800010301c10301c206544100c209105070f030300540000c400d03500302044001e160340040440c4001582082d00c1a1701581040092080c1c1c1a84101d0003070a482400c03940900d040101c58070241300c2c2c81039135020b0384003800114003810b00e5030b4240000d500464115031080140d849000d00c8585940c407034820790903403031900702078014980a9400381c000b007141c011000d0301c0e00b03450481c240901d400b0005c1000041220052440d00d5851041c000e40c4041d842c00316102560409001c0701030300e41540c042c1d000840b4100402088085e65000080340e52000c0103a807c000e1542c44000c054000d002a20070081d402820a01c7c2c1140c400c86590051510802e403004442068aa01d4002c0c0d85027243c107411040180c01060250500340001a01c040c61141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 992362437 1250 992361187 992361191
    0x14030a210902061b0105090a020108060f13150f0f050a05060a0e12030a0e012f240403030c0804050d111207060e1606020a0b0a24031704060c08030a 65
    0x501d95000079516072114000d0a035916410300780440c003c40034814154040c2c0c01c00014002c4408940020380010382c000c01032485146080e14160550f2285004101010034503a002d124030030807010203200001c814091208091861100000c03121550725800c0211200682260403c0d42800c040c00140e83c40084210148080d402c05502980c981d405800e410142a00c059030b280d2421084c010440c80c1240710184c10007132000c01103200b141003c00361010301100c0c00740c55030543e1844c0e80c400d400e00c2039880320b81b001e08208107200e9405010010041d0f208078480d80c0d0820240d4500403095880d124140c60107829035004060302a0814007403031a9020380b202e141e0843e081520340e8030a48005500108044a4141e22068920301d5003c040200320100c9152030003590750700341040c00c029030311880307904080c107a4200e080205010005581c0102528071840f102031021001002c0039102d40144c83c441101c00242c0c1c0381c4034034403485104099405458140d41c82081024164071800d4007500060f182407030380ca03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 992363687 1250 992362437 992362451
    0x5041a071506030204150e0c07060b0d0c050a171b01110703060f180314031f0b090312190c08191e09030f020111070b030a060314030a21 60
    0xa400c604240a03824900d19000c0340b00341c1144184420380e00440c5070442daa2038554018002528022411a4403110030316070141c4800d46400c11074080c4c807031044101d402c01c0c0e001201e2420b000c801d040320405e80d0001c2c0c946003510b139070350f0a01400882081441030102d41010144440603541c1d0440c6001000e41490020b0010003c000300354140941076100329082c95803168480c0d80158103014424015440001813000c5c070a03a46c4010f040f100d0b04208030f60741001c0c008005000c85000483e4480d0300303460741f06d6050485443d180000c0d410745c07210b00c22520920503a1100e07222040b581c022560a442c1e1600d0440d0842c01c40c90054444514102d0120340a90050000c4c4010111124020215400c0c0381c1c1c4544185c000c0e25074116035602075042d0074042001c150414008034442950800e8115420300e40100e043c00c0030302c8404d00300f5103281c0180c0c01a050000610080c5401600400141e034000c105164506e06d103102240da69208000c2164003040d07000241c03640361401000c1824602074440000700c0c9030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 992364937 1250 992363687 992363693
    0xe09100b03011503050114030a030c0311011b0e0a0f060f0207080d08042105030f061c0b070f0c05071a1603020d082d0c0f0d060806070f05041a07 64
    0x41e8009030098503d8100c1c8020521426505029a500601c8100810a5804c1e031080105e0b07100d1000c00b0002c0c0a01c01c1d0b10101d9010503100c1d400d4814903082c0c80c002080754088a0301d402c075510816003846800540848205401442c2c01d0040004841c402c0d03a0003080540340000c01d48140c1260000301081d03014840000404030001d121400c40e00d11965104c40325803500385000c151280f820303101000b103100c00032041601c0325004800c6a170809400801580e26076559130001d6a107000c3c1d03440c00071201248000880410180d801d415015100715110000c5103c0249012544429203540180c069072010b4030070000060003a0000244041d40f08100e0b2400d48284031540221240207000c41c0140d001d5404002035035070040e2000c2e00b1a040c0d00184181070024004d480d20b5050300740041490103183c002083c2c0940103542112034442c0004421919500c0300c000d010010700c2036101c5d000c42d9019041c006640180b1a07000380c8282402c58480500382070801198101d0240740c0c1e00054107003c8200450008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 992366187 1250 992364937 992364959
    0x90d030c05090603040f03093006110a03060f050f06070f0302010e190c061b03030c030204050d080d0b010504060c11030c0604080109170c0327061c0b010c030e0910 72
    0xc00d1b80178801710700340455145002054140f155002c1403c004108003d050f03186601811811003a02150b1061a0790209080c0701c0018070301071150300c406c00c030000b80c400401c9416420040444030300480a0300c5e280d13501c1e0140a404051f280085d0307803040f0100901800919004040d060ba80c0c007910000804441c3c2103001450003c100481181122282150100f003001020504010705079602d070060007207604004134000030178000c00042c20300d0f49030041000214401d0707056070002c1c400107000c0c00040c80c8038100344900d0780c446039003503590600b00f02c000061540988110b5040302d40701d80c0d8000d1516040e032208052149102c54407980741c02407510310100e50340c405003d0700150621600004844400c0c2c9001c48440031010090009888240b200001110021040d81c81a20316038050b480800300b13800d001030080001d5448140d001201003101c0b150a00e600410211941030740e1001c2000e40c140c58015500c0c0d4080000040004031801072030040c5050141c03d10b40c0088142e1a415402c949440c0b0400b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 992367437 1250 992366187 992366191
    0x40515040f0e15010e0108150409050303070c051504020a050105030907030f111f02030a27060c03020f03040e1306140c1801091505031b0a050918090d030c05090603 72
    0x10380e25485200303104007200f022040ca00c074901c0034241100100c2550002814011000744540e00469804040b41307195107407500320b244095840b130181c940c0c03851f00580242600c1d0100100340c845105013011030300c0460300400c405000ea500107028440740c524040044855520080001c07039280104000080000c20280403105502d02c205801c5000c100d42c1014041c0e500a00c0443c5882c070207a00140518480c0c020084a0401c65103290249444c1c450402d100c00490640604c00803107030484400241c03c5900180d80001144a6801c1d80eaa2661042c8510350320300948c02901c081810450115100c030403040c030408000b6100700301c00300c0d403070044204001c15000100d0368250b041e00000fa150b84e000940000140c0000001d08080c420681000c003502919840c1000d060180180000032521100f0340d9502d04149100442c002c50703587c011040000c00d0f1f0b800030400c542c00307070902480d0b1004908813295094428103055004020000500310114003070414803042d0300602000b041104156260b40c00118 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 992368687 1250 992367437 992367449
    0x3100e0c0c01022b02270a080a05030703030507110c0f041404140c0411030402120708030f0a200c09280204030209090a050303011a13030311070506040b040515040f 72
    0x1010403104c1501118454100302c14018a143c0304002c1d81c0782d0818683d481c003a95034200800607021030042e0003c500004100e41048240b446003101c100c04000c8000000c22142d031081d50203200c29210a0400d4945410000c40707800d00d600400104d09440c10070000030401c0c01001000412040c0740307110701642c81c140545060364000500c0b2400280c1c00402c000365101da01040d24104080714003200700744c0040c00003510083c800d1250384200c6050200400c010340282920f441980d0340c07513900018007110b0b40e00410300702010810071511000c0c102c1c000800da1044591300d40140922000d00c01c00c20290001c0280340d014220000080c41040341300c140020f403042c02031801c2c010781e81c1c0e0441c0100700c0c0d21700f002000b92101da4440c40d6080c00042010064030704641c440d013541959515002c20b0780c412401400400c404004040400106150340b10301807100807030f50b00081e40c0c3c075a92588207011051003a40a2100d8501003004100000d007042044d4080101802d1403c40c03c0580314000362900320203540c404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 992369937 1250 992368687 992368717
    0x10b030601140316030902030f0303011d06100804060e280318210c1e090b0a05150a09091b080c0c0a03050903160603061a03100e0c0c0102 61
    0x22000d941c1040300c810101000452860841c5025080142d004181805040801d038071804180b0031504c1c20004c2505184407607060b40d84a68503050761500c072424031440c1d1904111208045101c5041c41e007807403110b034035203551092000e5890f62241009080d0f600da09100b00d103c0c81c03299503032a4840c2c0c02e00c001480e07106018441d007008141401002c0705003000104101402e0650104404981c0c1c44694041c10b01d034040030741d9980075500300034040d02500da0103502c00617a4282407000742c0303243d0b0580405844000d2810407904c590102030280c00c410034042c90342c00071003842070142d09039140e46c060040400c15141c55611551126035100a446010407105c002050b03403948cc005282c0c0068241e42e1001c4134000701e60501808035081c42e40c4022140700502880f0340010140140e40f01485040d145074900080003144a0b568075005000b00044e03c40c1036140250501d000320002480ca044901035100340020060780740c1002c031030026a0300003070b0010000003410031007510410300078006400c5002c101030f10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 992371187 1250 992369937 992369941
    0x907090602010e0106080601290313151e15122904080a0c0804090905061006020109022d030f100b040c020a15020903070e011a0307021c020a0b010b03 66
    0x406401d6800100b804000f030390500c4c07000c2c000d07480001070380c40c1124090038130111510492400001c9200c54507422001400340041003041418040307403260301151041c46000426031070001c0040845007900410181c001c40074043d441c040da2070b0b0308490700c100f0040c154401da2581d50504210007481e6601c04031072812880804069910b03405018040d58035518a040745286420703540e09049100d94010f000500402c5c82d804d6050200110540700900341c0c0200802c202c64683c14260741d0b81c1030846007001e07a541040303c0841c285106015205807168054080c88450f03640c18141c1c3c205039810142001f501c0c040321100281a602005044464402c103400350008803000300500c4140c3d6070603089280110300305107494001690011300c00f00002d4001d0703070a0414180c2c0c101e400f0040d119004e1031607494450480081815131900c04818101c404144800c0301d241c4005035060182d01089600e000940c0015a903942141c491010141c1511040e105481da180c0c400c3c1d8810781c10610a80241e83d0079000401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 992372437 1250 992371187 992371199
    0x21e0307030c060e33070f0f03110a0c050705030c1503040203030904090804090e070e0c030901110f04060201200a0804030509060a0815180606070c0509070c15020c0a02010503060609090709 83
    0x1040c5c000d4040c2c112150b00d40c51400c0d150241c002d0585080110401041d0400c10301d41911070360010b0980d51155081660b0344511980007810005145010f46850155090015192a000036040e5040070080c3c2000414141d200070ba05c6140c00040090740c141c04100001c100c50354840c45600501440388101a858038144900b00d401c907003804000c007a19074440c601c18000459400381c0c155004c40d000e0a465900e60310381e81010301600700304603582000040410b000c0d070420311100241041d038a403030340200b111003200c42c9824200801b8101e24120100100200740c100c0d4890100254098000c0c00d00900c2d141e1548041640c5603c03401911001032020011b02c81c00c0f5400d902291100d600865000504055584d01e0741c004190241190b8404e01c000030300385003081442c402c0c3d0002050001d001d0400307450f0801c00503212400002086030043d0071100700680320390261081d101c10100d460b008101703401c40e5500541d119403002c2d108036800402444400c220b650b1381500d07148151811f0382c60003c8285000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 992373687 1250 992372437 992372503
    0x11040902131509260a0b07120c091208160b0405100c030e0c010f1101050a1d030a020d1407061b110a021e010504030b0702070501021e0307030c060e 65
    0x554102c01c120704441c0030003a5805074216500c0e038404605071410b1101c0f5552141c0d180a82089000b420030811100300005107400030100302000c0300000e002d10000e4401101166000c0c3e060103030700c51855015080c4030100c0d00300c0c009095268004002d45900c2442600c501040010498081318141d01000e281490040c550080d00c0400e061420700380102c00d0002207054071110250521410004103900c6940d035544504040300c8084c204074001c11060400d04402e07000f501d000e04000007c0ca140f000c003e400100e00004440e000c106550203003100e55504c1104460700c4c440c28401c1058242c040c0081400f1606134410310801c01e40101141c5448a43d0120103040c0c2c1a185903c07008540144080102684445080700400c000303030a8000241c0000e180181ca0b64000c0382c00140c09801c143c1c081140d9160001585d01c00d40d0000d80844080300d20581e40002c91980b0740903c40010b42090141400080c0280c0e02c500710b0350310503140814584200c0084a01c0d248014448010f100400f80c2403070000312440c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 992374937 1250 992373687 992373719
    0x30408010f0b06180a05040c051b2a010c06180b0f1303030506120d17100b0a0e0102010e01020a05120a0902060412060603050d050c060906010503060a1104090213 71
    0x103200034400424220700240003401910101c40212002c0741c4a0200d035130311722034241c0203404000c200300440032410b0070007010354000b4034024031210301081c0d1055255400041040c1c004480842030081c0c540c10030304007103401920480d51340c14009141c13507110008109001c0c100702008511040d64403449282442640c16001520400c4100030344020b01801030401c201003001d842e018140410700380c4403034010444c14200141d4240035800381c0d2080722a000e500c8844d03130407074542c400300881d03443d1620010004500c1d898030461200e40c17010407800c580700d030003140417984032a01400000342c503180c40d03442e41e400e83c0d00413140000040c80020301140700305500007a6540190300c25404021000c016400300c0d285200741d020709010804449080400c0003050f412540c0078551200540b005500765482c080d041d41c00c000300c000880d015000002d046018001600c604a800003801850715840302480f0900810340ca20070b264000608200224000e41a40010414443d4080720000c84501e0b10301c0c00982c40100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 992376187 1250 992374937 992374961
    0x6150c030806010f02031b0c0d0b0610032a0219080a09080a020a03170c12090f100c0201053007030608060f0402010302090d060e0c0901060912082a03040801 69
    0x744070310440204da400405d6405507880346100b46041400d4000103481d0003d034280741030f8042d010780881402c01000d076145600854099032040ca0710300080340b007078007a208407450002880172078900390060381403c200c2c6a8090a0280141c0c0c0c445140e01403152900349101074240c9000701c000800b2040b0315404640c402c0200b185a02920405110ba400204c00f246907200203020703900c507020605d4141140780104c41d2030708208011a10740d025204d0341e200e506d400c8041e45a00c21074060008010508001c0c0e403505e102c40c02942d031208160702c80c0e0f005603140d4200644440c00c0c407420300360340d8600b03951050b01510915880200c4079424500107000505072009608441415004002403000e9801d00c81c119640183d42428051b03141c07824400801d10b0130200b904081c2580742000401920300300702140340700040606603980c0700e00340e0300c2d00d0341130fa0b1303c5100b40700314484100400c11080200d03803c1d42c0a4003108156001200c000b006042d11056802070240c00d00352507030800107041011007001d00c00e106040c91 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 992377437 1250 992376187 992376197
    0xb190c0c05060711070b09011b03080108010b0405090c10110102070b04050f011e0b01051e120f01081002130504061806061b02040f090506100f0b070f031206150c03080601 75
    0xc0c10900785842e0346003403041d81d1b81044003090b41c0c64182e028102958040f0700c0c0c01d10359003407404a41802030181c1020711400d40b095107000b100b80010300b440e020b003d20410300d00e0000d09011910740107126002c031003a44503804003e2103a404130b280c0d582c207000404074103001d041d250105091070b04100317080c18400644180260324049030381141c6244071100765030450f40382c040007500e511050300589152007003108105039403500c0000c100500c1e01c0030b40600992170050140403116919a021050742080c00e009079884c9a01c03002c90100c3c1460340760006c00c40e501548050320172080c0e450380407405940440e00320440f4042d400ca502c0c94400200e01c40d9030001c100a04d4158492640c0c20340c0800ba8014040b0003a024a40f070341382e44203040642d80c228000d5113a1000403a4040d10f0401034001450206004403803846101740000640c2482e5201a10007142d0442008030480391950b03400c0c0e034070701000141712908648075480003031101d5001c80850b00c9404070f03440f401c40100c01403800400c451401801e0303a06000b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 992378687 1250 992377437 992377457
    0x20406230a09090317090319050c0f0109030909021305120a0b0c070b0601260c131a03010504020c0a0c23011718010e07081e190b190c0c050607 63
    0x2e03500c101c0070803641e0988503003217449881d0a00b4850552080d900138044460200c43e0888400364018020803c440d542010b0303070101030460314114280d0b104805c0c00703000a6484001401000c00590081004051102c511007420f80c0e0744000c074100100108d0b10700c0d01604039401c8502480500b0031010f82c400303c10801c1525140c035a81d00c2d100f0030807016040d9070410061510b40f440030117941140e4104040c00144106161505501080a950002c2e66110010141c86000500e01c240071081c80403641480039060f05507030814007404020741045c64062400e200d01160f21000c1847e100300f40000c1d044811915404058881242c81c15601c01c0050701c3c10044016191007604c0c440c426a20380003408400c015100d4180042c24030301505507104500584d018480b40080c1e03c850005540340219056080c0c0e0800c008940400c03503c0f00501000700303588202003028140081c81040b032040e400300c030041340d1a0445104a40c0e02003282c4151800101003904407401c50280141000fa150707010480b86440100c02e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 992379937 1250 992378687 992378693
    0xf0909060705071a040c03020307050a060215070c120e0a17030a110115060c0c1505041a042c010b03070c02010305130209040c0f0b04150c020406230a0909 68
    0x5004001d00d08070400c000480e036901040310840780d20341c100403c00c81c42182c504041c1071210b101c00c8107110880c0709105403803000ac1d2505002410500705c543d00e030058080030b194410254000d10300140f000c030400030211107140004030704890401500002d50342d003545420042c0c050100500c0c103a0040340c284505a138a5842405001048030308180c0c2d40d19122002300360384100300c1d015103c280d10311000c009030710b140410340320b50040402d205180500c04003200e280c1d503030200c07042d12620580c0038000214200014001d0392034102d01c0354107001c1043d002c0b6240c103a40c1c6070956400714805542c0c000e8504440d00120025494a00590140c48519815851814007550140c005030100c1002414903032030304009070031340a003501c025850780e4002e06143c1c1c40b460540b80c41c80354941c1c540038540c000c1d4600800070402c14107900949041d595040f009805800301c0c0c41c0241c480c010900000c9900c5905c89201280e41c1c1401101d81c50400d1485a141d028103d80004000594080350440c0c0704aa00d018094004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 992381187 1250 992379937 992379943
    0x5060123060a05090f0a1539080d1506020d17060d05070e0103080703110c03030a120b1302090f010507020d08090303041a07033b0a09110301050f0909 66
    0x486946400c200b40d90390084004030b00444c110300036050740141c002000144210021440041a03505582c5408c100c03000c0180764441811071003041d0300b5070754150003018480c54005051080e49401041c46a0038400c6001000d01900d1880b000c405800c0c4002108004668041100500d540d01e00c3c1041540710306207910941c1c1250004012070710070482c420045051003400d0241a01501494004464940e141e04003401c15038010081100011142c031a54a01c007000410300d00c101800007005145002c1c00d10000702c0d1b803074a1a209189000e0383e03e03604940c2c40e54070403460100b4040038036009a101c100900800028482c0c0c40700b680d05000041001d000141e81e89010f8018481c0c0c44225240c440030a01c0c00f00f03181d800380d038000c52285204424002c04140420004e401c4047c403075541d032a104128034004956110041a0403100321104203c001413507101044051108030014210210366940c40802d10180d6114861600200c54000010301083c1480c00700d440e0840c900f600e403502542416500503903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 992382437 1250 992381187 992381197
    0x24060314062416051b0f060406090e0415050907090c050a020309040e15010611010c0318060b15270103060302010f030b130204080f0d0810061112070506012306 70
    0x2c800c40014110354401c0c10003290714040c0ba008821a42005801c0c026608810003000845210707189114206085143c804100e03008d84241d681c40380b00c218034000458402e00c10151007180d48910030b0350b0f08090400c3c4c510031148650351080080ca00b051078100f247c030407070782050190410000100168040a40c000040f07503c90351058a00003000031442012600340945c111082d4101c101b034000000d484d81c3d0240b20b886490360b9050013000b50450061068003118001e840808021090032103250119002e54440031000c540900010644591440d041003268000c0743d1070343c01c403000301d8200c1c8090360007420000320f26002030038100700007400c603000a0210510309521030b04041c1c440c000d20b203c44e100d818041c204444521815900c468a0b0000b00b5291540c40c4c80080d014031400f10b500000350b2152507640d0080c002003004286440c1000c40441d480b5192030f40762101c61103007001d40c1c01c0c80585070008224445c000e0700035000550601200344840c3e100c00c0c010165005d80258010403503a29841150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 992383687 1250 992382437 992382499
    0x110406060c1b0306050c040602011401030c050f1306060f1205060102150c160606050102010e01110f1e28050901120c11011d0d212406031406 62
    0x82039852280e50032802d44036540c000400113420982400700c00a44240600f0946031941c000344035404182c0c12072903009800b4800a814000b2a940401c41030400155008400c0da016240f41c0519050034080c4040e94850ba10803000901942032004126500001c483c1c071141240c10240210700381040000d541e61a4121034004400172100441c0c511842882202d4060044a4900c80d40b0384041c241170008108601c9a24099400d085142a0000040c450104861500d04126041641071890381a29400c11503090004990340342c034640310307907940b000a072420f0f486494002e50f009803449868050303c0c044582e0481844420b01c143c0046a8000d4240c0b03000003401180059104c0c410318040f95900002d01d021000c5529000c140c00c8000350512140301e250080b82e0843d450b00141d12400c0300c01041c45401581801c001e52891184906a40c204810095107210100d02221303a080214541c10b400ba44184042580d41d810107a8004100e142240d00c0541100d54420308076009020013020180d509400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 992384937 1250 992383687 992383703
    0x30801092301270905062e061101060504020f130e0106170601030902190311010e030c0d062003221e1b1d0108030a0f030f020f0313110406060c 63
    0x41c0a040509014075504801200f080c041c004040c206140c0700c05041c0c07501e801da0521030322847c9010404146800c1a02403040c0c10100c45480c100085414449101c805000c1c2d5403210710000b196600d1340007400200c203812259654640c00442d825803100503a9001e140340141c02c50041005540007102082c400c2400c0c50219000c1e80c070400120020550958000d47c0500850b040742d100d45c42180500080d00e21406500345031607111030040d52500c000b01c80090781a84654080102800e0600790300a01900c11301012400000000e4000741080700c024110003004404130400c0b4103200c42100d801b40511442032441501d006689561850003880404058240c1c0c0901c5071404204580840c5084a0400740c0e41c01280350712406055840e4401c14601d115440c1a20000f107a5607501204451645030b03a91101c5400695508094001c1c250220160190329400c0c059001032200c1c0314021881a83e9180000da4240c1d40c43c82c20910351460400117074001c9151140c280501e541184208451581107105 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 992386187 1250 992384937 992384969
    0xd09030510050603120304080d05010f054207151404020402030907241707021e0115060306060318080f0f2205100206040c05010311090d030801092301 66
    0x441c0c500b1200d2001c091704044004108000e101140f03028010048000000f402280d9a0301c160000750781e01d500070387d40e104062a0242d00349958082d1030100c0c5016103000760b0218440450b030512035210400c141d001001c030008500b02080012050625a0020514100440f003142841135500220007080280030750f030f0000100e4080c0c9010004c503070041c07101e000b4518051000c0400407540034404040c1c040480c824042c40c1180c200e0640da0b031441404540c1c01022100e80000078011030689100030074507195600c0303072240d4085843d01c0351407010300026140405c2584c0b038440020202d40019070400142000f01c00494009290202100c03007500e210b200c0151107941072040c003080740c807c026500c480e400c07901d420080c050b0200051002180ca0450303d40c2150200400140c2c0c0320b40382101c0040100e0350003181440150300960005040c812020380d40707800c10148401085003400c01c124140d02103440700c0d00411a48000b806007903d1230010813078181c0d40588081c0c00840700c2d181170091030603495035004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 992387437 1250 992386187 992386189
    0xd0e1005120117010f0b0f010c170c0303100b090d03180918170a09090507051b1006080102090f060f0c030409090b2d09011d010e0d090305100506 64
    0x800c0c0d03180201c000350040c50750750355036598400200001010000395402c14906104001152040820f0386102401c81e06180041d80011110038141c050200c0e1140c4110b9410130b00c0903056006040301056800003035603281001016001040c055a1100012800c00c004100d0303030341c42e881140c040b174070b0303050400c900c0304110f125891081c000150000d100d00d61800d541c1041c14080e808600c3ca40902030307950301040d074402981c031b038409110f1602d1510100d0010030007044140542c0c1d0245038031144524140d42004442d0880c20460394140802284c16406060b0994071440c15105410061410000842c900400d440101d41803481c203200480c0726543c041014040400210101d4501a030300741c041d01da8840d141d2801000604502d013096070458015400030304a0b1101c0e20340d0b0b0340041d016900c0c40701840385001c0e026803150001409102c60b9504c0b400d03907200c02c0c031164544401800e00c501c00410a04058951145480703400c440c00760422410020400c0440e031302080c07000c98400b030740c400400c180e681e0310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 992388687 1250 992387437 992387447
    0x402010e012a080d11040609031506180221060102071e03060204080d301805010204060914041401050603040c030f03081e1918060908070b090d0e10 65
    0x58800c050480c01128110410001c500100051084c0c2c10302081a803000301003584040c029400340002042002806001140340020704c00300c0e6000041010403101d40b90252103140540c1c5802c3c0d501d4113900441d00f40c0e200034080a5008807088105101c1d0301c98900400002d545102d035124440702c58900840c0701d0816815004520301440c6c000b0000e55659030b6400d00e2035950740701a80a807002840c644040341e44030041c420381c100501e010f00c1c0e00107800504011504000c0114580e4111001d2840707050200050080c0007600041500e0b448405c8040d2405020b0b011b0102030942180c400c0345400300c103200300400c0155607815610207860468503a5550325100d80c03074840940000c0c000886081e5038208160f4400f001c3c80c462104042d0719a25802c6404031003110b4542580d080e190303200610507030b40d9003441c603030b00000c83e505481082c80852007042e16070380222405240d06480f4032400284400501c900c1152240d000788130b03080105600002d410000305041000d01c0901c1c440c030869a4070811041c0b0035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 992389937 1250 992388687 992388737
    0xa0c170f0316050c093d0608070201140c04091a060d09020a03150b0a0510020a08090d0c030b01080c030616050d0f0f0b03010b04020a051c15060206070e090402010e01 73
    0x17034540e00150400d201000507124050020450030aa803001e28840840d061300751034030b0202d400084600860a2803010b54500a00400d0f010440d0340c3c0e02c0d06000c50440c80c06102e40107000b24030782c2e16039590521510901b035030682000c503c00001c40210404c040d03104d0608544580e83c0c203290000e4030414510000b4048030385580080d02c011001140c454020141d94082600b0032012552010400c2d0350300c0920070140c0041e012000540c00408100004c03aa0710380007040841c000415140c441d900350b94504042041c1da8109031a482080c50042c020b445040010a02e54601180108038502d440e14144c020070070a240c403070b410003030045010a01031365590400000460340b00c80038040d44180c0c90b089002070814a905078030941c20b01a0030305007400c2034800c451031401035070b032124a40184111040e1084440c80c11b000503950780d92510f00824a13a61041e40007400103503020345864100510014201c0c02401c0d002c0f8071540060081c0710060b0f8101c10b100180080a00b003440c2400a030b03d08103a9600c1c0c40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 992391187 1250 992389937 992389939
    0xf0806091b030c04061803020d030f02010b19140103022503020c0414060109062102033d050603010f0303081e010807050102070b0c1f0209030a0c170f0316050c 70
    0x1109101c00c49030304030090001c0d85c5260fa10301c1070350a9042c0c0e071100001e06a21029400910f00c1c000400400e10520f4040b802c01107a00011803040e20b5100071a192000001090042c06040c070001d00c01400300070b1000a80d0502441d05509005810121010382800000b88188075100c0212580c2094001e114200c1c054000500170800e949401d440e031405030b40308561850000d00c0d412004100070740154440c200704d522a01c045180140400c0010b402540007030610318562808240003402904540601228009403084108407c8189203080740d0000d0b0940203c1c0c89030800744018003051400341e0b144030407680c15242004243e201d1800b403581251a905c0e91280c02010fa400119140e100028880300b1a08282c0c201c802181c3d943c2260800c500421f6001856a0040017403003140052812070255000b08000c6c006280858040000e031400010072011180308500c95030030000028038040c0354040000c08805414581401c0e20001e407640300f00f151509003070140139481414000104080c0c0c1a040e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 992392437 1250 992391187 992391241
    0x40303181409070201180f11040e030d0e1501030c0519060203090405070e181611060622050a09033005190608010e0c031b0423070e030105070f080609 66
    0x80719040690600301d080c0e4003590008580050901708e41054031035149191300c1c00003d58180080d506040d0050400c08414903128419440501d600c0894520403d00841c0300d2594086001d15040a05c07040b0300c030035410059002240320302000129000300403942c2c80081241d00044603507403400c00350348155038681c0c2c403500308013003070148655840410708160088058201c264203942c02803c0448a581601c09002c00c160040300110311641400392854402e103c0d03200348401c118401580c180211102107541c64801a15011403078141500038038004040c20006058002d1000c09080044119804002d0304500341d40e05c0c40000c040c0c4a0705000f070000303c00045030500960380d5a000316400780070103071030491880c00389c101a00d005140010705501003508290480305140c410f07008001c001d06040e20503000080912039000c08240500c08480d12030010340d1034a11400d00402c045c9421102d00814050902070300b00d1010040c5134000c40820381c0401c040720a03c1c4c0d15524150044002140c4201c15040c1d05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 992393687 1250 992392437 992392481
    0x105030f220812040501052409071e08101502190201140a050405041103010f030b0705040302040e0a031701060e0d080403061416050f0d020903011b05040303181409070201 75
    0x1103007401080c0154058402405291905400c0e0305039400c0c20342904034003802c1080d42840905140d0f0072281e1100b0075050021b0b01850380c105030100120a03540400000c1d8000341044a41d0337074000140b0015100381c10216440155010b030107981d0308000a10020300d1401154050704581c803480c07441030207240700710030103803035145030070024005030028000c03180300d107007413410304041c042d040003d49048501c4c642009034014995140c0910454000d84060108070b41084044090b0326a405446d2000f0103150040c0007030314a40c00c0080000d00440300401621070742200412003594010080c0028500c112200e2010350074500d40550b103407140343d00051010342041b40c100a1504144415032258203500b120700004d0b0450941141c20344122844004201014072880341c04002d564054507031000003500000e0131a01c1d402e06000139100540c4044000340c3c1c0028107008240d0300403542c0e0100502d042c08042c10301d0a01c3c030000004544000c10500500344078000851203032003504000000f0f261849030000030303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 992394937 1250 992393687 992393707
    0x904170f0a020c0315070513080a08190201060623040e010b040609060302030402030d110f010f0e070608190903050f07031206141f020c031504030e0105030f2208 71
    0x250704403184420250081248900301030070003140c0d0746602c4803102020401d07a40d0300310040c0c90301d401074804103c00130401c0b0004142c0d0300040150100081c040d0440f1519020500c00241d03403402d60402c3c0d03800f1a410841c00700b221640002d12403040d001040350071903c07442d1290518286020365800116412414000000c3c0c901888009005440955131281100780d110340054051340720a0310000d4050f800720507015402481440c00c04075000c01181a1051180341030040d500355030344c00c81900700040d50340c0c100d5980508100203000042016003052590352502c001007014994010f100002855166107565003010700c940c01300c1e0100d5040c100b201c1d885000034207008001c101115800d918013407502c030340400e040324032500748100100020094000f05d5101c80044c990180080c0045065110300040302040d5076042c0548039904640300722407107442c6040d09006100a007155142814003804100b8080100c0040240f1640280d1b00324220304842e074119800580c10f0304404020345080c001254151135 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 992396187 1250 992394937 992394967
    0x60607020d0201030e010f06032612010b030a1d0c0a080a0f0b04020a030210091505030f0411030708030711190819021f08090105010806130219030c0e01090c0f0e090417 74
    0x2c87d0107000d01940354070721440840b18282f107035a600b0429552104010410b40000c070005640c481070a09000c5031869484210815140c008412100541c1110415008604080142038010203414005090650b0540c41c1d03a507100c92030500140c00708044100080645d15540c0507100215801b500340180c940d8000c1c40181240707002d014400403020442070781c0922500c22000e49000d001322088088058a4540d42e4601d1104031040c00d0303405014541d00016800d2081c4050704065000d40034403848a1000703000c03c00d201043c265514a040382060042c011b6160006480b26800c41000004070304207000c0c000140d0300c03a1100c104445504161030a4021030b030b0b200a6081c000d20b0050002e01c0f059894901854030f803403040307400307800b1003040a02c180050318090b9200a200c00e14940e0b2810b03d00d84940343c0f240c41c04a680c00c04103000c91440010050038260b403003012441c48051034040350890600c1002400c01c00e2101c860361140c840c0401007014004000d00ea0070f0500041412999900029903030380303071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 992397437 1250 992396187 992396213
    0x19030e04091217060103150b03040c030804061d030703050d0503100e01091a0a050907032a020304031a040b040b150d0b060f090907171c0314060607020d0201030e010f0603 75
    0x55514203c04908035500130f0086e01104411007981d51201c600b446403a20581c1c100802c02e4070f078840e40c01000030100d010100100301030036030307542d804101c0f0070456003400300c8007007440c61103000b80c0c41b60304100041360b0046050b14010b0303003600d000c075075940310741041410300112500607100e20040480002105000f0303a20002c06420707901c14124905600030100179041405100f8207400c8224039000031022032099008003205594501c0303030104034064000c410210070f0f10254060160340000f600f4000c0c8041d0400310b4032141046001004249007556454020742d1014100411960006012a10084070340c46032080401002c0c080c40c55036106070605150488082d52101d0080320100054142403c0013401c0600c070392640740c010021b607403400303042c1031048214130724540d4a4003400d035600d8000ca056290b90100003080f5580400e00c0740b00100000e80c4a40d0242182d171140d402080714500689541c100040d600b902401e0000d04c5030030103110305000d01080707071080c01e22515064010040148000000c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 992398687 1250 992397437 992397467
    0x90e090c0a0e15061308010908040e0f13110f0405040f2006090d021801060210150303020a330501030606050117010e070e090a0b030f19030e040912 65
    0x2208080d03031012040c4140c01d082e107460803540c0c007183c0b0f65200c41c104000245001c40480440d40d024596610189084420b000421541c1c54030003e4200a4103a00c6900c640d040740c0303183c4104010381068007035940710400201005180b203210000c809295034450710501c03032008028000340b10038503241c0f40139404040e4040c000c40b0025210078a9008140d5501c41003141d1050141c00e06280428090030403e0300e9074a01002c0764042ca01c0c0820341d05080c03088180303d000305156001000040c8c00c40329180300340e0300480c01191902d030603d0070070400300f68001034981d0130701e0b080340c070800c50189030b08042141014098207101c018180c074450401d002150364403d034103ca0290408120f815261001158402a001044001d03541d080d0014042c01d035150006503003081e445c0c1005503580d960b078400728038005801c0700c040131240d80c3c50b0710403001d506080c840e5040f40d0303d0280c040c202c0003000c00c2000c107240c54403540140811a4246984207291281c0d4080340115800000080b41e4a00881c1c000700590b4044940b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 992399937 1250 992398687 992398699
    0x60606121a130e01111621050a20070803121003020619090504050403080405011d100c03020f0d0b010f030203011a0a0e042c0a0c0e0601090e090c 64
    0x108405095a400358a5000010010321200c0b50380c610140203404503035021441c80d540c03184028840d010070310092641c400020030607046050030341041c0503c0c441c108a541000c03112404001c0200d0741c0403084403221400743c2031007a9118a0641550b520001da044c0000da64428414041501180000030300440d103220400c40c20300d0382e504901c10010444510000790005803d000c03d1456031020f50104114110f5454103800341039a907400101a0344003a81d060307010624135400d00c803c1c01820b02507030135032150280c2a00305a501041403e640e846010f005000c609a841c191024800c0c42501100c01500141d134a240d201e0b130b0406040c5004106501903603000c9040300e02101e40f103501a00070b9038101c4010309801107418880e404d2500c0709a1042c4a418100061006541d2280d0b44903c02c06480d41c4074102002d90002000d254605120107402c040c3d1102e80c00010f103000000ca24905e01d8041e40c3d42c24103882040d480d83c000503141071109070030420140c0710300d00400622820001d8203980c894412a10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 992401187 1250 992399937 992399951
    0x50c0a0209070e120304050d06021e0d06090b01020c011403280c1701030f030302090a0e040b160e0906040c0e030d1805040902010c02010c080c030412060507033606060612 75
    0x1003141c0c0c0303109621487e0b41103116690304d1030108000354060030303039000207150490800341380c400ca4805d03d90124840124003561440207110040b01c5205a01204400380010210000c0150001c1c00b1000700c1e06860345405000000500148403031a420320700344040300c601450035814044000050055044600c001134003104d0100c6250100d20392641c12030f80c101034800c04000441d10110041e6100701152600421600400641b21480703c40252045000b1008101c050421041d914003a54820101c0307020406110412825584d0340c140c0030341c0141c400c407000030380507043c00420f4544c02034260002d5031602640c500d4050407500181031a580c59031142c020488591100100001c4500a5001030300041c590740c21500154022001e001c4858001e001460814150300016855580f16401a0700c481620182c0c2901b0400f180c040c4680104c0b650a06125644a1070300c401d5284000303140b5040415071041c41c03044502c0b011000c1c80c40c25500710400307010782a01c03248040c0002a4542096094508c2e1000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 992402437 1250 992401187 992401219
    0x50a06030203041101180b030c0f0a02010c030605040c0e12010b0409031e1b030f0e1237290a06030b092a0120010507081015050c0a0209070e 62
    0x12406d08550382e0460042e10b241810240c009503003004100c041216800c01200b480350140c24083c0c086d0a286a0001c21010801000141550281c1e404140240e080400d09072000790440b0400f00c010341e003552654250001080c0d40d6003d41550300d24550818545080c0c2c0083c1548008041c004602042c4001405990740d40c04948045030b050031081c15800211410340044c0c0701c0c200d2072400d8a160314002300030010f158005181c0c04c60348064040310360b002d00c00ba043c4054411032014070640d100310f03409081568813259100000701e400c0c2c0c01008981c51111130a002d240c0300c2040c1d284c7c2c1a0398018903101d0f01e00384804000601c99070100380d501c82c43ca48005204868000385007070326208844000d03070124005084480e11001e055000c00c0c140b1010030024948003010200100c0399010318000801d56043c2140050a41200581405140100141c043c00b40c1c14030914064003510306482c103180d0724001156103078106030f10024001d41c00134000040c001041d40c80807a89040d0f9100712007009280b05450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 992403687 1250 992402437 992402447
    0x203070c03060b03120c15090f100204080c121902130905030a080105031c080709080a0602040608070915050702010c080304061b05041a090d1a16030b091906050a06030203041101 78
    0x14220361b100d42e12042008842c04646102240c100c0400012a10400c4448100038104110411050f1381d41c2c0d07000c241080303000410000c6062086013560402200400d40020315240c07191102d00d00302c8464030b03004150031034558441d00b0000c06500301040050050500d0220344070f5110503820130026180b140081680c0ca004101c1900c0300348034000040744000070314403d072102c1174020665014890608800683e41d174090004202840c0b01d120010380c0d0f9400d00c00b02a0030214080c0204080042e0b42d40280070f110b00201000307503048014204541c440c1010300c012a0050300d011130003000c002c1e0100c144400c126003508401001301040380c4024a1600c0741408a980d4052441400303803961604100d400411031400c0146401440680317801205503c2d85c507074a4071615101042460741e113900d4204504980c2240018002c04414a002e0001458050000e0340782030001d4050306004036540f02e5a03000340b003954010802440098012109035a648401034000d400440e010b6640c1c00b03280c076131009d280d8498 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 992404937 1250 992403687 992403697
    0x5160506030a0b150c0109170c06010b0d020f0a03050a110c03040e060f0904031121220801060f0509060306070219031206170f01050609070c030203070c03060b0312 72
    0x5000141075603100091640a840c200342d159800410304403001004480c06002062116856000400c11030440d00d0071041c1c00c50802e0400300c5030901400340c00f146c124042420b034112141c00c9409601c4040d5814440001d100d200ea1080100400044031898660550082031151000140800040100c040c2e11200381c030510300e50301c4680d04201b00c1404a1404181c2d541c0e080300380646130001d400c1c000000301303003900c20540d015400b007200c042c03030505014001c0004500b5014440c1840c24020082104854140a0100d4081c254004215080311010303c0031000c10040000f10300034000751b40d03140e0040c1032118050180501500c00d50000440d0f600340041c043d8042c107010b500405442d4a1204204098028850210100321412285203c01c0c0500c1c000c1c50043c0040141202c60041500c42c8186004140d0741a0701969040a0401003a641c4210781140d001d0f138282050320408210b49001c078114801c0d00310080280d04050004001c0c01111340c4059000d410550881c0e01c0d6101500b00d4000758052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 992406187 1250 992404937 992404939
    0x41b0f090c18141c08070f1e020f041802150c0727050c07060c020304180b010804020111120d05100803120127050f092104091a030f0a051605 62
    0x1503019420000d042101884460f00c1001c0e0b0300d2402c0046665030300003207902c83d12003583c82c10010b98007d0144428140400f80040f103c0c1c0303204107607100d1640070500d0564560700140c070482d80c0d5502000c98601075a502c4140130785c0205440c1003a00848180c110a81051413442e41c24400c0300c0340400c0821041340e03e100000c0c0001403109184045980c2c0c2d00c09004014003031081d004040c04840d000540900625000020380d4000e144c507281042c22003003450122a0407404454182200c2c5803640e60461500c5400540a1800360304030001244820315040f01009100466130000401c440a10b2a80d070200e0b00654003180030450340e569402e074681ea64065030110350b1880c1c0c2a00b00421044c0c454070000d2000c190f0003903000221b99100c6451001f11102110080c5801481d00100101e00740148204038080c00070107500b04e204003200015070038a0040c1c0c01880b1010307275981d94a0141d850100786010420000900300c401c802d160b6140341d5180e43c10b550b000c0303c540c0300722140640200c403036003982000c4d640 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 992407437 1250 992406187 992406209
    0x1303050c06040b1c020f07080a140f0a0804240b1804150203041109040f0201090f060207050103110c0105010303110607030b090a0b0d0c0605130e0f041b0f090c18 71
    0x61134098140c03011441c21640c08209908204909001c020b520262610742c0c0540380e62521100103c1d0302902c8200342c56102003403010b003000b00e02c00c41d282d06400c2d83c1c451001c6140200e07980d5030b60301d019103114080e912401e14000b000c00b001441e4a0a9420030ba01c07210b420380d00320401c800b01024404541c0010349009182c0d4180343c01d000e4140311141d0141d41d11070f0080320742045a180a40119085000c159025038100c1d84508409080d560842c0c4010001d00c1c103107050031090303841c0100007511a8498090f80e4101070701da403565000440d411055951100c1040000c1059580d2443d0150800034421490b4000d0300450000441d254028850a106a40090310000550307440c545464000e10461087c164041941d0b070106001c00c3d400003040029103201e80ba115074524004124003c440301641c0000495034012042007030310100c004095803c10381c0b01c0540c25074103102804040124401c3d412903141c00c95420000140d81c0915044412450cd01303444809003903a5000b4170105041140c024001604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 992408687 1250 992407437 992407447
    0x9031101023c0c01051926151f12060b0f09150307080c0a03022b0f290321030709050405041101050a110a060b040605032b12021303050c06040b 63
    0x14942e020303c80c0c0301c186c040c0f030510021175200c82d0a0468925900220102c0344621041005140000d0310b516184c1108581c006d518543c01035901295140e115174820030807140052000d08080103803c0500600035000c504c503148d02d110031a5100d40d0b08034140d0248201002c14008011100110442c0c2c002e41c7c2641e40c0d11950780e51821030304c600703070310001c02c0008050b404c001c0c103020a0f0076291006000d055008400000c940c01c2611202550000529241c41a24081c003600300f07608242d1b210f1030108007003440601022080d00c000381c1846080e0690707503040300c01509052255200d4000447c0300e41e0f01501e6403407060b80c0b22020700c001c59074102c6000744a0318106004007603c0d0f00800203407180644610781010810701000440b0b0900700c401c68115121a140e44500200d85800e001d500058401600140074200302d007460031400381000c6100324000022aa02c411041d4810607241028014203001550703a035440e00c000701134400c41d40c0300a43d10390041e071103102500d1601000b15411541880200c41c240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 992409937 1250 992408687 992408707
    0x8030909060a03050a023f060a2702010e0310051e040542180f070b0c0a060501170607020105010b09120c18010311030102070309031101023c0c0105 65
    0x2031a5021030401748103144100401c2e6083c0d4030b0704918491100c800c00c0450054110001f5464220b010780860151402d20004c807684145a894201d116844040c5164007a40240016900c0725509845903425001750b0381013896502c034a4010602030002100c0d00b07079600f40420103044030584290781c001c00d00d400c860703d45071a001400e955400702d81004030b100300c0c254a0060f08030084101e501000c5007d039071800108070840b100d047c4030020340c0c40c40901a04189082c104c1054441e03a541c064400d84010100d02e015500d081044812115030784190304102c15610750440510f0801c8074084400103100b8540080d0381280306010300d90403900c00710080c07800e0000394020400d0301c0014001c211114454901205241d035214900705549200305038008a09505605004041044803801355000303070300400041c4002076100c8a00011a90809880e005508400380100c0c2003d060354400200e0b2080038110821400e000d40070810502800c8a01c11014600c01c0074154840f40042006c902061040c000c040807 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 992411187 1250 992409937 992409949
    0x2011b0201200f0111040e010b030c0d0228030603110d020d020301090b1f0e04060207061407020106060e0102120906090d060509011a19031112010608030909060a03050a02 75
    0x8594414100768402100401e4807040800c2c500c1124002035000c0c03603180208100c20700c0740140e0071602c0c01c046494030b400c155022800e610180300b805881c042c0040000c003500d2000d0706451031482c00788400c0d90f596030000040c2152440154400c07000b809c0d001b07d80104140a0700c110300440c4c0d4880005c4481d555013404018403100f007160240d800044040c801c83c010b0380c082c440c442c1001e21902302c1c0a00c50401c03002c003101c041c101c04100c481c03c02c100700c1d050280d954915005035002c0e40c480307000350b542c0c441e5180040207441c80310445a0042c11900a100c07144d85c040d0041010340d8880d40c4c1c0e824848841d8001269101c86420b070800d8005402c004944075420501d00400c082007019003105580701c09595000c040725411504075407680d54801180c2d200900d03019605010000407107800000d42c10f0200c0342c0b85a14170602c0001c11a42088080340d0301c5840301e10003600346400081c000c1180c546d80303545040c0c4a038040800948903a85807400107005282141151301501e42160041c800342640342d0078012 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 992412437 1250 992411187 992411237
    0xe120f011515091806031401050109060b070506062106070c02032119021c0320031608070921110103050702120c0703150207030e03010b030c0d08090904080307020d0c0201 75
    0x400c29403030310b8011003c071f80201511080c09102000020f62903160804d07200885040750012000c52000300f0810020030390014410790080710494202e4103102810440b841c49034500c3c0c2540b03116018140800c80281d401403a20410603000742c003a12031107010054010751001881c1d95203c807584040c0003184004c1d0801d43c2048240d0241d00407100b1508042c4207098016601101c00ba0020f03440784495840300c42e044501d0034000000942242c10344c01e04070100750424803481103520030014008000740c00d4501c100a0500203100039184420341300d4002000012741641c5010a40310610884114030640d4840e12456114101c03586c064200052500c0d00018240e0003081518114420301102001243c8042c00c4451001a0080f00507640e206e1031401034241039045544510a034900046408113460210b098040c4020441d550f8403181c03032510b802c00030340c090380041e11b800080f090204010032460100443c0a83d081d9003c840400000b51401c070b40941500100a00044074001b552622202c4240425 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 992413687 1250 992412437 992412479
    0x120201270606091103041115030a0b040b0907020c01170c121e0c070212010903120f09140624060406050d020706110d0c0504150e120f01151509 63
    0x20515642d40c81e021016a91218072030425020b00200748010400c52001c1c1080f040800e03203404180f0241d231107030348800e400010210040f694444a00001c00c1d03a690340308036031528004125265074141501c0080d076030400000b01c1e5000c5503d1110003d6080a44000d41e4494107810b4070541c5066036402c0a0119044d000c0e00c410300f8450703c400c0d10002c400011801d14490f20300c002030103841c4d65480c0100507045600d10b8840282e0b07454444d800c00401d903c1280c41e4443c0b100650003294541c85201103100410341040e0242c20f07001c0203a142c201003c0003254242c0500d40c81c603075040850003051004541c9040345c3e4038641c1c3c0100b040100304104c5010700003410b800012484010f041c0003141e1070b00410b841d00500901089580004c1440030995184150303d01c0190601d04207061a0401c00150a20240c1480e00024030408040030b842b242d55154212400c0495841515000c0c11248441c40c0071b00710400c1203001444200401080000d00d00c0120103480c20180c0c2e03008016860070301d6a4041e007081175064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 992414937 1250 992413687 992413691
    0x70803071103160315390e15030604060e13020409060905031b1606020a1b121202010b060a02191110050d0605010203070209072703030302071202012706 67
    0x1400e50700f60107443c044000e5014040900440c04000b90300720481e20030070340b4081200c50840c0e6803a441c1d0140c801da10001903401c109045000c00d440800c0c0d43c4030884820303030f6500c442c6640d40d40074010404006140110800c0d02c003400b5040c3c655050002c4403001b201c07414404001440c0702d0015113026004014000d000e50740004007902141c5502e420741d4002c880303c01c0c0301401100d80050b1300c8420000400034007518412640e0382c03400e1100080d290b074034410018122251000d4003045001e0240388180017000c0031284000b00424516103001485481d0403410055440c4c0094521a030420008035103048030154081c2c180d485050400c000b00300e1010354181c410032120401c50269480d41e0440f02c001d140c058803855110b540119400e010343d600341d000241150802d100100c0142c551454aa8000580f4200090304c601400400c1c048041ca00080b0000640748120000500d501a401441c1013405110301e44404201c200c07007039082c0d0711803012000a640168902d1038860300303802c0c0300d90220b078812480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 992416187 1250 992414937 992414953
    0x40f03030b040609050c03160f020c0d050c04060f080606092502070e0c1b030705030327071203030b09010806011206020909153d0509030d031d070803071103 69
    0x2c0f4004a482c00c56806c00d0300e6900000348002c5c102041240134011003189003107090b5182c2a20000c0d00c42100c0d40d451409146440b403c0c1c02003241c00d03c900d122510018108018007a40c03900c09160600310b9214228a41c0500070101e2380c41d043c40200c00344a05078001c10304080c040038480c4100100c4030081c031101180140b120204041220002c294011800c20811548803003100b549107021844030301003490f1340d80c02000280d0000d00084203a96010000e0610300c103922070b046e800c5188010b011b4000e80345501660301d02184808a10b508449550700a5800f0001e000b129001d00c1303003004e0280170314001030b032007640104586407050034156401d80c8185005401c0c40010700c0407808100b81521030903c48203900c034400c03000e070130070300342d00d40840d0a040c980043d4414405d90349200715a04140e4540191003000703402c62014001c0c0b089450242c0301404540f01c1d0300c240c042c020014580e6243d0103c1904800080362454140000c421017994100c01c00f40d4074040452f615100010b4590190700e41500505035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 992417437 1250 992416187 992416199
    0xc17090f06071b0c06111014060105090a08060a050a110a09050f0102101515021204031b05030f1005061002120a1b03030b041538130f0905040f03030b0406 68
    0x4c1e81d070040005403152101d003c8039400e61818640c03466900341d285032601e200100c00b162011003c6070080c0d002e0034465581c80c440c0c0d004c0b0344400b54541140602b8030a8400380007840d82c3c80d81c469841141c407850100300452404c1c1c0500042c0c8130391900b20000034810101405585814580c40c1c00818050040780c001c22030200d111000c0d40d24480d07011168917840c00c010840000c40a040c080b2042e039038809001d5640c401441010725004a000142c01c0c0034650401d103428280c4a030105000d0200142105c1c1e40c40c0c142074031180d940580b01c2049004034108408a40d55007045400c04c0c02c0c4c0d60550300074041990922510006640080314520100001b8412a41c0c1100d1041008c481050181d038000c82e4201c00f00e011300083e20075451640201303c0e01c4c9081040440403110390b001503016100840c02085d150a9203070021b10071b161002c000d9500e0005440180f00b68881140b508a820315030920940395a162031402c200c0c0d4003101c02403c51383c7c6601804000a00c01c0d481414407040041000804035111a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 992418687 1250 992417437 992417453
    0x1d030909091f020903010e0105060a031502091c03140301050a0306020c0c1002070303090f0e0a0b04090602040f0303110a05030405060a0c0b0412030506090114041a040c17090f06071b 80
    0x742d00390180754001800c5006040a004950000c10801e000740624100f40011a000030b1642c1310107000400c003400444090030305501147c1011100a100300300c0d0880300444848a014801c070101c0101d040c047d090300c0310900c500252030490310000c0c04019a5451515104041d40c401d0800c04101d004194405800390744135007402c100295964014400f407400c40c5030180481482d600b100114900e200020001d0001c0c2c2e8021a511907851035010511040d4000842e0181005620080a0394004240825a215400d19400449010b0f580c1c1c2e521541401c0e851948400f5081b1001e0a960030410041c04181011402094044410b01d45a140c082540d00c80c290803000c25202190296107003240d4803007ca9060080e50303013240f0f0449454444d94036003041c91080f12101400d0501941e20b40c4030010b400c1080750082c0182d10b501400901c920b0729208001000b01204140e480810852140814100300740000d001e126000107000521494681001c159854091500515501c400700c03140303000016645 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 992419937 1250 992418687 992418733
    0x100207030c0215030702060f04021507020103020d05010312090501050f03010611150f0106110328050c0a05100e153409090e0c090c1303140c01031d03090909 69
    0x40f40403140ca81c00e08540081c00d0680141400302180344070802e00001d07a5407041c040491500e41c02c0155512480303480143d01a002d0301c10b42e503031440e2400e0000018030030030652800079041a6a40c00ea2659181c3c1c00643d05e5011f0142c4034a10154248014807941e030180b031410301604030220840d00300000fa500703030f02142101141d00324414807860780100140c0c0d41000c410a1410b06410107103081071000726220f103207804181c0030400700c2300300400c0380251140180100d680034000309081e03410305001030800d0b51b6608540000500341030b07d05450400144008650a0444081e6049044041d100c0003c0c400d003401c501100e40b448040700c7c00d500c401c0041d80f24203d240804564458980d21440d00c48004c00701e80d02c00c44450318039080b00024850325a90203034203c0d401255143e510303448041d98446004451910780000300058902520074404201c0020800342082003640c0a2004c05603c448401e00c040d110062119641d100780f00c01c0285150040001d5840030300740044a6450310640840d280030700389 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 992421187 1250 992419937 992419969
    0x60a02070308010e04061e0b0a140102030d150f08010603050d0e0a0b030405100204060c0b01062a0f080309060a06080102090f09071101051305070b040e011509030804030803061e0102100207030c02 86
    0x1481c00c40948c0d81c10100722440c0180000744d5140800014280041c3d224030405004840030ba640d19007a484600c0c1110203040503140303140642c00b0054990070341c180205181d00050354581b00c0c1c2c0c06600d2038103114030040c40030b100000d02074841943c07500c0d40301041b82e000900100c0c0c0600446030591102e1195102400042082d81e9800440c40004d0501f1002b14030180c20201c100403503200010007901d804189001604c107041040c1003142c0850030180341089074014004d0006000009006071410006802806040200010498a55201801401c0340300e117004030780d04040340307201488981ca41000708076404007190804801c42c6240e0300c1500d0031031704111a41030100e0085002c01050181c2084106c000d440d060203414a8141064000f240307c440c140300e080400d0100380d8058005030b2240c040d06004650108400b0780319600c80c945031140d03230404c44a05015a0ac120080c0000d10100c0255540e44481a0050f002c275903c0c0003031080103540031000681c1480f81c0040341000589500c01c3e104402e6034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 992422437 1250 992421187 992421191
    0x30212093a2405070905190504020a11070807050a03020423090d1106010e01150c1e14031201061b0503040806060f0d15051e0403090503060a02070308010e04061e 71
    0x15021003482e81400400d00072420360307140c03070304010b8182c0c1c0100302281a900c00700c07051035440541c01c0d40300401100c02c0c3c103e15001400400e038a50700c40d812040b200711100212041d20760160702c401d207580e80e5520503c602c5a02480004d410000340c14244c4c00400802c42c0b0129000240501000741c065030380301501e5040303080c4e111046c04920140e004d03144100c400242c00c080c01840d458000762143c458018042c10150040c00740702d900d41d25000d400204213135648601c0318031920950a4110601610411090702c030a40c40c551007000d000310110403100903024a81c0c8105190342841c3c812284407440e0a01e07000c410094019080c042070041014000501901000700708130729002c000e002e5881e1940714102d015002c13400c80180056411041074410b12480400050039503160020f14a40c01070403c0c046040c18071850a00050580c0301c405002502c1c002d8080358155114052034004a101d020405070001d01e03182d0040c0b20260b484c3c1c0c521500320f4080d01d008103140c5410a140310b0030540600060322820303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 992423687 1250 992422437 992422463
    0xa020919090f0e060f0c160c080c04050c030712020d020c0736020f13060c0b090d0c1e0501180615030206090d0c0e0a09030212093a 58
    0x401c95009504006414041c14000d8802d4840010f54030a0301604400191110320000b0740592003010a440700407840d0000003182444e24105000207141501540085000e00c024039a00c1d07040500030784e401041d00da041c691459544202c1121f40f000c00780a40c01c1810307000c0025052610090001d4400015490b0180201034506030404500001e04000e240f8020070010744014030b042c441c100e00c012005529400b503034030070828002000074411004040007064204802154565002c025000341e10700c5070144011a032a120580395440704c0c030300c00580000e14880903040018030407485200c0a5200d0b24214218107103181d4415013034802d405140062211260003000c140b100c0d501503481500c45a84c106000c00b4255004a0503501c03032040070a004403440c0a01c0d000300302c0c6000e1110020400f82d2812003141c03d24500c900301a2441c00010340c010312a106010303e144403a20211104040c00401401480c140207440680100c0ca09014265061241821000b41c0d60540d001c594420f1003218903030310603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 992424937 1250 992423687 992423699
    0x10e1b2203201f0e19120807350c010e030d05061011070603090f06090b090c01030e1009081608120106080f0103260c030d05060d1a0a020919 62
    0xe20f40c0141c0c01030241003102c852010298000906020b641415034111207104c500c00c6003003061800e9648103509011084022900b40079228001c2c006c0d49110b074155290b616019000171450070311180c00c9600c0c4d0f4050010000107400c504000300801c6640300300208a0341c91000b20030381190400072503c1181078540c0100841e92074000e64a1400b804c0f6401c0c644880c00c0c0c18070980743d490304903014a00c281039603a0061028001c20100e0743c1d2803580d108a007030252003040c0c81c1c420a4400300f074507404420b206001100d41d042d030190040e0070881415100625501c032000b0407600181c00c58400a640c090010004541542c07401f090980000f4043c00c900c42e03940c07401002c444c841040584c048801c000c10340043c0000e1201d107160032411280c00c03521840e401c02490322075103403204e418180490901d00000302c40400344404000f86c640030b02103420070071080d9140b00500c911516030440080c5880c0040c0051041ca136040403015404c06510b0b0801402d003807800002c2003961941450003104a40002804c01074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 992426187 1250 992424937 992424949
    0x20412030e1516030c02031f0b0d0f290708010f062109020f0613080c030718090302010b1206090106050a0b0a05030a02090d0803010e1b220320 63
    0xc0032040d80c01031104898202c60080074040d255218109140403101507084c94403860007244415002802e42e001c40303520304801038180480030040f102d6507051600412951401d1481c1c0c80d4400e800c601c4041907802140d4542248412511403d81114408140600e0b010701a4038014071903080744e21500310f07070350500c051a0003010a545c440c4c0c003080f110120702e45a20a8456816481c0b08002c003001ca0f07600d003244009032441d0032541032142c001c9000f0a40c03514100c902d100040480750300b1000c0c3c0c2c1c8040108001c0c581c0321041c40c01440032140c1d46146c4500f03c3e44490b44201402c3d8080e20001441d00000000900d0030301e904141040a50701c4881406402071003072080b10014001180e0082c42c03c0d1030304d44a40f83c14002c1c1c40403082401800300000390b8040709a0116084600c0041c114500c5040302c0c030740703a1080d8100380200d1800c4003007040054001d00c0084103111005000601840c00c0400240c502c5103d015018000c03e036103072451200000092200f86600c55091051085040b020401c0c400c0c042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 992427437 1250 992426187 992426207
    0x30506091e0a1110140f0406110102090a05060f04080a121205060f01120f06090617070f090207030c05120c0c0108100918120c0b01050d0b181002041203 67
    0x2035541c002d40860000640a0b100d0100d40700400d03a149032141e0649502070701c080e040303403003585070364140000c942c594001c3d07170b60051040c1c804c01d4440c00f403070021489d40075080f8000c510700700707421811058040c012850400050b01015080b029240e14058070b6a4040c1d05103002c1980444003217400104102c0001c0d0040042c50714240d80134010400b515019000480400803264280d042c00030318503c0205001c0d00e1740000c4e01c0c2e107000090034401c10340c0c0c034040d642c01083c0c544a482001c00031916150440f10021031260102c400381001101807a0401240200950107007104606016101105800264050018840e042030b0410840d880d0b80d46c882509052517140b6511a0400cd070620800071882d400500c03010550b03210081c0095000c0316010100350030f01030100d000d48208240041c00c1040c41e4002c00c03101496210b10b40308181641ea45081c4103565441d140000e040203403e4000800c9405100701c003c074401084400c607207410b180700d6040c800f00c0c0d1150b00241c000c00251104230302490f8122944e01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 992428687 1250 992427437 992427493
    0x10090c03090c0b030f0411031006080a12050a080606090a090f09050d091d06030109141b010804020303070b061c08031012020d0b0709030b0f06011e090b031003050609 73
    0x54951700c0c080301801d0030b00000070b20003022180c80304204406510104038403d40040340d0ba108020541c1c032810056030700c400031b40c81140d0a103d2554107130751507489901901c10100150712010b0f419183e0074100019030304200304450b04a502d090300024291030900035065001c0c520364000903026080c2c00c000d0705142481030100c085c066101300800640b0602c000b150000c10307404e20002142d84034000001d000d80a07580020307001c0000d84985c600c8020f4003169001e6000318008624156124407401528920707000c850107035041c0c006201c1a004102203120307059000c00c000345418030b6611820780320031001c100f50405031860a400310030004407070001c122207030107400b041c050700d007004810340c2c0014401d40c09540000d00b1a0442c01c0810291030003400b251024607130013500c009051825008500b20300c0401c83e4070a000600b507071000c02201c52a43e100065031217840c5d5603000e50a0521542e02425071014241d94046210f005001000c24024404107025007480e80250010207881816000c2c4007043d94041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 992429937 1250 992428687 992428709
    0x1e0212030705180913060f02070206040602030c010b03013b0f07141806062d090907080103031d0a050301020403030801080706050316080a0e100b1311090910090c03090c 74
    0x201101d06000824500c001b80d0001010804020f1081c0174000b03400340803002500000c01003008143e00d038020025040800c3d02034006c2004403081001c15080c1e442c0030000c82d058488610a1b5402500055060040f040c2c54032a02603520329001d01c47e42c81c080a80107031a03a1500207040600907110300050030044181d04441419200c40e070308001611405c0080c2c0190310880f40018003603245003620b0080c201585481c480a80807103402e2001c03402c10b40c02000d026109824420026818074013600c1854181d0341c250f680c800c0a144001d94210344810304a0141e603004440110000d4a40d80900061024505c82c0e940c0481c55494410110b01c0c0c1166a0003000c05d10909004000c1038042051342d8100003900c48c074003810103032a41114040100f0f022407003400c940c051982280c500b4025908500091007060f0741451001c20030000b000c00301e0708010020411010100040241803503d4201250004a0311340480f10b01951411684100c400d449804800f29031209c003a0303804d1040d1519081c00400da08411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 992431187 1250 992429937 992429941
    0x5090303030126010203190e0f1b0d210306080a2a21030f030c08150307080f0d09150c021509040e01021e07031e02120307051809 57
    0x40c0c0c0300c0c08140103c0d520000b50401165040700c04070310f02648460b00c00001c660341c2c108031003104501055000c500924a0409988180742c650000e0b05515170484903000e030201d40c0d03042103041805411207803117130740c045040205803002c10415402e031103000d51808800c0385031201a80011341134800035401440c5640010200c18045001405e602c140100004441c0c480b90150f02002501201c0c10f40001080c2800102d000c0b84070503100a25650890103910b4055068003030241c02c4080d5040803800e500020240008164807800c0881d1007419940001d0544d881d05484410103481c0c1071103024404d1150b403080f000c400c2b0700c2d6000140c000203400e88511801d5050420080501060b203003041c0280a0085103003803c050b131007e0019907625040c010014442c0f40c1007a04140d01079042110100d80041101071042619901c02e012207410316031544890303445008d0400c0300880b10300c000c0301a200358014440180700c0b6801300002940304500b15192681ca8140131444070340d02c0c00301c1d41c6035a8051751060301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 992432437 1250 992431187 992431189
    0x131e050a05100c03120e010c0201060b0f09040b3d090308040314120a020304140a0e0408030a11040f0602060f01180b130e03040302131401090b0301021e0a09060509 72
    0x2c44140c40070300c1400c0010b051403851404803482804502c070600050302d41200040b002c001904a65554015a4000e0108d82d0311044061000d210f848580f07003124401f0401414142400e800c40c42c0802001003107002d00c241ca01c00222500428501500a4454500b80b0105442e200c10165420881e1a141c100c013250708665603071350240309a00004d850403100000031107120710200300c241d201384400d911690304c1e0064542d010b980d1b900f10b80240c000c100c0030711180c8505800c049481604540b18115910343c0350300e9580f82d0304141d500140c00360420545403030280c0240c007107034802040140015500c5951107850424003c0c14204054040c260080c050001080020241450020150a070710b5000440c1010000060500c1000c141080325041c10200c000d101020040050021a4021350700e0308148400d5400003803c80e948220411a0054034100500c058003d907408078505200c050001440c00f031110310b12401d080468096004007210011b0605070b0b03554815031203030092040e800d056045c002418 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 992433687 1250 992432437 992432449
    0x1f0f0e0f0c090d03030b03010b190602010f052e1e0f050603090a1202070815010801050c07050a0b06010e1c03110703020a1a1c0509010b06070b0a0908131e050a05 71
    0x980f004e4100b42e121454007801c0e58081d03110302c600d00001400c03d4070854114501c078280c42400d05c03600d00075510304540300d4000140d601466100d60200400030081d180442076003c0704108104003003d22032000503000c40d44448003d00d1201501e801c6401410301c034a01141c12040c1302c0580c0140d4040c136001c0c02404130b401c0b80000c1300c1c001c2d03980c01455440300183d4200101e2820025500031003691203020140100c0001c001034842c1a80e500b036000b44850390316801861010b10a012005000e40d00140e1400c0c0450784c040405d135088401458030400351003c0d64001001d2108200d540420341014490000030580c00ca0b20303400e41c0040880247c00003c0c60341d000500113108521440c110404158040885442e08208039240d1407403004084256420450042c00100422643c500b999803900300f00d9031441c9021001d503507a00350b10860b03000084d600c1c041c849024007488039040b40c810320705110740f12003410f82c025207901500301100e00c484040e0040400b10031010556100d240241c1d00c0b040d05001a440380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 992434937 1250 992433687 992433709
    0x302090c13031a0121060e0f0a0c0e010b07170a090f0905092104050904080702060c0f0c04020f0f0c1509330610050702090c0418050f1f0f0e0f0c09 65
    0x1140c000070b504290030b4012410481c1c03030400e002050144034240b00810046040007030a0741c0074000c0300524ce07a00c1d121001c0103807050160103400c070140001703034490304105600100038034150381c80c00310407140d039510003100d25030019000843d0550301c0e0006c002c1008010081c0340036081006c814803540e50501072031700300144502d004250041d5030400005003880744000c05c5904070340c1d01510542d554510000c10382d0f01c0740e03641e40b213200280c0644143c5034030794940341c002e5620a01c4800d06036843c0ca0380e40c480701c044035402800b2107859806007076949966820100e14591145400e80044c0c80140c181240303000350300d426240c24103c060f444407103141c0c000381c401d0141d541c0310100380e40e8004010302250040c1c40c0750040580007980181d01c1c0c8100030309513180070003420448235540c1081503007000d011140c40946030201d8030f4040e0360410100007401c0850500500c44150354106200403155100c0780080c0003c00550000da105103050400d02040c1a040718079194015103031803102d0b003000407031f50010f079840c00d00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 992436187 1250 992434937 992434943
    0x1b1507172a1e030c0c0601090b01050d180614090c010915030504020d0501050103030903110d0f0b060d06050c030103020a170a02060d02040e0403020c010f020a0305040302090c13031a0121 82
    0x1010950401c0300c1d00b9042205180d00140c40a5902d901e0071095065260b80681d5141c6a903000309000041e440c540f5004802c0e41d0300c070503120a420003660604100085c401000d1304e0206c0e8940101841c045042d0344120906003004810010040c50710700f014615007480c00c030b071490401000d40300410003000031003800350400761189800701c0c01e44c60b01d0001546141030148060411f5107400000820035400203a001d0880307104010761015124030804203d0070540c0004058440b0607070981309030005000c04851a4811002080800341c3d09140e2134550840d4022980b881d44404004010b10651925808100041c440641300e070400e802d40103c40b07501c40e10f04440c0280190404614000c1110762030b010f44010b040c084640118920340750900964800307200f444507000c1500e0914031840d80e44041385004c2600e8060321940c2c03a251a43d400d11031145401040b10003554070a00c042c003c025454034072b40780110300440c43e40d034544007005003205141714181d1040500e0104821002c0040000c540c800303d0580e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 992437437 1250 992436187 992436271
    0x30203060c090d12050d0507031802220216110316061b020603090a020906040e280219060807050313110d02040501180f0507051b150717 60
    0x102083e1840c02100c07000300000096290140f403540c0c06805858810698401484a500d8442060342244d18250783d14688004214807031026052640c04502c04032000d40d400c420720407610f404402260050000c4a081010019580080c0301c004e0300c040700294012400f600c10403105001055003a680c0d40b01d0f51050000070820a8500c0d044c410903203007456005000070355a40f402500c1d02d512000f030f600040f80305500d980040b5007241094400d2110f0054004000c1441903407821120f19072001c03005010098080c07080000700141c0ba14414440d42040420b00030720994200040940603400c0107154008220052041042174940d92000200d540d8000d00800fa0b203400c8003002c01c101060301c070000f03034010b414000002440f142080d001e207506283e201040103249400150704080d40c0003130f2459000207105125240072210301c1d000c005954080715003100c8003080f04c0c0d022081840f01c1100c00401042400400f541d45001107111998031182c0720400d0059048041d100540c800c01d200c4511007442 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 992438687 1250 992437437 992437447
    0x1a0301060807090905250c03120b0a0305070902030610020d0806010540060201050c091c0b270609060f1509040804030302150c0702061303081303030f09030203060c 72
    0x6800769100380040c1c28442c81c280178501c0d14a50011490441ca0240c40c81440b004100341c21b02d40c41260000a00c9515a5420080201e50319689001c0c0001c0030506501851985c0c001000a004101a5000704841c9074056128500f0303804000e03201a0407003411041d5000701010745411a4020700865010409003400d030380710862911460072250751482d4860040b401c4581da0561240c414401030965442100b5181c6140e4031248220300f41c07031058aa94868440911005140c0d207030452101c6110380442202e898409040e440d405025075040d62500032510920b811071050300d0018035030481c41c0d04240000d101c941030000366507070349080040c460010320541030049500c0b081503c0341d4020f007540040208180342010b0a00c00050751042c0f20440c0517100c0c1c003d1450b40030703041c9410648200100300703145091081c10317000e2046640c0b2808ec0880d501030f07642000b00001c2d1250015000300000302074003100785400d41c50003824807800500c0b4441806403070314003000181d81c0012030650200e05412401d440d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 992439937 1250 992438687 992438701
    0x4050c040b12043806031f09020409080a03020a080c03040b0708100531110a0e220b0906090c070326090313060c0f06150306021306091a03010608 64
    0x1d4101411104000c8152001c004032500f1580001e9181d62400020740010341c9800c010155201c07c80610700c00a00400b40081188641c1c5a0240030054006000490b90b07a5580c5d407a407141d633205400ca400420350203d03218403d240c3c0580a1175000042c4c0d0569440e5080540b113105403010300a03c603104102c901070004054440291900006140150401e40071040c421040c0803424505540103034805004810210a00d600d13000351483c442c07800010034030b0300001c01011503010791606026600003686281141808030400c0e00c03001002c03240d6200041c03040b00c0e4001c00c1071421000d400d89128000360030912028820305012101400d925040011031413018000c0384a00e103010309a601450108481008401c441c040002c2099540300b09072008207c2c0c5661090780d4050315480003402075205900d50000280c0c16900114180a102504c1c400c520355070b1341c3d031030140d078000d0742200c0040c03c040c03000300203c940251201010f02021030b0703c201c001c900c0c20302034500e0307000c144202030811034150089102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 992441187 1250 992439937 992439953
    0x3050f0d0608070f03060b0303030403140a0215010608070e0a05060306041a060c280f02010302030405030c100606020708060121170309070311061306050c0321010504050c040b1204 79
    0x400b918002d40c0c94080e59151802c8240b50300b407005580e218202242c9032220b14000c07003184d20840e41070700c842c0c250581e0600070340d146410200502d819032040781c40f09041034419060040c024006035913030750500d14020344024001c04040010034050140d40c1028000d6981d058203499000c2c10940d0002048003006c841801400e4500608a802540010340c6003c4034070042601125040b0724080c0848451401c03208540141c1001405000003c40c1162940198400d400850300a40240e04036810180c0c1d0b00d83c2d090078035401d041d4114030255a0301c000c1150301e0301802813400a0104a01604035589841c0d00b102d003140424215940d40204107a007001080a4400b105109050030200d1580300e107040f204c115a0b078191400142c660135000f194056442c034040c4e04075210181600003802039185040b81c19107494000024140c014042070004129203003605175120144600310f64540c04651410082c0011180017400e90030101d4002c210500802d105c1c2c00444061140c0301c00c01841c10343c0e660900c849 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 992442437 1250 992441187 992441189
    0x30c03060306020415090807030503030109110c010c0c050d0e130905160306060f0e0103080a0809070b070b100f21110a0905042120240106020c01090303050f0d06 71
    0x3101d2011030b005c1400c0b219a07024010310009901c40401c82525024a00d03034070100c0f440000c103550f204000601440703050350040540d10301450005402c01c6025041d681c20740c1c0000c5482000100b141005805001301008130034002d40301410408505030680c00400c100034120200011865191003040c0300300301040000e04104000c90703003442151602c03403402001600061180c040045902000444d40041840e201412a07a21000603840c0c2019a40e040d030b0b212a0062032021240600000010200c00200c018030b0340a110b03542d44942c9290013600c100100c202030300300c0d0168000f41c07002842003070304140b4505480129500107603001c0c8040e141164100c0298060350780c0046540c5000510314440340c0055020b80d12441d03d40706c070b000e0f180441c0f042c55100d0304508400100c10390003001101044072440f4400241c56019034645610700042d800306080032050340180b007174900004114055042c0b0601880c14400d10348014180d2031034400810f24050b1450340f44d05101c0000b05404903c1041e48148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 992443687 1250 992442437 992442443
    0x120903120702190b2d0403030c02031501060e0103060e011401050d150909031b020f30030403020a081903030b0105091302040504180213020f070c080c0a060302070b07030c030603 78
    0x1440503110800000d05400049200c1c03420394007217002c805050321024015a03100c48074a4124102450341d1401c8510450b4610180e803d406a80b0f1407480000245a10314060811921048180b114103000101280d03081d50202072080c0d0340c00c0043c00040c5d9132076044403001e0024a045030710303080391000100081c40ca4030044031020941c43e00c0050030036800e8106401860103902d800f10f012405059031000c074000c6000c003c0d8071030000c848884180c500715004848d0714140550307850b009500074000c0c108082d200289c33454141d00c0840e00304210300d020601c1c400a04044006010070040503800710b141d00345007080003018191207910403991039104500740d400c04a0014102d00e06041d24030000c0000307501a000705400f40382010349076aa80040c0d0001441580d07400740c082844442030f498903600940065007001d840100c200300d1f00780801c03505006c0e0800b0f00300b0b40001d4400c0c2c00f000c2081182c0c0024139070210702458014004800820340685400e13504c80c1c40d5003004140502011400c50051000e1780001f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 992444937 1250 992443687 992443729
    0xf010501080624011416050303240a080d0507060905060a050106200c040c0221040f091415010207090614090c040b03041220060702120903120702 64
    0x2500c8070300001c0160085043e101c00d084007100180c2280d0710310300168291400300e660310403a11031944140b8000e20780c012503010280c106a00c0740c0e6455041d507105440c07078003030403850749000c1c102d001e0100584844600c084036550380c12071420b050710b51644003221444092100211740d03c41800303402e80008072110f0b40002583c1003032424180d1640100b20038000c2d2800264011a145d82e4508030481c2c540b004c41c0018000c3c0413411046041101401c0401c08220031401800410b442c0c6010808080102d241e5144210ba155402d00e10072851a80a40c2d100030405801c0100340d840044101d000e881d0804542c0e010030030b03203881200040c2d02e0112140c2c0320350102458480001003000340180800d601031000c49a00300c160b156448008a6400b440c06026450b4500f040813500082c03858543c0d0380c0e109100d06081007812400c0c100c52089078919203110003207410035820071440c00d90601c0f9914a01d9503000201d0300b0514075501203036544041d07108a03481410001803000039540c2d4140c107205c50003000203031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 992446043 1106 992444937 992444939
    0x30703060903050d1d032a06091f05010501120905010605031002120c31091409150c030c0a020a060f0c080c030705091509090709140f060a110f010501 66
    0x22040c4200307211f0310100c0c1079603028025144281c0420025080724211450707004100b00300c4c0c0c620746400030724002c010720050303070800800b048107114a980090b80c04500e150050040045800542c0e152050800031584848a42c00500c075000101645078015201c1072130601d0180250b0304140d0003c80c4c403c03003600d040380780303d681c0311440042800660318083d9a8000141100d4040307500c0194204100100100102d04000c0f9200d0088003001c800a41c2c80d1622503110540405402c140d010500010011703e801e01c200010044183c1209080240e4030005003508010b01d29102400d0200b0030304070000b05801001c0040d644201c0c01c50f00c4580c07500111a0400c041a2490a0005461001031045d01c0b1192600301c4045d02c210b00a0f03c82e01c000708c2c109a6000c2800300303031881c3d09104040382c00702e145607502c0e8181aa4100010384c00d101109100c1c0052039410882d078604c00b0700c122361034030300 = true := by decide +kernel

theorem cover : BRFrame.Cov 992266187 992446043 := by
  have h0 := BRFrame.cov_init 992266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 992266187 ≤ n) (h2 : n < 992446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
