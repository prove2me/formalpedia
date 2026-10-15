-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4685
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:24:28.868853+00:00
-- url     : https://prove2.me/submissions/22703856-d382-431d-a521-001817c52cd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 842446043 ≤ n < 842625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 842447293 1250 842446043 842446069
    0xc0702400b010e10091701090327140a03080304050106090c03060b041505130e040215190e03010e12071b2d0b04080109110f032116051b 60
    0x1200f09603596408208050283c0f641014001c1010040380003035010b0080b140040b196a010000161050702403c004011201d4840024021280440d40502c900011310342d500850305680e07080810405820700241c80b280343d551029060150100503c42840410340c88a01117503040001049009440103098003a215544103940000b5400d010800180c1900c1c0c0094820034094545145442c4d0b1000355842c041b41260040b17501009210304020450900c068905003500c07883c400281000185a2055089125488800104030600294203001e0301d00f50040c4030f00c104c2403003c3d104c004440610202049c5c0108074140c942c0751007000c07884611081c3c0300503030083d503100096003e8840c0f03142208040041204405402c0c800c04004006440c502003000b501c0541018000483d6285450030001103a100c8100030520400744014000c6140c0e034001010a0000140440c3d10303050010540700c0c41980c0250941c41c10b840700480400000c110001c60400100c2c41d150500c405201142c50502c2052141ea00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 842448543 1250 842447293 842447297
    0x170a050f010f150e060d0c211b200f15100b0f0a0c05031911120d0c030608070b03010e07051804092402032703030c0702400b01 56
    0x20450b40418843c00c028454890081c1c017807864a10508154021241481480380000702c01046800c02c4070002e60110b03100114100080c8051211408261080c0c650b004d1507005016414118041d848403014024941e1a0034205542000c0300240c0400d803100280450705000300709502c00501401c44111140c4141d4803510703885800c082200c40004030690001c50b403442070112502c503500c0092400c0000b40068190303281c0110300100d02c45809410803c118101c09030580118a5800480481d0820b80783c04080000c00820100d02d0007030103900408054010302514011124080f0304050310000650494041c40c1c2e11002e65924030b482143c05025059150400c01d85c001d02019040c603241d0010b0000344d0081c400300c0c01e030f0000502d071a000901c1141858030702d59004800c004194590b1952041148a4000d4881c1e02c101c030158030580386d02c4010200c880d44000481d941065480d9041c5c031a404210f05040428130041d01950450719410760700311041e8503000d084000e0820407240c058000c000e141030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 842449793 1250 842448543 842448569
    0x103060611070509070513061205011413020d02040503012c1c0c021314071b0512070503040e04080c06071e030c02010e0a140c0a030b010e0403170a050f010f 69
    0x6820044c14842c040e0a11040002c00c0c07112440c3c1c1c000c91590791307008003044e448094102c031b8404030031000c2e107805920170b550716091024580b410303895898442c070344100101d0340141e407140083e90b41c000a000303d803c080d41542c03030014002c9074000d840085400500c211100c04000b210100c0c5555500d18400400c030601e81600513800c080d040c041c41396503030018402083c000c9030074209079000c001ca81074010749032114000e0314280190301d80c01070501d001d40754100701d032801004000d84480341e40384c0b950410312020740070001300001404001d10584000d0084280c000c0306904203824020000d41107105141814080c100c08102090701a00c06a040691410300c09070074280024010f80c01809410100420b40d501c6600903450840180000c1a43d50710800c2d411207490590f08080c1c0c58415480000c03409a0301000c014000300c3c0c3e50304034040c1100c8880325440380d16582e51400310327120101c507020700c0158a541030511488810540200b0701ca0031564210024a07030741c4889141602004d48602a902c07100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 842451043 1250 842449793 842449799
    0x711041e0b040f020d090c06020d050a1206081204140402070c05060310031202030d0e070b03160c02030304030b04140a0210120915140a020301031e061409010209010306061107 77
    0x3294011481800c40140b00041c00d0790780300d402d00305136131201e810788400c0c540d60805041040065180c45020301194801007084900604000c3e14511070800318106205c0301021a0072000c08540100001d4419041500c00d800341d0001880c4242d0414007502444140030800e51100341458803d6802c21a0405901601185007a0610031140c3c0b0140a14600382201c280102c080354403480140346802d201e0f801142d40e000300340400802c4401110a106603a08052010070071268102c0c180c80d0040d0441d05031865800d440d50b0255041015070394001d4050001003070000a1040c6081c0030352045000c2e1141c03800c003a003002007240d160004208000e500102464220065602c80c43c400000000c07600d0000404d1101a02c030307000010380080f80d40348059240d00000406407250b48100d84c105d01203240c10b5045505594503038180c00501d20fa141c80280e4241400010700030503801464400c2c001c0360b10041c850410380074650103580041c0415010900700100025014410089144400c1504d0003418155003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 842452293 1250 842451043 842451101
    0x30c0c02010f0c14030306210c0f060d0e0705010906030203060a270f0e0c09010f090c05190909060f03080d050c071a060a0e0c07110604080106080102071104 69
    0x2111031080400030408a0382e400182000154100d49520134000e684138540348007001003c2112200c0e41900b40b40b5409114800c402c0015009560702044035030040000e00d1101140d201e01440d191400c0013400c280d01c4100b2480c0100e202c005452080c0c1e55554030b29200c6401358160311050b21515001901605c0421000c40500c551812040d002d17012a0100e807a80c051f004265450944003d04541da1880c0700e1071515010400010340c10000e5503160002e6261107030300040458184560050380d070700c90406409a0b40b09404440c550700d14001c902c924114030b0b070070007441c3c01c4803070060500c000d10f8020045131843c01c120b00070080326400021b0910340740c01c04413580e014050203402d85c00015024450f050001e0f9140d00c40481c0791a42800600e080d180c0311040104071000b030703808100c00305024814084e0848822040712503d42d045208100c1c801c0c01c101c0892420711507507010000a510348140412451019001052100d01401c540c0f1890150003080004848507680303001e802d4158100200c030150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 842453543 1250 842452293 842452307
    0x2090a0e1b0103061502010506120601060215090313062102190c0c120305031905010312050c0c030d170906090a03110a1b0e070e0109260307120f030c0c0201 69
    0x401e06140100780e0729602c901c0b020a00003c8502080580d4494040020504205100207407520040c4000e10300d652501c0d1000c0d403640c40011103440742c0a0400c1c0001c031034840400844800e03202c9103007072001955031020001c2c50072110081e1245800040700003038010707441500070380d00320440c0e48a52801034070095100b5641141000001c40d07441d04400300006940405406070381056000752511a542d1800302040c010079020b141c16540b81e10719090040c80400c01b0313620813080040050801070703a40d000107403c00381340840c000c140507031507c01e06003080f01443c0c0c8818501100c008005001216442e44145183c8600c4115499a50782d4000420080800e204c0c2c1d820f00b60410f03144041d561010b045445845075000d100010f1981141136500c10401c035040c03883c07610f512204d06d24203c0b4000100b130b40003c01a031503030310a8403404080b2860245802c0c0b4121140418440140220790b60f0b0040c41c9809540710240c44488000b241d5485803c50300203009000d00b149100c003d6417240b03000b203590360040d6401e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 842454793 1250 842453543 842453593
    0xe0d02030709051611010c050306062101080d030621060c11100603030f1b020f041107110a0b0f0a0f05071515140904060207030c0507090902090a0e 65
    0x1600c12810300241c40450740c81960300407240f08400784c2d500c1a88542c00380c1400d80241c08500c00d40e1420004045ca40c0d40039041e2500a842211900c1c0d6910308007480114800c0200c48032070720006041e000240c3d042000625008060094400f480301d60f0b66100311200035001c01405015419840807444001201a40040c82c00701082c00d1106424110304125440c4c8244510851041035843c503060060541000034080b51201619005e481170b202d051912050200c0074100a001f10001904d109040d52241c0000000314034186c0100e0702d503403450800c200301041340c0840d28052141c81c5404241c444406080b50060100c020050b071402000e0403040f03940d050315500704000c2103024841e000004181e0307043c80c4d500142a0002250342500c0d01840743e0322040d264412099402d03a03a0340d08940762290301074503511a03044007006071034000c1c50401340c4c1c1c001c804820080550141c20070202c1c1c07180300307513101c503081070700070344040b40d00b65900003a68084480c0350700000e086510009187c03038180300381003c600c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 842456043 1250 842454793 842454799
    0xa080c0c011410030b01090b0f1e130b0f06210618041209060503091b0a1703120903072013050a0209040f090201170c07022115070e0d02 60
    0x5000d00c0984050610b08080d10600c032940b5110304100103021554420340c1c050f01c81002c0800100c100000081c0310007154a003958050400080e290b41008100340c1c030000c8076800034060610b0004121100b400902c2d5511886200f08240a0201700c681001340588600049008008041c050405411901e105000740080d9104509201068103043d220340c01c9070049109a505500301c0514400140583c0d12a0300440304100d018030400c41150000100c0c513591a070100080da0f4800720f10382c085081d00d141c070340018928007074480d2090070044002004101c030500075001940e064a40c10401501c9109584c0003501c01c00c40101d0311042070100022205001d04010b0001c1292441c0350818402d0351300440e03c0041d079683c0030540ea112801c0c607000d00a881400e01c00f080081112590010340760070307080340303680104814a20000f00e404103400122801e1540080802108007015180396010815955030700205000ea10803001c0015101030699016840031344501c3c076921102000e1107010404d00c002664 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 842457293 1250 842456043 842456051
    0x303061311120402131a010c0c0801020f0405030d0903151d06090105060312070c0b0a02070803040b03160809060703230a0b10110601060507020d0204020c0a060609020a080c0c01 78
    0x40644442005104507501444003408a140c83c0c0100150a41411110340005c0e081588000140c6c0302c22514040800c1c090921021212050804034610f65903600501d200d507200107454031542051030003500440e03408404070f803406205c4e80700071035100e0f03c244002001640354201d911750003d05c2d50050f1000300303120445405016a06034070340385480403e039684141d5035901d00c1401100c0c14280b00304185541c019600a00c1c2603903036540d840d040709141c402c4011008000c50000d42d600e10a0211a00800201e02103d403210380700c05c206289540103a60640414556a8040c5d201354040c078005071241d01e000c0003500c02d1340e4681c1c5c0180c02410b003010b1641030303c0a041318150301041c2a070207021b003c0c3c080d001002900c0d442c1e00c400e001c1c10940309900a01803001000000100b55800510b003415102c0615119403503c0f540d2002c03406102071240700a501c140040340140454000041c000700c101d01401c420312a496580200408902c100c0303880c08002034200002461105081004042250080740001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 842458543 1250 842457293 842457311
    0x2190303090605190b010c150b0a03020a031a0a060503100905030f270607020307060f0c14100f060b0906210c071101030b09130302070e010909050114040503030613 72
    0x50200e5001316804002e80c841080030311156a03040c070031074400d031000782020350031984039454000c45203071100100c0d20b085440b040c4040e0070b0349030710500d2801154064088008a0342b640340041d01c0e0700340351541e0b03d11400c0140018006003c540601750441c3e00140160445105021105024020780007003550141710400141e0f01d151100401042c01c502d0101d0003418050401c0d80c41c16020380c10f07228481c40342e80180003100141c3c5e40824840d044030a641440007a101c00e81e001a261030b18441d0000e4a2144071141c000d52854010a080e00d40c6034140404001c0c0344400b441500031502d10307000b441b240c3ca1040c400c68056040880003400e440d0a0411a2048110360030f2041d062805c08540c0120422030100e10a020001190813211000c102400d09208603000140460606440107041350041c01e600c0e04400181402404080003070070005e020b4641d42e6841d001d102d0081d001809044582e5840c00d83d40399401d4030321011050040d54030401031440c646500082005131040565245c840c165100407807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 842459793 1250 842458543 842458553
    0x6120b04051606111c3009030804050c0909030406180b0403050708121c0b19030c05010207080a0b0105010c0c0e040302010507031a01020a0209100e1f0f060219030309 73
    0x400010201607a03100c44107080b00798113609000100c0040b8610086990806401c01d4014488455248100c0d54130f0111702c3c203456402448540584004440505d800411824150b00124041c4201d00a8085441003694201400302d5103200321031215a54000b44418415103210760b04450000311010107901049442e4400300c0320355031141d40120b50b0380d44041c508115800c0309002680400c142054180e081241c003101082003846040d41844110b99039604185950b901d44400848551402d45200606900d0386000d00001120307000741070142c0329840b00040c1264001a00c03895040d800703a02203045074a400015038401055141c02c60b40180d80707030800300b80e00c081130b242c9900c00d0f0300035400401d0b6070522090240403550811428041410300b5000c6650907600041c400c04042d906840e400226503442c800d00d081c8070100e030003824031702e116103003809840510b030103c0c64001c840301028203070010740d00c4100c02801e001510555001d60084504000e040d01d9020495078024081e007004a106003466450b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 842461043 1250 842459793 842459833
    0x813150914060411030f0a0210171608240f15071518240b06040801020c100b0d0305030603101d01060b0a1209021f05030a0f06120b0405 60
    0x103080c07000e900a00030030041c440b80c0c0f03c00b5800a01c003540900281c402c40328080d9142c1d42081000f0740030300100440090401d00c81c42100841c3c1d00707c2c400c2180d15041070449500411008213007103000500e24000700300d02c80309000303a170090440104401205150220244042103180350740c1180d01c0410042c907805102c0a441c010080148101909031800100b04022002c41d4400c1c0121608a1190103892000070100201c4d0200d28540762042141040c8500000e005843c000100c0e5410180c0401c2c002244107054010303281580041040d510000c1c2d6041005003100c0441c0344070340e885100480c514010901800003550004000340a6030a11031082c0031000c2540c100807841c42c0003880d0500c84102c1840c0c00c3c810340001c2c0003441d401e2458041148002803d034507206207000109561001300104650712003000c81034203c8441206082100c015a01402903082228810362003030801c808210008820720500058540c04096998040c01036107a803a0503100040003200c02e88160b501c0c1ca111441e445d42c2c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 842462293 1250 842461043 842461073
    0x11202040f0b061210080d1202030907030203071d0c031e1306020711130e060601050f04080f010c090801020732150106032d091b0303120b0108131509 66
    0x80720010342885e6010071920703016540240d00340d40040c4030030400d0581c494808405003070a50b01c0503869468018245090002c2984000d50503c641180000c00c24481d40618180224880f2044c0440d520801c141c9280c1c80100c80e20040c540c0c02d020b40511444034034400d01c0d0401000240030311090b20503651f1030704903030043d00155800102c4601403042450009908030030048404800c2c4052110041070980e1040050a40c80c14032002242c10040e0000c079900340c034000d1500c00c2c101c0d02c02903001c1b502c8030700900036629100000740b5401004502d560050007241e110503406210450401c003003800c2c4948c0106000e050000f4600c1400019040e824100b19040400d1014018141c09515040000d41124402e44814030641104203510b40314880e480708103400c1d01d8007000d010170400001d143c003415000c00d4400c0755070805072020010040c1a800150841c49605000080000e80c80318401035407642c00440700301542c5c400690741e002c009210810318a00716030f1865004200c1c80d005d50384002d50036000c01c4d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 842463543 1250 842462293 842462317
    0x30203100f032d020108040b130b18071505040902130e091e0c030c06030618010608060312090906040b030712051f0903080f10320603011202040f0b06 66
    0x8000d0603a003000300f914020b60301c51101000510302c441c0d60020340303200002000500402d02a80001e0b1034041d01282498456a2001e040034842ca080e03845440700d4452001c400b281c41c0301da95000b045800071020b07034183c4d03540261038150130315207400d1025010b54072410902c0030001d503a8500180459040781c80703901a81042c000341103960003034021821003000803d442c0307545070300c1900581219100401c100101600a8035040d5480d5201c10201310300c81e482480181111007c24000140958404032440c05501d085099500b1101070301c00c040010f00650011981c050040008035100f07180c640d1119860440180907170310070329590400315800c40c0501d001a2041e41021060f8000c0c01021220780d04640800d030020070456180d51801400800020000048106400d001c00c240c40c3e5410b4405005082a120f10703054800c00050040c124046c00501401c00341c901250900140313070080079a07050340c46101179428074850503020080075100580e048181d9684e0b5484052050302c61200a14401e80e41c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 842464793 1250 842463543 842463563
    0x150a030303090213021905070501020909011203020c0928060e150406080d0c0b0405010b3615010509040f15030b0a05040201080c0c1f0c121b030203100f03 68
    0x2a0040c002840300e00401c0602032171041200d4641a401a41070814092035481c01c4d0f911001c10b860243e0091203661001ca0340180201d000044044c0001404a0064840c5d801d48031091b06140c14803c41082c1074403c0a136940314a0f082002c00d20f00c0039100218130078401404a007003990382241d54a41002598100300121641c1000c448a0900e4000c0100030180500100060302070100c004143d064405001000c0c406108080340030700c10250464105280000c04501201e22903803011000c00d4822500481c0364901031551200801c0ca0010003449040260504080019040d0046440c0e50100b05e40302e900c02e44d100600c041c55001481001d01d040c01003180d00c403a490450801c14a82d040045c20000c4045c104810080180d91104110340c21140120f01d41c0d84400034030544900b02480348041c01130201d05152100d01960719500b041680004c5031f11012130448507032880358140c807294500c01591141020459801e11b1180c6d0040d03078040702145044100036112100780f0300450a60340309442071000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 842466043 1250 842464793 842464811
    0x40501081f060522080309101e08010303030c03090c0e09010204170705010e03030c1207020402120906060f040c020c150418020705060609070816090b0a090e01080304030203070e150a030303 83
    0x4028000160014584951180c440c40e00c8200d46c3c3e01d104941803603028006c01a800c0f80030b140070304c1c03080701e5400500784002c80e05100b448001342101400d10013074001030300f810051b80c03045020f803056003200358100410130380480c2012001c1a02c084003400034403142d0360810000501c4020b103400710195420080241401510300700004240d150b40703843d580d2294004001421000ca40060f0104c1480c0322194859115030007400003c000f800b4407100303908940703583ca04014218601040d10303417052034121044685d00701d00c0000d1004445040c401480580e006030202c081d1f40c03904854005a01d00410442417625403203546060603200d804507a50041500420720f001081424004103900130780a41c0e0109003803800d0f0300700510355030000c1c0c4402c642403048010191001c0c8240481d20140c846050304030f82d2a01e40d114000d141020358442d000c20303600700400114052001000701c0b001c0700d40040060030700314240503402490700009811006140c1014000540d640c6440c051180114017a84000602403a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 842467293 1250 842466043 842466067
    0x80f09010509030d0e0715051c0b011202030402041b0f0f030b0d0312150b09030601141f030605030a140c090606160302030f1b0d020109030203040501081f0605 70
    0x64402451641404204406060000107913100c88034076030800700f03100300c01d4010b0300d0070003c0d55045410030750105522002180d810500400d01651655807005280410099480880b24050b0381d0074000703000548030401004242e0042c503006800113100192036070800c044c02001c100c88025100101d90002d000d01c08064000031800e24480c1c00d410148642d400e104006440b01c50f001c20001c00b4003031029100291102c1d1a44181507070f411003e05080c01da922010500456045110701512900c989400840e00348101645600b0729000035150314600d00e030445040304404c42d400707810410190f4404000405540401c42d5901807030040f60b01c2822041c0300714007103082400e5454820b000c1d50301c5809010640c0c42d4a42196882c40f034000039000d1403041ca240032412742c842c81c050100200030108048681c0b4a40300c6024101041c5642181c0130020b0740034080e402da894a082c0580560010b100410003540a070240b1031b8440080300280b030a48840d0f10000c008002607401c000002100415200d410351 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 842468543 1250 842467293 842467321
    0xf0706080717070c030c050609011d030412060e2802010314040f030f050c0619050721051005030d1805032109190b09011706100804030e030a0308 64
    0x401d01d408040b0000440d00000a0704000e0848810881c00c4400c000c2494425800380c90038680c030a06451907818282002c501a180340d10300c810b40040b1202190030581d0000003191300b25242c0074542c0c000c1424684031302c00109800e40d8560100c0c0568042004100b1184583d40d003070007084030090700141c131036000050840712200d840f064154884008d202c040340b00c05c070209540b142d145c42e01c0b015845007200122041e00a20000c0c0f0b4542c441c920902541e1804041c40c0c07441c04030b60010400c101d60740c40c402102d0148041c036a42d0440d02460040e901c2d45016a00007a81c040e10422075080110303918004a40b0b070807111000000041d03482c1d000e50700c443d07000840103c01814120010045000440c400c001400610003498501c200001503607a00b5840c1d0000c050031105c440c910326203c01d030707803498100000c0d445944901c2c001501480ca22100d299401c20403801840060007420001a05100641d90b1050182050b81880440c036100c40403a6020000d03628860301c00d03550705610f810051443c000c09 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 842469793 1250 842468543 842468551
    0x30501140c04030812150a080a170306130b01051c020c07091e09060603140303040b0f0106140a141c05011239060f2322080f070608 58
    0xc1c0d04200810808240c5050941d615614400d00001d43d603102d0300c1c0d6155900c40c0c1021601e803c85080c3d100000c200b07074085540c0d0086c1c0c1c0108682c002030b02d25200d28400d50b1000311076070b580c090b102410003d60380b06260700044244006060280c6401c0704035887d014000000c0e04d690081d00e800284440a035402031180c0382c0104008602446440c000c0380c401000580050820a00136680d8006d800074450550440c800942c0c0007840103250a6250010f9601c80d407044a05580c0601c1c0d8201040b46c5004034105541240c046a0300d04000180c2d114408441d98040c1c0901c100300040c002060f0582074003900201085412013801d403043c50307528902035003640e0050b80200c80048602442001080c1400d1001c04031034040c4c00c4500191205010781105420803000f01da00400c02e201001c0b0758107801480c400121920341d04d07024980300c0407081c172090101d039015004900c00c40a02544a403003424100c04a81c3c200e0704240b040c90f00d40c40380c040910b0064038002c3c3c042198404c3d0b1040103025000501c0b2500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 842471043 1250 842469793 842469811
    0x72c190b041401090b041d0105090f060c090402030915091c140d11071a040c05030309010906050903031b0d0e150a0c110d031809020a020c04050702150103050114 71
    0x104450805140c0b020540500c0f030b4102103078a50041403041d40d200c0e8400510101201c015800c0f10103070301101d038001c010450f141141440340c240e10340c00015000800611a4410015580c81c00014001f07100283d0130140040207d4450b00f00401445121904540e11402d0284000c02c10741480d4284082001c00d00b004100a00aa01d1035111108000c10101d500f0700c6906030f00400e0940350392002c08410f218028001e40301c050078030004914928070610a41c0114000c030f0310000b101791943c04060304d1b440b40048460100f60041c42c10007071180141c0161880c24001010b8a0a02d81903803880c140f42c02d41104107821301d8111180840c0400c3e0080082254148141e07603040003030315002c01d403680b07600c980c1c4e1680081c403400b281908100100340380030b9900d204024241c421005903034a00900841314600545903140d11302240403031031030560310a452100145a0041c071010440303209000040001030a104114040c07910f003501e0075010140043e000318815000011000000007100007500409845194 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 842472293 1250 842471043 842471051
    0x111005093418020405090f240d0609020f030303070c12030e03122a070c0608090703140106030f2105090a05010e0a0b03040c08010510030228050a06020706081305072c190b04 76
    0x40f1a442c1c5140100c0e40d62b501000c0003506117a0750000452281e00f00c240c05a044c03000000304040f0303507480b042104d01140305422412501010b0310060301a02c1c40b0410a6440341e0080c1719122051040d000701c0c82c1c1043c0540c03002007800d081005082c003550101c3c42c0407407080d01c002818a0405c052503004400074003442ca8492500c1c10b11135800340d2681c03032038800907200001404ca82c005680080d80800011544840c3e030002c0808a46040e1501400030092903a40420310244940d1290042d030450b1444d0b0307002480e24411a061200555542c101010400d0700100320604c0803e540010b0b500950145d4060000d40364228074001c000c6003580c1c002808141000100d8404000680b0383c8415241c20b014210905030202500c3c845502440e41c603940b09075880b401c444c1c0700150107a0081103410550754035a0358802c10f40d80703800500096804403140142603620440c1f04000506111048030000c580300111208071118041ea2149180d4054a40207800b6004c4054045100240d21402c0c000c0318094400388 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 842473543 1250 842472293 842472361
    0x32004120b0a05060a1e0905011502101a0607030201091a041b0b07110609041e060b0301050f090702030d06080d0f1e111005093418020405090f 63
    0x204500c0701881b920b1891012118100c19840f52402800042c08855108001c030b980c2d207021341800503800903103060240c0212404000f0380c902901911403000b141c1182c0070a103800241c01e0010a600c284010303011556200c00c010009180000003c050864940e0121120306280c1000400020070502817469000a01e40420004180c441034035030040e002100035801d07402c403c000c90050300c00c00c05070780e600c0340c580041402451128003600030312100716801040459250b07025000188403e00a050b44000c44212540461624501d600d45c03014584c41540d0524070112001b4040e0b4125401c00030303958000891080323900e940030610b09086003013880c00340034202c4d0500c1c5500d58481c48100c8441000b460084c0d1502a440812880e2130846512000b040716103890460107890b4806441c6e403a000c00b000303000100f40c00300100c20302000d480702d0f80303881d0450764a070480004980340c0c2c014011800720b80138000040c0503a0303030040c05c9105000300d20031030510303280c403801c8a02e880000114221000e229031400c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 842474793 1250 842473543 842473549
    0x6010b0301030f1112061321050412030e0a090504050d0305070507020405060a08070b19020c0a1413110702130c020a030e0402121f0f0b0901032004120b0a0506 70
    0x300403042d000303498000e888410074045000400785140115542c0305000510810742c00c240b03191021f55001e85000d5130004800c0034440c10b03401c0543c0001000076803e001c02d104040c04440300c00b2603075200c2c1c04d141c0100c0e01c2c4503000c1030700c43c0b07420b6010810075580c0d102000309020b003d22507040417000c1c41c5000c021504d4880c202030314500810001074011a40c41c0001092901ca00c034004020300070740000c90798a1541c3d6000301d982503120075964001c0c102202019140c131400051603001c07840c1d00800700000c140c00c000c1c80d0085d00003174450680d40048142440d042041c8a445031030541c3c2040135440355070b42c829006020b040c1c08501062101580f8140098100070360101e034101016a0501d801480342d07000000240181c0211402040c820726a107050104128401080c42c10000c0010380b0302d02501d50700c02d101171a40c0341d90700c0b0340001c0440401c600091980f10350b0218070310070382d022608140c3e030810748034807a82600145c02c880321402040e08804107100e0b0b90480550322198001090181e0f01e002004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 842476043 1250 842474793 842474813
    0x6050a09090b0102101b1409090f07020109060f0e0d08040c05010c030509040204262103071b0c0501031409030d0b130c080a06080c030c010e01090b0f0c06010b030103 73
    0x1d52481954030b16514005038400e000402c203803d0820303c24880c0c000c0ca405440641c0d5800d200346808210f00c0891a249140700e5016645600d00003402c040b415916580101f103418030040c08031045540c0d40d55031300c0004140384558003050000080010301403500c5603109140141c4c05500b002071200c10002c000001c0d01c000c80b01810360f442840c040010340080e00e426940350283c0100c0c65441742c00402d0103c0c0c119003d0110310030300c4000d406d00d01442400c08030015140c2e07245280081c9202469944e016100c2741c680002e54022001d0310780b49080f140303900802d8584025065007181e00c5426180108250340c0e041c02103814408030080b0350401c5003811035100f540c0c1d216003100c0740c5030191a0710710412183c0d92a021889982100d42091104106407100103001810032501c018100745055030114403160006001c4200c9a00640107000c40c804082c010740344c0c0000f04900f03904121400a01040301c9000501601203109402441c540368603ca145150528605070809450518103000401c0420708201c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 842477293 1250 842476043 842476049
    0x7110a050c061303020a08060a110a0801050d0f080d0b030f010e2d030c012a0e0f040e100e07050d020a0e1e01170c0a1a032a040e0106050a09 62
    0xa0381a43e03907601d5020200720304009500296100d1002100002c41c0d00380490198132803440300701d0030408200c0340e0b070340c4850900443c8092000600c0d5000144858180110010981ca014000543d10304107959903092241d03110310300d2410640e84070410030303600b81001c1200904c054104e10003409100ea00c00026941c82c08126070b4140c03c620010751107055829400c0b28400c00f0035024044d60317552401c0c49401c034080c1c1461802c0003044503080c03c03030007a405c907801c3d0b0b046003d03c055641e6180350450181048425481510010361080e078a040b0300c1c0503050104074946284405076004075106205850583c02c04080d5170000b03000e040302d0030b010780040c0d0300c440038501510f40c0e0596424890322241e801c001c0e46003042007a400301c00c0302c1d01c0000c600d8407101c14405190140c00350484e0214050302e024042d4001180c401c1c0780c044000c1229415080803800d01856200311800303103240b540c0030406030340031800c64001c40e1154000300028042c0001107914100501405007130814a1074403007802d038000d2800c0f107188 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 842478543 1250 842477293 842477299
    0x706050a1205062121070c060e031c09080f0102072f040903050405040b0415151101060e01030b0c0307120f0b0d0c090e0118022107080607110a050c 65
    0x400250207a48110215030203400c15038416140e00c40f40240d1a50303502c800c000c03152130460085e000120b18800842141c1d02c00764016241800c152402000350340540c084008a9414090007254409641204814207007281d025551246503520703000e01141030455000940d203650f4010410076020944450455003c4e51b5001d41c4101d440c1074100bd01d884000ba282491688907041c4001a0103069020016009891003124100003200d0714404003c100c8840114a0906041c1e0803c05c2054184000d4000c20541c214100080003062201080e42111410b410141c10700e445140140180107600c0c0503940d000245074281e5182d824105005000d850250840307041c110749480700d45041600c9030304504032840016000809140c1d10345020540c00c0e00b140038001c405403400792219940001401303400140030360420601000001a002d0190310303c40b0143d0751200441112014041507002c02c80c0e04000c2010b1806801c0c00c0c1014200100030b014201c00c4140c19a200f1300303029020840100c3c0ca800059822 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 842479793 1250 842478543 842478551
    0xb07090902030c161407090b0418050a080a0509060d05010602123c120108010b0307030b131103030a020c0a090509031c110403060b040501060201020304080301030b0c090619020706050a12 82
    0x261070b2050007550101031517007044c0962000020548500c1d002640c54079000ca40030b205402c00d00d140405998035030040641958032015101d40071a007240010300d104a0310340b602e18135141c1c04001146141d4024800da0091556076001000843d9040c410310401d000d071251035501d00f1085480c082e00c40d2440704100d81c0411881750b40b4101001100300b42000b1428482d882c142c891196021080c0ca0140034820b40c83d99509002d407112046c0340100390301040e030f640302200c51190303140c14480344d640c480701120443e003511501c00c030301c05c1e40c1c0d5080028021142c0b1550091603403440d00e50030300c00280e4840c2d0003e44818200f2042c440300000100c2584c42c618542d030a00101452900c5001e80078252100b0045003641c40060040b040c4a61604005180b01c01a2020302c600c2c2d90703a40080f0300300c4c4011240074040001c217000500c00a190440c100d40c000d03034608050b6090040e00d0002500302e40c4501c54403109619030f402c0701815a50107000e628000c05841c10000d0800001020140c8036000300d1141c2c0d0f03020303036803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 842481043 1250 842479793 842479837
    0x50a0e2803020a090e0d0503060103330503210915070f290f091507122703180513020c010b010306140607030c0506090f16030213050a02160b07090902030c 68
    0x803d0f4402d50b0002c500441d0030b6400d01a0000c00c001d1800e80480f1030000c582033003030100d054140010740100102451403100201c214001048140c0e811103441d0b598054034071800f1314481c00e40040507004040c010002c83d00c82070503030b14140ba42c425900000000c0e03600c03150f01180908074070f0b150f8554812140c20f04804550703a15030f2000e0401e485e80304444290100f81e400c2c07202c0103a20038a400c8003100c440404108408002d00c1103801c009552013130007403050b2200c0d1104c2c00240f0a49040c2070004040482510381a1164006007034103191410701000540c0c0840c0c9600103400c240142d40810f40c081c00c0410116048c0181c1d2200704601510342802010b00241507030070540310f00ca680d1606a0841c065902c00d0801080c100d4603003c03200700040030b92003078041030200b289500c1401c00890760700403c00400107a0640c113500c0604401040019825824000c03d0703c00c0a0034850142020b200e00306400c1c103460002c101801c0c008242c1c000e020400c2c414410007000300801400c0381e105800da4407000c500150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 842482293 1250 842481043 842481047
    0xc030801061b0209010f080f06011511152a0c0a11060c010203191b17040c080d0e0312120109181410051303050a0e2803020a090e0d05030601 62
    0x1940c5003000790050744c44000000d688985c61206c600340d070003000a8030310a883d00010380d680c0b02020b01440c0300c1c14255140d0b10f1896406a085004914000c0301640c4120003600c08150010070116881d00c2c8a00922200c62809014158400300015046001a003083c3c07500070036035902c0801e03102c020301600609000d011716035181e00a8903d00b01d0400c009540c1c920b4100310fa070358803007034420070700b40014100503113440705100004140ca2402c01c0355980c070b0311035030060323500d096030041c060025280d2580c980c2000c07810600501c8a85021411074662901c100340020503d8600718103020204074081003800041c0044410496250444010030004650201711a090303290440c003600c80104000340310107000740100d80103e003001c1c903002070300b0003001030740d03103d544024504464180040c0019400c0012034815405644081e0113040040c1c0011a40300246d05590310541814003084141020400100300314605103091101070008110180f00d1400354100160303071185440d01c10000d00c0408400580107034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 842483543 1250 842482293 842482337
    0xb18010815042a09051015080c3c0a05090409140d0908071505031911220b0c0c010f05160804030b0601020d0906110f0a11010f0c03080106 61
    0x4650185034451001c07404808901c00d07180f40c4244a00079041c0717000601c003141884080c5d01200c2101d4103803c0c0c00b8110340e40031204410020311040d2060400c4c400c2d03030651310f40c60702c45803102000d2003502c031000500040a2a80151001385854107541e041024201650703000c010740d410b075803054801050980b402d15014185202041800c04c10703114002d03407081c0303040e409029007084549107000d071540715448020040c1000ca190350340c10301003081080426420003910344484c6070840501c000007589220344881101c01e03845144a4405400003e003268070381011030414000a00002c0010740c80e01c0100881103880b103c62403111414011411901c141e4070740107100b01d800500c1d130f21003191003244641c500960240c1080c0800d039501002000010f080394000640d0711000555520340f81c003d03e1414404503100c50070041d61051b50700803441e0702c0c0003000c003c0205c080704620445242000c200c0c45070005205c180d401030070b4020021080e200324007207a042100b0724107481e002e107000302810315001d0902c0c8481c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 842484793 1250 842483543 842483573
    0x6042d06020315120a02150f0d0921020a050d030c09080118061413060b030a0203031206280311120d11010f11040504020313050f010b1801081504 64
    0x80c600000030810510003e141805044004842d09041c03150407490503941d80c0341c1100000e40018911030001007407641d142c00b9140034900c0c00d000510700610280b801c01074641c08081241c8004144180d0418180750480c02100c680d5144001e10031102c03142c0b550b95481d05036446002c03e0540d0f807142020880e101300c0800000d416284000d000c100c0803030400300395060f6103010545803d0700d0094071410030300c4046042809602000485122803086031a500010440d8941c019030502c15201e482006807014805811808007402c00e548043c40e2440c2401900c4140c000075061645c0a40c00180c2c4000b042110700e03060369042241440f00c183c040000c05d11100894140440911036a0354510507280c0c080c44c180c0b40c0c000c0010007440940003400041054400c901941c111090080c441882075090540c040c41c3e10180c01d410010f241c11440c0c0790305007403030003524101c0010303515020000701500f4440c01548482a00210950503036142142e460345a03d10080004d8603c2116000716092001e05d046d01140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 842486043 1250 842484793 842484803
    0x180c051203130b180319052404060b0f0301060605030604050f0c0708030a060e0115020706180b070204020702090f0103140a0b1303020747030403180f030b06040e06042d 74
    0x46c011a03451243c6510500324006c4a0900c551040480c6800d0780080c80845e0b10306000d500c040a80303450380d075400a014502442c030f8100c0b003c9400741c12699024000c0100a1041d5201c0079980c0c00d00d4010b00c026140000c00301800c60800502b40b0880d134485100f00c80b50309400941a68890b100c4019040c040c01050380100110041c3d9400414240d440c01d4401d00406c034107808582125a46030000c0d03c45003281e150001144509100400802121000406095100600041c82c001e1560f0006a603040c09440521408440344018010403e01050078400c451007400100030341011a5551910310704001d09007001010201e0701a130825000700300c000c018106111440d180304002002038042c900d1b10400710060001007014802040d89002c07010910a900c202609103982e440361001d81e000000d00d500e00103030300881e0100040d180c00418010740903510a40507800d09042a104200c2034400c1c0300081422a08041d040c040041d00070312180c01d8000302c0841001e2921020741a210840108000245c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 842487293 1250 842486043 842486053
    0x5030a060507110109081b0f190210051c0207030c050a060b01180803030a0c020a050708010f050c0c0c010e0d02090a0e0706090b0d020d180c051203130b1803 69
    0x400c00620350001440754960f03036918800c42c0c0400b101d0300e080e103046000c0a452248104022400310302c1c00e507900800c144211007115024104105030031318041c0209100302915418180590851030a01e8038103c0303000e04c920740a818031800344440341c100c000e024121880264000744a40c2014020440c0c585045d42000076249183d11508000c00a030896402d010b00040680c070f80403003c0070341d4a0000c000d9512240096007103603034450100000340040c1c0401d00a504c10105100002407023007000e0030251060200100b0020744112034031058a40c05040c500550f401400280300c0b021000600d103040400901e0038014000d1305002140e0b880740d59000180d0484403d404000902d40d0075040462690002000c84507500e5039030b41c003180c0c1c0c802c250048000c0e25070700300500c2d86182d031560003811440e0505d03c0f00151644012a48100f000142c01c02180ca1001d00401005503150aa8000070720110b080061841d101c01c40710f0507841e0101d24058030400c50320120314860341e0592150083c0401d20044c0850b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 842488543 1250 842487293 842487313
    0xc0a0801050d02180f090613150216080d2a0203180406170c0f0108041208071206080f060c0a0e0409060e0d0504080615100c061103130203010609050705071b0503 71
    0x5d811903812214410540701b1354000c00c02c043d200c49031070200e8640104820014010803103c7c040654001e19844070500e81c82d814441c040703035100004019091907070b0700c0010360940c510600720b550440d04800c0c000c0799400603d1000119008000c035203000700b140c6100020400901c000400511464000c006031002d03d410090541c03c00103410401060216480040c21100c4001101d4414003214014200e0b0010a405803000340140c0c800340c0c01c040306050218411242815500c101c840f540e002000c20ba01404200e507114000b07010581d04201d00d0909140b03080007520000c5d040d001c4c201561409281c0d00c0c0320310000c1c0102c40d40195074220103c0207030303a94440c01090082072500540100102405a100032a41994100205110380a00070f807403051000004581650880b4220800fa07400a032182d0700140000f429000562280007072100a07500302c0c05900605007101c3c0143c04c440d05a9203400144031900307400000381c43c4015405140c048080e5100300c00d400c0056090b03440070350107200740111a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 842489793 1250 842488543 842488561
    0x60f110f1509030f0f0304050102040e0403120b0904020a060f0e190303080106030902030a020904081201290408071703130906092d020a02070321080c0a0801050d0218 73
    0xa0718100c1d5004991580d11404050b9031284207444a11050071400c0205054070503020006d15806401000018142a0703584d201311201d0307004803804c90010381c000d0190041c12050f845140154102507940030340701d140ac1e42c0841c961a41c0c5024020034800c001900320b081c01d00c02d4002c3d502c041e0018006120400b10800403070a40c0d411808101c000c0b4003031000200712a4401d10400303682c143c0060040400700000c2d02403190428000e803041e52414010007036150851a100e0000e80206060a40a842d2840da80040c5220000da2002426265400c010030000101c00007102c205a0344410005060034036000811b07403a41c4125640c2000899610100040d603600980c0204121400b8000c240400c1c00411500c8581005a1011a07064201d000003810809421780c050501d100f2180126040540c07284c0310390924020014100c00c90340008040c20403001ea011420a40104810f030015091003840c10000d0243c1c4414000c8038018400d0802d01000d56031039503030b80c016001e1040307840310040c24100700c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 842491043 1250 842489793 842489803
    0xf15030403090503060405030d0c0e0d050a1e0c150c1a07030501050607120e190909140304030201091a040b03010e04030e01140d090c030b2502070b04060f110f 70
    0xa802080c0440c0c40090181004902c9034446c2c0e0748440914a403006003030015001f010400c2c0044100700d42100c180040f0b45503100c4142029004100030b00c07034541c1500d4141c8031061110b8401d443d10f000100000002681c80200b80e040d244244041000400e688004035966500102c0c043c0038003107280d800440400040d22454000c1d100b9075000d03c21a80c0f18814440d4607c0b070403000030b0156804194101c00e0300c0c03285a1501040b200148503449210300810003040003031540c2c02ca060001d94500b00345080000300c01410b000040300c10040c40c05c1510b03640018014040a01c101c4001e9201050804a41405401190080d0000d207011035203c0d615100040c43c5d1103400c660450120f0000d1426100300d60042c446446100c03004000185000d01d005010000f40c482e070340d4211101c0b052140e001c800681010501481000c005500c00398001010b10510b101d0525902e0503405e64110207801c1c821000842c045409407401400c01a03001d0006a01c01c450311074411060302040d0003155019a03941c3e2010807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 842492293 1250 842491043 842491051
    0x3010e0a0f0620030a18050111090102060619300b06090a06030c091d010f0c121512050c1e040f060b0301120305040e07030f1109010806010e0f1503 65
    0x40811940000e454954500082c501a540f5000c1c001e02c00191025050340024400c1012010b03000c00207440303581e0b4942969130300c2e1900003d040d8003080e0801c0e039580c10085030380d00440886101411b80c01c01f03610105c242e012801481d06d02e414080c0000642d160020f0480d908040c0020b030058040824146401a880f007550041e11904003800460f6462019006100c16250804007030030b1101c0c5011030601c010040c0c40e18200308005c2d041115002c0c541c00b842030111188000760041409030f603640e401800ca0440d440e44c524121b2504030034013107408040d100310041c0c80404551600002c00e60816a181003004045c40d548040c2c0507540c0c820f403407001e034805020701c4019241805007490000320f00e4259078031400384a1982c00d0910040006001c2080d060031828042d00b02185001d8540b01c141c0d46258003107840030701003903c80041d44101c0000b40b0481300c203201c004207414240b00884d40020704100024000e1810001004030611280c2c0e56510329400500b00280740c1510807000200706161900102c3d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 842493543 1250 842492293 842492303
    0xf050601180e0c010e0316230a0605030403030c030b060705070905090318190308030a05011d01050d022206060201050a0b010f020a0602211e0c1e070203010e0a0f 71
    0x5107a10025000500074102e41828070406041c1148045004491030b0b4619115181d041c402c29081100c0c2c0c5243c5480d0201070070020180220810131038010100b501c05448406004820069040001551210540c1d802c00e0f810b190218034400c80c00022000f4240e01400203078801c2c00002c0c00000c0150009600d41159030b4250140026910b18454a03102e020b008504c40c7c410784072031011602c2d0301e080020030020f0f00d040d02c000700c98030f42c40f504e61008540080f90050758507a03507800103010006520807031018107401950400300725810240854140500c00d100207001e0000c03400060301d001c0044141d0b40c02c00382151010030006035100c100a0182c05c0980304c000380e075441c10b081102d00d94030800d4000301c411025002443c0d101c08a90340c200c0250712800d00c88840016080350400440b41001c000750213010705810241100e04020440d4051020240a07851450401c02c0384c81c02d20b54241803400086400001010707241d903900c1c008240502100800c0100e80e01840403002d0070060341021207042c440c010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 842494793 1250 842493543 842493569
    0xe0a0518070b031905040506101203050f0306011716030b040603020a0b03090f0615121c031107152304030c020f012003031806010506041e030f050601 66
    0x44018400c0911a4600c00038464000e084107000c0d00744403100650b007007200d0f034140710000c916990155040b1071040c0d400f200c3d83e4004000b4080c0e0041c10314120300240c0381100901c1c000b0002a98085c21520580000b07604100002c0000b0794980e0080341c0d0f0800e0171041500d90861450070318119080d080c540e216030b00c080f03403820240c2c2d44035040c98401ca20503254040d0680e02c0803410082c0c0c100c2c0c141c00040005c40340b8841c00e211445c0303420003448800c0c050051425054500d003070540801c411808412040c9107183d006190341d4808641d484031210507400385090002e42c2d5081d90314907070348500c074080001d041c2c4080d1400d00d05500f1410350040192980181901d401c542c14540b50f150310090940b170150000340302540c050702502d04141c6221a0f05014141641012035074521040d03102413402040c0c0d002e420220400c50500701c60004da81398502014090410f80d8180300000f80b50340600d001d80c982400c180420b000100d400220001c02868010000c15104c0c186850100d643d40c0090054070701108031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 842496043 1250 842494793 842494801
    0xc06300b0d1a01081212010e100305161502210310080f07050102010b0a061715130c1101060302090f100e10030c09060612090203120a0503010f0512060c0f04030602040e0a05 76
    0x800400c6d40c1000002202c03d4445034030340784518910368409041d012425481c1031000001074010010410400c184050155020b0302e800303401c5604c2d044520154095410245844010b000002c100c0410b807030035a4809501ca40750b01c0c590103049a095003000b442d500c1003e05200e21280000f8100382121307003d03030003800840c19400610403024494451140854007210b0303d6010b001c10040303080d80c000702c681e04480c5a00440400203a100d1221000f00322810740e00c410b0484020340c1b000c60120115a140020b00c2076518660101e464030000030180480c0b900e040c00445d101d01c201018540050000780310015203800d210000882c0101c0030700c0101d40c0480403c0000451110501a200c02c6881c552a00b0a801414460f90380c041c0c12400030032640340c0121114405a01040310151284a04039a100c549039030600208044004098109511a2a00280d1080b40c03100014000390301c0810784640c41d403600c0c107042d0515414050ba400c004d10241c004200899465880301d00c0a2142850b400103001c10f0315 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 842497293 1250 842496043 842496073
    0x3020309132c03180411031f09021e030c12040c090c020606012a0b07200127061509090605060904020a060e0303160c06300b0d1a0108 59
    0x4121071070709070340d0f402c01d20610489595500500c2441d800250000c03c0d15a4140e103d031150b64812121841c074000825449601841d42d40d01e4000509100d141c210f00d402c00e100002229801c07401e8075a641560004001192204090b050340c014803107600c010385450501e031402c0c8200d1042401840700e518031b88240c03000703450702c009074541c040e40b0107844d03401c03001e0720382c841c0c404101e00c201000201103030940040c0800601c441c0303e01d9200354040e81d110220324110301c04070100c00c291103041403016810046d00c0141921000d0001071801e20048000e204c4281d149011005442c0303c600030383d44140d24450002d18501ea503040340351b030140b040108003c2d60b901c3c1c0b410444800e0041d500a5000070b00c50000b80502030183c44543d1589400600300c82c00e0000405001405001100f000c484d00801600c1c10000f19800c404c801414810316500400c512a2021b141141d82c0100310800c059103440b214601031640340c1007400e0230007036001504070204da030440401002d082420310030400140709032040600820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 842498543 1250 842497293 842497361
    0x2040b1c0606090b0901031407030e07060c0b130c03050105010902090f01020609060a0f060f03080406020c06030118051e0708060906010f3912030b060c190302030913 73
    0xe0b00340d1075802d695420101d4070100380c3c02019070b80f4140340d900c00001d42e9420712310f40440c0c4540030955001c9480104511224101341c1c203036000d0014030007102c0c900350003d01310071260703540304004640c10802009a03040031520300b0010341c40a0701d194038100001c20809401d80040010302016030f00310924884070b0740126603500302143c65100d540c10480118400020030341107000c14415810020401503140d01c4542c205002c603070300c1240d80c08400607040203019014401070200e1213040b81ca0f2400c542c035042d500e20418801840c16110903544200007000048004500c0d9440003201860038107610f0500006000302006465043c4141c941c0c030300143d22584500015210991903a48202c144d000205d90301d07600401c070092200200b22081c1c01d2540e2058240825441c1d58014144203540c96014507000c0c04840010031a5400382c0010003203050461000590858403106c0d00001050072411403c04a04501440100a50010b003405104041c0142d540124202503420034003d42c03c0090291003280342 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 842499793 1250 842498543 842498549
    0x50d0e0304150518091e04020f0a14090f01123503040b09070b1602030a1202030a1205060a030f05072105010e0a0f022103040608160c0305030c07060207020402040b1c06 74
    0xb20340f46d00415540610100740d40d007152001c0d1040300105c80d0180010000ca070550000c0000e252614449001840c2408259030003d8029002026550501e04100c0340c42c0c0f40d10801400c5a50780300808417891404803a1458500c01e9400ca403280030b080041c4132191540261015151a02c00c03e01040642a01068600490703030441d14072450f00d410074040000301c03512050260f9140c0035003280400031070055100f1062004190340503543c0c0f4001e100d00a0310703001d42c545c0450315580c600740401455071180043c43c0300362904240c0030f4919219038a09146007c3c107a0304020030803404d0815001d10701011800c800c40407132064000f440629000341c4d0050346c0704840390004d045590800c590700701506001c00342843c114941410b030b440b444070402400d4039680c059800040020307208c608010b07200c0120824406000c2c25071800c00d041011030744000704030307010141448441910019283e0200035403503044500082d4050803d64581b651480c070002d403078100c3d2513214071031400c108070301e40c40c00c040d40310361300c19 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 842501043 1250 842499793 842499811
    0x60905061206070503012106060608090d02061e0a0e0f0c0f0904020904080702011403040804030606050303031311010c0f050105100e09030a0833031903050d0e030415051809 76
    0x17107138604000f0005800202e245411040c83d1030391a00082000360150001811050f06c4183c09810306040300703403410719400440d80445d00100140510804042c0d00f01801d10355101c01c2c2079803030f204d40c13045000800101510085610500d10300e00030605000c664101c120301d048230070251070000d1034284820058100d8000354001060000a03000504250107002418018074207000c6c1c140700051402241e0380240c40980d00b101010030100200100b034080c04000d060b00b82c0c003942c00c40c01c000400320b502c03190185000f04031641e940c40443e1141d1142c000c0600c016000491030050106078286213009040591302509050380c0c01101150540549881601070040034005602d40b0b400da00301194052070290070105000c400321a02c02040c48603804034550b6951040421281461410415207801160841a46644100080384020a82020030307158484440c4070f0105007401040d0305036041d842103810141d02c4070801c0c003005903105e5019002d0710140c0c0000601c420030400368420416607100464010344 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 842502293 1250 842501043 842501047
    0xf030b0901120c0305070603050603070b09010e01081f06050408060a02130e1506030406020a0e0102120405190503030a050d061e050105071103240f160c0309090609050612060705 78
    0x715a2011004104960303006080143d08591690b60740f13418400540d00c404000781d00c510a20030207280511640c0000c00307100402c90b10b407086905c0041e085001072510141400043c80c0045c403000f0401d180c1d000320030304401001a0f00d6440d004080c2050f081400b0b00e40c5903108000c0090300c101c0e034078805c03225611502c03000703041c00609c1e00001c01c0b20f01d000140501c44091210309001c0c03803900e03441301842c049c81c81128050b0300c0341500d00c00140030380d81c072260036411540400121200c00b00d401080382d098543c117581d0240301031316030a4140100b400e9580515007500c0002180740d4a03581c031074083d1030741e0640071406000556683c08031001c4c0c801e0f84480c50403c6e407020f03d0104034560080008101d403178030030904103240c03c6e50980001d051000441c4014081004c910000f00a4168005480e9105d421070326001e42500705001d000507036001062511050041018210060601802000d8003c11300314105200598441000d00042d200a40d0795900034000343c2c442c4104c1001c0403401314454621959194 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 842503543 1250 842502293 842502299
    0x30207030b0a020904061212020d082a0c010507080c13151110050108071e0302090c2715070302062206020708040e090f0d051b011b0f030b0901 63
    0x14180394005005221095800c000101d01905c4c1e40c02030750000d0140c40c150b2401000a800c04841c1d2001c006078800854108014818030660460035280d0040700c059540403070001c245031070180c04640f1001e1903042d041d0200c1c0c008003071041500031922440036944c560b100d070380b213081c82012640111031400da000110701b0400d11404402e4420b940e0b2440081c07601c02c2c60107000d045680d0078401212446042c403902c440c018090750000300324050007006c103d40c1154180005803039006803901c2c2400001e10404509000c189a010804d0039035000040911503194a20021000e99004403005040711340103001110b051720384000c003c5c081d030b5844d9030990050509aa54003100b81da41401880c001c240002800c1c8100c030114010b84040c09140b40700b09807856030b0300e06003848140019401807002c5c0c1d09a0180550684072200815020301d40394480c00c020b92603041000d032041d540c42940090303028561810600302c100701c181414a1140340e555850b120343c40f10145404405450a1a45260700709880784010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 842504793 1250 842503543 842503553
    0xb0f0901080a061809030327020d020d02090115030612050613020102030d090c080106140a120317090a031413060c02031501081605010e010c020609030f100e010b0d03020703 76
    0x16a40c000c542d11000a440c586078003e14510522960308a003481d551203245004040e0144607541000c501d46030814101c0340a650000f03452412404000c0c018610324005c0400c6407074021410440541c0284082059a110f511100d0110414803007600064108940014505607192003803e50540240140c02c2e40d80c0e0b0050200200315603404102e04502c0b04211003400f8411900c82c0c03000951092440d0325090f844c2200300343c29107845411800e0702c00c0315580b52a0165886040140c12508418280c0814110a060546201c030b014000b0760b40400c440e40400809d40360210320424124801c0c1c0b1120075103401481500014010080c0f0202c00390a2140305000c8ac50290403508002840102160701c400410096810b07014401ea00c5084c040e8030244040340c1d41c00c0700d4035a25001e48820320b00400e0484452000030421071382c020019014683c001a010702c0e54400f8880d11881c81440400c559903440010f1800009211075541301266500c1d2482d01c000619202210b150107a400d9401046210704645036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 842506043 1250 842504793 842504807
    0x10806040509070905100f08060601080414100216121106011a090d05010b030d030e0316051c0f030e12092209030807091521091e0c0b0f0901 62
    0x1902c0d0511075100005045a498004c4512039810604014400c5242500189014004c0e40004095820800400140741d9020b141d00340d110f600114489210340c43c4586003030a011440f69000181800050440342e01d50840c180850020703c1810a466044048502102d0401e00d1221b180381c01c1d00218010402d21001c0c40ba80c0d9001016100c030342d85041f1000c2c0c0040e01d0006d6003039007110107944030640b504072450240a422120b0200c0d060a01c0b03d20b5100080d1516031181021610b44074088001500a2200c10088030320552000207444012081c00075010782a0007202402d08006030910001c80f065590100e00b54015003910380030282000f117400300f00804001100501c03040c070601203401c9070b284540342c0504180640207444142003800c1c003a0009103000035981144000f0091a040b8080190f4401219111400101010720114603d0030042000d0103005001403d1079442e20703440020350000d201030394211849004440103040c0e6a21100b00f07240180c0407101e041840c24400c0b030640d9400703a48 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 842507293 1250 842506043 842506051
    0x150d0210080c09040501090507030516270803070b150105130905041a040c03060513020f0906060c0709020c07150206280c02030306032a01030f020904061e090603020108060405 77
    0xb8034182407100038008074045030000d038441d00c03a03681ca403014482c0c1283c161141581041501d0707000b61440002d550054141c0c4503200990b000d0218030f623007a80f00340001400c01c001a0030100140d0344c3d0b52030341342030519091074160303030b488424800e80a40144960040d01202c1580c04144c07200c00045107856007020040c28020400c0c1c8602e00308000d204850307041102e400703100c0c910408414213a213041d418000c0849070f004000d0454030f00c04181c0f400241c2d0360300018025085086070303c2c5401e030707032003002180190081010081c45480f0f00600841c40c0030321034014200301072000d011190859901c554542d0444000d008031400740e002240801c21601d039505044108602e0700340354000125124507038400703c0d8256407005c0b006800110a10010b840e060100581c0e0b80d5603d0008a001c0000d251440e0b06100d840b000a41415956aa1076070340c0203898040d1030340c0da03100034010401660746e0840c042941c02c1e40305440515603810000418507481520841c03042c0ca40680d0340202d035503144020b020040c4030140c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 842508543 1250 842507293 842507311
    0xb0a0e101e03050c0c150a0b0a03080d1d01022d03010f0b0a030603050d170a0e030a0c0201170c04030209070914040b04020c0d0905120105011805180d0305150d021008 73
    0x5030117206040100c055202c807000306e07030101860901e90311000c0700c481001c040d01ca094582e4040010400600a444086450305030000740c41c400c40e100040c8031024149001c900d9400400c1d1020750800c0e504640082180041030142051031039001d038400c2d40f0007409004c0000c1c409820a100750081007019100c0701900e414001000c54507030f00c0b01450000b00c401000005081c254050020342c1c6640c4202d030704501c207110140100055608402d469000d011110000c0250104009095a100300a0729252100000d951405d604245840b0600c1d43d2080c04103a010f100400c01003505984a919088110365604020490480060040002501e0080101380d40580c080c003003070544000611001d0b690390915141c024100d45850144951401c20170080c06050b4903140040ac961000c1c59083c1c20f595032808000149913a480f910707801c0000c02100f00c429075200f081d02c8581807a806038040c1e030180c00302045460464400c0d104000c90341c0181140250025400805044007600038020903401031440d07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 842509793 1250 842508543 842508547
    0x303090a0632060109080c010801061b0f1119080a0305030402040912090305160806040209041a1e010e011d0a0b060c15100f0e0c040b0a0e101e03050c 66
    0x804010003462a48a140d0480d222002c00d10081d580c000107442c008107400340180144410200010781795480500c61001813008480b07281042c11361040c0b04000c0c2130ba110b000703160a0201030420b0a0490b191400c054000c180f81c4482c6500b49080031248422200d10500034421101c1c155001c664541020304100e80289e11102010006042c0803403602074044182c1e1902003142c554240517103041c24581040e07005956200040c070480102013111607000c2c2d01900d06088580b5a07252010100000701c2100c13131600001c40a00c403000010120025202d020b80344440c03240d907225102c42907071480a00c19400c4200a810146c10801c2800b2922036004201900000e00c407a48000072409960111075801036940001204000fa5803d006441d90028044010089410308203072428000700c0c20b81c003810040c03800b03034000118a035030140d00705c402901510001d140c44240001000e408805481040c40c0b140075140c610303030304081c070807140070000300a6031070500a0000c90b20f0080d0010600034000070042041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 842511043 1250 842509793 842509841
    0x11130b09030316051501060302030c04050402030618130c0e060105040e070e15070c080f0717030d06090519050412051e0a05071b0b0a111516020f0303090a06 69
    0x140504452070398043d4002c0d01400d04200317599080310074160011020b05105006004140148100361030560310182c5006941e5112200011a1740b05181800001d0002802c10001c15590a95225210a00c07604140b050640c079060015641e14040f1a1580040d5007403108001c1560000002c039040101420041030f040d05800c040f418050a1604004621100240307090405c40c0461022001f0302c07003a005400d00800740b00203542c0301c1916204601e030040400b1300406090700140122102c0c03030b5010004201803a503580c100c2c3e025000481e0901c1440e4994000480345060501403d0b1049900200a009642070b920040c0d60503008a60041403000508800b1b00341802c9240003003100184075141c5548400b40d0b450488800e80405100521a06900c00304000c100644002e4030b11504246c01d01060300000441540e181c003c040ca481141807041d8020700101c0d1910800b1109550002d500340c031a29000840d0b00c50390303444241e400300d10340d9100c88500300125482e940301094040420200c001c429007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 842512293 1250 842511043 842511067
    0x90602120306090a14070206011a2a0f19171206060c0f0703082a0304090207150f14070504050915060c15091501182a020a050111130b090303 62
    0x1c81c2c003100564002c10052040300c1c0010320902e003115606003c982f070250306003080404081a140e07071008030039020f811411584001c2c05003500100d666011103482c1c4640200c1120000784103142038070100c00b4404001d08403080c82040302c02204101c0c00e980d00540b2041f0034080300b035100e043e100c1031a01070740e60f11f40c41296082c441c0400443c0a00001030f01c078403546489240303080404d4855030741c50924102110b44920040161012514010b000503102d0580c2c1c10018941010014004801460003900000303041d01c5034010b00031007070207141d080600e50359510f05403003074807450281c0ca91010000c00090319207100c0c55500c03c00a400500014100200c60030070901d0041c0e207259543c1083c40788802c12008000800c03007440c85216103500301d096540f52400d030348240c505906049690a883d00c10030314180f019020740c0500100c03100f2102c034031240f00c3c0c0c0d002521031051000031541c43d401c1242102450308458152001e003028641456041c514024480c0c90350740c05443d58580501045c05462600c2c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 842513543 1250 842512293 842512331
    0x8180f0d020304170a150902030705040c0503040302010e010c050d150b030f160206011409060d24111305010809100603061d15070f120903050a090602120306090a 71
    0x48101c0d0000c640703440c00c003250f102d03112210101001155000d44103620200e10340020481e290301070601c0016041c010750010a08102458110303981140c1030040038068640d00c040150721882c025070082029500007600c41d0700307940303d05d01e032000000c0c010b1000b048d150025074000c403c01c500f00d40051180655906544c4003a80044038143c140010300c00810400c02c0360040f01e00c0345840f0300c0c40503041560409010059801090300c005018410030380009850b520b43d4241c0496a80e00441c2d0060740010484145c00c0d0743c501031010b55010b50030074540180e82c4c00d0480a035546542c006415910b02410000115004c8000800311200d0b8465180100030040003440740001030b501a41000c0745000c80300500d0303030f2502500341c0002c4243e44407c4010440076089501c898220500e0300d0500e505180004007110a81d28419881c41600d1600c4561010590000c004181c041150b2b1105081d81d50340e10b40030782e02c6030440c030182c40600d6800c0000940900c1d00741c242907070125803c4000284401510788142c940 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 842514793 1250 842513543 842513563
    0xc020907031b180e090a020310020306031504301b080d1e23061e060a030609180b060a120b06150c0a020f0d0c050d0302011b0201090c0f0608180f 64
    0x240d081b13030f480642907003001e01600d02c1207192140158514180300c400b00740e0b00c0f415055942100c2d42c8003c00700b03081000c2c183c4494400503c06225030100c142114524201d491070060302000324042410403181d5290580c2c00300401c0e500014564100558248040f024101035001c0062094000300740712110800c1d88120940b0180814006082803174100d5924282107021f0b002c18415200030024450102c40100228140030094a18685070b5000c00010307030260034190403480078076081c610410345183e03940c0100c2070801e000e40000e0074103803252014040d0a90a03401040101c0c01c40c1c90000001c036504800540c0c06c40b001030180c00002c40c07000c892901d0354019403880091500300c40312050a501d03140c402040213406c22141c4506800030795036100c1440b03000307100d0075002c0c4050f03034401c02c20f15000303500448103001e00d12044140b84540c624000c2c020302072920200c540380c84010f008951001d020020070151101506c41410390b45540c00400c2401080b91000125440b5200c0d10980c1c0520038854a428 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 842516043 1250 842514793 842514811
    0x150a0e0f0607030f0203010503061b0d181203050105060f031f03210f0f12020706110403030f14040306090c030503040807081b010e010c0303020d0c0c020907031b180e 73
    0x81d070420490060039200d24848038030a20717005100510451382c0c00b2034601d802404100010801d004038000e035030102d000701481c1040280c645080c03204070011a4007000c0c400d038805d04003622400c40a1809070225482030003841e4000209100c180c10540100004641041c1210344039228807070481007007400c038803e40d0000c403941c04001007000c2002d41c0d42c0542e1440440f2508115240c6c50504100402404150482c0c000700003d46215001c80d143c241d0446100320341080f001d01c14070400d419440c0c801e078850f10048001030319000e0554519840f031010440d800b801044900d14191070b6464078006400c00304029101002a80000000140c0c00c10042004212100141803020b151200103820068051145403004148400220540c0e9100c0a11181400e0900b0447d1112000c2d042c2180280030f901018138030700d40782c55540f01c2000c1d0080785820506100f2240d0b404156078442d01202030700c0000c081d8840c9030b10301001e11185c0d075004008080380c5c030300041c103003400c0c90b56500c8030200713801c1d030a03641c18107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 842517293 1250 842516043 842516053
    0x308091606050702031e030d0903092319120f0203011b1112040f0603050c070609060b09150d02060a0e2106070c0309090f0e3408150a0e0f 61
    0x714181880491b8800750f600541d140c03403107100d0490b0358885c4540c103044220f071030f91001c1e104201401119240c0180400804071f02c0c01c0001404901d0f90611381f82d014034855102c4a2950010b0b050344030b04842601d5181d0032100c0108242d50322080414003c141c120381c10354a61041d01000e95a021812502030000d95403a4007040d0451400c90070a04149650440400d04000038800c1070304d9a03006108035442d600c1c000981d9501c400142656018288005044504101c00281171051a812200c40d040341154011500d0700e0315000208100d00d411519500308040038020070141c90808040e000b00101401d048070002c00100005401c8a4030261008482405420652100104000081d400801030800405a00c0540c6000e03104c3e2841e4480c68118a444681000408180e0341280300c01003003440c2211600b0880030108003035144014040001805140a40701ca108042481310086940c004003034042155441d4080c005c01e03100034206103104e916801a64650030080000c4032071109a080902 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 842518543 1250 842517293 842517307
    0xd150b040e07080c0d03020718021309022b0204260d03050c16050304030b16080703180f1a010b0a14121314030a050408160b0403030809160605 63
    0x310344145516024a0b80100300610900c41c0014030504c2040c02281c0c100004881c0e0729080b450070904d1340103500e81900380700300c810190342d80c1d4000e0320049410700a50003040d03031103620680c1240512400001000c0300c942042d09002020741d202c4c00725000100000d4a02516401900d41602e0103281d41c1000082801524440200500480c0d201308074519080c0282e04044441c986180502c070a004000341400301e9030000c1040820442d00203542c003000c18100d40c03510003075070b903004c8c12110785003008030f860500002c3c10140301f4410003514580c1000c4140071344401c1e1301c460800d1198420103c0c0c6207840d8502d01c4034142100c503240d600a01020b00c05030b6460083c070400a0111400d5030840001000a01517043e1311402d0740d00882d44841070201405d11801c2a04124070f0541a002603599107000005414075402d80c4000204165601c440807602c0118600564040e915168400c80780700d018180010f20000740f141346041d0300b0010a0044442c142089203048042411540c010004580300080380 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 842519793 1250 842518543 842518549
    0x303090c041406091f0510030f1406130213080a0609020102070605091c050c090420090f06060723031305090f04111212130e07021b0d150b 61
    0x41c040d9404882c1c101140e03800c02c0c07000700354402800703070000c0300c00118030110108200b003882c0141d004002c01486000c0102c8000c1c4007800601c4a41da00c100d13081d080c0f00041c10b1b81c0d10002c0100340244409043d20250b1035000c5d031000001c0d00b008501c41c8106454200004c1d0800040108011040c01303100c0c0018012028400039180c135003030f43c2c000c03130605c0700920261000d555451400a030b4460907c800340d041801c1440d00b50700381010344034400d50000c0d190051005100d0500c0203a00c2505030210007143c10080142001050002181e100910700550700000e10581004806401e071280b0684020120003000034040c80e0007040200200810b0b480415010720701155102035500a140a48000869081c0304460003140800100040e06c0e051001040341c441c3d843c2d108601700a0500b000940c2e03c80350000c01c8020442d0b11811483c3e005412580d4085590a5601044e46c000c08864004245a65003000c0552900110031b010300e45c08480d03680c3c01c01c04501c281c145818203000c040da00150080000c420 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 842521043 1250 842519793 842519801
    0xc0c090c030605031605010e04020409090b04060b030f0a02120309030a060507030b010509010806150d1d12090901060f0203041805091513150b04181a0412050c0f0303090c04 76
    0x8141e1081c5d0004804049008103c8400015a0070078600859601181e0b40820068402d962086032030b43c3c036014110003800181c5034810301461069200744518207202007099501d2100d40194081c42c0c11500b81600146040560450014100c005480c10701e0704c01d0b8006810700c669050169820750300d440c101b001441d403501c50b03504480004d00b002c5051042c0340c00020449000204824020840d840c0006550368940c010b44040000560b02802400758032040701d82040c81d40035100c03815105004540341e01c00c00510a0390302111001d0b04203005c0c2e80c43c285089070142180c06202080d800200000701340412220142c0f844601918800300d4179003000020b0703600d01141c80e001c0403417045c20441489400140130700450501e43d040701c840c0411901c1c030801e500c002c104420005910501e003150b504401c5100d0340050072924054240d020300901c8020020040e07800c1150300811600c490030fa0b00da180e82c02800a084002001002c8642d5007500000051659109a41100c0e00b5030220200401130b1600d801707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 842522293 1250 842521043 842521049
    0xd1515050c0c220506131d1501050f01050706021611010e120616050903100c08010b030601020d050c03071205030117070b16051002040e06041802030d0806010c0c090c0306 75
    0x143d0b12482000c08042c4059511006620044103898402062030303079960400048070480c49031002c00552007801d61000c01400c41e440d9000c418000c003030208800c01c8441003000c0c100c1d20b0203022072820400e418011120743d4460041216156428040145010f20710250041828030681c05007048420520002d4004498180f8143c8150345180300408151008100b15400010203403d2003550641c54105441900130485440c6d0180b26140821200040c260880c1000b07041c252154182d0740d8a50065001510040394510701690010580320802486440104440000c0f602905d050500e40e660302c0c2d0348a0000552200003070400701c01802807502c0302c42c0c03248001c0300100c010b01050780342c210b00c06040d005540c2c6105891046000b00d105014044c03000300044061311008550782c83d281c07008041700d80829129107019a2130601ca051200c000040609030240d0014000d000e92550640111605079000300001d042100d00d4142c04009200003031040081c0c6406080401c011045080040448032558 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 842523543 1250 842522293 842522299
    0x17070501022826121303020c0118080a0809010315060c0b0711010c0206060310060e01031112030408030310150806150f071505070f0c0305070503162010050d1515050c0c 74
    0x5c41010002a0006a42c211000080c00c14000e1035054002680b6000c0095000105601640c0624810081d45a00904000e1003d0700e08003c4da01c241d02980d1400c940740e025040105511108000c0801c030005021a440790803440e0100384040351590660a454110030100056031002060069900c2c0034407030242d003200139043c10411186842401c00180d2810b2002a100e00360b034880202458450076160403c82c115401240c2e96907681e0882d80b942c031362048407041c0c00c0503d56140401c00880d580c208502403a6517a40b00f0702c0640b15541007102c101784034140207001d203900b046100d0700601024080c0444602903c1c00c0000141c010458200762440140841d042141d40c1003100f1300150004481ca0000741c15240c46520f41203149002842d5110305100c0407031003804810030038208100883c80c0081001c1200c01820500100010301902c01c000b1000c00c00401c0081c001041810340541c0508015a904140009031a558506410107528049145800624002941c2c00c42450400c10251624026 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 842524793 1250 842523543 842523571
    0x21090a060201052e030204020d020903061815011a0c0c33040602060106080c0702090c0406020d2a17031e0709060804060b12071707050102282612 64
    0x111802015113080d00009100e203a01141d4116122086d9042e26005030703002c0c00302d50050516052041441840c1141108a4400c1a02040c030000c1f402000504959140ca220f078840d100c1c80c81c0015a039081921110500c0c4541260844540e13a0b43c40e14906040345034115419846a00d121000241000d00d45901302030401c00c8200b01c8030f940052204d0450700186080c4006481c1d4101609092180b40c3c0080e520101410520031811030f0440100100e40c0c0b01d8084495110380c008094074040d14038241c070114200e8200d402c2104140d40703100d410310309100d0600c0340d020525007001c182d91500107540628000050036281100700c51001d030651f4210381a801c001c403000b854620010000c00e00200020144da49802001825485811000c1c602c62203d8003918078913500d410050404000040c0044154419a01d00041030b5001050700320420316010001e07148940140c894905000010038200c6010b4031004410009200700f80e0380c1d10518016088195a0b403080c051491910100908489428008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 842526043 1250 842524793 842524861
    0x50702130b2106070309020a03080d0c080603152d0a060f050306040b0c071e03030b3307030e060a02070f0918060f06150809060c070521090a06020105 66
    0x2c0040c207168812000e14000c11603000b00e06c00300d030780711215610083c130450002c03842c00120a025003200f01e41501035600c020340355a80078201581d6010a40502aa0011000120311050740780008012781051903c541c020014400d0640200403008807015031800e5541c10040c05401042d900a000510307041300204890305081c1c941341d503400d001504449075500c00103000c0041103507220480340c0b4015202001c071965a22070502030702800070042881d1003907824034001980d48021441880c2034a181100700d0840101040100b03940b9846104241e05204810701c5824042d511407005182e100708641c081c02c00c680c074120300021860540d030000b040c840d080040c070310300d103560000c0c08002894000c0e40206150002202d250024050b41e0400352100c0300c40781c00203c4140e0400542409411024116182541e50310801c000d1070050410050407a005030060429081031007000748a08400409101e01d80191100010864101c645c00350016035146d030b040154a440543c1038694035030603160700c0340380000707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 842527293 1250 842526043 842526109
    0x1c0b09100321020703020901030302060a0506060a020307080705100e0d09080111090f0d060204060e0a08010e061915090f0e010605010e0625081902011a0f01050702130b 74
    0x2c49928601002e400b41042000552007089450011500a44140600e50f16820000e442d410f045804071030460800f00840c003c1e040071801c6071504141a4007660416509541e010210b03400f401c0181d910f0310038011004120810343c4221004040301800500301c2a011100107400d00170a43e000360f40f0760b490140100201007110048440d0f4200441e440c500302002e000c00945445041c400203000c81d44081008103405130005000944068121424a526a5251481826102c006d10102c080740c100d00042458030303040c485050000c00e1000000b152541030859028100b00c0c2d954004e010306c130340b6295460301001d400d00c103150043c1440030082c03003030504003000a052800e40a4000c0e024850000e200c148400070200d00e040c400b1094441c0c400810254103004c103080d00f04905071a40303180b0044a00305018014403031a010031a055581c00f040d001600100500d48a850400303605109003040704500590f500440c000d52203103000380c0041c40c0c1002c06c00340071143c2840010403043c488507a4072030425807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 842528543 1250 842527293 842527313
    0xf070507050d120e3705101d1b0a091808031008120c122106120a121803030221040f06170a1407080c1c0b091003 50
    0x106031070a00108002c1c40003640002084c13810300e03501d228001c00c007130800d141401c0003c0750145005412a14089900784008080c90958010010001d07400841c12001d008040d401c184145203484094a0140411072a00c90602c500c17a6201c0034804c1e88440d049000d460001d880c0d00182a4885042041d0450040034290204c1c2211780604034250201c00201a000c0c1c80d12518007900c0001c0130366800d140030350009140342e00402c071603182038003864504c2c22140b550300041c0c500e6039a08081c1d120110044401800240c6005081141c01841d0b081d00c01010301c104105525100d407241c3c03219290030000c1700004281021011120300070510100381080481c1c0d00060041c04809500b4400c1e2000315621304c40000d0b031096520502101c0c0382c14030300040c91904814148101e002030101c2c51601d035126842003041b0b0301c04001c0d1185984003100401c460a100d030b00d1150788000000c1140d41b0300315040400c4407589a2451318a041e694440c10b629803039045c00a05103420082c0440214082411955030714640 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 842529793 1250 842528543 842528563
    0x7030b0a0204080c0d140a08030103060c0e030601290a08090d022a0a030b09060f07210507120f06061403130b0916180b0f13020901050c01140f07050705 67
    0x188100d08031701c014001e0044001c080c884200d802c032084d0764050300d048003445c0c00920007035420a10f80080e488006008900c00e045018000b406480c1c141c2c00c288507200481d0349411105500300b107164410300d40d0007810005000d0034903140c40e084001d19080109603c0c20034410054811074004004062034607546010b4200c445051214140b1241152408624481900ea201030310300080c200a010021201180642c003485c066101491b00f582c3e0404144c03004080441d040c901450340b280700300c1006180381e0140d070b0042c8440c80e0026000055001d000255000519646402c541d900c004100441d00604c9200e60030208181450840c074140304a0b40d868460b540d0090902403503440060a10202408011170b92002d50407107500355505d070310340040300041c0d158001e200540780814250a07494000d02400310b14800a01492035480c056403d48083e403c080c052a040c014140840303400a035082c0aa103036000180700058a051414004843c15110094402420301404000c0e6030003064021480c9480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 842531043 1250 842529793 842529799
    0x30c0d05070501052104061b03050f010b0a11070305010204050a0e040206070209091e070e0705091f110a05010912090b12041406150a06031e090c0b030907030b0a0204080c 75
    0x4401d00d0700b1410040031040120002005c403600d0410040003640c0d40702e0407014084000440c3c0485500f18140d0072114241c0d1b055852854241c0101b00c810541002000244c84a03e840d4a8000380000d500d880c0c100503810403142a500428244000e0074582d0000004182580c0807001d14245900419010f2188a80c041d019109103000252603503810454108018000500c07415140909900a512100e550188105110400011404051280e000e44484a40081440303480d05030050324664004640154141441608410101406014480f015140d40513200206801d210b9142405c84084010303042414009039079810b108080700344050360500d02c07a00b0852861501c2d17a00700444101540c0560300041d1256400f0407174500c03c4007860740750303481c02620340c01c0390140c903440207406803900d01f0244200c000c2c0d5140c1004a030480f6801c82d28006000d07680401c081074454019a40c0d6a1080382c42c0340301030f8440c01d410020031242254040c0d02c0902d2007001c5040a040c061035507191043d5100080c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 842532293 1250 842531043 842531047
    0x15091b0f040b01020712151a13050a0b06160c15020d030b15030112031103030705090f0604051f02070914060d0c05090a09020111030313030c15050c0702030c0d0507050105 75
    0x2005900030400207000c3e180c1210010104182481c00e084140541f13141c9815a6040c500680646084030005000019004180074207001d540c0700894010040140740e200030b2500c0310075529850300c45000510085070303000d8880041000300d040c48140301d1119030107071160552011528001540c0400c00c00510340c10f80c50041414521a0300080d564800080071100c0d5050000c00050a49a15800004813501c03d840d5014002c1500119680b203003c21500140850f004102904036441c0021489541c118000d0180782407984a0000c20071100c0790b103025215185000038500e40341d03901005201c008150884092040c1d500301c001d600180540540181c0c0030f2409103d07180200422031580c000585005011090b0601d00130030110040c220400003a4082034101001840702030001c41124404c01240300c440b0925102983c1c06c6801080c182815180158945034240742c0d881076009141c000e0080404c956142c140c0d07401010309020020880d548141602904540002e90110300c1d01c0c204c46090034550303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 842533543 1250 842532293 842532311
    0x151306091a0d08090d1703150f1816030e06090d090f03030507171b061009150326030a140609100b0a020a0807060603061b0203030a02030c0c15091b0f04 67
    0x1b41000101c0c5420400520020042041044000440012040e802c89030b016903940c100b424009000003a203071514040c03130070100040006e10250320071509401c891a00107180038a81c0203440c20400e09603510300058110203c01450ba40d07001000201503d070f50481d5004180c90f60741c0c00b401c5445409001050803140168080b04211404252901010500c942013407900701074000c1621088104d4841c80c0700110401f0200781d0046070310841910041030340d403c40c0c0c003600f507444074100d07031249100d50201507008042d0f80e1400c2c4018800346010303801c141c00100e03031401c207a440c2509141004000e5400f03001c5000410818852000c000d0007240c0c1d02d44a4980c0c0d420b10000d00701d08007212401d0103008000001360407010403001d5800328003240d0241c2400c01c41103516061b459103c0040043c020016070090000c56508107603a402503410501c034040d02454144070b000309505119240048425030b22441d401c2000d030440038854800140c400ba020364000c00c0d400c070000744041a03450320300360056503680b00c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 842534793 1250 842533543 842533553
    0xb07020f0114070b1e0a0501030302070603020406020a082a060907050d050d08070912050f1903080f0c0712050c150610050309101b110312151306091a0d08090d 70
    0xd6100c2c804114a45180900090007d0042071004030300510031348400040240c03082c8203807010380d01294040e0848402c16200c4005075001400340040d80103004518000880e0001c8418003a8181c03034002e411207103081e002d42400c003629540500d0140c44181c02c441d0004002254040148201c5d041100311b075250600100c2e40d000700c9812200301210145c404070b05126000a100030fa82d8018003c460320440310300c8001f0580e0f051008024003141d82c0d040801c601c01c075881a03180c1c0c4582e8410750365040c0217035510780361014850002402c2c041f910001e02681603640601865080c1c0d5a0001d1403103240c20400d0114503003a040160071003c0240100220394003036001c1c89151000b40040101740507902c042120071031000ca0381c84814000c5622403024203a160004404e8561001121f03c0c1000e440d6207641c170348a1007000c80440319a109000c007140158800841c450b600c050304003030300002403001619004c03483c0e08500740e242900c40d031208920140090b0032036044401a0905452607a0f202a00e450a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 842536043 1250 842534793 842534821
    0x1a0712051015030f05130f080c1002070b0a050709051509040b060a03061e06020c040b0111010f02030118090f170c010c050921070504020f0d05010b07020f0114070b 72
    0x41c45074400080d1401c0019505400904014480c032008100d16140e80c10f440358501c41c006c8004204228480104002c1422100503198444040d420f490185009034136400880c2c2c00084101c68549045041c049603840d144125076200380c1c1c9040ca401141c6c1054009402840c0c07021490000701c00004841d4417907180c40c3c00820440c0c40c060400e58640d05010406000751800b8020628007201410000310b040c005c0f0021041200d4181d000ba0070415039000604c4044c01c00c030016541404900e580102d01c11409200d0b001c10403d40d07210060b01d9504003000c01e078102c6501064850001d04042004001c6000c80d1210700599a021f8444d0200581c0c203038100c440c0d03008010382d0748125460100d920240702d41003070003412030000c1160710004000f0f08142104200d04150228002c99210810a025900f4558000c1512032540c2d44102d003003d894100710b40035100d00343c0015001c1c1c1c001240ea0011820030014140c08401d0034200600411800418481203000e2844042e143c036507880040380481d040c1441c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 842537293 1250 842536043 842536049
    0x15010804170306061e0d0c0c110114070237061d1503040602030a1103010311130f0c09031b03021e180403050a02060603120a080901180c031a07120510 66
    0x841d4006911207100100380d42c4d04441405070701c0078240303c5140c4c1aa445a0200340c2c0c2395a00030703c0180003038070840046aa00b1401d60303103000c20000801078031001da9039440044141462a2603003412a07408403490312032010085804a48941c00d03100240310464018111381001c00784108070100a42d401000606810800c00d640b400c0d0000000c140000d1024a0300190b110b420754641c24484900021992101d0344000d100103098000880d00c0d644040ca091440d0a0307030380340215408a200c01c210781e041d41c03c4034103104252001c00d400d0b140400402c80400c0da141c445075105040b160003e0302d1754001c0740440c1001e40811450840d2191000715507a1410500c9080e420702c1c810311309880c0b074280340240c0194800072a580145c45400002a014600001d9085800b42e42019050801c80e40320804c1d1007082000d000e000c01d03175484000e062000ca0305a405400b000e4010480c9074a090f00d9070070000c08002c0c0301041408490401c8041090094005240340e92038038403120009a00d03a9409500101004290 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 842538543 1250 842537293 842537317
    0x5e12031404030c0305150c07080405040902040f0501090b010801080d0f140f0d0203070e09071d03030d050408092701050d080928090513121b0305031501080417030606 73
    0xc0c010041c007170000307520f0140381e1445400c00c802d5150795010310101e0040c3c000080000314100b0043c09181840d800c404055803002c2c05c040340f80000100e044069443c244c08c14000d29a8401c021060356078005546801002a44090011030b440001c00501144800701c4880c20701803031140c004583d006010440b06511104801c03070351214014500c4030069402a60501c000071100e040c0b4407050318000a009020381080c0e01c59180c450400410505034100c040221039050205004584c800070050181070310991280080303644d680705190411642d001c2031064900b000901200d8082c40c8001640000d06403281125010b080f242d803480c0c0500188598141d49401001514088850300810503405400480b0350340b06204150310b400d004011150107c0d029005414441507020124100c1c3c0c41240c1c4107855460b1807281c03610005094002071010b40401c80007e0300020401000144114040310100c2d0246810b1040d4241601e8050351101c40286c03605074048000041041607035404112241e440c140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 842539793 1250 842538543 842538563
    0x6030a060c0e0109061106010e07030605060d0501171b0105070c1d07030c020a031706030705030703080c07150c060c1803060603020916055e1203140403 67
    0x200040c82c88501c05480d82c08544101404607589024100004120610302d0090269a01c6e0040786604880081e100d00e043c15510080428141c6130a80102091000040702141551400322000400290b41801a800d9000f41c3d010341e00e0150340c0000445080d0003440c0c020f0f250000b60620302e0180d21181e000000c2580072a0f20242c02c1c0000040f824070038040c645040241195858090382c5801ea54078000300000e0081c1025016182c01061150700088054211025103450300c0100e03240903c650002d50b0b85000210b01524210b0081040b0030191582100701c2d9a020308210000c0c08103148058002c2455880320024907109100e00d407a844034066903900011a680c2d00d0811800506d103030300080e0b0051410300001740303d41d041c000c0c101052746e100780d480501d0410141c2c2c0045454242e007410284485284104003402010003401040003642092081176015407000121400750380c11f0304500c44140d200200f041100030f405441555203030141011007646030703191010a03c40c465038100510034103070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 842541043 1250 842539793 842539811
    0xa0b041502040602150105030f0c09130606030c1e0501090902280f11010b060a050f0c0304030c090b100f0e01021c020d090b040b0a0c06091a07030c0509090f06030a06 73
    0x10005500d445c10030040710a19050b40ca07101407513103e02105000c042d65601500ca5421281810b14031b290740540000d01400c907245090781e4007401d6070b20991080d280c401c000901481614403003030312170080611040b25035901526103400a402448580304283c081c2e907001c240f0714004421075200d00da24017030b130148120a0600e108001b9040403600c0e000040080ca41d40721048030a18144901c000f01200101020304206804804035501d41c0310707041250b0441401d00880100c0c660800250010794454904101400d0078800302034110b0b458040c0031807140e000080149445a0880c01c00e402c81a11490650010541040140e00e410161002404041d90700030001d04410740c00320381c545507401e0986da54114903580e42c601c091203000d01c0c00313603164410080000752803a0b40108800c003105446244080b5884c1c05c10f40714480540c0070301e0380300c0b8003416000d410007464591500c540100b02c00c1d582811801c00315000302180004c00001c1104a0410580703001c0342440c0e03020081480c8440c0d0008040c080519 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 842542293 1250 842541043 842541047
    0xd0807170d0c0516080c030408010e011b05130501120b120a02011824030e010f14061c021309050a050114060616060f0b1315060309050a0b0415020406 66
    0x40074404440300c035890010000b0701188a8011201c00c03030a043d0149450201603210802c00307030700039001d000d0720b40b008010001c1c13803582c28001c00c1540c102c1e240001440d2004a868140c0c805001e4040c0420000100500100000c01d15010401d8030001e00e02082d00c0c8440c1610308000b000506803542d84805400301c40540c240c40003440c442458400e9071041c039401c02d501c040060070a514022540700d514840303446000c2c01c1c802e401484400794645004604d00c10355140490031520050404d40d1100d4640b41040342c20711110300c1181c0c0008050b10b103078441a40da0840e1540380f00c0700410082c8101c031019850303901c4032913a400c8500500c1e001410348800d4031091a0450090003891960030b401c0c040500000c406140c42e82c29a6040305000305a109100c0310303036640000600300341f00240e21540e9074040110f5142c07144000c0004401126200090325880c007500412001901e034806c0e400c00d07007000d40c0100007a40100ba01c000140d03202100d1140d43c1c076903203815002c101011014104980c0301040000c1d1140d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 842543543 1250 842542293 842542297
    0x20f1801090f060e0708070c0b1503070e091002070f02060a0801030506010503010c210e070605071e0201021207030e0405040606150e0f011d030618070801090308060d080717 76
    0x76200e2030100840c0d0042e42c00740341503c51070700c200c002145222002400160080c80c50551041c614a887c580c030300180e42d14100440c10596103034104042500040140307081c1005480058050803203a90181d01d0000c0d60fa5503295001c90510a40c541c0118034101042907100c40081500e42c000c1c44162501005000141501d00134801600d2500c03441000241c503003410f201c0e00008044940c3c860380555244807405107540c4d00801340840c03841d03030f070001164000303014001c40c409000c6650741c080d510705403400d16541c00e80c82c0b040d00c1c1c0c0102c104564420b0050703800103900004003c000601c10f48842c4282001d0300d900504e1040950804d08100c00c2004000450f8400070580302c502d0480b940f9980b00712002c85224030343d5174601d60000040303020090607602a54003415801219400f8060306801c04011a0400741d0583e1a0101e81c100034041c80309140c0240103074009030a0940081080c00c40546005200700d0018002d07600447c182680d000621001c402100c4819800c842401558030010250404035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 842544793 1250 842543543 842543549
    0x81510020a1a0610030c091403101406030f1615090e040503040609060807140d20030a20030408090406091e20040b0d090b01150e04050f13020f1801 65
    0x203586980c0382050a58061b205400c0304013416500c0ca0315103030030f041200007403441074031180e60300d88504d2600c10a50411405204800e402d40d002d844880e0401d502454030305043e1400041c07258200012202005140000d00c03400c940790300c0ba056844070581c0805680007142ca0b0403004441000300c1c10001070010000040080700e00581c1c5400e019507484004692000050364400c00140c2c2d1203400030042a44c11003e04a42c108100c000960001c10200440410071620700885001d1b801008020800307070300f8403510542d44c000c0d6144100141140103000d81c64800140020083d510101d00000507407195032045001c3d01c1c10031000c2064403040f4070b0102040040020540e0705604240508406040c2c0c25440e010a28140d04014242824110300201740e40000c04c50b0302e030107642d070302d14400410030703500c51203000300020829440180c000b0380000704044d001c6509a800307582090180421000c1070080070b9400b004001c08024121500e1001039416500d154100d9072226510710440001c0d910604200c2c12 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 842546043 1250 842544793 842544799
    0x20901030f02010206010f0b1b07050a1814040b1303300f020c03270a0b0304052b0806011206080d020c03010b01050306010c1106160b07081510020a1a06 67
    0x1ba80d83c0c502d00c0300c440f642d90007200a00c030414810080c29a034200e200042800001d401d49a0141c0c4a4001c2050340a00da130040b40d00a0f94900c10080348285841426540c1059515410752031500792914400c01c0c4001d0044400501d11418070400d1511425240c078420316003405040d07021420b9070f034603041202801c004190302c6140007000c1040e10f01c0c1340300311115814400301460030001013408041c0c0c01c0f0500411020200590955207543c2d58034200500701900403030f906640c8030b082c14205549411440c0c0b602c000c4403580702c0104441d01d01d02001001310410070b0f161040e030990359240101d407804c1c0380701c40e9050b010f4185040812241c0380032810303880c80352907a4202c0305800855803c041c26030312800c541d60f01140701040441c41d035501c02c0000801041c0904001701d5103152403008690305501065070030326010043c07042e02c010000203080407500b0075030b01e252003280340c20100401c80410020038030940c03007003125800d0700031991700a011000728250426100982c0161614a04101c000f003140c42c0c0344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 842547293 1250 842546043 842546053
    0x50717090109020916050f070305040305150c0712030209041109030d0e0a0608060604080a03090f1d0a020d0b030703060b0f030a050d0e0a0503060a0906110405011407030c020901030f020102 83
    0x640e00c2052065444083c0c00500c030366007644030074110b44907030950344452404019003001814035103a2407200400c4101d01c01d949076a5110300c2c50030000e082640510f140c07030440c4c0041d03040c000303a48200002d40b602a50000d040c0c3e401c002c2e1405055000348100b241903600300741071412aa1740c10304082e01810f80c40d0810307420342c1c243e101040c0301140d94842101a5907409480d10400f441124810324006d80e000c1c0001c0c10306840c00380c443d09901d10f01302111104070300140b0072030403d01480007200b260900a03c1c0003d9031440c41c040b44084150300c40c01c002c14680b484c4e0f6011500c1007050015400c003159a900240580e50740c01d4407420004098803008400902882c1c1000c0b55420b20b0800140c58415603821002420a0201d007040072a100101000b8481c0d02ca001040046440d5805000041c000c44010000064032941854944241d0f440e000c40b83c0030b50503040c401040320f41d0304a516401940802052203030341e1400341c43e040d40d2080920001075041441e660000c410001c2ca608a220f000e4004d8080724 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 842548543 1250 842547293 842547301
    0x140d090b16030204030b0c07061d0622030c1202010f0e0c03010e0d0203190903080d021c1a2103040f06020f0c0f1002072d170c1e0301050717 62
    0x641a4421817000038403072200c1000062075000900054039403113104a40100d4103508846041c0f5a80c025007003a081c1e1340e0421f000340300f42c4000081542c0c0d00c4a10100e0300780d1260240382c81c050008803120b04060651000d060104174070740d100394041d10814017000d608224425009110595605000e10014000d41c41c1004402c044840041c000c10003015541c01145880341c209907c06480303204071889028480841c4021002850a1000e01a040300050006856030540d20b0641d91182c0740d0741550f81c13018a0314029041800100c061076000303400c141c50f8a0400000c00c4c2000d0000d10300d400c041110382c000800c0202d0019030b5209030100716550b0740d08882c080000e006c0055203d030000f40d1499840300f89003901d03038403505003400d803100e2050281c019202e2155031441e280c0500b600000fa079a56480303983c5400481782e0206806480502900500c0b0580e081001000554540d51152020701c60080140d5105880c01c03d03510b074003c4000050300a000e10704003c000502510324002e07099180326aa0f40c005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 842549793 1250 842548543 842548547
    0x4090e01050108151902120f22230c0d0807030f03052a070209010f15110d05030c0409060306050f131a060102010e060103080301050901080706050a140d090b16 70
    0xc02d07a04410303a00000c03516202d0380710800e1901e8160304404ca0175602806001c2143e034403120740f10311482a1488800b018901101e081001c09900b140d43c0d540d0001d803002200204210b44a420301c401869417034023020800f04908507181121502109910a202c0c040c00000c01c05008040c000b100e21940301d8031806425a1420b4041d9442120240610070030801c051350400c0781c0614403126250744c0c40c0180d00d00250b68001c110300380000d8000700c851f00ca80c00c41c200030040e803803400281491a1803400745a40c43c0c50412968031010030040c0d01c0200310340480860301034007900003140d00401e800c4204020880d070ba4a8180c0c098001180c1e02c5a49014090000b40555804400780d20101d40c08041e141040a071042d20003a04400034040c41d046650302c54a11410340c0d802c001450195024122558496250008000c0f041d10141c01044079a00211402c00100c0e42100650b00c001c000e50610914042d4042c00d499900d0198180b9940c01505002c0101d090101d101d03904c1d030045e009410501840c1d1091941 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 842551043 1250 842549793 842549803
    0x308010e0933090708060105190e042307090c0e03211b010608010f0b01090b09061216030b0616080c0c04090803090d03150b030405070b04090e01050108 67
    0x180a050342100203841d240c2c0d00c05041d42c4080401030902012040040034807503040e220103c031070a80c0360f448204c0074000c0070002c01c0198010034040305c0345080c0391001d0300449000500b921500103004500c1000c50204442c40b1158030101400c40410064000b0199000d0f580350340b144925504145080340100d02903209000c080c0440300080c00405034820513440b00d0115200707500940702403a0040c00041201008a9044007407076400c0700000c90803505003900e203421900c0c03215070400d0940c580782c0c06034926600300f18120100e0b414407800036268601d04001c10000d00c128030103503505071061420800000079506000c483c2d0800c1d55401c01401d4004018861103129145a01503c40000b0582900103050030740140241d01105c010340707040e91a5031000c607042e140c0d644001c0b11140c1c4c000c410450aa40104440c1a6804180c03405001c460640030840403145414050100c40000000024040c440d0401c1031034003c00304d0038002070782e41d940c030320900000f40400e0491084035401c0c030380001420080011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 842552293 1250 842551043 842551051
    0x50a0f080106050a08060a0f090603171602060a0201090f030f080f10120606030c1d0c0a090e040204092a090e0c040903090b040f0f150c03180816030308010e 69
    0xc0f29403070840c110070f09580311640108425441100004003003010a482c1c10360304020000c800c40072030311508601d0081c0800c65038a08034800c1510501c06801100d64150480d001113406580007655181092402c9000d0b003081c080150450030455040410107900103100d40354080e50742e490307124588810071400c84114065a092803108841c180a10001e105041030000403481040e000030f105a8035036034009013a440303070300001d031314041c044d607150a6440c1098140e50100358803030094038000079500043c1c0321b60313454000c515040518500003011500d0f0381c2e02186da02a0418259110030b00e1101d4145c09000d14526003403581009000001642c040c5406024081c1d00b03904c0180249610080030300005040b602c4c0c05038104400c0c00c1c0b000a1040b00e00c00100054881488000442e505211300151031082e654820b000c1c2140369a0440b815541c8251485099945483d00d071a0700d520b0320381e0600c51002daa4120503a44d000300072620418028800c46001224481e84819020b80e0740c0d44c2100c1440f10040f1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 842553543 1250 842552293 842552297
    0xf1e2b0c0c050706180f0b030105040c09030c0e0a09150608010e0c0d0206070f0c080d090501050a0512040224031909020a0603020c01060f082506050403080c07080d050a0f080106 78
    0x1c3d809100150165042c0d0b40f100d009900300c4103095a60b41c1e003498113900190712100306920f00000600c00e131308040c0070741d8a0014460034911111482d59039060840a50f5100701d0594000c07601c0402d4808607560880303481c15402119004101c031181900100500b100e111300c155030f6280c100d03018109180131414040c4908001d001d030700c0b041c41035001d2250560042504131281c08002d104840000d104003d594050040303007000345280d0481500103480700a491b04070a0611500b03004000125a10000701c550b60800c270240b0407a152903d02c08100051078071000100c071038140e0390882c82502400000380d4440c241811500c2e00e0b42060310700300811510038050103904220b82c04018806c15000390014411441c40a00020f48036a54080c01901500150001600764105030480740740300c0000c08100d001c0d51500c54070015001e2501b503002d0064400c80c0b1000741045004540c11880180a00068004040035019504081991003008201c1d074807038203245003c10385200119040c43e01c2084024140c030002e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 842554793 1250 842553543 842553553
    0x1e0d030c112e060807210b0c0c0c0a080a150b090105151603081815070309031b0303062306070807141006090b03030f1e2b0c0c05 57
    0x105030103401c500203480366010002c0e80c0c8005445109458450000281031136005001040c0c2004010313a221107610900805440604070300001103005011000e82005070810495075600c1c02e0310026003403141103540320368001958900040d000c540070400e02030b220701c565001c910804c280c80000003202d2003202d020390042c140600600150801d6000307020000351a0001c6ca0914456544003200351210b010301b180003078181c0c0240103072440c401929506c0c010703600c2d025000011504c50704101121000348840c0c00c00d912060003c2c10705002d040103511283c04118001511200344c00e001c2c01600b01e5200c4c1065811020b1540c00d040e03032000040003c0c03d0401000d040c98015180c4130a0302a0304184802c6e45e188a003c0c1d100e401d450360030010055020282070740031500d81d00e0004c1800803204908401402900304219800c445a01041220180d014020a803855042c02d0b0081c2e52050091074007201d1380900b110900040d428640c0e40412103140c0f1408240140c500854045805003103000000300382d13030300c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 842556043 1250 842554793 842554813
    0x321020102040b04150c050f030702011d150906070803091c080106020604020f0f100f0906030b0108060d06060f030602121302060315061c060311061c0e1e0d030c11 72
    0x105c2d145020719050b03881c2580030351210b40c94107401d200b507404c3c42043d01d60001420004650b0070100001d440340301c210344944840c6865001c182c440005060a500c120000202440d0b0344d070303d5005a605054114060a07140c1c070301440040d9840080494007242489505003095900707100f5030b00b0314162462a40a44003a03100d584c24480301310600d400d03842d070051107800074032300030340b41c219003441c201c42242d40341d44d48601c0040019010402e9608034104060403c12420a16600540b025400c64002e8030700c07600400c61824000001c201c0c0350814281e108060400006011082e0050840010380320182040d0352108020b20440483c5050002c0d0081c40c140001350315009800d061801540000d003d09151189010503500400349030b00800080c6595080148248401fa500494680906561281c50040c8900e2030f00c00c0343c074a00181c1900141c940020b048014030074400c10040318203100d0500d00e07490401541607210000c4802440010b450440d00841c06441401c1703040011605502030451001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 842557293 1250 842556043 842556059
    0x27030c020f0d05100504020a05060307030212010e090a020d05160314060f0f010302011b05030a030603051b150c010e160e100f050111070e0406061a0a02340321020102040b04 76
    0x300500623a40482007400024081c3c8824006600c02c1c08603580042c0d03520303008a586c40e6030300c3c4c060b0080c65000c0310b18001c1004101c800200c8610301601164500090340305840c2652404454503440241682c1c0c0c104000100300315480d080500c6c8290341c0940304603980c2d203080c01c090940201e403c2a46600c1540041001d54003034540d29690080420082c01f174140180c0b5000d1842d44445100000203070307107020070014400c062209400b000d90249806d07080800b8200000c4008010080103054140006903142080c802540080402d200300c0c400e49001035031321115a6044072551240c0300703041c0000c0d0b0005966000200d40d0000383e0300ea9860714400e2908120045940110720340b000c403100d00c0b5000004c196440b0319420244154452240402c0704d90901290a042d644680300c2c003815410103000115a0540219003005c81c41e0f0003900354481c43c40120300c0c4e0b078444c500020804013010848680401440b41e5a900e4021100d04240c01080e0049142801c034200d200354880d4a100c60001e01061040103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 842558543 1250 842557293 842557301
    0x3070206190e1213061706061b070305060f090c220204050a080d0e01080c03061905040c0c0c0b040f0314030c0d020d1d100327030c020f0d0510 63
    0x4440c5030800541070168030031107407070140070f9500388015100c0800c5160488030845001405002c1a1512040c0303540c12207900340c403e0034003401281c03082c0400701e03140c180c0c908046005030003d030041c42100c684560b64201280ca410095902080300304100000840319180003503154800c2d60080c0100c2203c2c0f00c400c2540304155002301002001c2502004000f80a55440d070003c0c01070654040600000c9041c008013030600114101d55605000a00c0100184c09500354180eaa11000540c2c12003180554000d072024411284c0d0081d5500529202208840c0c5621080404025220300501100c0c41d803160800349090195104400103000711060a00024210140b006050301d86001260b003810790241c040d07400d100b00d00020031300503071015202200c04d961118484d1020850300e030b000900c000d004000308041d0004401103405040e1170f01240011a84401944418104004030140301070b140303441d00404000640200ba441002e180300e6250003840c11a80360f10300305901000400300000003a04510240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 842559793 1250 842558543 842558581
    0x60905010f090308090d1718011e0b030c0405060d0609051507110c0d0210032310061205070c030f090503070306020c1c0504090b040914061b03070206 66
    0x6548480c1d15001c16440360003200c0d0818480c3e20740c00310342e1620f10081440c181d2015900000c06c039400760901980d401d0402216000f05503010608540807490b2100da0140c0000d60b03040f541d003031400840c40460149541301c3ca04032401241034490b002a017004000a5540c02d485a540c040004a030002c000385981d40001d074517038414410b9403041c00036840c5140007070348101d65610100b0002403090a46885c14000e80c41c0b40241221080c00984030b68001c682d034030021001200c10b01d0340d9480f031000250041c100000142c003520039100d000b46059000c1501000341e521442d0007265a100075186156054001d00c1e124080c5a42c602d1100d684036101104c1200b511121881400000307500030409071428800716000c1c5010b810003603941d518143c122032a001414017403070328070700c82d200b01c0080142d800b000b00c3e8204c400405020031005080c000240003030842100c01041680c0c6040c110500f4400420741c24411500100d038000048444a0000a188011210040141c01242c0040d046207024010f100d08 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 842561043 1250 842559793 842559803
    0x105030a0f09200109060c0b18010b030d1d0a12060c11010f0504032a0b070201020c0f1525140c010903030e07050301150909030c0512091f020a0609 65
    0x44040d039161488800901c03581210080a070910014a40d45c02c401c00d20014500c034030f4031669000003034540d0041010b0250000740e06000c04000418204001d402007807000c1c00007800d0796018002c50f100603011800c054560000d003203211503a0015803403e02c107800c0488140c003d40005040c6070f0750b60301c001094a1141c00003880040c52508a150f01d0900c50143c9214841000140906080c10040c1c584110071001c403280484240014600700c80c01a10300300303010360203045082113884010080c2e000e4040c0c901c0c841201d03c100440c5941c09640019000c148003c14603c200c5161150303190781c40c00014841e8246450641c041300d010b0740310320807040900070180400f0503c0c10800042d480d03600356901203070241d000036211442d501402c202808101c0007030504800070403510061114400101089100e03040140d0780d00e460341000d150240d8110000b00368003009a40250784505964000d540240700300d07600415021a10714a14002070f4050300b10a241a0010107401c5800c1d84da51002c5d1480d030700d007140c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 842562293 1250 842561043 842561051
    0x4050609061b150405011a0609101b03051903092312031f050f1011120a091a160219030210050a020f010219050a11121909050105030a0f 60
    0x84400b00c140a0740c000101c0e60b65904040341480d00303140b030075038100d1102c110388246020108081680e0751411949034480030b6071048181c0e04c1c0442c05440c0d004520b0070b0150741c0c81c210a1045c0c00c044c0e015006003a03600303100d0f012903289625038200f1001c49944100050080b00c107100f1038184036144811070810b600070300c01220094280f900f6041241d802c10b40741d41c2500c1c4170380203090000031916030314403000e010244c0f0000c040c10780610000702c000140481260601c010035001001b04001401202c1c01003410700354942c0e503001141c8006000e403400340715000015108405130f4243c58110000c64800040c814041d00c0c0200140d001c1108500d0100103a5107000002800000180c5911114841d0040350b51203071902c0f4809440040c0c28003c0c4918502481e91040000551050544d044945444101d20704581c43c1d40300c0c140305440c0c1d4400582b59507201d20444c0b107414030000000e00207028458100d080114005500740d01521508158080d05010403014000500540c8040d40450780e689070401002c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 842563543 1250 842562293 842562337
    0x1030219050a030606140906090c0f0706020313020102070b0a02060a0c0519020309030c090906180f06010905150d1203021804060f06090e04050a020d142b050405060906 74
    0xb6040d204950080300c10300d80f5024100071080380b00b07200d05d8500205444412003854000005150200c000344180e0f04c1c014040b9980c0780143c441400d8400181c1d212200f15900d0074940090401c003240464200e0040c803540da804622040000140c60322150582c00421142e00c1c1d00178101d01501e543c1b09002e00f049414400703605100c0e0940691040100e40750003643d0343c6d031031001c1810b003132203143c50500f07000750358800502890050010368903038800070310110340f01c5003503406000d1410444c280d84500c00502c92140042244e040d0341e4042401740d020034070304031100b841d91420f100041c40e03400c078094500100c0c1202581900d00a0300102401210190707410744c42441200000c0c1114287e800c0200325041808041c0b00003034010b0b0384803002d092548800308641c1383c82d555550303490100c030400a0050310310341800f10801500060310001071400d04180c070f2818078064100e070b11501c444980c80c5290308030600882c044034061012101620405050689881e402c0c1041c031100b03034041c1c50403040c3c1d03e015030140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 842564793 1250 842563543 842563549
    0x3070807061e150b090105121b1201081005040b04020d020102070b0703030509060c0f0703120b0d0f120503010f030305030421020604060b0414011e0801020a05090103180b0103021905 80
    0xc490b00082c00c4200140700d2400c5918141c0701e1039960002c40080e202040404800c0c0e030051705a4a40c0741803000c06054641c4d0369400d04d140c150014000410b081c202044071503401c0a011143c0303058400c0007045414640c4801d03907800070341d80c0c16180908507101e0b010108000d41000d401808507d4010700448220702c2d903542c29140e03103601c045010f0b80080c0c3e5445c00e12500e80c0d800c1c8110b44d000410461254205001d00e0101481c0344183e44009052240603072040040640c10340000b081800b0041800e4080c14403810324448021011008541303103081d20700c41000c001c5c0240241c82c140e81140d41039209550443e42c0640315980302600c01e4401c1550104401900c032440120f00d5084116a4054055810203180800070384d141407500a2145007050103c000c04800e03002c85904584140340841c0301c03d40c114015034100c51050708001e01650002401411316a009001072101c900280d03800c11000c02e001905103900300000030001d000400000c0104094035022140480c3d2040800700101c12070380e64000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 842566043 1250 842564793 842564831
    0x90414030f0a11160e1308040603020903101401060c080702060307090302010f1706011d09040813120b15190e04150c1211091302180a080307080706 65
    0x6203007039940001540701e2002d03912420242c1080540d03001070203150005114843d0324011405490300c20442040002c20ba045e403401c0441d00180c004500c1c44c1c0d590740f9020001c0203580814100d47c040e20030201e204016142030701c0f4903000d0000700300515401c1c1e401d00000301c9292020368070540c0d9540c001c0c41a0009a0b44000086000304100c0e11554040da28510001d0012140000e07400c01380001c1c000300501103089480501d030301c10000d01c1e140c081508030b0b4000381c545980503448a80c0214000c41000200701c4e054000b05151080703040c40700c080a6941280640ea6064610b000303101101a034003103000c00511008200c0680720092411500fa403542c084229810302607484801950305c0903041c00309105800500400b0070703000c0c520600c00d081e11004003506800018456120700c0d56900c00c600d05040403d41a121007103402040b001e41c0da052544408017030b420902d0601c000c0c0488403052441c0349031084200044034a01001780d810180162540b0000d278109400643d9079a888003401c0c2c4a000c200e40c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 842567293 1250 842566043 842566057
    0x20c1302030402100f02060a0c170a0b1302070f020409020619020102030103030f051207120f1805100902032505060f0c0601050a061b0809040903050c0d05030408030609041403 77
    0x9001a103a14090041006404081c2c00d100103101c16260180d80460b030208100364803451a14000c40d000750416002c6802c0440100b10502c50254141071284400c4160000d9013540400c58030003001c00f10b02c01c074440480c440c2c00001442d0700c18440f4030b0401810700c1e80041c12013a0006103200e0824174503c40600c10420641e49000c0143d50000040c820190462401142c4460381d140081c14400c0a0304481d040c110003410100622001e07111110000c103250b04500001d400640040c0001800c00c9001c9031000321000040325180110b4184000301c9800e07108a809550700240144030100d424200c1e020310031005103280d000d8028081d40842ca03610f400d8000d04000c0c0e4071924107552010800341c1c0e030341444010b0308024071403000d6a10402c81117074071590031080b102091031211042c50030741c40c004846100e80c01010390014240100c0505040d00080545402e99505050320b07d901d08200d400c0315a0301c0308030340041c00c1c002d0a1010030303410b0a000d19560350081c07003114082030741412161458516005030b5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 842568543 1250 842567293 842567329
    0x10f0507060b0a1d040303051003020603040803130204020c0a140d0203031602070b0334050405010e030109060c09060f030b030712060f06031b0e0103050a020402070314070b1e04020f10020c 83
    0x40a1108261f490310406500459014900380e1440c21580010103a100c09013000d4a100404004602800754038030711400d086034020011580c810040d41e100380c48602060003038481d441c04990314040b0301400301c2e80d9004540141c1c042e501c3c5646d118451001c2c03c1e401510a0110b02c96840081000e114040085020b8041c007800c0070591414018100d981c40009000050004078410f1142076041d00034007610142c03002420310759002594140824010002d4002c080c0a6034184140d00c580c543e0403605003000d89205d07a6400000303412040b030a806a40d40c0e014010740641c4042c6003007082d01039a0b106e1a510a11440c4e02113105000000360030190761030b5410980fa0b0021234032200108800c2c08142000400c07500e250b03100b50398595210152510488500a030080d40c000900c4010584500d80703074661508640034031a1036902d10306111110b08000c0301c021225042c00c2c16005c400e1296002c40b80e2041c0e074001d24441640d00708a0610400c0c2d00030031451025842450f143c800e05955040c0021141d078081 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 842569793 1250 842568543 842568599
    0x6020114070c030804120c051b12030322030c08180307080f03300c09010e04050c0703031e020d0b0f0d080711010e0405091506010f0507060b0a 63
    0x511010320026a01420324801d000d042e05041000135001481c59074040d402c0302c034180c00307070031400800d446a00d0b08810003011070240c40e074458003500c1315403280304080c1c00558030a4030302d01900f0f5030f07166207100964001e4140c0004000c5051011403054076813155a2203441d0029030403041c0e40c0c0d0348a0641180d102404515641c0c8640078103030404108040041405c07400400c0c20101d844221074a0748030b10300e00c3c2020100680d04a00c4802160070021510700c01b40c8480b02c17101c7c0742aa000005a4100003043c500007410b039a00c1c0812850700d8050a03000303002c50000280313031000c0d40d0b800b60300902e12240700900d981000c9a0101042d540e61020303048041c100400850201c0d032510401124034628100746200d808910460070110f8100c1090f9200d107640441644842100000140d0303400e003090482a500908160401c0616203002c100c4179000068158010010345400c40195440314030010080c0c002181800501c2c081750703240d000380800d50300240095401a4462003131307500b0b03c000306109409807924 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 842571043 1250 842569793 842569811
    0x2003060903030c1602120a0515160905040209010c0506070c060e0303010b07080c031c06090b030d02060c090406120303050f010614090607050c04060e01180e061b0c0601060201 77
    0x1884255409100600514503600d041040c0040c0e40c01100c948021448030442c5820031911200c50502800d403070b074811a03000154a00d48155140541c0b84810701500700440464407a01d070000c80308040092903221698180e080809000081d000109800c0c10002c0d1a1a02e001182050241324000c4070345680782e05094aa0b418604107644002840007102c4c0e00030001000b604080b1020b0342c0c200390340010403030366070b405055540d4a10300442591541c0c648070101030807980e015070b034441c1c001c481c031400050002000300c404054540f10030022010168001c140003503611001c5000500340c070f20b0000c0000030f00d19102c0e609182d1030b80c8036400c1240030a0380c130410301c14804280c2140328010629840e0102c41e40c400380d20f904000780121203540e402290040b0300101004024031070260180409001006041c0e40e40d0134080c3c440700284a11054002c054030702c1203041500703014100303040d0356500040c0720a031201711140c0d0541e01c490742c1c641c1c8914070901c0503154080c028000c490003400c95900220328100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 842572293 1250 842571043 842571049
    0xb0f28020c0d0f0b190c0513060e090105011b06050a020c1e0d050f041502100b010201020a0816020c03030703170f06131e06180501050d05060a05040201050720 70
    0x1501010032403081050400050010f40c40300f81e08121240e005004c07085903280c1d6900d0351284c6007000c060440d054207040c40c604080d50b110b4042d04100d8200280102c5250f541d4600b41d40030165116030941201860b0300621455000b0001c00304040c4c1d250640c14001c4815456010440b00140c4170307074201075000a2007607a925000c0044882c2d140d0301c0c0720141c0c4017441d00f1080907030b540c04a846410510a0104400005201000944004103807018000e503000c07800f000001d464400d030042c910b05080c540601450035510503c02d440302c0c82e1850301c2d08003c070380b95000300c01d000c02040c0440788114410349403842881d8406101620b070003807003500c42580740030035002d0000da24035000b441007540710215010801150b4400c00070b54507001564000244c80042c0500d91001c40341004145d050751424002d0006a188040200708417551044038104000d9803914108400041c00090203010f95101d68082002c42c209030348003d4008e80b0506119260803c2503039160a00e05141e41d5030021200e0b0490110040e003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 842573543 1250 842572293 842572303
    0x603150617030703080702160605190201020306031e010f0204180e0111030a0c14040605180d0305091c0f14010e0d02031801050405040608010b15090a0b0f2802 70
    0x31900004580e40030001120250b5a0f00030386401504100c8840c0100301071600030b111040e05124100f07045403e041e2500e1000c0d1003503200c91440384240f0103c5c40320203655441031080c0c234051100180684201c2101052100e105258010030780960356031b0305404409540184000c0004101407109952200e01401c5948111344404a400e034040c2d041c240c80c200b0f40315584d006c9940c0b1081050000500522304801203c0d403045405240005071000103011a1894010015011418500c041d406070b00b49040c0c1805800100c10320000c0100700300380060078803481c080e0801c40c0b24200030002e5032911145621080d13400002040180d030080c01d113800303001d100602030107200f1000c1c4084004054080440d0002942e91194040801c60b9040011500100e80e209d882210002d24004006100c0e043c0c84047c6280203040e01c403c601d21800800a4202030081441d054401d0302c07100624060701139160004114079517202e1500c1101070f210402c02c0c1221032049681c102d118070181e0710400a6038280350707000b81c900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 842574793 1250 842573543 842573549
    0x30106021e0a0f0209130537260d0f020a0f02010c090b0f04050915010813030c081806070606030201021e0601050f0418110307170d08150406031506 65
    0xc1c0c001c0d220340c02c042882c000080c1021a41034846400544d903c101c070f140090081d210003091400b52003200031320040303401c070b0304003a2150450a0320f003011001c0740308c030031700581d02103004003240c41e011504411884000c00c1c6c01c00c08050001072502e80981c2d0f0300103034216090041076004281c1d01051000042d82c0c0b003802011034940d10700003000440503c2d500504000010322030f00c1246c03c0b002035480d8900d040c0704207680003098050603020540c2007105a0002c0c01174011110703070001d41050000b0303072803580c0b004582c0304c20364264407804203d240a4481084661000000e1880d65888003806001501c2320350003001101d00a5000041c071034190300c0024104218400c000c000c8403484860a0000744004c0b0f4981c2c1141d8086656004103403020000c680507040c1c0415090b07140d440500c0c20410700100204c00015150101e0030b4a210707a480e0426110358451007201c04005620116003000ca160062903a00d400c0040411070440c0b400c1e0b0000014165880b40d00b00312000c0902c24608403003050f180c0288409 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 842576043 1250 842574793 842574853
    0xf0e0f16090b1c0c08010c03020316050702090403030506150307170619210c0f0611190609050a0c0f0905160c08180303071101020616091206060b03010602 68
    0x1c401c58400083c0c00e052081c4144200b0b24400c2204200300188001e0300c400624003940203210001c2c0b6104003030001c0d00111550b404280c410303118070844038410411204003950051442007281c0300d44d00d0803002083d00030021904110701d841c0240c1c010011802840c441d12907a628666907003055200348040080203401180100c502000518035001b8406160080c3c69a40f00e00d4013031480c4400203005030000100002d40b60032080134002c19503100e020016419200c507a11a004500e0000484e15690711b180c003c0500f10a110150440c00100150404500c080c000c0007201c0c001400703a00c51189a1170144d103c0a08082c0e0000e08006070110360003007030f6124040205891440f0b44500c9e02070164000c8010051a0220000e07440b40c140207000c03006005140e0103411662120f01c280741850001441c508494094450040060302190301700d00942441030203646c41d000c0a0f494084140e07580b883c001c100301c450ba0380354900850107100c640701560080c501503000f0001480000050384039400c07201000380f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 842577293 1250 842576043 842576051
    0x91201060b03070507061e0b09010e04150509030d0e0607030c020f031222150f020903070e0601050d2906030c0f0a03020415230c0c040f0e0f1609 64
    0x4800c0000300192039120f01c0c0d41c00e00c0ea560300b5991803c4002044c80c00201c1094940d0740104c0100d04000351300214140c8000e4558400c641d80300c441c844c0c403803942143d000b0251a0944100035420300d10780c10150304400b40d4170449090071941104c42099400c03c41e1607107ea80d210354200007030145d2501886000c0725160014143c00800c1c1140c45d512445408090142c407000400410320901c3c2c65044503c0b510114180041003200034941681e00070101240300c521181050381600c402c1301d00c2d20865540200c024010400d140c54001e6507904103200412481c140714050210890310f68080c0140003410301c007258100000c0841a90752494030040e03d0113a80a040244200800051694202d448420070b1403d0a030b00ca002600007100684a00e41003034101891700080c01070301d250000804041d5200354018100f048149800c80740c2036000b540307a40e4100b40e1002a0f050203505099001d0348565281c840d01080740040e0007505451318516000b1210035500902c00584900002e40308400a0210048140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 842578543 1250 842577293 842577299
    0x180605040b0121350301030c230405040302011e050402031203071b15090614181203061201060609080613030e01120f15050a140105040b210a0209120106 67
    0x12400c64102e0000419000c5190900c13400300752403842c0140c0c80800c42c034a0084141101a02c554180c00c04c0c0b0040302d0070030800d40d0224000d02e00c6d04d00120b07141961200d142058088008010207010050410323010340d541d44158202451116103c42809492503d0100e0b85040510515140c8a074800d06849520f40600034480c1d06944143d001c00d120121548003140e400f4507080c0000d0008004507480c12079032411564400304420f5400032094040c2d40741c4c03144480d41d076501458038860480040c0c0d1520b50083d0f10018181a030602c045d41d00144080c241e030209440307540c082401c540701c81c2c02c400d0104500d014200a91101000000ea220750714020485541c0380503540a007802404030b00300c074144000003001c581c84001d1580003140c0062490760130b116898075034140c90a030320030390701034980a000491808929424011410402c02c0d01c180d4800349840d00d800ea82c00860f4106070400320030040e130075440601c3c8040f1888040c0c0070f8154954010703a103604980800c0744c4a02d01c40c60848442c1d041450030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 842579793 1250 842578543 842578589
    0x60409020f0904031b0f031b08030c0f130b1e0405130e01020702040903090501141c050702070e1f090b09011a04050306011403010e2e180605040b01 65
    0x424014100b5140008540c4941c541a1500c800203c0d5801c954200101640240803403000030140c00d6010740c640040500c01d03010001c0103c1c180400140c150714042000c03400c054203000062140c860700e40502400c2030b0b108104401c0300b14490780210413000f400304000c402410002220341c036401001ca4105d14051400700402d00500e00342002203582d40c0c0c0c80c0308411a0902c290112452030303900400c100405109494042c00780e00003400703028000398004252400b1101345000720741c00d90194032419901080d0940e41311024240040c02c180031400f501800207540540c0c09042c1d03008251104012415010f0300882582c4c1c440320345d02410807182044200503603900e0304102207055510517170401c03001492204c1ca150326449503611564041c4142c000005682c2c00c400d00e9040c10100403030007030002d5034102401c07913074902d0503c0705002d040c02030130000b100c182050001003140d0780756100003007001d40d208101c80c500c4541c16401940c1460f1108204010041d031841c805026061051408001801442c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 842581043 1250 842579793 842579809
    0x51905100c090902070b01030510090302031e0405090721020702060913020c0f1f050105010906050a03110d020a030b060c070504110c01060303120c0e01080601030c0e03030c1506040902 81
    0x100341100340e88900480e070241c4a41c4080780030700b41e0075401390350713503002c51a002c203a1100900c0103860b00d0042e281c0d105500a2030380107070310700c10303415038015402d24055285407851040300c13210001c08620200030028240e1101c0c102248560044d88807541c00d19a001030840403c1070403410b40b100c40344100600c400680e503070000d0b506911010394a29003032641c40d0207144024030400170a010580704d1030b052004208800038040540100110010021701840b68201c2d040d242c084c06180d02041e070740001401407a100d40042d0103c085180360224400b01d012a1100c200e52260709960201a000a03d000240760035006421007a41c003600e0701c614220390700c1880d944800382c0307018540c031580d29070340c2e903000181c550303801da481c484564002040900d640e40b030b001e02442c00c2c2c00021441e0354140000741c081e00d806101d20f800f4184040e110002c540e82c558004400038a0b0a000090900c9419564401662420409000400320312802490002d8a042c540c0b54100401010103102d6803c1c260050016200c0640b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 842582293 1250 842581043 842581063
    0x605010e0a06120b041802030106050a03081207030b091e180d0c140102030705091807050301052e050d150f03300804060c050c0c0f0a21051905 63
    0x240000c03031140d410340010080e100304c80381540c1c4035007456525095100c2400845c54030310301c00c41c020042c255964082c00b00d060820310002d07002d000e043c002911090385503003486d94061f9152600044625043c0006009050f055880361218198280300740074040703284542681011700340d0901c1901004001d405959400034040090400c07108158002c101b20050458040420080000355183d250001c40206a5003000120341c1c41030001e5480ca1034908090000d1038043c6941d41d03241495030303003010f0503c8040c100e0f0100c1a207042c600000d4000e0f9a12519a030b092407040241c0e1002c1d075410b407500382d100903605079440c2220420150807040005070f80025185046950041c8204011140c001c0381044280e446100000c8510b1100f881003081d651005005105910903101080301d00f2625004407500c1c000c2481d41d00060384000c0e68003859262405540c4124400140480c034a00d407500c00b06800001c2d10304c2034a1800039407107010f0041050038400c01203000803141000c040c01c404c03501c5040e0340c1c0b04d6000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 842583543 1250 842582293 842582297
    0x25050c130239070e0601020111070f0b15030a1a0a021314030307080309010e0106121509081e090f090f0103080d0f02040602340b0c0a1a0a0605010e0a06 67
    0x762480c5071051a100c2d102007281020800c0c0c0e81c0091340c03125a14407030803044400600552800b01c0340301405103a802554204c1d600b00941e41d60040d0299103204901d20064114800000900c0258080360b030104003010400e4443c0408106c035244200d6030000c081805401c1c418020300500c141020004c1c0284024101c942c0f50280d07018004900010a065119801d070241850b10000100701c800380741500459004441c100081001d159101d00102058010502c01010240c81144102d170303d6003147c1024040d607010301350440c64200035101d9400c3c1e40503030100800d000e41c40400c0c0549186030050a1b910105000c0d0358501c4a4500103032100410001404010040d00010031409040a0903911450750b041c00b00c0c00841d44c6c0c039210400a503883c5ca04a520020b010300001e002503601c44614205001404c3d41d502c48020380e400c0008407003d1f45c0104400c0707007044c480d2180f4030010070078660f00c40512170b4103241c2c1d4054a00f480740c6c19109072a041c5d001a0b0601201c4030003006103841c1c400c0108103c507514 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 842584793 1250 842583543 842583607
    0x6032108090c060304060f0204030b040507050109060f05090112020a0c020f04060e070c03020a0204050708010816050307050d03030221160809150a1b110d080103020d020625050c1302 80
    0xd181c06e60003401e1203203600c4001c510224011080025810340356010754003030400c540940340c2e110011103104446000710400a601304141d10110b600030006090503005c1410005c5e241c00d44000c1000481e0411003045000944050001c000e6003000703829003c010313800f5541485101c3c01c000050341c03990000f5144504000c0841c012005051080c4031461074158010b000340500c1c2420040101641400c0c040c0c6c0546000e00d184498261604914003400c40314060701400e07a2031710b071000308410510020816000d05400300703d102403180404160f4a001020500c0114141c00c0a5454100104041118000f400441802c0c8828440006081c0e091442c46036000c0036603a940c41840c00161154441084080c0d240e2a030f140c1e00b00380c00c50780c1980c071281e10608580a0b10703044042201c07440e41c00c0c403000e504072090012410160802304014049160003800f070381c01c607c92210072408144200e0310140d40c9070f0040c0362040d0041ca4584e01c2050406541c21701075040818458807550034200d19188481c84040d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 842586043 1250 842584793 842584801
    0x323091608010b1c140304120210050c120d060306050109061703070809040f0e0d02010c0806030705010e10020c120a0611040302092a0c010e0607211e06032108090c0603 74
    0x4810000c2d8600b080d88011b59848640d80d4a04241d141d034200e07000ca12442e106185da5605500c11400c3c2d4040b001420000c0400e424090400c186c69488803808869080d203841010020501d9400b03441d008280c503d000154841c0f41130354400280c61907100d0160a074208200f5040130810712425113001c101e00b1a13000580c03080243d404001000301080303544450250705004000300e0380640c048040d4440f00e80300c14181380e41e14000c064448800380565800304212568560542c1044010700307621004500480720301301c004000103802c01c0090b0754004481d9100364000000c010460250008041c060355603681014156030024101141c010b2032903031110407a981214018100305210100d06409403540e0350349645040b1418007801d20142c03c80301501c00c1d04042401584502030000781c26540402286280c17a607031800c80003401580700051205204400b407054190040d2007820000c601c20584d252405040142048904044400c42400d0086d02c0c81000b042309000305a55910b0901151001d5590303403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 842587293 1250 842586043 842586053
    0x3171006021c03060f1511070f090515030703121e08060f010324050405010e07020a080706111201030b0a0605060912120c070e010b09100323091608010b1c 68
    0x6280c0c00b40b082c101c517224000403030b5800321088000c0c000340d582d115002c40d04102c803140d41d00e8481d8490700ca1043d5481408106010b4158000b541290320280700c2d541101307202c4002494910190070958120441029a111141d0001000a8070450b2001071340c1e030788440080c014004480090109005080c02d04441280340e100307500c08102c10340608620385620090300c9030340c0d0500030140916406245480000b09140400c4050a44501150360050803840807aa50344031203a04000d000f200d00c0341d21000040a401c03c1c1d4005449011082400c0e545598074505142c5195400a4500000103182403414445621554125528200251a0708003811030032002c40d890904009031090490102080304e842e10000400d01c00121070040c800700800341d807110194102c9120b004000c5610001c501c0003200403078041c0d0040d8042c07980102c4540c0503901280740c42406034404403000410b40c2c10000541030640c4090102d640a0007000d0002c1018295000202c0c070701c020f070407000341000c141585007402084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 842588543 1250 842587293 842587301
    0x919030c1202150708160201060302030d051615090303050112030e1012060305030703091d06190801050f0a0c0507020d1e2102060112051c021903171006021c03 70
    0x2401d4100030855440c00803030042448174261400d0145070a000022980984140070724010340341c000f8040c050303400c10700000756025400801036031710004c0c007000045c001c5807031701040c1d050503020103002040d40c010301c0ca070040864905070400c8219080014071140403980c0300754208009081035131189601c0b5070581090b13607100341d10b0301c03200344640c18040003008100000c00a084198820744441003116101c245140104445c07000d51240d4040000000340e0341d140000c0c0d0441d41c0440840c4200389580c0303d4614a09452007168010403610f243d00c1844034940461003200d080d401030307140c0707241000180d90014401c5440000007400c1000b820940b006848541101e0342080b980c01000209050b00e6682c4c1d180c40131213500720000142c0035181c00007c07100300341c41e00560300d2607114026040c200350700c0f0b01ba0034004055038030720011403140480525905000006015000340251501c2c1029490f03400c05030140040184074070011903a800742045006c0e0000307420b488104141c401c8481c030b9490301004500034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 842589793 1250 842588543 842588563
    0xb1204080d110c061e13081303060504020a0512191403070c090501050616140c150909061c0212030d02070605150409030e1905030f060919030c1202 65
    0x80d030b01e04010107164069007801090310f400e40d60103440081c1d4480c003503006402100c43e100040103283c00006460b5042d800c5100e181c00c1d00c00d17068a07060540380c80b10184650303415001240c1e030550740c00c184400d41c40c00140510040070110740d060100701d6003c0d0160b848602610344001c204004881100801c000c000d51490071031210401c59840c0e00450400c804d40009502c00c810003945000000704481c00e03c0012150b0420502a00d42080300b82961501c0500114860341c1110380280b0b820040599a444490310400d8050060075481d40384020402a03030410281034548200c04140d04600501111002500d490750100e8002141c2061484060f045220700003420080d00d01c005036240c104041c0d680064014003100e560b41c028070701040244000c4650009010380030542508031581607181c0850f01c000312141140d0b040b4891036030361000c03034a00f61240c1641469a00940d08001d02050100031000c80300303a01141d461505025a203001d0203030000d03044090f01d00008d0005104030710b03000308120020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 842591043 1250 842589793 842589817
    0x507020a0504090f03200601051e09010303031d0a0b010e040c1e0e090609100c020a02060d0f0c0504240c1505150a14240a03090b010b03010b120408 65
    0x3c00d2220703e0154000e1065040440100e456a1010317410388070400e110740c5881c2d9040c0010001030742440c0820070b4614103008161148080211304607020f442d0030b048140298801d8a011881c21551560b603100c1e61840d80f5040035590010f1401030110f560f201051b8110b4000c13810041407602d480c10440854010394000d012180204076440750030701040c41456086482d0130121818030380310380507100e8035007000303403060300540d44501d09444030000b00d03502208103e100703401220801c004075404540142c205042d40007159941e41085101050030307010701c140b81031282c070b0440d1070603050041c20201a000034268142c110504a02000942e000c0d01461580c01e4000052112a50701011032001410040350110500da0148040c503c1500303210b083c071015a21040a202c10580c072900c02d000042688465000c10390b5900100245445110001442000c4240e0740200d41d08200707042a01501c00c040c0d1018140e04410001000031003003800c142c50805110320341c0c66020fa12a814034a68a000c0d07501a103003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 842592293 1250 842591043 842591051
    0x90218031207050705060301180b0f120f0c0103061802031e0c0309070b0a05121308040e0f061503040b0709090c0201020408190308041520030106021c0f0507020a0504 73
    0x25101241e40500307403640c810000c0782c0d4603544800a11040f400f080c03080800d08501e0a040c145140300d0350b048900d1140f005841c0d803009032442000641c0500205209000542102b0b08800c1d21500512040d012803d00f82400e01600b4a481821940080003010b008800c1781e0200114200d0150221288101b0103540c400044e64101200c02a41c03551050700c610000c0c0c8906140080c0f100e482c03206581c4049910303113806040c440c0600e011814084000c101c5048020a402c507800050014805000a00070201a080003032828158040010340003904440c80384600707094031000618845c5c11258011f038080c4c0c0c010200e4a4000007a1986030f44c42c0c100110090605420034225030341540a0000c642c011012030b8000c4122060103000400b410a020380024020790010303021528030014800102c6047c600002c540300d81e1907150015010384505480c058400100420401d503040000550b41011481000040450050302910b04200110990140100072921b8029551100d0600005190103030080c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 842593543 1250 842592293 842592313
    0x90f070512100501120b0616060207020607060c1805032109280501110303040b0c071b140118060e12060108010906050f04050c012a0309091a090109021803 68
    0x403442c0203409002d0008402041030041c2140501071880c0e081c0703029040c40c0c07810111900b82149140c040a0503180560208140c1005842e180028001d09009003400182e03805031100090815007840070711031400041c402d090015075408103107074114100850785e00c080c00140f6103d0041c58021010015486008a04011006c00210424080113040d0030390b81201540c41d040155103091540c620b0004a13441413000900259000e8252500040444482810183c640d034501d02821115540f0001d015080c580810400443d206001c017195001d0900b01c42802880401004615161040300104800b09440c03440030344610040c14040b10704034040da0410343c0c444803014064000914101c8425180900180c202200702c0c000f54011030b4810003400c00c100d05a0011180b4465160008201800300d40c3c07910658000e45e0311100049200341c5824403090b15100500d000c5903050940384080c1003400d2114451541c40000d600c1c152400280c00507168007200c0ca11841c40040d66012503003500c5204040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 842594793 1250 842593543 842593561
    0x61d0f03031219200d1401090209090703092114070501060f08070501050a05070309050907020609010f06060c0807060603390b0730030f0b0f090f070512 67
    0x51288014804403400c00b80c810303101000321402255030003800c1408030803500c4c1103801503004166195480f0801709003140c8810603101114400c0c0d01c0b6003c0175500084001306810000a0542d00c890607007410080c50920f0389422007030003440c0c030580c1e440c0081c48034480507043c0520300305001e001801c50b1789510303041d5038a011b90080141c0d000709580302d03c00c2d00c000907640c0c400080181c103640060791004d08180400c07000b41d845800c0709004500780010220046055102d0b2038800d48101e445500900031410003110841c2110400e401c03494040b400c0a10a000494100b518140559844640cac40d55808060030104001d12f0325800040c900c1c0e980c4006103c48403548010104000c0010300004050b00840c5180a0841070900c14941140c005200940215802c1744c0680020802810110303045102e1800008265640e2000b03500840c0d607500c004140ca901070b20502c40403080603a00c02e20044036150004410100c02040745241a440a002400d014422001d440e802e0540c050704009a04288000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 842596043 1250 842594793 842594827
    0x140901020a0512211b180402070c26030f07050a050d1707020703030801092c25050d0b071701030b0105180712110909040c140a061d0f0303 61
    0x2d5001c0d41c421228040001140450050300582080e98500c40f0100807170080b040701e400c00c1c0c043c51300596581446031526220b81c001000c003a07100e907001001c124203100e40c00546521030802c0300f004440318483c0c0c50b030000c000400c9558807a003038511107480f00e001e0710f00310f0300d00014400004e01c130f40030b031250600e2050b4001c1d400c0c2c8040c0c1c10780c045020950791a15000c03a80c80d81184000390018600340010406c4030426880310142d500322039103e0880e10a6080314030140a030075172251900e070f40011282e4440080d50641e003195004071220043c04c0c140f4050004140e10360281003d001400c811020404681c040e5003041d984281100da010810341c0d480c182070306002824403820307000d008182d21501004080852591080b66152600034144528100d880000c240804c080c0b8100c202c100300d0300f003da40e01c081d8000d11451180d03009000c424148044c855005010304a0107001d01c0d1b0b0003906005558018041e0f2611014111052520041203400102501d84070b036850340c3c0601000907140d041c14076000c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 842597293 1250 842596043 842596057
    0x1314010207150c080f0c0a0c0215030f01050907030b0303121f0603020408060a06080d0c2901050a06030507020d0815180403030c1d041d0d020708010b090403140901020a0512 76
    0x140d044d1141d403803803c100c0242030201c804940300c0c0c03000c0200982c0c0a0040c60510045400030305011822a41900311091652007519401040f21000004000034581918103aa0261440c0741c00d00411040d8404030b942ca01034408094548100c1c00000384590200c034400c2d038a1340e5900003540700001d546000c040c000350300502501520780104030011390001024021082192182c10090071260880740084449a80d041011100c80c14001c1448032440c0c00c0b08816090b084202d890300100b540740c02e0400110030003030741c410310900d410142045034550700811b408202041c0c50508401d01e80c0c1e00024103886410420400342d1240207204e50071000760850403114840c1e44030b0b842c200881644103400f43c034942c0026850302100d640040040c9440c0c10150881c5072040d50125940220301e2a55031490b0616111a40500c0140d00c0301d038003040a4082402500d074203080903551080c05042030340f0014101d03000c41140082c0d442c8001624290b03a413080101d01089904402070707410356002030181203e29400b211b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 842598543 1250 842597293 842597297
    0x1806070f080c06070513061b0c0f0f090e070b0c0109023a02090a020f0705010c020f1005072003090307030305090a09020c1504031b060c171314010207150c 68
    0x3c40010182070280044440000505c500e40814a213058000c0740d10101c1d07a120725104014085030440001c0f1f0300d81d54400034040d0304004903001414451200484409c0343d210300140c5041030b0001c05600c030040f03225825a0000302489984040407e00b40d0302410007954000d401ca131083d850000500b10070040c2303004805502d11a900441400074404951800441d03000e5805480c4a02040702440154020030b02c0c00c044080e00c2d401c0003440d84a203800c690765901c444c00581c011107644015803200f40103813403804054460801c05d40c24881c000400384030703c040c821a040025004192480201001600c0640130002c046030701e441d450345401880c90308a410000e0003920610b10219448001e0b0090b949140380d404001d05204c1c44500c1609501c0c04042e100364107014940c0da0304c1c0f07550070340d007082640b07000d01800700440d0450401070005c06070966071542a0380d844801c1c0034405040424842c00741c01e1a08a00005d080c03a40d9042d4040c028404c000f00101004c55480c40d40c1c00c3c00340540c003c0e2090389030b00c3e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 842599793 1250 842598543 842598553
    0xf210b1e0307210f050a020111071d06040207060f0b040b010504080c040203060a050a06030912090803030a090503040b0a1d150f0c070e0a0209031b061806070f080c 72
    0x14001100380d9909903495541034000010510200602d412031202c0803a600840502d5103469031104c5050409004007520243c111040c41415541c2003000703440140c51141c02480301034600000c051815048001031142c400351000490b510fa91140c0540310300d96000031003040301c05540310381040102b0280709154091410200c2080b080d60148055400700c0e11988040d001c4035010408210080d40000c00e200c2e440324500c4004100c0d503d995202d100a40425100050481e15904000d40c0c41d0040c400910308009003008180031648022007940c1c3c020390618404940c88480e0326015040d801242c0107181590004110b03140c051784e204010450302e0504001c5040b000901e1810300109000592214414100420400c40d00d0668100200b400300ca460003510034050301d800041244840945280001d284c0100b0040a82d00e400d20000c5580403400d10704100d6841180080b9102d80520b85c41c551600000a807100d041e0b4607900200c2d0491a488070328051030888610306580940c00131300074072a10f4400c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 842601043 1250 842599793 842599819
    0x20127140105093004061205090a0c0302090402030c090915010905060d021201020d181109071d0a0e0916080a0302030409050a0f0f0606030e03090a05010f210b 70
    0x2061145038001c40d440f602078820120425000070b1001004105010300800700310701e504a802e900b01c0580060581c0c2e95030a0890710342d80d2107010655074050100c4505402c003488803000076804208502c100e0394142d0341155559117a000081c1004000300060303030041c0c003a008000c68400007040d0340c200f10101c003a0b4551141d80f04c0354120111082141c20035008944440844050f1602200c0503031034100500025151503180f0001f001039900c08035203800c58110070009201000a07100d103001c1c020400383c5001581d07242014008101006080510003103001101c1c541c5943d4030b5200c00403020300900c3c0103d505a0608145166072a40d401525001049000102285a40000c1810a03905801d98000d5082c242040d48280003004041d0080981d42e079200e440c181400102d004040241180e8240040d40030b1606002a040d5007515010010b10340040004810340c2d580d054444064070003e1800c642c1c078031740120054540e207039804400501c1000251080e8045512a0001401031206450316900418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 842602293 1250 842601043 842601083
    0x60108011d0a0c170304080f0606100305070909050604020d2309060106050301051905030105040f0309050103021c110906030a05041b0b0d1a0a03081207091203030b01020127 76
    0xd80b80082050754558000c10028007550821103010714003000792403400c0ea0f5006818581075000c01041581d810031400c02c582c5141c41c240344850035141c0e0400344464906040b00030280b492500031840701d1681d030004a502600c0f164161485034105002c1040544020300600401554510800700041901c400107092544046a8541205c0c0c0c0b54842d103045909190410800074049002c000d8103e0070a80c0008071aa0240195802a1b000d036084040c0b6170340c01c4c10020060034580d00203034149401000b01440d46202100704011040035628006584103040304030012034401ca40070346510800200501035450401d5010354000d5124540071900b42402d4400510032066620031802c8800c000e1083d402d040c1000c3c0c010000b00004da6408400410520001442200d010303003041e10945008507100c143c0c800f0300742036290414558201103017214944a910a004480c034a0010304040d2182281c00140c0d0003500302900c40c0c03000c02820306142085003101c22a814000b031098500d0804140c440c64046 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 842603543 1250 842602293 842602303
    0x909060604180903022a03071415070204090501110d062103050307020f0d17061c0201050c1609090501050a05150d0c03020612011a09010c0b18060108011d 68
    0x140c1d0880e01e0704218808002002d00030b00340d0b49801d805500440340400341440054960782003820030b0f40e11034240041250306041ca0300703089030000c1d2413034011002d4000303003607541030040d40828030840501a44c40d6101d2000c10050000340d00002d0141d801d0000e50740e02100418081d21035090844010000141d032405c09421002e480d1200981020b41428000003081c824001154004050b0044951481541000525103006440c03c08000b40544640c008440c158460560308130104980030641d20381f00c0203403c081e81074007802c020b041c880005250110b601041c00040d002c2c84540c0031003a0010b645c3d070074883c058080c401d01264194601000240904c140380300c1d003801040228400003140200c881480001e100f403d83c244e81c940504070000005130b0700d01c0010907200e9800c40d00200a5450310030b140c070010ba4441d0b0320408070300c4103005a14003640c0c0414881d0240d07400903918070f001d44401911491411034000700305001c0c01840c0000c9030480054000040c99401e68104a1100c1900c40a030364a503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 842604793 1250 842603543 842603549
    0x609020f0415090e0f1f2309041515090507030c0305090a0f061e0219020706080c0304030f030207080c0a0c06090e18120a260403020c010f230909060604 67
    0x413400740c0200305a080d15071091079104024a448419611612001841c0d945040e030100440504540214000407146001c2c803012040a8401d4036007818213540d01108000382e141c61400803540c0d81d42103030200b4600300d6803100a001242d410091800d0004008001d883c2048012001c241040080b03110ba1400080d01c00105402c0041340e0b03640561655100054201c1c000401101c0400314081240701c411480217040e94100e80200c081d0000203c00040d05140c0940d1204045c0b00100080080e40d03100310003201c1d40319a0604c0c001d50311580300d0f030f030540c0240074410300940048004900c9009803000020303c0307407080d800b41c002d019a4955400d01241d040000c0d00803603030307100c03541d60101c0e0800d043c01d400c0c0500c1d10211000c0c0d60809009201c11600794000a00c040c00050a94581c03a09008600c090581da0100720000c0032081e00e041d4501a40e038000350011203040010b0b4644148049102c0c200038141407d06181c41b810b402e82007401c0200a42061198502c10758200020503424070342070086a040b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 842606043 1250 842604793 842604809
    0x10b030606042c2410090f0b12011d13020d08030c0c25170109061112150105120907030b0901020903100e0a02060307030908030a0f0b01300609020f041509 68
    0x40628100300740014100503030148400c6c402006c2c1d0124011480d1340008014203041500f0300d413680e40707501c1140d5980d10b060340800506698141e0180b070000c041079200354004c40003003004004845500c00305410014648014040020120900c2007080b881b500400400c0d4640c0201d9800140001c134402007a000502d04e0400e44412203400c10140014504084900c01c1f0750303000040305103050316a0000c0e1290f6a409400e495000a00602d004851070111500018280140c0f0f000c0d038943d800180803131150084128100c40e82c4400a0483d403010000c0b07201465001e1600510307030814001f0207011f0741080040d1440703030241c18406450500c440c400d240e4020440030003403c811081c0d40921a440d40701400100c10035403a040d80b40c001c03c500314011400f6202c1d600c400101e4058025020003290740c586441b90401141d1800d42004906003003e0240c40003a5082c000c0781032400c000300100411044d4040040240041400c10000c0304000180084601c4000e22050001c48401c048460708001d01030000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 842607293 1250 842606043 842606101
    0x51e01060c0809030109060e07150903060209121005180a020d0809010203160c0f0509040f02150c010608070819150504020a031401050a1802010206010b030606042c 72
    0x21040d8420380c1c44410710781c041d1120510b401003040109003941c07000d140c1500c1c1d00d5258540164488800c0090034005c121404580c10390003581c180090080a545c40003400daa500840c0b00c0c0401e540703c920351401170000104880b00500468610400b920003282c00da0014032005414296800010074041740d600c1e801001071080c19150b96440361980c00c1261400e0443c4400d02140700c481d0121100c2541b030f18052120000030600e8020a0460722580d0780000340a0340800061000244800c01030b400c3c1958120381c500744141603650807144500412524181542c20b02c03c000a25040c0807545800317480d140c01c16114501100d940e441c8214012440042c4442072080006091048503800795401c07610003084804081e0741da845a58010521814008007a55184144051071050b440788609018560300c243c01801d8694002035111f410500c907220f9040303c0040000c2c4076a460340200c03409002024404032803080c2c110165104124510040094440581c0204641c0001c00a41021803202050350300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 842608543 1250 842607293 842607299
    0x21060b0d1a07020f0d0207080d21051519030606060206040c03030c05150a0c02010c09060203041211100f0810050a050f0a08030301080307150203070503011e08030403030f03051e01 79
    0x20354003a0008115104601841c20a40c800f008103210000410045d94020007225040001090600c01c1d800590f00a000034840030340c0201154a00c0f4801c030942881f0300007101d9440c40e5840c0d501207a0305801550202427504919400c000803013000060381c2c02085c08101c2c0c180c9a00c4140e90b10b40d02914060011b04501e034003000020b03c10000e103a581031140054a8181c910121509601c110948000045a803180e45441c44d184c0d09124502c0314842618000c5c5442d898008080e450703200f540a403000c1d400d503451101041c0888400342e10303410640540390b40c000d0000e01000408040010700404005440307000840c000502864001040e0340c0010035a01049143c0380030460010700303c00b103440e000347c2c200d8400034001d9000d00c040e42c000c1c070403030014566400192400007030902c042500001c50b14814810701440507440002c0d68195041c403041c6041c042c84d07000319070400061a41c090680340c400024080701705070f4404812050b89209440c01d02141e210410000030071400c409881c5440d0354144010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 842609793 1250 842608543 842608583
    0x120525021f0c230412030f1e050a03270c030b0714090105030a09020901080606150c0c060a20070e1e04080a0905120c011121090a21060b0d 61
    0x7030f007480d0b403820508515060303036011074064501c03500c60154041071050700ca01c14402c1d000300844240e6124183c0d58031a154000d140540140a02c112010405988941500800140440241c4002da4150000c0b860003014036010011840c21b000c110303098481d0001042c401d90141042c1c042c0710b040c1c40001030805d000700c0011110b0f604002e01c0001d00684484034040981c840c80f6805000e080d00d54042d100354030300394051029119102c401c002d03603010104245010f020001c01c21252014040300c0c0c032583d0380044201141d19005100c50007120308043e0754909507103071000404008982c0c007018000e00b190703207211030035441c0c6c04c40ea510b16040105000006000403c0017008142c6521f10b414581092074480713000c50314200700e526181103698480041080e95607004048054080e020b50b00410b02503000c0159417100281c8212001800c00001c1500d120329a5074510181c090140381081d1007400c0b0700c010800358210031004040e541e071445e0010f440400d00b0030700c6034082240e4105550300081004100d203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 842611043 1250 842609793 842609837
    0x4140307060507110a170706110d1209050c2e0f02100f06090204090203040203010509070f0b03090307080c06041b0f0611030d060e1005030a03120525021f0c 69
    0x921548032109030300102d0004049003500346c610240100074240b0509005014080416880c11140c007540004071244400d0750240c100e4942201014001c03501c00100c0c9031807440d000c0c10f88202984011000b000c0c1c05010b0009400a1100318103501700600c0742c0b41541d0a5600300140c0c440300b00182c20544180c1c0e2456000e40001c250301d540440c0000c1c0d03d0380d07610304080c126041a004140c81e107400005100543c6070900a90341c00060781009007203030625110113001000504d104200100c00003100007105060280b05079a10305410004d01035407034941410550b2184400ca030110b0f581d1812492200314858501c00c484240c03070030080098070003820708100780ca0840c1055003410b4213100801148003001c4590244200425003005540400c0c14081d01046240c10300d40c0109020345c0c020850a401b10358000745061010711a4030303000603030b51582150202200e4003080d405110b0a00c05d120070701e40a5001440c7c1c080711030030580001180c60b48507805010782c1d00c00761fa1031001849591201e80c42c1c50044507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 842612293 1250 842611043 842611073
    0xc0f0e150414010c170d141e1e10032603190e0a05010603150b060f0702010507050d0503072c15040825050f030d2a0804140307060507 59
    0x40544000d94145e81d001120f0b000031008161300c0348049413500411003140034903040d1200c0c1182040041c07a0410060200b1000c29a010704c2c1e02c950b084c0841d9004d606c000710010380c4002c40d6039196040c5021710b0050241d05031803108480c5d0351680100100240103000502d175442020110852075500d880800000c40c00c0d418024140301c9649003403c0009080400520004a00c40d600224605186051008400d850043c0c031040700b41c280b80b81c42e500c5941751001c4401d4004030640b0651a05050700040303505000d002401441442040001000c05400074007640c41100c0345d6444129049900702c4a8201c00c100035039a0451900724070315501c0c1482c2c0a01d01080c14504203212605081c1e4801089140c100ca081e1072207001810030000004038a11a08584050b140c1520000d1b0b2101c1680007003541d8952110110040012486d074900701924882c101c942d1180d007200500390030710128186000568000d10504d4102e1418000c2004113080215071402100d030a07880701410102a031300e80b1002011480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 842613543 1250 842612293 842612297
    0x105060c07090b0609040e0715020f06011e050d03110c030a02400501031b050f09090319030b03010b180103030c060f021c050a18020f0a08010c0f0e15041401 69
    0x4481d0740d45c2d070b48440c4220110006444c00400301c80f850b000203c2e030b8500c040c04196045411942018411340c0c000148241120035000186400ba517162201c4403515002d0740109501c0028600084249644034501d943d40c0c18020096450844200d000c00d56a07000445000b9000b801180448044102019420011a0000340c5c606070a00b078460069540b40c0900c100ca02c0a107544400500600441c000070710010300141c009110380d1030800d000100c48020443d0803270301c508005800240504400d006440382c80004e143c4603500620b40c1e842c050094001403002d60701a40c68501150781d5850991140030715a2200c40d01c0e40c4044c4d0840c1c40840b922075014000351812038442e030b1281c403003604510080032010707040418582d008100d10421001e442002d44681005810606800390141002c4004480c00b13604507030070480752031080e010800b40030456000341d0a65103440e0b20140b040d9089400c0031074001081d1703140b0321002c240b00b040018020b607130390000c0e03403640040c001440144c0718a80c000509032014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 842614793 1250 842613543 842613547
    0x30f020f0306010303260f0a090311031303150207030f14070b010b070201030f0b100e03010b0907030e16060e09041b0b0a140f0f070804030f05010606080105060c07090b06 75
    0x40109182c55000c0e401100045c25049544076151140001290700109000c4c08030207a042100d01041e070034102800c0c2c50030040e80e40c0060b50425009441c480f1006401030140c94032402608110200c03005140f2041c0e800610220081400a60600c03c540860394142c0701d815084291039001c4400350f0342d501240ea48101c3c10820034020810a0000038024020107a40e5541c3d00341601c0018150b800035085d1210241c2041c42c0c4185941e54010303082d0310b016092038000301807010000024003400100002c160040c44480500032600d526402003070107652080212821004941001d41038500705104100004000c0c0c00310001901c0e10504030744c3c100340a0fa00100000c1078240300c0c0c01c511f150740d510441403030708002014010b030b64111000b290414800101c0e01d0138071000f000943d05034411440c821804010008044e010440302c80c041c2c40245401a010998a004910303105000f00701c6400703108041200c9000000e05441d186c003c4070741d2141400b002d0150585041e61550151001c0d80d289a405841 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 842616043 1250 842614793 842614819
    0xf060112060b090f01030203070c02190308030c0405030c01090b0a14070602030f060f0301060b031b130f0e0c1804150519140109080601032607060207051b0a030f02 72
    0x30500030403018094004540343d44803290002c000d1402d80c03044001d4107060051081211407500000680d081a405503040d8641100740600d07a1102c502e1908001c103000004000c0c08035003452a070141c030980340e05a04464a840444006680711081840b0b4002015002c0200724850b61180c215004c4038081a28942c0c10039455940b081e050ba001110051030b0040c55404001482c075200c80b02026000e01a0000c000c06402c00020a0080c4402020a0012001725032440c6c0c12000710400c480700d032001c03c010000c0b0f0a4032090f0401109101d4410001803ca1384008583d4404512045a03490b5024000c8205030010610502020b010f182e22103680031840004005201c2e1540740d0b240d00c03a1031004e000f000340b050501452038139280c401c0950a0400195550a024a101c000f40c1281501d0300a0396401c1e858107200d152030b2142c1000e000701060301c0000300706035081003030f42d80103001c456100d041a541001e11807249481000e44509142e58031960540b4100041a40c401000c03030300d00e0000c1c01c21084622 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 842617293 1250 842616043 842616077
    0x109020a090f06051507020f030c12100e07230a1e050901080d020606190f0f031a0403020d030f11030f091009121d04090303050106090b040e0f0601 65
    0x3155485004210703100e41422a18030941d210780d002130a800c1360700c52404c80381010340e21035500848100034012140e00e03469030101d540400507500404001000003066113182184581c91f44001d40300720f01403c0c1080741001400102240020940300c00c3c2c880b94002900c6100e1310044403510050480e04050001008030b4681c40f03031035a00702100080306100303400d50b1a00090102c505016849842d864005504910013143c1c0840c0c400c0e0030800484500c0c00b80b440802000e4410788441d41300e5040c00305000400210b612200b6075030003c40e80075503100c01c4030a100e00c191071035000c400c48009005030000c810714a145406648216079245403080c000070034400c60590060268000e91f0070410107480711041080d070807010001c020501950300c400380304070b4a0554a8108840b2a0f10050051220083c060703180500c014100410455004006200321101030401800900c0280982000942c90b000081126034100c0110b40485040d02c00b40c850036500e02e10080348500c4060141410440c1a02200104903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 842618543 1250 842617293 842617309
    0x804030519180b040305060f190912030e16060810050a0909060b06160602070204091e030908031c0506062701020c091e0c0903010f050103020a0812030c070302010902 73
    0x580c482d221008441c6002d65074031400303400c81e071007030381c01610400c018000104040342c1c41c0c3e00602e0b425045a0140c0b5010243c1d801060359204d0404076506d014403500c144074424031504d5840621340c40821000c02c2e0500c40b203444200b41c0200000034942c410007001003078805d41d00d040d0300101d1110000440c0d600c13580010710024040d40043d86d03413a22401504144000b0f07100d100c0c20b056040701c07070501d4154042c0c07a0741c06404114002034402c985c0860071400707640300ca401010300c242e882502c2d4051918020107254417068003032401d0700050010440412001800000c4819038201f82641f0841c1034a185841c1c00a4000140311303581000c800e00041842d1400c00702c920102c004429a5000a864034100091801448a4115101d0380305001802064003810109450464070000c1e0807007255501c980c0c8540910420110642641c60a000525040810b074000c5050340e100320b5012503000e5881d2010307031b55601140791042036654100082881598410300406165100e400046200340b0990001070042d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 842619793 1250 842618543 842618587
    0x1101030f0e150a050709120314030f09060129130b0708030106020f0c0f060a0c1e031b020105160c1a090f04090b0a020715050a020408060f0f0708040305 67
    0x6900212081060700101e40801d540070250050130071451600682c0100544c5161180d082c10190214402c01851f00c18440d099403030800d00000c99507420000e144105c25001107034403140705c1c0074a00c0080f504242c02e0320801990140440d007013081840c10120a01d8542c490440c40500c0052210002841800d0710040c140c45401002d40079280d600d4844e0190802a121800c042243c2260540310880d0b550003c049402243c152071080c4c0700c0e94240c3d0252080000d40360050406400528203c104041100d0404441d038032903a145ca11410f40c031a0b800360344180001e07009000c81c4041c810040700e001c2d00c203451003650340500c1e088020195103011914803c006560383c40c4034060005840c40a50500e4038040c0b0b03004800303580c1003144e499140c4400070040005482e008182ea000104102444441c202514111180c2d03e81001303030f400d041c00e01d0780095000c0c0c8200f5125004000c0040c2d0f0004544030413500ca1082d0992a19055650071000c4544241c0200200d06008050051841c9801200001085 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 842621043 1250 842619793 842619821
    0x120207150903090f0b0a0c03180b0a020d09030c0b1c0c081b34020406080709150312031d0a0501060f0f1802030a0b0d05010203190e0a1101030f 63
    0x30780a950b00b0b0090908156400007091a0071031482001070a400074100c4454107018a0821101070741407804541c01c600c15120240c032200b90704404905450035000500984003036400b03d4006220b0818160b0710f600517071002514035075880404201c842d01d110014001d030680c84481c900801b42d9514080c1c103c171100319101d80014810b004100d2161800c5129001d01c1032606896418503210401c3e142c940340980550205442c2d030031540401c2c514440790703401740859009006000c910b45460009641d080c0510501070618207001060000c84181c2803000c0941c1e400019040000031a03e109a010300500e100700d907020b00c2803000640d541d000038404821094410170020804500c0c02020441c9085550010b900d1803844403010040c9003080a50074078452901040582c80c2e6842422400060030b503200c0a0780c214000d01c6071071040050650096210b45800059424101d2030110040d044030400d40c0e855043d54420039001001c0780e078259007a5580081450003003491070081c204c143c1520f0500d02650340c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 842622293 1250 842621043 842621051
    0x14040905150f100302031b01020106050d14010506040b10050c0304090203010b0901020c010f020d030b032d06010b0a050306090415020d02070605130c030210090e0c0c0d08060306010612020715 84
    0x20010b040e40301041d0441c1c000c00e01c0e601103500350f40010303888100f42d0b403452030b81c0700b4080d0080076964002e41082000b010001c0036510000554281322018003c5051003035099481c001c0000c4081c130f454820801550f8001d021034100400b0001c007543d82da449203131400900e101c14017001640140b9800218043c0642000b05515183c2080000e45000f541c00e40903410b1100c561214410958001022100800c003031801050004000d000310f4108074000d51200103d44410300040c501700305024115282178080c2040f96002d030b90311040502d1a01030341441000060b401c0020818624055010345d82040c01646403010403207100440900b02c0c0d0000803055a6250041515401e00c00c140c412a40e020f413410750f0080074500d03030759103011460009020083c0310f070300c02c00031521000f0b01c0b90b00d0031400f405d1035041300700c51410b0205c0095000d1f04140e21032052032140c0032400620798419141140a01d070050010101c60b420880f05072160076040d814032002c66820302c0614082400e1016041410b0700c0440005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 842623543 1250 842622293 842622301
    0x8040510061410141602120a0b24031e2a0a0e06130c120504030c022809110d0908070605060d2012011a09010f0806011404090515 57
    0x402910201c080144444051004003410000d42141c028503602108175505100394400a9030821380c0c07240c2942c03d48516a032080401c20616041ca001b68290900e42c1c10000c420a10790340394200441c1313600e405411401e1a0b8202070700d001d1024036074141c2001550582c00d144805080903002d1a0311001e420490450751803003c1c2013620650f00a03101c1c0c800740c090740f440c0c60000301d440508030500800f4400d039a40300070060240300b142034103401042c2e2601441a41000d0400611b04228040e00b64810f4442d0344206944188041054003d0340f01018461801e5250403551001032076400740e904002301c81040801c4000d00c0750f22410040300d00c0744260989624803820410308442005001c0341c050300b001464800840d01802c01500703d428903061031614241000b0100d18159810f504da503041e503003000810b85a1005241003400041c405840e040c01c80d0781d90350069450449903200d101c01582054006009410700351072404030031000680046041c031042d958036450010054500c4003610740c030700244 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 842624793 1250 842623543 842623549
    0x15060e07020106090c0f090e041a010801020903010f0b1e0f060406030618060e01090506010e090c070314090f0603060303120903030709150e01260c0c0c0d0302030a080405100614 78
    0x9070800100e10b107801c0c08509040400508041440c8c003a12150031017a0001070200f041c4803680307240f054240710014509507034403122907001c1c0d08641603a611a500302504400d040100340300d041600f03400244408103940000d103484003008021403401e900000047c080d40e02607100c50004000900b056580010440d00e0310103044070840541140454041c1000000c1007100c1910528134103507181c140000603141c07078200060fa001c2d007404850f5500404a0420408448006800380031045c0c003a40f01d800c4450042d040308040b0344030384100f80d40e000c850450114128202500656031200d000f408032032910504040400c2500030481c2c04003c150320000c100101a640001440d000305601e16000344034015240024149281480256040044034004101111524881491229107000c2c041e80c0c42d05000035018070340e83c441c0c46103110341e00c2075000409140c02c003000491045601b40c3e01550800140c06821a0901d00c06442a2024400d01d161031803903030082e209040003480da00c0f884c1e14030000340c0d00c24 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 842625899 1106 842624793 842624801
    0x50703200d0903030e18070e03010905060405010b010f090e070e030c040c033317250303030608010b033d06030204050907030f15060e0702010609 64
    0x1841e50003611040a6900955602c000d2000e0001884007422500c00c402070740501180c00141c4140c418681c0c20304c01100200003180048071a10b800d898510f05441c241e5070b6940d0707600100f0442d82c0010341100c0542450500c600f490b0320300380f5100e81280c4001e2440c0306018034414602586e540500040c00203a00040c03003004900e10942d03004000304039070800b4030007462104580760801c252501c106a66078048850040400d400c0100304200e0140980c2205428410903c400c0490540c0e0f50320602c5418a0b00c1032284418074508006090740c15a60060b84281d141400c2c10166880c081035402c241c10b00c16110550440a0481103000c088020800302c01600b003100c80315000458a400c07220490380200c2d1b0500064031200c2141e5100c00c0b4030304c001480d8014160700c0030005009a00020301c21501481d0000312556540c46126100904544000050350b6480c401e008001442c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 842446043 842625899 := by
  have h0 := BRFrame.cov_init 842446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 842446043 ≤ n) (h2 : n < 842625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
