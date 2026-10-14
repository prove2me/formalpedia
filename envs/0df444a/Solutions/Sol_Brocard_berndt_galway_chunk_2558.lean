-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2558
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:02.047687+00:00
-- url     : https://prove2.me/submissions/83e07ba8-dc36-4ef3-b31f-a69dee769462

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 459892086 ≤ n < 460071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 459893336 1250 459892086 459892117
    0x1409041a030f0d110d0905040504051e0601060e04090b01060c0c1203050901080a050906011a0c0304031b0515090108040c05030d0f030f090f020f061c09020301140f04030311 76
    0x7100c0001188041e040c0c40e46035940481c03907184501d602c5d0741d12102c9482101260301c820703040c0300c2810640c0116500c68060001c68110340088012600b25448101e0b0840c51900080014024075500c00480400140d0072502840204003036220a42e40c61018800e100c140504a0009804c000c18a40d0700c100400000350101c400c680340d400e0140c042d52007070410f2070020b14080001000c21002d84034075805080000c00030075042e82481014103005240161a082c0700106020124150504200810156101b010306201c0000a02d43c28210f0540340c1d003241e44201c040c8150250038001c0d0b50207031120400240303002c95441e260340c00c1a02410415800481e094003c03500c11550054018984100324241540c1c1081b85001e000f40c0103048403107142005042c20004003102c0054900142c2084056000030155403520440c8489002d6103000707243ca66200f16260f40c0e0340c0c07066140a100d1000080c948000c0501c591270400c00100d174001e801803005040c9561080401c20340f224180982c0c50602c17912221 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 459894586 1250 459893336 459893353
    0x14010512070c08040314010506040e0a030c060608030d021e03010803070b1504060303020f0606220207061b0c03020c06030c22090c020307050717033109050609071409041a03 76
    0x20b401c2c220501305900031558200748c0420118102841100142220600a0300400d1403d9508803060091010150f0351162204000326406100f0300c01003030508240d01d8016a6081800b220b1681c1201131300d4041c04080050004110280d0080100c0c0e00840d40f101c2001c031070ba070304d64050000170407501c03013a5508903107402400f00030180c0000b4104c50303d450050403103905984d103e040200310035201e02c445807821a081c3e81c444c512402d0341c001c1c1c40c10301d00c1200085484040381c00d602c4110440317100048000340031a5041c000749078041c40803880104090b200302d4510300e8450b0811800d07100c2e0000620340307218842800c010202092a051000e005c500000b802402c0801300001e640350040c0c0780a0f650350186003c001901c8903050780041812800b803016500b000b42c1079000ca43c168000e151460078070b001c3d1110203c3d43c5140c0103828800b80c101a00001132500340b031010f0141e001c0d402000d02c024014519203990f0700d9038020301a10418401210b001c100400b005041d0b01c03640521868103074040c454040e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 459895836 1250 459894586 459894593
    0x3091505031e0402100e1305070e0915060f09060730081b0702180106120b121e010605040e07080613030c030f1115010f14010512070c080403 62
    0x1d5015480790008041004401e1218100000c0e00b40c80003540024501e40540c1c0d0030340201035020b00140010b000191030541c0d05120815a90111006400a100c181c1e19182034604454003540200c4545120940c0710300075000708010384640209259901e0380420201c4695603400304a901c0c44d076002c0d10301c52082c200340c04200342c4a00d40c00a550810107200124030005446103414038810f40300507580980d038804601c071502095100b0700069801941da03d2280385171594151003103000f429181ea840c16114042000712084510701161039104d000501c228030311000340003880f2602031000765031304040a10b45a08a07801801141e00c00341e0024244a0460b10760344020500b07a00300d464050a544840d40c0703400c1320003101c52440c24000e012500801b444000701e44241d4400391100c042c0e081440045c660081c12074034004628408043d00b0541c08014024686040790501c0189158020314810014403000139200e8000c0c0c0303040d4030000c0e81000008031224422400b010240d81c2203003546030381d03035240e0a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 459897086 1250 459895836 459895847
    0xd14030c0106150c021c0609120215010e0421050904090804030209010603140109020f12041101090e090d08150a0e010609060c08031602151512010501060e0904030915 73
    0x2180c00f08100d40c011004402d980251414512036074003d151840c0b41e040030040001c800a00d500a136006507850042c038000590130000009852159001402c0404c4042c11442c03a000f01600b143c003400000c001400001031560440f00c41803c520041321800c0d403000c00c0e04656600036441c100c0e0f4048d049c29441418000f0500062083e00d000f030754281c6990380c8400b800d500b5122154180d1032007110302c400400041c03450381d002e400c070381d940356001c0361900c90b45901c020450581910251500503503856418031540c1c202c4c0c400c400900600014501c0c52606c04840c41d140c001c04420f11701072000f094000b8003495011411003035076400c01071180e004561585103c0d05881024050400440c050030340c08500c25002e41540d26841d075110850300d1542d9100003159071040518503004007580b01e1050140001c0020311810740c482c1040aa6210501601e1010000186040601c0703401d643d140034018801140d029222802041c82510400c202d500c4502d421511582d45a01c0344100f50401d155241502c0e6010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 459898336 1250 459897086 459897089
    0x60c0803331201050c03010618150306051801050609040b01020118120210050606040320040515010219082506020c0318041401180e0601030b0a0e060f04020d14030c0106 74
    0x640d52422a80d5402c0d2a80382220002d0f158950b05a00a10041042900c10301018406000c400001101e01d962007810f06003081340c52400d800070a0b11484284294200702c1c9400e0b51410200c200c21525514010100d4000e115540616002e0740e2666408845a4001d400030702e08200c40200d1001809080d0030301c0300c05030805044000040c01082d041814041c0580100c40c06002c1c0105814905440c40d650203221900e540034010b02d44002c122074102580c4c491180510551904030701d035201d41041000242000c04013a1141010a10449900d0102d01342c00c0c2034490000050b00170950341c40304c01e9921a1f03075a000030801009140001000341041e003010025080d10440d110400780304d61402e008000c203803841c8218081d100a14603004000000ea1001c21907030711040c5401c0001c452508150180c1062800d03002611032880d0041448591910380c455400032030f043c00040d005a080400d00d03010368130390150001c0d102d04079003500c0b001441040da01100b56280203900b16569020250603003400381846 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 459899586 1250 459898336 459898339
    0x308090f18061804032106120302070819030801030212032803200304030f0e10020c09060d0503030406090317010806071205010f090905031605060a050c04060c080333 73
    0x90b041c0c04501d911541e02c10f6000340c0c3d02da107400340c90003540c02201250b250450501c0d646c0742d0301c41c4070000d0410003c103000c5441c603010707502508103030f070500024a00d0066140070200d500d240f20080800880d03848411103040d2a8102c4000c1c000e41c0b1049040303840c2d405950001f00094052405545064100904134202001c080d20103009c400c40d001c00d4248405803001801410100410015000030701c5644698030820460804003d071480f640049026012007034429805a48000420300c0c2340c1c9482d100013588907c0454409c0c103c0103455651503101c0c0006400100440e4031211680205401490350004402154058001c5503070f417022031341e960306416508d0001003a0030780e0302039040c990b45000c0c0f41d058400d4034007402d54181ca07098178500107054218094503035010034030505403400c92100c00d003116103000344004c0106042c44c244e440301325103019000006141c000c01041080d40d81200514000c1c98004a030651a40e0319640300070301100000074400d080314401c4030401200d032582c0c400880b21040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 459900836 1250 459899586 459899599
    0x3130507050102072103020f030301080a0b010e0106050702100c08030a060306180b070e13020d0b03060a140402010f030b040509011e0501080601120309080d0201061406130308090f1806 81
    0x1075500059807528a1401100300359154034841c3c240103002d040c100d4215a21070310490b60200303035182205085800a812442644d005030707400341c0500c05042c41c817070302409442004e840f095250840140482c456400f000380200300090243c69044e000b030105850181c2c1100003150749103070040c1d039840144254042160550b10307014154866501e1098250346803540040c0c41003081c2c460340340036545004040750090344860b6070304802a450f0460f00117010708100300c0f000800c030348100c0ba00301340c1403001c010200d40003503140c6103d100402d60021415900700f6028200104110f5500e08200c000e8900028844c1d0802d003400184820f420301503000c921010310101d0a070172099069007082c2c06507142031060000507031001005020340c2441440808031303688a4204030303102c03540c2c0c0c1140d5400c2803025103010000d83d5503150108101ea0001500110904080390440c2c41d102e60800000e81c3da405902020781441d1001c180d0b0601c54907445c0110006010050010346440050401e02c0f85800c42182d08500514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 459902086 1250 459900836 459900839
    0x1509090c090e0327032b02061b0a1404031a0405160e060906030109051e060c071e0c0504090b1015051206060d0c1e02070605091c02030303130507 64
    0x440c0401992000d00c0d40244c403140000004826a03010f442295a00d9410701070800c0010b100d40c507182041007404104010f160340000003010183c113011004040710082403241042503c0d44000000b26402500d80b41419181071602e0541c451060044d508010a84001130341e003264546110f6030714522452140d01103448000c241014459461800e1107007510418000001c913000e890188105a40b242c03010f400000d0080507516000c3c9000381003289070811400461950f02c04bd181841450343c010b480f00203151030481c40b580c1305282011111001080440f00512400410003050360290003031800a000f03111031501414500c0c29140b007583c181c010168040341c0081c000602c9415001d10000c6920340904000081d458000100e000074151540303c0000c0101d107500c4c1c0394510400141101e9965088040340e480400034a2121140209609550200208010595129085400140080e44c455852190b01070704482c62900d29440294907000200400540310342060000840c00e004ea030444503d207 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 459903336 1250 459902086 459902111
    0x1611090a0f0b240705030d050c04061103030c0d05060a05100504050109121205070807080301181a09010b0706150b03160503040c050402030405210a030e06010b0307031509090c09 78
    0xf5014425100c600d44900349000100e00d1450191460500910990345040d800540c608202c880c111484200610042414000c4c00e034081c001070340c0820b0b50001145581080ca1180f105030041446117000e1b0781d116000103089881c0da101c2c41e00102805414540903c119540292080d002801800e00150f9245800946000c440070b035a15025044500c1080700889050103c40c280d004013029641654100500320000c1d510000941c000c0c8001c0990204460400402500782c8000780072a0a01c08000c58900c602580c1d0a003826044802d40b02d03034076643d03118524202c00602250f0440c1141d900c485c0307500040a00c0030b08001c42c81942c20b00030f2031102514280054a9a000558020381203c2a855040c00141096801150400d00840464609811490366400c1000d04004082031001d8007246a2580325098000c9243c590503c001a158542c10515601c2490000802d40c0c0c0c10962600804040408030b020644003034400b030b500901c0000c0103420117404203401c42c031420111a03c0c01301150401e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 459904586 1250 459903336 459903349
    0x1b010e030304150503090a080a0804020f040203091005090a02180601081e06101403100611010606021506040e060f06090705040506090f0406050d031e02070503031611090a0f0b 77
    0x54540102007a1003203c940c1c003080319660001440b1b83d00d188600610135020900d048050140000c0350755070681036191a106012101d1004030615004500620a0019540d80400d42260b0f08903210800105035441e0340441e85000c03101840a50003900c012006100c0c030140c4202148208401c3e2105501c80e202c40c0c07404440380d82c115100800480d218004500f02d490f1141000d00e00c1c4449140040380c1c406600c5440c0c00c0d1381d000b030b1801082c81c10540c4040107080e401100f00e60034001084001c1003890b14040c806034484880b05541c1c0e0401861100040c21030780c9580c08080600c2c0c01201320388181c40c04000c0200271100c142e4880c1d01c1610200005040240b04d142203505079400901028201411401882a203061100002c1da0140d100e01004c42c0f6901d0395004036074031a0080d6101d62203d000e26004800c6518606603610031500107400500903910004211001c0301d2085291400629890412030202540c10b00c43c242d00031040c7c003d00c078101d02d441e040401c41740c2d58a90200a40a06075081000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 459905836 1250 459904586 459904589
    0xc05130506043204110402030109020307031a060702130e060c04240e0d02400b09010515070b0117100b0307050d21051c0902010801050d141b010e030304 67
    0xe1030b03a200076000a204500c1c03d0b40a800505c56416201070a001c40001816600240c000304012076000c000c100007150b05005400750084140701428000035014080341907445601400790040c100f4802c206440001a4440c941d1850b071041038441e9810040050a50303680315125202e11001159880a40e07205c803107015400c00308094440e20390000c07188051141011760450180d0303001e0800010751003032864448443c0d00d02da5109030b129410140044c90101090a200d5406200c24a402c0d06103a140d10741061280c1940d1045136100345c09600004120036620541c480101040b600d0300001556040a8480a800f511347c40191030524100f041014222680c7c684503e90542c4450001c0080341410308040090354029644420661491510110b4075030307030807600c40002980041c1e0010b18001c00b40d4060203004000100740000c500741c0e00001e26948043c00341034402c4610030041d40400078010880440d104a007402c0c0e900d074503c1e20a070101c0101110680e50f0215102c00a1031281d803501108480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 459907086 1250 459905836 459905891
    0x714030a060b01020a02090a3801051e0f0414100e040c020f1c091d01091d0a0c03020a0f0614130f08010c03060512030904090c0513050604 61
    0x4a040d4551a200c01610b031000c90b80381940150f030f50407009070701c0300400e25120340d01048001c210300c070585003607546415088408054a20050250040da071f81c56012603001c0300f00911300b2503101c94940812a80a10350405042d00d00000001d1860618070307100d010740211642d65101c10f5a401d82101401140720003001e0b040c0c00207400f00342440b003e1801380d100b4540303846144100c4006c43d20f4035941c60702e03002c010b040c004190b1941e002c80407006680305012001030031068a000a50384544d9000040303505040c052441075036203604004802c9070052103155000f61107082200e008980a003002482408280000c1e801488051000318100a0018041080701c00ba80e451040200450410320002d8026000c0c20900000200c00041d4090480303071000064400c2e10000034480416860207411a4101e500480c000c1d501c084a40b50192004000d82c3c031706c4241642c1c08692600c980c5402c510030342c8a90007076988180900341c0c40c40402001c0e4030044c42003c003036504100c00d1250b81c800c80322000c106405032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 459908336 1250 459907086 459907093
    0x91605030307060c0905100305040212070305060721020a050703030b040606020d0c020a052e02011109100908190501050906010f1502011b030c0e090103121b05011d071403 75
    0x3d5190740441c0046420f4a050b072800c03a11040018040501c004400001984070b038148020b41c0380c210900301001403608002c1c644289999120746e03c1d100c000700344c0d2003808406005400d00c003034034101d2601da6402aa008540da0700000c0d4000c0c00f00d403c5000d00b0b90000b03280032042400383c10b25105400544207550000c1641407031028044402102482d0220780041030b0b003000141540302d2040146808011078102a20791a600c1c10100c01401c0d41650141160f0404c01002c408000c1c00d4102d4108040903170303201201c2000b9441c16503644c0c100d80e104003254070400703c05490300070248540a0304c841c8240020b11080d01c07428902940d4100c28042c280900c3e080c80c8013008000403000310014105454000480d6010a00303400200c140c5841c6015800b19171681040214250301c0f11039216599401c0301d10303035030550542d21107650700f0140c04e0010044c41380c03180d170780302e074000300c0184090049a205000b0311440310b040305581c1020b444154010300c903100301080800e0141d0290100d0303480a0003c2c008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 459909586 1250 459908336 459908347
    0x6020d3c022d040515040302010f08061f050c101103060f0a0306060308180409030f050d0b090a0212062b1e0b06150a0c0212240916050303 61
    0x11000039481120380c411007400d504080782d0b030409a40100485101c0b24010283c5461a1000780b0954429541c0910505d84d81008240010f03078110340901e2501e1403e00c0d040b5603954884011580e544240c030002441c982480f07517100281a4004007c20901031002c05665208070500b240d14103864800800030703822101880080d4150500842910548200406242e0803980d26241c420843c0c083e908240e5649100098048219582500c68040c441050b9010031000312140c03002401e48013000d19100403c100000c10386a5100705800524202c0c81c020100f6826081c1040c0c40c40095000d41700600c040e18040000610318500f01a605480310a04205c46401003410024205418500c0f0b000300c1d00b140300c01324000502d21200030b04201980c802d01b9403030140d0030003070104002c1c2c000003001c0c000f80d407508001114502d6031180703120740b882d070781526240340c0c0100c4448141d080804044240003510341000d80d0042d013282c080c0b400390043d42da09081d2076103000341e40001d9080e0010b038002c0c590158005c001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 459910836 1250 459909586 459909701
    0x30204030c1701060e010b0a0315050d060509031b1e0c01020604030f09090c120b09190914120d1a0a0314010e031c05151804060906020d 60
    0x408450055110b400042d5154640e10405d59140c006e03000703185421000704e02c40340c0081d014032411702041d0b400c124680304280740c0740002c0c40f40c054105e0000c0200781c0f1040415150035081050316407081031005101b1003d14400100c69075090300e40a941a0f0343c4280041854420010902d00f0a609040e8094052607942d5281904d02d25482d103010010007070b500f1400940e0784514480d50700c4844003a924010029160801001914801c203081031041840c0c80601c0502c02000034410601e112440001c0b03160106c078204210480000c02e031002c61805469080039110082c1c40c000d15103440200f02c10405084007044002804000c40c51454200380481c0040c40030504450650090700c03000cd0010880d10b161005440c21745c0c0010018420b102c8151180300c440c40a140075040d0300180003040741e003046030340b6000101607645031564022031001c20300c041028464590041c420240e00000d05540d2031375a0602c035002013401d1814408125010120500034409011644c1ea50039140891403240151940303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 459912086 1250 459910836 459910859
    0x8010f030b0c030403180b0c010e010c051801140a051e040b0909090a12021e06090a060908250b010b07020307061b0b0108030301170f0d080a0f0207060b010f030204030c 74
    0x113000f5018450310004a145540050a014026002c29102191501e6a4041032070960391200e107182d01507410407041603442c950000c01e80e4030581000122a8a1502c0c82d4010b0f00c4140c690000c0241038400019141c90700c0741c104000780340c48030305480d007007240c14214070203002d090103540103c0c00c048404104260390ba180801045400c04010005c0e1009080303156900d580e410012440d903005030b00604e035040031400d0030307a940d51004c003a04405401945030000300151503485100700185603503a1001c1d01c00500486c0e005071905c04842c61511000c80d4400b42c1032040c0210025400c40c1d80810b007000100b2a0f000c00f806880344981d0180c014a401400d000b000d490852040884d805049404080c40700880c595422242c02003030183c01851b907d504094941d0100c402005a02003103901c503c845400e00c50001a81005180292900e010b640e03c810401c04090b2254074038040c0d80034004a40c1c08248615a0700c4011186402d880c0c548000030f010700d066003640260f12000d01045c0e41c81004110f074010300c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 459913336 1250 459912086 459912091
    0xb030105060f25022b0206030414060c121003020d11131505091006092d0b0901121107031b020901031b0608010311010516060608010c08010f030b0c03 66
    0x5411540c108000070043d10008152414010010061008404150f00380060740c42e49601c0c40181325040840074403840da031070403000c1c03c00030b002c0c1000000040c1032240d40040c291808885009a90081c108000c9040d140c5d0031001020844811083c042626051500040403c81ea409049040e000e4526100c0040540e4461036498204080300c10791a000442849400407440d01c6447c244411802c020178080e1190303008108d48100a9244030921040e034109000004490014114038603503812031b510044004155003492120014503400881c682c00f240020f810346203401c0c2e0300c00483c80ca007400300405807500e0b40842c50301c442c0304004a00200303100704c000c8080c0642060300032082e90002c0c1d020900c0c20700b09900c1580c4110200302002c003034494081e05400207010a140040389941552511140c490a0340821414000005680004404020621180660005405c11605586400d01ca01810814001c2c500007421100081400c50480c1d60100c16241c000d0560002c2c1d64a01107007921a0b40702 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 459914586 1250 459913336 459913357
    0x30f030209010e0d172704050103020904140c0907030c081006050a030e15090607020609010b030c0f01021501060305060109091b200a0c051512040b0606120a0605190b03010506 77
    0x10421450b0380b240d07a030004201d568031244014030240c2101d07041b245076003074048140b48103d0900c001080541e840e075103207641203a00b006111181c0698540c000d450304018842d110f0300040c10314100612035802d40d002c090003200644404049948142e07114040c2890381c054240400d00c207201da810100e102e035010301e43d0100d48404540024080c81603696640c201104e003541a548084100011650f052000f20742140581e40280240207044c00040e45070122880f90368090303408881e02d42030b00c2e032003007205045812042420500035615003800801500c0200e521f42c1c045003e00e0030000d130344042ca2090403c001d010800582d0180c1d08954102c44075051640014000103062403441c0001c00b003404100d4030540f1030064500c1d0702d8500400d01000200c803a404d08903030103051200a42c41c811050140d580954402c003c981c0d55074030507002482c513010f490360f006448500c0500708030709080154418415200129892441c1d0030800351048a21071441c0514175044400703200400c030b1420202c0160103000e0344d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 459915836 1250 459914586 459914603
    0xf130803101205101b09031209030b040b0601080c120f0a02041502010e0c060405031005041502130f0b0c10020901020c270105120a030e03031e0304030f030209010e0d 73
    0x7036900a8025911001006540301c4c2c001204100e1115024421404550561102d0040714208604041d255010174032020305202c034010011a1098841c40c002c40185070f100c0903c56079424a03052542860104407409408071310114040f6a1030b00c0d10304192080465241000350569407181011103544501405400c60b02d9002c0c080851902d42e8520f4820f152101ca50001030091191074000385880025142e280c001d0401300306c24890790310b0200320b080302d1992004000c90b2a071542e2801c3c4000007582044026060300c04600d8034884080d40e02441c080f101421021201c0300d4483c1507541c0d03640310780420003849034043c1c0b0100c030342090150080c00d507000050058031010044100031642c94006098520320000c600c141420f83c0314a0a14013a01424007030b00c583c02980c941c010f2140e50f4500e05c01001d014004145041019590200102d81c942d02290030118509501800900002d8109030b80840202c2c1c6d60b5000c0a43c0288a442650034540d4160344072000825a40180560840740e041d090f6103200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 459917086 1250 459915836 459915839
    0x30e07080721170a2106030210111e0d02060a1a0114130308041509030b0a090f0c0b03160c0c0312110609060108070e2403070e0106080a050f13080310 66
    0x50000300075013032030052610b40342c201c460315050695800f811380c6007148030b2914281041c00582c0b282e040500800503641044081210382034000f0340f07026100c11724800000320031039100174451800f0030342c51901481c3c0c1d000c0320320380e8840d200081c1c107642001004803030107940551220000e40c40b810350000a00c6d1148042c1d0700e1b01104522031010a00c640e081503402800c00201000b002012500819800b6031601e851103006c2d003140c1d09d81c001d031078002c2c1c070b070b41916901c5223580028060b0b04000c0c10503542d03000202824a90751100f40c81c45581080703464500900214031242080c41c0a0880a1101035100c0e00306140c1074115510400d406050180110030004107101001160608006e850301802050000306103e41c50b0591091074840140c01402d2243d09803001c1c05003a01c1d03054602d1a0700800403030740060100034203002c40d103000b01950182d030a030340b0020300000d002500214060300503c1100020b200303c0d41ca003030410062007429181088203803c0e070030121001c0352a00c0040c1d5001012039021041c900e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 459918336 1250 459917086 459917123
    0x16060b12060708070f08040c0326130e010b0f041203050f070309080c18011208210a140705091002010b0a1d010f081209010302090907030e07080721 65
    0x1d0444100010034910014890040e13044080f40a244800c0e1400c0c0d103941c90960741d00d13800c1301d001e4480240701c10080313a00000358800005590300b0300000740b0718064071200d030400521441006da00ca80b9064003001800030480c1c85c082c000703d4140e00c194140e11854980741160088820503008415000c009041c0702d00980d80719908018000036000e40d8035416040c2c100b00e8042c1c02d000c185400c036445443c20f00140301c04d0b000e540021604440d05908254031034403090820f0b14282c410740440f0300018011243c81d00b80c41c044007031803901810400300100060b2811043c0440307039600a40f403050210300c003840360700f080d0300e0920352001031b040440c400440d440600c1c2011031100306003174010b003046423003d00e000440003944c80d100c5801440900c251404080c58291900c0c2c40d8041d2f802051090304000803108407a0740281c044501c0350001420510322840c214030000e0040c60fa55209002d107018404000910902c00540d04007a5011100c8040c1010381c100184070b040e003006007040f9451020168103107a07a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 459919586 1250 459918336 459918343
    0x1060b04090f0f0b0f0f060712091505090a0b0a0e03060a0b0111061b1e0a030b0310050c0a200d0e030d02070308070f1506030c090608010216060b12 65
    0x510003914003240e50003884441c0c2055030f0540c5145203440b80f9180b50003402d541d0384031413800d07644410745060b50f1104000c004540740d44548070f0003814001d491001d20342d80039803251454040340c02c1c64501c1e2400100c9100c0803240d501c00d40c14043e40c0001c0d003050030300200e0b1014009143c01d26050501040d00061600441d09110084074840c027800d9482c1c440c080c040d60064802c901946644000d400b84d4500703000f017184084403080469400c92804280c4140d6410401070039000300c00803a2103a62108103100c9d0050213890450b141c98040d020782201a407440340c1c1809800d0050321215134080c1096503003c8100d4180c02154103244c190714505030001034009060294141082440d500c100b03606208400f890300c2c08c07030541d8010007158003608040000c58001402d0303500140d4000b42c5503200031854100b07403158520b002c0c1c10038003091400304004100120385170700100301d5104c540e00780100c9a072115468201c0c00f8008030102d000c1c6044020100207502c607030201880d400000d101c0140100158851840d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 459920836 1250 459919586 459919589
    0x11a09060c0111090f0109050a03060b06160b010f12031e090f03080d060e010b18060c1603030807030b030c15120a09020916051207031e0519050709140301060b04 71
    0x3070f0b0400021007450f40d06003250410142c00c000c1c00d000340000d1400000c20030318001444082e000559031190041d403940c3d60001c4072007820105041701c011031468101090900000c0c07103a07a45800c400000000d0f41c064510041c501c0c540c0545070b400c12009030070380c80f494580006040504100964a010460b01504032000010f1401a644692195010803600701101c00036042400700c01410310041041c106090203d616805e60360303040500c0b8a0800d4003140c100d0041e02840b40d86402a542101110b1041031006d00849000340d032a610f6940b2110010b504031551030703907210303055001102d48030214100841410031441036642103d00d00300c1c072041c031000d0201e0107941c1030b41455200c0182c01c0544c50040c4401e500701114454108107814030140240052142584c1603603661380c1200041c00d41e40c02603004941e1710440103200b48007215192450001031074110354042030682d00d41c4004039202e690f440365504c1216aa220b199007241407003c2d4400030842045010b81c113640301d20010440c550203201500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 459922086 1250 459920836 459920861
    0x3040503030f0d0e03090a09020a18150215060f0108100806130c060e0d0f0f02040612060e0c0334061d010f0e0d02040e0607050705060c03011a09060c01 67
    0x181c40b2071070500040169890300202403002d601c1441003000c19907c4024810482d01010001a80c1c0e0801c41001d403881e1a0f02000800d8003011038500207540c0840c03e4103001c8983d4650300707881c80c4000010740041202400d0381c400c2d40111414103a007141c1d5006038001504004001201c14023a65158101d6162402c100d079440b0390718a501860500300480480b00b400600050b00b0041c0d6440c400e2004101c0150001e1002703003442d02c1c5400e007041408a016100c05030a90003510074801c0c01d4840940301c0132200b510900300d40c0c1c10310344800340740829008039a03009002c20040140042c01041c640c034151040306c1c80b0b01180b1008040407502241c110300d500a0740286444e8a9600003940e03155910b00404a0040b05141800154203070500140e80c04500d00101840445007403907400345a002040082142c6081c0308190310603903042c03091080d0044090103401c1d110304120f6030140d5407a0061840c50200b0300c10b424201005248026030b4030000c0e806403440000c0a010307181001d40e81c192041c2903440003015003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 459923336 1250 459922086 459922117
    0x601140114190f090806060d0303090c081b04020f04060818010509060a051f0b1608030114030601080f03090607020f060a110d05070c1802040b040e07030615050703110304050303 78
    0x1003103098004280c2d01a82c242c50401c4d00706240b41a0040d40c40b258020145ca01c9000d42007180c100b058000d50209140780d03045841d80c600c281e141da0038266503444d4030007407c1c2d0081c0e0500b1606d1180c6040e000726241002e0640409080ca8a045c905441800d0083c003290000b020f000c20b0740b98100024416144030b204030400810090178104480f008441000d8045042c2e02c1c00180c50b40112109500b01c0400c8414140d4450360301c1c03103008092a003501022000410a0a0000000032008402210801d10b180200d0aa4401c1e90343c0315603aa0303a440f14840900b07102d4006000e44071132131070440050400c681c00503061030f80f855400340004000c0e0340026541c0002c01d902050304503075a2020801100750074542e0074a545068080e0300c6802d074546143c82000e132580345186050401c0d0341c0c0750301641e0083c514480c071961144c0e164441600101c03000c441e00d1002074900400018040b5420904a00000c015210b5925182d000d0702c003220001c0b107502d10b40b0001d220070000000c06850810040c01c0c0503614006d032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 459924586 1250 459923336 459923377
    0x9020d0f140a03030218123c0a020a0506040819060b1002100b040c30020a0908010c030204030f02060a1710030204110403020307330806010813050601140114 69
    0x20030480c0c0c106001c05000307801f40d44402d60141c400090020084501d4030080000f00307040101a00044a42100c111840d0001c204083d590000000c402111610031200f04e000b4a440f03001b40701680c001d510030f481d240d60142481c140114822604807402c24021030020620581480110b59a24002070f04400140c0c02001e002846121901c244800710300704650501c80300c0b001510007006030380306e00c55222095055601c902110060000c0d640c180c3c9016160030354640000b990013030194219449020b0355542131038030507000540300744202c80c145c0354440d44110790003000303400384a083e07040842c0c15401e100120344102e11011800c2e529921842c1c030007092060690852051101f514003010f00401d2a80b0140414001654049915003c0d10001d02c14a41c1080401180100c01e88080208121507100c1e40f28082a643e8072600e44c40c441c81c0e081c0c035600002c0c0c690043c000300c0e2000303008000c0c20302d8000341c006008440018105603069101403610810000c298018424158404c82c01c1400c0d0000c84c424 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 459925836 1250 459924586 459924607
    0x26011a151801050a12361101031a120d08071b060902040b181b0408030a0806011e0206041101020c0a05060c0c040f0209150313110a03051b01021009020d0f140a030302 73
    0xa00c1d903182d07104200c50607486c0241c2c0c900c5c104c0000c01d00b10506040e12284260005000b625070703c810454001c0017155800740e54200c040c2c480c7d41c50440c1d680010085000660301e00e01900000b050007000d042c0364501c1c4e0300d403034403828000c0900c0c1e84102d03441902c0343c00ba200156103c284284441801c1c0d4000c407068145054000c10014070700301010000c800501c01007000079008002e56450244074204a04140e1b13450b8012940c404210590529070800601c900b030b00c540d070001707405202e544904940752425062030010781e43c1d9101c08043c154400c11540b002d010f60b085c03035406404c80e298a60704842110500e14000707415901140c0c0315801c41540481c1c6010745103800800d04000035110303a0a02d20350709082c3c0350401c02c00608400079040744069003080b94981c9400040c00b000b1500581074403501030701041201c06084a4801e000d0040c421250000d0095045106020050794010300004450506503030342840302c04c05400030781d000e198400700d11740480b106000c0302005a01c0795030300590301c0c0c14518 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 459927086 1250 459925836 459925901
    0x60509070501020c011107140d1a0403020d09080c0d0318180507053412020105090111090328020d03050703080a02030f0126011a151801050a12 63
    0x4084c5410440142c0c00742d4140072010400e10161031880600041d004400000701e00224803646000b091071001181200d608584007400c64011480781d42036031032101c410b1108803032844d000e00804143e5082000b9001c80743c03600d6003203141da40e4420b04110000010082400084080c240d0058203118190149004522018401c0962110040c10a20308000508446a481c038104006a41a170074404018500e0001011140c1071683e9000c0030040c42440b60200080c041c140c1138480016640c00d0400b200e921410b1002500c094100150052840761100001c805c601da64a20b00d4140011b02e081003080541c50b20144c803e0018081e4a81613580e428525000300742a10082c80072030720324414024000c1d511407035500307181160008114142c00d15007408115581031141744000c1c10540c640305503008807481c0029070300c0d035000044580003118a210100a121403081002e10644080c2c5060000041d40c092409007480f4a8641f4040500b0441045000101d0f042c0b48085085400381d0400c8041041510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 459928336 1250 459927086 459927103
    0x90d02100509030a0f020f030409020912060103021e18070c05060108060103030c1118010905100905040213200c010501050f01053a060905070f0c0b070c080706050907050102 76
    0x14001080103240c600b100640b41d016000c041030400861a5032014a588204068603804800d078003525580e81c5d56501440c029480151403074061365603001a01d44003038000c64858101c94010301004034900c2c11031141d84961004030305503680300d40b0720b68441100c4424940138a101c0c0c40c00c0d444081c910300c00d0b1b003499481d240e8142d204a10075030056005200003903100704070303850b0740d40d211000810341900030b00024042c40300d2203046040c4903d8017000081d2401c150b0040c50150180320301c4400c0741d179103c1842c18240c40b011500a50403d40c2c104c1d0004030071149500009603584080800313104180120360b00c1c80036900c800e04000b680e82d11003005100c286040d08483d6612502402c0076858100d400500c1e10800c40421544081054406611002c8405030350720b040005d2401d210820180d51100403c1000f008242c0e9110f0004000c2901d0000d4140a41c9911011540211064120351b4813158200c1d40c4881812044032074482c28068000040c0c05030184900a4100300f002d40416420180020300d07040d4207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 459929586 1250 459928336 459928363
    0x10080a050a03021c020c090a02041212030e0309061902010b09040b0609060604060c03031505060a0206041101030e07120f150b1918110f041206050609270106030b090d02 74
    0x1413034469040d680c0020b400034800d03405444441a581e42c0348440c200a00455102458101c401e403030500400545c60b048007d0b90f80f090302c0400046452044103656400750303160094201000300103100e142c02a61110070307101540ba10000c02c1910500010500f0080300b501c0880c1c03803001030010f10a040c9400404198403c2041d02d443d420715203416802040e0700d20080c00901071503590660fa41001c4000419a00075203406048569510380d000e03402580d481040f202556403c95101485007258401c0c0140801180e400340100350f003a0820007500190305178403100305d56441d01c09881c2e034000340d04009140c0300b003c0e00c10300001e8580c41810a011382c00c01202c000000e50b0003009801d000350400200084d02c0c46540600000b66601c00e9a00c14030b607807040410000408801190004010b82e03408440c6404034030502003440240c07100002d0007210203058504103c0391900020241e04150b00041c2403103c0d107124030001c82e000303070b4030f85501604440a881c0603089030000d0200d4607002d90104400e90502c2c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 459930836 1250 459929586 459929623
    0x3120c150219030e12130603060b0c1e0a150203060f03010b2b0c030605011a0406120c0c0f050303071d091f0b030f0a0e01050f04080310080a050a0302 66
    0xa06008160b601e94014034040c55603030a8581c2c06903004200e00000d0008a8444550700d404185000c0c842c034681c1c0c407a58002034100207001c00d0580c10700303040d943d100301741c01d000780b040032241e40d60781d1080c4800e91000d44103841032001c14004158911503c0d00801000b505c01030717913414480c040c030040c1d50100c00d20324007a80c14003c20203000d4540241d202c9031004485240010350000c48440141c038805094041e06884110401000340001903120a04072891180e040e44c000c000340407440b0316400b55125003000704140c0040400584030036007246058071040e10f0100c948054503907a203c00810074000c00d9543c1d0340302100b0019120f40141c10060054a0880181007520354800000c8950740002d08030100300811b40400c050700240c1203000c00160002c1c965254076445c200d289501d0b41c00c0205c440700c2e021400c04010310b0310810306102c0c050041903038081c100030303544d5144c6410020350b2006d402078410400f103550004200d441445034406042c81040505114021410000d10b8446210a800c2d600340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 459932086 1250 459930836 459930847
    0x90504050f04060b04020708180108070f0c030f030605040c0903050d0e0a230303070311060f1504051812040e010506120106030c122c0d141303120c1502 67
    0x202249500360b20a6000c030300880c0c0c12040d0740c0800c019001c0c00c0801000c4404c0816240d800d09420707040c80d4460b40083e641c45000340d44031071085440170403400d00800803985127030741200840e228551008144200d400c1c0802c4169454020800b11040341d0b41000005e074900c1018401c0280900a41d103c00c2d0781860212580001c0f680051000107032403041d01d4064140c8140c4e552900c2c0710409044040e20018107680e140d03041810064040d01c110440c0c000d8038025080020301000706040c42c5030048030741c0303090f1450030031201041c04024000070780490f160b100c4030203030000d04503000c00c200080101d00b106225101ca01d40a010541c205040e08124400e00042c0107140107201e00b02051811600742d4a0046071f07001000800f690360b00e030b0460180580b41d0816000904100200381c1051400b8904030440610034030f4000b605441340d404000401c009000e688410400c01c0100000d40405040e4140c60356a403030340c980d6405491001000b220340803407100400c00c0b05107c00207202500400021406605c1d20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 459933336 1250 459932086 459932101
    0x102070309080f0309191205030c011b091205070f080d23120411092409010302011e020f03030108010c0f0801060f0c050a05060c09040b01090e040201140c0102130609050405 76
    0x17801680c01107800b805038620380100c1c81026500810050010f140e1048000741b1030704000b5269071144d61001d22139806d065020440a24440469140490aa54040c1d40704d04044080c080c602500c0003d0302c151044c194041616a41040032400030a0800000c0005841401026060700196420691905200441113030b001a034031b021182d000348440380c480501d545070310785000b000b00c0325201c0a03003000d0560104908001503d0046405441900b181c0604050540030031400c00e8003404000e00081c8890030012407540d541070401d0f800c0000c1d005840c00c03c1c400030303021460350300240e0002e10169100d09021402c190420701000c0301814500d414009503040c800090941c0c059203400380300b00550591000240b1a05100740c40061703a005007502c00b242890380c0007008603000480864403481c07411511800540c042d07101d00049503082c000c0c034050340c1e440c1c1d0019207010251103041c0100080400c00c14080311740070300c000c0a6030170845450706100e50030b0280060030001240c00c05070060f89800140b1a01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 459934586 1250 459933336 459933343
    0x190c0e01030b191703070606091e02031603020c010f0906050f0705071a100806070306050901050a08190305090d050a1718150f0d021213021c02040b09090102070309080f 74
    0x1a00c1e00e1244c420740e05141d0079a2140395115480000c1c0c19640b4091011400340301a07000304205d40c112520408038981e032450f22070200e10090300c40c11051101080d45840d03250003500540740d0021600c00020ba4040d585403a01c2c10388109a40840d00390f55218208141c00d5000300c20241c201d056032030141c6c2014a00e0341c9403440b0011f2188a1185894400c0c0000c0380d03024141e207184040c00084c019144603003860000900646124000d03584079250a10020840307042a4101c14211241c1000030b00149950b07041e5003000800c0c1080c1a001c01c031041260300d010b40c0340d0fc0340502c211440341d40100344121541c2800c40b8514155654cc41400c0c2c0100040000400d02c1c02e001c1d03070b00c82d40445203da4891101030310202d1600c01d2182c0000b180501040c0e02c1c4008829034081c041501000c241c000d9a41d44070308400c2c0e5000d5158000a510031107484041884442c540003105d11144003910020301103182c14009002040c0c100ea40245070fa4001811070101a0f000460400418106004001100e00000120345 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 459935836 1250 459934586 459934589
    0xc12030712080c0f1c0608030c030a0e040902060412060c022d010f1e0e030408031b101e0e070501020606040e010b1005040618050a030605190c0e01030b19 68
    0x7080b108001103000700c040708084600d43d481d49002640c0c0c07120180c04040e10007101e1200c2021031841c24000003205400402110b880020820286181003407980d0107403004000074082c0c41c0c0096990a11000588a56004101a00040c003107005030680320b103068003c0c0d1b040112000c0442d00070b00c003007814140c8149408003482c4c0007416031b1034841c100e00b44418014000414450413103801e001c541c6507140301001e200c0342d0110412070280032040b0059045540d900c80d0b4462061180c0c0108000c500c546610400c941108003141305075621080d500381082c042d140c2030108155210600513051560b1003045c490313074a100b0b0140c0c01400300c2c00d1510001030745504004005030301440e01c1e80e50700b0040580a42c4010384462005110302c40304100e85c40002d110307400c140101e8020a00c40c0c2e1404400781c0d00218248101c5034001c0400c1d4000f0700f1560341101501c070240c511000303498030160880000802d402009200007150380d80728241072447c40014165200c00d00d0380e600a100400420a4a0301028007a10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 459937086 1250 459935836 459935873
    0xb24070803061207090518010608210f07110a0e072f070803032d160c0218040b0a0b2d0315010e0601030506011e200c120307 55
    0x507241d503182c4011400041079041030030710500810102284c5c03c0e000b80d100e40d00030241002042c980701c044003616800c03190580115562a40064400070032010355010b00b07049039044504a9040868212906032a0b81003c3c1080b55005003024508015041c001c0c1004c0c001c0800d04420240d908124002410051342e00f26540c915281890048003200004c1d801c5030003111400c401c85100f5070351124100c4c4c40e500141c588103120003100240994a01034050308013008544405035810740d880d80b502d2403035236089000c944014412107140c0280581d6400ba0a0032206c1c4c1010805201490103240806890200500400306580f40c500a1070158941c1102c0e80c0007030f550160824800d00440404100d46040940d01d02c1e4580708603100320300000103003c0440d040714840700ca40c1840ba111a00103509441c0100d0f429400210300d0781d44603031062560324519200d03d015040c00b490441c0d000e171112911424400c0b620500d0381c0031007904a00b41c180354100e180c0a031014800780d03017049400c1d55682e0010750a90106c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 459938336 1250 459937086 459937103
    0x6060d0b06010804020a180902090604020a080114032d1c090b07060f0e03130510050901080a0f0606210504030c08130918020f010906050d0f02090301060602010b2407 73
    0x1808540fa201d1b5164045c0c401003c05007042a80702101d140940005d000032406801400302143d02810140242e640080650302c55049a80c00d017003417100d0a00d90010319950621030380d2040040424402004c0c0003032034481c5030b48104280b10310301007842c000c2044030711500d40e80f0b6840740c3d0714030f2540006800166680d260f54255075440310704180000d481041c07400c002e2903281034000f255502001000f020340c4071441c2840030f18103960380100641d04180103100720201c2c030104001545503100d00c0026502c0202190700003000d041c1e000c070000031100c80b40c00000c0840e4000c1003007652500c42e050341d20045150a1014007440c5415070f001800c3d82580c0200a018840102e828070a8940c0140003001400c000c084c10407000300003208880808211400580c0160040104100030703500c0381422005444041d21403525017805900b094000f0300000d040112015801d008030340b1940d0b003c0c016840205004e900100d850b05a40c0704000c0750072461000030184010007841d60310030786400002c1e10141600400c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 459939586 1250 459938336 459938341
    0xd0f030b01090b030a050403120207050a02010c0203031204050304170c0d060903020a08070b04060c0509030a02060901170a050411010c0f080a17040507210f1119080d0206060d0b060108 81
    0x580d4010700c0b42e0030a9001d05000f100b080321301c103c0c2c0d41c080b0744124041d5550b0382011032001c500604901c41e00c070000c0c006030007031a030ba00050f502944207810b0691020b01168903041000d041005900d005880c110780340e4100140400001c078035948403141e541c41603000b504c170704460240055400003405400802041c1c454030920141030003030040c00b081d240c01a1500780c0d00c1d12103140050b20400c0403101203a2161a21200c81a054445d0b03060310030400d8081c1c02041105520340070800150400302105041055448510010700e0102c0c03001401181800000304031803d0a10305260b8002c40c40041a040200e0b040703000c2d02142095000c65026a0010341907551105a00c0c0b048030040c0c5030500300710361320003181c01340010028009007150031694a517140d9603101405105801820344e4812001d014440700320349042c0812a0001059640c03540140000c41041c2401400c469001e107640c08000079070801c00c0550728043c2c050194941c0310a08131840c50314086281e03911160b0200c05403c403810840701400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 459940836 1250 459939586 459939589
    0x10c05060406140c0a09031e150e0d03020304050303270f0105040b0106032d0204260c041509020c030405190f060e010c06050901110f090a050d050a030c0807080a1e020d0f030b 77
    0xc8d20f0090703422022a00c5c521403c00c0f8144049c182c1016030041c20f00c1001120350010b4424800d403070086030301501551850311502c080034030f46040700076800610341240c9260845114100b01d40c034901d066450010070603140030700300100c007500145e01c10800e043c104078061205030303030041c1b0002018507600300500d104005151034000030f002e290065500111440f07030070340c850030000300301038295242c00007152940e804600900c41907030011510030107c1c0d01a580140220440358000c1d1000d480100d0413203040075541c0002508466542003200900b064110041c0302c003807071034040000a0010f41c01c090f0352050060000070314400312040040c00903aa2a8045072040c0300a41000c91900c2c00003038081e0b140d26540e440c00340540d1010358040c1c420404001c0000c1c2c981401c1c12048651a086405000030381d0043d1015a000b003850f40007120141d0041001d900000e10700c402401c141800d55076226108603e10f4403024850589046080940d800a524824441d80c003000d025a1074107a0700d00407030078554880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 459942086 1250 459940836 459940883
    0xf01020d0c050a050a0803040623011202060c010c0305010f061b1e0f03020706111b091b07060516020a020a05010e010c0b0c0a0f0c110d02010c05060406140c0a0903 72
    0x104000c201e4051503003030702c01b03220f0094061800303180224810002c4001c20010700080c4c03061b036188112a0001100100515a95001404906030000d407a061800060030411401c642d9176900c204042590342c0300612440740040420300140900b805c0c20041c2a180c6035280000a5520350004c15913601001c500401403105415508040e60050b040502c800c0e0794600170b901c59141780a00000030f800701181654441d800100c0012044000d1501e00c825030414040c080101401851001100740000d02442100040c000400c1d000b8001c140c00030b118140006000c1041d0120303048a42158081402140980d544901002c00c0b51000d00304800c1000c003c10050342c4030410307810040c104138200c104000c400c00441c4014900d004d02662240c0001c1210201902d086818041c054112140035020510314107062031082c0040e030050506038081c0000d503550724500302041780c007190304c1d44d2502c105c1480d500448104c03e4104a000030410700380102118020400307550791002400820030709801200d14040304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 459943336 1250 459942086 459942103
    0x2040302040e010f0e0a0b01090c020102040503100b01030b060913091104020a0908160b031602010204030f110906012c150a0807090e10090905150a0f05060f01020d0c05 74
    0x161092050340900b8188500800c80491450351035414010b18004482010442c0c1106607841040014070340d003407900d100020421210194207541d0b0800000c111a5001c1100c107000c0900b02c2000300e640c822000004058507802c00c07505000701c0050168030816a5074020301821103600ca003001400c0c00742801c080441e1b482d550420b0303800c14400504515003580c810f03484800d0b5800c03101145c4541000446140407601640726801201105001040e0303010765003040700d548208544005410240c4940b92640c802d040380d01c0440e110308404021040c242031140906a0010f0700342480045010032450382840c2d8a6034548038000c2804544c42c0b62507568940c5e240c03040d04640328010584404030850041e10042095580b4070100308c40c0b8000140381000089028411a42c1c1c000c1d61401d0762410100c0d034041c04d1031040403039003400380c42045c21520b00f02c504501c0c41445054004112035150320071190440e0300160031103009188182007820140d80000c0d0940c0c4842651a0440c5c080513141402410221031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 459944586 1250 459943336 459943339
    0x905010b0405071d0f2b0804090c020f060105150a12060803090310050408070b15120c010e04110406080c1e03010e060603040f0308060d38072102040302 67
    0xd003001d03c6800355004145410504071501e180e02030800c203404101800f801115000c0c0d1000d0210402010001408101514501c08240c4c00e50481000e03500e445035500706030082640b6030b079603102c0ca403041a4100031500e05402c010019041d5541404007051012152803070b24400d01c40b0001e130151303806100304089070100550b03c404016a54032111072a0f00e030b130700c4904190322030f120350401c0100d4007540d40301c1e00d40159440344d049071402100d0354a020403813078010701a0829400848a450040e02c8002ea00c0d41c0c44080807000d86642040362001501c1d202011880034011890460490f61074004103007118195030060030800155501e01013681c05901c00c1050840084031006074500764140002c0242d4140d83e41000c9000c00340d9a8901070042d14003040b1005891103006003100404280034000007900210040c0c46410024500d0b15241da50502e541c0ca0b0800000c0c10798605c5501c3e41c2c06500c10703004a01d0030f8072501007504100f00b0081c00d071040c03000b0a00500f00942103107000b0900301c0d8102e400443c0d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 459945836 1250 459944586 459944591
    0x2030a021513080304030506070f0816030b03031605012003010b090f03030c0105062e0e1903030c050c04060e181509010213290c16120c081f0905010b04 67
    0x2164244244c40b90800c2c801141c10b0b200d48008113111031301480190800c0d00b290b955955103603a801051098840b4000301400900d071741c441c00b40003d92424401000d00c085404803004413007459140c42c81c21600249203200d10f801e4154074849120790701400b200c0c110b4600c0044191a4400c90001a00c841d400315141c550500c400103022001e0308042d04004d00c185c2c0103c481c100c08280f45901412407e05d00c03c4d4001d02220b446400e40d0140380114004103200d50050080f04600b981c4052140560120b50001e401161a00c18403108120041000c1040c180c8240c40074000149020038142a241024012400c00103100b0682c0f05090010032029801854010480e5240e080110016000394448124008071040d141e101207110f450708034015601c08040750355803846441c05102d10700d20760402d900d1401140900c0703035019052090f040303580c0098201006202c80148072403802145e0044158010103da030001018213165210349050030003145962038020686004914041d13006040c1c1e102e1441c1d1161 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 459947086 1250 459945836 459945839
    0x10060c0f060e0304180e0105010510031e110403050c0f0619020a0819080a0b03100c05070501062d05030d0809150f060109060314150607080304110a090902030a021513 73
    0x217205d20126440395107600c0401c0110300500201e801c0e124240182904541d0708540348400300d02c25481015000c60355606c41402880c2211000b080e59410032140c9248030000c1418070510034240400b48003030000322140d1520800c14008510b082c01428601d17142c0131004c0719070f03c807542d00a006001600d540818259600d648840d20440300c4882260600002032000e4001021001035118100b031300903004004000c4079400203c480054105003160781c0c1000014403084000172024043c1d88082e02e00c00b0b52021241c0310381c4401c151403000c90220700043d418807070303420030003900d005c85c0403000c110583c58402c080355503182d1034500d48030852002100e42d00403031080180760300c0c1c0782c0ca21a01404091f66203510b40f0b55108001c40079680840d20340b00300540e1001c089a8640f05001e1088080f00000d00640d0804d0305545580099070400c83d02583c8698140410400301d00d02024814082c00004004101032011500840d5840707141e11030080c000c1d0380545540032850030340303026078650045244c076011509 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 459948336 1250 459947086 459947099
    0x801022d1209030a08090a170306030c12010501051903080313021c121b0b010509090a0c030b04020f060c03090919092603090d1409040204061710060c0f060e0304 71
    0xe610044c1d840000684400124000c004003040c400322041c2c0005400303500400c400b540090651010744a542d05d403003510710340c603001d40341c074454108074602c40800011598908030038858400407ca880000d501c1000006100140908096030341107402c0b08048900080c25201080c03041580030024001040ca03101c80c5410481030744501f4039800c0302e0b5601e0340e080300c40d280490001c80d01c65840042040040000500460610350f4100390710118101c1103a01c642030944500c840000300c1c0e00142d881000341c004100950421031101c806802c0e00741c0d8034503e01000700341c0c41c0d51640150300b10540b18501500120310030001c0341d0a1180034102c2240104016004c51038003103070070781100451200d106060032405030f0b2240c802054900c41c55034000a03142c081e40904007142d9034115110071078000d460070300a14505440b80d1000d800508a69222400b0000355000410600342c030003000e20740c1003140b8000c184002e6074031101d800b60076640702d94940310b40d0390545003200c00381415070000c070218032012a000800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 459949586 1250 459948336 459948343
    0x7120909140a0c050c0709090812040510050601050a0807050a0e130902011101021306050c0a080d06080c09090c010c08070203010f092001091208190201060603060801022d1209 77
    0x1c2d00308a48104070709002101d0940d804d014402c80f104880e0001c83d8200041111b6400c50303c1032a218201031850240d80446500380110141c03003e40e0b455000e00100d01042455220b040d40060302402c102e1300f041041d1030700400250005040c441080004a00034000902642c118006010001c0079103002c0d8601e5440a4000d1060400585c0020032a52290340c5005043c400c03600c4000c60b030058420481e0418506941030360014041d40c000b4407402103c80d000c03540c0c0d140541102e20f4415800f240b998a032040e1246040c416511907803017070f582c044c06d018200030001404d189041081c00c255640302c0407424000094000c0003006034040d403c008290405250651000e0074991007442c2c400460380b00c0908030f40180000107004c5010580c2628107004560400c5044800035110741320b42c1d440c1420680e443c1d116008026070b80c1d000b5030345454083c898550180100310140032800002c506049104946422070b10141c0859910500074040c0c01001094203801c95408410300007601c242420500741042d13030b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 459950836 1250 459949586 459949591
    0x11b02030d0606110307020405091213140102011406130f110a09081b010e0d200a08010b0604032303071a060a08060a0c110a03020703050709020f0712090914 69
    0x41d00c624107180403e4180c092000e0340f1044040000071070826400b07609104c0201ba0207401800700e4071484400c0c2950380c00d5030b0010085103d00508204a01d40f400c0035010040d220940c4007415a418903800e00d4004030071800f02980500e08941c5411080110454800100240400340540500307002c00501134615042c000c0c40a20a281d81c2d00101da82d90f405417940f42d020360300000d000c2d1594840500b81540c8100304040001a009018259000300e41d0b42e0901c0d214640c00050340c01c4000b84940480c00e05d08007031100014000403009105513900302d00000c0c1e43e48602c7c00010841c8245280901010601c00122100d5850745800c4a41d180182e0070802443c4004884950491002e00e0000d440b5003058160b800445802c000202407546a002d88040a080582c0d83c85003044000340c0d900c004c020040016074445406500504045403d6090407414549107030004000d85004010500600d061041110079254100c080350b50340610154049074404920f9001c04501803c042d124001c0c1c4440d45051030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 459952086 1250 459950836 459950857
    0x20301050a12050307060209040f2c0610051324030507291b030a0e090a0b0f060a110717011808090d060b1002031306050316030e011b0203 61
    0x1500d10766a04a10100c809801d800404580045c00070900103085178002e007289a80040020a6081942250108a0b90315010070702000100c0c02099010401d00c1540000705203c0d81d0281485180c21011000030080720b1042c0307801190f0400103c01c2c090515030007070107010940c1c610111101003100c00400004400c0c0000d45580c000c01c0300c002042d600782c0e162444800484440400e001c0f030203020321061500540d404191001040426141904d800d0004203507046264840d50134281d154800e00481080052440b401903250554403c0107a48994800291440440d149a503900c4003040480e0744c40b09004201101d845612004030b0b0302c180070580d91800c100d03030200801503e200382c805c40c1e032011034842d0094080d190400c12448ad030308019141d6517926001d0740010440c10850300c01b19000c2e0018444000040c0c00202d50341810b840f81d000c1480040440e03107032941c25420105802c8880c42c600d0300240042c1640c5000715501d0801c02e41121740b11940c006650100100742840180d1264031002d10b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 459953336 1250 459952086 459952099
    0x30a02120607141903020f0d062706030f02040e28120f1d150301120203010506221a030316170408120310030b04080406020d110312061f0302030105 65
    0x10103001100390181c55803000f1502591a4044d00003105500030340c800e02e140054410304011028804080b07001c1d0000506003d112610030510070000d03680d0031000114038040d160308040e01080840c00030750f00303404a15011a00082e501c54643c0800349002550205a0001048004007141e080c80440e4801c0c10140a04c48905030140e02d144111241e40307400501c27a02069858108404040380381c40c0341041041c0141000d407604105ca11480c0320703038100b6407040001c0b00c9d0001e070140840c1420b020b2550403a4007900c01a1032010301e8104270804081442401404a81c0c5140c0034074040c4403401c400013091030240940360b460040040e1800f00c03034261f40094403072525050240e0700c0e00903594210f07800c41e10200302800c62055524036030280da5002601000c1c001c4404c1c81c0200c00310368840d2150b030141e841001ca860740d446c94100041c1c05c00c0c40c001960410700c820301c102000011008001c450000711010240c458590f241301c0000c601c80030110700083c811111440a4900903007550045040c0c070b0080314007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 459954586 1250 459953336 459953357
    0x7080109140601021c180e010f0b0c060a02070c2d0806070f0c0c05040c09062a0f050724020f0c0d03050d110a0507021009080304060c02030a02120607 66
    0x381c441820103a40d5280140c0c003010344002140400c5403595441082441c1c00c843c100d80c0fa4050366042c003d19044414456103000c01042404026030440c001041e07100801802d01c41d440c00201c1d10b44c80d00504469907035030001241c90400840010100207232030f11660001c0c07000c03540d010300d01c95031552001354130200740074020114095500007009803040c0c5141c2e8800e440020800380c00c0b10024245141124030b00e110340c0b400700352552140210640350f6610342d2441003442c50f0180081007040617080d003000007100f003542008101ca410b00120207175500300441c610403d4a52030042d2600700c0650200f40075403072500b4089401402d1150740500e50704203a08490084840c2800b81e500d5030f000b1725107140c1c003400704002000060701400240009051500c0001114110103d280c03c2c16445003403850006140018950110b2800b656080004d41e85441c0404015040c40321031ba03602d201c0d501500c0180155080320f8000c56500300300300f2503c1d42d03020701500326900200c44070311b5561406480a03400f2036040d0f1070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 459955836 1250 459954586 459954611
    0x402010e04060806060d0f060c0509030d0e100516060507031b080108030307030507110303011d16170604150801020a02120a0e0f0f0306041b210b100e07080109 70
    0x82e00c0e081d900f144010b0605900c030441000840700c400320049920800750503210003c00c81e00e108410101640c1e0301d45c550741300e048408050506040d02c2d070090a1103049043e820107902c40ca0340c051111001424840d580e413078010f420210390030054200404c0b440c20b0900708062070703505401192403c2d00f000d540c2c0d910b070b450103101034542038000d0140004c0740e4030510001d841346200750080b0381c10040b1404c0018003d40002400341c11980300740c01180c030310728901c2500b07541c2c8420201040d61060b11454120405030054400400d03101140e01007010003044130002c80c40580d00c3d0351081000904c103019404545584d084154007075040070f82c0300400342c080d4000c0c1e246000728400407207404128030703a640220b400551041200d580951480b01d0b400c1010b5401c0c3d02d455440801c070042c091070086500855000e00da810100340d80351a504842c8044e0b4044942c40211450300460042c40c5610031510718481e41c4204c10309100280661214040d2070101c0d0078400190341002107071b8103a0f03420f01d9090080900450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 459957086 1250 459955836 459955841
    0x50d110708150a050a1503141b0609130b0a03061a03030304020a09090303140f180c100305090307020307150201061a0904022a010b010e0405250c06140402010e04 71
    0x18020002006007000101c6503100380d8131042d031050708260001811068119401340c80b5201d50002c440712603040a03d840d064100704034401e048004102e941c0c1c20b460000313005c10414001e59602c58041d481d52207600004041c1354001234403131000a007001e59000d50701d090220240075a50b0f501c0c141500090094501402d002c822a4402c80e0040d2001510034509085c01d030013480c0d001e105034101641d5150065145803000e4a45000780711841070b40c0c850b41042e1480c0165031582021211440e4400e180c00045512255501e000c00002401c001030300340d0b10b4820031411807007140d03c02581030080c1080811020f405d000d0130481032140d580204401030b00d850000354a0300007081041c070715483c140001442840e0680040c550100c20b0740e0640c00c8100300e081400148908858800c0d031694684600040e5135900c03c84000d00c1040c03c550030312141c204444484417075032900610324440901840000da0640c09180c0100003607a0042082090041c00c0d4100480c1000545040340080c000c16110691480d250 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 459958336 1250 459957086 459957103
    0x61b0e040e070608240303130315140c070f0f030503040c0b0a050f0901050d0f0b0f0f0a030f0201170106030213060c0b0613140c04080c0a0e060d0f050d110708 70
    0xb134503510076649444011000030078610404182840001030314a00d0740c4c6041c005441c038205c000d105540190f0662406022504101d50580b6407189402840020062411055500800e1408500d5660703421810403d442402040000c0c010f1800314203000201940100110301c02d60048540e118070702c0d150141c46003c0c1c40340729855400240180080c0380e03081c158000a2a2f41c50050528903d400c1c00380400e402611942e498076035000c1e5440c06802e01c83e0410100400504500302e49500084c0d0242000407a507914a01026009000c00c0381c0c3c150859001e449109181580710041c1d80040d80d59041c020086c0d807216041d8400301094102c00901c507402001c1c1e40c90703d43d0b4880c1d604103960b502c1d441840414500141031520158440301c00c143c03469840030600d030042d200c3c40c2105907910300301240da42c034001da008a030354007400c0181020442d10140011a64001781cac200d40c01224841d85003804a01d0841261307018005014004556820b69005030f0425410142c040980300119510381c1c6958980302c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 459959586 1250 459958336 459958349
    0xf040230101401080c04020307051204050a02040b0402070f0f05030702061603020106060e0907030c02030f1818060d060203040201030914010905100608280b04050303190501051c061b0e040e07 84
    0x1201e4110345d031401c0d8000d036510074218a4900e0078602e0f9150b81e03000b0b80105513803e9403290040310041c02941482d001c2d1a4900400307031810351500282c1d503a801d10032114808060000700003119002d04025003407003103c1d0146d8000340000d071100840000086001d1b013616044001d0f40c0b80c4000094128010703030f030810000c5c8000b000d071403143c2d9503076409402510990b10701c5411400200721a40e680c140c042d010f028048820102800200c040c482070091030340701100440c0c102640041004141d541c1e0030162800380ba84101d000d078481d242d600c0140e02409000b1801800d2009041c000c0d403880700158000a0901d005070115a0903803d045240005c0701c4040c01001165040204003203161003036407558180b00e05882c0449400b000b05500e404400c884140d604441c0c2c3c2c1c000200f03000d080c4160710b0216040080142080001d94940342c00580500740c040c401c810009501c0c0703040380c10f1010f294807480900a40382022640c482c0984c500070550401340c8452480f0750300d89801c45000b0000010008191082c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 459960836 1250 459959586 459959593
    0xc01020a0f060911060d0906110c0a030c03020102161220061f0506030f0601230a140903070f65030601090e0f04023010140108 56
    0x2d455000140418120a0399503208000340680103898940080c14068031801000800081525100c000e50308d044c051603200c414244120f0030190400315400c041c3c6a414200086003513043d10303080c1d001e4050a2900d18500341c9180c203404c1400201d99040c44c2c0c2c61940da071050032182c0c1c11040101c020202d201100b4265020703100048200c00400c00c00e12055589004200405a07180c00007070140c1c4c800c0703403c03003800c480201c03d110350b030750b044461400303442c2d5044c00848007146500020b04090156600c044104405982c10b0711050440d641210034040000d01600d002503100c1c42d41c0542c02c2514401c1603200c4e85017081034029501c030800148850f5101c10320b2a400c0c09101400b183c02180043c080c524217030804003445640d0348030740f00e210100140d01007002d51a4540200050700502c655848400d961080b02c0401c09202c94404c4941d5000c0e60481c5d10880a10301c290102e1241c0c85c00d41040703101c800300c404400c0d00c61074000880e50140f6018480c24000580b01404540038101c0038862910541e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 459962086 1250 459960836 459960863
    0x1803081207050a320705010c09051804061a030a05010b030d05130e1803030106020c0307092a0e0414040b060607031d030a060c0f02060906011503090212010504030503090c01020a 78
    0x403000130010300d05000d02c100c4180514080521180b0755000d010200e406030754030601c03070384055080640e840040004a41c80310703046402c0349140013241401800102030546d01c0d0a0b4415440fa0003a41100000300602200e40480a5150460003404040303441842031283d03059040c0102c0c4180100d540d58228031020300139a030f1500c10310b150744a40242c60134040e0401d030b241c0d06e00d00d03201c05c002950007000c4550042c183d00c803c40c03090500b0100c0580110aa0342d0512a03480c030113924480c240d2039541041580d002810164402c11500c11218100300d83d802420039407060104402c20800718005c40c0a1414106a916641d0402c5840d11a40c5001008940d6410181700014228000c00e5090310001c0c040e0388081503950303034240444030b1280c0f9030b00100b580a0300081c032041e0304004555010040100401c540d50401c1350000f5021080c254201c10140c6078001c040844d214403480407400403124000384018281807401409c140c004580514281c440d103101c0034410341c0300060081405400c100d9801006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 459963336 1250 459962086 459962117
    0xb060a2003070609080414030303130308060f030105010f240806130b0402130305011a0121090512030601110601030b01090504291e060906010c031803081207050a 71
    0x1401880c880300c45400305004101c0450494026040b41d10b00c200c1c2c2d402d030351b582015065880c00300945011400783e403060081010002010949240d06a05800d140c2c5540c1d4540c0001040703c8900b4090a8243d4203100000460f2611007031110190b40c0c040e90f0707000c0c417a907400c40041018403d03042c0d4080081d400d040407403071030304003113950b00f0400c00690b90114009941401090130307a8410000d40c02e44a501c50030401c02d101c030a1150200c0f22841151350004801c0c2100000d0a0041312414030088100324850480d24081c0caa10250142e81d021058800d040c6071140c8103503243d04102c0303103607011448005011510b07081c0442d200c0c0c183d95000b55921011b900f001c01090091000810803540541d48aa03102200e4421580110050350741c04010001880c8c00440f000c4001c13040c0020f40814042c44c0305004031940e46200c40c1381d00200a10b4034815141880c281120300d1410b81348c0151600040140110921002070000d1006994407a070000341d1340c40e402c4040324144100407211000900000519064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 459964586 1250 459963336 459963377
    0x121006150507260705010903090510030911060a03020c0f1c09081b0a05091302010905030d0509060a09050a0605070209071d010e0a08070e150a15030b01140705060a0b060a 75
    0x40c202c3c034000290030b2030440d03501c060031141108015800303d14130f05c0041140d0b1420103140c0c0304055040c078043c4852120795845011402858810500c20070001c20415090340c402e40c1950348a1500c903080300e88000c000260b080c0c0781e80002581c0c121815030750590501d581e008201c84021264024001c28100d503118256222021003a0900d5074810045500081c80d995509182c1d13015140341185030040100314400507240030400c0c0d03c01402500103108400e54a90480f090303452034001591913594a4841003c00ca8102c52603811059015400740f0300824800d900c41c0c0070340350300c0d4800ea60092954a0341501501d1203d030702200842010f5944e804070b000c0354807641c3e00040106000d00056400b030b03122001c150400d12940c001980000420003000920443d00d02641c5048109444992074142002120213804956403501c4085c55181c882100745c5900c00c5030392024003002020156210110741c9072058031008207441e4010501e00f00094035005152280444500099a465628009a0b2143e00044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 459965836 1250 459964586 459964643
    0x90f05150906070f051201181a0102030403030c0c030609030c062301051009030804090b011b020a0608090c0901030b06030c01090501050316020f060a060e0714030411121006150507 79
    0x80007030900c214444106da0102490107012004040e0407556000c86c4030700200c0e43c00c1401030035000c07045846400240d03000300440b016607800d460500f28140150428025000d0140c0c00188480e150010070300c20b05038421010310006c2e1142405104000345044801c03d1001032905000804240b20010402450b0072a42e2034a00c2c48681402c005041d07494131810055001380e400058420b44904100352a0742e40611001c010b24403010400d0345488098000c0389942140307010720018031004502181605404104803259158010014a800c1da101d14003508140c8065031307084e02034030800c1800041d642c0210800c2d0700341d80d0180d441508555921610f002642c25803000c89040d4000c2da61016140141031084a01c5824003020205443c5d00c1d20301510341c41403005100f1000c210000741c10310510003805040b2604160840114003071200030500081e003c0f1442c0d4034100d40b5100b40122160b103961641c2000089641050920200d203182c810161031a2091080c018609000d1424403034806807800030040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 459967086 1250 459965836 459965867
    0x5070b0a0504020118030b070210020f16021201020711011707140f0705070b0307020d050c0709090c15030e0705010e010c02040e0a0c09051f0501021905030d090f0515090607 76
    0x200d80c030252409912400c1c0846c2c0080c0c0e1030307820100c100b060031601000000358000c40c5040851500d51201608000d500036108071030008842810b0a00640d079a40800301400501440219600c0c40c461030106d41c014007034185180411900001142c090a40400f514810142c50b11031401d1910b030b4400500069000c510100300c821801d11180780402c2c420440c5001524101d02d8039542c3c1d05092801918000c9000c0402c0104a4100680072065101140000032140794003c00301c2c1c00380007032038407215551203500415400340e03258862001d0650305070440c620b003807080c40555961540722001108c01d541c0c1d0103403041c081080e401844006040562024131250b1082082c0e031602501aa24200c2c1c480f05503200b40421030304c8000b0b208a0004910599a41d0f07080005210503492810001035205e942050004402c40e401c4000384050000a000b00c40d00c80c03400c4d1104100c1e000991a20001002840340c0a94061007460000c50f04081d50b03200c19805080384034010f020a40c1c030001c0031108116a109020b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 459968336 1250 459967086 459967097
    0x70f0303020c1509010f0506100c02010207031709120721020d020d050a050115060903080703171009110f040e1506030f0108010e06040c170c030a06140705070b0a05040201 75
    0x210640b00900c100002a40d544248150904140000e0b80c29035841c1c6c0304c503800c22403620301400942e541d4482c0d4403031191080e040982d0b07003820500041c0e051800560015000d103092156080d00078148100400004008840d00020000804465540c030052401080401035000307542d41d5091004c00c5003d214540b000300811105c1ca02caa01082e4016a04001203c40354010f0703c0d00c404101081c0140700c3c0d0308401c506640140b6141034002040f2080030700c80607121680004529051500c20824112404040a049042400c3c1400c062911610510588103202e241290060540c00c201d0308480c212400300308080d0900d070074031009544040b00549848040b0515103881040c83e16054003441c8190350400429001e5858140d0f01e80c00d44d45200c00040181c0c00c0102000002403403034610b0f00c04c3d1241460192030010003000c109140070041504554507102e801910420000150400a06102c104034031754580e488440051300c1a00410310b00404600360f080005450a00b158080c680c05401403600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 459969586 1250 459968336 459968347
    0x603020702150c03120109050f01030201030e03070c0e010f090b09060f0d17030a111c0b0a05030f06100803070503160c0306150e06010c08090405061206010906061d0303070f030302 79
    0x2196507011214a07800f5070400704001003c02d04d4076640034010101a1418000e0b864450081da0402c42e050000a040c9651440244035648040058911281c0d110840410050b103d44046010004c00d11070704a46803a603882c00324020b402409280c1c88070034094410b60950f11900100401c989030306000f01d4015072608849008103601212034044284114000b0b542ca0034404901401c5e1581408401d05003001045140300032464003015840c020303020480040d10b411200c001584810544c1d0019a2521520b025141d0383e02c008030300a07000d1220310340d00810940e6035440c0a52a40189007014016400920810300d842c594804071300da025211701c3d054070b00a902c80d5204800c07103410751300c0880603c0d019030043c045100100301d0346811200908000f00c240f1001d6035140d0551042018850280362642c012554030f40704c0c15492200d0a004200703440740da686450b450700080049109a0000955100c0b440707007804205c122094400710090050344c601030250700c4200d03042e03502803401c03420903508108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 459970836 1250 459969586 459969619
    0x1110705091e13051203091e030d06080c03010609090206030a05091603030f0806010201181403070b071707050301051302130317070c0504020c1e030c0304031103060a150603020702 79
    0x548522625140d2030501a583c0c2c41e080507482c041d10490500910141001404045500003ca000000031113800d904058914400380600318000d0303802c201a03860070583c0c0400c610340c020036401e4420b03000794002c1252517904d5040500b601c200b01c001a411100410200d9407084a80d0003007944000a03000b16212040981129814a6007951054001a402d0f00d28140030301e6200650075000300f07091009001000710380401005000964000400b405103440480f090303203800784180e130502e03504441102892300d08500094210400901091003a600c071600158401d8052803c0d28140c44014001819440700c071040c18000398088660302c240d0070500c240000000b14001c0680d495542d00310341d119210b0319140b0f020400d500042d040184103d00500034807051080c0003611406032040e09003040074107030040003e07604501c580c915080d541e000c0020044244803074012105c14083c0103030110340d040d1f940e1500c414125104215424071a111003d020440244a50058081c85000900204d41d5158050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 459972086 1250 459970836 459970891
    0xc031602010603170d050a27032307140102070b070c02180a0f0b0105070f081312050c092508150a090606082a0d0e06071d0111070509 59
    0x4101d80784d00200042c0408007903124014107410600405c428011441e1001400c845d40ba140e695038080501d482c0070040c00d0500c906d5120035084104100c4045445420a08280c00d0f440800d0640740801101c403841c10000741482111460345d0001e039441e4207074444060880e0440c01e03034502a68070414480c21184014900c40303a840c0105821000011107148200c00103054440854041c0e05110040c050399000c510100070003644c1e240e100c5041980d565144801703041c10405c6070401004e11400e08046001c118001800c0c0a440314120340c40300650780c0c3d0301c5a50300b00035100300e5088921984003407940752030317802103140507040382c0f000c0c0c1e41081803400c11012410109290f40400901500e41004120341a000b022454000f5040040c0703440e0103554038a03e101d8404c124036502c1041800049480c1111800d03400707180d601003200152074060418220091101c8481008520940080f480b170b960158081c04aa500c103e0300d8002820105103040c1c104442c0383d5009100c407800c848118181a851103101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 459973336 1250 459972086 459972113
    0x203040602030a0311073f091e08060a020702040b0604053d200c01050f090a1502100b0f0f040f092109050d03050906130b0301060e010e06030c031602010603 69
    0x34102901c2040041070a01d00c0341c2c0780482032811441d47d0002c603540590f0710204020558821400855407107800111501110b410781c1d00200040c0240d406100801c01550000e02019000701c03001c1c00324148940c1084400c0c452889819444211525a44a00c101038039150012036100c500f4000c00101000c002003617081d600c1c1142c0001680c407490020b4402100b4110140c1d00c2c2480c004121052503000080d00c144941c1d01c07660015100414004003540d80c070241e2202401040c00e107440c1d03220680e00007a50341e410b08101c034111a81402c00d100d01c01d08003c000306190b040c00500768528540301e40140700080c2060b10300c00c0201c644406694001c200f134180b100601d0031140404d40080300c26404003d205c4861074104520a1b80e04043c0d00e00401e9004040e1405070740d08980c103d5540c48140b01745143c080c0a82d0001d0300b42040840000b030409e40210b034403080c811003030b00d40b07104129558040129502c802c940510742c91034148003046456a1880f507400800c0111b000002e030107500e07500c6040030204c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 459974586 1250 459973336 459973373
    0x4060905150112051917030417070c060e01020c100c0512071113020708040611160e090123010902071505040b011a030403020d12140a0506010f0203040602030a031107 73
    0x101d0b500f082008010070046078110345045010124903120340c0c94110139030196000c503800b040e02001040910140c16840000b0748100e845d91503480680303103420500f102c4144a20b0001c241d094110b6001035001003050002040000c01082104c01c8440c001d5072400e210810075600e5200380040181300d98102401080003a000300c9903101005466410880150340c59a04c0701c8040703005001ca0000540c415058505640030350034240140c0520f80001e42c603040702030451420194503c03034001051031018407018003409803500207200012100485c2280c5042d00d51010599568110040082c0042036002d00415482880c100004031491102d80c0190365081d50140c65090044d00104580d446a9040030100418400a0ba0543c6042d0710003035100e0014a02280c14007003244840e4a0000017503119601c00350a22107400518188284441c1c010300c01140c10b903020600da500000c0010b400001a03a0840700154000c0d0700c0c003041100c046000c0c1c24101c0b0b0300d50100c64180851800a010700b804025060103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 459975836 1250 459974586 459974609
    0xd06050d11040c05040e06060307140315150c030409020c0106030203030a030509010c03060521030c0307030c290a0f0603020a080d0e0a060c0b220f05060c0909040609051501 76
    0x70300c5080200f19100884824140602000308000e82c807443c3c1c0780070b83d101d213044480a0703c9a5510340c2c140e03244109070303a4a0348907200002c1049900b05e46920007030030310301055401100410081131500350700d106030b51094085600501081000840d0f90300100301c0f5040307200001c00c44d90703507aa0101e403850700502d441002207a21441008034090382482a1038842803a49003d116280c0780c04041860003904100c03032102ca520703400044044010800448202180540889983c0c80f060b080040c500500c144003210102541c4405202c2003090513064404100e10780f08506482d1102602140209004030780d19410030380301c15000003d41c1c1c89103c0400141800c1002d051103286021000f0b00c8101401c2200e481408440d40902103c1e90000d04d6408055110400083c5501c40321410311400d075140b00d0a5440346006c0028904001207414491082032042d42182c0c6580c075902070400546c040c1028194100380c050001801058081d0031030942c160050007922142c1c0803111951070203d000340c211000c4d034107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 459977086 1250 459975836 459975863
    0xd0819030b030c090a200c0f030f09090916080304030b060d0305041e091109091f0515090d080405010f0906020d0c0f0b070f020c040e030d09150203090a11040b030607050d06050d 78
    0x1040c423a442552210703001543c50b01b00c0c00e1a800f401070084400c10341c068240e00001411070241004400c001d09946001e800c50300c3d541d100c40b295a80d00501003124040085000315515040113200c000503542d00d521001e0820341000c101c0f85402e01801d580f05180102202c0004840002344184020001007003030090f9039440c20001c1c07281450b00a820130240d000b071030040e04022017810308000141d9000300c6032000c0006160000035401c0c007a40340480d6004059605910402c135400f001001101d000b17032248200e0401030700003981c040c90305110b0000542c02201000f42c10301c2c818000244101e104032908003040801d600c6000c1041402c94100c004964100141030846404000415200804882c20303c400c1015040143d100c0c028800508010b80d241e0b034100b401c10182085541d0784a41400045480e8940040403654a026980040e40d020304120800c075100e0805028030410104007a008121646903080112039136800b0000d03a501c41030340c0c0c3c1c0d0085031903a0f071004240f03178081c0034005880042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 459978336 1250 459977086 459977107
    0x705041707230306180a080f0309011107120c03170703050106090b0a1d0103020c060a05040213021204030c080904110306190f140a050d0819030b030c090a20 69
    0x2c1c020114026101020914001200c1da0f00094a0354441c07084400e45442e08001e401d05441c2c071070030041c010031200d408140720004d0505400610f2044423150001d20050079584e500100c40d1041e402d0140420051188400c48107010fa05462407a520a00d04101c0d8038840064000d842c400075502440020b444400400400d070703002d400100039088041b202c600e02304845101800701401d407080d089a4038042c0c0744050b056806039060303500e0a18050700f0382c0c080e0300d0507800c044020300e0100d50072485009881c81005035014280700fa905006542042c01c84c0b1602c030740c2c80035035540601c88803c441c28507040013210200d41380e0b8041c042c2d00300c006400c0341d0703124280300d0704112180c0f91144001c032440d6102001045003100240d44a41106d2300392081d40e444403000300118003204455008036400c84841c07074112040004c1207008200900c1001c1c440b1510301c0074100100c098800d030b0400d544e80740e40004400c0415251141d0003d411442c4040000791100c40070504000c0c40c0701440364540501008606070150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 459979586 1250 459978336 459978359
    0x18090a09050d0302090102210f1c1512020904020a08070f03062a0507080c03270a0b030a0f0b030607110d1119031b0813050405010f0902030705041707 66
    0x10540c5400e0a5041c0700172140001c0d43e03003070f00140702c03a5011048006210b041011600f21f90b40010341c01045940c030740f040c400d000184900c5200040c85180784c00a055560f81c05524100d094030400303114050303045810703020000914409403099a120308582c00000700007004000300d20041210034111406039103542442c1c0212601ca041071444445a15161041136a21403c079450010090910a403210480e08000e00140180b44c200e50041c4400102620302e24280004540301c011240340106996101d1000e02c10302003030318899140c075000700780023040051669030054000c081e050700c40029000ea41a00007807400200381d030070a0203e41c0604c40d106200c0b4003405121590002804d140032580010a060340d0b0303034000c501031901c051030303803c0648007014450719054242c0e0281d18640c4503000610300b059180c0c0e60081a034441182546c4200144e1410680a142d040750241c030261080c803494084180c000c0d500040c000403c100041002042c410392006450103070b060349800802030b1609102030f4540d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 459980836 1250 459979586 459979603
    0x9062f010c141206221505150738010308040f0503150105010c080403021e040501060e06030406020c0f3304050c010e0a0b070302010e060106030504030c0818090a0905 73
    0xb2003103010800d1440d62585500c160350042c4041e00d002c1d2810040c480e0040c180c0c040301030443c05450404120850030740e148080350045d102c086401d003440b84d4903414002810700c20007000400b05000c0c050010107c80207002c110b6542c50010640383c0c0c0c00c002c40c2030036802081c001d0b00101c402020103e130074003440c2d084a2840d07020f000c0580042561140300070100d0300c4181d051050320b040014116220080240310002e640007542d010301030740d024801c00d0303c03161104c81004030b82c40c0c000e03031410300005030242c0300c0d40610102c0c0002410700ca245403500d44640002e91320068020ac190321911001070400c403003c0001d84c00220003880384640c006c0c004401c1c0c9010040c1a04604000c030026004d120101d2004901c81144101c2400c100040c106d414021400c1c0c003005a0100880c80710110319803007071640641210468003000c600741e130101c0e82c0f5524254204e4609850190005103425448800070f040d0740000c004080310942c030407101e040501c000401c0c00e0000c0300d0042c1c0c115100c0044804204c1c0810002c00d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 459982086 1250 459980836 459980867
    0x40f0b091309031407030f020606030610060c06111204110f0a0603020d0b06041502060f040f081803100e1b150a0c0228120309062f010c 60
    0x280341403040000211007a8400111900341c82c2d44415030310405000700401c849680300c440c403042d240c4495043c041c2c0804005241c080141c02503400050b1980b0f00442c80920807240c1c2140301c2502030400d10111012100104103c40d01039480c03c01c41c1c07050580d0780262943c0c45061408414514151403c4210318200d034544a020302e00ca8484011251349403500981510313220f14005840b0014052644003804012000c640c002500180218100411a081880941d05034080303900d184ca4000503030910313507800c440240036210301554030400140454000c03d444440d80b407104d0040100c110000382802c054041282e9015964055005e104000b03009031462504000d400208001d800404a0640d80002e09200000b000000b1228072650003034410b1480290060b01e94001203a0710680c841d440340c0041e015070701440c11001d000802100f40b04040c280f240c0c0c550349469100d840c12400fa599103030b00120420140802c0854058004038101c445203120200130004600c2100e500e202500ba880c0a00029 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 459983336 1250 459982086 459982109
    0x17040803040b071e050120040503030d051305060f010314010b10030c030618020306180c07030507031106100603050901060311091b0c010b01020d08150f01021011040f 73
    0x420540602009880882e954500000c0da20341151030203404c04000c0380280030110000408200502005521100440700c03902d8030304c40040c0044169400c1c07400380303120b01c075803542c808c02c1207089820240d00800c0c0c0019154040c499121600d40d07816040007002c803080408102c1c0c035401081801050000b42c1d4101d40820000c02c000000705d00801e40c51225060032074140350f100c1400d42e82151095114000a1150342880f0310400300e4640b0020283d030044e24031a1182c101e01e88281c04e95a40c032040d280c0654020890180761802540c1c1c10b42d4580c022040950a211301c071008401c00090620501c2e202c1e00c06e200c09800c01d04c2c282b1402904894003d0034480080c0e01d055000c4c80003840034005070507107001c105c80c400015510124001810490044030508070348001c2810020306605401c00350042000f6000c6e55400d1114003006c031010781c0704030303056060350b0480d07250a0454207080901c0c4400780c5041c41500e203d24124117491b01901d0b01c03a014038a880a00003820044120300b28071110140440c140038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 459984586 1250 459983336 459983339
    0x10b04050103030804030f02250518010605161b030f02010206180309150c030a0f020d260a14180c1c120309062a0e101b06020301030b041704 62
    0x104400704c010001000c0c4820203408202c2c960081110703072802ea2400302541c600c2c05840c141d032000c11202e403207098050081085100001e0740800d880505840480da0b5913818640045030603071510650403015100070701000801a00c680b041222903014502a400f07200781810140700080c41c2c840700030180c1510702c0000d0f8481c00060f43c040112003100c02d040300e4034014020034240e808054800e01203591858840080d0f0b010000d900209852a40c02b1140c00b0f45886011101c42a2098142c10030b92401c00036140010a0301c003041c020305d050b040680e69100281c9141d400d03081c409010b105495412400c0c1001385040760310f240c1000210304086060b15a5203405209110300144c0250018004100764800c0038640c500714843d1740f00b45800b039000082805100824801c00848505902031a11203442c00c0d080b003403078240960304000c80030b400500754044041c1d1031390044440a1109400346c840c0340b40741618001207529400514040c50090b890f500f4141000c0c6841515000ca803025451001d405000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 459985836 1250 459984586 459984593
    0x6070518042007020a170c0307090e0303240a0311120a120f0c0f0b010608090c030d05030a0b0d0605370c05070b070206180106050d0809041b02010905010b04050103 72
    0x48442c00d03091900da0007a00c030410341c40041c04100e503541000044030208440300e0f1902400003007a0340c04c01d005406542c2060389800c1e030681541c04e04c00088007141d0080000c554400100c01c501030f61340024000c02c0812200d142d00041281e002e03540169401d0744990200390710351602d040c0c980c0d00c981b0450018030702c1084950310f1404035103d00407200d043c88481310198002d42c0c003581406a8260703100c030510701c13108040d14007608071150a000c0c65001401c6040065508280000d4a40020000a00900030310004100c100c8140d8001071404103001d485085006841c0c50300740c00a440180300301e401240f030f41340c08603610800001800b0080315a2118600c18084103240607040c0b6a10f01d51520f0211b2449450729058400d48100e2070010103c9200a04010802da13010800c14082d444106018103051014151513080c0e80c1a030213410352103602c00c5c10500004260000600e0340d40c401030004144e680d061088a25030010011030800035075118000d15081200030b10440441038011501044554110b44 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 459987086 1250 459985836 459985871
    0x60602030c0615030a050307031806080f0609040311013602060f030c1605060a060e190b0a0803191205041101031e0c03090b06060406050a0f050c0607051804 69
    0x801c1520b114070782a030301d8010f6480500072044015080000c0341da03208007a00d4020500740750f40007112107040c0c90340d402155040c46445020b019000100400c142900d4420030404250b0f005001181404810f16030040d4000b003e0148101c1e880070725001102150040b036411100036030711030030400c4042c0a002d4100040e80c0300c0d4140c444035108552281d4481d81c40e14a4414207203e49100c2c014001c01040032071081002c00620640300b8030039a4014052642c0d02c42000c044040261010b00c20800d060a002d50b5541e490f6004800c481d000908600041e40d40304440c41c1107074000c070302c283c42e5040b2510386140c1850708002090804020f610080186151540f6441d6554201410407410551a084a02031004880c8001c005070b800a2a0400400702c00c11340160042503001011500e516030717800010150326041d402e0320700b2202903490f01440c0c41c00403503049540c910b40c80310100900c40140045089100d040280510515a946450340c2d14070b00001287c6400e4512050f0b18800c030300f094045407a4403940e2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 459988336 1250 459987086 459987091
    0x14010815060412110d14010b01020f0303070c020a0509101508040312020f090405150406051e1507050f01020315040b0a03022b050705151e030c1c0f060602030c06 71
    0x25642c440f0f048003454001d10b640e40c24201c1da0f0340285d04c00c1415041c40051003505030090300c9007000300151000d00e00103a80355800ba2840e40140e0f0420300006030701500842881d18134603c010b00ca50f008a440e40d000074151013003907030203882103070b049072003840503802c6802140c3c003803202030901201a02d03140d40d009254049504590218513000705081c000c0c01142e00548244c404024030600242c0351041c40503400c003040c4100184030700d080440c00100380c101090400001004003c8006800ea05042030142a150310b59000c03c60040c108020800f156003480b410354400d100030009a960300308078043e2800406c0c01d01c881d078407851401c480400701ea9105144101120f0303050710000009d60940401000c030b02019500d9023030740241842e5480800c08041810f400b580d800311303404441d02c08101104240c60184400714114110250034240f80c90282c0e401540c3d220802c00c11541c079240f5010760440c01d003d003040401c6141a142c030b0500c600000c00e401150003900c22480114281400514010307a641c802 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 459989586 1250 459988336 459988349
    0x5090907090c050904051602060a0213030210140c0c010201051015030b011e020109052b08090c0409030c1202010c020717070e09070f0e040b010e0619140108150604 72
    0x29801810b0000c0d0040c015910324100091007000307607142c24404c2840c0c45d22107107580c10040c09000c00140d07401e0024800d984d6961050101c1d2100d1904550078009817440f00d03001c0200380310528141c0c00b0381c22849402491900208409050303104100c40000e0300f5143c000d0038140c00e0081203a01446070060b88118040c000d401131030b002c1030103180d401c0140c40080005003e200d090324900c514030b8100b901500301a80c220321400844003000d0315681841016250840303040f00203c07480d075603150380f50310800c0c032076401c1941001582c8180c0380440020301100c1801104902144050400605204c0401c4007072008620f40e0000f03001981546000946450040c0900800450b94060320750407103004000b00806003819440000540c01d240c4500c0d50351350601d120304440c1c4030b007220011440c0043c4004e9107008690066103c1d01603400c0004101c62400c1c02001c03140c001215144018480c07005407580c1c4010b000b1003460215542c1290001000250010030340080c070000300c0d2000580d6181c45049400301c440703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 459990836 1250 459989586 459989591
    0xf14010f081026071203091707120b070e010f0801120f080a1e021b010f03020d0617010c03180305030402130608010b13090203070303050904020c0102041e0509090709 73
    0x1602a1040e0b586101070f00002000b002c444103890b05000b48004801e004481c2104035040e5980e101440c409030504490001e0006550b400c08001c4003a0248a400701700441ea4156218180c403161518034240d02d018040e104140b12301d09121600f5003184940c080b500085c41c00c06954501480c0c0036090300010310860602c4984078036003e080c4000e030700300304541c01d500400356a40c600362035000600d14050107015007040f03007260101a0000f4000035103d61540851a1038400c0203003d000150f0711004121403401c2415020409411840214402d44010700304240c91601818400c1280d9400c50724911160b2041c14503080c00482c0281c0380c030440311030b032560618050b6600e075200c0c80842d003111b041014901c00241003134070210307034000c0641005403074070015240c0e182c4030304400218109071941401d0194054004141c00c0c00801d110308020510840e000d040545000c0d6460451402c80e40203900070427003541400080c1d80006200070b441001400102c0f0118110304011454a49503001c1e80300c0c201040d503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 459992086 1250 459990836 459990841
    0x3051e0c0a0201140a0501080f1908030a0605060a02100b0a08060c16051e150103030509040e030412060b130b010503192c1c0c11060d02130f14010f08 66
    0x910075000f1103140c5404091201003801c05c1410100504030078010f07c8014056214480710107500080c120003502d846c46c01c0001f00402d20740360300e40c0d00d03840500361942c4035407210310105070340d101e05000b01072a0303140303a00825090307603001002012a20721000591003800309110070415040001203a503001800000710503035450300550700120030840560300420501030540e68500c9502c96041c07091500c207018043e0740c50b0701c548800d4403882e20030034000180414028410308516052a5004107240b0103032104807442c0c207441d421058922030915004445030b030385554600007507040c00031501c07008400352001401015410b00003e0020b0200404802c2545c00007070000300c540c10345030480170600580c0008070803000d8a500810030314591045070400300e8401d40300c140300600d0030a40d551048050315610300c0717001005540c0d4035400249076504981d0084003400302e00c03000c00303152004010801989441c0d103621440c100c91980d00c3d45a6130700c052141c143c081b00c502c50700d9800010709034002c209480c04075080e6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 459993336 1250 459992086 459992107
    0x607031103040518150303091305090709050901271e1a011d100e0114040621050708010c02071403100c050a030e01060b0406030507021c020307020103051e0c 69
    0x500841e48203a0b4440054a2843c84003800c00f40c0580c045c40d0811400c0c0c9400920300700703150740e0b40300320404a500221150891007200250754000ca4000030f5180075a204603070344107040803d840081d140c42d20b15955510102c5d4030b025440441c0b080e034000b80c21101a0354503040e11145d1501441d000b0800301885030014140401c808500b0b4908031410718030300300c2065611140f5400c40c504e405180711040440c0e000224011216480810080312601d0300000f58581c249541107440225121205400c1a1903a0000c1040544100c4602020f03042d0000500940c071203040841c54840d03507502100303659140030b08804400344c3c0456200305440e81c2042d580300c8080401d022a1528a40ea40701d040c0403458080c0404446500400a00c40c95400ea503052000425120185003280c155200b070035002e000c2000704004050207504607561007005801541d001511005804a00c1801c201d032400040e04000341d04811981c00d403150940142ca41c1340403e0b00004528518400c603400608941c0300510b0104104448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 459994586 1250 459993336 459993343
    0x109230307090e030d0b041a1c020303070506071b030e1c0503120402090c09030a06050c0909010f090f060b03060409110d03090311030d02030a0f030603171308030906070311 76
    0x7403040b1941080340540b40c00d0900e449410002c1040107050403c5403e2040380381c2030040f60141c03a08189a000035052070170070850610f00c070866400454030b003441860090b9800b44003038234405010380080c01880c038011900030102c81d0420039040044c2011740d01400403036842a024041c200046e507803070428016040d040044c042103403030024568070001561040c000c5000c1d041c58002d070b01c01e43d6580340c240c4a00c4038002e481e0148a21841d01580095850f08c08500309810032038020142e1015207260100c400c0204491074801d0704520b240c1003440f0000c03c04024180b09810a022813000c04118240c1840d03040b8072a4070003c0c1c5001c0c8600d490f80e41a200340409440b10002c480c400419540d940a0b0500e0064a0b4400700c3c070007070741d510741d5800d440403580c1404a03007465000c401c0e50180d442c0c000c5010054035080e80d040303054400c15a6507403021002500c2080303013103001402c8408944d1a5408840d4445140302c090308a60720603001400b244000303441d10710a541c9040d81c0f6040001c000c402e0f1422a515 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 459995836 1250 459994586 459994589
    0x2031603050d020a0e01020f030a14070206070f0309180204030f02190b0a02100e1209120f010501060302032a0405040e0102190c030f02010b0a03082a0303150109230307 74
    0x40061000449150864005648138801310302a001e5070723050b040303c4113450f07224082c2402e06070101d07142012100c03100701102c0043c5186032004045a00780910380c0c5603c00e403507200c080304070041480d5003028411f040411180350399142070b11034103510f0581941d079401a41c841d082070090096001d243c6810340114440a00000390503040c010038dca442c16203c00940e10700c0c00300c0c10709242d94601b10740c280c042d01c400700b0455076140700030140c0c17440c003503160b02070000f0300d501a00c04625601411418400d210000c0c02424000c1500d6500940c40742030000349400054503005244000502d588407008450310401c0c00d84003211021600043c5408180e8031180c060b12404400c07080410400f0028034070f19030064440c6e90024001c0c0da8841034030072a16000c0c2c2c222003004440907030040c0d00100400c0041c110ba002803910b4400c4d5442110340b00803d000c85144c185085c2c00d87d00d0341d50400303c00c1240309180b102b8a402d034103901b4a84818628030f0004000000d107103204ad00d00038640304000588198404014000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 459997086 1250 459995836 459995857
    0xb0a0207080f03065103150d140a2306040308060307080a050f0708030c1f180c1802120a0203041419120309020609010804020f04061d0105030d0203160305 68
    0x90302002c0102d92240f0340b030908418852001240005c400c1e405140004a60f00c0411592000d00e55140c51045441402c080f644455222070109003240c00554854625407001d07100300e006004400c6549807003140020800c61510102c05c01202c3d00045d0400001c10b0b42d040350700f505007059940c9506010904001141d0003040d154800c071ba5401040100004800e076000b007141c0705071f0754025200c51203203880e84940401107496034400200220742c1c25041c01003224844a220380040d042c109180ca441540d24000001d503070b86c00c5005000c000b06901c141d034904102e50350850440c50180110030818800201030900c6400c945d0200005007000020f03a018481c2e0040b040032204986c0c004510380f114125807810071a0700580700e00481e03032840c0c02400380c5040264000e00840c2810f800314011624100001d00c1680d102c0341440c202c42941d00e6520424001e05244810544802c00192a00d03c51b180107900c40350080c0e000510303ea01e0f0070360100956003035210046800c03103070a02d2414201d031640034120184 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 459998336 1250 459997086 459997129
    0x1202060909221119050306070e0a0905070503090709110703110c040509160909120507060f240b03060a1206061e061b02010801151116030b0a0207080f0306 68
    0x80140140000d8483d81c4400840f00701c4e06403442c00c02420034902d140d103e82501035000e000030504060090050a0044002030990a070881d910762044064840a480603400300c5d800006019200106204a1014000c401024440007002303100c020407501c40d0720406002c01641e51905002110244011750b4010030081007480181411070700707151560341000c003105400302c03090000903d000883c000d11000c95045034a00798800c544190036509607200d02c0c4110b5485503203900d00300102d0392502c118a4410361011051850b6400e01341040c0ca480c4940d000301711000b10610800901d135681c100280295610a043d400e403141185c075002d4003506143d00420344400100f8001090703031a0310f40c03814088996039980c003440346042848100300b1140d18030700a40000d08542c01400b07092000e070000b0303120306180d1904281c05100703040c0d0503041910402070320f05132540303030a010028403154481e6140c0000403104218a4000ca0381d40f609910700c1890940310003514080300203000c55840040e081400b00c44165075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 459999586 1250 459998336 459998401
    0x30a0e0102010f06260d02030a050306060d0615021501050a03030e01050c060f100b03070c060e0f0304030602040914011202040b1804060b01031803020606191508010f1202060909 78
    0x1450b4101c5c1641c401c000b41100e0054020000c0305000881c184009002d801031486d1407224903040312143d200410013a0818020010f600e15100310344500402001d40907409041c05160f440004c0c201035401c0e04640d004000800140720950b00e50703800320b0881c0c0d418140608400e1405005070350b5401640d003010348078000d02c0c04001111100300009840351000d5035240003a00d4031004080300d6804103031580740c005100c070030042c070000d4010383c041c4e00610800700450781015084003065280d0780c03190b08201c51613500481d0403c0400300c90b015098040040110000056050030000b0b03e601c061950040e207e983c5500c17440c492a1141000349034000701d500c0c00da840e00d14180c00d0240103019181050390000c0d2800ca03609605140e200c440e03400c2e169050303020308090b0700d90104000307842071103002203005003d0003000014421821042d00300c0100c1e098490180030362421461500040c0c00d680441c08890725020270b00010390341c10045442c28002160907158030344503290103c05805510f2100300c1e98201c44080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 460000836 1250 459999586 459999599
    0x1303020f070803030115050c0627030408150601090806072303071e020c0d20060307080f0c03310c0815060a08120304060b09010e011401080702030a0e0102010f06 71
    0x2141030f0307116440c4142c02e04840820480d80c604c07944035a01202c3d080900815114038002c4c5060081c0c0c0007120004005462b884c0400b42964840e034011150341d484611400d18000301a5000c950103902400c0940c0c101d460001c41588400004141e20100950780d8840070707160101c0542c3c05d2004680310101a01e030700e40480083e0010300c9541c800f80c030b01da40407807982c120b444c4005000140348401404c05540d60030360b0341d24910302115013200541499404000120300341c5520001d903103d03201990700c4500d2801c0103006900d1380c2c0c40180c05100c034144200b003000710810004a90203507065031416001c5680d088104803000c8017941f050010010300d640e4000107060740c0c00040780000e03080465044110381d2071303041c00c0100600652007400800d8000500d54042412960040c66015000d020b000c0b4540d41250009052a6402d800400b06406403600602454880440b00400c8075800c0c20441071074240014003945e64045d03c940601000550041050031fa4404c0d0448801c61030071460a100b019241c84 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 460002086 1250 460000836 460000843
    0x1012021e0d0e01060b0f090a030f0c0e01150c022b0c091a0307090c0507080301030c0f0b0a0e09060a0b1b060603031c09110315070f09030201081303020f0708 69
    0x10010640e02d050103001c500c503a5061040d00200d0700320f19400d9241c44001612030115410584200d584203020341030001c00704415158103030846d8032907490f50262900304001214440c1c0d0682003814040701492180c10003980208981840b1074048600300b0000c8010040748500400803004e9048129200188030100000000380b40161181551b09200c600c6c025002c4528000c0301c0b804060f8141e102a0003040040c9055002548500c21f5103070652414a03652150746481e403082e4000c80e0840f400d400d041000c0320781214440e000d0100249494506030b020305004000065074020a80329511210200c5c156503140c0146c07400916003102c44a0b00c0e041c4092080024555601c0310b80081d024540024103140381c003000311005040b211459001e00c240020a031001030501c010112007004810004680c0c41d50100007540b9000c001624480702890000c0c1c00802509c2107560080a1003403030b8809100607a0450011075211444142e10441029541012840d00c1c41102407500c00707000f07210300451401b0380032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 460003336 1250 460002086 460002097
    0x513050d050a060b030f120c0f1c0206010b091e01110f01020d0b0901080d050a02010f02070b100b030114060304022e08070503010315050414101413021012021e 70
    0x71041041144d15280905440d02c259402004682e000030307024000768038040c0c4c05400c0d00320018089a50341d00b030801e2202e2816100d0080c41040c95030204c000859140d04001817800741644006045c18074070824081000b11401d41c00f4428242d01820000030350740d1189003d14800d1618800311140104110101c60007548864000305d003043c1041a100d03840e00b803070420380e41210341074401406080e000c04d404603081e0308040074500840d500c60100450420081c0094603199009505400c101c0c145044d54540e040d4076944900d60b2207900303200402076064030a003d11140002034440507070300d95580c80050b10110000400c0021041c90100386049500d0710b171005589140c41e03403610b07144c1d521591400c0d1041d00003440000c081c01da40c00c9000007072241542004d03801c68402e044010801034202e20250800350127101e07012845079104031441440c940114456004541070103c800003a41540105000c0501521052f09014010306000e068030160390441d50940d24480740044004a500480045a4080c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 460004586 1250 460003336 460003343
    0x50409261b01050f070804050114010b0315010e01020c10031104030f1205030c0423210c012a02210304060e300f1002070512190513050d050a 62
    0xe24808045001481150b01135403500034502070590300d060007200eaa0000800496095407600440901054400c04050103803403a494025100e02c1c14248c00183d0108960344141003020360038be01c811a9802040c0381e0141541543c0080100420042c20b0380a0a400e42d8961000c8400240c0002400b094481c0030b25407c0c80388141007030001c0341e070500f00c400f40001d51700c2c81107020042008001e802400ba002e100080010484260b52240d940c3c000f646034100c07410310346c0048504c505c9518000c2814080c5030400340003428a070a007a0345807444030541c00c0d403100c0380c81c0602a81e580158259a203004152040f4510000d10042c0c60307654014241d02e81d0891f20404010441c124512803c2e86001c01030190040120765410303401250104c00e00c0c031801110b2100750180e004540800190781002c0c0001c50380c0c042c0b60280507a5404851030400d240a0b0480d500c0d00300c200781403080355240c10720000480300c1d255482c940503841d000003050010258200d988030308d0313100c10078021000800c1004504100340c10b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 460005836 1250 460004586 460004617
    0x2c0a0b06030d0806060d240302030705030a0f0b130503070303021903060b03070c08090303070c0305061b0d150512100608030a0516060e070605030f0c0a05030105040926 74
    0x110038041c1603403039120709030b404003043d04000083e000b402d0039405406c03220840d440210350100d03401c2d5000c1c9028011002c594851070982d4050082d0306003000070b00c0c0141b0095000b03007504070040e00d07460604851400000c0c85030380200b002c80c44011901306030710084c03034000054941d130700418600a4025030003032401c40c02c595810701403014018000c0c821241221400b5040c10328545e1640750841d015a5520001c80e80d00c0c005022988098408101400e0b00511400c191944a421400e01034500303140100081c88011a220301000f00c2c021150944004001400020620128895560a00b00030540009811400b0054910380481c2c000880c03400030300d030300300080013501d0329030f01607031740300d1044034144800305070f0800507200e100002c51aa85660ba004074000111400070110003802d11903198001c10010f0b1000c000d2002c68481e40141e00c1d0401e20000c481e524003000d410000d0041d02051040718031407607480c8111807d1001411888809614198001072228521689883c56800410450202a2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 460007086 1250 460005836 460005841
    0xa06050703020c0927070f08011a03010209031504050c0301140105010e0406060212070602040b0406021c020303040b0c0f0d15060306320a0807030821040c03062c0a0b 73
    0x2407414041d805603e0941007440c4052007480741d400d040c01d1117013001105204604000910703e40680c0d0030b41c0070307000882c00410240c070781e001e03c40c00c070320780c0d10301e1080c1709910410981380c0543c0c0008161013900350391146502580d0303c2d42810b5080410151400c0c0e01035080140301c11010000c0e4810703078144c0707909807aa01c0d02c0413011028481101c030701d400741c6c0e405030780040e858021080c1114081e00301c091042c40094a405c1d00d4900c0d0710b05c1a005940000051790140c0001d00300c0c0400450f810205030b41520080d4214505070b1998900000007800d00800c0d074500150842c80b406550080380c3d8007040010040c405962504c02003009081c00384581c0e00040c1c900000030800361049a0114941841c040942034101c22441c034081c1a160001c1c141030f8003100740d6100043c0c015081c418000114015880591980c55098006208111680c00d0188403000e000c10000060180300ca0501a20b400610001c0c010101c02e0440321041c8109104203000940014891454100007682110080c840d052000c00381c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 460008336 1250 460007086 460007089
    0x110a060507030e0a05070e1005060408030702010e2b11040203131101030903050f160c03240207031e23040810151a04030204180512030c070b060f0a06050703020c 71
    0x140c3c05500c0c005c1c61504100d2040081103658541d031604041c1c055200100c07079a80e8000181b050703209501c4030072035801c040bc0380310a660700142c484461001c00d0701d03a0030101c010140e190703060103404154600c00095145240d014095404515402c0d041e02030401c40da60b00701020b03049101040b0f000d04540714000c900160000354400c1c01404001075160321294180300003800f030300000d07400c0045d03201d0314607007416040c202007040c000c6800015409450030300c001004885500b031800c10009502c643c52401042130b1400268001204134042c1414810540c18111085040310b25913145400514140790f4482c076010484074a03001072085407003000c11940b40c03601d842004000d41d42056004043d414010108104c1c0306400701c42000f003802084e6105160a4880e80006e0032200d914103072603001951001e4030410024100180d800d400c5020886500390326106e01030b007050b88511a030082c20304c2c075001d01099083c0c8400090080c82980200090603050b285c040061058118403015401882440880c8449 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 460009586 1250 460008336 460008343
    0x90b0f1c1a03030a0905010c1b0e0906090a020d151d03040e06040605030c090a0905060c0702030c0901030803060d080d02040e04020a0e070e092802131a030610110a060507030e 77
    0x15901c4d10303100d01c0581c505d0000152044000450140c0310002c2034407203040380b03011303900d480c034003400d16500011900e04100750400d1504078000c0410701181e00c11002da4001d40c1e15850300c01c01c1145d10036000f000d582c15021400001c0c00200003c2150f078401c0781000c542c8560003002400545a070307031042c19101c2e9615010003040d00c600c0d20990380c040d0803030040c501c014100350010540c03140c064030010400103c3d07030f606d01d450a8402c43d9072011090010400710114502808015030780380c0c040ba01400b0550450711500310a20020b08694403a8115440010410030490241c0301c40b410100001c5448075901c510342c0c00080001c40f0201e01c0740700441804221070030b20480c0c1c0d0340500602d0380c6e5020800b9049051200c100360240000c03120b0b40c50450b989100c181814845a00c1281205025031221076460741900f41c0e10032130300032000e4015032040d4450050b0000c0240c9912a87c1102c00f0061082450f006485500d00d10914a031036000e5441d601c41402401e8010f5401420030303681c10000c40786520542502e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 460010836 1250 460009586 460009597
    0x206070215060d03031d030712080705031603020a1106043801030206030601110d1101050106110a080f1e09100c02010219170406090e0603030307090b0f1c1a0303 71
    0xe003d11509144008a4400da00545c1080050700700500300d40c000b03641d02441d54000c80c504031842c0406401e240c040590120300075402c40250b003003103401c41c2000d24115001c2740c403030707514901016408111030601d180b00b820401d545521860540c2d04904090814511203558401c038500c00340044015028900307002d50a2000d0780c5080b0f4001e60345642541d08000c000c1d4000b4260504200c1031318003110720722100f4000854a602652508610034003030820751425110142d21500901c010300e1045940705601080940003107612102c3c440c0d4520b440c50b04c0386014007980040284100d09840d844401454010081400706000c56172401c000007020310854030004c100030001c2c010b8101d076140341c014180c1d0001c0c00040c144a041e81d028924200c1c0c0001c45a43c005607c482c0c001000b4000401003404410800c5411200507000345203503203414900a8000601445a81e00200c1c00103a404e50b600000029075101c08000050b1440c00580485940082e141c2c001c12211012a142c00002c50b52800004480 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 460012086 1250 460010836 460010839
    0x91806010312090e01060f03141302060f040f06200a1707060603050303150406050d080a08180102040f061214060607020102010e0118030908030f040e0a0f0c020607021506 75
    0x41580c256a2030354602c02800000005010440c8008669515405002c074040d092681e1030b46030655903450000e0070741301c2c8122051010080401840211007803020031032039036030b0181d50242c0d8408901010180520940e1310203815090381030f20124a042c0c0c802e420342c41e1151044100c400014a1403441c07a110003000000404802c00c4102c040186c3c3d0042001e805005d0050000083d081d50f251640c600395031040342e080d242c030f5901c44c0c802d41701403505203d031501400301600c10072180c51444d90744d80c8580c81003e4141c8107004099000030000e410140d155104a46100c00940d01c0d1a500c0740441f49041041c095030307020071500c1440f00307403009561041b84000001488520000e4940e581441107940c0640c406a0455480701d0111109400c24001c0180e06d01d40042ca0002c034400c0ca090003043c140c0142c0012102d1b400030000c01c0130102011041d5002e50b000240715501075100c0c0c00c14072008141440844c0710706030610f06d6004c00c1c0394020441e244a2010780e02650588510901c2d1805807410032141e05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 460013336 1250 460012086 460012093
    0x2012706080a09050a0501060501030e070b12040f05071d070203090904110301090206120907050d03020607032c0a0507080c011d01030212040501050a062724140918 72
    0x3001803a1140000d0380c1c110302c030300302d0000301514952103e1341011100d101c00c0e1140d81d1903c20810265a05224107040041c1148c00b600400d41001d80302d070480c5c0316480e00052a42c80000218084c0120305a035014030541c0242110300c1d13981c1d00e82041d03800c0580542074040034006007000400340c034004000c56900c0c00f0f0041402103555101c1c0e80d50381e400a074800c19290199a60240c9500585882c07004080c04040403840921030b1511004032460029a600002d01440f05400c01c000000d40010380380b908042141404504030398292074541d61410b003049413410b0305030a0251009045d402042d00740c0814050400d0340e4100d511541c0040d604c3d032500c3c0082e40001c81c0343d003041780c080e100c1e4032024452000c14540541b41c050303071030800000700109032401c0e940c41c0d540c1c500380241e05d4801d1040d20010040c096103083c110780018039030704805040d40c1d6042a83c503141c11001c1c0c0f004840310398504600101c8001492056103410305a030f442c40411014500456800c0e02041490410080d00307010601c050009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 460014586 1250 460013336 460013339
    0x30c08040b0609252c15030a0209040f0b090702010c0c0305030408041e0e011512020a27030303050f01032102031303080304291501141303020127 64
    0x144070440c800284100c2124603a08416019101980410034101015645080204005c0511000455141c441d0400c8051000d100c82d401d5480d2160448680e000c0c03100400d45a0303403007a4148000e8812490040e9101c0c1c075008410801118590000301d00007001c0c4c031404002c0d80c13400d606900322901c103200000450b202c40c40c2c2c10002446140107549c06485503c401c1e0038641c1d41c041a80c031055441000e40910300c5111010700031281c07080f100030b0041114001401c04030402c554044c00300c8490701030101c49580c00007085480580102411020741d9580481481c200151406400062009000c1100003030308080200714000076400000d81a42d4010b0f0119882020120b0110866010901ea02c010760000f40403c5000d4000401802d00450207419851b1741d0b458185012288212500f141500304400c20b8600183d00001201c1107500105415201048000110040c0c1e8503000420441d040e4810004000c506801c181d9084070841e80300303032211051400f000801d1000b44100440078011300490610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 460015836 1250 460014586 460014589
    0x50402031f060905090309130203160f03090f030509040e0c031b010903381006031e020c070303020c0102030c0c1c02030f0c0a061818060b120106030c08040b06 70
    0xd007124244090305001445655580000095520884504105801c003041510711030928004140d1100d40588045284d86803000610b02005010309200c4100940e182d44814518042d41c03050a000d5004180b100b000c2d8520300e00102716500a100303040c003841c2021039942968500240410306c000004000d481240300403192103802c6941c500c08181040202c1c6000000b2544009408400b000600d5009038005003070300c81440103006284210100d10004001c1060f1403014841c03c000751106440c01181403413040e92845505046c401a07a140103100050788903072620006044811240b09800352403082a01c10016030b00c80c01042d0701a8003603048101c140009140800c43c2205114104440d241d00303940e1500840e02c2c1c041e05c0d03071401c00d0503030043c500d000b000e24050807104028402480e001320760a032361401c2c00e51462158802c0100524900d03c0c0241d0b9507200d500005c014201c0c0304e80c81c0361211684040a19081c0e400c0c45202d002c00e280c040c0d18440303075215040d0640300b140c2100c02c400071901e4100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 460017086 1250 460015836 460015873
    0x406080703030912051e0f15010b0304020111031c0b0a08030301030b01030f150f0c02011b0f1b06020c03032208071202120c0706121406010503040305090303030c04030b060405040203 80
    0x44c0031200741c00340f20b0f0002c2ca4000c200c8206e2800c040b001005100c000a07010f500c0b46442d071040d034200b220840003801000100b007040f0490394419428038018260808503a242440c5000d00e00300041d600c0c0001c943c04040c1c0702c4641c0510101d500803920514030341c0d41e5095503a01d900c400e02000e0405480301006002140c46003011501240c401d88900c1c00303c040b000347e00c00032100070042010780692141070105569609014540800c8181411030042d654101f0b4050840045900640180101006500e5408002082c00200070345c01120035540c808603c0c222545a5008030754104000c00d04a0203610720241049100302c4a691102d401c038580040b40e01e980b000d0303d0509151900b144585500030541c2c1d070511010b031013101c55010050080c1c4e07003000030141c0f88205a60345040b03140d1400007800b803800c0f0041c1c01150000d4080c20070a6594603a400d0464551150f01901d0341c061000205100c4a242050014070841c4d000b00c4155440f44c450004101c00e503001550040d51682c006c0248112510041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 460018336 1250 460017086 460017119
    0x1902161d0f15150c0d050c0606040e1b03070510030203041b03020303071106160602040f0533120114040501050303072103021606050f13120c0606170601030204060807030309 76
    0x80403c034104a03020800390b00e00b4010055800000d40f000c10081c0300c0f118204540764110070211018060306500423901c80d070300c0e0506034820400c1c988a505990f0103803030034007200018140242614803041d0007040e011700654420380b81290301507811071005a10400070942c82d01580c1e80107000d549080b080c1d0f2100342907c0c84d900501a4044800c0183d0440900b40000042d507403440360720702607242c0e0b15101c00032518002940c086406100401c2c00490b00300301c98140e80860a0603075000081c007013020110072041d0700405100089000c2d49400100b2400c044a181d100e41c0d1070221402d12a076a02c0c1c00a05482e40074845004010408403040d041d8580448556010002c005140044c01c00b01e008001c0132008007000e20540712181e460040c004101003107480c6583c0807034041c01d6200c001000e56201072014034100300340e0081118540b46801000480c3d0802c0000340705141d81e844080c4812000592101802c0c842244200e02e8901c0005020001181400403260583c03075140d50340d071403da44a51212040d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 460019586 1250 460018336 460018369
    0x106080a02091c11011b15020c0d08010806070f021506010e0315240a03060207021504090b1011120c0a0605101d0c1902161d0f15 57
    0x7800b19503042d0311085418003012a03007020200d0035072000c0c106054440c000c0c0031218100660360400305071000789168403030300e40c5601a080807505001100f50000a02807145003107010700410450070b12155000301018103032081d0605441d16512546020ba0349140044601c0c8090703041a40c50b042e003030007082200c543c8104181803c00405504100003410403042c1d00100c5030018240040c0b200040e0030b4030b0f0b10110040620208103042d003413400040c080610f07512000784001c6d000500401107448513944090340c0707a41804955126a00c50322418003421851743e241d402003504040402c10f040c407880d0f1001c82c0791002006072450b10803440503140ca50b0b010410035401446814060000514175118584c82400007440d0018280d0074602c842650300ca4004000740256848018041400110801c0700c0c00d0b080e00710208424042c0112061f4142402450070a014450201300041ea01140190015031040a07116814a655070001d0b051003060f025142d070710b19425501015034090034070351902e80c4035551 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 460020836 1250 460019586 460019591
    0xe150405060d2a08031b0c0a0e130803010f0801140c040504111315080a060315021605060903090112020301080703020d0516060c060606020d08040602030604090f081305030609060106080a 82
    0x40b01c0e00040300b0f4400c0d5100621960001030325800460121021409940192002e884000d03000c0300042c5804030a401b41d03004501d41100131030101c111074003e0007080382d40213590903107a41e035814455200c6440c920501e0b0352542041c0c504c800c0c0459000c41188074080c0c40e02424109802e0205000040c03940d00d401084c40c5004000e0300820701c4c50507150030000c00c0c0000c00d00e504200e0b581c100070090040680724091840c10701c003043c000254000c442403035100080c1030041c0c9038024004c034040400c900c140302030003d003d6003040c044120004001000150020380307990803551801c074490300c103d100034440c0181ca40c110a40520042c5003021800110358010001c558080805440d40381c519034070b9501c040b01044095506500304840c9000d0680200000d0001d054161001d1001904d92040200000d1455070b0010001d522695203601c04481160010000b488151b00c80c42d0201e03a40e880145003a58000e44204c0c00502440e00040c0c0e10311841d0040081c04d007a0f403a06809031007010001d01210002078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 460022086 1250 460020836 460020893
    0x3040515270612040c06031407050301031e060c02060103060b0a0f050f0f03030a2a05100c120e1f0b0604090b010e1216150e13020403050105010e150405060d 69
    0xc0820340e03440c1c041c42c0552280d40400d8600f0502900302c0b400e234038124152500350303000c1000054100058a044903008142d50740111412100100c1c2c50f61040070082c04549413100d102942035001441506a9100e164200102060716040001c500f80920405440b846583d40070302250500340085002060042e218000040003080004c3c115040401c070b6a0010381101e0519442c01a01a000e90b2034402030704016005006907210035880d6074013580c080e1026519560181c0301c00d0310411040c41c5140c9906020418103240b40c00c01901c44401059a88100c08641c0143c55403500130301c99400c41e000c000748a285024a440800d401030010000d110341032150345140f8448a4691071156006e0b00b202038080e201c43c0580a1505881d4552038010808141c58008a92545a045045803490b400c08807141c0a11030741c0700c9102000381c0b0540d00b0043c229420080005048403015500301c0c003a4036082c5940130042d41207400d110840e60119a481d034090b84012210b000f04081400220480c1002d24100a104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 460023336 1250 460022086 460022107
    0x904020d06030f030210090b0127020a02101b050909040303020c0318011821060f0c020a03020d11060f040602070b01030302030d061d1b04090608030405152706 70
    0xc07140d90740190b9001c0b0410710414201a4140004075014103096001c001609840d01c501c070504a050041a180b0a0960080464100c51040c0b1400c00b0103041c009654407c040c8400949850104481c41041170030120303011541e1b11018540001074a650360380a0601000c80100864580040c00a4045c5a03080184545810703040c8010314040000c032941c00c0f41d07520042c2c0010300c140441800e502118812950600070000080b8241c19954240e075076142000005060110050254446a503000c5180040b41c5407001d8011071110f030042d0094090341c242001051007540c804002c0340000301c140c1c01c00c60004042e421a8100c00c1e4200d80192001800c1065070354904908002c2030b002035025900201c3c1c00419440c80e4050403000c1c2000c24a00100c2c0a401c401c8240d0081001e402801041074a00b01e40c404010b803034050703500401528000707028196a41d00303201e40b07170750042c000e00e40a25486c0072462640d03a90030301214031250512420034204800a0140345002c500420401d03070103c41041401c120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 460024586 1250 460023336 460023341
    0x3020906041a0418020306030a0215090d0c0e070809060c16082b0605060909070c120e01020d09120609051c051c1b0c0609020d0302011e0605060904020904020d 70
    0xb0003028640c0710740e8843c20030544411a1541c01103102e0300d24010001c00c035840d200031a00c010f40c00c0d81501d4000114000c00d400c0301d043e010300c141c4d00350006212070b80c4505100f2030b06010002c64110705030031043e0340c840d0181102c0520048484009a03481130002c1014090450000c042d008411048803080c07004e00d0362502000d900c1610001d542c0d10440e07050106481d005110105200c0300404204201803a090108035180034064001741310350011030000d018503014408984915902254003518038880c5400600626200d810050040c031610203021a17643c0140d511070b0544200044d00ea00c40c0c0d11a03a00d82010304100c1100300d840d402805100340314140e03400314240203503000e526125100c42d408048a0342c41d41c1003241c850591030801c1050b040340d411981030441d0328450317490800e1205501e8201032003e481d046100035000b22032000e040b014541e0650141284c1344000c40312101c0c05031502c4905003030310343d103000d40c81e4014820031540b41c4500c0c19500400740140090409420b0821503040da104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 460025836 1250 460024586 460024619
    0x11031803070b04030e0901150c020409060b0901150809010b0f0d0204151205100c050304020111241f03150e0c10030b0102060a060f1203020f100b030d0e0603070302090604 75
    0x104054042c10004ca24148101034050f00004c0040e4528010001c2c00612700d03405400b000c1d0180c0e5540b41e010b4184902c1c1d03000b1250071080600b1441c07080d40d541018506410011003c00c000503820008141c2014041c0a00666864014640140c0794010010454200391006089a0059890010750800b2074510341c40e6004252455014010144034100a410310b4080207140c510350b40f5116807155030740d8210040d241c200d41c084c2b92074150002a1030701076140c03a08148598510f10b0803020074021080c080c00319644281c0b8500419060622245d06a070903440103030000030b100b507086d070110400280683e4809403c603030070315048800e010394240100302380d4000b60b001080000c0e101d00f00c1c2d20165030108000f6410401698003000300618114007112070110f14017601842c481c640150006042c420846c00803950f41e1101543d10b10348a090440006040c1044264020301840c1c414600c9540513070340b24001c1e1800500954139540e1012030840c000d50001403500c2d4030a1080c40045400c0a0141c000070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 460027086 1250 460025836 460025843
    0x305030a1e060f060c050304062601090207020a08150609090114090c03011112010b0a140a110f0706020a020f01020a0c0303030c0824091b0d06090f11031803070b04 72
    0x60043d05003103002c4505082c9402c52002e000100d006180012000402c440807500380e07142c02c21100e101d405641c64043c0301003900003084000341001091031102603006100c054030842e1000141e940c1c454040d07031207030000982115a014000006021402c00441b03017540700d072105000041c803900801185110303450542e03105840d540f000c0403c0140781000d00c60001440640311a0707604002040010000c40c40d814001e5400880300442c0303407a28a400f034403c00785000100ae5a4035110003c182000301050300400041030b03107200f001c08424010402181c14002c1c5c03010365002d0140b450440d020b1004011502071658118407410843d00081031a04210801542c401d07640494118000280105500c501812110340912807031081d529241c0110b0641c0c44000e0b054072036845d1583c48441c0501c24262501a490103a000080d10000654480d8045000d554506d0300030012402e80c0c10100040307a4030424803030110003007080030440340000d00b81d580c1e14121012046a141020540c0c40900d00d00003a90b003107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 460028336 1250 460027086 460027091
    0x32c010506041d070303140f0f0702040b01210203190501060807020d0e2d060a030b1c08030103080c0102070614010503010e0a12050c0325022103070305030a1e 70
    0x200142c5882d0140c01881c0c40a2400b207a00c040d02000300719120445840010184904040c6102040c200e1200f55040381c0c0344011a55214844490007410a500104041740300728a403000c80001c1e58003c90380c03100039a032004a080c0d208a80c01c00214020361025201c0d141041001c00380c2c50081510703020701d502910041e0742e011250f0a0103a400ba241082d041611030500c545050950a541c9900f04030907890b4000c0b0312144a419444030a03040603210121000e5080700b4001940481183c05800100b100c0710180d642d40180b411010880c8501005050f0080400e8070030401000440c2500340035100d49502c9000052800c0915a078420032107011001d80035200b9200b00c0100041c2c64207200c0c1560429000d030103000c000300715a0703e003102003480202210601401040040e903c01003007050710301d508150407040507503407003041c00d555030045201022881840c80004d0301e8094190a00659a0010707140010340c20722080b550180c6440e00000c0145590590311040c0c0b03204002d031b103204031188a0940900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 460029586 1250 460028336 460028341
    0x3030c09090b01050901080c160803060a0b0301050f04090203070801051918020f210f01020705210a0305040303180c08060601020c240403050307080418060e07032c0105 74
    0x60194800396200d1034409140c0724266100366000400c0328186802403074468125a5540340d4160b80d03000305c0040040711b01c1c1d4186d0748010800882c000b540202821a4803404403603407032021920502c002d0140e81d8000010392500743c0035007440c2e00107880240c801015103441070746070000207084138011554803095043c0300c0000d2041310b05034402e10759400450400780f000241d0680204d00c2c8050f10b800d449019510704140c040c03c10040c00c40c680383d1050604281c510000310f031250240030390007130041541d0902030148414420300f0703c2c81000d229004000341d483c0c00d0110360a0141d0040000400c15414035032a014043c40303001b4400c0008450511880704d040300141040b000d146031002c000c0c00e00e415580060008604d50340c40c0003080e1542410000650300580c44a0001291805160310050030791201058400401451901a0050b95145142412083c0040064101ba038034140708041451341002c010444c0b8034442c1d0810f1a80300300c0541182c0c03681c0c112406005c3c0074040c8568100860359510203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 460030836 1250 460029586 460029611
    0x403150b100503060d020d050c04020711030105060406080601030b190509030c0d090f05040b0a030501230609070c110f030d090801060b03014a0702100509031c0e0a0303 74
    0x1ca244001c01a15099040d440c2440101d06010f043e400080e02c80c0d04a00360392820130030100508005401c01070b00954a035206883c2030162045205042c602c00d50034040001c04506081c8a00e001300d0745484c0050616902e50307161289040c101038080c04149400c1500c002000815015003401500b5401c0116550102041c6080c18000070500800c20490f4824040103c000039911503000d90318119000030350b0944c020000f8440c080190b00c001d000f542400804449007003105411400d56075110b061400c60398985c420054846800c441035408126401c0700e48000c42c1d262841604503040142c80104020320a50001e490440f08000c400b001485442d02841444400e015120081c1000c0540178115410241460a41404a803004221f0101003d001c41416111000b2400320042d801200140301e40c079601c0b01441104c102d50031000762088081c0703030344484510b2050510600c20709010f942440350107012069406001500452484e48640000804a409100200c80d0320b21985001076801a001d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 460032086 1250 460030836 460030849
    0x101812030807113301091508010c080411010c02131a030102130618090905030301030b060d020109140d0b16030e070e01030b040c0305030a0f0219050c150403150b 71
    0x80ca9801000308070305041402d5000040c01d07440130220a400e4a242a0448003c503c000b403001c3c44464009805200004000e400f0f68400c03903038056101c8400b0101c81c2c8903d1003a0036074034103014a6001421030400074002c244401c080c10346540c414503200c1221503640c0c00260503042119090803085544014101c44102c40410b000c038001c0c001c1e00250305280844080f004104914450031341400030350360b5041512020030360464064000e443d820002c3c40380c1b504000f41d80360424001115620f150201241c09480c0c00310f8510035150381652009035680c10408010042002c0c4402981c021035a049000005058054498400e04d440346c040e00ca0008907071802015a40754002042007070f00081800c2c0b00d42980440841e041da600107600c00c001e0786491818401407021603102500601010403400038260f4032240040003003085900f114075080740301541a2150020350001080c60740243c04042c1035090003640c207000320340b40020881c101aa2074448180588800f841c0c420000d079034403c0c1140c02d18060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 460033336 1250 460032086 460032091
    0xb07020d0212040521060103050c0102070b2a1903020c0f0a03021005030c090d1b0603050c091e101701080a082a010c090302040b060c0c1018120308 65
    0x7032004150420201012440a100f0f90003050b014024000b00e01c543c040b07401c5443c415081e040d80c2164059a941d051081d00c40021050700b90050042c4d8000207140e080e81000c0e91010415902c00c440460f280804012004842501141c002d0068070f10072411f0301c1540e6100e6406ea0f00a4000e0180b0040c07407000c018011361400012072041140c11010300158482c50000a000e00141c20403660300c2d169908442c09a00075040300b5507002403400c044508003d1488034038409181603800c001c00c13158035620305401781c43c1d00701c5050054000074004e1080e585071180d220b0074190f170202102404410b0600204051662a0b0103d501140e0641e1031019008102900d0754014810340c0b001d40b0602020f55280c800900c0f0f0781b4a5001e19241c501c1000c411014151008894035044030001c200b00c01807070f00050051621488107a105d20714081045100d410148202c0b034003003031090007904c0c0071240c95042269407000b0320881030800c0700140100308806030342d08d4490003030260310300002c001d42e146150081021500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 460034586 1250 460033336 460033363
    0xf1209021c150905063d0314010e100b21011407030b0a050f01021005010f170a050706050703050d060806060916081b0c03030a0209010f05070b010e0a0e01090b0702 72
    0x1003200703c202181c40030030041e411041740e03c1a190040003482d00d120440f4081d030204040001e00001d01d100310007940c9000c00440388a5040c940400200100076401c994556411907a160030a808401186005901802c441c85004002d01d81d864042603204010f0240340e0841221695241c600e507240320020414158010103601d000d200c9085003001091000115100e03080c040d814001025000341e000b80700f50307681c80348220000c1000b50380d1503a0b102150300851085484100203041080b510040210301180f405070003000600c44285030a00072a03540d400504285d0410505101c1c0c2180c2c151640183d00007403500000034035140c100501007000080c4060040c0001080d0040c0345222150003c1c411544041001c0c0c200306040403e02402d201480f40860320903603400000100000d01d02168094101480e003a0303101c58203010443c000341d9407881121405080c80c10318900402c05100c0303840342a54000c40d41f400205e041c485812074123003901c0510b0340480d184003030380c010010fa6603410029098030801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 460035836 1250 460034586 460034591
    0x170f160219031104050408070209130b01080d050414011103160210030506030a0b1801020a032004030c09021c061805100609050f040b0306090a210f1209021c15 70
    0x14580e03400d2034149a009515006581752000501400652429101060f4000d0182c004501d4080c0ca40301848ad40c07034030220b40034800c1c00c002282c1c10700700140103e41c90680da100c9031314060500b9045613070038003020082c0d410030101c50700100c4100001e0000e8240c0a01106075511005040e02c10040c041998507409010103190404020007a980024400074440e0452520300c1d058481c4918040e2004a42c4d0300ba0025600001d0880c1c282c1e581a4001e82403a015501160b40d82d012540c44800107204a200c044d1003001407183c18406005194010142002140c0e43c80305244800143e0805407620381e8810701541c4000710100090080601400398001c1c0a00301220f80c240c02c001000d07000300e104e409a00e0080c14080c1c00e07140540c9807584610048500102181d035249040303000f003035807000078a038115402c02c40d8008002500c0c1b24a03141c46168111a00e5400c1d103004090001c486402c0744503070215500e600e0f518888056180e19903c0c0c0c80070400546800114001800d040390008603020041e01070f1403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 460037086 1250 460035836 460035839
    0x1d01080a02060f07020109170a21080402210607080108101b03091a0907051305040f1104021308210301030f03031d190605180a170f160219 61
    0x262020203c0b843d0300c005420311034448500f400100c5075154180c0008241c0d0340f51203140d00c5040000503001c0c8c1514801c49503200d200c8171060441c0195502c480000c804660317550040b9005150281c40000c05492034410018543c08091096280ca05c00b0703502280852740d0f031001448080c600340b12025200c00582001e1110310b452540030b8005080303100d0207004040c1d41d0122501000740c030703400c66201d006240c440d040e15802c2800003561550070500c10b6610646070300c000031543c11903d001d1680714640124082d5184d01a580354003035141c888001e8954856800c004024021140e00e50381800b41039590001c2103a9030301c11a82c070441c1c00b00e114140b0074019090004000045545890000d81d503854600455240c21030035000025118080504001d03000b42e0920039004e40da000b00394803256015400500c2140c95103420904103100101254900307800103000c0394041850098000104224140f049181c54011456024550000f041a0480c9500c1d080c1250651400803a034005a18145e079803d110b40307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 460038336 1250 460037086 460037089
    0x50403170105090618070203040b0f1918030b0402010c150902090709180207020a030b0403030203190c02100b0604170304081018150b060406030b100318080306191d01080a02 76
    0x8207070307500403007031480c0741703400078802610034000e80f0018000d102000d038450008410110841c0c00420b200b0030800d5510144440240c80741c28940605002c52000d440c4040c10340e21034800d4103000400590503c00819140d0000560f0b030456210128103491000035802a00d104004c00c1002c040d101d44100400c03400140102c4580ba003003c0701c181030048005076034000d03d00c081244104594006059034018000300030900d505038008500c02c040800e600c0c41944010348044040300c1411600500590000c856205000c03110744c8100208880289028241039442c1c14092192541c050b00c1101030704041010401900208a5140714442a1030706000c0c000d42c012800f00e000507680c01c0941800280d24030640014021f0b84034020000001c0d24055071107440700d10182c0030f003461200c840d02400c020301d0070141a034800d114000241c60341200d070866400750390300c9000c0a40c00140480c0e51080d141000303184e440982c10418802024a20440340b408071402441d07960f0f07640141d2044a00d500040c83d501c005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 460039586 1250 460038336 460038349
    0x8090d0207120c1205031804150303031808210903030603060708070c0b0a050103110f060a110705061603020f070602030708030414010c02010f230609040302100504031701050906 78
    0x10340b801526494004061401c0ca506a281181c0c85503003020702c90251075080c8a4040000d0190038516402c01030394001c1d000a0008881c2c46009140d03c0d800c0068052001920a40260761920070020050000104580b281401035100b000c0142c4420004003c4000c2c01003000286a0700c4140d41e030103141145061000310b81c460f0744c000d240c0780400205038000340e0094015501c500a458000603400807904e4200a00e100404080c0400e541d20848803450214900c0d026000c4c135203c4d10050040350402042b14004e031080c26940c0c1c4290035a024254011070b09498000107400c60506400361100b044007141070181c14440c00c83c5e00c408007038100640274040503800104941c0404c0d80480c0e41c60f5242d5550400391603851010b13420f44119400c01c0240c0c424964150040003000458038420020722480680c900c20200d2265001b96078400014005a118070b405042560301c140a801603d03000c005d4000d0790303801c458044808602245911a20000b00300c280c42e841e82c09040309880f024803908244000980 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 460040836 1250 460039586 460039589
    0x120f0403020f120102030f10080a120e181e06120c130e160612020a0806060c0f0a080c12040b07062c0a0b060a061b050705120d08090d0207 61
    0x703030020004200894030fa03280724510720050b00c0000c54a0741015102503e80d104141d03800c0d5051007840801181e42ca4001c502c400b0f0659001c00021190040c0ca001a80c11400d03443c3c0407580099080e00c0e1028100e21528441d1095400100c4c910901f0410000320900c1c400145c0140d014a07120445626610b0000600310950320b0204d0f0002c0e9500c0255091802508169080c040729004e0088005000c00703100d80000705903215611900500010048510228003412914000082d9460049881400c0820080000401c200d0a94218018001e089442c0c021820000c0f6481440050b00c0c80440e582881040050891626824a458a01410700445c0d0041d0000a000255118000c1c0030800d880b40309090b20f020740445407440950308010003034132111140020740d0400904000a24a440c202956801352400b40d03c900b400000c032034a1540c06441c2031a41150548502280824240d9a8021303002c3d0940350304009020071043c0d0f41d001060000040c011340b0a070303440344961840c8142c000c1000b40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 460042086 1250 460040836 460040839
    0x1d121204090b09280b1c0f03110c1c0807080a02030c150103080d1505041a03100509060f150a12030315030c0504020c0a151506020f10020903010902030706050309120f040302 76
    0x144100485c2c00244820000c00c0c05001048200c01802c0402510040402d800ea010382c03507102d00c9251b100c41c4103403940d444403d82d542c08101034000740e2096228040001409020b54016414103071a0380e1031901030360011115601507800840c440714a82c10030090b041048002a204088551456482c3c0700b16000b0b484c81103000503151402010ba82086072002030041000070b009100100c1c6030118803070200010210f050103805501c4950020350054080d082c05a4605801003020b9a50070a4500310b07607034040d0a995440c990900c90506690702c91009201034021000d00420310304841c03030302408032034414101410b201e20811080012641c18000141103e105403000751307864950044150a228200000400380000087c036613000302c00607448a48401203001c0f0302d0114a880b182c080c0c0e80e07420122188101940682c550603180c40031500078101d0028041c00100c0c1400c0142c0c00039080402e1074200d40002140402049a01402080501c08000082d00510f182c645000f4951f80700e4411404040d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 460043336 1250 460042086 460042091
    0x90c0403030f110a06050708150a0f06030c021c0801062601030303020c011512140303010e150a0e070827120c07120f03030501061d121204090b0928 65
    0x110f00c20803040c80740c41c030780c5940715074100002d00d003144029000410a40343c01c00c0d420607140307525446003880300207003082d1110526810b50070b915000d000c401510410040000f10300441c054400c40b40380c101d64030151620281c50f950302a42c10800d0050a8000d4414140d0480b0000d034403c901043c5882d441c41d054a42516000d65504111200303640075100510740122505016000024450000340981301824441c20001d4091440d101d90a541c0340800e02402a0742402d800200350f5582da450181c2002507000381c400fa21260b0307030b07480c2c5081c00001114400046445e4908010804101d4840500a04180301c40b4080d80b460701141c941d40c5102031042205030920000f040c24041c4e0003009190700030184244804041c100b1403518084003031a0a04c00c801103030510001051a40c00340a50320a00407103100034052900301c0c001041461000c0e5003085031940180d01c0c4107214107251600a001604828201144082d05070040c411040c000820700b81002c0c00300310384410b06100d0070034150019100507801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 460044586 1250 460043336 460043357
    0x717070c060e0d02010f0609020405010f0806030a0b0411091b04031401140403020a0c051e0d1104020c0703140705011e090918061817180a090506090c0403030f 70
    0x50750042544000c10340d0948100003150704890360541003440007800307266040c0401c2d80e0750a5031000b640140c0c00b6484c003088086200a00c07651143e5022940000000e040350569105501c611400e0041070310140c902180003032030780b8050b00f4007030702040d00690101c0d80301c20109a4046203900038050b5000007454401c06034100d14800d04250085980d8643c0300f607031103a05007068039002e0b46c0c0c2d1014100c2107030200c038503000000d0b0601d084404030001410080e660f07240040103008001854481c0300045581c007600c0e0f207100e60a034480b8405032405505000052456905600302149481c2c000080c0741c0081c1d00030001440301c0e917405584800c000c104039002d220801030055007650704e1000c54001c0d10505103043c030503a046801070114410740500500302003001d6508044907069490500101500d001c2d91045840300d1010320400420100242031034401c1803e021200040f00010b190b80b180c003071580c4500034054070780783c141c401d190071040007035041d860300b46155006000b61068511001c20701021941 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 460045836 1250 460044586 460044593
    0x1e06041a0408070e010608090c03060a09063b03030c070b10080a0308010609061b0b130212010212071d0415090507020105090601090603260715050601080717070c 71
    0xa075005072407007406a941c01500c0b840f80c002520340c240301c1c0c0c8000071600700c0864040d07500414003e113540030140103004551781c1c100300d2002800e072010044401c941c1c3d890022902980e046040e401c0814588194640309007a20107984140f00480400300c001e401c03c00c24480c110421000302c444031940a2581c2c030541d0755414180f10545541e50010925006410004c0304055000030306505a8001c1c0e1141c3c2070361072715034030111492003451a0f032524003450901d0b6a0041103c02c40704983c48214402008180461540401e480c0d00128180038101e1b0340128070300400c00303008000140d0012062800d8146298620b19845031000d50300c00081c0910390b9542c0c44c9901e1801c0d84440b8026003c0300380c0c1840b040c01c0c5208002d000b4002141c0b401464010070001142c108514060402225082990142c0d1103404c100c0002900c485c1e85550900f1500812006001841e41c80700922000c0d0300c00310000b160701d400c100240001000800b80d90421501c8101100c409148960b541d030002030b24984101040810300d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 460047086 1250 460045836 460045889
    0x20a110a050a0815070801080309040f061a071106131203020109060c0210061403150a0905011113060306050d0f050a020316060e03061612090f0b0103021e0604 70
    0x300400c2c1c0001d41c088000c80d00003400214150803080d0041001d080d0f03a01c0c4001110807038400c2c011000c00d074008101c80300c41032501d07030041100c140302e07040b00140d0b2a984203600305880b0403107030212441080200300002805080707031501c80700c200150351b400e1815039000168041c5840d140a601c0003425407603604424103100354880c0901d1680903608000031080454065a0342418425130010a403d285000c1005481074200c0b050100300030340100092501d0030304904402c50010900d06066941d1031038003005c0b5209000f80d0788842000442e4559810700d841500452041c80e40100003411304181041103917403555030744200800d8201c44801d003101001d241c400e080240d0b07020080d50601c03c038050446120440c070040d40444003642c85800f8403001980c00c1c1510345000311400312051008104107002e10b0300481c1480c088121811000500c402c240e9100c0c03103a1480d030002650750011280060085091010490904125800103082d80a84550004242e845503000e038a626103030029a54080740d5100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 460048336 1250 460047086 460047089
    0x4061d0d12143705040b0a0e030a030207210503040b01140607030c02040b090f01060f08130f03120509010209040606021603021504050303030a02070501110a1e121a040e0102040501020a110a 83
    0xf0100604418031815031880139002c10344040d54542c01010105025050138807510800782c0240d0042c50408800c801c0640c025040261300362032011684040034418403106004481d4000107403102902c90900f17061100e8100c03016005503c00091046401c40d42d5500c0c2d100765240303a54503140c8207540060520225010f404140700807a0016100b200344001c107c0200c030160305071039490703450711120020320b2411224204103664104241e02d4260852011038484003200e003036a402030400d00d4048070b10540d000e0844808583c8d100340e6940c041408070140c509401480700034103c0c1d1004040350400815282c3c0075500911000344a04c41c0704c00202001e010100c02c0c0c41c000d1000070166503c1e45805000304010354800ba8041b5a00d505e445099680ca21200003510f00c0c8034419920369120001500310b000c5c03007200702c6280c00b060010f103000201461055008114044081c04030388aa1008100140701c151ba580072282202070340144030078092641c2c0020342c40c001c190800e0078030203030034480d002040242219 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 460049586 1250 460048336 460048411
    0x904112b030c060b0301021e0d0e030d02130f06020d0809010b0324061516021c030e09060a1401030504020a08070609140402130501050304061d0d1214 66
    0x58140341028541c10003585800540103040c1402041c400104041c201e118883c07415201030344044114846c041c0741c002802000b07121200004000c540006c1691854021a0a89a000d80c00060201002c8101480c00000b440042043e5040c14100040652a1000711119a08108d201306c0060340e070301c4003504000f00e407078000b40503180e0707074501150b1030410b07030011100848030f0191800119240e410026059200303460070001c11401c08107012240b0500c0b043d49101683d0004101d12140f03d06000340070070b010303900c3c4241c484c51340b102040707002e205d00711100410442c410800410104072414a01c00d051070321400c02d20380000c541e52584005400d00280d50410102807260020110300c9540081002058568112000f944038000f00200803d0f445500b580402d00055500d0030080c9502038809180c0041c8034107030100b49205040042001c0d4004070201d022154844600480000d03044080001190000e140030b103c410300c6207a10380358454000d031940e505500b50480030711030a4081d17140e50408041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 460050836 1250 460049586 460049659
    0x70810030803130c0f050d0b040c0515030601030c0806010806010c0c0f06050307020f1b10110a03030501170303090703080c03070b01090204060e040209030a0b06120a140c090411 78
    0x100001103c200c4021110215030030210a00007140500300c1c042c00740d007107a000404103d500c2c82d40360349120703000f80054005c4955000d02c00004c201503031014400c450001c51840c5494803807400c0d0000400b6920b21030b4148041c89204014854240d90061200d030b400802820840c5901d42c4038601218400000d6000d81601070b04204049180c0c1e50090040d409681690300700e0b0207551041240e503842e62030640482020401d61080450b40e41440b840b811104155414103020354a90502c1c0d5034204540b65108030f0010350381d1401400f403008903108164030000740030700450444c079065a080740e40f07402c1404040c4c110040895003202d560300810443d48403c1e0701c412642d0143d41e4502d14400650810300811012600754a00c0208604040c400e4800e685001002811440341640b0380500c4500041c00c8a5000140d0b0180380303041000c10840c40900c10f04c00c540501c001144088502d080192400303813244030b481c2040c1440003280d404801954403503012030322240080400501100c4044900040500342070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 460052086 1250 460050836 460050841
    0xc090b13031e140708070303120e01020a08101a1806070219030c17061504061d0a0509010510350609012d150e13060e0a0209070810030803 61
    0x110300c034400e450074418068a03214103540d80c1c01c0b130b895030218080c5400c80d500288040004c46d20038080440684000d41e000100342029038001400c1e41e209405040200c2d1889041c001d4928614110f9001001403a40384804001d03c1254841e092264603440b00c0c1441d030034504040ba550744d0004551410394018501e40f82a00d1510708041e00c189284001d8580ea43c41d0880043c2c140104843c1510150070403002d80020b90b0f070000010146006102c0064101d42d8500b40891242d802811180e50f1404100f890012481e000c031210041d01c0c00244804a180d051105002c40e10005880c0141a41c0c081d0008130703a003004a8984400225107034140038501d040c14650506204c502250f074501440d035070b00090000001c140c0782d0046034062441980c0002c480300807018807800469000840580b24150030b000d619540354540340001d4015203615940001e445d2040381040382911a80c002030b000721010b01010352040d000103245190050030503003482480c0c40064603240c1010301c2c0030f024680c0b000740140c036030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 460053336 1250 460052086 460052123
    0x60f030b1608040804050d14011109120a0c1a09030105040807050105070206010e0105150f040603060602070906030b040f02030a050706020d0f02070b070201140d05070e130c090b1303 80
    0x500d05039200e0307404242603800c944105120700719443c4a40d8012407500e1500b86040b051009038024400d043d90042c1c1000324000740c07100d00b03009080131280c2142c0920b0311007040c0380400c20008034084184c5100d42c03205c4108800170300180780c224110340d1140603600c0c00507100340420040b4803c45006560551a010410040000000103001421700501c020801580d8000040e6a02c4600b0b000704501c1c20b00f403000404c2545001809401c00401500c80541440d01e41c200e10800e60300990003800100f5102e150900140380e0402100c03008010b601002c2c0100341c41c50700d4101c2d00340806007010b4419009040c040c015034404100d0318040d9075000c82140d01e6146d039203034025110100051150b00107108400404030b502d20019101c010350b640494218a4a106039005484030340280300584140c900c140041c407050f0300a481014481e00c85511185c01c04a0781f0f1040000c030400d60302d80d0b03000081c80c20b00e916070802d41c00201c2d24256200000c8465031002d007210385008086166000809255a240951400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 460054586 1250 460053336 460053353
    0x1b05030d1a0a210c08061e0411100302070f05010605120106050f3a2618010219081e09060703180e090a14010c140706060f03 55
    0x51408400c0c0821441041c4100010407200081c09294401c0500409001d00e020000e6000c40c1c0040300110b00082012664546002c510203034060546034212000700b0005215607000920f03000c01210f00200549400d80d200502c40e458005040d02606a030743c410340c8041d0080d8120341060380c005825003522040b0b80713001c5018081d207001d164040e400d0075542908803030341402041c00303a4400907c000d1314800b100d0140710500c46904c10700450341100903e100d0044882c041c8042240140700d80000c2c03030719114144403e6a1450640142c0301c0e911309426244094580d6040d100344c5908072000c0c01240b147d82c00100d2400c00d24101d1200e80940080d0442d0400031048000c10104144101e180740b041140d9106880d2405954600d98020804000840000388515000d180d03007003e10701e000706803549030981400d90000840b401c9000350300c205e40b00c50034024144503000012502100034001d03c40c0d1072200800b00c0091100304822120046500300410075150008070284c5035404c1d88141c15943c90070040364 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 460055836 1250 460054586 460054597
    0x307060b062b1d0d081506070510050c04030b01030212150c040f15020322090501170118050c0d050f03070302030a17060f120a0f111011060411011b0503 67
    0x10243c039055036428405000002c1c030401ca0240340240141030b10590045e81c503a007000f402044c0280207640904540da031071601422000c2d000e00c0007015080f0380c4041175000c4510141103070034003401c14401080028003840c842c03415250b050b40d01843e0400c1d104841d17071070132200c2011040520100c40c01c206c11000d0341d0300600100d40140c140000305641d2048100079030600c0541c1c000050b041040b09945181c0d16001c02d04a4643c2c0c5c45641055640c0c941d030200c21140b00303800009411a0380c0101001518007406601c075a07206078245140c0c003500c07a603581917a8993b04204c16008608030690901841003d0142c4034542644005880d0f5490082c40c000713440b0761043d002d00c03000c6035010443c170416108900c0300318031555010f070042c8081c01540c010010a200d035242114000d204110042000030244103c1400080c41121010a241340711402c1002000000c4120380401860088003000e118001034110741050300034060410100b490700040351000000c084120300080d00300745000401c10008000c19 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 460057086 1250 460055836 460055917
    0x1a0702120c13060e070c0201020304120501050613020a080106030c090503070e06150a2c0409060605100f1d01020109080406051c05131205270f010507050307060b06 72
    0x10800442100b4003001c8601d503010701c10020719240300003000300b801350480040031030050045a041980e41c0c03801c0180341c00d80d50300c03c0319141d44a000780315071420900340400081c1128001903003041c0103034a005224081c148140f13801c06454030b688452450040050304060003001c0d041d5904a6207420b411005140e040e140701e4051410b011032010420380c0310342643c1414500b5a6032800c1c0d000407509410110280009492100b03907081c4000103940da43e8802c441d80c140c0314540204601c0d103000c041280d4100e44400a1013880a03102d210030109078401c24a401589511a586269503000b400403401440302d580000c0c048900040d000c140b080c0c00101a1109000c024050700311a014216007000391002560186140f0340118006400142c40c078107100b0440200f40303001f03400d01940040b030743c0c002118040080140d1141e5100c040b594101144d0070041c3c2402030a059203001c81942d110b0f5902e100316540a00070755616900058665100c1c4115a4208415034004686440100c4000710490f4002c5401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 460058336 1250 460057086 460057099
    0x906030f1101020601030317060a091b0905100207090504060603050a080c011b0f030545060c031801111c0e06070503011e090c0503160305101a0702120c 67
    0x1401d9880001c01c503040e258550340e40c00907841c140b900d01e5400d450183c83d080c1e2048002c100400c8800c88c1d44111140d00c081c000e0440350a1180d9030380a41003100d150456070040d0118840180030680024104085446000d00028241d0312800c0c1440204650b81004050f0300542c2207040911000c00c01901c2550000c1c0700030000c004104005101402403030344504003107010482d0903404a8041c1e400294000720b44418280c01200c0b084400480e070801c801103003000021168a10415450749059520700c00c42c060013450b1a080c6524458440e0100030800540003041d11208c02200394290417061164686400541d00c1d1100440d51f84420310684840c01c840c10320f41144504032602c0042c007603000303c1503a1140352450742004414081d9031002900e01c00840c18290000602c01c1251040440078401d075130b44c6a80343d00700700c20004002441c601040c1c04241c1440d007488014034a011a85040300d01662424181c50305164540e0494059000065031107140e8141c039071540540403d000e0a1098219100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 460059586 1250 460058336 460058363
    0x4050111070806040b04050a3e0a2c07080103060506100804080310030503040308070b1614090d02040e010605030705121b0111030a0504080706110606010e0a0906030f 73
    0x1960766641c818824005180d03c6107010801180001c07940382e403c280900c0a035070440e006078035030780c0e2407020090041d0004942005000d000808075410360b003005408004800a0000701400584c1c03840a07030103070060501c4035803c0c20040050a140c0303251503e280340944445031034441d2000d050440244410345103039083c00005200c525008001602c6650b480e00d60301c3c8107454685400c542504000e0103080e0040749004d0104c00700f6410406000114400e000d1940e03111010304e01a2018103010b0807100e00a4070300c3e0040e1307400e1a00550041904d14400e222143c1310002c05001403041220600042e41242ca000400b040142040d003006040e0b4605604640280390354200344109030000d007a0b080350a410952071294440e003000400051341805240110131000002030140c04e51748100c5401d000300d480050308105499090000c4001050a0306102c200035420984c92034032084000e04d014104050780303c0707940142d540c81c8400c001428010074104202a260304d0124420320003000d00390b810781480201d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 460060836 1250 460059586 460059617
    0x306150304081605010b060c011b09060807050c03121302030708030f0922140103031713030f030e101524120b0315220314070309120503040501 63
    0x1100d024681c40a0b4440c94401c8200c00362621880248084504d5502d4507407852003651100302900142128a00000d4200401e51040c541c409681e41e1100600858800800603140c00c681140c0d481915810117a0713882002201180c2503110b5128868a0100c0d11014088a09841c0d0182c0320103074070a804a40240e610382d440159640690500c0b120351007010000b050311030520403011003d60041850445284001404030400d50307640e00034656094880100400916074012008140b00e0080c2c2003150301820411458110040c210f60040d00f4020350700542035990f07100341d204084504481080d520b5050520700c5d000094000d8001000300c1c42080c190128618500c9440c040d968410a01100c02d5060a8901034802d4402140302c0e4098503552011301c0da2546041c030008404031184c1c800840285404162000c80c201c80030118607664034103034400e0740000d804c18241062102288100d6845080d00c0c601290242c4161700844013152500a0080401ca030000150090340d0007600c40c02203131a100d69 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 460062086 1250 460060836 460060879
    0x8011401061709280501020307050304051603020102060a0b1807030c0909051005041e1b03050a021903051b0f1b0f060606090d080c0a03020c010c051b240306 69
    0x103400c0b580d203400441a01407458201c04c03800503040c2400c1039903807500e05152106422a0003c545d54400f140c000801c210400c01c09020b6584082c1900684103841b504540000b940d88900404004002c0c0d41c90700e0310049503030303904800740548041c07003803545451030031000003409810286c2404001c60842400440c0303054160049600c14951001808110380c5448100809400340c140c030324251514060401320381200c1e074013441d03820400800c000c03500040b541070024115440140900080c510500400e22003016030f010380d0100c0350007403a01065584686001110b9000c40d090400200000021080101503500007d4011051200310892420090307101894441401014842c2c0c1c42d00254000740132850540c3c041e10400b6409000d080300c0030001c1d0b4031003402e42d228045103810b591100c01110201a810802d003c81e420080c41c0038440d42c0601d03651f40e030741c1e54000e01240345031140360030548a140e2a4117100c0300e80381c0101850b01d074416000b868480d41d5684103440180c0549404854070b103101c294075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 460063336 1250 460062086 460062091
    0x20d05150109330b042903071b320d140703031808041e05150708160b16090509070504050909011104060e04050a060f0b0309010204080114010617 64
    0x814000d01000c2600c0f504900c820141c21000151600003000801c1803a0410003400c040d0883c208503c0141c402011841c0800e0103814481081c2e00c0d08001704000799510812000742e0042e501c890300301c07149140c5801d084e4903089840090002c44501e503141402d005c01421043c50741000030568900349051041182d034030101c0100c0c40114402000501c0010b442503000051013000b80044000285d10707661a01c0d03543e84594003001030400c06078120604029005041e000030941241c184121128a805255240c000d030580505408004906c5102502049080580840c4d001b20840070a1404800d251f00035800300c803a05001a0594602003114204400f4050050301c2544a543c10070340340408200b00030340c006081d2540344d5240d40410340304c0c00004010300007402454590850001c0000140000c034ac030000e10ba040c2c4039081c05001c01800b0350700a2070030b00341c840c2c56020700c2d66603595001c41800fa2040f80c0c0841039542c60714003400041c494005203503040c1c0c0c450381c0e01d22211401c3c4501c10b01409105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 460064586 1250 460063336 460063361
    0x3060f09020a0804021314040f0302010b03071503090807020603010f031401230c07050a03020c01030b0105120c07020a0b1602040b03010b0114131809060e061b0d0207020d05150109 79
    0x100f02140c007501d03114100301d8041aa00d0780120303180c4040c0c001c0035510340c001e44003119506d091503500001c054080c01401c80e0000c050340108065032411612414004003000d14006140e9156568414490702e1011562402d4000e48510365a507924001440407081500c0140c481000903030b108041c0c0c58040c00b03004013082959214444413210700307019055005000c0e001000540003042100005802405540200c0d4000e4002e840c1407107a000c0003505540c8080c50150400004208584195160310718250704070914180c2c0b00d803038601a02c0400d03c0f505190300148105280400c60703112a200803284038a21070b10980d014450054481e0a244c26201c1285181d0701054140c85101081c00c0904e01410003070000e001c554001e5513451941711190200d485102c8030281d01c90200d14240807442c00307041d0740294688018203051806812405102c4551500c50900080c0016204856403c6030140c1c2c070150b800038405031521440b4501980c1d031300c10845402070030390003440000402c1e07040c4c0c4c420301c80c1100b075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 460065836 1250 460064586 460064597
    0x91a0a060c1709061903060503010e150103080c1905010b0114070f06050a0f0e013c0504080d11030a050606042d1a0706050c0306011b060b04050703060f09020a 70
    0x100110900120f4004100d0640c01c500d09014001c2280c0c02c0c031819460300701c45914005452810442454256108a50800450350041035101c04a001d0140903504480d04210190345625000402b11700f8651040510900395101c0204007003402019408095618426210b0781c08140b80100282c049026406c005801000601688804184241c03c0194415044140000c1c2e11180f54056030440e06214000800d503903580102104100395007442182c0d1203c0c10500d820b0710845403201e80c0c0004819078100a05980b500c010070200050801a107072030600f0007000340050003207801028007540046400110072428800428014103100d0100c81c10344460010501070041d0101140580c00d542c00d94000d41001541c10004510456104040e05070620b10842079580025003000c2003951405851030010800410611403141e801c41881c28200404103804182010b20381481d07802003011164568115040604000c1120780c1940000700350f502405d032076810035466000d0701c2c0c01c81c001d01c04600003059 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 460067086 1250 460065836 460065863
    0xf0f0903020f011202040f0f1208040323010908180111060105040b0a120b0f0f07301103180109051015030c23040b091f091a0a060c 58
    0x100111600d48100041c1030240410404c0010307441203034172660028078600149641480000d00e4055940010003801440c001c1030743c40c903103446442e4412440000c003110f0000005a0134070500b09407500e10200b4100003004040031a0414a03d0780c0c1c400c18807a002158404d01138907156004030308c2c59007105000c40041580c2d1382050240001000507401203544070402c0840095422580f4200c03804161056100403a039003424481c171200982e0203000203440e40d4202c02000050740d0301c41840351070848219075480c0f411591540c244400c8401002d00c11a4904286030003034603d008400842c001c66000c1d1403d00c2454094132001e0032036420200052054101c1a0542c0e001c00d03c540202040301c0003c0355044560381d9070394420209041c40e0780011840d0b040680c0c1540341c581c10084512030140c0c251424012003070300d80b0000f04030701402002c41c1c010a060f585403400305156100c1c03180141801800401011a0b452100401144c40e2072040d441020322440101d0020b00c140450004030b03074844890400380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 460068336 1250 460067086 460067089
    0x61b120f07031e020604060c030f060f0311010c1110050702030d08090709060e130819030902041d25050d050a0212012904140c1308122a03190f0f090302 67
    0x28071405401c03000705900c902b0f4403095418284101e00040140c00c141e0400c1500d0751500c0001e00c21800300032410b11800241301070202c2c540101d5001d01c04001c503880440f041c6440b40907100c078040c1703040294062040b44920030795035402206e01030058581c50200c40c821ba5450070380e801035600780e014075804003018002003070b8000301060001416500c2031240b5801c00002108454420204551a0000130303113524a41c41907003454418568403404224050035011004020956141000104000201c07808441c02c1410042008640e01506d002400c3c0d818884190070415650030781c8941c140c1c410080d002e412000c86005100d0514042c03030140d11803024110b83c0c4c0c0300c0e5101c441d801901c076800c1a02c03400e07000b4004108003400c0c3c0c403d100940c1c0712912501d00c10840070289902e0381055419a0088001c0607a100ba200c06603003141c455004000c46444406035050900500c140e5450910301c8086a00403903501c44042603940d41707030f02d07503a008140c03030560b10216600e02c240b40541020940c113120a00c0076 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 460069586 1250 460068336 460068341
    0x1140d021e0627010e09010303120905010e0312130c030f0c0902031303110106050102100908090a080618070608131109010303091d06061b120f07031e02060406 70
    0x741e041505031a018032100340420540da100385034070b0340d0440c841000840d02500030b200c0c10b2a510030a00e40525000c0305100401d074128010301002d0140f000d1b504a0040f1011540c00903848640c1c040024400303070306441c3c1e00c1c50340c98014074007143c11b0451610000b40d152103094400010315400050340b1015030314540310342200743c8940c2e5060701d020000c401c01040080090000f0f5001d051141c0c0c000f9882222410300400303010381811115680e90519804000f5aa4002641c001c003000309480040c5a185910f0711300c9140c0700380840140c02030800d5200107050b5801241c1c451141c108c0c0a032400c00020000e03032041d00c42c550380c041c010215140c0804128a2040c64070480702d03407446851040a003600540004040c01002d07403044001550009041c0b01e8164186100c50030141c0f4196114848d05000000904c0b078001c4100c40403130741e1590b418058411030100302c05164107290640f030564607034100c07071a0100c690103a8000d03008038515444c84502000c000c038000e82d03822440e60141900f6119503030f54038003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 460070836 1250 460069586 460069609
    0x91505010810062d0e2707050901120e01050604150608070e0616050a050f0d0507060b0604030c03150b06041d04051c0801080c060408030f030603030d180b01140d02 72
    0x3582d6950300020141070072220214802c01c244c507203c04080b0040c6008111011031880e10384061011200c15014131200e90421043d00501f19091880d142e0700480f0040b109500340206904c6658103045000e0180441135002d00c0c052641a1307818040c032410f07144c0c0d1502e00d0081d40f00d528005540c150003c2e090358811b0704520588003004100c01d24200846a8400040008070405c2d14990800d2489004000c02001004420050784001d0418280b0303a00700500903000e44ca4002c0c0c031858958400404940d070752400c40f0080d65110040820740d40c0c59041072060500c1c60406803208902c5c0c2a07010300345140020a540c111941211101c03d070f41102e0455550041c8003800c02c0b1224410980d250b2148240a514540c81d100c0c16611040152301d0b00301d05914081c440d002c800e0080c82d0402c070902045001204076003e541c66030410b690f69840300c0c000b0030310398851008603504580c6031204104008050f66012055107000388003218003a600c03001c04c01a142c51030783d003543d407110241d0088401800e189407140d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 460071942 1106 460070836 460070867
    0x40605060922030e061201060503100905040b0619170d0221090613120f060c0f0915050c0d02011b0c0b0c0c030c010609150501081006 59
    0x180038400845003e81000610110b043e4992079590442c1c0c90452109400300d031035079680a0041894206032010b80e40026035080000785a6400c1c0121400f45420400010044d2181c20070004c981c908014510503556013031300300080501000c0e42025078072400d000608448011141d000f803d0034510108601d0b008851101e214180c0306880c161904044140e411a5595000c070740c000e21f0b100c019130b2185ca02c40010300103a8041116906910461902c01c01040c422000803040c151030103042400100b00081c401d1104000b0707903101034503100c2461801c1c1001e501c3d0180c044003c034241000103030700c000582e46800c0800300c65030030916000c40d48585460140340011700c80c1d41d0341c0090070001e0306a41c450f0b200800c503091100c8040c02154800082e10000f000140d5440c0911030140c8500c0c81c00d000811440e440002c0d40b54040c2c15403074890b101131100300300864104001500c3c0d0085490010 = true := by decide +kernel

theorem cover : BRFrame.Cov 459892086 460071942 := by
  have h0 := BRFrame.cov_init 459892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 459892086 ≤ n) (h2 : n < 460071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
