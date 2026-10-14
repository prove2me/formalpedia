-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3212
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:33.111581+00:00
-- url     : https://prove2.me/submissions/0e056bcf-70e2-4fca-91c0-2e01890f1f2f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 577517985 ≤ n < 577697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 577519235 1250 577517985 577517987
    0x106060f05210f01150f0e01030f0f02031302030613030f050a090f0f0503100b011d0111010c170c04030206070809040905011103010501200d26070215010e0f0601 71
    0x502002050308040508180c0c04aa0001c840b407089400b5107824030003c0041c0000d0403003020440c208800d601d803004081031005001001c20580600040c1850b40300c031580c1848900981244000c8000040215180d1604610035031401d003002034260b00a02441c004a0170011110250307000c1c1d00d0b0103480d82d00c141403070305201715060b0b0b01801c2d04004100b07501c0008104d01e0101c1207003a0007050302d10020b00b0068140010541060200c04c15401070615108401f401a40c000c080d410060102506a805036500e1400581e101280b540104045501e894034800321030b40c0040c01e82c0e00d00c5001000441041d0388500c0b0b03070b021a108500001e54420700902850001517070f0b90000744600b0740302801c0815005a90b80e9080d094a0701c2080b44990a880400103008559000301075401007441000b194115507013800400e034a4050000b480b80411441110589a01000c44024400c0301e0480102182920303002c0030007511140f01c1d0070031031010981c1100004035103e8120039680902c640c1c0d4012182c84c0c40d0300d80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 577520485 1250 577519235 577519237
    0x3030406080606070f12030e0105060f041d01020f04030c05010801060215040f080307021005130804140a0506120f0609040b150a080d0e100507050304120f170a110106060f05 76
    0x4100340c3e100104020400004461003882103e840c450030150b00c90a40c10036003c0e003690242c410ba036800782c0c5850304102860790340300144000540c00b99000100351028003414416020384d85d078040c4066000169800c100d0140c50010f0040b240114400d084483e1500f004580c180c4081c418107006900c00d13060490700b01d950f00180742c1c006109101c1040c10741c285a640e0603041c1c200701c400d040980c0103026240440b0200d4001d0075070080360340c1815499104181c0e0f94001c903006500443d000468245410225911503910800240000030101c0391140d45040400080074411100002251041c0d40410b0346410640344d4940200e0307101c4114221070366000c12030216002403520f0386600a0071a00b000030036500c10b00141c034850310300c1c1e51001c00d40e42545050101185030211002e003007007000c100d1400807440200c2a00d05441910202d108411803a0604008503001c41c0d1b4043c0403040f0400780313581c4011f00b50009240c94401522039800059030b402ca42803ca569a01c0307140046000d00a610781d566221300c3c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 577521735 1250 577520485 577520491
    0x1630021c030204030209182107030f11030a0804050c09190b010e0d1101090b0a0302070c08070b0301150e150c0c01080c0a1116080a02120d1b050f0604030306061704020303040608 78
    0x301142e200b04039140d01c4144000b08021942848c58001400c001415400149602c480009080984030a08808242039584c86884182c00c20001014046420031605004416442400800c0c80c080b50074851010750032080709400c124603240c078000c1000d01c0c950040b40340c1e00c42044001c03c0d800400c0b00b191038103810030504468450400c10011400b00305c07140c02501610f082c0c0340950300180c03a42440c2ca448080325006810044241d400290208600b00310320f01100e040d9648039440071075004003444255140401400055030144440e070f50792203101d28080107044080c545504440f400369100d401500cac2e20006440c15448501d04215150600c2c4c018400c0c600080f00420442d070040c01e85c0c0550030352500003074011030200d03008000c558095103400703000c508420a01e90701400b01001e00500103080c01004501c06500049a0030214050200030300a903662540c580c020307501280350034500100200b0a074002c2c8030208110f0300e150344551200c0d0141c0c078810360340500118605030624101b9134042c4401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 577522985 1250 577521735 577521781
    0x2106010503240a09060b1305010513061202010f170c0711040e0d030b180c07061b0e0415080f1e240a0b0303040b0904111630021c030204030209 63
    0x525124402511201c044a400c0c103007e080004580d410201000300301170003480102c00351410040e0502132620440000e0318150350908290300c0400c001042502e4141459598034013450226040008108802c0000d03d2124072a010071500221440200011140406540300c540d07030008441c500c5203030080d03012401100c802081011034a03d000700210b92810226452000c12002140d12780804c000d80c0542011003c000c400c054520400d40001088540d5139241284255200c48084022240c50391f111000780808070155480d8a46c50b1134000e558078401c04210101e0750080021314500300001c07420040308051045a030001c081400000320101c0c01c0a01340685050f0745111090403660108024002081018101501c80c09014108402c0f12000340584000d907200b00011940100c6101105080652010030b10b00e4041b04450700b02c3c03814030a80c0750300c15069100804c8009080d0000369680740920090080004a000700100300c05074010340c07000075004040c2c4d84c0480e0503c0f01d4680c226004002c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 577524235 1250 577522985 577522991
    0xd0309050106080d03060302150a2a08070b0f150105040b2208060f010e160507050c040f0603050708210c0336090708010902092106010503240a0906 65
    0x9400b825801d102c01c1300a20004259070383e00402c218280b1014440580008070501c074100b40c40d401014144000c4280d03009001b110b0702000300101c0110340d8000602030f4000741426121500c070318002c0300c0c00c02c06072512a54619000001502e414903640300b810540010b0350b030103003010310340042c100c0310b03400aa0b4649200c49645030070140c00a40012004010301d502001452a070030700b15508040900c060308a801216400020040301c4030401d9107260047d00c40e0701c3e0465941205060450425803d86803460384903060000540b07a5100e00c7d0840700580740608103032502155503420040d40c07000c2c201101c03407101d02034031b1b02e18400f1a1402c01800c0c2010b1240152071030805000c0d1003c40c12810380d4580c102d0348416000d10403c0d8200141c15444121741a2840c4000382031514020b08546130511811078941d8000844004a49030f440c0e900015528640c17944d440701007030345541d84e20351209001d480c1c000d01c18285003070b01c100b00e40300c0f00c000c00550f02c42d9940340c66110502200c000c0c0c24030034404d03a05030fa1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 577525485 1250 577524235 577524239
    0xe030a05030f0a2d0e031306092310120e0705030c0409110d0c03171201050609030a11010509061303030212070f0209060105070b1f060918020c0f03030108100b04050106020d0309050106 81
    0x103042c00140f400410642c0607d15481c18400c016000560a4100041d00c401003203c0700e030310100101c1c5108000e2401c48040354180d15114040703982e0305d07440c418884040d0401d555601e400707000091241c107940e411410344002c1e045502c01e20084410205024202007010711101c885800c0180703284140d640521f08109002e91640c81b0f0980569102403100b03100c031000540020703542110b8000d2405020102c60680c500078010001035550a008030018080741002225100c440c1c2c00f4900300c8144c1e0b10050041c0c0d0715104550720440810300f80c1d10003030300035002d03c0c4190301c100da041c1003c50340341d03a500c100111103e0040c0d07024400746103001816141801002c200c0d04020601040c4603500c26200c422800003081054549805510080e030300c2203050140c449028042450311a005480140b482d000044e1280c0003c1a42c524245800c109210301f4000000003158854000c20032625212480720248181e101074024031040b01c0d0240314038001070304440c2003034402d144240c01c400c000724090400801c10036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 577526735 1250 577525485 577525511
    0x8070f020d080d1b051e130905060405070c21030225021201050c04120c050a18150b09010305041a0108030a120612080d0e030a05030f0a2d 61
    0x820701001e5800c2040410b120030060840c3c0140d000e854a400e440d807121803415480035095004a04450010106d2401202d440c4a0b00d0001d44403108401c0003068031550ba2110064002c06054034994011403c080020380f07124080c81351400c600c0c1e07004401e0312078032200c240580c01801002d0141f03000c054003040310b008a0306620103241806a484100040e0054084c410000710103400c2804084d140d05000c104080e40c9100820b4030110303044855880f03500e2a051520180003110394010551003140b40340c02180d01d4001c01d00411040c01100020800300344562081139858181d4400c0108032003003000000681d500c6500500d030801d101c1c01c1c0030046d40400c0a100c0e015080b09070843e00741640042104055107900124180702c900c00700404002590600d4114182c3c030110701c10250088400280d5904900f400c0e900507000030070004180c07501d820320340c000105190f0080c1c03180c5540109a5000c500c4a01e1a841110000b20340004c01c0311420840c112031a600103035400310301d03041030b0395080b0341c10540d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 577527985 1250 577526735 577526749
    0x30e0d181421070b19030e010c080a091403070b090d030b030601050409030c021807030b0906100e060d150f050f0a06140d0908070506090a03050d020f0903010905010b0109060c0c0308070f02 83
    0x9141180c10700030005c10742c180102101d40004812802c2e81c14292140456a08035400c183c0115081002040144060074050070b00f41050080b505503200024820050003540c402c058006c00c0350f01c0596002512000084056412594085a00da0040c03401000640341560100204030320034208501480300303540020391400605d101c20803401c2e006c102000200c40d45485148044042100c1a00c05424884c001c01c0b4001c140c002440705100c01c40c51000002d44d078030400d80e42d001d150748400f44010741c600000d000e002e81c40c070310850074440c16007a0046400d04c3d101401c1c2000c1c400c082c1c040a009860040102d8006482c04d9054070840310401665091003c980100e0580742d0040090720707030b940d4180c94000e2270080018003e16440d00101400320000e94498202e43e079526441c040580c660310b54902903c000d10854841640c9980391030489004c002064010100401d400d032a04038a9030764800056840301c40c6003500401541c2c01100500000d40e490024003202401800b003000e01e4a4160301140031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 577529235 1250 577527985 577527997
    0x20040b04020a03050901150305070b0d0b0607030e180106020309040c03021b150603010c050f0304230d080106050307021905010f1503210804030807030e0d181421070b 73
    0x39131180f0030002c143c0700c24060b07090001021105502c03000c0c699100c150b19401c244c040c00008481c002a4811716840a41000c02c0ea1900107000580d40c1199140261420321a445014044c04000c1c48040e69042080381c00d41c100c1d00140c01551400001e402004010310200c42c050741416401e1010094440000070640c82c084549401821010071440d40000d4a03440103052510036130604944007026588542a945c241e00d4502c1c2094598846181c00304041001c001040000080c0a5214843c00000034844881c00700681f1840c2e01c690b2201e4088030380740700450340d010140e404501142000e00d002c5800303044072402140000b404800d01e002400645886603c03840c0c0450f0100c0060040c44181e00b4200040b01030070700b059150004441015040c540010402f80500802034001980b86000c1d40084031002c00f00f40c15121482e41c81000a809101c118518900d9201c1c440f9012030082264004076001180082045000a4041042015000d40c1d1007032801c55004041d400a820050440503284c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 577530485 1250 577529235 577529237
    0x30c0c240b04091721040b16110601050f03100509030901121404020103051332010e0307060926180d020f150403150209010807080420040b04020a 64
    0x414108041104040d901d01854441c0300314545150480040c1d074610780c818552140300842522200d07007400f14400780404120740d00c40c920052007004200002e0600c11440fa2000c0e1004880456860004885440402444400940c05100148211700c2d10018007852140001d013212a1100c003c10400c0603640705032540b00e8658404540d1a880f03603000402e4a4200c5040d03c2c007008103c8140150ba022508080c002038103060341c0741d010605a861315825030301c42d103420051b801090070344010a0b402e10308103850b02c846a801d02d11100307101018103015950100071a01c2c001d504081c0a52610001409030f144100c2d400700382c403c0b40410518040c04400d00c13100c10007012640391141c014290f42d540206000700c03481060310907070200050707694024000e0b07880c078199000c6101e4071540081e046140710340c0d04040d207030001d10700702d03991068030f15001003901402c207903104919031301e506c0c00540d140d00c4107580c028007910440042d01d00f005240c40b003202018200500200b4101d070301a01140c100e90020704460 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 577531735 1250 577530485 577530533
    0xa1107051b09071d060f0d020a120b0402210903040509071106150102101508071410030507023316020d1b020d021306080d030e0d05030106030c0c 64
    0x214031440d00600c503a41c0f03c070303050509940b030489074040144040300c4c1c01491440303a9000304061410500a406030707417242c0b580f801c0455440c0703d0707140301502020302c05560f280c249040c000030f00143d00303043c0269005581100000080a110b25803040704036000200b0480461105100029072039840d454424003500803600c9416402048115403428a10001c0109201125200c0300480030707640040c03065500c1020080010700e011410134651040c018541c000900d81c414441d000c90860150030b9045101c0004a400440b6180e5102084d003d54108940d08030158000d88025903062090400b41c0003403030000b28422201420410b0b00d5a05500d0580b0f044032008c815202032034076150108a00003442c2840e007040a40c00f00102c50318142d00a242600074010344040310a9802c6490b070450212003060645c406003c1940c64802155031a01c017142c40c100007a0428084d070841d1100464560710804076941c803580345a08002064003d49038843d400707000c210000d02d80c0000724808001c00300d0145844c1b2030316 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 577532985 1250 577531735 577531783
    0x60d0603031139030f0f0c01030b0901120b130506040305180108090c0d150203010803070507060305061804030c1403270a03031103040306141006030905060a110705 72
    0xc2407601c45a1420659244074103103c811803c1a40c40d0303a0414880803480e6000412080c1e00464181100c0300d4a0300054819101c900a241e58040764000d0003540030f0b64204903105840c4100082e60000307100e0307620203207090000400410850208a41e211649584070161640c25683e561f2900c0707411102640040c0001c03400384c13170b01f1654154000240c07000346802c11190802464842c0c0710b001074032482b489685100c40300780c204540c0d04410511130240c031174219100d40c0d542c00b82c1516548003440883d082e0180c6540421043c1c0a03110701170168802a04c580c0303030514a1513148000d010080c1c01541070201cac0d10840000100c1002484d803046d007903100650b80341e06102c0807201022450095484603500781d95600602e40d2960508041101d0f01071a00601c410741400c0b41c02d00f140704a400240060341081e10301c0040078001070070325008000640c541c094a03543d400d0f0032000c40340303144002416a0040804584000c5103032f040010108034402e016840d0007590f590710f80c6000807440c0c0901260380481c800c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 577534235 1250 577532985 577533017
    0x30c0f0807140d1d040f0e0c03060c0a020d03090218040c0314241510030c0e040204032001090b2107110a060e0a330c050f030402060d060303 62
    0x400003480b58100030107000d0125080078003141e4099010359545641c000e0750900315620342e0051040030743d40700d20400184400b1088140c40d0040d1b44456070180c0b2464011503410100c890840c1c00d400056805401341d20b41d6504110040c0116200603030380981303400c40f80d6880c0e8070381d1003141d4061403250541c00c4000b0300e90300c0c08498400b040541e01e2600c1d04400510000204840141102042020000c03a415558820300c609a1902c00c0c0c0792a4207c140400b0781c554480d0107500c40d410016058940c040c0500000d010807041e44140d00008002007421985d02c081032004010f000a5076205041c2160304680f02c1640c5016078010500d10140c40c2c0d0f16000c4624242c03168211240c00810310324000c1e0340843d035001c00c07039510000c41c44018400c86c0e071010f020100a4062080e940c00c40e41c0b00000040d17140ba0055120b406010000607000c202c444042c015003014580c6c80381052103112a00d51904103040c00c4501d80d000c0e04003d1090341c00050070440100007840310b03c60000914882e4480d0b505102e60619 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 577535485 1250 577534235 577534253
    0x2040b0d0f0c0f051209070b12040303050603070f05011809021314090705250203030318060f04021e0102100207080421050709020304020111070e1f031509030c0f0807 73
    0x401c03001480700c45040c81031010303444012214005817415203420192180c0e49028070304803c0e0784c000c1607802c002140700960020290030700e9015131300070756092015445080c01c26485844610410070703204030a04003080254020f00d44c0d180c203540220603d883c6240d0310f0191000307aa03c04c0c0d4407880b81d0316001c08107000034010020007140606080e5034410940ca8041e070003a01030300c40c079001403034540d658090410700d442039010055140c075805400c0e6a05d9027082040712003201d100800c50b80c018000d20000802c500182050381d8032071070300102030542200b0000c1030810050804580e05046000b0340012450301c1c04c0c2400100710700d070b1056106582d221320741440c82c044100c103080007515a211911608002c104000b070f51005031402b01400507501d884500c0181d171b603e0107141501c4401d01420000040030050024014440c0340010044c580419840c0c0105107005400e001c001e252191031810040c9000180e030015880f5807082c01e1811409225440c2c4400c202070060b422201c1c2c1000061610401940749 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 577536735 1250 577535485 577535501
    0x406080f15010803070201030e0307080409050a0612020f0906040b032a010203040f050f0d021804031b031b050a0c0b1315051602010315260d020a12020102040b0d0f 72
    0x20110710099414114610b8a1303104000010703040540305c00c221a1110740038000c40e4a03903548450420341e900d558070300c0800508404c03204001101d24002c000030f00c11018000703c0b031078107a00030071180ba041c200714100660554090601c82d0404c2d500c0b00800700c44e4a0410030303100c5140401010188004104180300712003000c40c01c5690442d08180820411211448255410b40700120f50012041e111500410065445040083d60121101d41340b03003140e034001d906841c0158040d6990721038582a001c880318050541410041c0044c420858000c94447d052310303824000c7c0e1062043e911510303115101c9800d04401c90300a458190000200a01e0b07410390543e041d002000c200034091509002c1001c050b11391b009c3d56124200310985441c1000c2168403e41c42102508061440410700c142c0b240c44130a08060900703202580c0301c403074600b4444a0030000481000940240c0d005100100807551032404050b0b212840c0300540d07409010210312402c03504040c00c1301841c1d06000240d10041d030014001950040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 577537985 1250 577536735 577536763
    0x7080c06010816121a1e090705010c06020c07030203160e06010c080d0c120c02010b0102061b09120c372301090b0705071e060e0f030a020406080f 64
    0x1001140443d054004000215110780080da0f00a400a082080d0307115081042818032003d001d0411a42100301000f00e80c8103049400805260b994200c00140c0c0c406090143e640412200001c07003002411540003081507015410a803031303004d95243d021034501201c0c00300c0105480e0706a0003e0180d60458891264020b50928200c11741d8101d51303c5100c1c00f48580785e440f040aa4460341071441280c00f45000c50064100303410204039070317000818024001c12040e91907034018000c071000719503145501011004259006000c45103030240400c200100200d000800b03a81c180609401c030b010a03541d102054040141d4042165001081414904010509100c1a018111841c0800d00140210b681c007003440185c000943e060300030403c00160782b10810b0ba8000420b075180003401e0001c002011881c0821101645141c004400c5001d80d4562005818019031000910344401d80d42e243c03428080380c007041d00019058510155042c1c002c14283ca14642047d1001e0348040408a0704800405c1014800814 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 577539235 1250 577537985 577537993
    0x1060f1e0302010e04091103070b0c0f0f07060822080405090703290a0f031b0b120a0b010933020c0a0b0c030c0712030248030307080c060108 62
    0x1c42e0b0019000340b82c0d8900c2c045c0990340d034203c03403400c201c102844c2d40c00640d0010211441c1903580d42503c0c6441e48003007400390382801070094000c0d0b01500024003050b02094000076220150600c00100d0307901d8001001646500c850160400746410600c607a40380d010f00034055540d45509000c144250080701608140c1003500d080180011a22000040c5000d940e041101c14014001c5000156800f0b08030b410258048804503000030030440c81010b030403002c2070420b04c519042d80c5d0716032103c0343c140944480d8440e0300403420300080729000d8992024045a105051460000b80c8801100520f4a41011003507845411805480b0b04a61030101c10a070720226880106214038801e0f02040000100e8442d03003450260105288007095018401e964129501c1d0084500c015602c40d0309246810700b4500940150082c038450401e6240d0111601881c48206010046c04500c40000308050700190f03154820407042c40d0030900626030307082c00146081401009069203400d9400c0900d030905006a10601c80e03548 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 577540485 1250 577539235 577539239
    0xc040905031c1404050a0309060f0c060504030e130e011a031e1f150b181314040b1b04141e06180a05030115060f020309090708160806091807050301060f1e 68
    0xe030161400c000207511210101d412b0b256454141c60000402c1103803540280f05030304042e040c80e5140e2207a482112c0c0040203100314443e003c0000d030710404840c0c2c0d00d50190400f02d0340088400e59003c1030070000d038440301115006142100c221001000c1040101c101036100c8140204442080c0c59000140841c041c01c4e526114100d00d15a20079030281c0b295600070151018980b60485295101486a104041e180b842c0d9103002c0c80d004070303c1c5004442d61500040e107070500340c109a09013000c1e0350039030742104208000403001c0c4041081d81083c030810003c45198800d10002580c44000c090315440a403206d042a481d000001080101c0b13106130030003806030303241200c2c0c8442e40d0403000500007203031201c0c14050b007000c0d050b08049040d846510281500102150b0600c0350f1103500c810000d10840142c00f2030498100300d410110b6100405a44042d8420070002c04600b1078101c41c600c44164900d40360465942d950b44602003401d42c0c0d1544c0c0700b0690301000c83d03820000b041c2c903018000c403c0380b04902d10707001d414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 577541735 1250 577540485 577540487
    0xb06030d021f1118100c0b0402010815030d030c09050d0f11060403060c050d0e061005191d0405010b0d0302030f0313060f0e0c040905031c1404050a0309060f 69
    0x418900c0070702080760104001d0001c408030303648841d41c101907218103142d550084004038624013000300c2a60f4010002043c21301d2019108110462660707a010565242e1a01e0315001140c1c0d594028200007040742e000d600c0488035035010490806148000e45000c039140121039006171545907980d00c264000c070415031580002035844561106110f030300640d803d41058810020500501450708000c1080740303020040c5003a6900a0058000389201c2d41041c0007011280306ca090702c6034400c0d60b0750481c0e040000d5041c0242d1078460200030005032031042d401402030b03030b6620001c030079030000c01540341d442400d0007800184502030040644c0450140c2e460000020b280e139000f960303071240200307029400354048082041c54031000103180005170004010310a0146d00289800100021031400d007403440788080940441c1401d00481a1450b002006141040043c02c4440da200480d03442e1442c032140d9684400400e140e10300e82e21800340d03000300002e04000010b440c0103007245500317400400a101c00c800c2c0500140d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 577542985 1250 577541735 577541743
    0x1003050d141c0b03070803190318030e01050d061d01090c050d1e0504060c080108010621020307080a1410051308090f2701090902090402100e0303030106030501030b06030d02 76
    0xc628200030664000c062424460001c0840755003ca5160080070f030002080c10000000c0c0000e0544c03086200011029040c1c1981128050501501d40c510119020004079006240091a0840c10705006103450b003c1b10341c040449403e03806c032090102c402003d2981000c4074840c0d55001d000144c41c20032414910850103003443c022160181e002c0d45d216108003100c843c4070020440c1c09403803264107000a0405180c40030203030400303000030b400103005400000f407120300501854040b10494bc14001c0104051000d0201d1004151011380c0c2512410710000b0b03070340360b0030400f600815024556541d00702d001c0c00d041500b01040030b8095565541031009001303126085031611300d03007168460310071507440c4020804611103d040d004240d034001c400b0400d6483d902c0c070007801810000c0c0b04c005456a1683c1b24003c2c04100c45621070080cad08003082100042c014100050409e040c1a21801c1c58081c1865180c002445c0d540260040d5000a071100010001c0222541866800241c101d000e8000c41d03050100095817 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 577544235 1250 577542985 577542997
    0x1a0303090105041e0e07030e1b06041503140f25091413110301170304081b1516020109050d03270b070602040f0e07090506071502031003050d14 63
    0x1c3c1d2404070151041c4404c0c0307a60f0326001858003a52440322842c000b88050001c140308a07001c251800741d1418651030140c501003c03451002d005000909207801d013104254144214041c840a165a40307400c200d00b0001106142e100c0c0d0142d00d4641d030903182c100ca1030803056140350501e40c43d1012400e400a101038020b11510251452440c050b095100e10700300060004405007241d102a070720f8980740f80300c0c1c01d40d6000114141e03406105001c0c460b600311041c041e03407840f5912510685030008040041c04010001c200020441c00a0813104660b1401d56500c8665122004884d12104140342c01070840d40c010120400500c1d04582014044c50182c50140c1100504055000c0d0140303024034090550800724901000303800f0483e4650388541c0f45190400c020f61040c0240c0707560b00408040080c94090403020f05100b010980c4e50b1402c1c0d00d10308018000070350003c2c1c10448007884a03020f01d810804180c4055072090000c000c01800309071450034614142000a6028030801886e41081d007003108600c4100d540b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 577545485 1250 577544235 577544249
    0xb180921120a09021801030b07020d020c04051b04080607031107110d03050c0a0f1b060f0509010203070821060303040b0f070c030c0b07060506061c021305131a030309010504 76
    0x4019560360070300e2002429190f030000e60150074041041155051513103668140c0b407240050080c1529040c0c4243da4440701703103136500b0069103c01001d900c01d0a0a4222541111003c01414824200c5201907900c0f50001e0300001071a61150041152207076050003124038000030601041d291a00944030000714071075501060703000303440303410040741058400c000b100c0001d4411015104150325038900b9650042800c101500c4590181022010003124480c12208a4584d81c40c0c07034604098507902651941c00c0144054150300048c0318403400310b4041c10050240c3c0a1085110610080b802924071542c02c0c050102070003540140720500400c81144111220000709002ca00d81b140194070340840d9003a440e0b00001c0489140c3c180010302030303405101400070a44268418801a80e0741003d001c0f003405001c510100310014107002d00c2c208409035009110298640c80c80c0c400030b54983d0042140e811000d800860b8080d5219903500350041201d1203040002c0046000d5450400780c10002000c40c02103001c1c101c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 577546735 1250 577545485 577545517
    0x10302031306060f05130c0e15121501271206020c01020408030a11010c0f080a020c0a0c0f05090609040b06010c0f060b01080c0c0a03050a02010b180921 67
    0x808004841c06103910550b40100103104664940c06120800e030b00501c240c5028002c0140c91001c0681039001d20540c030822030b034070059040740742c00400c02c001e848218014200d000c01c02004000840000e0018800e0300f840941d07040d41d00901000410500442001410440a0a00480071006000740354000c41d60311141d20b0381c003407080382000c030003d1081070b200d085190300c0003c000404c0304010000d003629041c0350311107401f03815810004c0303800d95880c2d06d00c900005a421207a03407500313070140d86440d40240344503074018200988140514035112200700180c81003d6000c4e01040f9a180d20881e02c8040c20003540c610489090000105080c9130002d8001042100701d2000100164400c5001820b0715400103c807003076060041c105800144464001c0303030f001035810000034000c80d031840121500b102d0300c00003c1c48806902d40782120b241d00714810310001c42d52148000300c1e03980d031010384044210011030401022410041d10b00303490606c00707028416076100790500d000b1340e4041003c00d6900401c4004040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 577547985 1250 577546735 577546741
    0x1a070c0e0a0212040c03020108010f080703170c0d02070e161d1807031b0e2808030408061905091b040f020417060c0306030a06090f022107060e0f01030203 68
    0x1030042d01501814510b00f40c41d40003040103100070800fa100441c0d000303072101003080c1d0300c3c0c1c20818007040300760095104943c00444104000341c007401c4584d05450350300821509010b1075105d11801d1404000c0d084d001684050000d00c42c007142c000300715030805030303021101e40025030529001d0a08805146949402d00510800100c15110740d0340da804036502403e80ba11151400b4070018009101000705c48001c0c401c4840c2403c0e159002e101c80300c514800c001e141e10f1450f8410f101c0070005020398042c12820f0907a1880015600d20204040c0004e044520040d103080d181c00c050002042070810b01c40c0c01c10328209002d1055803800810400d0514144258070240800c110000c03801038040c03000100142440002c00041001e004550303802c0c0f0140d080180d0300c6a072a201c3c6002d1290100b510300719816004000144000350701907120000161003901c1d9110b040d000c0b50000b69002429509001c01420184c05c180204c280c02d100343c0f07010345100d0400c00041841e20b8041159156900c02ca207051582c00404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 577549235 1250 577547985 577548001
    0x6060c030e0d0b13110915060c0c2710060c1203060f03061413150903020a15090b0903030705030a05061c060b0114030c0d091e06061a070c0e 62
    0x10305034080e8210103114980e08050001200789440c8100c1034030910404000c240d070700e16245041d1806182c410606051f506480c80411030160b0011032603039070600c101000d040c2c2c1038903044c000104d0425030485004241c00341c0031610400090050595981c280c040c0703c24402560804102c0d5140c2e504007444411a0201410580c001e0250f034111903071411250200004202c4980c1020305a010360604040c0c1c291101c1d803524641c1d44a05e080105034034541d2006002000140d4040c00001340248110340c1c02c1c01c403c2e00c46000c0e9594101406035030075143c40201e0240401101e01c15000100030000350302d10b29110314010054000507200b0032005403140089481980d45d500a82d0300008000540880740080d0715015005003030080703107980400c4950390b80350350b1400003500f80d0f44952003005400d0700d0034a0240301c0d0342c024010503000709e840c0b2442c40f002941a050304680214290b10030400026400e007403480c0c0c0d5000c00419003106050000c1004040c0000b0017502402c0111001d01c0410016900c4600d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 577550485 1250 577549235 577549249
    0xf020d060f1805071205042f010f03020f070204060b030f0601081b03100e09010615020d2003070b0c0301090b040e15092a0f060720040f0606050901030506010306060c030e 75
    0x50b005d081401c000502c8140998691440054881a240806584447c00207080c1c00f2a03240a180c1c00f2846404803210b546009800402c40c0d800f400140341e00e080e800e6030000e011100d040c0c020408107800482003207814006040310980200c002d0030300035034034600b1500c8542525828200c00003040c00200c0811492004410f159001d07100403410704140380b8140c05a540205014441d140040c0070101854122500100390400701c1d0500b5616040007085034407910b100c2c01071610410b44a4401003201c440480c60840c41c85e40035007000c100043d525450540c1c514181c5402501300d42c0700d20b00d05168045880030002e154414070300703501c0e2481d1060ba9103004070b508000b800e1440c0d0301c00d4242c40c40c4080384d03411904c83d03400141f0012603d07104408020814403007103000d6500010086040500d2040c212007140d50408441d040007040490580c0307100c0d4510f002d598965000d83e0115030041007164040da01801038590004003031800704821032528000502010301c3d16009800c4c403409503000035980d1103141c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 577551735 1250 577550485 577550507
    0x14030c07031b0314030c010f180b090c100f080106050a05032a0d02070201110c03120d0213091431031b0b180607080c0a120f020d060f180507 62
    0xc131205501585600c0c1c0e40e8996011a407040c403d546041024103803401544180030700501480e01c8152000e034595507070f10407048044c009803c1880b0f24010306c0c4081e41c801e010411f810201d962000d440d5800b5107006050f041c0181c0021091010501907060881d900c0005d13a0360042400341d00d42040f031003600d6002841d208200860980000014569000c540d850700108200e5100307070f9503941c440c0d8000790015195041d502d0034640c547c0041c0070b946031050210001c0c1504941034607005140099116440201c103150340e21000215494283c201205030080c580e0581c00b124103150350b0480c1c1407404a1884030014011543d4040c0781c0c9040d440b0a061081491034201041d0402ca106110081e06013400703541c00480d40d40c04516102e9011320f00801d004500503024440075100c1c205140c542040d626101d40201c610041044072002031007514010750302070f4001d00c001c01d007001665420301240c0003003664080d070000140300e4070140080100c41c0d5103980d86000d81503968000185911034a00c2290405d00407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 577552985 1250 577551735 577551743
    0x902030a0804050307080601050d2a03050109170a090b0d020409060e09010e0a080711010522080c03030901020601030602030406092003010b0d11090903041d010314030c07031b03 78
    0x88224102004411402002a144100d04075600565108521a0b4685003400f40507006481e01000c6400504041d10345103030801f9186074000342000080bc050284401c650040d07a80d0b81d103c1105805124804d083d100b0305180b070960b264500020108090144c00e8603116104460b0400500c00c1c2041440b41d06807006818500b006005a9680c8c0481540043c0c0c281c0d00048a5441c0005245001d2400039100c08255800080a130400e02192030794501071076901842ca040c004100203401040c401c83d1802580c0304851024042c515003848201494100ea5020707a5020b41c0c410030604001e42e030002440d03411241d21000250707403a42c8a2910318041c0c8105400204180ca0303902c941e88042e10340c2000e0111407507054008003c040c8c18501006140400c0d5000500004101c1c013121000d400d00c941c8142c0d03c10070700b0003102c0c0b0f42a951480031104140c2d0130f2040f450b181404006000708038910641c1900310403108011030408060360348040d01c03403080d480005d01d03101007244006880004e02e00140011504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 577554235 1250 577552985 577552993
    0x80f0721151e080a0b010b0906040b0316020c0a050a17010e0712110402030c03070302031e15011b0804062118060509072603070b1e07090e1603090203 66
    0x5a0080a00070300e601ea00c0e10408503462440200c3c1880000405a07102070304020688541d91030038058000c01d0380084111504030b00c0410001c035100840d14000c5004000c039115802800015030070003800d18481211103413040506c01c204015a0b991800050180c3d000c3d40d42c91095203413003a55180c0105140e180d04900360081107000954203610004244c07100c0d001e1400e5201a40b42030b010041284011214401262030078404201d070303a8841c0d4003440d8002003002804c4c20340c018030703103802d480f0040484180e62a2850000c1030707029542d1100c4c10009220500790403030300c003000c80d50320800349000314012001040700301d031090004d0700c110300051200029008030802280d9440b00318038113a243c42c54410b44240303040801181d4820000610031040322032640c60403e4021b4030381d031000c50f00c08120403520502c4c881404408040346c01e0010150103110f00c242201c18182c03000c080c50b200040018001d00a020012208005d0800b190f0031144d0321554088032000c181c50f80364400e0f00180a080340203074140c4a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 577555485 1250 577554235 577554239
    0x1a01030c090302130c08071b060b0d021f020111070b071416061407020d08010b0f0f0c070e0709030302060402010c08120a1e060302011d0301060302130c080f072115 72
    0x4c4a03440840c4440040d5250300f81d540d1498000e5480da52800a85014444c0b21244400402e8a940c001c0000010081c41095444040d40004148010041c019000031002403002d1071400e80920510344140d9141e18101c0c20319206884040c0706c8500180302206001b0821880218512040c040700d20394560786503090000c1140d0308044c4018100c0401c80c009910a80002c6500c0c1400014001604c07010750351030000907800c14200e80025040069007881880c03052001040328412b210191500310078000007003c0070b030700d0b00c0c0c014030420002034420424002038000a0010950200750f150f030160702820200351048240c07501d40841c0c03180c044641e0b07080c400b06042c0548a85580c002c80100c200302c62000c1450a0300d00201c10031101e01c0e10009000c0382d1405d000d429160b41102110008120050002540a50700d03004200d10030458040001020365801d440019980c00c184450b4100805149901c080d240510300074103815203031001103180143e9030312209192005034022a40c0c5240c0b002d0880da0107a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 577556735 1250 577555485 577555519
    0x190c0b0f09011505130e030d0905012003010b040e04052803020c1002030409050405070506120106140405060f0c072403060b030708060d050a0204060f05131a01030c090302 75
    0x4030040d90319030002c1d42001a0441c1e10f80803d1241410b03680d000709103507441d1500d152124001c0622081c10f040501050081200c1e40a036071040d1404070303000354004500e040b0504003020081d51103071142c400c0034038180010b0080403da201610203441ca40c0070390036203944943c240300345040c048100d0b903e0680130481158280c45075020900e50141c0c480d070221080416644200807240303100322201d100590080c4400c0210362182d4008640150260080d182059141e5000c10301603440450260005d88040004100541c0c0c41000311441c00d04600401e4101411304002070300500c00d0b0b05000035400390216031f616602c5820b00440004040000c4a281041c202800b004401741c1410302e001c0c003017860408001902200d00089070312507400380d07846035519914041000440f4004a0050b00c42d0f1081c0014800144c840d8451a009003a28400386c000a510b88030401c441c001c8184404079810b03080003410060900118200307150880242070114180c844000d00304d078071002c50350000e5404110800005540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 577557985 1250 577556735 577556761
    0xf050d0c0b0f09040f060509070e011b1718091302061e160303050115030504110d080403080f03160c15050a140103080904050f130f031103030718090b06190c0b 70
    0x7c50341625004000e980d416019102003908c0000f1a022482c00000101240a8000d01c145628070594047e840b401360040700c00c01580144540108102038401c070441e09252010b0540c6c3e00200d41c9010381d02821099011071603d0060360811071100388102c0340354001c005500c0035110a84071100200e10429103d05004018000a00c166110b007030042d40040e540c0c40c400e00400d489150050b1f801c401e506009004d10070307500c000311001d64a100c400e000120009442000070190f840e05910100e0b124200007030195100611803001e10107020905d028440001c0217000718a0303440ca994900090165100403000b4081d11480d403590240300f101200110030840501d019105a00060300c1c10050340c2c0d05c03107404021030380c001e450818615102e0040380700042c07490800c40c00018400d00d000e803014a01020768a245403c15a41c001c0411003001040c0402c00c0416900c500510341c07003005004444040c000708100c2c2c03140541e1403208480060081d83c010340201805030006512080400d42850208210070391 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 577559235 1250 577557985 577557989
    0x18030f010f0b0a0b030420101107050105070b0a090206130e01031a090a06052d06041a24070506010b0c0c101e0e030f03040f050d0c0b0f09040f06 64
    0x156524280c2c81d180981000c0c99150240d4070411609495500e89880d6812603040b4040e00d02c20b0701141c03080c0920241c540110000064200341c45071000030b8090020942003140ca07401823030411100340019804140401c5c2a81e80098011340006410007040c00420000c2c0300340c50b80c1503d581c8005900241600d507207400b0ba0304882c01811080d03502400e0082d03015154005488601c050b41c0042e6000e000f0800030707032100d42c0100d445081041ca400561101c03d81304801104640400040d48080001d10301f444d0184158184014042c9141d400319a400100007007510441e1140c180080200302e00042511381c115520300d9000002c6803180c2da96884070101c641d2000a0045281c05120100022030508040d000c0d2940b60a4681600389500e660201c50200c0fa640049030130040b0b44050303803030381d41c07403d03c80022082a184040d40e40c80f414026001080c16945d40114002d0345581450000302d042c0c0c0d2900303000c0c0c070314800380c00d5683d0001541070007480c0034003060380d03521a20342800f4503c003044075846002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 577560485 1250 577559235 577559261
    0x510061502070b070c05220504081c0e06070c0c170307031205311208060f0909030904020304031e0f0e031f020c030c01090c081606021218030f01 64
    0x28a190311003081252130b001e400310042c84103507400702c00e00c2149444800007505030154040d242100440c2c40491090369820348050f90b503040300144801c1450500101c031003403a81c00100034442d5040c40c01c4890f6650500411100400c00440d1040e000c000c001843c460040c0310142500a140024110042d226408924106e021843c002c147d441a6030482c051944207020150a000a0382d60341d200108102c1468110107960f20601c401c41d60004a00d1a107000d1b0740a641e603a254158508042440344209080d0101c1c3c0c8103030303030403002c210170381d04008104c85c41e4007416140543c50741c0f40e03468160f584003031040701700410780880032403090503d0380301d4032180c088006540c0b4000160302c0f1400f4591200110011000b15000701c2c800d850007050b140d0000c16038a500507003264075200074051140e08445844900701c2d80611071101c20001080200401032018110412100300e552030004c0280d5150202c407052903030b2102c04180b004030940d50500c661031b8001c028055a40398820003071090b00038451308000503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 577561735 1250 577560485 577560493
    0x10060e18011409010524070f0803150a120203061f0e0f0619060c0f170d0504060c032a0e0a080a060e010b0f01050309071715070c0c120510061502 64
    0x560385000c007040121041c81c031b00401c1c07503e0200c0055041c15802510140d40b18024400c032030b00080c0303c2c0070085200e0311416142c401c0c415610400c01011168542c03041200710040300131403000d0795020814903080104003071506c43e000f1000a10240d200c0c00c541c0550740012035501027000e00c0d1010812640308507000c5031006580720003540c2d0610584041d000d04000100e089841000203040030040038900d07409504070003203810502003002c40300d80c040b903841001141c03a90244800c110040c000c6e01c180b04190304080c8646540784090340183c2d446c14019501d042c45410008070054002d004100000d8400340c10005e1154403052850394440b0300c00012103030503103000c040026540042c81200320409004007403140c6005030500441d000c0d0030207043c60b56640944940024550500c00c4180340302c140b0b202c0a00350142d032103000004c01e01002004101400030b54054200094078001c004400c0d20340d568007950300000181010b900c1c1a503002c0640001601d005000304190304003403202482000c10707908031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 577562985 1250 577561735 577561739
    0x210090c1d01170d17040f0501021917070804080d060506040902030702101b03150f08010e06070e0112020d02120a0501140a03051209060d02070804030c090510060e1801140901 77
    0x740d030340ba814140304900050407004001441c51420003000d1b0003500030b0400d08891070154030ba40c2e08a038459824498045c032060828188950041340c0d04144840722102c169240ca0000005480c00400a00040803038000003442281e03e1075030780c0618054a4040c03d556165600c031010540250300076141d46001d8415850b8007070a21120b4054204100320700d00708960a500710342d205501918002e410391003609030300d00000c03a08020803001000284108400421186180d00001d801d02030060f02e08030070405200102001642c20941b4123039101c44400006070358803444d10131034009000d50158078038601954030501401e8031554000c01c0c180d42e03191000e0145001641c0402c45e240c4d0302c03444018060341200f0303032203041745400340c001d0441c5080103000f0918060050b04014200d0380f00283c00c892800021809000340940120b1140c040c0079400c104012906000501c40369110642c418481006030500e00c142c150b032581c900b20656020580c9000c0820353f113461400c1c0c80d11140c0e810540c0912400c40c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 577564235 1250 577562985 577563029
    0x605040c17120d0605040513060507050f071b0905040f05120c0606060c010b0310021c230601020c0a0909021203090a060c24021c0b010210090c1d01 65
    0x198811041c1e050000e09a2440141c10011140c02003558240300641e0b45600241940720b60107424130510a00848501003661843c002d0b04681000d800001084410300181c156503468200326503002d504180c46001454603204402c00c81c000c6600f0800015040006120030054410803908400e0305c01e2007034a80d02145582801a140200f02c10710001d5441807021030b2150503ca0700134110641d118002084007400100400d26211940e80b212700d01c254001003610610350200c49441203446022000d202c0b4909600441e4000c900420451400b040d42001003500c5a00030001883c00020252908004076070b04e0300208014481240142e01443c141d0074520600d12000c41141d04044004008996040c2041c0088401704100076084960b003480ca0003000301a41041a96040c1c585160b002583e0303000300c588200024890440040350b440d05201000c42140e801140c41542c8507610a40080d12001c41c0c1801e9080741603c1d84440044401c5030b035450100441285224140c4504076460482101b050007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 577565485 1250 577564235 577564259
    0x31509121b0f160b070c080d02030309010b041802040e011d0d0314010605070f0c05040513060e1618060f03141509100c020a021008090d0915030c09120605040c 70
    0x50350108180c1c1c3c0100c14083c0d1450f40018040e0a801081220220f5450700c11803031900454682a07805680080100151040240103481e00300000703960500560241040200b40c224040000038811a140c58100309a031100b580030488099114422044000850741d4840d220b00ac0003170000002406c00c100d404141106008481c12203074142d654501e49030362a1141d40b800c0b0101041101c1200c143c000018403035456004450048080349442200b0756401e01c1c0907011156a01c8103c0d030141c200c5a1003002070f40d8150f0340c1c4402c440d21310b00c1100000c0d5130440c3c0039000304515080784400906035200403040c440142d07041080021000100d80445068031070b5045692001c80c0c00d20341690090b220054a614542c10000d01011180100c070b01e2403c0301e900080c6c22400da04250400581e10008001312140b08201c00c00500b445400c0c0040034504002d07005c0742e4030a040328208281070301e4401d03001c4143e00c03664107200145040300340400b45825034a0607101401c41a5810b80d0443d060303e0b00801c1a4851034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 577566735 1250 577565485 577565503
    0x7022206171510090b060409091a01080c0112050901091502070311120a0e061b01090c170705040510031205042c0f041e0f02040507090302031509121b0f 67
    0xc03050980080c030700118080517007401503002d50048410f010020f4008040c1c0500050f00c0d100314020000303500d04105a110350f040507800b004665000101506107642c01c81c9034045812110034012510ba44d8443c0d2140c0985000c600091104a00441a012107003459001d012507900c21303a00e068240404511581c1d441025417038400c60700c0c0041103401c440300d01a0194204500e00074001a040c64883c02c1c02c8940d01456140c603010036511104214104001b1180f41005022107a0101d114204012a00c80d1340700c0c141c1c02024051a52980410f881c0b4010202c24030045074010341c0c12940642c07818004101c0c0e0864402c441e258040781039002c1407000400c00350300301190001d101107036650310328040d0345c07102030058810350b003070720301c9240315940108030380c1007503022501860420030f809040384140021140010b012a00704851254140016500401c4101e0402c15001031003009444040c4c1070b40c00e02000354403030086510002004080c000c13501300104c008498410aa602c43c40d21f200001d41c03100682c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 577567985 1250 577566735 577566751
    0x70305010e0c0319090f06050f0c04140303040503010219020705010f17060d0501150602060f09120c03090607140c1503011503021b01060e0c0a05070222061715 70
    0x207480014001c5200c40003455210390504189501203110b100641c080303841c0980d081d0789918104c0c4070642400440d02135a42c200038038081080003484c000200c404140990300aa030680d1088142c0d003049030741d04205403009880c00800855680c20030200100111440c82540301c0903008004001071198002c940d0010f002066443d078a004294965036100b03404002081d0319840b00e5214640307004a0380034802c090601c0420b180e44003405081040c0640f03040001441c4200ba51416000c200c00c9450100e0149007108001b01070b19195068031283c41e003180034900060313400500100310001801850803075a00265021000d50b403c4850070350a01c03107003031412a01a915094100010040d54550480c15003007040c440c070f001804c002c91120118207180c050542c40f03030282e44801c001d00c10f0709017003140c0507080800414218500134003090081c2090040400c080d00c5800d0300d58804020510080040d1520750070000100009900c0f01d103c074240105041c0751410a00c510b44880400310040e0015074010151 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 577569235 1250 577567985 577568009
    0x5060f2a06070309031d28060930051018120302090321160507061803120503060a05060c0124050d08030601030e030a020705010f08061c0507051509030607030501 71
    0x3032403248001b40c0b22020b82240c0c21400450003c0024601d40c0914100031140350f0090819030300e01b84000340300b23070340783e8004d0111392400755500d108400f140c0c86901c0001090203030800103107050b4180713035003004210300b80308080030b0070140e030000030300110120012034501c41d41c0784204041a25204a049015001215405501003180841c1c42c48860111991801e07001240d6841c000c0d600400001c00c1d82e0340c0c442110b1503441903109104403a00241916801d040415541584a2450300d881c60034680085100040c0a80000450681d403600c3d4010006071074042c0c51107586001d000d002c14001c04002140100c500b422213200d14120b0000044079040324030082c8030004240302501c440c4080d0b88090700b0603041c5644e40780f00410000041c00900095651074010f84503480c079102c005804d2041c1c0d401cfc5c000410400004112a5903110300d41075003600c0c00d807000c05071040003a140070b5140070526005207070b0010b400b0300c1d00042007802000600c0c00200503010303601c840d180e0400580c19600e080c001c1c90040c4032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 577570485 1250 577569235 577569257
    0x31d100c05090f090c0c010c08040c1a0f0309161205060105010e0a0e0a09020a03260304120c0312020d0606030f020301150507030207050901061e0e0a05060f2a0607030903 75
    0x90440d48050304005820117140c50481c00c02001400c403820040c41030041024003003000240150030081c0c3d4024640e0302c05251f0441030600100c0e00900c20180e003620780d04800720210f00c85150030010380400c403080c4400001e11984522200105050368041186c540c869072002051552040f0110241c81c90090b20b1202d109046c0b81e462a05014003c01074469980e5411010025036500a51100218000d29442c030030350002030101c001d1641d802c6030803010f10b542003082c0400940040c0943c0c0d040e19452034030166031409072070120781170340d42c0e440c41010560008c00d050b480b400e919400201111102c6c0c9041000010f103240d01030a82c0000d1062034000b0b0b510b94800722581e802540149242446403043da08010385403400962079107002e0708100c000403010f400221030303000d1078400c2503d10300003030030419145614040040c00100260042a000300004144c1e038000c1400135069405a04d0300c0120001e074540710b440a0070035164202e0281c1011320480d400300d903406001c0e20a442030150190b98188006e6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 577571735 1250 577570485 577570489
    0x3070f0b0a022a3d020c090115030e1207030309080f0409091103010209030d0f091a0d0c050715051504050a0c020717030415031d100c05090f 62
    0x5044005000294001d100051410702c484060024035415080c9040c1801944039044c03121100e01401300c0e4051840380081d01c2420710a8400020502803001d081c0c0080049166080307050a0a9100d6150001e101c9400444c2084c143c11b10030103000700f603a17010051122040c000e280e540c0d0303051080c1c1091240800809000c40c0c80b0b0b402c1910910300a004981c64507100c0c03000c3c0c0d119030340b040e404042c0c82542c1d01d00020401c044400755001c41e00b011030096080c0011039000a450300c12480422080c41104191003148500034400d1a00a001524a411981010341507541c0540d10040350000c001c1c4c50a203011510300d00800c01c4d80c00c3c803a0032100c498011030103051440010400905821230041085400c640c140c0d0329805510320400c0d0042c0b021948494000010780303441e1382138100c4c2e440203252000c0030700c0c1007400105480480d420013020388202010300c030081e07006000074900350506c003a84400441a60600182c090103000c1301810800501304044011a018042c20f54116448048519590054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 577572985 1250 577571735 577571737
    0x201030e032d0f0406050316030911040c033b12030c0306010302070209040602070b0f1b0d0e01090c1805160e010908030a1706040c05071e0f2003070f0b 67
    0x2d54100354030500c2c158030403c844100384c125a00a000041c000000c002c40742c40070940309600140c0354207090110440d41e9544481c402c0c042802540a0390f0349800d01007546d0b109420005940d456480e80740d03114400d1010500c8220b4100129561020980740381d1060307004c0000d001545910b00310f80b041c1c21a265500607220560018080d141019002d00c4010050b07550000700324082c0d03210720801a40d5004034907002d1000f0300c0062103a003816840a040004102d046507104580035482c1000560b01e402050076100141070801c0350304255031030301c00c104c0100500481c0070025901000700015038184108180d005a80c1c0495445c0403405103454000c40f43c034040c01e2900c2800c0b00c141000d080468681c08940d2640c0c0044c0ba8290008034040f421f1381020000b903503600d401590942d810f00503008100750180c218031510000400394007080e8024481d1103c07120600200300c1c2d00000e46039035180039003400030804140140b08504200489c42c004a24a13002032000121030303c5080241d0003616140c0c1e12281d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 577574235 1250 577572985 577573057
    0x1e050a0c050705060a030506090610081b070f0309050306090f1e100507020705010e0303070c06050c0a050f34051315092301230f09070c0201030e03 65
    0x1c2440741041c0070079103940762806090201a250b80000c1e00d4a041401c0200d0400b01030700c014002e805480481c19a540c1c031046007903000c03104c0c402c4140b000703804407942030030b52241c0c03407024041d1002494400c040541c490a154102ca1088040711210340302c444441e900d070b0005100c00c0300e290380041e00d401007600701d03098035540302e9440505540f0701e001d480140e40183d440855981c00160000c940a0101e581c0116951100305030540046013046501d660b2845003c2003401200284036012600581c408020000301c00c540c1d80c081c059a03049064000d0050f65a80040c81d10b001f009130040c060058032403009440500710b00502181d40503540b814003485200e00546102114164984078003203031a600402c0302c2001044980e000044001e04811032042b28007151580072458510741004200741c88d00303543d28502c40e84001e071110b13030f06900c4030001488880c92481541d401c1420384042018aa03048100098164000c1e01c040c08a6181c17583c44907140d103c0c10034030990484c00f5800082c804458800526a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 577575485 1250 577574235 577574243
    0x115051e04180b180d090e0a09080702060a17060402090f040e0102041e030b010b0c070902160b190c03020405030d1101090203061303030b0a14040c0e09090d1e050a0c 73
    0x2452454598100b0220201d51640e1381c0414070110b96840101040007400c0c0a03410314181c06190b040c038542d404070b00c4019000f01601c50b01c9094502c14032045404403400c1070350051505540d0b00c1c0001025100066644030701011140000001c1d8690505008442c605180103244115034481d02c0200700041c404025044c0c11994203100202e05250b0881c1c01064007110035240e61111031a51604881110050308007401096041c0f00145000000041c0401640c47c080009a281d040d19142c400c00c031101060044c01065107203060208415001410600c003841c00c103c14042001c2c112001c0d4240d11032032041c0754055200c05540d03942c1d0761207101e88407060781c40c9000110b001502a000685000015214071041c034605117081c5040540501c20030b45508001d0320540c040620f450650610403981004081c0616100c00244012601c030b44640e040c8031100400c0c1e01c0300307410708059455641a5000044002c504000c11101001480e42c03544001e15219680d43c501c1e122085078201c60703001141400b15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 577576735 1250 577575485 577575521
    0x1c0b150f130e36060c160b13060c0e010207050103020904090b0f1006030509030307050a0e09090c0a050a0b030109090305070609031e0e030a08090109080f0115051e04 73
    0x821044419040c480c000c1c84140c1c00601d540407003000f03400e05102d180c10700c01200d201c003002d0840c0e030a4010502e607502810480b0703a80d0b00c410000503d0b420b10522800010803513011a000c108080c00850540405035001d40002c000b03640e42104140c03078041340e00002c18050307030000c8070030012036210b50004c001100016102080844103507481140c01e040c242e4070702c81c0251a40c41085100c04010800c2401031002b46414461400e124421b01e0301c03484040e000804001c0001005020309000303c2e80c0038a22880644019154030701a01e20303a88811002c204503110f00c0c0c0c3c0f06000162880c3c0740b2600c00c03d540e9190700062559190601d91001011103600c110180311381480740d60003050540c031030130031440d009803109007442c5099201031018081400125040c48625151800c03641c4001803c40c40395075210101c65940e680e404016105a915544841614441d401500c00581c0064101c090104a0b8900300007005841d0000c11060b0510f46003600c815800e2940800c00c980703415082400e60030072900f202 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 577577985 1250 577576735 577576739
    0x6210a0e0106080a0204050c12070e040e0d0206100915050409030c0203030d020301151b0f140304060201020408070609060212030403030209090405160503030310050f060f1c0b150f13 80
    0x2031402e5469540c410620b50304944071600c1541418001d0f5640b280c071014210380b8100d811500421240d0002c1c01003410040040507900c0a921282e002c2d0100e040d80340c04480c1804000a00203584c0c54040390b2880815240312070005606215004054001040482c100030250800042c0030040003590002d4003005210024100581ca091004020009010f403000d40c0c1c960608924aa0728100e0001100801c2038220040015061410000c0c02895014202c01e035440410b0810f80101000000b4001d034074000090001a016015030080c41281c02007070607151440e030342e2841650815614800c0c0d80268200d0318042c14003080480c01158018864200103041003880303804070b054480c0844048030258800c448481e0012541900c1034000c01048000710b00c4c5207884100e21001b40401d1041034040c988800c41c00303400ba0303103400513100507100c4881e4054481080c402c000d19480c04601290380503a1414210b5080c42c2481228043c4001c01e000c07031540313030000c9803403190030940c01b00c100401150302003100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 577579235 1250 577577985 577578011
    0x402150f271819140901060e070c0602091f02030d1802182505071a010317090103020904090f03081006050f0c03132d0302090f0c07121d06210a 63
    0x19180702e040c1ea051002c101c915110188501f162440d8004484c10305a02040009050340314a40f4898250b1200c005a124142070b000314803002144c01c4d0000842141c4c0c0349441007242d00001508403800d0b40c50051224200408505150444110002e50481921030700c105540b603222b10690b810140e404400102d062081c40f80c446412124041b80700050400201e000500510f02d48000c003001c4e0005100c1007651540c3d807054150071101545124076203003c264410661f001c1e038140c4000301005041481080500c1c54605200044124100e02040d91800415104408602090b040c0c5032036880b5680f42c60030800400d182900601c4003080c1900c010081e00c2880a0b04c40041c00040124800c0555103211400c0c04082c281c5105807c0c003540010a1000c00150f611100980d810030a072500c42e0005444403507d0300d940b8070804001800c460016120780002070f6108030404001100704481c02101c0e4009410019503108000181c500450012160200100c100b89010740280c5109000030307641c4607602d9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 577580485 1250 577579235 577579241
    0x1a0108090f0d2d02071e08060a1b05031504020d09020d1b12030c083f01060804020f0f13060b040504050c0901020d080402150f271819 59
    0x808940000d0080203407082c0002030300100300c3c003041d01c202c64041c10004400001d54074580c40c810425071000d0705800a030103c00b41741030b01c0041c102c40000c0e00d01d20b01d400180080a054070003038404040c0420490515154452820307070380076034401d90400c200c0f0502c060811011b5041042d440c220560381d0b4140600503901c55980300700c4148180090030740c01442004a096501d0b0940c010000010b00d03403a4080025804248110324560100d071603916001c0b54040d14072140660001d4107500d144000c030b10344510003030f80041801d140301014070701003a85e03c0d070b5000c49040b1801c0e02c00a400408402c6a13a9036807600100100c11200c016000c860248003c07044901580d0190b4007000200c1d0000809011a041900071203602031100341d0314924010004000035039541101083e41d0070402ca080c0818119918403070012011804896541d840342d0700300c4002001079115071000048200781000c03080c140c1e21500700040e007030340004181703000e0841c01810141080301c0080140c4d50b9800b01000502c01609244 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 577581735 1250 577580485 577580503
    0x50d11041803120608160509040503040512070e060612160c02090a090b060d02150c01020d0207030e010f11030a0507150e150705040f1403030c07080c040f1a0108090f 73
    0xf079600541c2d4980f0440000c1107851682007004941c104c00031000035078498881c00c808443c0165042191030b540c0e801d00c54114012038101c0b540c41014400c0504151100140d80c00517039130079003070109a64072001c040282902c5103145802183c1041000070b81c00401440412485000908104041035041d03800034421a00488001e00f40e03035a10320b03001d41444104c40c4110b40c055002c1d01c1c940ba40444a80010704081d80d980c5c3c241000e61000611007008050a40503129080d026100c107540b584c43e41c2c41c01900310500c56a07070500086442801d608050310800d07031014075510110280d860050145e0086070b5540c800f06066070304000c04884080a81694441c40e001c4c515528040e218101e00c1c5009138105820240040b41041018041400b10445051101d13040b66040c1c85aa010481010046421401041c1c500402c40c01051800146401c2c08940c445000c1c9003100c040081c9849000d03d8000c95102040d803040c100007c450700391503940102d20781a00b085100d021150035906040d0b070b55140c45448 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 577582985 1250 577581735 577581737
    0xc03030e01050a05090f0102090904110a150206070f2105060103020405090405060624190915020c0a060219080906130f0617040b040215040b040803071b050d11041803 73
    0x22401c01805d84802c2c0014000071042100175071070a01208c0c00218001b5020304040d00244103606440c58640d5a0b01c0340c000203103c1072030000080135015201030344480d01124100702103442c01c09202c020510640174a00b0081001c00003502c5550310b0084000200801040e260505500304800714042c0e90b10b0032a40d2140344120010449440e1940034050100d180391035404410b085c10905860342a43c0b407040d81c04451520307003840f00b00300c010072003100c0000a582c071000038400203a181036482ca07400f0034030010410040d5170081e030407075543c1d4080380d543c0041c1c51141d610460b80c1c0c06a40004020ba4028044194010705550a0160540b0311200340c600e41d502c11100c50642401c10407840d0781007254442d0340d014514182c0076901c1c150b1210b240808000700000d125070440078006003540c0428050b54050001d00a00030b40300c90701c5101d0703150b40f640000d40941304050810500000d01007016601401d03558040c1100111194990303a2003101d012a902c42a840358640800000e101400c020041c20310740a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 577584235 1250 577582985 577582991
    0xa0609110607140f0c090a0513060207080d05010b1306030b060d0608070e07050301180207050a080c010c0e04020712051e0f0403031b0308010b0c070306060602060f1e0103030c03030e01050a 83
    0x5405000d0b0711301400071894034640c0d0000b809170600c65440040f01c0e940041e6442010500e075440ca40c41c85050303022840002c02c081c0c40811b89006201820000e400349151012040000d40d0309c40030380003980d000da0424403141c1c1d40c94003c00d0100711320a0300800800721021748005c1c10003001004140c2a209a508200c2d601c0e40078020270015608158526034210780241403031891941001c0402c40c25084042006000c0d0b6000580282000020000e68040d2500988000d403624141c8000300d0180200064a5000980880c0300c3c0c110b030310b401d200f00c030405a80301c129402c3e90444000280c946402030442c0a00032003050b0807010300c5c1c1201c80020b0188404c0c218183e40d0b111700f10314011b081441c0c01080c1a030040941c0c4000c1c00001c2d0820400c03030664021a02250300c6e81c1140d00c83c20710b090040e80000308041e0400383d0006215800103009409014002c123800010742c0c03120620b540b0b24680d00c801c909040580740040000c03901481304081c00381d00910740440c1c0302d075640d4030450a40b60181c2f6120700b4599 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 577585485 1250 577584235 577584263
    0x9030a020607031a0906030c180711011e0e03040e0907091b0c0308060f030708010501030b0c0a0c02090c070b100501030c02070303021e0102090a1806050f030a0609110607 75
    0x140c1441220360140c000c0c242046002c803a80f0880b02d1180d007542c400d9000d6503550010a07681d507003c02600c5d049030801054038100703c1ca14110320018904c1a5154030105501800c1030405c2c110600030303000ca081c081541e01880c01000074405c800b4001c894145629408100b1000c1040e4444a07040c601c43c0c2448802442061300d0140c1c140f08840409140d607401d010342c10183ca200030351081461010581600c2c01c00310903110440042c404001d01404583d2521644400207140790064010a040300e00902d50101155520b41540b840d80c0b0070700e205400050385503030f1084010301d40b000c603403500880c035101154101000380d03603043e5031130384103603a07580e0b4034150384ea01000290b91602440341803040c0c610242c00078602e9660082d40d03522902d500c2800c0404903040c03a4030240d0303095069880c403a07001001c0c04c4220752307640d58060007030318842c0e061420a82060004602400c0101c8908140c0002070001c0081070000d48605c002412181d804468a0650740c60b030150170358905011341101c070702030980c4000f444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 577586735 1250 577585485 577585487
    0x131815060b0c0a2904060b15070c0e0106300f0c020c0f060a0504120807050303040803041103030307080718050306070509011d100c1403030415151518050909030a 71
    0x581d50140c3d84c01d038030508142289488114001c01500035900ca04041541d4609034001103800b0b00d200e124140141c401300c0c116061005a81c0d840c1c08841d00c81c079501c07060380d8903580b0845030b8000411400171000401d41324004103c001e03000c9034201440c021f50000b581206191090b040d6100d1111500040c0e1048040601500c0c068000c1c508d44601140c0003807414006980190003409948200e981104403000001d05204640c0102c0340c1c43c540c4131094941c1e91400703250001c00c07a041610203640c003042c01e0b100d10903075007400401c80b409010a511091680e684154040f00e0b007500c1d020007503149618054001079103840401c8964000e0080c0e07110300751180380490004020900d619008a1500d402121004198031480d0008010304410710300615149418100340c80000c41d0340b10701150381e20001040105004114604450300c1e0a40f03c002c0c000740411011441100f040d50244460180c61012080980c078020520714100c885c885041a1096903503900040c40c1d0801150503260640000400d42c0d80b403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 577587985 1250 577586735 577586753
    0x5090f041109060109171c0203030f16050306040902120f06010801150e010506210c040518040302070905100902040e0411150f0d0e0307060b131815060b0c0a 69
    0xc11420b03180c0d98940d00c0e100000a010040501c603080303008a420100103441c110500c0850b07420940c1c041409400c2e2020350b0020351303950040303e101030303940801b5010500c2140c0580c032101d0781560603550349003151151400c00008111528040b40d10150314a900310042e10b090100759501d075513080190a2a6252007082c40c2507811024100f5403885542c10244480004400006e040d12030980e08503849075168400c142c0506007500ea40d0322038488409c10087c8500013800200b080e0f6505640f18510050032076441d0305422401d0382c0c01030140c2c1105900b4410520141d000d180d01200e00c0340007581e407075a5864800200d070300a4009a00d4005144100818003525091682120505403108100e02c001404001030a010b0207114943c019070004103142ca5540369002000c0100e18041601e55440e000c0c0391040c018070700c2101040c007070310600b05400c00c010400c0c85241002c5400014640c01201e10f6600c4540a1755443c0c21041e00d21781d0b80c000803502100700030103401038400b103000420782141542044004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 577589235 1250 577587985 577588013
    0x1b0306050406050607080f121617011d0c090607061d0c060d020c0319020c0301110405010f12110301061101060b0f0f0903070e0c1c0b031f0605090f04 66
    0x8900b882d104101d02d40314070b03049401007a0086e02c0c9030380704e000d003299a111600c565281a444a05003000703220050039240d0802014800740c1d26900018100d040c09500c00b01e109220700200810710705201c81d4008000c0e00025400180039060a240080d040c1c00510703ea000750000380c90305030366450b45a9500d80c640b904640b1031001000100860030b44580001c8491040541400c42c007500030032403400c1404100241c1d11551908840c40b0407103400f001d4000c2d590900400428825805c140d40003a00c0c496940c12a0181c0310181d4a4240c0070013101c0c4140c1d4035200450a10003111340da88019068100c0040107140600999566405000c1c1e800402c1804e503000e5402c00e9000b08400c2181d8002082c0c1e100480f2505110094060344074102100000c0c181481c82d80700551104441e0100440910082c1c018042203c14007864000105851070820480d80c8880b0a590141d014603090303400c0001800f5a06800e40e00c01e6008641c40d0b4455012544902c003c0d21401400340e2400148001c00200c4903030711003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 577590485 1250 577589235 577589239
    0x1b1305280e2a13060306180605070f0806010c020a08070f081e03070f0204090501060b0c010c020604080301050904140f010902040c0c0215032a0a030b091317040302041b030605 77
    0x40b420690103440d100c00c1c00a000305218034240c103580000b40c02a50000c1d001950490700800941150f00000300003d8020340080740c0c81440c0c100010704483c080c80112119940e15555601e082e600c030701c01924089510724041c5d0b404104400000f0759071804004582c013070100904801d40491404c02020325280003221000c1c0040680100c0f01000600041510002e40e00142c41c540385d60b5031400400d00900c0b21803005800da500703003000030a10841840050102102940c000c00c04100c481004a07103d140c103a4004124000c1040108201d00d002d016107078009014195075032541601c11161071070701c40d0701e1114070300d240d4640c00c000045d85450300c07a02400f40b84604200d2880e070b1150307001800034140202d02d040d03102c0d40440800d510050509103564455403c43d100040e000005042030001e401903550a0002803c1a51050150801c0e02101d0b01480100f80560301c0c08005030385a848100c203a56884096030400d0000101582d1140503a014600005c2260714030210f00340c100034240d4101e9044a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 577591735 1250 577590485 577590523
    0x42306030c09040203070908030703170903090102060f1522140f04030f0509130509070503030708300a020304030f020c010c030302070206070c080f1b1305280e 70
    0x320207601c1c1100c0b0041d4084070010385c3c0c2d079103080080da403902481c0c000010343c0c440418000e042540080c0384a142486800246a5682e90701a0355641d030721903098101d006030072600200d03038154010b5640681203407000d4003100c00c911a00d4080b68140c10501c0804800c100d00350903001e007103c1944a070341400310701c21100c3d0b201441e00c8180c80050b410058002001c00c1342c4030141d010b200f48200140c414109009262449d1143c0c0441d004020303040c15110b0700d195000e0340c80001250302d0f0010840d610143d1003401907040c100840c20110540303416074030403910500c0060240e24072043c034042c460b200e004440b8005840381000e06000b0000d00700c003071060707040d50310001400040b42c1e0007480070389a4640c1441c0160780c404591002c2202805190b10060401000d140041841440800d041040c03216035801c848840d001850440c02c0421303c124425000030344000490f1004070241c00c01940000101c440c511384080c6903d13400f44540318411030801040c2d588210401a110a02c5030038442c070480c0c0144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 577592985 1250 577591735 577591741
    0x308160b2a0901090f0b040f1203020a0201050d2a0e030a030917010209030a0501090b0f04110d020616050c030c0906090115110d0804061107110f03011104230603 71
    0x1c1580c500802884803200c901041414903a031092004102424080846a00240ea9140d0303a0341ca40d002401903080304442050040f4140c00c030849050041074040c1c0c014840862507400542c1c071076008031100701005031503812021031190a005154108043d201059180c161100d1000f40588600c0010710b1080e0000854200840d81c401d180b071041c1c0f030388290a034129030006401c0a009205583c001c0f9010700440c00c9400c14490194001c0c6000b50107041c3c24002c1da0303501c6d1104084000120780003440c801c0c40c0010309205003425070700b13081d40310310280840340b600f50400b119079002c4521039803c59460303020300c03208246400e05211035001c0081c10703550a881130a200b0005120035105005d69010404403040c90b949940c0700700c0130046c0303900000c815940280e00450f002810000211016a45e81d400c0c08159640c2c079208208039000307641c1003101d080310349070450208500c0f4414180060b5140d906d540703c0405c0d500e0311034000c2000f4000150054400194418103561074900045164443d000c14010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 577594235 1250 577592985 577593031
    0xc08031204080a030e011a0306011d13020f040f0e07050604061d040914010c140306031504050c1507020f0102030c3c030901090504110d0908040308160b 67
    0x6141d007140e44024442e4880004a904400038004040904c0c495802c20500c074180c119094049051194141c040d6005a0780303640c04000c1e0040180310340a40210040001010f000b000a00702c40013500c002c1440c2000300a5800041c190392104050fa003c00d5070714103800100c50410803082307000701429510241030a00d055805014518503251031400c10807040064141a91150711014000790b00c800360f00c0d00400300c0380f0030b180245100d080141c0030074510181c06109825072030a9034410341d0014000c00020440e00c0030040d2601010b081160140f0511071442520340e80c0200c12031f809280b00300115220243e600400c0b52043c02b000e87c007419504100000940008041074210203118141c06480e010386402c080441941000e00081c04020400f09803c010020088002d0041007800d99900d102d03240c0354000c2004a52203e400e115900d04100440c0c11815104d800454030036010302c5003c0d080c41ea07a903c0709080b580c80031566414500d142d6003041c1c1080320400c600f5412600030500c1c4040155201c3c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 577595485 1250 577594235 577594267
    0xe0f0c010c060b030709060b0a090503010902130c0e03010606031514150a05120a050108011a0a090c0302040b071412070f0209041b03060b0f04200304020d0b0f040c0803 74
    0x1001405040d1215000c00c811340f002c11901004001080040191607680c00c8504480c0e007000c07480740009240c000700004c4501d014090903410701e400070007000e2010040000d000c000c0204403590b406001044060040c9a6020301c2240000c0c01c290700d0200750710721b20b950f4240c6014802e42000610441c6c07074648181c50340b43c40c041803c0c2c01e00c0701140ca580e0760450b03030704c00d82316401000a10389041848100300854680c4c9030b00405d040f180b15500070311240349445048900d00c20040b01c0b0310b8001c40420030400c0707035408d25000381d00c2702e421a080051401d074813542c0311082d9a00000044e142680c0441414100b0502080380815450700140154204003241e84c4412240c04c00c81d4003e84600c01d6003000c03905001e42c008040310102c42d50055551481d60700e14000340900b9900026900c16042c4c50540c448904180c040e904092401180c01d10345d10b401030b145100c1c40d800142c0107903080240b010300040010200c0c245e89008a144441104081c5041e00c2e00d241c8901d400d400030b40c02a002030120f82021080c00c0c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 577596735 1250 577595485 577595507
    0x40218010314010e03031603020a09080a0c03060c11060403050a0c0206281404032910090b030c010207090903110a35030412030e1b0907020d02210f0408010e0f0c01 72
    0x3140140e55040d40c0e4804035800d10240e000006580540c003703a604000c032521145040300d02c684e20902c400c0c01450f2007640d03010b03550001c602003078004c440000e002a00c950000c000101700c41c04c1040303070f00455802103a15600a804501074040900383c04266680e1718640301d4000d2041ca250902c2e03603800704100d992003400340d80f0001700a001500090a0b0309104019444101042c0c0d00c001c4800d442c00c40044ac0701c07003841d0b12400c00034519241c451402401e0210300005155010f80082c002c083c80c04a641d8000c1658980a40c104041c00c04d80c1310f0318070303420302551040c80c0c040c082048038401d0110b0ba02e074000601c2c4000300700c2d65106e95411080080b40e00c081e20360040d0418040c0c07507001c42c05241034010f00b003054008861801008800b00c06190340080490140c00d00b40d404644a580ba01003da07564008400c1c2e90015071b0054010040b00ca050340010320ba440c00401303649040001080c90020701e03410030b400c0008965140c4c0200c03110000100070300c02522070810002c0c200c0c040c0d05000a030540c0055 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 577597985 1250 577596735 577596737
    0x200309030409020c0c040c031505090a110a0f0f0806090103260c011415060909070513060807080f040b07180b0a020105061306060e0603040218010314010e030316 71
    0x440064410101442541c00500e101a000c0d91340d20003042c81141c80700503010141d441680b42407010500103100f44292811414180e11101070142040f00700311810200804030400c4684542c8000d020304100c101a01480c101600d8000d01483c00e00ca019201d0205201c82c60100580041008205c0d506c2c445490304590304510000e21164282022000701c0c0c0c100d400c0c1001c100c0002900708003e101c154042980503000c0c00354210291a11007000180102c40810f442e03000e2800e00c0000c01c5490843ca10036086000c90800600c0e103154003014500030311040d070100c00032500207010000b01e150020071a60f403244031040c03041c110749019543d50000d0140030301660104804040101c900e00003d100e00030113003c200c411252241b1000800a01a0800700c840901905155200c0f000100e00c90060f8000e07540316456480000302e080c0c00744502c42c1c02c000c000780c0c0c1c4250b1103024914510181c8482074040c50040072200c01c10030100440c142500c01600030710610340c0c010401c20030040c2150708540603d401d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 577599235 1250 577597985 577597987
    0xb0903030d09110d050607030b060705031e30060405070f08070e030a0809040c05040609050609180405010b040e0c0a0b0304051c020c0103060504090b0423070305061920 74
    0xb0606007104100c00d4501c04a41011500c00c5600c180700e00010024800e101300c2d58240094090607044c03210034007a915005000768011300402110340c0c083c802d00784ca41c0c0000440a410103070301c001005100d03a188034501a0030880c03540250301201030500c030b0540c8404c081e10284110704114800500701000c41c80c0000400030540042400b07244228a04521000700404032a0b4009071800c1001240d0702c0100e0480c402ca1510012180740da01610540342202c4194590041e0f0515103401e02c451944101a0603034082044002002241c08904042c3e00441c0607400004002c064401408111011010f0310300803640b106a840da003581c0c905c00d0b046c00f1340758440d512075129215440d24a00c0c1c0101c1416001c1c002d044000c40308009680000c0e408405030302642c0920500d5076031805c1c0006c407010f91a000e4160046040002c0200707a21642d050703840e40c041c85081d608220082d46040c201001d940040700c01d40c01010500c0364200348030f0b040f01e10250350400308002c3e441ba11080840d50080042d80401e00400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 577600485 1250 577599235 577599251
    0x11010306051203030901061e09110417100b01030b0d030e030a06090b0709050415150c05030a0c0b010806070e2b1103010e0708061f18020c070b0903030d 67
    0x44650022001071601802c1200c0c201c0181c0032041d160781084800c1580f562030300c600007070100c004036070480c901100030061311969401d0040360750262990036452075440104100010300200482082c2c0884d29a001c045c242500d0800e50080540307100c0800241010305140302d20b41d040d9a070300002200280d250401c410700c5098040800d080000703440f00680342900d00007080081c860201003252141c00030303039544ca24954a400802c000c480c1c0c4030340c012106d225405402e000300507540b103403000d03480d010341043c0081d0716040d96514a07550201a0b1a400541038450810420030303540d03280c901400c1400b000c0c2c1614a031200004080140004c211440760341100b800180700742d040c60144010440d02c4000840c100042d0401c400e0303440103004968029071800304045140d0388041081c00a9820040243c00140c4541c402090802c11100802c90030701c40e00240000c000000c1e0700741c410441000c07400507071a9011501640e00344082903100c580354140402c02c620f21035801004986008006000010701d032a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 577601735 1250 577600485 577600487
    0x411041a0a0305030a12140f1509040804050103110c06070302130306020f040302091305061513020c010b15030c1611040504030822031e020f1b011404060c1101 70
    0x41a48220039401003451807021040c4800400202000360b101d803940001451301d40080011260035139010310040f4000c00100c0d04044040100030b0b000407041589185006100c0b0000e210084191422148000005020462540c0601a0040854a410303086083c8426040c42603103420004000000b055070004166015800000a9602450304214110749a03c00c00320011040d51190005910681c617280028804102140b107504095034050060400c68039101804c154404070a0002a0700030400498096081040d1024000001c40d1000108041c00c100f014420001e02000400902100030010418005506002c8800705252141a0007000b82c3ca800e2040e0050804030100f0744c400d003040144400d065000024900640e40c2000c2e030840368242c041050304903003034800d0080100350382d10107614400c80c01c10100c80c102c04460040c2c2e00700c040700081c0d80e4200f1101415079050840a020845c40f2940c0c841d5084004001d031400700381c9014240b0a01070704c10400e5200040c00701d54952096060743e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 577602985 1250 577601735 577601771
    0x8071b0f030c05010305010e06030a0f031e0c0c06020a051203040201050405150a0809011505040b032d01111201030f02010c0206030c1b120702010513030c0f06030c08041104 76
    0x34a0511440c0102503200e191101101e42035110706400070b81050000706240c2c0c48a03c2080c0500c50080c02400e41c410b00d565000303aa030380c0c0c4410907801e020140800500c1d1140e030602448480c0101e0740c6250222009250018000c056a0045821513100000140010702c0c0091006502404820b640751070340c1d52440121154842c907040903410400d8480083c250180c60300c040c0411204940b60710116940e059401402c8031038403840900703000c080c040704022310304281e0b1043c28600c00213019600c1414020a10303a041c03a504030410030101001011203100080288164014100495402840c06540754409060980107000c0030781480b14402e040b40444e0300421401c000154043c0c0400d07100d207080408440c3c160064985001d0707100600252a840300c4021914034055100c981042d8249002a0011161900816201503800300340c0700c8003201044a040c845c400404d0041039400100d030502500400755074902240c80c00307024014080c4030006e44540070416050a0580e00000d800144a00600751 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 577604235 1250 577602985 577602989
    0x70302030318040c030c08060415030b0f0103051911090c120108060a060905190b0a0f08030306121914250e070215130c03140d020708070308071b 64
    0x81440700280011044401c2d1a0358812520101c8040142c000c441000341c040d10944103945c000194400e001401d00e15041d880b9110300002c0c000000c50950300c135501c1d091a120140e580c5001e18640d0313401002040b0f400c005000c84810041c81d0300c030311201696102580501910300e542c0c880c034907410000d900c1460150035900810b00031260301c98156501c800303041e1500c1081c0e504100003030504c00041800305c9240591409800a8095001d102040000c01401005c0940074030ba880b11803554001400c00300006403101030511031000d1a0780b41007610820211414802c452129504080130181d20403007002c0f05a91110b8103c0b66261000e03c82c20003a5060075001c4e441510001c0102c05805520401d242c0070000790fa502c008030a401ea02c0b490010390f5a00380241480c2c0e403600c0402e00150101c0c00c0241400c3d08035101d08005481181c81c0d544a80c101420880300c01d180794411880e000516604206200c000d01e50400a04185411500c80c000c15115244002d408400c20f00c00d07180020607240c510b000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 577605485 1250 577604235 577604239
    0xf0510030e0a0b01050306070504081902190905010501080f0613240f0807080f030f0f1201060c1101031e0216020603090604050606010305010609090903020a02190e0f09071205070302 80
    0x10b442160324100e0345500d0280100b600a02c11440042e039003500a42c02c99055400c0b80006210709000b1807d04030000c58003103000c981000b103103007402c08440500a424806030601d900003046a6044c2000100705150041400040c804480c041c0f00c041d440f1890354811140703104001259080c0e40100b400c140841a4004030035003c1e01001c0004c01c10b5085885500b611410415501e01c01c0d0355480307440d034601c80e04443c407403640c004004040b504d90044c3c004105250700308030140e0030000c80324040e201c3d4000076408100800c040809034000c22509028140c2404807d0804000c0e410700143d002010120f11600121141d6000416030320305180390124640059004004680d41d29007103400c980c031004256070444092003454040741140d802070207410306031985940c0e003000d814600110170700500083c41c003d909600a501440000d600c1e504802e00c0d104070140344400f8500c4c44c244449902030310040400034480811414442d2050010415808071844004c035185039400c1420b00d00c0c02d100003940025 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 577606735 1250 577605485 577605493
    0x10c020f060a0903020319050c060d09080d0f0c030621050109050607020d0906080c0307050a120603060b0a050105130b070812070207050906102f030414040b0a0f0510030e 75
    0x1240c0141d100f50407400396032003a003d0311280740d01147c1d111816008107000030303c00e07001500080041d0a200d400307015880440000420f01c00794603100d00499510019017125055120704000c04451481d0082400d2004540b50820a00d03290600781140307000d500000081075003440c0031200511409401c643d00d41600102587e5803401e04800296903108000b44120118004010000d030700340c040d50b5614802c1214809036440c0d5507803107102302d405274094101481803003c540721b00e0100c80024418580038501c1800001591303175019003040001c419642c05035040003c10800410130100d00314412044076400e8055940710031441c641012140200040e10380d503a00103000300542141d000824030300721042940e54030341c0b07501c801c010f0194154807400203201190040849031b0f055591408160f403c1003840c0303540c05010b041e284503a4103590050380303e03074141c100599031099640b80501c54403100c02000c0707807104c44a52505501415441e16846514070031800e900b0088021400390b00581d400c0e49680c4142c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 577607985 1250 577606735 577606747
    0x1020309061b0c060606070303090501090f0b180a02040c051c05060f040203070e090411060a170c190c230303100b0c0c1e060310180c0e010c020f06 65
    0x20659611048480b1400c41c0000302221034808840c60494450101c054041c0805548000901100303138400c3c0c900b14101607903244070300040780b020f109140d4114030800d0300c5003035800c90b410051102d00d0042c0c01c00590001100c0a801420000208460302c164141c9000c5480c1d10f41c40c400340d44600510864400005050076600d8a140e81540182c1c4204d004948100200c442601800101e0208032002c03404a10b045411880030310b0044851a4400c0c8500c00302210f101410700480d90075045410314101055013603031015206515131030260391100c070f1041d440342815180c01e0f20820b0341c401030240c541400851101c0005001d04500410f50042c000385c480d4040740d6054031303451ba82e43d00c1250b891000e243e10800201d001c01c840811950040b1801008200304a089010007031000d03210b400341d00c0c0300b040118240f0445e444040c0614450810300c4d4240054610b80520700d80300000000d140008940b030500740481481d08602030701031006c0203107003c2e0f62102c00c620100d03034a0101081d4081e4800307008100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 577609235 1250 577607985 577608001
    0x40503070c06050408160b0a030b0d080d020901020715080711033603070b0d0f0209040c0207080d051201030311100e0303090c010c0506011a130303090536060d05010203 74
    0x1003044489845c1241c45410070132801c2c031071018450080d0100328908003c080380b00c5100380c000da040580c0041c03000781c0c811030750340e40d5070003503840100038101003500480d15003515a01400402c2c0241220301e41c180c040058240010040403000f0012007c0c40369219015010040800a80303040700340300704a907403801400740d071212001c011410110441e8903861a0442d898100490501d0484140182050801080c4480c0c1c0d4042c10442c0301c0358500950a0144107016034580c0150901480160083d100c03290411600e01e00b80070502c080041131003c1000580f01e14405a074200381141d4051030442032042c4020300c258104100d152600400508003113006000c0c100200c0194054818441207416851003600195509401d4800c0540144c000d6001084a680c82e915804000811040441c0c604642c1070344401c2050300b07580060f00003605040060125003081c42c0301c4001008608040e45203120095850080303640a00452f00d4550300c048040741042d1034104500f0b10131917004000b07540324944410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 577610485 1250 577609235 577609237
    0x40c020a0b0f0a0c05270f09190506032404030903050604030f02060106030b060d051e04050a170f031b0d060902131a0a08101203030516020304080703020108040503070c0605 76
    0x3440c2126900e4100c000903420f005201b15214510170905855a22903683c0015102c401d217a031845411854100780d252107681e87e00070391880746840703041000360800128136032411103c0c000c044a0003580000d036216803c10000750080c0503d20f9610f0892040d80e11890110303207070025640010300903c00c1100b1f10040540081a030344c1c09814650882c1d500744c0c0ea4040c2202a6010050b401d9004030082240c28100c0425403c0942c0c03098041c01000c10111082d400d80325004000c403410368441e000380b0170310810000340c2e2840404234003408a015040400a0340c04807050711000d41401107503007484401d41c1d50400b405094551601c40c002041240707075610309400d001795020480300040c201f46404042100d0255141070160b0b10180c1d0502404c04c4442030741524085000f824005001e90910b2000a0700201114800e01ca140b00755800301c2c2a091010030b0218282c4005000740c00d5400912090282c8240002e42a00300c0f1b4092a00c0d5034280c441e07003807803410b42c403030b004010344509054400070481680140c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 577611735 1250 577610485 577610491
    0x1080a0f153905070602030903040f03031205070207050a121a07120509030301030f0b0c07060603140c0d0809040c051312140607050f0d0f050a0605131406040c020a0b0f 74
    0xb5031610210342c0c003007400c92a15103480e034402c007003001070059002140b1954091035021f00400e08881c585904d82c2d40b20803004070540d00890004000306680f102d081c180d030040031b030451414002000443d0804001550f00e20080c05031204a034a550040c4052000384d000d6100c005c01c03001c1001c0603034141328000030316240c2d204140c00315050402c0b0108040c0c100000890703040302c0d004610007524080b242d40c2c05200c0c02001d400d0920a40003400b11501040d0a4440c1c140214444c00310300c03070f40c0404160201c1c00c0c0440c08151a01c6443c10805900103d0726507403c0350380382c1c002180d00147c00403c42c4001d5819021f100d0121900109000b80440d51070200450f41c807a5034003400403503105062122440703580d9007040b40c541c0d00041003441f0000104052801a0420719480d040200e40382d141c42d100340c401c6a9040703ca68038410f0719203004106900f003010303105140c00c09030081072000ca0360900b0a03a94226026200038051541c1c0d1003d00c00140c800c1c0000701503941c2c40278000440b400c0c081c90f2100c8580f029 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 577612985 1250 577611735 577611791
    0x61203050711041a030c09131202121606050c0304030c02011107091401031a1003020409080c0d02070e07020f0a02090a060f0b0c0d0302270312130f060801080a0f15 72
    0xf031b07142d14015140c88041d140c4078051018000f14200789540d12401a007000300c43e000150b00c80c2c0e01c2c850340c0010501340078111049040c004d5905011490400c2c00648101802c82480400e00700103210109034880380b1040826020f0070009a0041071103840782c94007050758041420103292100d4440791048100b000f034105c902440104011007070a9440d0000d013182990036190707008485500708014141900710680e01ea008140c1c1c1400c104c2d4001c0d80c00c0c2000d014246150040c3c000c5035003880b0360181d84c001e44c1e030440844d03c014000d0030003907098130360307a640c0540001c1d01c54101c4a0000e04159016000b680180004d40400f070ba0890b5118929006074001c1d02d40c00451340155909041075510900c25170380104070120548084070010304c2c2c081101080c82c04012341500038101060000503020000741161700b40f01c2100c40400345005490010002d041d08004100500c403c010042c522000a05503151a0044004401d2007841d00d824104400150004007109080c40700b844540040307040da00c6421400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 577614235 1250 577612985 577612993
    0x10f0612090c051314060a061b0302010603080c0f0601170a11040b150706050a1503110d0210090f09050f07080a0b1008070e030111040b130317040f09061203050711041a03 75
    0x1b81c50100700d00203019002d99400240c000c0010000b004000429481c018024000001c20079241c3d1501800f951050744508015400810081c03007845041107032500402a0f407581d40c648101c0040c0caaa155a0356000160148605008041d40b55845500143d58110010403945000a0252180c002500020303016500c3c6443c00c3d00049119901e40980001c020008a0b035261450640da10306176201e02008106070004484159000162a503840c2044c50300030607107400c1034040ca04a0080058031598000310ba400d070804d018800d0580c4035103041a000106410400031907610040014020259242c080768010038130b4802c0c070304043e000703140280606003c0c0e0f110f00a121140c000d040c00d0315070302641c0d00c01c0d0103020001004020004405410b2140300015600400d40c3c1e2500c4038800c1c1c15a08000303a803000c2c40081e04104001400e007144c4018800004244803441c50a40204ca2488010401130148240010a4020460700307050030f01c45083d0080c000c0000b8011050b0b10305450085c0c05005000b482 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 577615485 1250 577614235 577614241
    0x2707080f06010906031a0703021e1c0b09040f050a06060e010627050f010e03030d05160f0c02090402040f0c0305070f02010902030c060c16080303040506010f0612090c051314 76
    0x1c2c0c0644d109994000e20404003031403192441000c0c01700010410f80130942c4c00d0050b900307401825001180701860f40101315803178100c440c203c030400100e13064800c4d100310f1030001138002039160402c9090b4860b070000f20280300d103070301c07820403e00740048008010700710ba140541c082030411024003544c0c10b8841950765016020070114100c020614403c030059a90580103808000701d00d0180700340c04008806140c0020034034080c001281c650b80003241807020b010345032010891201035140c000071b520166031400d9125401c00f2400500a40c1c41c1f048041e00442c2644000b9040d0340344c0340c000021903a420282041314000740d0034014000c1200b51030000010b80804529081d030362050003880d4115800401815540c0e203444100b103030075030044014680c540194510403443d140241c484034000d181d5a00074694030324091070302e5828010f05030040d80c41000700041c24840544e1010310a0201380007810f00144031022410b012402c0c1009510a0b80c0c440829820321402c4a0140c0007240700300410798200107903803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 577616735 1250 577615485 577615499
    0x705131a09130906060f0315110c07080109060506010c0b01060e030a08030103030c031814040902030c0411072d0201200d050424052212030804020906030a0b2707080f0601 75
    0x6d8440c0b0018144141c00c1c100c0000e840c24a1340704042651915a01710b2815410502c10350a10140e948011200d0b59100703031403001d00a0a019a0b64400400d203042c919a00d010b68031260441e0040c01030b80c040000103178030140c0ca500d0400418004070b03046188a6240e6a41e843e005021042040088000442a0041822080f410540c107002c1e1004250040f10b5030320050203020007040042010303a490f206c1ca41240034141c0321840343d140c001d54040368142d0b407040386050034a201507401008500c0c05004a00010640c0000a03403200515424a0011080101800328003000c13050a881c44800303000d02d1014080301d940000041040710b14203100c0340788000e614107045600c0d50100706800017040e01007100c1d8081c21000e10061401040700c8543d0200b0039100c8150080d14040c2d1a811804951a5814070040d8500705503c90384c000c0040b002402142c8541c1d41e1044d0750b14010344500c6480200e64a01502c0c4504844100003416501007101d50b080da580c0b102d95039904103907030b141015000b01d6001040ea1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 577617985 1250 577616735 577616759
    0x6231204141509060a0e072c011202090610210516051303020d170a0f030b0603060a060e040e0f01020a03052a030408090d0f0b0705131a0913090606 65
    0x140744543c004e84070b5030703880303580f10f80140902064440d058060481d01241d4910700c240b1403141c1c1c00f000c40c4d01038000003049002c42c90301103060304001a240d4491700300c900103a43c1c80c0d041650040c002d898062074240900e00c2602c904052840d8090f00a055042d4120f00d51850340c0321038440c4100d428101d10041c5058400d13900c5100d10300000004941549040c000345c02c05001032608544a124001e40046850822030b109421500f0250300140e100e004404e02d1035414014600781c1da904550051842c2070140c00284104418070429090004680303142800b07648951100d02c41448000070f603010700d05180d078090700030b5102200401c0881d241c040441c41d0400b40140886070340f0110b00c8003444e00450300000d0f090320b400c028822182c50300d0030000310455455421482500c0c4d48590030400f04044546014120900c008000c0c00401c2400c0c000101000e4903521138200720341700c82916004000e1640c0d2100c1192050300c00c0660081c100c55020440d0381c907682d2040b5002c6019a0341003040230707120310304a002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 577619235 1250 577617985 577617991
    0x150605010509060409020a1407050c0f0a080c0d060e030a020705130507051615090813060305061c0f06060308030406060501020a020f0f3016062312041415 68
    0x3c8032090009104200044e4001c210203000d0342000100510a81c0b54031445601c50803080710030b85c00211440c0c11505061511412070031041710b00d4010241054082592101c04c07211240c401c0c0352240100c000d002c550340c48802d90303900640603207503603988500300699034030310030b01c20a801000513040300d182e810250b210f00d45c00f81c011641d40919140c22800003120004d80c0c140292070110f4000501201500706118840245104017881c076100d00c1d0a03800c4485107030450384200141070403c1c00300700141c1e4580440e400241016a2a01100780540c01e080910b502d240d0001805285045c0000c4140040354024500c03840c0b0458041c044280c640c030049803101e100c0e00d0001e41101003443c1055881c80d010803106940c05010f803010011460103010016044e1002441d0980d2080141c100340101c0c20500600001d407030341d030301b21040b802d19040d40101601c074183c1e003a001502d00d0210103002c001242e01200c104000d9014142580c0c14141842c00300d00094402c244d185200f50203951443c2c4c80302c039004600c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 577620485 1250 577619235 577619239
    0x21201060501143f01031406060a030c120302010f0203071806050c070b03190f0b030c0916030203091c02241e070e040f0c0215090a08090604030f150605010509 70
    0x2040501154044820030a109007181e5540744529613030140400207403019000314002c2c1101d010b110142c51221741416006025903010390340002d41030002c61480182a400c80f40100d4030f070350350980182400c034010410340040c480440c0c000000d100d000350344003030138401c000d5403420b0310441c00b541d40301c0950300c2c1c1c403c1032009044ca400c405000c00a03504500c0181d5800303030f07448140781071b1030050744c6040045031442445110215650f15409100d81001c2106580440d000e4942001034100f01000558225129041500305500080010316011007800704c8800fa52031800381044c4100440d201a407145180c0905080920003c4c1c05414913400401c5d0040c01400c001078440312551640c07010781e07084400242180f0500404030381711640c0d921603101c1c043d500c030860500010003100e5000b0017030800c0b020708000d50f200741800061212125022800c40c100c9a800403405584080c110080340d200d018903031018101c84070000307000090003445c000c090f13001684e4040400c019920741005485038010030071101d07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 577621735 1250 577620485 577620517
    0xf12010b031c02100c1202120123010c0219030c1d0703060506030a150f170d1115040c05180a0f1a01111603050304090f0507171302120106050114 64
    0x190301c6901a03000d00d1781e0f0320803850400030080d0407040c10410303680000741c03002c00c02c0750407401004440118100103074507009035184401e003040d9243c0001c00c209078410303002c4c0c800c00c2c2c1600007103080d0740c0f0032059600550344080103c40d0641c2d103003804600706407101d04030350316a04130000068003540309200d850b0030345100a0500e8195199904d80400503d8481c825104200100c0e00100e030a008256041c1300800843c03580c1c1207a0b04603907031001c1c00c1c12021845c10701032203501c1c140107000980126400c00480c038001e034032030400d41da14200070940c16190b0303020503000710755401034802e03001c4008852442480b003080140151445c2001309802c03101000014000441d2505031680250700c0b405c0788141c030b02d550404954240c10461942c0c1e41d51001907000321807617071001a0800400722076005042d03100844180801991074002c0028000500800d440304036203007000c00245444040841500055801400c5200c09130945000c2d80c0c0240700c40e001c3e040c04185440e1940890010030811281c0c0303482c1540c025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 577622985 1250 577621735 577621753
    0x409030804030c32010608010c08010605031003080a050307020d1103030a020a020c0603100e13020109090203060d1205090301060b04030c0311030a1502030708130c030b060f12010b031c02 82
    0x40703459180e004021903015003002840045070140c1c00500300c4400a401550284091490b10607003119087c0d804401d40d64100501d07817920b40e42001010781111064103001d507803035649507203030b40b00c200399500700074101d605c0400d064282580c003c001d14814506a000c41e44a103d083c102500c1004415600c0003030f962080002683c01d2000303030090300895255004842c600700614000400c2600111103804140002000400035910f022101d10340000300d450076845020b035035400003080e4801601400769450340001c045640303070310380400b0f048a542e0090100c181082442d080184158170a003030b614440e40c00e2600c0421209980d8044030222070340110310344480c03451640c900402c0b00441078a60b62600072240040302059170340803d21a175640e05d0200690b0b0340b802c01800703444040003034000b0115030341010142d0300203498031052038281ca030490350b80701103641c81301e001540d11501c10176000d805c2074441766104c070714000c1500f01000b400022010740e01d82c4a104007000303c172251004404001a403080c102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 577624235 1250 577622985 577622987
    0xc07150216080c0117220c090906050a0528050603210406171302041116080405041b09060e0d020a0b03060102060a2013030b0108100506040903080403 66
    0x40808110490054a508041003100035401e0000d40e8802c18041d0030500300c1c4045980d20035140d020b0085298608035003401e04124410406c540c9045688007000c100440005100180c0480001030513118024000b8004a10745500641401e841003c5441d00704008100205001c41180c0d41c800400f50364110400d01c030352a0a0041d09028018540501403a10b050b1402c2403201c05c000c41c119990303d10305075036901d820f10040510001c02c00c6510b001f109202444126030000144003200381d01150003048038003c2284014076441401503600036814107585420400c20000042e100301c400441c0d040014012a0914540c00d130760440c25800003800c1c090042c0041c1d0b0143d50380c1c84e03104402a00c90720460301c056010461901c200c1d00030781d00580b0003204003c01580e041140350b6003c03220390070070710074240d05000d0600056a08941860240c0010802000c80c50641c400a401113400ca06140050b50b0760f02c0071141c03101103825000b40d8050034071f40060043d017050f0086441c0154195901c40050b034442e14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 577625485 1250 577624235 577624259
    0x30a080f04030506090610050301090b070c0312020a0f020f010908091005160c0905060a2313020d050906240103050a090213061503092006040b0a02160b0c07 69
    0x3501142003a010300c800300c0441c2003040403a02c254030403001080c0714207100605000c03041c138a92040e84030341e0505d49580e00240d40404801e400041d64284066003c1301840e080e41c284d03501240310240188089049401a94810380b010340007d4140c0030b646e00210f0b0210b546080c0d856844018043c268100125004c50400100c01c1c0c40c40a4149415410909044101c110089058005a514005080042c404082a44203550308604200c1d20800c006140018071103900d80c00c1da48034030940c0d000c1d0b055210107480300c002a10060040314011540e504100b0b031000020403040e54066514131405c0000307951810401d038888240e86161b4880ca03601c013400300044014220080031003444c542c441d98800c005889500c01951608016000401d00c5420410001c52242c001c040010805003881d04010100309400c00025020803d4000c0d000d2180c40c03c0041a541d20490340095001500010301c040c3c03039940800c0400c0400e44241d4200390695559100030028003d0406c80c42da96040500c08109241400d9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 577626735 1250 577625485 577625497
    0x18151e03130f0f150f0c0206070804020f15040803040e071d0f04022503020c040c0507021c0f060e06180316151515020f0601060807030f0c020c01120506030a08 70
    0x90303078a80303c8a030144d030790804041d0355291250000e0745810070090041d149004e040104882480140840c1c0f424650040c035020002c1e102900480c405105034000d6115041410b440319103e100b039030350b51691001c2c5c0e1a502d038032611559108200d1354001c50642480f0744c18580d00c00500b0514a0040c001c03140401c80307050030818030365030701550811035075280b50458040d1046180c0144000700c00c2c40c0203418040e0a20001001140c0308034941510301e0030036038114041d5030b00250142e40c00401c82011800d03840340100032680243c801d0000d0346140c0100013031744d04030807500c0d4a0078087d15004e88800450800c0302c2c0007050a00c0407a0410301001048040ea140160b01140c02005000302d1540b8480303200013121480c40c0c1003c80c0c1042c0d20024403c6d10000300e02011301c07102c0f0340300818003c8584002a81c031044c041c0201400c20101c580480d800c503110740c0145642e809101c60400410203001d001954603084514042e01184410540040c089203600c074080c41540051b0162454007410f60310300e00d082d8002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 577627985 1250 577626735 577626743
    0x12080c07060e1903030903080a0507170c070b09070801060506160b060a03061b1701210512180102060915181501060e1309020604060518151e03130f 65
    0x5140c0f1107149202c0108425540d0303000380c50005a4254509000302610340c001c04c400c1180e030602051144103540101503800c580c142c6800345015450f01940b0315900e1040442c003400310142c0a052011003080452a403040700c0e1000000c1010300c1d0341d402484880c2c094602200c480b0302000c0395210100d4029290366502c0034009245000d0070307469a8804084070b2288108042410305800c60349292a0000d0540e016610a520800007a41c5450b4501401203041030503100c180405468182c00c0202c06c008410b0010720b480c03119034940b0031642a0b2284400f440145d0f600510422002c121601c50101c0c2c02454050351032069407590ba5030645034207640d101e5a200403924850070701e5662303a0303180c0e0010701c07806800c0941c2c592003640000d00810440020300d1099050062070041b0141c01a40d421040328110b84260074803980f10b01840805800d6114001038554024140b1001000243e040c1c030001c1820070b4400c2402c054000c00b1560801c00e40c001114881d448180308000c503008140481034144103170380300d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 577629235 1250 577627985 577627993
    0x6030501031109070e0325060e03030f09060706050a0203061c0c150207090e0705150a020307020f0609030a1a13030c170c070b13060e1008060619050712080c07060e 72
    0x2c0c85d070202e0316240403580345140c411100c2c5002c0302d03a110142c1e4242c005055074948802c03134205000c002070311b170300c210b000c68100e0a40000784c2d80b0f01a00c4100c103645210380c10034400c20a914203914044065401100e40318403c2040101120720714004115104007075811143c03400c003941c10310207070aa40421042d05c42c4258480c06c503000519422900071800141c0c0c00c00702502c0d15034600024400d1030000120600c09081c0c040c021162031381d60000c180c0d628550121503507018042c5c2c1c2c00110303000c0c0c0b0400c4c054079050f01404001e1400e00c4440074940040d9000e525058a095445144400210b40b28110060001e913000701d028020481c5071a00c00c3c0b802c40d02491580c1b806030307443c3e6807910349001c4d9800204025070104203001520070191000004043d00d08115006481020002c1c0c0212107030380308841070180c80800b040c1c494881d0800e0b92401500102000064880d0050107801b640000d2400c580060008100d5185684540d0225000b002c50020301c3d070422000d07503070f0306018010301780041c00588a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 577630485 1250 577629235 577629257
    0x60804111c200102030c03030703020a050d0e010c17060a0501081906030b0106090801022113140705090604060501080f0403050c06070e0429100e030304140a0603050103110907 77
    0x111009840005521410025032803036007080365401800b42040800d41075401c144614540740d81d010007103c2c0d100d5094900141e43d5000c044050781c9034059122404501d86c03602e1143d420301c1905501c202000326154607007082034111501c1415403071320200d0b420760300b0940c6040204440c0d4020140d81d0b80200c00003490056060400701020308a5405a1082d2142548000100140c0380c00c0089540a420031000035803801c034480d80301520303403912403800001034034807500081e581d140304035000c2c17850325484001c004055091031240350703417100785000303d0784100c2d941c05c0841c5513450184a0a41244c406840b580e405a8800310a0001d444006209a06120f401c2000c17140707a42041c06898814152600c402800300d0307008060100720347c003c0034081980451402c0800f40c07060102900b09106408a442482c000d05c0200c08980d032450414100d9054400400c0105070410324007140d140510059402d07100156031030700200d00381c81303081c4409071000b03100380d0858400e0706180030060f42c00300c10f900348400601 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 577631735 1250 577630485 577630519
    0xa090902061b0a0b0f04051506010509031c020d030b1f0516030305070e1804081309060e0601180f0315180302010504020108090a11040c11030406020c01140406080411 73
    0x460142c040c40860308003a10300e00c01c014884e64400d030080b542100050310b902d0f2543c0d43c141d869900300350000c110014900051411781c800d4003203c0e80130344060207503660003002000784110040921a0a005805150810120a80f0900c1000360843c2c0041242501504250400001100306001c11040000c100003c0c40940513241042d16018869540090207141103880100901110308460f4421501c1c074030b01199010b0200e007841e4005401c83c084a548121542e100320220150740d0100701007505148000a91a0003007410f507121b11003c0e2188030318013050301181601148079024144440380941410700124060005640c0341e010868400910f2243c00c00035000d0440c1031880440060303444201700421564418902600301461400512103110155243da15600b03c906500c3c2c040c580c0c07254003032002803103400007642c540610303401e40344d483d5150301000b074036000644207444c0840da8034208440d040e64904104c0f8121805035590045a440720340e110454640140480c680c0300700022828500d007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 577632985 1250 577631735 577631767
    0xa0306050a15030c1d010e03101a1c20010c15050417030c090910050411120c0a05070312090b0a09060609050106050304030f0908150a0506040504020a09090206 70
    0x2801e030400d0703546031840c02a10300400351800204d040c4200178519166444002c00c51081081807032007400c200d5091645040441d240540c95000b01e000c140c1880500d070312103070300c042458094103401c1d00c1003a56241c4d009005520b000e1103580081010078a854048001c520202d151840c03018145040d0080e40141e488800d4000c1105034000e00c4141e45801340010003005102d94180354002c03940c4c0d42d0441c81d10081112103801590f1049000308078800c0010740c10321070f001031540940401001040301c0103040d084040103070429040c01700c1d540000400b1485801d407103026611801001e82e40e6528012042d07a0449518052001e20201d190f10751a00800003204d12207628407a1500c0a00000d03520321904001c429030b03001c0c2c1d008000d02c43c6090b0041c06010b83c4401100d074083e40506111060208050088030030000e903610140340350040c00d4908200b90404180b0314003d180418003884070b5201c2a0800c422a13500f0ba900a500004c02c0c00c08200440103a000030000070b000801c014104410641074800c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 577634235 1250 577632985 577632989
    0x60904050319120e0a03140f0706060305060103122a020d061b02010b090603030304020906180438060111071701151d04081b030d060905060f0d080a0306050a 69
    0x401c480400011118003d4800c0307140d0b0911040c02441d00950075100646040c0180e9505041d51500081203088000304504036000c881d480f110401110350f032400c0c02c94940c9400e00044030310000d210400c098603841000c00d2003101031107150062121448003a80300400003241403c0760000380501104001c83c0c114840c000c107980302d040003402010300014009086034400422288500f400905001c0e160f24004250381e8490b81c150380c180c0349510f5040000d01c5d1500500c03800d40c40d080c102c000300700802555011141303090151400354910003444448483c04100b0b08a00e4880d46c465200010704a584a030444e02107003510907040d95607080e102c81131401182c0c210b0302a484640c2d1100d801e40c143d44140709a00d03009142c00c031115000b000031070010740709844000c0c001910307401020400d070303a50070200010600030b80003000849031b40c4c0345148445405050b442c0f04600b0154903200010b1030604200f140d540e200f40c401080c80b23289c2c1440b9510b80300036811881240307003050303a5080d000c101c40c1c03280e048100c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 577635485 1250 577634235 577634237
    0x30c0f070f0510060e01170601090e0304051f090504230612120c060c030702060a3605071422060503030714011107030e10020c060313020406140108060904050319 71
    0x4c2c030103040400201c0c04100680c4409551541c0310203403001800d000c81c10f01d06488500402060030429100d440b499402542c0126034071883d04000c0c1083c580145040c5030300504151100c08046558204000807206400401c001c04040c44d05445000000107413550fa0044000b0441040b8514031141d8910b0211102000c0c0114080000c0900e41050100025640b0a07403d03c0c0c040d2a5180901000f0344a4801400050701c3c5602c0d4044c0b2849047c0000803072205081e203021100020840e0303600d0840c8807070000c80560b258041c424003c0346210000b1a60540340b40083c102000c40d02d030f031300b5200c08111a095210344d4069902c4a021445650920051164a0044c80264441c1010444107402c5480155020f001c59208005000000b50012403100c903450044562520306904240264201825a40e0301e0394040c5001042208101e01210b009800d98000e031410000c0a8686400400191441d15981e021400e4600050075034903203e008164090712031000c1d6810f041003121240e05220015410b50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 577636735 1250 577635485 577635491
    0x603072408130809061e040b0c16061e0504092a0306150c020411030115110a15020307050d0f0c030f1e0e0a05011a0108060105190e030f070b04060e0105030c0f070f0510 74
    0x1c9ca083d201003002d80d02c407038103076803268407401e180c102c1c082c2a5581201081140b01420b20010b05414000c40c207440090107486018400320380200c0076644400007101c03a40c0300108440c002e06090512030b208401c01c2c0c82c4002c04000d4100762010080d911074100c86000c903401504d8280000311040c1050255000b4440cac29410000c9020044000e01a00115905001944c4c802508800401c00c01c88444a44009a0200603a00d48480904440a11480d13048221060905081540804503a4400d1000b0f001540c3c00b04406d9156007070440a440b05500b0200c442c0e080414404105587c540c840b00030303140d242007101d29524042e91850b09480000220720307400c040702c00c00f036141540c2041c0b8107030f4042024a00307685020741d00c00d6071204640c007079088e032001c201201021740c54584080140b00503000b02e03d001c4544056507281108290350150040d1700020740104030b41d10141d40110b0a80b40100b0b10b50000070f00b88102c140d009401030700000c4096a40c59040500346010070f40078030800440142c20b003008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 577637985 1250 577636735 577636747
    0x7021f050c0d090f03110318040906092a090b061801112506030203010602030d090507082a0a050a030303021c0e0609010b030d0c0b0603072408130809061e040b 70
    0x9072041b41181e00364034554000700601e03640e062800759581e5a044044400043c1e2203884d050000091100100003031510031800c945030281e81072404941000345940310b4501510351030345550402d1327032030460025030024000d010000c0c00c900d1444c46c0400708501031524074140300030360305110314007a20451405c510700851607250f0f2514458808800c060440c1c0d0905501c0d552510300f00035542d01c21050840704a40ea20584041084020301000b8004c21118044598170400d49000b4014082130441d00c103a540802c0c182001c1900304040301c0d00480d01c000748084070f0f0034510b460550196004805010032900d0f2000c9040c3e65000b00c3c4102500c445c0900020001d900c0c04400050031680c923610414030030b038001c2c00c00c1103a16501603680740305a9849090710300261a0400880e00d810400e802820b082c0c0032200000b07901050000a0203511103450340d4550079a201e000c01707544a05540726000c1d0410508006406490810900500e00305034176080035103100c040c40e55484003c3d08980c1240d0140c61002400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 577639235 1250 577637985 577637987
    0x16020607060e1f0b010302090114131a13050301090503031602071e030605090622060e030706020702101736070f0605120109050408190c0b07021f050c0d090f03 70
    0x30003941081c20701b4114038103100c8400190007000041c20240d08a0350000b541807440561010701c0c401880c4c0f24040364a19000c1040d40ca4054001c2a421040c080a1a0700090710345014020100c0840d0811b028501d140c5600715100d21800001c100d490a40c8190400082d9503c0b40203040300d000d80c41070b00300c032340554113610341348040c1c0304007030700c50421940078109101030005406114164042c188011140030301d600d01d860700107004006c00d5003d03103000c0400c00780b007440030135001072201754403c07141400403040768841134856600600d44409012601d50010b0844035149814140700794040781340d6030501c200b00324030019200791905880710b143c20144003000101c1110b5411030150030700381001d500f0400100018629a401413141d610219216008282440926021141414220210302e41001c550000190100d622440101e4800701c0c00c0c00083e81e041d101040025840006400c040c842d800340c280d200000d020082c159050500c420020f40402411314403070010b495100c2d440001e00c014080c20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 577640485 1250 577639235 577639241
    0x70807080601210b0306040f0b010b0a0203070b13080a2007140d020a030b0f060306011d0a0c050d15080709151a130806090f0316020607060e1f 63
    0x4902424008040140300e042e80e0012105400600d0890745814160b22030803800f0044c01050980c9900b50183c08240028400618950488240103a60211460766656180c034210f00c5040041401a0000d01035400010b002c100510b400410006443c0c0c9204403070348175440943d20000510000c910b00342e01100000380000048a4217081d0040a042000d14060f88803c00503a481166841054000a40c908541c1c030742075070501035600088026880c0c58a07040c008015030b01a00c416100b0b2140b0030001800c402c1c1d030050a00100c0050f290f000301c680b0385602c081d01a00720320100809121003480703c8038490f201c620070300e40715603618202210300624040089090400a400550405041510700c440d6107544401c080c00700c64606a510040d51220220b0f000039001e070300705130205031050250005051000003001400707508800b05440d000c41a100c040d80c0c2d00c4c850043c40708240e0701242d018001510f030240103811078078005c1c0e20101d40c00c0070200030141400d400785100b000b1801800207401048c82c183c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 577641735 1250 577640485 577640491
    0x10201050603060606041217040b07060b0901140405070324090e1c1202040302040617010510180207050c040c08011d040c0b0c03090904150b1f0f0c0b09060708 70
    0xd0040c0002c4d04110020680758440c0c1d0003543d043c0c0119601c41420004602c0ea03104a14001807052511140c58aa903844568400801561098106184840989003d0076058100d03100b40008411170405001403102421b4010b2030001030503580c80c106065250207030942c06084459030210010030b41016041c00440d00c5410308480d40c1d41c80f40700c0d00c540c5014281c1580300b03804502c0c20031400400310300808001030321407500000d41148c01c00310001042400f40200505440b228030003400340380d83c0c220040350014268441c143c1c44003203292801c2c01180141d0b0080408502a40130707200d1152442c1d0200b420b480e1495030b424005101000100240408003d44c24101c14288110941a0406031207100415002e030041800140d0000b030001c861407001c104643d94980040d00d1007805180500340b83c00415074101c1960346081c107000310482c0f103140c0001109030001c1001081e800403202420304865103040410701c401805030ba441d02c440803030784801615106d5014200140303418078020318020000c030806 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 577642985 1250 577641735 577641739
    0x12d0311130b03030d240b0d05070203070c0513020f03130c080d0801030204050c0d09120905030a0b0a050709030c0315150e040f0303020f040608060a0503031c150f090b0102010506 79
    0x30722910b020b075800f01c100c03400c0100b0004081aa604e221079001c400807030a001040005006010000381c851041d0050f04910110350030800c02c541d00c000003a40c4a200301c0e0801800320740b45610a02907440c211020300c0e6440c0e107021005061030b035044242c1c0c4440d402600c2c402c503082c0703070a000b0350204aa03804a0780c0140400070082c0030505d403841c00c041d20810701030000a1142c0d4a40340003412041d25401a0b941c43c60303000e0001d00411900e0f040c201c1104184809075000126040c01c086920b00b0002a01d603011603004c030540d24569128085d1100512028000d18104110300d04000081a01a4010000345000c1c1a215a500940403c1d0408a561082e10750100c1d0310282410000c460680000b00e911641101c0340c08280c014a01d0704600910840d40d41c104150700c082404200f07507a00c001101d1180b007003a611200c465894a0400d076803405032500d00704136000b10000045200c400768001c0d02c40c0e6404100e80680541c0c90362111600c14580e0b400800c0303820b6030f40c002190b91750713824064584c0241d42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 577644235 1250 577642985 577642991
    0x6090509070302060f09032a0102150105130f0b041e051e13031403010f0812041a0a020109020d06051906060e0f0126011e060206012d031113 62
    0x141d43e001c56940d0040c0d00c0b942c2038020002c200006030781c90071301002c588103820310396102001400300c040f41d00d210581c1d00c04a00510580c04001200c03040781410300c0c146d880040c00300442610501c1400040e0080c5100d400030140c80ba848241c035615540a030445840d14050903151011014000b03504892005041c000c010494007401110120302002036900720300c050b107080c1c13944111411f041d038400708801d002d02041940000000b818528941c062130aa42c21401a01e00310f0600184107441d45c0140d01440c1d2940d06c1680c1501d01c800b4091006102c403500da400089809003040e00010340b4064201000d50780c0726215420000108495011800ca0162440d0100103030303400c0c40c000900311116403800601503440c0600820300c6d42c1c010714269007030301582540403080300078500e001c20a0800a00c58101d04041c00951401031b464180032a109954061b4020318a0740c0c60f0101207504041c01c0e0380d04c498400280543c8039070341400444410003840c05030007000082680306c405d101001c071401c0d207203c00e0149 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 577645485 1250 577644235 577644239
    0x15260303040819270501110a11010f020f0708070e0610021203070c080403081806030f04020d06092a0501020a03020c0f0303190c05010b04050601022a0409060609050907 74
    0x480303001542d503200b10a880f48510100c846030b0595010b00c00c038072815624001007640900c1a241c0c54040c3c4190b88007039840c610300a012003481c42d40c80501e07803001005001d80a40081a65100341180c070990040303441201c00f0586850161400d140454000004070341100d8801d2200c1140b0030040c581050302034a2500c81188684d100035200d00203600d1041135400000b02041c040c61080c05004c0c55280c02132001075585642e494484142e51209210503403114556007030300b030549403090a4074460501c03042b4402c101d075507035070030041a001b0b00c100840d5510342e11a04000441e20350000c2c2c115602d01c0070040006000c0f0f88181ca030340c0e0202039008034110340c403130010a0006a03000c101451400d40a03603a01c120403040c5400a415802003400a031580c01c282034118203070903880b280040b0070030301410003000700d00c0e1404140300555004540b00c60141c2d1200340c1d00c07250703054810802c000c501290103029100c2c5040000203425103e80c0c41c1c0644080fa00c0e402c0900209443e40302e69500080b10740001c0004034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 577646735 1250 577645485 577645493
    0x1060306061203021c140f031f05100c050a0606081e0304180b0d05060f1008010b0612040c0905070c0b010e0f0402010c0807060c050403110114180102011526030304 72
    0x312162460110101c051904415500507240e41820841c80301c21b0781d40744c48000000002c1604212034001b40090010b616071100001010320300103460014000c01c415074003040042d1440c244035401200c152007040326802c0030554601c620000b909a5230003814000300c0c001008103100c5115811111035400030030007040040f05190742003c94a040301001b003021512080014070b1040d512002401600540c07041055138000b45106911910f840c038481000c4036110414607080351485901c1580249040184000121820078501d038030601c0b8807500860a0f80303c5008105a584c145d820201090070b4541d84000c00c03a2140b1443d000d1300102d50203000c00e00c2c042c001c0700302008019001905000d0000c50400511040c0d50440b00c03029084241031081d800543c1d401401e0f030f0311921003550720f0301215050440f15841000c800c3c41ca0322240b18103600f001460402e4511940e01810024150341d030300c3d407810401101414030711000b40b41132241d080040380d002100603205065540e98010582040007044002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 577647985 1250 577646735 577646743
    0x1030f0510140f1002060f0a110706020d021b0304080c091e09030c032206080402010206010e09101416020d02030a180b0c010e1c08040f03140c0106030606120302 71
    0xb11100e41c8001003031659003002c034041a014000d0180c0140c0700009a00b24160001002409200004420b174110740d252003803042101e00c05041c50783c0010f0104845000310301c0300d4014091103082010018034180241030b0340c1840384190300c0c0305c031034642000c5004c000c100000c1c48a0601c2210540e4a01d07000d2a186401e1845840c098600300c0035000040c0210300300301c1d400c00070790718100c0c0e01c1001c07070b9514110410000504066069200c060580c0d2b1400400c0e410f11a28186005035170680090180ea4242401d0010005000340320b1503182c0b242501021031002103004070804101d0b5140429000c1c1407000c034141c418002150350900350740c4050040b5610305e41c00402c840c3d18000c01d1600250441c5100620004414158880c10000d880441c83c26500300703065001414010b0818111140d00400f0420700c001500d5807046900410032000005022514941080301c40c64401e107000300c840c910395828650382e0303000360328020314580d924841030080069610860700580f80d86107280b9541541c07035038000d5803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 577649235 1250 577647985 577647989
    0x30e0607110a080c0c100e0a06030905031c0209190509090601030818030304090903020f0717070b090613060c060b0603012d1a18100903080304080706060e0601030f0510 74
    0x2000b40000c40070507031907081c44a0b0200d843c00514942d540302006c0300c020862080d101c0f14600c41c40300c031500010510b001b84a6502a10383c804042d500301590070300f807050a82160744a00c04411307000c000c3e5102984e00c55840c000210040c40c1400d000508260a0150701c0703100410f9007041c0d83c007000041c004548000151407089001786104089000c60300003003419030145030702050840741441001d900309500400e2030907030a000e40044940e425900c01c2c2000c1041459a0070018a411250051219465280060030b29280c040c20341854006024041200c2e00041d5100500280030080c00c0c03c10040e43c2e008050500728225901415941050717200048400916407008030f4210030441000484c584602c080b0040030b01540c80b916011000f00703540320b5a0311416040c440307c601c035038013a115440c5c070015408288519503030b804941da0031079682d500c20740e1001d03000b512200814043c0500141080c01428003030b1204088c0724495043c010005015900205801d20070745007041d0401060b81501103080d42 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 577650485 1250 577649235 577649243
    0x1602070b0c06010e0415051303030e0106050901050d0602040e15010f0305060907030b0f0307030818040504080703050c070b0406021b180a0507050c0f010203040c0f030c1e080a03030e0607110a 84
    0x40d11645011b845a10075000c4116215017801304015803000248240705405010b43c800388061040c2c2030301c441c01c0f52143d0280c40d902210500040c041410403e100d10140d51103030000500e0682c5a0f22800480d80b01101c1c01d03e018507018450309019640021800c2c44044141010b0000382031400004209400061514040640d903107a0101103507541c03088680c01440150a5030f00707035034403810803103030a03440380e0038986101442c1c56081405013803030f101c0c891142d81c1042c500d42c00c01600e69001ca6060380288003003603191045980100305212a10300078001032500d50000c040c40c081e0405000b6a103074004245500c51102c1e0b2419521140c1d049007119444040e02c0c0000903142c3d5282c60544240c042c54007034083d02d00ca00c080d900d0446030154000c50049004943d4a891660b407041d44040143d8580001011031000a00030070500c40703588140c0311240c4112541303903c10b6460f0080585003061005007500004e80f10086011401800e000450300900c0c680341c041c00d51000c00e503203c0d64a401d0313a88010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 577651735 1250 577650485 577650509
    0x306010e010c0f0c030b090712020d23070e0a021611011b0f0b220b06030a020d0b040c0b0f0414040b0604080f060a02070c03022101051602070b0c0601 66
    0x340181e1084541e00c1d00141e00043c055000d507040d0030301c80c48501003030101b1100d00302c041c004140d585800096002c200c0e910340c03c21016694450342401501003140d4000c6075003d462109c1046540c02c062020517004440e0b03402010300b60329081c120044944094070810405104004611807208020300c58040309400181c000d040c1c914010040703600142c000805086400d10601010030041200d2030008032500a11880b102919946d540313404501c9015045030344c3c90311007441076000400d8550080d90058004042e0341c05038016801041a100d01e85038111400e8408104000421401d050303140098454004c0c070170304042c40800c1c200c01910850281b1b506907409c0740d1164110381e850790408202e0f088050803190f100c0b0390b0b84041c15130302e1204060154103801a40001039840300148280c4a1258220890008292440d001e00131022030380071206c0b1502c40c403c40b0890700c10700e090294900a0781d00240815929007801c00003420542660800b45c13818000b04441241045d00095180c10744095100d02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 577652985 1250 577651735 577651757
    0x2805061005130314010c2607110309100e03010f1506030f060807060f231c0b0907022503051c0c0c08011509051312020c03030c0a0210080705030601 65
    0x1207902c40520740c0003e100043e0501d000300c4132503040d003101d030784001c158554840b003804490418403000c1384505581440c0310081d0028607017521445408901290f08000e5074600060381000c6107000c1d40a5079078001045400c041c103005400e0034801c1d1101c04040007000c110011200f48465207011492242c44105910381c0f88a00d00402140d10182c000d040800c100c49581d80d4441028010503e0264081d0214078501d803100341d2080c0340d082800e0120070500000c0d2a005030b014507101440800304a503006240c0d1011800c0090721030320b4000d40102c07101d80042c04850010403140d0781d21600f82c0034000c01148614001c20000d42c0026a40088128481c0190602440c441d811100d2081c40900542801240c01d40010408010760040410003241a1150f0b64203884002001c20303141c0070781d543c80c0d00b804500d26440105010083d40144856184140e4181140c1440020b165030048581d03c40d80b500a032413080214680030f0101d820140480c1008ca40600d003641c4007801c5404000c024606010201d0702e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 577654235 1250 577652985 577653007
    0x90b0c0a11190605010614090613050402030403030b10020106080c12010e1c17090c0f030102130815060102010c2703021302030f01050a0503101802092805061005 71
    0x1101c0492801422680320307400400d03010204824140007603403424130341400422000d224481c54441a42c01402103403034002e01d01c05114507503120108944c00c00030508004103140e65240011405240a650003040c4241c3d0103003048100005990303580309680c5440c07001c00c120b00d40402c009040c420101c40410110031080d21203805040081a00c0ca401d005840d40500e103030a0320408484840c1031030342c3d00320554048442c10003c0701c80583d083c03013460340700790300058443ca098190f0686094001e00090f0034106034410201490582c3e40216201e5000240700c0ca421101c0300a24a42c000024070080c001c1101804014001d166024a0324044e694032200d1480031241d005030703120007158043c01428401c00c5900c503400080d0400e4809507103505403500000389901e4034014050a0700c600030050580002442d032000003c009050425039140448170013040540d2312030b251726109164001d1180110300100c0032001607100001c202413015440c020501031207031a10280d00b07020710054103007603942d5800020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 577655485 1250 577654235 577654247
    0xa05040902040e071e05190b031e070c050c0901031703091f0b0102190b01060f090f0305030a1220090d02040f20040305030f07080706060b040f09090b0c0a 68
    0x4940303c420300c41c1c0800000e40000020a502c41c101075003251200c202d848104210000001d80800c0142e040e40c24400d016004540e00115003000340c510380e0749a070141744d03c21440c4080c0101c51303120201e00002c0c50b12003408420b024031483c3c0602260281e038158150343ea40041e081d2044072504c010003012001541d548000c000e440a45007030092030728003c04031080c0c00000f400d0800321142c014080c400c40752003286281c402000c50300740e1200c41e6020a80c200324045441d4080d88901c1020015520b4001403a5208040c6035400355000780091035440c642e8440281c203400040c942c1025072171512000c008210125800240d44402a42505654603072441c0040c116840811010b948140781c59005048114a43d0014070440e00503041c8402401c0e50009581c901d00072440054015001084180c845110040040c1141c40c408c3c4d40300d6043c5642912088200c43c4260000300c054100002c0c00c0c0203032140954803600418248000340000d042907511b04441003405400310211010201c0c1c5042d0541c0610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 577656735 1250 577655485 577655501
    0x10050d063311014b0c0c080d0603050c121b0604031a0f060d0203060a15120c0618050d0b15030d0302040914100b07030c0b0c030402010e0f0a0504090204 67
    0x42d0082c000440340b40c003d81c01c0c0010811050410007000c000c2c0c2c00e040b1007203401d011503840380d880c00503907500c02100100000c2c020901c1c240c8200140c1c4ca05240000d0b00c02006020401c3c0001c40016043e4110300e459450580300c44000d0344908181a40701c90340d00c1e0001840d80d51007201c107804040c00080500413130302c41e010350b820007014195082d8000806015004000d481030320081000c200c46d4942d081480490707800b040002e50544c01c0840001d008100c4c0e600900c0c10746600b1038084201540e00c07002c282ca4000102412150078014001c20840b095104004401c1e0168040070100307694a84000130f941d0603001040240925900000211703800c8032940c440301074250140642d4000d00203800300034001d5016002d03600b9034600d4101080c403c4400c0082c0248221414020054034504104106565800c1914110b0801a2002c00ea0002661412400307000c1d51000e4000303038032030900344000f41c540e03200000f40500500d0000001101aa161500181200c40076a00042c0205880c000310b0003901c184 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 577657985 1250 577656735 577656767
    0x60f061206090e1c03050c1204110909100e1f050711030c0c01140f040b0705010e1e0d020a0809040b040f061509151e0201090210050d0633 61
    0x407101510000f900410500b00301c0c1350070440000210250003094044910669070000a02414400d50705200c0004c00035540280c00303010104400c0e42202c1c001100c0d841c00302c0d146507450300440310142003003c050044d49003414440010705080882094260b901d07480e0b0b00540400c0e5916000030452490107041307103070004502c05090b00d541c0c08140d0740c0255034000c1c0090f40c0e8006410f13141c000c0c520410040c00e903600c004502403400e05d49403601910412541000300140d4055607588200040350500304101c802c3c00c00703944465403c19203c1525181400b0545403141c05540080c1410000a801c000854807a507108a5001401d541c400700450b004004014a10f10036904e40403000c5100c4015440e03001450b21583d4400c09450303200c80c840c0a102c140c186c02c16010400728178014442203004062549031041510000903801200d400140040c081c90302c005001c0b440c00a400c50310840c1c80c0c00785502810001c221158618035550226031010011040c0090241c80258030703448107807082a001040c00d8030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 577659235 1250 577657985 577657991
    0x606090d120305071101180f020102120705010b0a0e10091104050316140118060c060209040213090509030403020a030b0a02040b0d0b1f1b060b180f060103060f06120609 74
    0x15400c080c0040c40f0540d640408141d25408020f0380b14414042d01c518030301007010040080c2d48986d5000c014001841c012810740c02030792124110922014040d041083c0140008101c01c2c042c0c500b4440348901c20b0300f09500d204040c800f0080c045281180d010119a200c4400041f01d06220b0b13958425801036401ca1a418007909103410718540d40000903005072103429000400d02984000195020300d90036501c00c01000110604108541c0241c240c0c000c514000d510251820741c4c600c00040c12030f80300902d48810018442018030100d0b40611840e03070f001500368000d5107080e040d0340003d800c5850510009140b444440005000ca07950f0741c060703070018840b0340401074440e41c003885104040c0c4800290350340280d0008094a103202c0e08081c0f071012940564840c2003030110504085064100c2c00c8c042900e44035154440d01c80140c4130303820904040e011410341074426041540394403450500191181b81003509040c42444910014208041211490302b000c410009603098054045c10890f4007070b10000749 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 577660485 1250 577659235 577659263
    0x2070503030a0809012318070b07050109121103120c12040309140a0f09090201020106150e0a090b0109120c0f060c0308070807050409022b0e0610030b0606090d 70
    0x40c00048650103007213010003d1144000c0824801150f0311440c0102c06a032811801003603001d40c451100c3c2c1c2e006109007082c5c81e40b450b220400814075030b11079882200c0580d0740e60684400c0c0441407143e68080b14035032030151a84002140626664091100c190220f81503590209883d8031045c01214040d10342c01452106501e072500700038010071110711545160303441032107035520140360954106090741d1000154848241c1040e500200508881000702e06642d607504001c1040003580c40d4903900c1d40e440341d50f100004640d0b0000d200c1c0100b040e80c00401d0310750174a2881060b40c0e030000c140000f9501440c5041401c000d040c00c044004440384d900250700e00104040c045140c0e41e000c0d07070441129000c0c1d120f00b0740d5511907032400c4520020803513200c000124180302c1031001c056250010320400c6a03040c2c801181070038a102d001001440140111801942c0f04500b204841d01030090f00d500800040b4402001403841d1188030b10804010450f03441a100000c015406640c2d050074180b4154200c10000841c0b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 577661735 1250 577660485 577660487
    0x103020c071e080d140301030b13050a0c2102150a1b06020a0807020c030c13020c070e0a0e070b090616120c06050a0606140706060806040c03020a050f1e0102070503030a 74
    0xc6001e003e24a4640208050303442010b0084000070200302c0443c183ea171440c1e01c4d540710750b0141c03c0040e180c042c00e210429002000b1038410004561300c44e003d5401c0444042c60031004411750040082001001720382c00304884050fa6640000b245080a442c103481d540d1a100d107012039080b4803035406000580543c0904c1e030180043e5030f0113009050280d880321100c5880c0c50b1001e0781c0c2d8646034130b03c0382da00d0360151080602509001c1d40e030503045903241030058180f00b40040554240b0300550001c84400e50300794100004402a401101d03860481100680303240d42c18200414003078171030100c0080c000c0f1400200b0842d10307124007840d2075542d60405103441803002e050304020f142920003202551078900b0200440c05e00001441070000319400c0740c0703455480100c120760113030f00354100d54030a40350749a80b0240000d49010911040e4810362003441071a01c150304610401440d0645a0001d50150700d410b6100e918946540f13624501e214080d415010f88d0b01c18001c0100d1a100240c1c01c85900342c0408100940c0745 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 577662985 1250 577661735 577661789
    0x90604060201021206060c0c040f0e07090e0c060325140c0d03050c13050111031b060405010509030a1202090f04180203061e0414011103011508070810050103020c07 72
    0x15112404c1c042c03150b48501c02042520300503034601d50300c50340007005040400d24159011144030300b005c1c0e00c00318411010350611130a0031442d51100c5501612486440980308044c05103900050040355424218104011282c1181b580c030717804400c034040b110150307441250151141850020780c400080c0c1e039541c40460041d41743d840a102642c0440d01f4540840c4900034140140c0c3c4030090a03c52a054051174080111801e8440960002d03890008010242d6022080400507000c8400d2100420352404c00346070a5084550092800003190003d1145408856000320300f200010503240c005a19100020b002980000d00d0b05080c1d0741c040c0c6440d04190b1642e400381c21144116008405468166495100c504010001002000d810345c9220000a0000d049e00f060030500e6040b11000048843d00a44081c01590080e0071004a000346010300e41daa90798008011544062a40750440141c240000507103044180c1d4000c4078141030300811482d46003081007003c03200034801c00180c451185041c046038002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 577664235 1250 577662985 577662997
    0x200919051f030c020a030203030610090506040e0103031107050a060c0212151b040b0a1110020f0d0c11060408030705090d0c05120a03080a051302090a06050a060f02030409020a0509060406020102 85
    0x42400c0c800c500c0030813800400c2c03076001c41e034054014528541c2d540c01000306030101c000b100d8050004010001c511521400040c0000c0c0c00d82e00c000008a50440c10017030705640320790801c0f0b0301c1c540c881c000c140080d86681e44182c08480303590408880c014050302c001160286540700c59101c5103e41c5026404e900c0001158a014207581c042000d00c2000140d010726040c85503005010700c46408201181e14507114003607200c0000f032000305655518021440d0001a030b4060001e500e10088003254030207a2190610601c0c020030710034200700415140c5003105c40c0c1ca80743e0080c0050803105c001b00008104900070000c0310000c910040c001002c0d00700f50b16000741c84648030f000762401503140011190b000035000912408268154940380240d60b601300ca50409031400601c0c1c0750340c0d0515200c0007001600c4042c003441c0950042074022965904081c140030003091690301403000c1002c01c02c441003e8580100c00c40c5d05441c10900090780e80c003c615025149841003042868001c0350020340024140da0641c06014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 577665485 1250 577664235 577664237
    0x40f020d0c030b12161809050609030711040203040b070c051006260f06041401090803070e031c0c0b15150304050c010c080406110a0b0118200919051f 66
    0x18141d003e070300303841da0368600c1c0c660341c030076100c440c41c0007442504d079402c3c0c1811406c0c1c107801c004950381c035640d0b940c6410043c00360740c0401c0e40c0d0b0000c11501d00700202c01d4802e91484106a0302103041d0f2416884000041750054090828054a902520240502404041c0c80721104003001d2102e2903035102d82441c00000300c0c1110012005944081503021404075003540a04000070003007055071100d846520074011500400040c0b0343d03075024501c00243c64040a18841e54817601d50070030000b040400d16042500c440700340c00d8007146140f0340c0521035410900d0039003d1900045d40f10a9965403040441c2e1094100c03103080d5102c6a080e40343e42c2c200917440300071440f40e0311410588004006c800015100303200d00201c000c0c11070364240000e00101e4840d16080003040500c20444800b10056215880f0718182038006040f18116098602c00d80c410301d0213082203102503178034440c0381003800419020180c000c0c0282c07144070314550f1003001c01080402c00341001600703000782800207030003040313600d174440f2000c9283c40c01c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 577666735 1250 577665485 577665499
    0x2160303111603081015050c0f070501021f02070b040605180d0915031e020c0c0306130f0507031707120813080906070f0f06061211040f020d0c030b 65
    0x404280d101c00e058500588500e844281041202d40d800c2c1c034860380c0100002e80700b800180c000a00000307002e55100c460b040981744e0302c4d5500d071a1080b16042c40615091500700381d001020420290740d00007109000b4055191900d07140e15180f20615019116980c00a00f00b11481818132080c010307254400d032300680c40c0c0c2c00e02500302d0040c2c040154841d0b0203100c5050104000b42c504210062808020302d190003100d184c0051244001d0710300a842410450b20403024a50200c2c0007401c0100030400d543c1c2c0244100c00401e0346184c000707490200d59140c1c01e4014500d4031081000010094100007110146500016041c0305a080781003101d869005900143d40400294154004a600980415001790704001c402003a41d00d503912410090ba00812450390003000820140c80851021000d51280900c20550200740340209c0c01c3c48402d035541d0340c0007008031b600b00302c0202c4002b0f040024061000b200c2a180403c5000e4001c40b10b600038000c03011038000107400c02e00c07110b6030070b43c0c141d10601ca4090221021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 577667985 1250 577666735 577666751
    0x30904020310290a050306130515042f071415040501060906080624060d0501230a0303030c05090406090b090a021617070f140f010b100f110102160303 66
    0x3c1e200c0e80f000910000d12180081112158151080008540c450342c0640540261110051048102c0d5030445840500f2401c00b07040e06454034041c020200f00070300407094500c400c260700c1e02c540b0700c001c2d00602181c41801c0000756802081983c0c0134031036010351040240c4000312400210160310503012242128a94a0503001250520741d03440741a0640309848004d20066840d41a022000da035418400e00c0c1d001e0000050400541d034580080041c6444101c02040c0340d49490391114080d4540d1000c002024441c0303040c44a6500c8000c00002213980501d07022407182d00101003540d1911801c80c40640147c1440d10110300c00075180c100b0750f095034003900c802c1c08964880c4840c904a00030302c00c1080140114040207400b103076092040000e016041b42c0710070714200c0e580d500c3c00030800312a2411220000d040000b40c41c3c5480901c042403001884000a0080300500c40000d002002c03010080e0b4144501803101d0072001e81b0540e40c070f061b86501c480003103549d08943c0d01250559980010100c0000b4108824 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 577669235 1250 577667985 577668029
    0x1e04060504151d0121110c0606030106030506040f03140d091a010e0c0903030c01050405011b05070c0b0c0115060809010f0b09060d02061908010f08061611030904020310 74
    0x240c0400e4042c0c0c3c451403200642903c01100e4441440c0011200000d0301a80d980509415201e01c0d00c96035a10f2444942c2c81c4500040c4900b044001040785110b640360540420100b0000300c1d201d0707030041d8041d00a808031890340c6030558403401568508200b20401103a0241212401d42c44010bc2d507005103035002c0d16120203008520100d80034090355109240365070203c0c0e0850000303400381c01e101c0001010b4a0038500c901078000d00310340b011142511b990703440d40c100d4a800c1e0505040039410a100c0c6c0b40440c98401180ca032855640340900c03480d8410f03030000980350803d100c01e42c01601c80310444515920a00c0c0e81d0b2900901900081d10424801c4d4a00085491524503500c039080022202030120002ca03034500040000160354854141d8200c07108001130070303511441c140340c4192040c2ea42c544000550415000b00917890081e0001d00580d4040c04c18410312007800042d805200d4520702d007000c000301d24003030b5207411402031405084c3c2190000c018801d596000b010240c0a407840c0f03038080c510001d44e00c0a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 577670485 1250 577669235 577669247
    0xc0103110a02100209060f130504060602030c031210080a12020607022e0b1207062c04050c0c0109030306080d0302070305040e07230306011716051e0406050415 70
    0x1800750140e4000403e414503590141c000d0080041d0050030036052103400e400a800c140e1020f46d02500c4212840c80c2032141e450070303208080c050805480150b040c540400b4082d541d0384a4110b0726042c1140080008a403031006104001c0502800d000b55170b904408c5140c8007405440010030b540240c000c250000c0e41d035500c0000d00b0120194a004480300c82c801070384240c1009040190000c0a0b13079120001c0a0307443d101c0050440342100058010028a45420300003000405010b030540944c0116200810762040702142446030f91100b110000340301d4035503040610041c4101c080c194000c1d4203189480040c076400d40d10040c01c0b100c0c240107980b20902017581c00c40032486500001000302c7c5081c8000d01000c14407140e499440401410041a0312111f42c3c008546512403044154001800104101540d40e20825110b404640320800c2226400c00c0981c1c007500c68044035415040001c0403c007084002c86070700f49180e001c41840b00f03c42c0d81e543c03100c600920b035901c180611414658014481004144112 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 577671735 1250 577670485 577670497
    0x3120e1f02070b0f0d020f18030a031e230409060b0a0c12092111010c052e051e010e090706260106230c0d030c05120106020c010311 58
    0xd409420b40c02e0920b00d8040c0284c1140d0204a02140c06111684901440c1c1c402003007842d0203200d50035200c0003030500c00e894004010b1101c60281e004610383e00c001036003008500b12400101104109507011444080310b0352070084620918118200c80c00300240c080700001031042d903103a41401e00149031185070000c180d101e984c1540c0e00160a28aa40c1301043d500700145001042500e000d514807a42c880c0301001c9403502c140c0100540d030328581c4160810a2050341d07405d034941e0030300b0150050600703600c0c0c1580b01d030095600142145e40d80010445140382076402c40907002c40344001085242448040c120407a0305103468024449820000812885401d45100b841048000c009280003800d0800803183d0581c030400d1014030000b015810081c00c0c030050703600c5001e803a0564035145070b5041d0740401151208402142c201b001010020f00545ca507010030b4150b0f06039001d040c0030441400950040f00c05220b40300030302c1c3c01c1401840c004541d407580824907507586030090380d00b445903d9130174004070b01c588140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 577672985 1250 577671735 577671737
    0x241a0109080a080310030c03030f080105030f070303180f030b01030507060c050c0f1f031b3603020303030a061a030919021212130602070609180603120e1f 68
    0x30341c10342e00010144002554000741c80700650b0300841e903a030795001f011111070300301710702007000c198050381c0165101c001c440c010103080340144003d140c155000394071440b081c0805803c0058840541c004410240b15240007080080c220308a29546d0b82084a0254420b01007181c40d400380600000b00d036486000100480c58012014045511014081210b280581c5403100d0304100006c3c240d5044822407a0001d098400b1505c02050441c281080e80c0d0004204c40018024802d0351041d029000c6d131030740b07401e4403244580150306012481c0c6801c14140001183c0c0300a616200000422003104010707000b2604403281d00e11480e9100e10045a107038068003044614103030a62103c0c1c21294504080122105604c0c000b400780000d01400ca5a042e042156010003c591800005222400da003400580d078801084107201500e011802c0042c0107100c102507104d0316406070106c54281d5060070381a8030140003035600036003264501b200307018060702000f4800042031080b0684002d00b074210483d094620500451 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 577674235 1250 577672985 577672993
    0x20405011403040204090f03122007030305090f01111309021c3308060c0421111003050a050f010b0f0703020102071406041b080604030309241a010908 66
    0x26403407030500e820043c02607074069201c0004901240c2e0421078402c0c3c040c084c0d0b031120072000150105c84140c514420403c41c4075030008003503030143d49140060b620010390600e400705a035101c0e15089450461100c807101d4440d40b901c138030b20740d5800000d0010304c00c1c0c80404c03695035a040e03070740d1080108038040c00981e11000300c5501d011b07001e050141e0f4800da00c542442103107940c101000386001c42041e0782c1c1000000414051101c2400032440c01c1107901c0d801090116000d18050030907a890000801003003c640340241d080724001b003044517070110210f0885025000003d04490b5050050140001f60341c040f40051800020680e000060088541a10114203080f8901a007084408001d0740c81003900b82e0441d5800e00284001410454448844c405400b0041100d0309241c282140e00b001c1020b110021004002420005141d003ca2000d80c8241c041c20300282d09121802c01100d0202d500c0d950ba60145122119a80540540e074000d4140175191101c440a00342c0c18801500e030400f40d40202952a0301c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 577675485 1250 577674235 577674257
    0x130812030405190807080307031805010507110303090c1009270c23031503030408010203070e0a1a07081b100b0409080409230a020903010c08190c05161104060902040501 74
    0x61b040080d43c020f2007900d4001080345162151141c03106000b031045400365154800d21184507070007662001209044c81c003452550400301c90f100e0303482c00c50001107030062900c0c1003a0050720b8001c14104008040c4460f080c0207000d201c44dd11250620195a4181c1c80f5180c80000408648207501d0a4402011015080810749044881840c10340008046c40e0a1020342800f110b129107040c009400107107611000580c69081c070940c041d01d14101128007500074115503104200c491100c60f81583c02d04140b48617541c0c0e84040b800c001405200da00188450403034409401643c0e03e500007050b903140a441c0c0304c2001050a68400c1106560701c0c5000584120030034442800803900c280c0c4541104d031021603c0c2003804020f0501000c407854115a01002161b000c80c1d020540d007428021260000e03024a080149031030021484000c1c0554001105100356641c502d81c64000d006504955180c0c0c0300c8051500030007910703c0c0411032800600a507600840c2049000540796506000340d90a0b1031058503031206400d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 577676735 1250 577675485 577675493
    0x70212040e040b060604080d121103061e130203070c030f09150809101b1812110a030516081b06030402010513050d03030522110105130812030405190807 67
    0xf80152080d58030801c100000910100c1c104000756401ca5580c55018281003942101800c032190403050703004104081080280c0c40e03684000006030029920b50f4424007104410219440c10216086100e21b43c5c4000148003405400c0b05405880c40c0c0f1a40e01c88103d214051801c41d40084240704560a22044407503c41c40c02d4044d01005038060600d00c201e488080103800c04800740c1c0c1e15030810701c21009148003c940c84075030014000328641c0c1280c80d444801850030300f001a0b8503c3e140c101800203442201582034a41d00d840d0494001c54200702180c4414200704502401d200340d61080040341c1c0310b080e0001d0301c60350384840000c4071308100030542c40c11036032250010b6031a940300e03003081562082c070501e011440366924404004a0303402503800085500d00750200f00014040e2103401049400c65045500000f600003610240141007071030000d840300007504200903000d9850300942030b54024440c0746000340019002461040c0d00440488450700404150000329000c45180036160403c03c000c0c003004a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 577677985 1250 577676735 577676753
    0x913050f011424030a061e020a21140114040c080f0610051c020912010e120d0e060412090e0f0a1109121510050d120c1505070212040e04 60
    0x520740c2e245407245a9003e00d40000d0070140c011900310303200c59964200383e40f01c49082a145c40300c055004001c518100034803001800c00c00100404500c401150040415808115041030507502d202c01039111a0356110241c210b1518404140c01e801149405a584402441014014000c01c2c044114100740d4a5a030300748050107000c078001c0001d100701085030080d4483c0074080c00c52030b08260080103840b10040c2003040411400303102c4000c0a80c2c140794441c1d0002001142c48a8070141040c800c9541c6e07039070040d464024040203848414140540310400090049100c01d011500c545a0340b0705016a0701d401c0c04402e600016107000440d21107030700000e112080346500c41c0c800030715241525400c0a85020006217000110600700c00a0b401420303006d60500e8140125a0f041506160191991410b000104044c0b540c1c114015101000030341e0010300311030040880168050700801c11210040e4449145005400203503040700040c49445607040105003c00705031001d40344d094482c1c41907615143c840443c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 577679235 1250 577677985 577678021
    0x101503080d1401030b070807050c03120402130609050103140307030207120c0504180c0e07050d0915020f1c0513030507060b13060e0604060f050904030e0913050f0114 73
    0x15596010302c40c4900302907680c110300841c4142e582d00c0303580c68009001810b481c03001d4840820300030180541d0403030f8403010003503070344410149042040c0f5950320f000060041d8816241e0509442ca4048003007034902c00c5400040c1624000e010314240188203147c1036580388100303400540140c001c000c0620104005402c48500c0a0007030010040a6844000040446845160420703201d03000c160718004224640d034510f0020104450a8407032481d19480207030243c13240708610081107990b007070390104115822203011340842442d00110740b0b03400e0118a041d815400040403882c90b09042442200c4007400d070080a1050920244010351080e0315030f01501c0c26000440700b16130103031b2a841c102c406511010140c590074043e258021440d545403403000130010602400c107a00540c141982400610406031240c4d00304c0e8025030300c1c100c0c2940c45060884000c014038500551210200c5c0c1404078208015206025190080d0b0582c0c0707012244d12155400c841e1855a800c1050003e000000e000340004484081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 577680485 1250 577679235 577679257
    0xf080a02040b0a0c0203060907082d0616020f030f070201032304050c040b011125080307050703030f0320090a0306050405060108060106140d0c091e0810150308 70
    0x70400b6100e4448089a4101501240004e550654a41c040d0701d410000980c0000d1544064103c06040c02c3c0201d841e10072404060460920400f0207190b1001c1ca40b00f00040e0200c05020b40709039080101c180800741d07200601c240014810200c8400780550040b08032985014000b0b282c510342902035005401608010f00c485210b206101e003015006030002080510840c0302c0ea000d01160b80602080004a070400482581000303010600420402c83c0003d0051003c10350200c0d070980c0d40c494040c1d0540c09403450b0451b40e15400042900001c01c0000114801928030985852000034145a8220101c501c540480c10820080e880c2d400c4d0070260400080a00c14030240203003e00310789903104c0d001601c400b80c40444c0d00d517001d00010409004144075141c00b5100a2030f2030b00102c403d041c8080701c4d50148102c0c002440340d0b40e10081c114140103a41c031400914002e144c0c10040f407440c0805e140360442d00d100d980080d0007405d003243c02c0080284642d0314003083c46c40404000a0841d250b400c06030300244007880d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 577681735 1250 577680485 577680487
    0xf0d030906110d0c0912080412020301090c06171506030718051c0501140f07181802180307120308040602120c0706061e0e09100501062007060f080a02 66
    0x40e60801088003c240a040992002c14038a80001008104004a0340600391180c00c20b45054000341166045904545002442d80c1e5001c00307900004e4010030301c01c5030040002480c2c206c0003a40540040d05402004500c008030180f5a49418501086100800761190300007401c00c0080c07901c07400341c60412240c03e520400c030f0381c2c82d580310004900400c0490580512168460f0204010850300b4011000290341e00c07140000d5a0502044c408800c040140c590340c140701000d0300060351501886010401090090402c0d490380b11180170b0b1900950161000500e0740341c2c80f141c4040d4504001680c2c8040301d0958940d90b5880c28a510100e410b24805402154140c0d0200440b9131200c0d015003046005211500c81c1e99500d031810b1422000301c8000d5446014901c0707030b00e02280c45c140002c0c06c841c0c080714945100311116a880c0e00f0000d00f080312007008184032624060000c0707043c5034045041c50395428101c41940a490180441032b80d21900c41c4140340005081203421506140710707240040d0807800c050005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 577682985 1250 577681735 577681751
    0x18040302071a041e0608180c091501080f0601140f0d0c02071e060504090f0207050f030c070602072402100e01140c19030209030c030f07080f0f0d030906 67
    0xb040d00c000001150401c1220b012500b4044484000309460303144800c6101e03221060b00e45035001d441040000c060010390840c1c0308101710100d8080c80a02e41c000b50040400407a03280c10240690784500751000c1e01d000554520005114022943c003c1307000d000144c5900c2c0340b01414140021481e4855205010144414010003810311502d010300c144030720340e54000d89071079030030207910000c0d800360340420b007051440508041040f650010125410b66903920404641c2d00380f643c0b0102d010348129000240548580d0604445405001c00680407140d030b000242c03074103103680d48001c80c0d403007015002d80c0300b01d010806214540101404c12a00c3e0003030680c01501d0401c0000c1c604038044500f25103004000d130351038000001e1020b081010103a4051000c42e81a0305100000d060300103c1716010a0007002d040d400208400300d95800c00004518035001070407111007580d940c006940b984d100c0d03c030321f502c83d10a032050200c00b0240412040a0756405100522019100d010214003038207160f403081d1245ca81e10300344 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 577684235 1250 577682985 577682999
    0x23010c02060c0309030a0c08011407090b07140d030b100504080c1c0b071706010c03020309010809190809130e1c0c1403030601020c0f011706061207080912091804030207 74
    0x36001c2d031076021350030382d02c25a441c008c0300b1825621801d450700070904d008010000d14907000343c40c0c842038a100501c5161268064076080156084800e44c0e41401c0c841e240c40c2c040d2555164002e42024181a51980610985214203903a24040c600a901090f04010700300c0c00e071400c0020060580020200c4100f1100c0c84c640c40e07103540843c0030381d0480c0000d00c3c0d10004074002d07503290361043e40102082ca0020841c03102610b00079283c1c00b91000003410030204a01050200070204907241444564410403203d1040600e0401804c3d80404242405608840b0b1905128407241c410144400501c0c4051320900b0800e20f410002c1d1110714002c0340a200c10341c5c07580c4011a041c0004a41998504c0d00116074a081000000e8605801d4581039131240992503004075a603648072a9166031410401440f400c00d032203101c006803030303809024030244010882204000c05c4031f078050b05483c024048442960304245031480428928403c0301250354000340c04905111a91041c601102e500070f0003441640c0c481030b19515 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 577685485 1250 577684235 577684243
    0x10c110402040b070605070c11040914030d0207020108011a0301030f14030f0d0b121002090a0513050106080a1401031509330e070902031803040602010623010c02060c030903 76
    0x1c280c3d031542010401d00200f151a218a64006010b81030903000310000d40e0301c1c004800142040f59001c0c90b1038280c2001048051000366885d441c1110139039071100d1001e18844000c0d04441c000f40e00003400c002c0009500012907170ba847c80400b1401c13040c2d146030b086403101107000b542410110741da003074424a42807001c41d090001d4804e44204c0c42e035295507645d00b01c0d0b10f0010b0f1040035414910404081d205040c0324440021580b00c41424107001603140c03840c010010314400520352250b03401183d0400c0101424407507510060580718680c4802c0f4036601c900c80e01c0d40480301c1d18070760103a84070945001840810fa80e10000200705c82c540001040f2074080b5968030888440e0240d020310019001205044158141d03140b09001d4480940d04200c1c1d2900541d041e541c6040c144500040c2560000c041031100c4404a074891004880f41d0880c1da40e1907899600074000c101d684189924440c400031102d845100d10390a00d100b80105a4441c0728008498080008a0340b02d1114405584000c00c14101c541d1800d02c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 577686735 1250 577685485 577685489
    0x70e0106030501242a0c031223070f060618050a0e010c02191a0403020309030d03060605030a05150a0608010509091513060f02180a06031109010c11040204 68
    0x354000c5074651521045030442d0b000031801003c004070301c07400a10400e07805685c3e103d681e01841d01c8104d00c5500403034101c400d460030b908080e01002c407005022041c0f011b08002c100c4004c82c40d07a00e84042d01c6804444c220280c0d05195285401c010800c80318020800219206101d58040c2c01e0001c1c100c1e0303a5a02d001c454a00c60b81100c5007544e2110304021404440d4415040c10282c140001e0020304007901000351541c241ca1106401002e08080c4813050144081566490310480d003440025030400d414041d6607a00251042d42c03080c41100084140d10b44640224011151103486441c00c5441c1c3c2c4d5044000b41500a003941104002c0e0075103480660344081c1c03010028401500d80300001d50404041c0810700000034122062940041710f00c03458100f00380f070115800710309090780082001223880d060000d008250b078084c00c0c5600210342c1092072030b0700003903c0705251030464038000c2036651080c041d002c0e241d03801e0880e0700b0700ca018440c409040d4014103030240094811080c07003000d40701400004007280c00503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 577687985 1250 577686735 577686737
    0x1c08030f180a0b041b290a12020d090203030c031206060910030e0a290112050a020d050f010606081f06020601120203011e02070209090102070503041403033f010509010b0903070e0106 80
    0x1c85450354010302c8030602d00c46c0030061041d0780707290a00100c00581043c03c011803040103103900007041825800d0a50198024541c000c1c140d954030300c442e10904e5503d80220130402e460110020104e0001d2500c48112072560001428004070001842c6047e4000d00c1e14048410b0b182c040c814a03100001d80b02c0c0001e455103011004400c400c44012140881c04040580000070030246490195001c1540020030641141d8101d88100540c1c07a070b031030000c3c10140f0000050b0025800c003040407800503000503040c0d21445448121002002c10840303400c803210b1681c03042c203000d40c010f1001071100d44180700d2003814046c00a400440c200c020070700301c040c21040e8903540550155000c83e03440214a4045500b035004071807400254105886034403401d46920441c840c2ca4800c0c0b40c1e4203011500b588050040c0c1e10748110303800318092600104821100c12451550303e065a0360b2290300c0c01500e00301c00045042c185d400241c00407006a0034141844910390041d40915858402c041c070020344018150240e90280c02a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 577689235 1250 577687985 577688009
    0x2090103051f06210813150e0d030c02010f051b060a0b01050403120f0c0f0f050d02030a1709010213141003090f111c08030f180a0b041b 60
    0x904442c034500b40d014411194908000080104501d1444640030710209800c1503004d06240345400080c502c81e0521031034a24601c4070000522140640030306000041a803120a000012182000110701c810303000240801d0301204034001651283c00c19107184181d03420700707030316113082c00081c0c24081540240c0700303510394051000c00c8890001402020318200082c2415030030942140e892000380b924485400c410070803560421200a1f1056510305903058024074442440713403180c10080c1c950030b5442d5041d50070b48a06820502709910001c112008000d084d500c11041d01c240810b1000d28510207000c0640301e44d024440000e8190380e0701350600080a0f0603009000104051040c0606100060b040d5010b040c540502000407410b643c1030765a9a5038008180209a24038200180c280705800d400c5248002c000e2600004010405c40214002c0440e80a0494a6500d01001041005d400060011550001d04100c0005101d0100454006100c7d91420703071469101d21706680303030203402d9000104d9829 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 577690485 1250 577689235 577689253
    0x5031906081219020601060903031404030c080318011e08060f1f08010803031513090506090c0a0509012d1a041d102105060f010314010915050901090209010305 70
    0x2400d4070180f80440c80c980080e014a615012014141149a1101034107000100e00c4405090101500720707006960b00440464090392285c43d2142d580c1c01219025102801e44603041c2c0d8198090131114040d1138542a01c1c0b5840b94180383d040303450b240007810039600311020f108054002d40e98100314520903440c0f2640500e88040c0e0100041010406a021a6458108205115040b1800d480705075180c0400d035090494a1035090390b6400410070b510340a402c1d4000c900612000b810082070304030302d540007112010303c002c1e107903c00c12018450078482c90038100705201c403603002c0b00901d9411105c0145880680030f0482d640740ca0301804040c60302030340008030b04005014018006d41c034001140d08030050a82c0d5030310385002910890219054094400d40a00b0b48a040c0c2a507100b41220f885c0042d4443c06807115402c102440000d1300d00c0030f00044400c220919685012240305204010b5900d80050100c1e0351640c1f47c4500c0c000502c1c0250110070f50b95241c40c0c0d1400581c6030f50760458001c3d41b0500003051141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 577691735 1250 577690485 577690507
    0x110102070611030a031e05092104080703020d0f060906020306090a0b090708060d05151006021f05191803120b030c270414100b01050319060812 63
    0x100340c1c0c00620500280030034040701c41c8000030990709071a5240c14005802d8000c285903140321903000590f8000c6608000400030601c0020442e91482c40d01c80c00460603840d034508540120340142d0003148840e9200080c10000352030030181c2c2101c110b00442207410f04a510f5200c001c1925141c040954240781c0020520070315042982da00c0c4d0b44408452810025220030b60b0020358003d0010b030004c0104880440031400399503d004095644ae94400d086410a410321000d0485006044a4500030151032280005e21a8000304010200c0f404c8401c40c60b180c0c1c882100c24000510001d8145a01180760038194640805248145104000140400c1a1b104414a030003007000804480318041d150601c5d001e59401d440001d4194800c1c1811190241031912500c0380da00d1848182946800882200b402d100074041d51160249a03d1034000582e50f83d00e00c107443c1c0b070044d0340504c030440e80010001c00028070860100e085105c1d4519a0b568007150030703913032039819a00d81802501416508200090204410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 577692985 1250 577691735 577691743
    0x90c030c40030807020f03010f0e1b04090519030507020612041401020c1f02070204090308070210110301060c02010c080a090f0f0501050a0503100806071d190b09011b110102 76
    0xa020007000a402504594400d540303400703400c0b8000c1c00307204074882c401c0b0a44d50030b422034101c2400c1c0e5902000410b595401281d5070300c8008544c0810414075486a001a082a0042d000020b4010b802880c0c00300306488402c00740b000c10b10041d020030106110074001039031510b00400000c5490040c0f090030b4240307414414000040c038004540143c0c4100114205418003060740302040c541c204001080d00e5803000030102900c00d188000791b200d860944040101b640155100f070155140b58200e400304121805020200c40d444100d07020600400e10040081030b205241651000e4410702d0449458182580c0d00b0324260008550b08003c5113954134107000f0304440300c881100801d15035031059007171850603001800d603210303002c042c4041100020002d02d85020403d42100109400b104854192500382c800621103802c4480c400714600ca01c80a0103060b14008003000c1030206000c0f150544070f0725100020100da400080000d0511584400181d149003408485103100c0d4060407007031102d0002c1100083c10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 577694235 1250 577692985 577693087
    0x152a0d0219020106030506010515120112050f0d170603010f36020a03140a080d0c081501020606012f0102091801030804180902031903020c01020c090c030c 68
    0x31689044000c00200b01c00040c810304581d0103941803149908034070030144ad0f91141c0c034540994464103100029124050701c8104030a18000c5043d1011155511421a00d40c0062201c40d000581c200c051400110003040481e41c1014004000250b2000c1c8032030342600f501d01c140c60b00007400e2811503505100d140c4100748219145a8000c0b0b030004091694001a500f000c980409095522a00c110b05103084003008100c410a400c0a030386529500f0f01c1c1d10340c0e000b40c5096249080010501b80109816040307051401c104914160007800080c7e8079070004444c940d0b07258892011040d22400d00051042820343c4012008a4900000d6624140c17070703040c0200040c2004165020b000c0200042000c140c0417001d580c10760340001d52400822400842c180050080301c0e001940c180240f039403160740760b40d1002031b240010307129030243c1d0290380200c001a41c8407005c410950790846402c5000510100c0c0c684c5c000d42c0c0c0032503003140050800c2d0700585651101d03a01c101050900310541031010718514549003c2c1c2c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 577695485 1250 577694235 577694237
    0xc0307110418232404030c0c0b030a110406020a02040f06121a070905010801090c050702100824100e2e020105011a0405041a1306030311152a0d0219 65
    0x28041008104420031038213030102da119420f011502107020940300703860541c030b0250400340903136140d601d81e8100c40e03c6900c1a21007105092a01c0102c031601400002a030b001c0707401680240262284503001d000c0a040c3d03209209011550322280400c00300c41d10400404010300030a2454070086106690601d50000940700d8008e0050341d400410450fa441001d25064849000001c11011050401900c0f01d01400d8802580003000440141c43d065015000320710900159a80c00c01c040c24414215071a402c101088a402c490b10880c18800940907410746c1001d520302609003810442c04c0c0344030381c0c81c5101502c040c903610b03040c43d401014100c0d4240201400f40a842c110071500202120200d00e0505c200c0c0b090501940d00c0e80d500c00040c0d071100201c003500c40360103840300754181a10f011180044c00680011000300d0380e0b20341b81c40041c010014540071000300e6a2007008540d100c3e0b03000c1401d03483d000d5205415922080307a070800d900c00d104003c0d000f42d200700c10015807280105055801c4800c0020322002c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 577696735 1250 577695485 577695493
    0x81b0301020301080715020a0501021204050d1d010302091215061002070501020715020c12100e2d100f150602030c0d122a02070b0c030711041823 64
    0x310203201302003400301c111120300540c4040d14001c001d040c2d0901003140009002035201107803000d051240d0384401480fa910a0040d504140c1039000d00340ca94100ba0b000c1c410000e460750741358000c194000d80c0107014541000701048940000700d50054a00404820a0f9030200d07114400e00c0703024188100d1040a41e002c5002078921039041c800001d5440700944a19101d00e980146020f0220303000380440a21420081e01c12902182045c6182c2d6846410b800310b943d80794942080540003a0300401c542c00d401907082800c00103090310710314454084c0c648139042d541500030641609060a480c0c0305080307030700000200110321514500a04400d080361640710305d0541d0401c0001240119011400c0070200c0c0040c100002ca500941358100c00404080c030843c800006c0c24000300c03403415903140ba102d0010080d41c3c00c451070b550300c907200ba40085c001d401d000c40d51a4018800340000401024110300300080241c400201026034282c59042e4002c00e09007540d043c025000540080c0b525840041c246c800f00c50005c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 577697841 1106 577696735 577696739
    0x5160c031b12021c03112a070f0503060105090402220b060403081e0910030f0917130b090a03020f1504170115060c0f030903060204081b0301020301 65
    0x725130309540814413030700c00b144a40100c280740c01d154800141010184400120b103690700315502041c1612203604050268000c01c0311000800100c1404402103241c64241030801d401a003016000310503060800000d44c50702c0c0d22000402c1400d01142003a12020303206000200b60710000e07594000000200001030100071703006040c5000001d801c0c00c001e0510040d1a400c0761003080c6c045e07908075903040d8540c504a4040d9128030b4100c2c20948005c60041000d82d240d0b540207004221040c4000c130085851100807040c20902000b4003803491609181c0f01080d000a48a0b80c86444001c0c41943c0c40302000c081a00e408400100542c40084400c2d01c1383d4581c8015003240226080042d101c0d0310303012000308202c0300210180210380d9503440c1c1141c00100c1d501d03256a244121003042d03041c840d0041d800000640c0510043c00140149809803d80411f005580300d80d07800e01c0280d080c4268018401 = true := by decide +kernel

theorem cover : BRFrame.Cov 577517985 577697841 := by
  have h0 := BRFrame.cov_init 577517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 577517985 ≤ n) (h2 : n < 577697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
