-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1314
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:19:38.085604+00:00
-- url     : https://prove2.me/submissions/5c4e8f95-f2aa-4ff1-a23e-4dd151ada56a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 236151079 ≤ n < 236330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 236152329 1250 236151079 236151107
    0xb0d020f031906060801051308070303051b04061806020c10080c090a080a051c090512150702070602210403080309070b16050d020601050303090d15020d020a0f09050109090914011b 79
    0x3231066032480d51b070310002803241c050040c00705a16200411030f00f5030f01000400251601407000c0340e80d10758540c40903016840b03104808243c1524400d0001c0ea050001c43e9010310740700000c00819a0564a600507505070300301411600e58607034103104507007a9032a98108807005e0500d00e4010000c1d0050303032602e01e10300b240700c0c8104400c84010b070a482104a400c943c1c0315003507580c1241c14000440d50b090034146482004020b44259200000900860702d402040c19000d88590350300f603420100c030414801c0756601907000420700242c02004204003140c484401b4603040f08101d0280c440b21952240044845d030400b000043c80010300780005c9082101c10011407640d803c40f4005004103601d06000251a0301480e11114018060f600c3c42004010300c88c0607004280d00002011521030f0758407200308000390400031006002c2a0310f223a0012490380202c10503030440340e05a40341d007002400c02090901030117040c4000c5650500d40b10031229622028026290000412442e03921580c11209009001d44158010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 236153579 1250 236152329 236152351
    0x403030201060e1b070201120e16050118030809012d02010501060314281d030c01150b03041506030602121b0f18010215010306090b0601030b0d020f03190606080105 72
    0x8013103220f004400554000ca40c090800108024a450300400903102c04180400103008000318503114103440e9072410244c0d002030340c0312155130258030034041aa20503400080c10181c014031000c043c6612a4006d0707407a080c130010985a407140030300156410512004071000140c0d45410061040326810700c1181400b025465588045082245240b152281d9080c1d40b10720100710301c0380114004502d500040d55807501d1608904c0310060105069440760044c1101013542d500b0400c0d0f20980c1c0c400ac0c0d40440a4a4079100d2552942c1c0320341d9070b042890010000700d020309980383c450000202d403443c4003401c00c4075145d00f400c2030b051404000c0c40c52100070380028400e80c200305006810045c00c0c25002e58144506075448014540b21540050345401c1c05508442d1003e80b0400000c020453b59403c9200207501c100a03101d682e0b00c52400550550b501e840e42c054200107581200b10262070150251690901d002d02038903040030030341c2e0120f140c1c0f4504030b4096030b10b282c030b9101c00c200101c001d100e903d0f031011501c80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 236154829 1250 236153579 236153611
    0x30a06020a031a06090409060b102001050402031203073c05040f1e05120a0302241311120a0506060a1212021c032306101209080403030201060e 63
    0x10301c140034142c2540e011b5079070340701c0c03600c200701d804d40c04400d00d82d00003000116800e010030300c001c0400d1943d1140c405500010b624210303074500d05001d0180580d40c02009062404100444812a40c00040c2000104581c4507075017204510881030101c000d08090581e003100c19445140c8603020208505860100401040104a0210018941c03001d503200c8100142114010049092500c40c2c0354110304e0b48082c840807a00d82c030030400200c2c039114a12940903600115500403608650381107131858582c920396100002000514010150803a0a200d01200c0342c545c447c03400030038504001c0340c1d48900168403c9020100f031280c01c2040340c0c1d101604a44000c0c4060508030b40172440321803544020604c2c1160120304132031600a005059880b010413104800074849c412008000d0300c0c0ca020340d1106002d0002d8031043c0710421441c024407400c1e001c5e180070007248158104079240004400c9940c400303642d414240c00011b070160002d10045001e03a0012525900f4403034134912140d000b40c105c0114990b480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 236156079 1250 236154829 236154881
    0xd020a050d03090807080301060206100b04080c040203091e1f0b030a080a021222090507020a020f04231602030301060c12350a0903091e0302030a06020a03 68
    0x1141d6020000901e00818000318a1514540a025140c4020320102021001160403580040c0d0603105001204014100d25070760902d892881c4514041c19803140c01017050356106040a03002950000ba000b8112100346450700c10b400c0c400144151210030030b4001c0040822006001d000d80b040c0d4800c4c00700c003040038543c640300090303690320b05410090600b40b010424030031240c001d0000c40710030700c4819001aa02d40d40d005074030b00307041104a012440103480c040041180c000e01e120f840c0c4120308940082030900500d40801070303c62000f241196219440b00c085005488103ca9241003501d032010204015050101d248150348481c080d00100310f62042c0010065240d106d0003030b09030a90800d00c901d40c07020300c0000031164002100c41400700008829800c2808495105c494003110714540c0480080e0303282d54440c0f0b81520b5071641e02800098518034284003000d9041d40d00f208031043d824100150a42c0c0381d000c0b90a01d813111200351041d55020810440c008d4150242c0b0202c1006018507102d002312103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 236157329 1250 236156079 236156083
    0x1707030e06040b0c041509081e031602060d020a03050a1802011209060b060715060602031303080306030a0605040503030901050f040210030203070c080d091518030c08071b080d020a05 80
    0x40003e04242d80307050100713410074030044c102c501a114403840e15040741200040074104d040d151088181c54031030a401b0240c001c4010b0440b20301e05a00300007441c9002d440c94040c50200c0c40044040e68001d504000031048074045100400283c81d40d0b0b2004aa9440d0100c10140bc8440a85c40310708914031300000ea8005030390240f41d0a00c040d48080d000110b00025040040007403502a42031604203900264440a2107216462084c8504c270102d410301c40f8948900302241c4900400c41e103004030065a600900c00520040083c0d903115101408441c2c17860f070140c803200144c56059400b5922030b00000148419481c080c02802c2e4482403041a541d828203255012a803000340c8000403204055010012031009482100402881754000c8041d175120155000008024103a500d42110900c0b00d00c08100301c5003800740a03542145031142c0c4401da117200f1584054961906206040301c40310000c012400000d0a07a180b2581e01600b14500414160301b013210081c03416010320107010a5610420300f0b08001080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 236158579 1250 236157329 236157331
    0x9100b120c0d1a07080103050f1204060f0203070b130b090c0906060702241308010b060a0309020a030b1e07020c10110709050414012702210d1707030e06 67
    0x3582c4140e803414050a0400ca4110102c11000312980c011051010884d84400311a05890107101500c0308405405021540c81900341180a21003c003400b003005840d00900303c5c11401209070059a1500070241d03501402408210723242c44504100b83c0e003020a010030008140e41c40711600b4020045400e0708400603402c0680105414418040010080210b441d003c40300c2613140e071380200014200741c001102c000d60b9000b00150240c101c1317802d040000c00d448140590502e400000e0f21403031a100d02010110b0140c0100300b030581e0820890f0f080000012801049030780315503217400250380c80070403029048039040d5014040c81d04544c416203480e64150368035a00010884001e0030900c02d4103c1d40d034800c6080042c9036001e100081d01e450204410720072242c00c140b1424080e50000c00c0341041e680a202910720203c03144c100c5850740203500030018180a0280c0b01c9a001003004028002007800c0d045141034003a10b4200000750f0308a00110500d40c2806526800050908051200341c40c1c0d51240e03503031000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 236159829 1250 236158579 236158603
    0x906080112020d150c020a02040c0c0206040308070602041a0a0306050a06080a1d010213050306010806010f0306050901060b0a0e130203160e060903010203090f0709110405010507060f020309100b12 86
    0x10854141c0010010107407005130160603070f81001c2c0f1280001c94000313505c0b04911a4103a000c0c42c1000380981c80b06104100d50036103194020411800c060a44d00c50145640200034100c034581d0b42004041040036030b40c2114944c2840301522182c1d0303070300c0e0749100a0a4810303d901441c024007645609104c2c06ea0840d840a5100548410020750b91141409072007640e26298111402544002101c0c1000c210f0118030300305844040d81101c0322a40d1b0b41010a81d0b0b443d09210700c402c158000d24041c0009203103038201503042316144001003040390f214551348605521828034103011801c0340e1007904043c1007200100c0460f002100c81141145020f00008a038500000000700400c25071709080c030110b50b07031307442600c03411075000d4001c6448e40381442e1205e9032181e400007550020b00c08c805000504c0680c17409104030307106c8040c8a45040924000066a03541c00078001120701036111001400b1403031441c8007641c46849890001c1c051070009109420403110100e1800d805056410b02c020b501c0c503400651141120 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 236161079 1250 236159829 236159839
    0x7022b0f0c1506031a0106080f0717010611010f0509190f0f0c0e0c070503090f13140105010e010207080c0906060708030403170609130209191506090608011202 70
    0x44a038500c11600303400d10081c01000304803049610115603a0943c070a505030303485144c0061220300241e05100c0c082800344100d00000300e034107000501c150368011500d5000503143c10030a0013201e04c1000348109041c2604002c0004104440d54034403044240181d2550802d19141000a410000449900d0340e1500026580e680074070200f24040007854048100c0060b08101342039900c81440c03070500c241c5091441035903040344122003c2102c1244600071202c40e6903001d4000e40c40c0134162400e100044100c1c5501036803115401901c07035044801c6000700c2c5e10a1141c211041c18540c1854005040f0f00c0d10020315071304561240e00207000c2503a0004942080324411a401100c81da646000200284501c40006111317203004400e1104058020000300c03400d0686102e120314036a0b841081c48015001125a01e4541c200000d0740d5000d414040c00d200d400550581c0340000c4058100c1001e401e9580501c120014840c0004080184035440606640580110301d49881c02c1d514110072140940420322010348130b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 236162329 1250 236161079 236161097
    0x7320c0c04050406090203120a091806031a0402031605010503010e090102090a06020a03140f1e0d150e0604020c031801120f0f05090f03040303030509030405031507022b 74
    0x642400c12a8100008005005000601d07203490010043d10311024100e0291107400001640da03224203065a000c50483c0d42c421003294a4540e2440400d0030019010030060780c1c400e00400030aa010b8041e2031002c2d10241e0103059401c1c0b40c4185071030302c49040c54900b0400035059040c403c580e4090210f03411216031083c0c6403420748031020868024841c410055501402c2404000b404540210700204c9080c080d4440d421851001c030a882e01a11501048500001d0100596000396001c06803000c06114101134080c00c20f83c0c1d144080341214041c0003500243c80502500b0000d0007184054182d0141e400c1c1c904cd801c0885640b019030b81e07406690700f2006040c800381c0d0320082d264856088202c134008110400c0c00001c281000710001000c145406241803420b01000841206c0005032610007075807400000c6107070070b195450841c003c0002405601e2a4041000700042d00d90b07080110000d82c0d60300148420440c00d000070301a01d484601c034480b510b0a0480c20005601040c1604070040a52090404100c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 236163579 1250 236162329 236162347
    0x120a0c020d061803020d020105010801020a1407051e03090f0402090a050d050a2102060601020106030c1e0308040b0405090f060a03081c0e030301180203040203060726010e0732 77
    0x50302e440440c0e404480380f444000030a0650000c0c0f041400ca4840c1c000300000c4c2d0301c520b9903900782c5c80341000c00750200380390f01e0504e080c0301e0039103005000710382c0601d05803450304043c6105411443c05048081203a60f00100e020300003441d041d810030b00820030481c1e0440c82d10040d0000b294124940d84200f9102e1012882c410042c0001030010307042c2c55038031110800c410080c812440c04030341c42600d000c000600c110000600c241d40144101c1060742e4200241c1d210081c0303045100c0420501000180f071403407842d40000800505000c01800c06805101120b64945003070206022452000425212820500100380300e5541c865140840660b500640b1032580d0307814244081d5000584c0c0448642c2407494254054401c0e40007202541c143e40c40200c000c04c0115807130702c02d04168002910081d5040d0808400b00c0d070218064000302101c43d81040440765804142155039440c0e0109a101c40c81000c0c040f0200403d45038080c48052503045001802020308407140c80c211400c00f1050004100c40c1000510014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 236164829 1250 236163579 236163581
    0x4020307031407031a0f010b0f040504020f0c12190807032901081303020c04150506030403050d050105100c0303050402060408010c0903062f1617030603120a0c020d06 73
    0x4040c1d5000110300250038440c100e59603a07160284001d03900341e40f0017107080304104485000e5030b0180c00c20360681c0c40f050342041c013050502d030702c8400d800040240400000442c1e4403070b40080d120900b50b5444864507210b0b41d0b0300301420424140c400c0184140b04000d00113155052100800031080300b481c00d0704444d650135005500034001d18040b003011100f4080303001c0518044c103568016119080c1e903640e80c540c8031201c0c40d00700344840300d10040c09a040a84081c1070307400c080c0e100c2e5408106a449030b4801e551b444010030320070b6205980640019900080840342c40c042800b0321401428261110003105c10031140003000341c05201002000c058561011805542c0c0308001d035000741149000030000703605c02050107400d00d01c1e580300407035250381051404016012508101441c03602002040641d030503500e02c40c11a264072162682810b215851040f001140d044000d001781c4103410581d00d55203003080300402d0325114a00c0503440c02240e0820600d00f11560001d0990700c1e2960588107110700d2401854050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 236166079 1250 236164829 236164843
    0x20304060c06090c0902030a0c080c1602180915060d0201050d09020d0b160e0a030c1203050c010203010b0a11010b13090804030203030c0123040506040f06021224091e040203 76
    0xf400d000c0140d04017040c8001c4690055004466a1070204900540c0703800544845da401c69080085200030301c0713160a4030040f41c0c80c03400c2d110710041130302c605007a20740c40e50070390b0070313802c0d9800e82c0710364040240e0800d01031000401c103400010488612083c00c4040c3e0000b0a18814182002c0c42c4613190032940d0b0841d2185440e0202c00c1e540540100c1c1285400e160101305d036842c482401c0c00040a4180e0214a0305044d0400000d9035084841948190b08007061011100c2c02c104003203080000401045002c08001c2c800386000e0411000071990b140707244000281901c1d450312002e280c90340b401c882c1d4841a40e0f80501114032000781c020118080e095824880018002c03a40040d4142c00001000039007241c0650004118102c8a18440054030507509500d0850138203c0f00145036500540204010a9414403040589485480e02600c0d0109054010440340002e94281105005980b54025522280b1030122409103054449055910f465a01d0300c030b0904840425451001c40d8501007001d5403014001e06c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 236167329 1250 236166079 236166083
    0x510031a012411070e09070e10060302071704090c110f0601150e030f03070308090318040209061b070602010c03140604020904060e0117160302090403120b0307080601030c1203020304060c0609 84
    0x2486101c0e917504804a1110002c6442000c94080e45c00049119240031701c0c050f0041640071084c401d068200f034410b4009512000d801d407030100c02648600004146203002300701403c01d800d00402c4601c655640507046403c030400030501c0d03411902414692a10024020741110540060f00240500202c001e4500241084059030940140c0440d04800b80c1c00100a0603428800e94a510550760b80d0003407642c590083c038001003d44d00e400698440145419005004040300040c142d0703140c103a003114a121108010b00d080031054002017000c011640c3c0a10403400e10b07030700a043c1480b40031410b0032900080d5000814280c030450b8007045120712074803a648510054a8110784a40c101c1d6100d40010402002202035080399109405191003c680744940600469a000d401c2210315243d581c2c05550070b05140020440d900d555880c040310310380d42001600c00520569002c0c2030345506500306182d604e01160081000001c449201c103001079400400c0300c0444900780f80503994508240b0340340000e0a08101c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 236168579 1250 236167329 236167333
    0x507080910110106171b0a090f06050418230705190e090a061a06071103010b03031c0b12070e07110615030115060e12010e010510031a012411 62
    0x101751031049900000e00540380c10210b031843d45105181c0a401d8144120703081c0c100c2107184040054009036084002c4409880c0d43c00b14026071070707401040403196000d01c1040b5094180b00701d0070900180002d034008101603d51f2640d400402d1800f1729070380d00843d1003102c1c06856607071041c803402e400c400c60340005401401c12854039420000261547d412586405643c40c5140018840821250b0100f1604a0f040a4210760074561036440301080c800e9680c2103550195250f18240d00d06c0d0358140018164080018040c007445050000c0784e00440d05e0500c81717075019003039404410300e000c5000038808007150130008074104980e5851804a8101108040110003071103640c0a0040559104d00050004103040e030080180751031004100c3c51002c5a0701c11103020440e03500072070680d424880145003160100c2400030480c11341c2d404200f8211103040350000700d911141003043c400c1081c400c40487c3c10000e0114810441e506000c407103800c440c0e040900420a20072502043c01a50081680b80d14070021802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 236169829 1250 236168579 236168591
    0xa0b161209150809070e0606070c1e1a03010e0603190503030a1b0c060f06120b01030204060501020708060601120b030607090306060906080a0204050606070f0807060501050105070809101101 83
    0x2024095200500659418030703440e0165402c80d52003414020302c120050320080846520b0f0012485181c83c014203d182c0041040140310302151150318448014083c0340c0640c004850b291003001180d0a45400030200b40a014001c00c00546018080c0c0c0e0540d80d04441c00082c07901d134800000d10b8950003244603034051a108848a092200203c00b07148140104941401800680c40d81c580c1906e52240020002c40c5400c103401001c603406030f20000102e000300c200001c0c8107440f6481030600350403001d0101c03051018000144114102801204001c2400b130001742444d03400c141d20744c0d4071084000d044904000600c070040301c2c040040d41161803000700160503210311b0304120900402d1001540010349405050001c0009e40782100c0c4211811100804082c00c0070034420340c01c12000c0c00b805850700e588000c0500045010810515001070788510941105640740c28928080c82035601c160f001c0b5050080074000d000c080b0b01c04004480d41c051044030002501040800150f50200003c1000c003038940c0303895 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 236171079 1250 236169829 236169863
    0xd0803100509070305061c02010c0308040311010e01060f08070501080c07020a091802032104091e0606020d0206070302030106080f06030109060f0c0801290c010e1c08070e0a0b16 78
    0x10388624001c0e0310070759941600301780401c03003c90007d051200003800120048445008240304003801034016210b45008a4030580c004141425644058000c5801d41d5490800b00004140c0d01e100000512810000d4003250303203000700207000e8660040403001d2104c03001a1340011556900034580140c41000410091414080e4484403141940d4034105d01912503030040700080e030301c003040340c7c1255400314125500d8241400d08203000381448503601c0e80b1391580200d4000414800b802003101401082d801492120420070009103000009015501454810401840703000d5218007420703403008040107030500701d071a01c002180c010007076038002409003458160321101d042410f0b0070041c00c1066540c0e070300c00c103641c03900c0010068000d219048055203000c08507503200c80c2c0520018120600d0380c5000042d056540d41c90250070010243c1106150380c8440c190314200d00e8000c0c15035034020f8001c0c40e0180303c100700030002c220380701c07402c0c011541c106401144101c0d14103180012040e09562288005445107000f07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 236172329 1250 236171079 236171081
    0xa030b0613090f050c0f0703020c0307060c1703010e01030f1509150f0b06070f0f050f0106030c0920031003140d030501170a200d1406150d08031005090703 68
    0x14003610b1111401c0290702d0f101012640142c0313016050300c1901c2407a081c03522524649540c00b52200b01d0540c080c1000c1500e00344e406008080040c4090f4440400d8031402f0310b014890700b10304071000d200c0ca034418001444401b402e4036005040d290700200b076042c0307814076081030030020f02c0710212100c81600706003000302005210107450400d40d4042c4030a1000f10b22554880d030a40382e5403158607421200c2400711a021502c0e8055040146001c3d40b159104160b032600e0306414900091841407040c1e444a508008010689202e00001c100c00c010400a800008010100a86841041e040d800c60080042001c003a12160400300569204c9140360822034440740b09616141c1e51040180840c3c0b401000007a2582c403102c1c43e0b01d10550f1304002c3c202e2800c03e91b85880c5408024840d83ca00200540860449a1195660500300f2401829888a000000c3c0788540c5003040041c8403003441e0141c40700010807074035940301d020246680040b256440e6558191a0217000070558400d0780e200d980703041403051071501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 236173579 1250 236172329 236172367
    0x6070605150f010c2612070203130509010302091f08250e040209130c0e1320060f0306040b150c010605040908030c0a020f01020307020f0c09011a0a030b06 68
    0x1c20384007030329642442801900c800d40e1994028080b1000710030f00c658201074900581002040d4001890304010421400400c0345c6d40031280500586e00000d1905185403501011000500045848480a60555000c18840000984041c4001503540c01d082e40110002c1802400f400d0361404075007415162483c2075150040100002a01450926010903500c0203a4105841030350040c101c00700170b4440e02c11400283c0d00c0c0c0d0405403001d21189074049809036402c043c0d82e00501218801d07218880c83c60070814480c0e105030240221500040e503015250751600e0095620710400e64103800d889554200c0400e0242c011010007561011000251503020b003120341c054600d08220f10000c10000303850704188000c03200080c1000d4041c00c02880001c80d440b100c0001031141d0141e51058403143c00010240c40d080e60020380b500790140e0405600009000380030080b055070142d080b1400e001c0740d4500301540d0101c05c0c108440c640d801d80002840c054060103500a4010707120042d20003070340e51034401a69080c4501d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 236174829 1250 236173579 236173621
    0x5040501080c0604050d080c01020d05091e0c0d060b0607050604031103070317060402072001020d1d040509071205061501020109020108060427060b010219050c010e06070605 76
    0x11808002140c82040001c981d82c42c0e100c003800d810b1406041508011004200302c208441c1d0304002c00401520200c00c0c009010400940c7c40080703440d0900360b40d00c0707080c0b9401030395400001540c0410052003490005a501021409850200c1082d503a07061000c00781c0141f2178102d8104500045c0300080007000108988258004e980c2c0404500c0c01000c80ba4882c840d04401400062110302041804102401a142c11100080c401880c0215036070b1803e00c2e15585210003c0310b04100994511917580500c03850030714816170728000407a246224031000d248814001d00d5406541c0d11800504540e40400c04940a000e4002207840c0b400114649030350b82d00821110344690a25506400039103500500030302014541c140c4803810a0354a40e008d2000400f21407500c2125580e064005d40b0408298508410724103000e500d000c5401c1002d400064501001040500b0502c1e18460000020842c0402d15640c205000d1074034266040b00b00c40060700314007844401609082c90314051000d006200c03065088844 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 236176079 1250 236174829 236174831
    0x5030c0d08041109070908011530110d1e060c0509031e100e1b010c020d0b04020613083a050903011b080a0e0109020604090203190c05040504 62
    0x540482401c482400050b540103000414001c8a100342d480c0894920b54000c0561070081191980c030a07c10b800e6074960740d11540c01650382ca1003400310f4900d5541d004084013101c1d014400613220790402c00c00c104415400a4074072014581010002c0c1ea40000c0b00c01202d4100308042c1c8010301c00c2c01c4221016046d040708076003c514108942940da4011400c1d41c404000081c0500740105154100c038038070104006540c3d0450040000c0c00c0007102882c480d000a00c0001c100a16502c0d008445040350381c101c0b142e00c00c2c1881403482c0308400594441c1c0308024600c0d4071410f400090384070b03031020661038000c2c0401080203114000010072010000a0518a801c200440c2c48801d8040c00f2054080c0548030b15030a19002000c880b00d451860065009091020025000064a865100705d0100303801a00c40c4400010b101c8209212030103440e40035203400b24280c0c0c00200006e800315030000e4124810792123402c2c3c5003070300400051b44a2942000220348405006001c0c4105c18072600010020b9006020b42c034451 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 236177329 1250 236176079 236176093
    0x4030c14040c0507080a020f063117180a0e0604050601030507020c120a06020a02010c080106030608060103030c031106010602060610020307050a0b13060c02010c031b2708060405030c 80
    0x51500d40141116118a038031018607150040d245c034600b41e0f0012035190154803d509002541c203108104541c40383d90902400008810380440c00c1c4c211602d01c2704100801c1071240d0314040031a41d01d0210b010012006940a03030b0394400801003034451040841605e038031070503408000400c1041e13120a180300e007004640401c06030f581c0000544c01c544054400800607404107a42300018140b01c1c6424502501c52003c03108031050f10b940340390990303209030407050041c1d4403078001c0800d294102020a01401407800c0078010301d41406e40c80da0382c803101448050b00300014401600c092601408000e40c140d01100241c2ea0a503031500c1010755150004c0d11444d005a010040d460760300c81c03010081c0e4000f1540700024000c44403464460458408010700180484040090384200241d5244201020030155070004560035014550240c222604415100d601001d042c14856200350f121400410070b8090501d4840c01040d0b6110031802d102881c2c02004080c0701e0002804240400040030700300086c103000c111280 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 236178579 1250 236177329 236177369
    0x303050106080403080c0a050702040203041a070906020a0602030a060503010e010603050c270a15090e0705040204060e13021603090509010807060203030705070206070b1806090c030a151104030c 85
    0xa030b0040700c02600203525200071402c090000c60003008107102c2841d025042c10582d40010b8201c0c0e005070742c129018814010810140c8916083e5a42d02c00b841d802c0c0801c0340b80c90a10041d40f580d40081001f41034541c004001543c400155000f20050200a0020006d00b42c560803090300a100d98041580d06206070079034250f591410300c2003603100c0342401c64220030005c414004150792000c042c004080c040e440350940d00c44c0c000204d0401004041c03000c0c02150304180b450459007450519003046009a0042109000c40c0d9004050059401001d89801007506503131203000009004401801840603802c01c40c0c3c41c00e15901240030410b40b001281c442c1020b990340c0e000640e880201d48a0304000d038200b0b200180340d490203400641541c50000c4c1c0410310301344842e56213101c1201c2c101c0707070500e80001c1d4108002d400d407020880107521220040041007070356042c20020755103010011006082c0d8500c1c000d9036580b801d141d04411540114145d995445917124134118101ca045400307031311b0300c5020b9031211400b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 236179829 1250 236178579 236178587
    0x7060605120c01110a020d0f0c0b2703160b0405010e101407030903051002030106030c0206040309050d03031e020304020117010b030c07050c0a0b0c1011040b0a090b0c07030303050106 80
    0x44407155641c01402c001c4011401918101a4284201c980b4003541c081caa002d0707180c0e81060601c50384214501c507150122458408100400d50f081100c1000342844005031200c0c14000c0000480348890080c030200c2843c00000b03103016a0504001100448080c0008030074044001800030785d4401d807111480040403405010031514040c00610000300300000c500c600d241c48500404541d402483c1201c090b81d1241c480916215120201004480e4000010802240c0c148110545510f144c8040e210702d080c1a03d004095106500034680719682d402c400c00304241c004e80c0641c6a9544044a820425608101c00d41c001d4004903402c1e40441c0030f040c8440079084880703440505032076913004c01c1c0703045842d00c41c2103490ba40c0051000302c4a0b48650450108180d5890034818000e10300980e0507540c3c2d03091071900c9401c0035070400d00300c1041424482080c00102c44002558243e426240b510f50b26049040011a41e1000c81e40c01006180400281141c0e444400f04030750058901944040c071490b640e07154101d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 236181079 1250 236179829 236179849
    0x7030e0a0804030b060a0b1305040518060606030a02130815010509090d12020906030a0603060b0d050a02040c0905090405100c0e010815040b030118060e0a030503041506030c060507060605 82
    0x400c0700c0c0c810001880010160b00d150342c3c120001034511075050751940d940664547c03086c80d00301408801e040701000145480c0c0995980820001c00e44858428201101c1e0b0360b40902620b103d10800011000a01c0540d556042d030340d550340809010401e0960b6030170f0590700e80d81000741604011404100114043c2041c9400c940100c203602c0081c078501007111000c54600231481d40a0074169000c0109140d540c1e0f451018500401030f242000440901c2c1d880c241c1c1c1124040040c0c80e0207240e40d04442e102043c0c011903015041601a94082000390400c2004c82d0942026080998007000034401d00043c0300e000242c5e024000703503420b0100040c001c4504151001303500100b80a00040d1100d0010302c80511610040012a038050030104003511070700002402c1d502804c0102407842d907842d104400348012030068040c400148005402c1c0d048441d00c0090035480010809810758203d14040404280ca075804680103541140d200d40000c2c1d201c400083c116408601c06480c2141803070000314451404040c0c1c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 236182329 1250 236181079 236181083
    0xd020d0f0e191109093025020301180605060405061507031202030c0c16050120030c060c090301050a050106092d030317070212070206071e060507030e0a 67
    0x420b0035065a03540e0881c14081034800300d603c014101408000d9490b02c80125009072099805040760110801d0701c5080c540003010800074117840c88020205a03002e8000302c0e0340100da501c640914880c2a506001d0074000d14140080d010741c07900c1000100c1b50710692101c0d038024403440c0140301c95102d0178104400d607942603900c0e0b544095180034a03010107448500030403c4038820f00b4807410214cd4545860200d070422150b4420340200010007030705414041c00303070b0790700f040e820a4620781803414840028070309503041c40c806031803008102040610704410404d892100c03103c80100e40c1d807490300d940d801c5025040054154025170030007021908034402400380d141a55a155200400e50b07180105400c00041c02d10310300048040c0072030014220701072001440740034602070748441303001c156130030341c2030846000042c000ca0464100000b0084d00c40310312811108100d804560054480d885030401041400442030004201400310192504200143d0000340c49001d054400b0050021483c810644601e420000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 236183579 1250 236182329 236182333
    0x10e010302093607140603040b0a0504050703080a0e01030b0603040f020609040b0405041b08030a140f04050613360c030e0a030306080c010e0607020904170d020d0f0e 73
    0x16040d011554440c0708691440800398018a80e480e95440043ea0340d50442000742c208010a0040300c0400601180050050300c510b8990310b403988940046100c05094442980c1d01c2c1e002080c103004082200074060754001d003c1e2680c0e5681c010000d0000241c4205450100e42803504400300d600d04481505c0c8a660852481108041e16a00b045081e0340306100740c503485a95400b4042058559103e524440c2d80f1170212500100341900f03005810780156031241700c240d402001029a01907004c016500c0c9481510f1a01d82c48100101440f80ea41c01203400942d00143c0208540310003201340240c0508a0b007005c07404d003022603500700f01290a002150080030540d1403010806200440c140e000c0e000c100741d903150018410049182c01c60030064603080a41c0004c0e00d58509200184041c4074070701c03000e507003400e111031102c0d03104010036645c0c015030401a1061403e40e00141c103111340c580303d68400c2000c0f01c54090350380354a240c6003c000d402c0f004280c482030345840c0c5c0305010f40d0000d2189031901252000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 236184829 1250 236183579 236183581
    0xa0503090c0a140108100909030309021504081213150305060f01020304060212030a020c06070c1a010e06060c1606020120030105060301120f02040c0807030e120f090d050d02030909010e01030209 85
    0x100560f4481c802406c04208500e58880001e03580c2400c2c4658620705204c0d50300840c0c81078030340c010084903110351504000074040400081204040004d91080c0b60600d00140c961100c0181481503150b0382d1541c031446122000079101000250303d03901c5a449031314100c034041d013000b080c0001241d032030046005050141e84a420040c3c440b0b00c541c0c01856000003005000b52401315885152410054107403440800b040c001441503080024124031131a07a00d01001c0b842d40507600d000180144628043c1009018980c00071302007410302c90500104101440d215400c0944607a54038009000308080c24007030003a84861075810503014071107000c1307074100c41004020600307590078201a400042190b00c0225011a0165000401030320349000b501c0d640c00c2e4545408900c0e1038203030303005001e40c3c0503000d2404e15a0040480b90b0034901201c1c0640300766440b480516511a40788101091444d00001c402409510410002109640d40000141052301003a80c001c0056607859200c0e040d040002e0200a50000f5904 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 236186079 1250 236184829 236184869
    0x1a0103020c0703021e0a0b12040f0203010e1501080706110304091e0c050910030203040f031d1302040611070f0303050703031811010905061821030a0503090c0a 70
    0x340180c0040240d40040d220b0a6039664006040d240c1c00c0041c0740d004940c00300c042085072400d5000e2000820010990740d2404605010841c1c070404001c0c0000d084807201094081551000d512088070700316070311708803203030501a0202201607030710901c42c5031003620900c0c00220b00d0700c0c0700b01c0112852110080085040604280c03000c0e01404d24003c030007000442d041c3c541c0e9401d0016008411440020f074485503519030000007449500d0f031840d13070024141801001848001420046030740b148941514198034800c8500301c074a62034039050400ca42e40000002d45928421070540d005104980c440c4d2a41601e28504c890310070389551191155200340891907401b040424001ca0003003002c0d80c4203142c00103889031600071000c81c403420003000751a03080c203503c074083d000d5810014000192000311002818140e81d04c4800c807012070309420041c010905600643c1821503003240d0280c02148a2090b642c44000350440188190011a0030410f50300c40c10030f819000e4100028050181c031150030b8840135484e014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 236187329 1250 236186079 236186081
    0x9020109050f04090503040e071e080a051b07080c07090e070608070221090102070e060d06111204051b180411010c060c020d0810050907230d1407031a0103 68
    0xb84141c10580f01d401e440c000800500007040640590300d0b0b54032032402c2441000b004200e0b4041c070042040b541544900704142c11610f0680e100e1510710000c142640c45442249030b00340c0071120390349208130101c1e00508000c094405800000c0040003100c50280d951b0745080b050b601c0100d07003203801d82c016040c18080704c1e00c240d83c40d030341c0628240111380c660310003803900c2d03050300d14269100713030580201141182131903034144442e0b0020501d1900c1200720b814480d00081405144400081c02140c3c3c44540744c1e401202d4a0945404c07182c5141020114940382c00c01d56103844405c01d03210b02d008054000c0c0c0e5000e01d0903545604659008d07050001403a44d070ba40c1d48000881e060000c9078140068000354074000f0b02c09004035100703100ea50b03000d031071400104400906030880142c072080e800c2a021a0030300c071035250041803c3d44035040c1c0c9000700c9843e41c114550150304c40301c038450a089400000f41004045940d8100b003580c941c3c0d42c20140c0a82d0b5408138202c003101e540c0c40d4620907006528403141150f61103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 236188579 1250 236187329 236187349
    0x903030c0318010209270a060f090c0e2115010305060a0b0d0c060909060b1c0c050f030a0c0e0301050f010303110705061201090b010f020a0209070302040801020a120507030902010905 80
    0x2941d000501d412010720004180860200b54099100306c0c04000d00c548000f00f02540b9006036000701d090204605001e02072115420f03a01030000d00664400040d03c945100365a0040141d0f00a00b0020344600340c00d0111010191803454074045210b0404811200060169414101e9800801918150f250f00086401400094070050780c4125035854210115211300c2c0520010411034884400d501e14080c074071420343e840c0754442604070f10240b10194440240104003a010140680000742c507241d151000d07965401524031059841801108000001c1c50940c0049810503103a1500c006a42c2c13218105401c1e110122681415101000010400203005e8103410300e043d00d0364400d4691300350301e400208078075030131000385200d51401c4c40340100000b11542c8502c0307407405006e1034000c081402220b4060350390141c0300e200a004829900c00264000d1080e0305440c00303458140d00039507407603420143c0186415184c00c01098941c3c41c18010440c1c0d94000e05c1502d181d40d0b41a11507000c10b0f0726140c03c22800005d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 236189829 1250 236188579 236188621
    0x5070f0611030f0609060a050d0f051203010803120a05010b0d0506012a020a06080403080c0c1f0c02010501060302090a0b0c1204060207080c0102150c0a030f0c0c0b0903030c03 77
    0x24880c5a00309099010390091881003002d928000110700e1301d801041141e40001c1d000c1400303000c03c10400d111548070300180c8000c458126146540c03806c4545003003172900850706811446600080f0010036548004001000b08020f405003284050b03c0703d6402c0f1701115800c0c420540055800c21441d440c50406401c21544400b050400303140c02e1035400c240c0b456681b58441070801461030710052104618000305040050301c0c0e0344c83c10311045d03c0c00b079034040d0200c0c50103045441c120801040c401d15802c070801100904e40c820341040d41400e140c1c012950054030118043c0005035090400103e05076100380b007034400901004140c40801d42c074142c40d0100692007501418518042d08442c0341000c00154000c000071b100c0e1b60f00804001c0c2c9015030860900c0c0800c20110f045402011810510008902c6c8054102c21500c400300e907a2041e24005500810001041c0001207062400701d640d029040303003c900b285030080070069815911034021f00c0e01d91100b210380341e1b4401020720209020302d0091448640f416 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 236191079 1250 236189829 236189831
    0x3100b0a1b03020a0204020d06090509010c05030c0705120d0507020c030604240209180103050f06040c06030c0e040c0203031006050906160312050a0b010e010201020a0e28080d030b0604030305070f06 87
    0x344d450740203d000c2c4e074030008603414032540b01c14007040f501c070300c51041550020020000304012100007a0013403032440060226580c0d440046503003401e01a080c041c21600c81000714216a481075a80b2030030300586011100100540100700d100980e604000c140d00f0300c680c1d482440d0300e4024401545c483d100e0142c145403402c0003542031103164500c0e182d46589803d480c117202950700c40c542c55440c003940351403010300c000c09690700075909002c00602003800381c0c003d90f005800c01242c001542042150100c0410495690181c207240b04070b910a90003000560143c0e1907044143c1e00a9107403603064689228400150b50003c8041250518011011820800403031080c40c102400c0d58140c048082500d1303080e100390303205540c1c1c0c0c000c644056802c0340c0d4420f450320b0b0a00003036040c00804034025040041d501041405500a0b022450031481544c861010410211a1803c80c9586820306640c0d596140340d1500301292038030034100c060b8075110041d134003103a41c07645d01d13540b8204250b40d90880000401304100d440ca = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 236192329 1250 236191079 236191093
    0xd050f0d05010807030b060312030a02030a0b060a0807081e0c160c0608010602010f0506030a0b060319031809020f1819081f050709031b0f080303100b0a1b0302 70
    0x1004900801e4028142c0d10001c005190440c10240c5e0300c408050142031080d0b005404001c032400212040c2c0303a120301d81e03910040c0c803a524034030240007800040300300c3c0c1c0d07204138002842007009822078519030150f0328540e030741107082d60b803265810004081d01000c00742c2580e07240c0025050b60360b4000200201c0a0300100307840340b4003c075901c403501601079400c208007058200006103ca02e60901c02c2ca05000c4030160700b40400c0c2000d4000c651035110110016044c401d1900014030640c404000305480000c2c0a0b000700e8007400c81c2e050080c41c10030103a86d00b001e00d1880c2080091708010030f00039611790000303034200a0700d0011420f11b200041e01c2401c004d141c200c0c1040c03801801c1d40e50b900c04c102c80100030400240651a100111480c00402c0311614444014505418420001d84c400000c5c416254462544860300c5c00b14030504204200580c0294803005a018012490100c040044c6d80100c00365400701e0180c1d602c6020b441041d0146000010014480c0e480201c034450140c040c210300345000f40151a19 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 236193579 1250 236192329 236192347
    0x50f07140609100f0504030c0201080403030b09100509061801060809160b0c060709081c140a0905010815030c0112140a0e0c0109030f0305030402030f24011401020d050f 74
    0x8241c8102c912901c02d402ca01030a0000c054036018020030300151550810541c80c4c0f40e50094501120090040d04014403040010b0030940240d001c07433a058801040241d007460000100c982011203405001c0c00f50050f40c0c007280b802d05051a2503005a000d50300b58000b145e091141c1140da2503c0209204090312510401610745501c1d41c03903040c041e007280d80c1040e43c0c4d46035100312141b070008040e0a810811050440030044032002103008a282802402e101203c0e5003107840c11504030302c122140006446002502d0420941c1142c0d07607400302c032003c0e00c48004982e0780521400003c00a205072680542106145546962141d13140c41c65201e24141c0014079103690165452115400700c0b00040520765030340840411420800c000314402c0001d280c0040824210369841c030310010200402424014040089411503a0030300946015240540441c2e4609040c0c01c6805050781071b1400180300710007c0030000c207c4903608102001a407030182c0040c002a4002c2a0841e21a44100e43c1490590802c2c426100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 236194829 1250 236193579 236193583
    0xa0501140d0e10020a0201020304060614130b120304080309010f14090603040609050a05010506011101060614071e1203180206031303120908120a06180f181a090706050f0714 76
    0x2992017180c1c00161285001d240c00300031500990002038050240c0da00311692a501d000c0d244004022400c0e002c11940441c6000c038149004808030011a40004107002c00c10420000c00b03810200380903685c2d0003481d4001c02050703c83d45d9050320200f50466040004407141c3c2071540082d50464417440c000242c00c1141d032074203410914000801c9502d651101c09101856034007032007601105000304005c00c40546001009411110340c0080048800c00102e01c40013808030300751410003880790100400504541754a403200751280c1124017000400d04c5d14400c03001d070003151b100b0522083d9010742603610b1500c036480c1007200f440e180078084041002008102c0c407904c02134002c0140c800c0c89030840c5520743c0c4000d0a0300d110400300806c5c080c03501c0e26007031080011030f50119000b0344402c040b03800054161800c9103140701400e5041711405140801d0445203040084401a00a40071540d501000841c2c550f080501c1c0c0b111918891000018800e2154a2001e00400300911945101d801000841204d00071058 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 236196079 1250 236194829 236194837
    0x70509040501090c08010506090307030204050408070203010213080106080d14070c030501020a02030a1209030f0c08070506070504080c010305100515070f030e01080709030203060f1e0a02090a0501140d0e1002 91
    0x400701e613204c0c0c40c0e15080940000807540504421610b203030820701c40c0004a0740c1c0d54800c0c440a84140c0c1c482d401300b000d21a01c0b004071078246801500a40d901c140280c03001e11007582c90b119840e00c562901ca40010204030102c0e00521924460b42d034a881e00c0806038440481c3d80080406440d200c003001000000610240f00900715401507402454403099054406021480c601f00400b460300d0411100000180d4810540d12002e5900d040c070840241280c10074a1041c050121700070214801c0106115110760004040d000f16103040b0700326080301d102800110203480d0140c0c0c0e0789600705100b040501080c603000220003018910708410a0910a450300d41e0800038400d41c60036801b1440e4401c8020072540d10100d0542d000050f400d051090a01e15030120780d541c50003c00000480f203042001c0b80380c144014280141d0700c4c0f60401600c0281c00c0446214000f5841034100e80d21409100c02c0000d03555008a0701c4048060400089c14200542084040080c2c040c010000150740902c0030f0400e403041291000e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 236197329 1250 236196079 236196089
    0x201020913060906170c0d1704060c23071503090b0f0f09060108210403060903020709051b160c080714150304050309040e0f0d1d010302160803070509040501 69
    0x85403981c5440303d0340c02194a282c11120140c4005082d000c64144001003500b41018241c40c0381c92074906c1c0b401c0c146282c3c401c0003410070322680700040024402e50b02410710f0600d1030003004c0c07102500e40048603c0002d241c0d030003071011258015000c1000a040b080c45a10103241d114100481c540c0c08983d11905100400c40d2040c0710381090009001d80d00944082c226404001900100540d50500a03106d0303a886103954510000e066070115030380d0010401d01038800550f880380d018403403040e19240103912403009002e014502c5180c000007403480189002003200c007840548450f0319103014001c0c0714850780780d100b406a0b03d944014100040b041c2e03080126400801d503105001250200717038010040c2c1da5800d074065102c4e061040c81404040342c40401216510301003228005042d00c0c0121196013841c2224800381018012882800b51440d04a01c1d0324282489056205042d2002000103504034000c01c1451621480b01011030701c000780c00c540046800c0744003810010b04020f504000501074546c240c0107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 236198579 1250 236197329 236197331
    0xf01050f0406022a01050429030a020d050c27031e1606050711010c0f020a080102070201030e06042109050a03030504170c061c060305030c0c150a0518010201020913 72
    0x2e0f08643e030303009018181a582c440c0301c032100c130003001e00081080c0241d0203044103d604c80300001c0c1d0149800000703c1c00400d041d1031803584901c1c000e070030711340250000862903003018241030003d84c690303001d0400c94500301100c0001d000c4125001c1130504003001d1103a402605445016405c003514501307110440031071200c400c000e010031140306035070144011440d030006007881400d0010070001001441794a9a420082c030386800411003d04185000343c03410080603401021511001c241282c042d001801460f000303880230b00c01521011400b5031fa07008101da0152001c110701d810441c0300205460001420510f52400214858031280011107100090740b0480115000050812003001c03464460100c01401d900a00754400340000070991520030068205184128080241071502d02640000040c40e048400c49850f504071410050352000f442c2d2559105d904050540d10341c4030000b00c21166410b800b0307681c0c07a052440e40024400c1f00408000d0550555400f440056190385855007101400341c90740c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 236199829 1250 236198579 236198593
    0x6190e0625030c020c010e040b04091101090f030f29090d0809030a2f030403060e19050d0305070e0904150506030a03050f090d02130204050102060a02180f01050f040602 74
    0x1581c80465248064807001d140c1000075442c0000c0c1c0115000c81800428241140c0881c2064000360003015641d440300d9020f40f50450003000c3c0103226002e40200303a4280c0312408803641756501a41710b0039844c0b00c0100030340c681c0010400001c0101c400c40059507400f0410140c031400c441c2c03400507025000c4482c1c0b644e550011101c040b8007540100c096030805241c001039442c00c4003a860003000f150142d59220042110311007020b100d2251030b000003940e20700c0c0c02c060f40e886a40b2460150041c3c901030501000310301c64111801010946000d141088a40c0700c2c000304401c00e0b00a03016009400300400c2101440030b211008004c548800341d038280310380d100d11440ca4154403500080700449001800c018041c1e80810351900000360004200c40142c1e86040c450f54071225400c00050307086070f20300e01c0250040d120a0404080c2001c903000303001a11000d800f81c59880d525564000300b01d018803414042c04540480582d070160800a45c02c00b040d20044c0341807844d100e006403c100d0340380e0203030b8000d01c01a80026 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 236201079 1250 236199829 236199871
    0x506160915020d020d03020403020d1403040f0807090e0706080a0f020424020f0f0712051e030418091104051005041e0509210a020a0507030f111206190e06 68
    0x44000724060b40c05d41005c40c20b2900f1a004600c09160146c001400090740200103012203004205983c003c000751141d9180040d04c44080030345075200d41c850307003c1741410030108000008ac0800c4030802d440f600d95078400b0640d920580180a85200d03031a01e4000c690802012801440c0922007039130055041c2221200c125500100900c3d10702864001c0ca590381002407000a032a8010420500705d43cac61a040604010702c1c1e0070309074180a9482130354809456a40c8040e81502000f00243c07007201c50b443c40d80510b20480d0b15400f002c0c3e03580204002c0102c2e8050300100d80c10310380399011315048100755048000305134449001c80d04031201c1e81150340818840e000d244485420034003030303213500610203000351150600603440d00800040c41141c1d480e1010000c10a070310000d100700110031125400000f00d0b9803465981c00c003404200314900c401e640c800680814050a03080c00d115242e1141c020600500555481700c0041240094010b0070206141d160340c0314105001d0b0401106000c1d80c0224042d02c2640418 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 236202329 1250 236201079 236201083
    0xf2a0602090913110f01030221090f0d08010b0703030905060f100f0b0708070f08040b041703310e0a0b0f0d030504030f030e032b0203070506160915020d02 68
    0x1070001aa4082542103c00000c090400120003100140d0300f0f198411014001600070f4000d00c030b2601c088640d100c0f2280303250002a118580101c03a400152110030011034034013a228100c00003002c0210f5030b80700042004046043c0180112806890000340804641c0d0704d4904101082c0c810300ba10060110070f2080d620481c80880b80189002c48088291034139154401c00e481c09a4480030b0310f600b038040f42c860244803500f0342c20700000c0d9101c0200ba5440c0e8580d01c8000c2c444e08940500c03120b515032880d002070503080010448110003003030040484550544100c2501c400c0c400d646014080c545030000040103440e000005000d0300000c0c4000c43c00f054900148407a00303801c60700152107800300154403400701e90030204440541340c200c941a00051800d0400b070740c4600384054050780500c105081d80c1c04c43c00190310a003000380040d984450001c07001d4041203940e0301840801405d59044940403440c00303420340840306000581801d01419080e03032040b00c9164081445e0503440940c1110010481442d81 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 236203579 1250 236202329 236202331
    0x100b121009090308060d02180403050d0501060327031b050c030d0e0915010e090703050a0b0a06050a050c0a1a010306050f1005010e030f1b01080f070f2a06020909 71
    0x200090400298005031001400c074003015064030700410301c165404e411f540b2444000055003c89081c0006513007854540200076a024a126070b8560303103410008140d5030300c40d0050814618161581c405100c0c00c6c003400c0d0002c2d00c4c407503c1c11414044000800f02081c40c00d05041d00c81d49005401806180700c0c09818075040050842a180800c145034330440350980d41e607101c13141c0011000c280c43c030100b0051801170340c40000e0300704101d500408140c01c010700b15501da00054441e4030412010701654584205200c0b0400c60382c010030011440134800c0403441442800074286240f210b200f1030ba1280550788904500c0340b000042c140344103484e41c0061082c096140281a0406440240038000f4a003171801e1a0a841c0d050081a04000309a0a2038050780d130304001a00805803007000307030340782d110469444c41c0e001e14070901d0f400e0114510341c0000d100c0c118200041407084a00d5140c012003000d680b58100c0d00180221281e41189002d07003410300501610090041c02c041c440c841c010307912a0f02c07408100302128 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 236204829 1250 236203579 236203589
    0x1512010c08071202070b0408040810050f0c1303080c0312011a040302040b032407030f02030c0a1103040b030403030c09210b0703090b090120030f0f100b1210 69
    0x304218a84030210707401074289a2018051030b143c1030f4508445814806441000c030080d000041c240107120078483c03408002e00c11a040d4504444901d0401d096580a440044600300130146c60f600004500a03080001800010a485118032010740c82c1c0c1d47e046e2103a046a0054045070f400482c00f00901a42101d9603405060320380710b40d401d60108022a02124841e5002c02805262500381040303042d10200b142883c5054803080381c403d4000e81022034803c10200320b03900c10000b828094081d0b07110711a442180d000781d0080c94002d00c2e0489500060b15422180b0054000e40c1c030003044000343c00d402203030246005a10980d0003254584481e40b004000503069000f581070341d02e150707040d080f182d6004000c07010030543c09089d0080e036580b00c0030305800400400b0f00103800703000c1c08010049130304c00c19031101980300094120052100404441c8038000c1c0001c44002d161820340101203500d2000410000f42d219262118508184d522000090042c0c1c02184001d040101c0c201d0900c98110f40b130104142c0948 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 236206079 1250 236204829 236204831
    0x82a030a03050612030301120804051e09060607020f1c080d06082803030509010e030703050d110430020d05011b020102130b0c0c0d030203030f060303092b0506151201 73
    0x1052065200d417680300600c50540320030f01044031141007082200a0710002c000040c641c45944206001c510903208000c103003244180c0c20100058580d1500c5015900401e40291203031a00480103418802007489000e404460324122411140016407100700411110030129000310300c46103000c0d0801d2425001e6464609440c024001208184581c0c84034920680d1701441e020496488900400c0e00605802d01d0381e80040c0000200107090541050040c032103045800720030802d070026168042664003d50152503081d12603a600465001e00c040301c081081c05040309101d00d4070b000ba5000600c0c1c02c403540c030202c0d02c1e40d445000c0012a640d854401d1203041c0001d00080d440c143d0410350158101d142c501070882204004544511008d90030400d10f000c286004d000c0d00150305d590705005c1d6480d08119401201d41c03468400042c014200070055414881000e0019001007810b0610030003400302d4203103418204100440c005003c103408118050182c0b40c1c440080490800703100c18401c5000d0201001e070120707 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 236207329 1250 236206079 236206099
    0x120b010306121104060f0816081c0804030203160b06010e0102120a031e090308060316030c050103110904060308030601030b06120c0f0705100b010f031503082a030a030506 75
    0x201030980101c28603241d0280280d480309043e00f00080003071503ea003181ca50203415000200301d0b080001f4442030146815001c21204941d1035001694599071000020b64010781c030050a407070a03000c1d05005030014407030300540f41400a5103200c51001e50310500d00740c40c00d1a091041c88010351300051160100602880505040000d021110301c0b01d10600c003c030390400d503940c5003241c0c0c2c0d24204c0c005013a6075408042c05100040c283d0500800c003180981d211803080c0a560300381000300c00790199603c2100e0388442071a00c0b103807030240190001e10407154101d03000c240410011040781e6840c07280502852003240c00c03540302e041c01400101124050565280a01420424164028500500164480441c0c840256034640b03100b00c9500c0f83c0905c420003080382c855000c141c0794001c2581c200c041003010030713a00c40392914111101242510b1072400310041402003601e05001080c0820000c0c0100318000140d00034a500c801905440d010440b4003410140e0001b06403000c10aa050185542000c411030710800e070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 236208579 1250 236207329 236207339
    0x1b01020102030f010b09011103070c09060f062a140f0c0a05030a0f030c020a030c0303080c03012303210310080105070f1b1703040c0603060b090402070515010303120b010306 76
    0x101c18014240e04000100f8484200e82c49000c8c00d40050070444240e940742c400724540b0b529400c40394054040b1060038180702041c07920000101c1002c86040d50343e00d828440c11514140a2181800e000c0b04011481e4000301e00170a512124560401c808000200101d603108038a280c10312080d81c070194401c01d05035904206541e00090480910703a00003c1c0c001201c1414581a42d00d074464640c000d4009403500c0c0d0010a001c40c0a80313a0048078000d817640d13201591980e49001c03044c4824050f11094a80d42d1080d56500b905801ca03025102d500502107518807807085a241c4c61511041c0c10200318a0000000c02034182001c03071000c0001c01249000340028142040f0203040e40c001410900d04110711300320782c51400302070810340300d801c0341c1c0201080c66910a903842c02c1c4200e6104482c1038680182e40c00c2c0000380c0030700c80c0c45110708454040250300d06241341c20082001030340c070059054480d4800d114003900c0b5408401d040d1402036102e42c0340d0300c1c0064400018441650b003c506007070b043c145070842c1008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 236209829 1250 236208579 236208601
    0x103090f050a051c05093003040e071803060905070504021804061205060105011b0c0303050702100801141003060b030a0b0a120209010b09030114090c0a0e130b0403201b0102010203 79
    0x20400d002160f80e02c0d0782225a44a80e041d6034404591075011f250250403a203075010000c80200156151440c0030000b641d42e91070159503c20486002c0c10981c1d4100c54100045440f99110019071803203401074403240303580c0744001b0382640c0090805032101e0300d1b00440d40d0342d503150502ca260000c241500380d61a1802544e1a0aa00c9050500c592414418010078810340d03d10212282041310b94400d45100f480380d243c0c00e0042880c0c02410b001c034058412040c0301e56885000c1c05d0b01c581240c5000301c1d50104e5170340039014405614807181c284804e05494210100e512100c0d140a103200d00300340000082c5801e11103040022002465200428012411400201580351a4070403810349082038400b40c5ea070401107010034014165150080d03a41250403062141e03500000c160318000900844003440c00e1034482c035010070150300070741d0400d108403e001c0f0b2040018a480320340e00d501c280281010452460740c04003409a2151583c1640700070f03081181c1031b1003072013440e0354040104902072000b18118a00744008407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 236211079 1250 236209829 236209837
    0xf0f150c0a090f060e0901052d010e060301080a030e0d030f0518060319060801020c030d050618090c03120405090406110d02040905010e0a020910030b0103090f050a051c05 75
    0x108040d4000948a15480c0103042001c0140728204020064070b0b580c0c400240210480d00105110b910800e000003494589860440c0c682000064102206030042080c1303401400c00d05062818040b00c02180d44d0950303101809503000304110006805414503a00d402004081201d07103140c070808142c12a0f0010a5010386411040100e03810314555441c143e8482c00170b00003642c03002d250700002c0002000203409419480c0355560b511040184642901c030039134542070340551004100243d009200c52860038419401464200c0c0028003080c0340654811040c548074442119400d81d07a5101d0f1154207294141000482804081d5508a40c24282881c0010303102850162000e441c6170717100c0f107550740017041903011110001031026085549035560010300c0c000e44000d2041c00002900a0700080ba6040113000700d500c020b000034158002000400c105400500c2c07102003e50405aa885090000454521454030014041e01c02442e00f84d030a80750462a0980031041058082005454811166040b4040d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 236212329 1250 236211079 236211091
    0x601080607200703080d0c030b0111031c020409060609150507020a05130e06011401020106050301111c180b0415060e0601050c101503030f0f0519020a050d020f0f15 72
    0xb080d50708402002143c9001ca250700080d081701030000314059a241907610119008010340c40500c81103d0842c01556060440c850000c00f0ba002041140c40281e1400080c10515503402c10043c00c4c2500c8000801c00c84145070054000b0418200091091f041c4003e5028a402000d2900c246000b06503400328010707070703464801c4a0184d03520f0f40304208004026041000918000d20803942c1d0356a42d4100510380b44808100c10340594a80040401c0d10309040c02100c610341a0880841c1c030301194804141008282480403500c141d54410552451600c90640a003640e40115444401c41c00c0606019110101c6410707050b0099103031a2081240c843c0e404030f150351052090031b0594803030041260141c20410484100c09116142942c0c005500c0102c0c0c1c051801c0d01d0013561000d5003020b040740c007994102079140c0c0e040e0118400b80140c0720714500c0094019070b41c842502c142e489140c0380b9500e0078540030100302c8400242e0003800302c0203c500d10420514400440705c0e0000c1c4200c040f00071070764802c8600903103c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 236213579 1250 236212329 236212367
    0x60a0302120102070219060e092208130602030a12020715051e0903131d150d1514060a03110f01020a08070503180a14120c04110306030601080607 64
    0x4030342001100b9419074110704d0b0090700c5403c006c800e2224260304180306000b04804981202840c10481c00c0c001c020500c00c0b13414000d90140480300741c1580d41c0034110990116801c000420841c20260b0034110400c00400203a00150f458003116100504081242c01c92500100d10601603807003c80d03a980864500c1280c042c9001030a5252001030481a41c40d50b402c2078010601e84083c440d0256002000b000b400700c1c0c0110300200f443d140e0542a94003800684840c2001d1014030220720348000034080a40e08204c01048401040110f0b529000302c407140072141e80842d40d880e0704000300041c00c400c401d5800345048502c14241801c6940e0205000c4560300b6031b81c00358202074059442640200700c0c1c001143d80103c645501e0f840586030081e669440610300144492404510f00306a041881055082c0c440450602c034400d5101810b004070700040781015000c074400c50448403031a40301c5100d074070f100c0310099002d5a0b80e46402410b15150140c1a48600303000c1d40003808210426038070901c10840084042c2c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 236214829 1250 236213579 236213599
    0x3090b0a05061f09030209060a03120e03031902010b12010b0109030821010e0403170f0408030a150b0406020f0304050619022b03180b01060509032404031403060a0302 73
    0x1240f101003006450602d800400344000341c0340c98100c44040c046901c00c6402046a80d202070500007080060b110090010360607070700d4400c1d60b038019600c5c2c40c100000030301103d04014a070161900340003c0c1f5030403140541d5544440300f00394140044d003101107151000083c0580200d803c002824450349100107002240003064002a051249455201d001603521141050b5619000b4070044a981540d0131008a1b01e80030268801e120340030b01031881107a54100300c000c55551a110340702180d000400c0d0b1048281d5a1030140c48811029807410050301c00485135945071420b01c0c50191401c0c0e00790014035100c0e84140070070007981c0d81c0c00d0205c40c03481038800da41c00b0210411100691810304e40040e0900101400650b11444000134080d00350074062507030b024800c0400e0541d01c424200c0d0b080501034128030080e4018040c41c0e02401c0100380022002d030441d0000c1d0a0400300c0000d0000e007104110f01070f3b154505100915500c082d90244058101070480c1c590708080740011a11003423880003d00413403c4607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 236216079 1250 236214829 236214841
    0xd03030605030703030305010611070b2b050103120212030903040b0703120f090c050117060907020a140304090c0f0c11010e130b01030c0f020604020d050a150608060703090b0a05 78
    0x60440c000411000d011101407a031203140182c007500c801d028210014582c0c4808a8a40303800096070002c40c0c8000d81d0261030301c1024200203220400c840c43c462032070501914403039a404950302c20180218003841c106c00724840000402030801c0c40413158002030000520134480c10404c044200c0b0300300d8842452217a5100d41d00d10307050f281140b24041c0140028030b4007400500d0180380e500324410750303482207030750494450300c46e001558803a141100200008600b4000540c0070b04101400c50740240040c01220408101e0355100c1d8403605190050007080d80000c0340400c0b402c55940280c52607000b0505142011840e00003000380321502501c000341c52000c4054520f052070f40a44558509a9409800741804c031200d404804041e09202c0501400030f4900303200742140c50303c02d05001d2440c0c00c0b150301404040e16640c0030480030082e2081d0542d0540118600c28001500360901c1030341c40604080c000c80c41c02e00d02030119080c00c4005020106150070002100006100c52000c0307a0f00903502c3c1c9000030143c030f0b40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 236217329 1250 236216079 236216081
    0x901050d170d050613020703050703110c060406020a02030115120b040309051224071409032b021c0f050a0c080a090e0a060b0712050702040c030b030c090106020303060d0303 76
    0x18858180d50800010303081100d100240c000c00c2c444c1e04180e903001d0402156030a608224442c4d2134024001034400e1001038000782c03080508a200304940c5c811242c42a50390300010b040c66015500103800750b40305001d00821130038207004a802d01e00000c20580030b660710702404480c0781e001c0c0410061210311140700040801d4004d140c448094480500b0b03080b030720408255030030b549040301209030b0402035056035501c100b10a141d11031481190260344118400030184035001c0990000c90700241d050043c0d020341800845054154818803495640c5010040b00008020703081190700010820b07243d0180310402800c0e0b401440c1001201080c1c540380d0b0b5950392018045400c58404600100075410014508140c83c2c2d2007400711050712500c90040c030b4140c560b4136005013142c1d11071040c50802e140c00e01c48000031600c080852900f03010719041540c5050b519500140454a100300400040b035030703a10030003116060400c0300151088007607549010550500402035038900004144d80c1c45000002c051604052003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 236218579 1250 236217329 236217353
    0xe01140d0813060801030302061609091d0105070305041b0b03040210030e0601180e01020910050304030203041d040605060f0109170304030c0902031503030a0e091b0705010b041a0901050d 82
    0x108818110364a83d02c0051840f00c080c401a030041c4520030109283c00c008030b030a0395485021f40c44815a0038a000004c20181200b140c48403402c490400081010074400c2c01030034400c0942d9500003503d4501860289108807403007421800000d80f4036014001d509079607017140c3c0c0042e01101c0c03a0400009948041b400b511242008001d180250000001c54198580c10444942c070340440c00d01c1400300079000d583c200d00174580702c1a0f224481c2407406002030700600085410074004d205603441d00351a001801e03d01c1003400186941154540104424404144107050b0448001c40e480780484100384002840e0300780d58021041002014001c1c035494001c1081102c00071075010040c080300a0781e0b801c4140c029041182c21048202c601080074078207140200c1100c2c00641e461315a0003145001400340142200010642c0c0c448a0706441400010201a005411050320400020452105101c1400140c038031400100b07081088003e001117603980d032024803505540080c1e030f010703039415424144242803885c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 236219829 1250 236218579 236218597
    0x31f0602150606041511070617010e093301210b060307120506180312010b16080c010b011d1003090f0c120b1003031d0114130f0e01140d08 61
    0x45600200a1019000811001d40d281b040080c2c034045959046c0c1950065103180039584507009800042c41481072403106260020034141c2100e2182a40088660209000020010601074402e0000c003a0f01c80c8040454054020b1036800803511540350340900584840150040084102400083e02c54904024980040109e0006985210880d080c0551070301d4082d2140310080711a5565450100b10010881c0d000d0000b000c030742c0d0010b030718290104a55800080400d0813003051091300d04082804640a05043c290b15000040c1c1045d060001604168010000911a00f0189081d5041c1c6d5111442c0d8089584c0d03605021903030304020300d0200310501022000a0141904810110310100031014101c1c40512411a900b6a9100c81d6080188140740f03100080c0040d5107401038421030700303510110b103005130f0060501d000c070322114007000d55080d00f1a14990092021003401003050000160030200100090b10052501c2e5041003c0c140c8a11405003205000c0d080100700c110403c5500310894110301 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 236221079 1250 236219829 236219849
    0x909110a1805010503030313081b0d120b030c1e01050f07050a150504080313140109151d0c060f040f0806040b061f0e13060b031f060215060604 63
    0x9031206052441d1500304076820004070724210000c100307030500208483c000c00684240b02c4400c4130b507a603002c405900c90342c4409844d5240500c4400b003442d007000503800e550b180e5199000012020803400c012548055001c1c2e00c60782c402015846140c407003661265141a51070144041c48004900595003032003441000c0b07180d941d000a0b40700c00d104001c02e2002d50140324100000500f08070702418000d80da02510043c10198040012070100315421602c150401e110b01d490781c03042c0707007038074803403400c446090106503034545d81c2840e80345904c209481403a41905c00800b200c003901c50744040030790b562030343e00f42c1ea180200400280d9401c03c070301010a5030014540505c1580070b45460716043c0f61103020581d4120b4018800801140c11842c08913418162100c16291354980032907042c504584030800051a6608407c8602514586030164050311025007035240c407143e900d04004e00d400d100b1038807608400c840d600e00e41200b8412030303502180d1600709220114600340a030b1141d170300041c03a0348602d030700030704082c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 236222329 1250 236221079 236221099
    0x3051504020327070603050f310209102c0f06060c0a05030702010813021e040e01090c0314060705030114060412031d0306060a090921050301030611040f090911 70
    0x1c290000380000c10740b08244d42c07c0c030454949011490781000d003542c80c0441800115814418240e02c40d25000c03007440c42d1b0801910420194000c54000750081e03c104031507060300f803000c0c04520b9003604807248480c9800c4c0740c59105c0c0a045913010411902a15507030040c0c4d414030110320b480c0d0321141a120002500000d5a45c40f00e00c03450710aa8982c03145004a0100d000b4000140c00b081c044103114003a160050180d05407100c0d0030400c00c15407042c600e00da590080c3d58820108001d00241308201800e4440e45403035001c0c0e400c5040c845c1900030a41003800c029031001c0204240e80340d0101c2601e04544c0c403a40120301515030ae00c0000c0741030040c5d401034104802d40790324a009059004080f04140d154801c50030303589000768400e240e182c00f8221900364000d01d013640308001c150441d6112000c85400344c1501103c000d080850000d55600d191517035800140c0c04401402800020b03c100c01c01c03000d000119910b042c4c6888401c0a80080340c0c0304601c040b51381e07001e2920a200c2250102c0b082030340700822603242 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 236223579 1250 236222329 236222401
    0x92304061d010f06260604060308030c0418050603190809040c17130506070e0d0203061305190203061303050c0f1006091505060c031b0d0e01030515040203 68
    0x74001e00744a0460100304016000510501035482c1e46a0041030603104d2045c01486440000f41a2010b0059600b042d504c89000001c00d5541000d10301811285521503502c03450302008002144406003e40c217620318080a0001c5640c002491080103504502085002403050034140c0b03082c014042c40c5038009090105003000d141c0d10002c8609440d14120300d894143d100d50402c0380020074043c0c40203106d0f80c80300300801c0000d400b8413041d100c0c00760001d105d0400240c05038042424240306440320103002070015003003000c1200522401090485c0d5014260441c113003074002954506028000c0204440c4551f03510052511410865407451a441c045170483d1100185407503a030700c01c00d05000c264601e0500080f80d00d100c54010540d420040b1034050302d03154104030401500380e00a084600091108000b4003001011003552100010149005091600084c180c05814800700c0705465040602c0c2a040001d8100c40144040c00070406883c01a129030714031500005821100b06001c000d9021a514008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 236224829 1250 236223579 236223629
    0xd03050601030606021903050c0c040f0203060102121e0f070803070905131e0203090a150501090b0406031a04051603080d14010f0b090301020f0a0e040c09230406 71
    0x2005403001c1e601045038580e15002240c941d203000141011040d55110100c001c42c0c4108094503d6140d10b07801e41d48401c10350340c001021034600b014881c02554001c001c01160351f070148400038009070060345081c5002030b840c046202036032000100131221071340031030b200207944504810b03140e40b95805070031582e41c1e080c89000a00440c2842c031030030303200c0c0c0b074600791101e803d904a0142e142c0d00c0f00c1589030444030400014210000e504028081d050600c21001d401d80032400516100400790010ba90000da43e506050740d003070030703075407410441030149040090410014101d401c4403203031061100362518064985203803d5040c04580e4195540f600c5c581e550210500c2075480044c0412040fa0302e08026000341c0e1000510b42407401d200d07410007015110307420885a003860005240307400d00100010b2400300c82070041e031140c0e00184403080000d5003803c1640b01130b05045c031412103102800d050100c14649041061b0072204041000d490804007600284d0441e500c65400010180091150200040b0881e0883c41d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 236226079 1250 236224829 236224831
    0xd050303060307090e100e030c0a12030605010302091302130906060f020c04060303020613050703170a030c02010b060d090f0b071809060e2e03060c0e01020312010e07050c0d0305 78
    0x2d110340140100040c0b644228031070341107007180d1400500003404004117210020a907101413441a800b08006000004c0350038071186501c00d201c0c0424071054500b85000404172840b50b0045030500d0300c1004030143d641d49404036207051100d21030001d82c3e241d8145040d6880c0603016404500c94904150001c220f40350001c00c003900d85030352a4211a09000f000c4108425114184005400b60700020b0110f4030b550303078480c2c445d10068044e80031106629900c0e550a40341c52014004035095200120321800d0403a03050181003910708042c0b00074050360076840b00185e235500c22901649102652961000100040c500300031f1070707a607044951340031985040480a0400c0822041d060b1401e043c860b0046205240c51252009890321311100c0701441d941c0400c03400002c082040e941e290301c1206584400141c1031200e190000d144038030004644034415030b002900024988242d141907410034449091100501003400d81190040c0326401c400b511118000d5541d841034094821860103118250364485402d500a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 236227329 1250 236226079 236226091
    0x20d09060c0e0f0613140619080f070c11091e010902030604110a2a02030604050f061b03040813180917030c071218091d01090314180d050303 62
    0x30711040d034208200c44c03882071496986588080610910600040e1650004041d801401c40c40c0742034044c0a50407c030000b45a088000038a010040003148100c1300c84403600701c1013a04000552800c0381d41e80400b040b0a59460b64061448180054079a450b40d0041c0708400e40c040188071000e585440700c080183d80102c0702540038508000104056840100491f85070302a2580c421035400c00b203c0c00342c0a0111700400c0f034054400c0c955806405681c06109150040c3c0c4601c004000c40f00c10111050f007004c0e0700a0454807199015076031115140380c48001c807584203500100700d50b074800703a400c0089602d00c0c840d00460941008034194081040c1c00d640403420090168070706010741aa10881d14000c0d00c81161a07640c00942486070400044100f10b030302d0007041003828100c0201d6403400304500c2c0c80d805a440103107000d0f00c0d1000d484484246042003400a0390781c1e00244900921514090501c030410230002a40340000609001c8450b00e82c4002c1c1c020203070061450444500d6070904030b680c0d410030b07030f21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 236228579 1250 236227329 236227339
    0x100f03060506090601020312040b040f02220b010216032306270a020a06030b030f010e1614090f0a0605190302100f120b0307030611040602060c030910020d09060c0e 72
    0x104d0410741c000010356010300b10340344040c285d9507120760380d90542c92000380c0101c5030110000c3c4102d006aa8004520b680d000d1918141100704044a400c078058540d40d66100d0b06641088849292102502001d80103030703074001c4180103080300700051001408482504510140c0103107000c2c411402e1041c00240c11040400245034010003c80c9140ea031281c40404000b94880042c960401c40355020346c1180302c070150002c09582d14101440429400c1d1481d03040c50400070b4010780c900d45500c2d0354030030b180c4019013444a85c1400c54154800400c0007200c01070070303015071000c0900003e43d15141c107070815005480054454100d0f898008000f0040d9500b500040348101c10f0b4001d581e03103280c031030b0a01244107191a80d81c88440901100c0200092001980d03007030b01802900c03004000308a103409040e2410000800031990740386898002418000301800b021038001d000c0050105c00900002c0d80c000c180e040030801662000d05008200003000403001c02402d140c10700c07040c01e040c0d5401a0074280310700d1051b17030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 236229829 1250 236228579 236228581
    0x1080604020112110d0f091202030901171501050903210d141006030c03110f0706050903030115030507030605121b01050408030708030603070509130c0603050c030f100f0306050609 79
    0x40d03c441651503010b80181e80c204188045007404840b5001240d2032100706c00c000078038140d5030700da1180d05511103003c0400f507480094182055603102c034070850401480b03a503181d02400c00020754181c10b050081610b0403c80007058211321507400317000340380c00b04244c1d01c008a000d00c01a02410600d8101d0038080324414034140340c0800d841d030045c16061189440002d0862803d0a10505400500c95210058205076503050500d8400d130015004200740b2171010205921045240351420503512b008101c40301940040c00100308007074200c8005e0040380d6460801007040d64902808800418195000d95400743e40000c0900407058085180c0c48002a40000420403c03200001510300e80b180d0701c0b501103550300400c8070320003046140020319084040107007510740f5150760f03000103210980150340c014049a03140f0080c10421484511550040c1161f0a091166103400110070385a40801068040e0841003400016a600c2c1c03840d0304180580301300250005000d4a9042a50090504503099806030315020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 236231079 1250 236229829 236229857
    0x110f0d12120207030c02010c060f0c03050114010c020303070308090a060c03020a020709050c090d05031204150c08220f06020a030b03010e0604230705040603080307030b0f0f06091206010806040201 86
    0x10003101c00f0180c141d2111490342c1c003503a0044074007140403c015101c00f40c1e03604069840c41c1150003803207411305156501044035410300781076001c40e0a820080038184a1810705800068030040b09075000f541d018100b6040c00e40d1424030340307420f001202c0c0c8024402071500c1c2075880481e8140c1d000e0000b11459900301c4500315280c0c9049411104151142c0d25255001d020900e0607240c038030302550f002440350341a40d080c4091306084404a4406503011281580b0388490010283d607203215242c445101858070b501301e0b0400180007420302c80a6807541d113005c12051400c000707120803d11404c0d42580d000b83c013150fa400202d1030041c01040b140c94280d20a5003081401209988001119801290050201030b42d124049070034030100310003281c5155042c0203604001032140d80e5031240b5001140903d9000f0399a02d0400c030010115035084001034400d045130081c840b5641c8a4400e030551107034050325655941e410a800041004041e1420040e1302d200d19000840da0700c030b0104640d4050340c0300380c03140c060b000924 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 236232329 1250 236231079 236231081
    0x3031419051008100b010203090901030308090d020102090f120a121214011505070c2103031d070501050306040b060d0605010206062b29060901060906020307110f0d1212 74
    0x3600c5001d000b81d0005004c407260040a6100c01c0b041d90741401200d00e0070a0400102e45032240990050700414064410080e458005014400ca81e02c0c041c0f000314039200010300021250314100049600803220541e540810030010401d44101da5082200c03280e46448130140101212080100004524100700f5590301020202c0f015505944500350480004910349404135602d4020b10300540b03006040c1d12002a0a510b1050717030740c13010000c82e10b0100041c0c2203820054140d41c246071122401b283e0f511580c0910440200321a0166a000d20f0308558a40380c00000074050301011504650241000806800c1098244e004c10f0807500b007a001d80b00642d4501d02003003038451114030a5500803440c6c81980e515003016600400d0107912410000030b07545484200304509031421034800d16440d0054052203040d180072407110b0b004254500e0040100b50400000030348034082c8500081031045030279603000304d0ba52109910700c0305c2c200143c2140f01000250030901513402a552080000c1900a4100d004500f45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 236233579 1250 236232329 236232361
    0x3063807020d0b0417040801090201090608070e01200d0905040507030203040f152009040e06010503030417030906190e01030504020603070c062a0806060705060c070303141905 77
    0x410040b031040050f1148030507540002d10498401102d29412106400c1c1c030b1001e400070b01240c10000620154610025043c840950001020b002165040003980399000503030070401c407c2841c0880740081610400d103031044000080803d01c0c0034081c4039845142d0321418407000c5880440c0d041c01503886500b000d800302d01c41a070b000340103107103070f030b030720304c0041114a2414121054114000074410010340d050070841640081c0803103821200080880440c94035014030a200c5107203402407d41545804002541c81c811442070220310702504010209a14051095403000c0e40080d2800384d079074540100000c080710380e5154410225001c150700045a51003482818407980d4050401495912031510a5480d59942101260741607250030080034001c400180840441e0000e20070740141001040015118401c0180854083d640c10f206200100b0400079404e5001006002c809540d99001d090803006480c08411003425140341c142070004514010309103018011034120108042e888000180030302c481 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 236234829 1250 236233579 236233583
    0x10c111005070f0f0215010f050906030c060d2301030c030b0c0a020706141e09031506090402010e01050c070308270a0e0c09031005180601030b0103110103063807 71
    0x143e40221003028501528002d400d81c4000d00451b014403000c03014100074408260080e080c8080040410000c0d414016159500071104038081c04221a0180101c1c80c00c7c01480422071400e138641c00141c001c043d11080442c5541c50725201c030401c070340e182d0811101c00d02c05880210381c441411800584085526000d6883c4400c0e0341e4050314196151810407100c000c88a000e0001c03503c0100807104400780d407011116560340d12034001c26203401c0e100381007600701200801540d0500c01c9200c108180f907a944200d41703600607824200140007001050049500b4000d6460b400078a1003106404810311100502030801d8408103600d81c084046020402002000030814094000d601144203006120081d0030701d59004102c0c090007424034181000003031401644004c0104d407075541d00306014031241c5400c01000b84444440080c449545551303911560f40d00c0522001d8151004101c24880d6603100c3e4000303000502c0b11040a10740d21014009100035000d06c0c8020540c145230007174207802c08612400030390304565 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 236236079 1250 236234829 236234837
    0x90109121107060804140d0c0b06030309010c080d0207050607030b03010b1f030b010210020a0305060306130f112d0a060809070b030a020702040615080606090d03050a0908010c11100507 81
    0x54500f000960b0300040c0584211400b0383d024804041c3e00c074080105108030003099440d05403016003800e10250301c2d076010381b400b07000303800403c84280266005050307179181d10b511501c070a5992201c8041e00d4001d01420000070700e103006404c00c0c840d425a06800442040c0e20450003002845868030402c4101e00c4500943c0c4d0b0202064050010414040d07400759a202806006690402c100603169000320b91064840002180da11410302c111030804001e05503111001c0902c4030011310158560390481d282d0740f0300091051090101e0340d4860386900302411827a01040d16000581d0801544034143c4021120803a80070300c082c0c400001d0f0980c42071a0207401242c0e5a40a024050305000440302103600040c00c2907801c1c2d80070070411006131034511801000b050850307204131b000700d120703c00205007550180142c4e110304001d00c41c400c550364502c051406003030760600709690713525a51882a20030202c03170380c001c00b2654a00103210f003010781c019014600c4104248192101030b6000ba03800d10403100706031822000a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 236237329 1250 236236079 236236093
    0x7180f0b1e0102010e030c0a030905040605060436050703180c091104080318010908010603020f04180b010b04050f03030c0a120507120c14061501080c040b030901091211 74
    0x107001d00a8440e06045010b02c00480c600214103c41d918540c4005090310b007d910249041b0b0a060740040c400000d4681214180552490000018074901642c00b602402e80300c0300300070302c00700c00d000e00340301262000e1180b00003154098680402c0c0140300440b20b0002003800c1c0110040581070401c0b00c1d5040d01e0340505004685801c180340400107056112030804040007c22020036060703000c0014121401e0b81140c9002220546c07000100840310385d0380202c130241e04162041c8010b90b5990441110400300b40c1d40000e0401c8030810f040229141c942002e403807400000c0020030466010030062042c0c92040d2004801c0c0f0f0a148107040e0f40c2c0c4501011400c55400421243c000254a01d0f4890480f00e15031414500b007410603207a0035006481c0c40c0102000c81c100905c0942005a07040c80c0341110464034000c0d01062505903110305070018890b0865041042c050b0000e004540e0602c2542d000d44038040d00c150712031411079409030091980104c2503e62981d60004030600c10f2103070401e510010081c401420507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 236238579 1250 236237329 236237359
    0xc0b16080a0f020405030a050102032505031b04051f0305150315090a0206160c15050a2a050a0b010f0f0b0906160b040c090203010f0b07110307180f0b 66
    0x1c10002c407260300030a80030403002075165420845583d0490040703000503079030300705030740f503501d082c00d108098000380c9907454900140039400809499004800103250741d402541b16655003c2e9100e660080c5900007807900700b8161a2061140c41c903580000342d2070401860b00c1d444041103000d0b0460a001d545a4881d1707450755148030b40c1d031035101d8110000a088507280c40072580003c41a07001401e2207800d03018440403030001c0c801d540a60400404040c003144181c2d05210b1801001c0d071041c11880000d01001080c8508000361080e00351600d6621203041007241130031490700e207848100525040d203000320200008070340c41c10b0b44501c04089540c041a07043c8454034080644515801c5108030781e030700031404c0c801c10301c410b0256080030580034465a180c80c07032071601d0f02d007009011900360899030b64188140010302540b401c8a540400307458045644644500e4945803030040d14042407446505030003800304c00221030103c201d0158405086480c180300c000180c0c603120084407800700d911580201e082580d125 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 236239829 1250 236238579 236238581
    0x703090803090a05010c020409230d030b0609010810080d020102040e0c0406020d080417120117010c08060d0501090c090507021209012c0a060e01090501020705030a060507020f06070c0b16080a 84
    0x4010b07c09880840d20703030f082d034442036409040c0b0301c0c0c9804000c540035001601c003a000d1040a8100c100c9040402402c01d028010681c2e60141e20003c6052206180105140c1240050083c000300074040c12518020190300009010303401038405c0e01c0f043c0303060001141c46a405a0160780039900c45230b004000100c4100c000329486540500300391880900040b41d0341010182c00001c14513010b50120800302549882e404840304009103d90809c2030349060b01380c4040551058001d5000307401140c20310003000903803c3c20340c0181101d403002441401c040c1c42c0011140c80b1500704511440c019026038105400d0110010b00e5842212060350008403110f007240ba81c1c200c03110882e00c159080d84c0b54660003503000404280010302c51b0b005400440d4605040f40000d69200c28803002610b0284041c140e440d2400c0042542c0e04030036031004080b56103403000584450700c200071200410b42c8080c00c0b1106410704a0000e840c95002c2c65055912800500004042d0354448046542c0424940d0301c540706543c1e5250040c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 236241079 1250 236239829 236239847
    0xe0a082101031a1f06051306030b0f300a03020606031b0415030b04061509020403030203120c09030a0f0b0123041d0109060605040c021f0e010b060a03020703090803090a0501 76
    0x19080304040340442c03000131141000003034089a101d41e65181d081c003d00c43ca0324071050741301d20b00701418280811940e80f1241405110703250281c0f03010146c00c8150b0070002d05010410f0440051550704482c640400c1ca0010724a01c049001e9000d541c1c1d1a12484281900d038441d0700605042e1030000d0f004541507040a81c81001040034003c02200c02e2901d0b66142d180b1800306a50a6460380e403980c400b02804000c4000c400000c1210324411840c0c1495075402035113074016140c0300c0440350320901c0010040c3e4200002c45a001ca8001c041d1058501c1503d002c1c003030800034000640741d102e110070001c00c1e41d14400c01d0100d051002c910905190004807020400544401e83c0d0f6240180444503c8404100090007181e00092050314081000c60030502808101ea1002c880790045502c502c1c0318894221f0040251410050300c804081540d0350040c400341d0241c00c200c0111034000100080f08104640e00d54091300318140f00e0369030510200e560704130032a034034004c4000c0180d004900310010011980581071503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 236242329 1250 236241079 236241091
    0x9050c0f0d0c1401050f030702010506011101060f2306040b12060103060e150a03050d0c031209030801050114070f0609020f0103090c1701061e03021f08150102010e0a082101031a 78
    0x190f00e062070300746e007280b4540c00c107482c860007517911402400129030300201c82c2550805400000c1003101c3c58000080101841740c0b14045003900e081a0800403060303034840c01061403034003030f0030303255541c0c0d441c0501c501e00d60150094075844501d21003c50709641c441e00922003102c0c0035501e6000346032203540101c130307950340300c1c14010b035101c11303c5040080016400e00590b880b0708441e4840c400c800c58503080181110102d606500c2d8040c2c0340c0214000000e40251205054030820701c2d101c070840003c40c47c001c1103842000c03030103040496038040700010828036030065001c6034826509040d606e0302c03000054054404101c0001c3c22688508030602409100d00c40506621602e400041341d0580da034010450020781c00400d44c240321850072024415428041040201c0010620b020032004012a60040c00710034041c1c150075112824a05003036450f8403d4005003101203100c0290b415103540703442c004806510040c0701c0002741c4114002c158018002ca03480c1f504032500301c010b1340301500d0034880e2201c0c030303501c02482e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 236243579 1250 236242329 236242337
    0x5090403032309010509190b010905060a0918030e0d0203280c030c0503120a0f0e010923030c03031e1e0304082106010f0c03020c0409050c0f0d0c1401 66
    0xd80d03104441016120b4003c14801d0000205424101d6403070f0304241844956800700300a0307840010000340b2150b0247d0449151075000609900c0380030000e84104c1265022540260400c1c100c490004000113980070024440d88031540202c070310001380f10706982c3c2a40042d51507040385202407040d0014201c005802d0a00780b9001c000c260884c1d44500c0002103a800c15206a0b0011400384042d00b8100010706210700390f4180941811605000100341e10400c80c3c20340f040040c11a464442c9901609c00d9402500c5000d1091880c06a009158018070f030b00048840e11910802c1000c0140d400c3c08400c45808414800544101c0001000003508661137018241071141e0001924291134218034040c500451085c402103640309901d01c0310461000202140d038180c1c1840c84148280c50380c215100780034482d50b03401c1540044000741026402c25802c1214250407a0804645008100d40807502004514046030116001c121441c2404200e0018550081c0b105000300014061240b10422120282c201490 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 236244829 1250 236243579 236243621
    0xc04060e0f062b3e01090f060f0216060507080702030a020306180106060206060a1509150c1403040b0f03090106050613150206040b071421060a0f0509040303 69
    0x104185908421560000c0d80302d4640c441820409103403401e0400500780c0e16180703030070030941040341201103034071210b154010302003003030084240d0060f0044801800b500c0001a0301f2642e600015000380b503030600c000c0040c000e20078108002c070350024451043c0d0b0882e580d1207061080540e107030031040e4071140042e42d042c440c011111700107a03800c206140c840c0e4800301058500303404d00e11029003541c038541c00074001c0d0340140d41000040d46a000600c400c490300030701c207130030003044621040c0d8594070701e0b0304030b1124151600d034100300d016040702480785c0341307885841d00c80c400f00210310725181c0381e01076070040c0d881001c420032010f190300c20a0005103030404460000010143d0b501e800181d442e03849484182d0740c0f1142c0c1181040b40021074214100015414005015640790541d01d07440d41da24010102e00c103110102545004100f00c80f415184440c55142105040c0c542d80b4003088220002250001d10580205070302103541000c0700030800c01c940002e000c1201d0f5454580e400c0c2c001e0980040440b2582c88060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 236246079 1250 236244829 236244859
    0x150501080c21010906020702150a12020d09020414071706060d0c120906140105010813061802092a041d1b030a060f0902070302070302040c051b0f0c04060e0f06 70
    0x8419080f104c0e20542006a42d62000d10602c000041a014000c4045109100c108200c1d41c014600d280188071040005940790044100d00004206006001e50050301c0d2082c080c0c4400040348600b401000300d5100c20070120a1150441302003038046900640000c802d00441c4080d01103604903a200e05002d080c078a0051803000d503d641299450803081e101d5a8403016542d20a002c1e01000070b014101c00e01e44941d1520300b840d6074201c9280d0120300240780325a030341020306034800c000c1915060343d54018201002c0c0d051840b01d8030514100c0c90003d04489003100d1031541a40f8050f0100c40403540b0707001961500d030039000555030500c0030080000074450084840c01000a0300840118030a921000001800a06101d003d841c000c0d0b036030300031059080c81044182c020035000202c0f1030450354115070214401d02803c10031545d50041038080240c2840c48028450140c0010980101c4083e08908503074001801070108000d03140715100f4205881e0401021a010a4896003015480701003d44286103800d030803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 236247329 1250 236246079 236246081
    0xb060a03080f030a0b0405040201020303190609021b010516090608220f171e0c0304030501020c0709140c18041119080c030c0306010f030e0316150501080c2101 70
    0x2000b500c0426000020030000f84d00c034144507140305030078155800c1029180c20790020f9680c0c0b00140942c0501c00e40c006800c0e1104003542c2100014242130081592103401000d200c1c14503c8441071080415400c00d00002d039005580119040803070040d50790380f400304d4a80b18007540d01903c06045081c424100c0501410214000c00300c1c0502d80e4466101c80070032000324100009411001000041c60001c200803040b003100a06e11009025841c0c0d8000035500c41560146500e1803240354030040081d4004150303400400008104082190194071045c001d5080810000360740d100100c2e10341905010900c0f0700d030001440a04a2003030008054400507a45100388003410540d00700c410054a0b494204200d803a03c1603000c2c2175140c1120600c00d1050030750a184420001901000b00300504214228264404c410700ca41c206041003003189003503d07500c0b800710420410301e03030140006448012014000086804451081ca41203818040c080c02da10701c40f42d0100700000e850b0f17641c000e070000b2030341e114000c4c00381d82 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 236248579 1250 236247329 236247337
    0x1203070503071b030c0b07030c02070501110c0406030c210201050a120e060f01061106041e020d080304060c0f1809051803030c0a0906020d020c0d0c0e0f060f0f0d0b060a0308 76
    0x70b403540760840e07445d0b00d00380c00d0b4200000d180f08101403c0000c902013803600003a1040c01c1e58001d08000300300841054125103400140c6c0188d5034000e0411100000f030014036542c1c01c05a520020301c903444200c0340b00d20600d542100c0311009001520400c60810424802c1c01ca074002c00d54102c80103c0c400c3c2507881441d181400079943c02c1c001003840c800400c00c043d0002c5009550100c110068209440d10380c03108864061420f2000c070003c3c1c4422400700c11980e80c03540000000d644001299101d080c1400d01d800202007030001c1c031021503040c410f41840c20340548402210399403600b0101540700d00700b6180b4406040080d10f0820030155030050769495020070f201461081010203209601c3d5111100000d01d00c1b019a0f1040381590048034074804c1c0c1c0342d030100e007502e0461401c1c2c80c0c103420411146414042c41540d50b00440740188900d06103c4610041c10711030f40102c8086840078070000c9039200300070121103100e3744642d00030b0140d4080c07400580c615080b10341c44a40107140801e642d40d20744a4580b191300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 236249829 1250 236248579 236248583
    0x2060d05181006140d080405060307090305061014040b0402090d0501020d0513080a0819060b090f010504080c0405041e0c08210f0702030124030201080105031203070503071b 76
    0xc2418032020340c000d000c02c5801503466502500b8040145000100310b4041d4195402a0103400ba002d80102400742031070840d401080f002c1d241e0390350381c6007410004118040314002198140104c00c04a00c01c0307600c0040c43da041d0350000c141c0d4004100309900308801440100c14664105800384070700802652420191020300d0f014400250780c0b82c0c0000031000440d0340c0106898280490081c0903800b01e60880155030451b000c40c100302803103403680800030a8080310154807100b01420480049215048100500402d00d0181c1e2007481d80b801920054800d40101e00030b001d50b548c00314458402e14a0160800d0350414015202007070b02847c0c0308080c49107041da10b2030075034004000780010091402c00f040301e0a01c1011492012061440002195607281704070940d01d0040c1c0008600341c010340da820b521030030190514114441f90058040c5c4001d04500240c4416408036441c0c4000292500340454594000c1c8480da05492071503031101d0b4242c0d803d800c09000c130020040f0368140303500c440c000151000b030114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 236251079 1250 236249829 236249851
    0x40b0301053f0c060a0f08041b030807150c120b0a0308040b0a0927110c01050901060f050301150614070602030a060513020909012603190f1404060c02060d05 69
    0xd50032100b25458403020002460080c2810005416010ba00c04461544030304540340c5031103640c459040c501e040c030b81e074135101e54805081c50000008000942d8002c3c000a4481d60780400d4001100b00c2c60011660303482d040001041080320701400305011a03000c10722041c0300800d00e00c403494407a00e42c800160825009148441c200140b03500d00160071201e014020038840c04000e0207901c003003c400090000c003000c1d440c0d4964132502050352094150080d141e10a0814008111500e010600540a03243c1072048014098a0050100d0181018041c046da00209017000e1034001d0b1810070102c45d68540b4030484c041000c824011100011010b00043d4041d062620001c100d1a04100800c127a01c0034503401111340b14810808402140c85a1540f40d044448149010703060841c221030707820700060942e0605440d4000000c01403918070404c1d960342041d48050366500380d0141140800d6501c0c040300f802855a0310b4081c80100007a41c41502500e80d542e2014080906180c1412041015514140c03000c0d5111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 236252329 1250 236251079 236251189
    0xe190f02040918030509150f070f0b10031a06010302070f030507051e060403032721021212040512030f0a0b09011802031008160f0803040b030105 64
    0x10780baa004014098a0344441c400b821140c654014000d403060b200074a00400c2e00c12101c40380c010480d0265101c200140d50750781c1e9150b180340703008041300c20080d40451b5081602c0001c00c25640c0d61442d00d0003a241d01c0300c0d81c001c440d0802d00500c0c550300c01c014402c1e0f0415800300310b00c100180011b518082400d10941b901501c0c0c0303056261141c14804901500305021510301c800d81d0f820400060305582241d05402c00013041c14040424400703210010840d6640d00e4204400e0308108035140c1d0354150421030034440070010b241d0340002280c65118428901058407024403210401c0d5101004c840d4100303118204a40c03404c0d1030307104030742c0301600200c810a01070840c2d00f081140b41c0303a45000306083d0805c01c98040b2010740c140112040420000034009029a5011000955080d10000c10101410b07220701101c2202d00403d40ba014860000c2c042c500070744003640706c00030714008000217803030569074800ca0803820f40e070900302071104c800001807024540303142e03061288171015215500140340d0501d0300045555 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 236253579 1250 236252329 236252339
    0x5030f060405062203050c10060f0e16020304030210180605040e09070e01230d060606140315152a010b0a0b03070e061e0306100c03090e190f0204 64
    0x107200b0018080342540804513540315000b94480394603841c1992604000c4d8440d8260070032507241200d084048843c0781d00e801000304c2e110a801d02003004442c0e00842c40141d81c6c1c0e940c80040c905054001002c40942d01c00d010910051030108403505911405107058041c0006055404c44451030701e600031000b10300300080c14408804c2003c02c1c107034450000401056130500c0c100702004100c10500c2510300c02003460f41a14120280c0142c02041c21384028040c0400c54110b0814200603c00c504c5081d011403031840340360410201c10001c0d00e00c20340ba54445c403080c1c80010414040021040c6e90510030042c405c01418143c0e0210700029403070005c04031400418804030400c00d80c01c5600c60107945104600c8038500700840e00248044940c000388c81d04d003c0b00d07031400c10030100d0701c64011340402c0030614541403c511500c0c9580c002651182c0c01c00c403405151004041d1041e28940c0b400d00e030142c001011140188a1400c0c440b80898000c03410309a814903541c1024445421101e03e00b580c201c50940002c1d00b004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 236254829 1250 236253579 236253583
    0x30c0b160f0c15050901020d0f02071e05190b070602070206090904110a0927030309021f26150a120803060a06021614011206060c020a0905070516050705030f060405 72
    0xa034040300d04050b0725000ea0200040c0d51510101c230340e5000c101144000d40740e0b5070305c24000d880003024201c042680003503d403c205d080000440c09020b008001d04401d508940c0c2d8544001c0003114040340c0194a4140103848201c040c0d4002201a40c00c08020890844035480b180744880c815802006441702c10403903802001241800d0f030740401c2003241020f0008051540e21039411440030720140c24080075190702d2805402521f40c0a0000e507011001c05000002c1e6890f0720064941c0b442070350740d005030040c4c1d24000d00c49046a504005112078180d1000100050481c01444c2c2401e08014440c2c9003a96032040c0c110510845000100c94480000c010301440d0706005070b543d0f01810141c0090b282c1c0c101e00300c031600d00840440c4200384150b1008000622964002c00217140c000e1003480c0180015520350001400070000d0010803402000d070f00200284004c5540310712805414541e0b109131400c0c550184c15500100c5041c0c01341c400f8016400001040e59003084000341561052001d001d1724601420514 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 236256079 1250 236254829 236254859
    0x3010c02010b030d1107090e030406090803040b0f03070306030c080102090310060509040308070c05012a11071a0409092301050103080304080a020f10020d0f06030c0b160f0c 76
    0x28296810901082441d542c0421030745848803903403030101602282c4410061030010f10741d0200c01d406103420342441d60000d0110041c0b0540d80c007038803200520303541c1d502038507542e01c02e5106a450f5040148010000008444010740d00201c2d90301d0f010401c40d4594a450101604940c09214581c3d4006040b501504083c0b00710803414040e0841004018038001c0400c0260200400007030411121400243c0e01074014000081c406400c08003c001c6c14805108240707803010043c02108104260355000c4c292144a003000e40d6501003030402501c031042ca00510307040d0270710074588603c0004d6010b00000c1250586403140c0c4080b58054146442c1d800d420003000108807030307007114003c010b034180001400803c0000f41203a421170f0348400c0305952252000030480c2008600e95014086015011052050141c29000780084480d0140c080020b40407003110300c003c59000340f000401040e0030340702c10400610341501400446500b400c5d24060917885581d100b02c803002880c4216a40b2002d10030038005551000900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 236257329 1250 236256079 236256101
    0x9010e0a08060a0b1c1b09050415020a02070503060c03010302151603080c0408010c020c041a011b020f09010608090106050901060c020d0201140c06090c03030f0d020f1209010b0301 79
    0x12980d41410001c1c81900e403031000300f03001a055190264800c1540342da0708150020240c9040300300d84c108203840d000c600d011120980c21440c070390f4200c000c15003082c0c80c0300e078034021a482003a0b000743c4c441e0311303400001075004a442d0100b54000c0707000004541e1403d11605205000d40e9660664960452041044000582c4a0440a10400d124100059040b00000840329400d803c0c100e86595516403200d91500c9141c008804650801601050300b40d0001030b000420901100c0034001e00c9460071b001c004820450000724001b904403508031240070502d260b080111230000e4032003803104400001142034108280d00903c00070703a983c1e04210561500784a1030014150844810b003c80d458110000e19102118401900c6000000d06d9071045a005031380d08520f401e1040007103078441244124a03900c9500803103061103140242c100481c034614010085412014000501a0a022003441088005d402049400984910400c1800034028035200300c14442c40605001069190150043c0745c2540c00003071103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 236258579 1250 236257329 236257339
    0x9080c0609011806091e1101030c03020c070501050f130f08070b0f0304020111070503010f0c080114091603060515072f120307020d0303021306050c0303010303081807060509010e 78
    0xb094901c41c00c00c20706070400580006000c03444440c5c90601425015039041c0021072030b01c503071040c2d50402c0002c07012216480002d880401c071003403984000398107a1052501c103000340d0300f00c54404d02c183c1d8000c1c1c0143c840c3c1c0c40c1402d6413030704110800083c00c0d02d51107540c00800071058032550401c00c0380003c1240383c001c1c3c404c8241960408542c00d48400d580e00000d0300007418070070004e0007580d004400b080418000c10008000340110104c400040d40140f85054070880003509480001c10404c8000e08a10000e90002d0304048081d0f564180c2000b070300e045146810105515114002059031b180380c202d600c1016550f8645544500c10b140010084070305054074114082d004090ba031082c0011465603a4801e0217139011901b144400004501b9403064050095200386401c12000c14580d2650180600d001034540c000040e43d110355055925019000c001c903201c1d0700c10801440060700c50f0380d1080e04500001c04610500300c40a503454100b010b1380e00300c403000600c0030440c1c042541c0d00824a1907108801e43d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 236259829 1250 236258579 236258591
    0x80405060705030c0328050708040501030b010e040501090c11010605030a08070218150a1d06040b011103130e01060206090619090210021f060303020a02090618040804061d030d0c110409080c060901 86
    0xc9c607140c80d4001d42c868503041c940c0d54842511564041c140181d462103008004102d07940c2c4800c8104002c1945644031000508440c01b0910110414440c0310b0075640d0080c01468030080075900c00b40d05600100c8101d030050320140c420403158841d007040c2800b401c8000d024042204d001818000c410f0190f40c855905914081d188170341010704480a190064001e480200e903001207100180d49410301140030074814070000a0441118003c501e41d24150781a1403444003d6981c0c2d2103040369600350a468a078030320380003080420340c50748200b0402070144a0101010640c44169000140200c03510326418016810040c94008200d400c45040008480d07121810421075040d61802940c8010040000307005040120204803107980d400031250310340c0c407960303034508051030316281511164002d44a060040740e00f1009250404000c1035001001d0680a0000c10402c07224802c11100500140c1041d18140044440c11350103480380d000340140c0764050004256a456440390903458468000c0000d446a45096 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 236261079 1250 236259829 236259833
    0x120e0607030801030215041d07050c030a2303100902070f0b01090b030606040c0c030c08041203120606020622031e09260d11010209060d05090c0a03080405060705030c03280507 77
    0x52014108c41980755015003540d41c650081d20144070710315040200e444042211203043d5841030329409100e040643c8040d00100340071140b5174a00094940d04540c8581440c02d00c06c1f01041da01501d505401131054513462034150b01c0da40700c192001c1e048004801d84441805e240bc1c2000c020050f00003605031404c0102045880c4010090385295500400300079003404520240312090b030659000d800324030141c1c04d0404aa10700504090f51107041080110b043c0310001415074004a90242f05030100c41c2d454051210389409004414101e4104405000076018400001c101a01d50816114010b4076111400c0c5c0c00c224242c7c00e86c244064166004542581c1c0d0070201c03281c0800c4103440000c0300c0c200400590343e40410140a40111125503401403400b04440028401c0c90f0042c1c1d0192480c01d041c0c4a4244d009402d01003006003502000d00714042c20030080040c2e040210041404a0090041d2814221090300d07260860b44041802c2100310038482a81500c0c4804034100740700041c03503003000791034a4410707 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 236262329 1250 236261079 236261099
    0x8061e0a0b070c030605090a02030708010605060405060703030f05040818030304030203031917040305030a06050319080a0e060301121218120f080318010b0a0b0403120e060703080103021504 83
    0x41c094001c1c00760340429200100200a141c10000d140c1c00541030285160004100360354101d4680c023a0f12a101d0000002240c00301031040c2e4040e0f4038050002c92400b4285014810540d01202d803c03803c16544c0d18440c0d89c06042442a140540d1140806607960040b41d40c11180300c0d6810030041c0e210350410081000107a600000b141c4035900d11740c009181030a4400c4050f40d405480c2440d01c5142040001048105079010008500c1010f05140811403261641c051590341c2448039030224411310b21865a0001c21000e0b4003030003c86090746403002101019034003044080d00280e11a01865481480f000100309055201284140340c0d40382881d540ea403c180c0e9214a05c803503100700000004900a600c060103a940000f0480a412166103036403800c101d130328a100c00c40803480481140d480c10121502078038110000904071040042c0c01403c103030440c0c4400300751880a65003c4140b00105549202e107442d200081c10f80d250090f1260240356242d40140312136071070078500000c411a010881444840b1503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 236263579 1250 236262329 236262349
    0xc040608070e011e0513051009050103050303070c05030c0f030c060f1b0304080702040e03190e0307140402040816061205010b070609110301020c07080c04150b0703170708061e 77
    0x1c2005006901aa0801070f2003030f600b46401903508881c0a06d1103c1d41c04442d6007000b1301070004504500e42540d07071414600110b4500b8040242030343c2040011407507561140000401709405201620316019945d45c1c51440c2c05034940f8540142d40000c6642c8080150910442d644941d0342551940a0310b4070762207008400380f00d9071101c4099600030000c1014000214107541840380c0c090802c02c14503000354402940c0c1e03040326a000070402a0781552818140c03107549801c00c0e035040070b0020304d80c05007403007005041280c0c0c921b121500300d5804e210000e4203c204004186e140c42450640382d03509428060300400c0f20041100d007038101030500e401006103d40340c00883c0c0c03076190408030000b0888418a0659011141844400d61542c00400c1c42000c0701804900601100d1904c0c0c111034402201c18180b000361480d414120701c4c101c8110000b0050311030010f0040211604ca450804c41329810b10301c1500c200c00342611044000f03070403c8100103040c1482000001da401d5000d05401440300400001818559 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 236264829 1250 236263579 236263589
    0x1f031d070315020d050f180705100309030e150c06070305010602070608040204022a070509090307061e0f0507080c090a0915080a210912080703050c0f0c040608070e01 73
    0x591041507180b0000da80c141c6509080826003801203080c00001882040001d82d814400c0400303291707405800005c0005d1b16400c0314006044109c20a00002c0d041c3c0082041e002c0c10341c14408940d03005441507580c2810034444101204c05c054444860380c44092500c40003c00c00402c0c036150000500c80203800180100c00c079036240c6004406a511440450064081d2114040d03036428810140d8034040c00340864104d14407101c0b4121010160b440c801c111801034150347d01310494100704204030210b04680c01004010035049040312407440f0304c0c03041c14200c400004000d016155a1400c0c007400c694000ca01e603821a01151501b0308091000000500c040642c0c4078011034039640c0c81c1034250fa100040141c10040c02440d007030b45c440e0003240c1450f01004140b0465481e43d40c81089c14800c1d1540030b03040c40802e0b1030820000303d00c0740c5110303540c00207150300004044d414480c041c00249542081080040400d440403000781582ca180803060009070341440e0400b5050f40c10014083c07120340500120141155 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 236266079 1250 236264829 236264843
    0x10090203041e0606170d09050d140d02060604051518070905040e240f011701020706020318060a0e0d030513080403120905030118020402181f031d0703 66
    0x3031107526103620200c03911200d070641c00c80e8002542c400d216540d80301404079500180401e46000103410b2158072502d80001050100700c01480a00c21400d056202c406117030f01c1414078a8446616000e04c0d480c00d14062940c000507400901040f91508150095542040030343ca03540c510540c69500050300402e000800c180c0490080c000030300c0325880f600c4810300500d400f030410000040002010b0740c0303450800c809480305500c0301c49001c00454242d40c4452045400405521299081c0103024628042d07040d004034056400740100000715020b440154096402341c1c1e400c00350110314031081410200c000740240a031a24154064100d480041201c01c0c20015505d0f000130565030700f54940b0f4030110340c0100500441000b0402104106400c5040d120403101a103030300840c6130342c076010182680d8003182c1c001c6074010b800450b00b0040c18903030083d041308068641601074461042001c90505116040030080c948510b0340b0410220b5010f01c0b4808800402c64004040d410081302c0442d9984100c0c0300080c081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 236267329 1250 236266079 236266081
    0x6060519081e01060c05010e070f030206030c040b18030d081006180e0c0a02100204120b0c070605070f030b0f10110f06100303110d020c0402031008120705011410090203 74
    0x4202c0c80c14103035060366000c80c40c0d003109586591004000150710074046990307620b0940303040200e0400141d201d003226101401c101c2e2450540c1d00740065a0400b61083c0c501c0081440081401c15010000c0e110000305070258035403804140040501d0310100e10300c0c410501000d0001d001003005c0c490000c10036a0801c2c1440e003040081c504402c005110030364030280031001128248001c0b10030813401000070704e0310b40d401c580c550b000b07102144080748100e2051304400f0021001480004203860700f516809080c1522090501103241c85000c1a1001111640700051100d61140c6049425128000c10010195602d220311a22007000c40d85940f001400041401240380751402021003c0145900950f8044280c40407406c05c40d0620440044078001200402c50744408401c000320b00103a0040c204150340c0c000d151814040e01400000e50000d044a055801220008141c038603042140010380b03120074000a5981760315007030090868612440d040c0703071890100140645001c08101520a4850036000180d403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 236268579 1250 236267329 236267341
    0xe01090c0e300a060e0303071713030e01030207140c03070902070f0b09160f03020907082e1d040605010515030403050c010b042d0b10050d0e01050c07060606051908 72
    0x25143c030b5104000d24071410080c1c004901c01000c80a14001c4210340c03104103008030126260528400111924420358240300400004641304031000c03111000e041c180185403040c507880e260b8030035441441c0710126a10400e500091810100105001480a100d0031803c225a503a90a0194444010302030320803000c0c0310205072440014003240480401204000340c84564400f07200300804203c0c0702c240d114076801ca000520b0179028807903961080c5c032510b01250104201d02540c02c5008000d51010f60300f0001ca0802043c01100480b580c0c11540e0052b41c4018586420b00d40001941c8051b04401e0044503001d6203014040c150300d00b900e4100b981410030b2030f01c03062120845401484205e0a0340e81c0a401d0080b001c4809115010040201c0c002150001c84042a55600c034246c400080400d500000c0c414072071810310740b003080604603a00090501107044c5032202c200c0ca007540e400340c440e030011001c000b4803c0104442442108000c0c811800c10f00c0c10314582c1000d1700c0d212074540c681d03001405002c10004171 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 236269829 1250 236268579 236268583
    0x14040b040504150507030c08040b1003140313080a0b04080714071401021501060221220510090b030105010302031305070e0907050301050112030c0305040e01090c0e30 73
    0x50454054001c204614060600c0064807414205107850380e4030313050100780b00c144240210f410b034101d00d4039000c0040d1a5503841e50300c2d42000800c80c0305120203101c00440011b594490b44240314042c0710055841d141c8281c41300d9604c00b5242c0c0f04040070743c01400040000b907181a00140d20035080380303030541c81d07210604125000000e00480c458a03401282c20104024a064005404c0c2e00300070307401c4501512101450004140081c0580d2000d603000c0d010303c08403030004000004115400e09481404c100700c84010564224102c0c4540388051500b42c0148490306141c80174102c624203d14100c03d43c640340244044840c0b0041c000c40e410150000006000e5901401d0b2000e0002e50101c12244065910000c1100c960070503103000005000342c000001d0203140502900b4103881d4424404040710202d0340d0107854800303111100714180041880300144522072000c2030380c0208000700001c1210400800300910240048200921031030118049161070f0f040b0700c20700324018080d00042201902c00c189054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 236271079 1250 236269829 236269841
    0x30918090708010f060e0105090f06040b01050d090b010e0f01030b01150c081c050112051902031c08160f0203070201030906020f07060f152d35161404 66
    0x54203600b04501a15030221350313440401228a902e002414990320b400400048030002d80d003801c1402041400725030a85030039441560505414180145052502259034050700c44486e4141d480e0000380c4010031902211008081d84084140703003407401d03581140c0c0c0717807a5141010300540540d180c80440040d40240141c4401c800150083d40c0c0e241c4451081c48048900d46020000042d403904050000450f92080d50104042642c404050200140302c01510701c0b202001c01c5003640d00d403280c100640407000c080c001e0400a140255204505490010000f114001c3e207041d4a508000c11808404403055000c03059420807682464003061030710013410310001a0189a511001302c00000881d5030400c42c00b68020400f07449c5444c0103000380901168025240c46541c8143e40031403900328001380c06004503858001030501081e42861026885055000003070348207003248034184006a4800c2450a0f0f000c0d2000315091008008003c040c0050944045407440c511480512011a080c24003261740c6e180c001d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 236272329 1250 236271079 236271089
    0x3071d0a0b0301030615090b030309010513030c3c05130e01020d060801060806090c06070c080a0f030e040b030715021203040f150b010c0b060103090614180309180907 73
    0x45840f940c5070b061540003460200400b1400c00fa01401c00919890180101074103d078008001d1402c0202131001504c50317502925407030403d07020b011008000280340302c41100181c1010400c0c0030300800d901182c0e00d0310181480c10030801007031b0070a004102d020320400761816160700781d400512802c1c000000e40c0142242c103070071010350350010a80640b24286640100d080382c5000d00280b21041c2d5580c03841352515030541c0c15400070f80010106121a081020041048074851107a005010344da801d141401c01c540ea003800c6807003244807004807062682c03002d01524040011101000b20610a100280c1e5900d203c0c8640858109207040c064a154001d12202d803000c1c2001d1100e030b580f031410703207801008080300000031107201140c5c54038841c0000d03035441600075141040e141d00d400324a09460b42c0100480043c61541010b03110030422002542c14024030140c502010003101042c1400c12181c100c8020300c1d105003016030f1003405031450030754501401c020344e00d00a2009480585a4442050821100c3c0d041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 236273579 1250 236272329 236272349
    0x61212020a1221060e0105190305010c090914090604111c050706081602030a1b021e030c0f2d180a060f03210302041a04090501080303071d0a 62
    0x854103080d50002803610000c10b0318030b10141010100e08a83c001c80d4214018444900b0380f21005205c02c3c1800c120140c2c55a0119882002c41c40c1e803030f9289403d40e03020807500000200794400c10043c0c400e15000360880b089150404840a2414a074660313610b59004201034850b25982081c2d4045444102110f800700c11600ea4281e011030032270800ca42e8841c2144075000c00100c0c40e00000d841c41c0d0900c0e003030000b010396a60141d03280c0421544110ba100a2040d00b11881143d004181c00050b43d980c01e502c8403c0001c42a8010400301030820541400c60126400b406840100042256aa1822032070324030404c6200620313820b41184810010603110341c0c103446070002d490706900540d541d4080d4006d4454052441e051000c50744039665407000c0201c0b440000c0140070783c900e15a5410302140c4011000b49500d14005003080c1c0e441809804200c3d49056a079401b041c0001c080c031103016180501405403c00e440254614140908020004030b6021001384541d140349920390300c907549150500000b031454000f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 236274829 1250 236273579 236273603
    0x60a0c111203160302091e130c0e010e060316110f070e2401080705030a1b0504080106080111121504050c04091d0318030a0218090d03061212020a 64
    0x44540340c0c6034030950f2400d0700400001c8031608410320900845d41d82e00409040c1240a043d5810b140c980c0840c80b64074198030401000c400940d0710414030030304482541541d01c02d030b94407480400140030044072507000c1e03008250030800c018040700c002d074000d0390303c9030b040c0b403d50481c02010074454100601d1021191041c0109040024840c0007248c180703001f220b01c00c4924000c1812410040e24154400c0b2103e4003103120240040c60b030314019000755a21880c08200880d002217811007000780c0b01600d15120001c290080740520800351b092040390050520200204002241000011814010f03911010003480c0e0000000380c001c481080d04905c80c0c04098002d01c01410314131610f10f11a0401c0c000e02442501d4101c096208840313908004503002c405002840c90028400814501000710300501e903010300c1248444070040c1c90b00a09211005042c1400c60766030300b40580c001e4140030b494480017007054200081440005141b144525140d540038001d41707181c2c102d03101d00380d00301041c0582c007500490500d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 236276079 1250 236274829 236274853
    0x102f01051302120c030a0b060102010e12031021060e1c0503150414061011030c0d031805070b0a09030b04120905040212010306090f12121a03060a0c11 66
    0x181e4510740500c215204600c03801c00c2c41105581c0e81c000c5480c10b625900011032100070a85aa5940760400c0041c030011031660302028805260041c00328989020007000400c02110345103a0310001d01074240201003d012807400c0c4040b0194624203030000d4400303661503801c41440c010800c8030b900034010750183c0c07882011808001810750b8201f12104404004141a081d80d14505031240e80c9450001c8103d101c9a611103034180020004501e00000902151a50544450303c0400107001594100340080405054150000302581c500c000c0404600070007d0404001400208030202030b26011074a01d91203000d85142260701d0320b803960003d8285a0380720180424840650300381d214640c07844d141e0323429180d40c07030050000300e1060300810b20b0038030744c03840c01440090516081038207094000d5444034142c510507222205240007200c4e1450118140c1c0c0c00031110741c0307014010078500009480c1c40b00101600c01e00444d40345c1030b00409101c1d034540d4403c4002e404a010300e081e81c0d94443c819040700d01005400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 236277329 1250 236276079 236276101
    0x120a020c010c110312061201090b04021c020102060106080703021b010207050c01141e0408120a020715300204060203070b0105090c074d102f0105 64
    0x3615a416030354200a24618000d0150040e00010001c100007180340c00c0451062200c1603c1c0900380f15403021001000c5055841d0902442504c00d0080302d41c81020b091510411510815551042420300e03200e90002c000f6070380200351281100c40d581000745d029620418100c00074071a1110000c6100381c4045203665507041503015009851141d001c580340b0700311b40b10056800b05501c3c600c6100c1584200042c9582d0701c2c04003c445d0613201820141c03030070070791a81041390034440c81311314001c051003010942e82e00c4954100500d0004007001904400c5410000c40300400c50400180640c0b0500d101008841035091450314110b00310764410b404540740c03522410001d40300d601100054171070b4151103001045ca454680880b90284945803100340c9030003c91b6070b44000c845041e07109044c103800d2440032080a82d62281510180c0b2495181d188041000e10840c244101112900342c0c1c0a0401c11480052864000038007006100c051814070070703100c1c0407007909100344810b070404030b8240d4201004e0160803d1a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 236278579 1250 236277329 236277337
    0x501260a02100e091e06120c06040603021309021c020315030616090e060321071b0603050901020918060f18151504050603040807140a150207020906060c03120a02 71
    0x41111042845c1d00d4901a994036645501c03245065115000c01180c01850094400e1440400c4002038a1210180000042a6800a6000e0400700b40c000650030140920800e1070006040c91000840c06e00d018055448461f800400240080759070000124083c041c3c00c2031075100805009040300c01c0340c41c060402030303051a054120000400d03c0d40e600494a1406e55468610801019005115081510701502c1c00c40105500100003d20200403450201c1e00c1c102d1300491160410700300e00361540c5400f000030308841c801000c4995a03403060207040c00c191b442c100040e103030000944050340381c3d4036283c0000c0d41e0080f914100540c850182d0344141c2524094034150b5200d503401902d1241c0301c4255905106881e400580c25000f445400c0005102c2c502c0e003038010f190450302070f240440c203050003603030346080000d20503900f64a20f51100c0c02105c01c0165902520040c0c404d010020741c20007000d070740821740c0c4400240ae15407042c03002198141c0a030800b0000e4030090303001910951401d0074020b19081c02948 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 236279829 1250 236278579 236278607
    0x318010c09080c10050f070c050316050d0f0201110316020405010b040303050f0a05040b040602061b04050303090f030f1c0e031c030209040902060d0c0806040501260a0210 75
    0x100308401403503401e000300080300444185070090810300e0240f80c204a13078140c1451454040c00742c188143c540034407903a80544002c034425410301849505210403d4035041942054421903403110105010b107071500030703594100d0703540704040f503e84811520050381c02d10b1542d09130301c0e004c0c0720104e64034669550705600c1c080a46d00a0303404111a90302c81410900f240f240c1d001c007602180e403c0199001d0440d03414003e11600e00a407600c5802c1544030202038802d07a00a0344290010b900040c148403040c0d807070242c403000c1d190b1025482c1d81f0303051038030000c80c0d228060706207550b204000411400425031402c0c000403107100851020344020180d12094451148043c906e1640002c4191409800381e04001070020701c905118603550501c4092984100c001e584045042500b2a0b01ca003290303001601d40d10301404514500c4400410400500c6000905030710700145060310460070440100038544121851451a541e03090740c030f41c04d10f5540303074100d4034004601000070740100d12009010002d03507124450000d400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 236281079 1250 236279829 236279831
    0x91302040506060703020a030c05070f09020a030507031505060c12030a050115110604020d02030a150b0f04110f070813060206010504050c070512031902030f04120207080a0f02040b0303031801 84
    0x82c880c482407143c0ca0040003802000741e0b0007105030741d021034054003001c91541d108801b02c4280c180c5601e0b08031a01a02031341300780012034020426580aa8050248681c032402602e410001c410020380f034640004824800c6501810000601c0f000c494002d125228400ea80042019030303c2c10f103a40c089005182c01d10821154290032048200d9130391003020059a00105071000308040c0d142c0d43c081060360511381104980c1480303602c0300c5100081c0b0010313002e505400342d0280003c504041d1b000703001c186840301504500c0b6520b4021090260019107080c4d503400116641c0c0103880301e9086c50019644e1044000c50079244801d020700085050b40002d106050340c03000d40d001e00c990b84542100d14441c0c000c1400081140d0080b0b5400c0c0c0c1c00f14a41406943c1c0156189414025200c2d4620408100da00a40d500320f000c441c80004c00c02030100520741e0ba00080f130107100a00c5030900e019061521105990001407000d1b0641401038250343c0c03603401003100f200d00202034a54900300460811441e981800c1c07031320225 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 236282329 1250 236281079 236281081
    0xc010608101b080a230403080a05070f02060406020307180b0c1912030b03100e0114130c0b070f0c0b070b0a0501050109030204090501091e05010f0c0905100e0913020405 74
    0x142501002c207488411684410380503842e0030380020081c2c00074040c080c0c2c24003200385c2c0f1041395070b03103107030307086002d14020b0b02c0301c000c1800c114421005403032000701044140300340c0c0414501066800070b10264056000000140c580d15003501c00c0383c7c05814002c01e0010381c480c0b03103070204221214000900d4480381c4541110100031101850000c0e0103040c94024040840b00703002d0801640c0a030700102e00012008041c0d5a07085900c0009104940380c0c0b202201c86a9550314180340e18a1403503004503000074802013100e032059142d6481e41c00f6501180a070220b4490045054401c1000c005006080c41c0c0e440301a521075203496032191a80e9030002401542ea5891110218081058600c1164140c44069603030000c0030f8115001d10014000f0b076001280c0c95961003122001158061000040342440302001a0080d6400d090190035204c22881c40317001d0916162458030400e030040500c10441c1d206588120741020401807da9103400b504100d190031006200400500300f2541c01c1d0a01c480303200311410056 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 236283579 1250 236282329 236282351
    0xc030a0b03060c09090a0b040f06080c090919081e030601120908090d0201050405060408150c1314010309050105010e090d0206010e01270207050303041a040f021003020c01060810 78
    0x62003106443d0031202c140c0810030b024250408404050380310039240700c00f088401c030380801705089810303041001d5212130b0348030720a01c96124288004039080c8011110000c05062500c00662108180c02ca00c501804130141d03079000f000140e8081d181040c20580b200d003031401403648400c0255100b240d40e64002240c041ca01c40003002a071191202554000342038908100008007889a000580c9905a06100341408009650381e80c0d04000c01c09480b01034050650101c1c0c41d5542030b840380c4080e09141d413102050050409400b407030800c0400300c0d100d5192421689032002c006900a020344a80688a9400c05002040900d180300b029401030760f20004551402c4c405420413a07c0f22407c0c02590b052880b90310040102007404600c03081440300180d4407480e0600b400881c18200d03441040f00312402d4001004010500c400d01c403512030490a944005a12031520b0350342c03000419190a0000c1c032441c0c807010170704006c0d482a41510f2590060000802041d03449000c447c1c1ea4682c000404040355003081d8003506 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 236284829 1250 236283579 236283583
    0x30918060e0717010608070903020a09020901031d03030601080604140403030c1b03021203100b040807032619110106080f01050709150309050a020604030305032a1b01140c030a0b03 79
    0x2550b01c149400f540081d9003042e40445411101400c0e00040100200b40400540d84400380a0000c003c0440010798452442c4000340c00e8030140300d2841c000344102c807000b0745401804022654425000d203000b480315551a00083c00509004c0c00c28109955018204010103401d940480e00325001034884881e41103c5400b10242130102d080c0040044c0c10060781d0340d002085801c059038011040b01c0800399503985a810090721a0410741c0051000e92004a0800501100300c140c4c00403100321144a98200303100001c03031080e41c8a001070180744001e03032000c2110050710400e04040310a00c40c100074804196203000c603a640d91020341c240c80e000d51800c004035200314012a40241166040c900d800304c0403941e15000c3c0d008007924034055a407405200c240c0c9005a0300c55001344081c521a489903074503810b103d41d402d200612510055400804007481c0400c10b400d0000c00c0e20001c2400307d4515080b0f0003020140f90160256045a03211a0346040600071281400000b03148036002000c810800390b40c80c001019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 236286079 1250 236284829 236284847
    0x603070b090a0501110f0604080d0e030909010b03060d15090204052223030d051f0303120902040e0105090d081e0703111e04060e0409080d09030918060e07 68
    0x99020411070030400081d40111850741c41ea081e0b00c000c6c1c40041c15103002850078a02c00302d4040741c0628000441d07d070484120322940810004072001542003c1c400b6011921060040c0540ac00710003000c0002111a40e0b40c0e032a0250701640074128015402e60000c4840141c00e0b4050100d10440c180703000a0441c05443c040c040030445208800c800440b829150401c03c940d856000c080203118640d6942e8104101300010004110680d800041c18074003c041441d12882c01820038103c2d40642c1d03401c0012a9003c1c109010f0b2590031080010100c07241c0c80001c0041c1684213043c101c1e5402c0c1820005806804115003681d00140d031a090352595540c1c3ca4030501c1e5144081300040c247d40c0c13002041015201b6800030902010b405040c62402c0c501e241c0480c0c80100b00c28110380070243c000340610005912103460541001c0564040c00100080e0f03480c0c2d0390354050103524948895440705400203042c07003840903400800c55060314240b41d074904032003000544898020b400c84817440101203581c2d01d101e00184 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 236287329 1250 236286079 236286097
    0x20c031e0303010b220e0712020c1203071b0503040f1e0603090606030f150c0f0503040f030203040b0d06051806010206150f060a020a2010080a0f090b0603070b 70
    0x2031482c0d030707080002c941070a0701301030760035088111144a031220a04542e40c0003c003401e0170004003e054540301800a1100e061280c2c010080d500500c07100854a2000886e040e05419400340c10f41c803a0b030380d200101c030381c115280840d0043c0c44100c01039400340040800180103070750000c2000e03462180c680c050142070396040650184240c1f40020100807180c401e030b11030945107220319004107886640c0d45403800c080601410644140c0011002c0c030740da8041a20402400e45941e040c8511945170f0590040c2040c0001000a009072100c0d450750410148240100ea028000251110361101d11044400703008010b6402440d00031603c8180a034610340001c8003c03842104164028002691000c210b98444084540a15000902090b0070140c595685000d086481c066600606041c01c9500b010310b44080081c82e05000c030b4170f511f00300d00c0d40740c0c80d4405110f000b518541440c82e0940c4505111b82c004210003c4c908000900d421130030000c0060400d13000e0702640044084900843d01e40c03c4403030f050305c601464 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 236288579 1250 236287329 236287333
    0x327090a1b080402040204090c02010e0c0a0f0501180f0807030515011202130b04060603091118010611120d0207030206160503060d02061c060816080601060305060301090f03020c031e 80
    0x2400407148902a0158890310150015050070b0762001ca68050303c12030300c61840540d4449440083c0b40104010071007100401b1103003410291b01d4822030311007881d0640102810882041c19014401d059100076200400c24007a014850703a584010154407002c49010447e034a02403160301700c1d40e401c0c0c150180c0d1b06a07192014080210516a42002020407a550384003840a0729100740c40721640d81ca1041e10001c018036200031071290f40740d04d01b0f56000300401c031440d480303032080d14244064910700002142c1540d10384d013003081d44031948144091801041c40c04001030501c0001c0c5501640f02203802500c03102d840b079002c880c56070312009072503d0490510f02c80c0c00001201032000400364034000c0c4004494500180c00c1a150418402d5001070016104451002e11a1145c20410040c107040158140740300740c009042d05902e04010400c1d071600018801e600c1015100d41c00b15130039650a510070025a42d1101c401840d6905c20f103400ba45641c88800464443d0203035603440000d94039000c1514a0111940700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 236289829 1250 236288579 236288621
    0x130b0105090601110a06150918021203040905100f090506130b060f0409090507050306070c122d09080706050f0a090e01090207060c17060d0201020327090a 68
    0x1060141c002001400d41d4108001061a0f03d080070080c0200c1c07007110f00408001c1030390038110300d41e2200c60719a070344001c1d030701450f01c2c000d01e01407810020f03003101550341141c1c02084482d08180440c07450045070090070300145801d040c0708200010400300021a8440b41002c0c129035503d1510408a8508803280d68000310005e120070300658843d803007620581001481c09061121429448000f508280c111040341d968840c0b148060140402041004000c200d0080c8800d01d03000c413006007801c1400200400306002103c203c1c035a00c1c011031032030b040f150044c0880c08251810300440341c0641007818501d0301055000c140480e1a8001082000c10b0b03550603220145081010069915603a010007070a8040200b100c0300400c1402c254200b19000300b103c9000540c8640c1d2a003454802c9403016000d00003480b11600c02c0d074281c1c007119005980c1c0000c084400140e00112400142e0842c80781e1300520345100c200f05400060268440c0440c54003020550704d10170f845d03450f109958101c1e680e075000010b03810103030b807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 236291079 1250 236289829 236289839
    0x1a0f0a0f0c021c26011d0603070b030a09020607060207030809010c090b0711061b0106050301020a0915021e030409050108031623160504150302100f2a0506130b01 71
    0x1049000c000310742e85801840282052a0182080c2106031313405280ca03c4000100001c151584848151503050039114080d4100600044e60790342040c4071301c41f028a0048002014403c40d50302030006543c003d80f4071a522019450700f200290701c042d05c100c000c2071070381c800b04554000501c101c40251b070098503881d11090414640304c0054200700c02c120b510740c4155a03105000d8850602510000e0300c0035454038040220701c450300d4203450081c0c10550203680306100103039040d0b42c0700d4245002c40f100580c0400301d024503071208900740848140043d6200c0a5a100341018020000c0204211910034900f082180d8a07100c0302c64130b03803007103403060054990f00600c080701080510440702c418070070305054040c402040461a50601405111b01e8019074030350746081016090030f01404449005601c40c00c1d40403419940018482c075514140c0380c0c00c00c0740c8000c8200d10304c2e02070540044036030443c1d2080007840c0d641003412010005070010407103443c080c11012038650145001c1960381694014103140b4213a00304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 236292329 1250 236291079 236291113
    0x605130512160501061e0b0f0d0c020a061a040c0311030402060c0f0f01050103060b010203030402030d0e0f1801030201020f030c033a0b01020c0a05060909041a0f0a0f0c02 75
    0x6880c2d03004020000100741001900034403400000b0154561000d07004a10014002c410980c641d06c0080700c140c0c02c02c094100d00414a00301d580c89044083d00189084003281c0803851f0005c800310060050b440c005561b000c084c000346841100300c90884091226505240040b820381d9102c0411401455040c40864010300e8050042e04a64030950111682c10b07142040c0c3ca443d003440d1880300341c01d695403600140240180c41c003550841041c28002140395081c250f01003603a4030f030401d0403a02081100c0d0f0124540b0740c2d80810400010303000030310194220b03201c581c0440d045c050078841203001d407144011081046a000c42030311440311804000d54101002a02c20342c0103008415900304e06a0160509426200101070011034500b801c19400038407003200c2000640341820281c51680304a4040784100500d60b150002c603410f044098903072010a407104e1514000e00c2c00c2c3c6442111542c22418100b044400c00c00180da840380502241c01d114800ea070740c11103002c48846540040041e0000d1184101c82411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 236293579 1250 236292329 236292337
    0x1c1b1718010905190c050f06030a051008010903050c010b09010e0411041107060b0405060a08030d0f060b19091e050424090608070e071704031206120605130512 70
    0x8000b207000e039001d965480c244412001d01092107841082c411080c419440410000b5242c107032200600e581c01900018005d0200074940042580c1701c000041d00303101640400002040b2030002401890f01b1440c016103150090b62800740c1e01c0d881c01d800c03400c00b4030f405880e0b82d0480d9648507469005803213646840b003016903611269074020b038079901401e112804140040c10083e02440002400d119658100000d5130f1020b40310520a85e444003080c004108044100c4601030f00082c0c0c00030741c6407c1c41216070060b0500d5444007002030000301d41c4010141d01c0426825040c001d80c0c1d22640415141e14070440006a000081e0344503440c160010b02c80f5050660050700002091001c2c11090060b0007019040700c007443d00f00302001c41d141d800400800c41c00300000ca018060701507003141c6511b4032030001411840444c41d840c91380700c0040003050034103001c1c0302d03000c00987c460b20301804045d444e40c400420219080e541290300b1454400040c280c0e40c01c045022407641d034041c000d0f0000c1e6422100b001e0840e00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 236294829 1250 236293579 236293621
    0x20d03020316030c0209060a030209070c050c10050307090b030403090b071a040503091c0b0f04030909020703051b03070309060518120a0314070b1b1c1b17 68
    0x4070400440c1d400a5800411542480c4203943d900440342c3e0724030600c0442c1070003601940c06148070a60500040e550802c21550040880c80e001c420162035052642c90003031503508158100105140305003a01e0f0744400218030621031074079404009683d4900c4c00d229031000700c4010340000d00c1c0040a1007007a00c19001042854000c070700400545801d0040c160f21001d040d14201c40550001908807103a06100f1008062910714012041400181e51100385460f08000c00860030058000d000604260107904441c02808500f0002c54031140780745006407895112000340c000e0320800501d4034052000000445e00c40b03a41c0341c0d82c1d440d4500d21f0542c003a2113a410041000b62044d2103070581c8045601c4040400c2c0032100140d00a1030300e0303409410007a00207508030080d0000c1e200e04020340750120300d0f14004660803c20b00d420311103010382500074202c580d014082d5010040b4130b10071701811107542d160700100e60f501c410440c14011450500d4003601d2200c0c0c9203250620031401c0c40001010b090018031501200c1c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 236296079 1250 236294829 236294833
    0x1605060f0d020c070603110403031704032109061b0c1b081002030103110406080613030c0b07020109050c01081515041508040c0503070b19200309030f010b090103020d0302 75
    0x807207002005801d0360050a2500360030f62000c0400c12003194503005041d40006076900d210f01d054207645000380503046c0b0080c40c66080c901c54020408162080980d021039201c4600c00d13075940808507070844060141075100b6502242019503d103070500b080140b0030340c3d4490646907d240d101c0744d0b5540c04281d0807445440d4050300c200030000620400e042c00398081c3c03984400c0700103940798150701c1d048a441100301c05640c0a03510f00701c420b10104c01e00080b4180c202c030621110270703031902a910701100d40310040c0740002c1840011005000000c1e805401442c8018820405e6440002e122001103800c0c03207084907460490301e880340310100e4500b40703441805100c0300031500c241c2c035040d1108214000c038034402c2c4600c0000390f400810402800500200c2001074401200a03211041c50a48403000a00900052840380e5880310110705107507004001c5958521a07030500c2c0c90840252904031510b0350804480d440c003e010b500800d1440c100103101d4040d1620005101010070713400c5409014947c0301140d402c074154 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 236297329 1250 236296079 236296087
    0x31b08100506030c04030b09070305032d0f030106030b03010902030d03090c050303031e090102180105360126150604170c040606030e070314010b0405011410021605060f 74
    0x2038880c94000c61062112198545e41c8501e541f4194402c0c18008003400042d802440c828000102c01104803090344140c032040c5002000103011001d5075611000503162040c5002402040c161042c5000d98100c41c1562010004408288145401e1366a1220029815080f01c248112158000c0c0d00140f002402040042000c50b141c60100e403441e481a81d50403619804640141848590b42802903885894040250306100120402d204551001030f0864180500442d06203503c8840042501e640f0f039810403031070f418541d2030701c0d10a46904a07411860008103680349450202000e44401e42d40d01001d40740c00d100641c0d07427000c500300c0b001c1c40e100310740c1c1e0002c401c00000880701894030300185441c4000c0082e140042c8035800b0001240c500364000402e05080c06940f00381c1003c041000822250401440d1420822502c07103d40180f51368400c45921034581000800c49100c000208100c849040d1000d11800c0c4000d0b00c1680d50314404501401c5480001e0018007150600b10050900142118141418 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 236298579 1250 236297329 236297339
    0x215070b16210b09011e03060c050f07060b031b15160507030303050708070c081c06080f2805031e0706060e160e0a0b0708040b03011212031b0810 64
    0xe00340c2c0b0801000d8655181c1031607100501c4d000941a0042810038200504a164000c425410040d9880060b21460b40d4002c40380741a80140126840c408040e030010307640da4218a00140101103207003030f180c040c0c4202c920b241e901c599807201c1754207070701d0000f801401d542e520b80349001d00769404080441580d9107000140000280300300450340145100f91008600791500d07040051044030018445020407081c00e00c5800407803002c1c0700f01c58400180034007080b020308002c106680601125400565a40700d448900500300802003a42c0342d5003841d200340803440588020710403900030803840001e8600d800407c00d44265180b041100f52000043e44152801c2105588450045415560060314541d644030100180b50580800000416007a820921000c1d40d043c00801c59411203409182d01301c810005124042c0310082e0242c0f40201009140e96560f9a11409239041442c0480d40c1180c1c000d014000c005003450007030107810006508080c041c0700b60074214030304131000e2001501e4104120070710400881c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 236299829 1250 236298579 236298617
    0x20306180c12010b070605150a12031715041b0f0507031403070903030e04141308040306060f06140403050a0f020d0203010c080702151504020f0d020301120215070b16 73
    0x300811320042c0040c0c030780000e81082815151300231b010071070700d5030100c5004443d5a54910700c04142c4445100740044502203140543d058030900c05002811130505040040d4060450700c90040c0b0f050035601403009012240314a202e580200840e40b0104404140400e4002d201e038010b456a50b011b4500018441409010612190300c00d490a40010350b00e114240203140e00200360140502090300c0400160003a8040c81030030030000340c41d5100348440d14400b0414002010b0580c1d002c1c40e0441000c01500e0b030b583c4030030708401c4900c1c4189000304881c40b41c0742c0001116142618212034218026001600342e6550705074400c801e0100c00c81c0d01c80b01d070841700c0015850900c916000b99a01b501d83d140781d4101120b002e407515145d0003025107002500b0042000b10640d0700c0e20a0f40c1900195005038550141d280d924405004000881da0f10900c08800029a55403501e05210518000d450011140b20880004007a074451441301078851480c600202d100d802038000c840c5a8ac0b402440d08102c2032000841d900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 236301079 1250 236299829 236299831
    0x3010e07350f0906180114090a0209090307120f110f0717011a04050a0b09040b0a0524010c02030304080703030905040c020d0f030e010b0a090c02010f020306180c12 72
    0x21003070480800c00c0309106010000e003035400212124a0407020301e010401c460307135618010940d00301985030070f843e503000e14400d40080c62941c1d580d801d908094903180b00e80aa99030200c0a00b41d01c994084c2d0042032030500c01104071402a6000624840c819a11b00c2e02075683c0d030080c0c00c00008021100c0c50904101809000d800714408460002e854034610713110000c0140000b4104141c0301d0b902d00030a401070304002c81c06075045000242d80c0440c1c655503542200c001842720b005d409804c40200310410040050000d00d403803046480a00401c4103468006580c010071100c0d15108200303803840003044015600a4001c24000c80c0300908403480c1640b250f4a8900f0010158805c9003c224420f406002a143c036000720703800340080748010024003007459002441c0001c02c0d41c21105041c0c0c2c07906110713144082074100c10024000a40300c000d450307542e001030b80300401c840c4c0110380c019440d01031290b00b283d4284c004c0342d006d008000d100d241c950304401e528240420018083c0a0391000810003d0b0030006014425 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 236302329 1250 236301079 236301137
    0x90902150703020618030a0e0103050c070b07091d04020a05010509131118040e03030c0d02070f030f03150b030705130909080c0f0610090b040f1b0e0105090603010e07 73
    0x1420307050401110301d01d007030f2444840b0b4010131b400c03d004819103a54401c0703014503007440902c0e0103d802d031260036104c5240d2281074001340814130240304104155401c40350260484544a41c0f0300d01c442c811f000c0c642080791099400951102e83c10804001700d40c4510042c150088004101080701240d2001c0a021520105c0708040c4079070740807480001d940760f4400c0041214038266818403d40401488968403031000a01300500443c0110314880d0a40f5075a068522050384451207140015050401914100321038100000283c2840c0c03141511450741c08402045405001203141541c480c400141d8064001120541805119000c0000ca07080c00703016000c4110300511081e907403031101000c2241840c000405503203490340305505211065820101500403101c0b123000008542000d5070010780606100c0e00b03400800e03414003d01040c442c10138519590220b54030f40307559405c2c090000c019212805000003040d8010018001000070080b0358100d80c1c0e01901e40d1503c0c07480b02d009111170000c0c030706a50b0b5070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 236303579 1250 236302329 236302333
    0x405010212010608010627050103020309190303050f180d050904140c0301031a1302040207030c021e1f0c110307121406010e0c0a14041802030603120703080109090215070302 76
    0x1001000d411104c0703c44180c903154800410b1004940c107030010300007c0d10a983c105035001000a1000c10140310123012005060392003050b8102e5402c00130003805090394a0f030011000c07000420100030350114030500b40034001c406001a070940c94400d45082e00000d250315005501d44885000c0a210000c049214a0b03900108649039411820405078841004441843d45c03050642031240426400c04424000c1e64100e41c007603921071341c0c0c0c03030300f21407100d1140c0000790002c131103405400c0000807401d000280d0750001d6400d441300315403580d260481d9480c04d0300344001040b448608040420550b4a06281001e07003c1d0448007800e68511903c0b03041040d0715000d031a00050b0342030881c0c00000a01605004260001ca02c0d80141403a02c4186528450a50000180003013080581c2c515020001558001c1c101101c000e410310104440e4170002e0760044600ca4824060750000416000045040c1d4802c60f405940c3c0c1e940c1d03603081c10404401454480e00581e0f2081090309102e071906160030007420114460340c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 236304829 1250 236303579 236303581
    0xd0314070606090f0203061528020303060f0f101407210e03070f061107080618010f0603030504030b0903070807060608010506030c0306071b0c0b0a0f2102030405010212010608 77
    0x9203c4211066a07003504c80c03483c010020b001c0320781d0f20b4106d5401e00460800d0b4440d82c0310340e0590444420812194100d00310451640c070565110740104c003540c425003054402000c5400d10208201030480c00481f404c1c0d101c0f024080c50030300d45110304c80b103000b801c40c3d26102c1482c0c0300698840c100b076901c5840b18181c9641542445800c0b0503449010081d45003400c0d030080c810b150600d4003035203615a5038019441001041c1103084003201c4200030b0079000303201d800240d502c0ca0900e600c2010184d010070010500d190b003482c00020b12001c0e02d10030001101d4040c0d032641d080508580d64a000110040c02c0c10703070030744400e201810200b03200b040208a0345108502c0054130ba864003440d24250f9000501c81c5209070040d20a611a0741c4022030000d40c409840d25154142c5011041c1c01c0405800140002e01941e060040204404101030010b001400c0340351203840252008410494214803142802c0381040091107401a10040c0d40c4c01864005104000140c14a000c505000d458403809912240005441c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 236306079 1250 236304829 236304839
    0x90f09021905030a06020706090b101502070807090b01110105010b1201150f1b051006030c0b07030f180302130605010809010c020303010e07021207050c130605030c0d0314070606 78
    0x74407090700e0303902280d15204550300d420300280d110708412070094103c0c1d80020380d407030801c50154882100140c0c4245040d400f0f062040480700d289285000b404801300740749042030f000600009011086500c0f000c0240800b40c1012540005000b60381141c0341884200c2e08107240e0904203000341c0b0b018000c1c0710005501d800007041c4c03044103280181d1040c00000781d09149482165402100c034004840c007810300055107910303c1d4001c54517003800f43c0003402034000d0f030000f01c10701003d070f4110f00308603805000400348140c1c559240c070100340708058004020619886514030318500520400c011906881d01e142001030344c075008180c4e03a90104c010081c4481d600c0e4014801c0f903030030071181508000d161008108081191a029503644010700541c11034000c100009039869100304810b52040c264089a9900c42a080c9421592a144076103803622849403000040c03460266849000704488004008121b107840c84018404400b02511041d402c10504480540c00541c1000061008070702ca5040020010b00d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 236307329 1250 236306079 236306089
    0x140c030c0f01050a0309051603050a0b1e0a050907050d060c08010608060a14240304050c010513060e01020f16030b0f060603040201050d1b030e0d02060c0d1104090f0902 74
    0x800406104801c54035508585907844000d8416192150600140701c0d940d03410300c1480c05240c0c4031543d081d5084000084100030300801d03401c250705d10070044500151905806034480c2403000c0c40320040044000c0000e411440c0c29088079400540c0403058928158540300070541032040044240c484603100d1210100203030340590454010a8a131034044800d0800d0380008270300035024407890b04041c11840140d05030f65140c50840d40f002e800b01820700402c03651240e40340520381084900703946038082c124089000e0350117a01110300d40259544c08a18003400d160060b0340001103254044d0442c8038042402c0c8101004011029160141880d04015989540350690840e00000c3c16543c1000d04441072182944964055031380142d424200161a0159094842c0c01400d100c03c0001d6030f0266400c4c01e8880e40d826910810640341d040040d14148407046506981c0c40e0416900088004400c200c4020700110f50f03070141075080f290050540c070302591a200300c0302f5500d10801f80f042c0b180d07440707a06000718038003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 236308579 1250 236307329 236307343
    0x5031f0617070206071b02040b130b12010e1e0a0506010305030d110f0906090d0804030b07120c021b01050f19020c0a03050303130c090f2004050901050f010309140c03 73
    0xe920060440703160021000302501c0c46c0b43c034840d606950741140481156180d4001d4a140e0340c024141d03801490151420390702501a1483c0103003d4458a0201002004103004007080b0340102001030010b640c0c4000da00c05100240b240c840d9441c0140d01c05040041c10500829008502400040d40c0314104691076104540c46441c548450308030803c62030312084080700a96041c40b4088601540b1001c4820120f043c076200f0910062901000181c048100008058040c1c020071103980c4d00f0001262810180084980300820f030405030740b00c1c030507020300f0401000080c2c0c4500381c10f140c8641840c030150807400036a000021200207025a4500c4050344582c10480d42113140300440b0084402c03071079601c5a946900c03010b080381800110814041c1c040c4180d8419200040c186003804110740317001c11003031000800c4051810728041d544000301d40c500c07049580507a001c2c0d0f40010501c3d07803141d203403804105200c070880a100e8145a01e400d501030214a50311f100020901206c0040d20085c05440c041609040c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 236309829 1250 236308579 236308591
    0x50103180c14060c2a040e10090302071a0703020606060a050306121c0201090b0606040501090b0c01180302030726040905090a08030f010e060910180605090106051b030301030b0705031f0617 83
    0x12400c030744c000d040c0500007078140008088e103c0001d4116501e040c120b08100c8641c000000400c0101e1004000e841c2000007044554001d85c240e640300d45445080001c07074481c95142400080060004c10075524241c140e66894180381b1080302c4c0e100080801e000c200140c072508602c0075075944d0410105014104801341d50148040f01c0640c40c060401c1c0018014030f0040c0a2034948004c0440d18200c00b1b902548844000f1550503c8405413421030b1030002d607a580549030455840d00550001d507039031014030072038890056401d1659410103040c2440b2000904008000688901c00e0416620225900030700550040c4c00980a0505940c140f011280200402510aa008640c0394007000084000e01d8550000d50340101c10204008241c0c105203405011660429036010b1104000010003c0e04000104003075610507505800350304807404403640b280000d11014100b540c100000825042c85080116401064084510030791400919103901055079034000c04003290090000038810021845501d40c014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 236311079 1250 236309829 236309831
    0x3100204030b0c03070e0a031202100c021c05070f06061d090601091109130608070f08250b030106050304021e10050307170c0301050103180c14060c2a04 67
    0x186199a440010701c0000c0c0203600300da03c08004504854070444039031a0001c80200f0a419880e201c0c2401c0ca004090181a940948140781032002d0f400100d0182800c500525000f074103880351035000c0c144464425035040ba040240402c060000070380b0488115001d24000d09000070b496060100d560441901d01151081c7d204603c410400c1e890b0700000d8140c1510071220001c0b800c4082e184030111503001d02c2c03490552103255260300c045000c207582d000d0000c0350700c840c0031681b00341e558200c10b2030b081e02f00c1d009180c440d4004040409042008581d038240c05e80390102c10080309a500ca2003014290400c0e00020001000002840190f240106072007890b201294262034522000c10002460f8868100c00d0300c090007004400105000e002c1e200c04003172140e002502035650302e0405080403040d4000d02600e0302103451b068034003c00c0000e20388640803035940010869809410080ea80d000c0782d03098480d00741c1c003920420000f00d2800702841b0412030301204001181c07030401e415010036800388000000902072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 236312329 1250 236311079 236311087
    0x3030f150d08030a0609111917060f0d02130509011820010c02060a0306051e060d050a0209030109050703052112060418061a060a020d030b03010b100f0206070305010501120e100c0905031002 83
    0x1502440e03180c0c2c22010444080bc081000c80700860107844100e000130354050302d5008107403010b90300c6401071407080f442403000704203030343c132010125642103400000130304078921040307040000c01d000181c1c01c001400141010005400f081d40000c22039405100c5620000e0b48440e0100028204203020812614440c103036001811244808500507004008286246c10748880101d040768180c1e90454500b42c0d000740c000d00c4010703400d09215070f0b50b01080c841200e203841000b01590020299241341545d13680c0269400b46081000100a0304407100908080d620035626440800d441150f41080381d0460700c17a20000c41c3c40300ac000c2511000600000310341c0d0140c034041210341b001c00e03804101a82d91808906001a14200c4a40030a0040c14280311070703034116011030740b50411030b90026000d82e14014182c1c00c50384540d4a2420071400ea40c0700b03118860200e030580300c0c60100c4c10010f4000300c007403442d00d4089440d181d00180400054030f60400d40040803039040707402480103003014040c407401060a602c040d850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 236313579 1250 236312329 236312357
    0x4141c050702040b04090c090209181e090c040501030c0806070207080303010501030f0f0c09030b070e09010302060a05371403070c021302040803030f150d08030a06091119 75
    0x341c8164100248250307500c1c2c04621059030350b82e000b00319040d008100306080f01d84680318080290301c100c0303d40e413082405c4070b007200649400400e56445030003070142d16504626212824544050060408283c0f4001e26584c0845074482d449082d0003180500b14000b141e43c94401c14504002018000ca01150002c0604ac04818000000c90b41100e0082c40c000800030140400c0e68000d05000d24101419070401d070401280c80d5200c0313406025a4007440c1044030a888103c0161050b10080304072541040007100100301610303145000e0400c051160420524040b0000380c66035404102204865042048100440b046e000810041c01001400d0600c3c184400a001355031181d0301000780104d042103a9021a0030454950706462185040c1e00030043d07446540358103071941c40e50011680c80c807003501c0c1c080c0003071030f2030450180f01640404041e003814624245526100b031079920042c0b000c1019500d074040029002030a1190181c400c0b10100384a88808941408040c0c81070000da5200c1000184e4100c40d034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 236314829 1250 236313579 236313587
    0x30c0306051206070806030703080d0501030605180d0c02010c1b171609090c0e0114010e09130f060b030703080c06011502030409150506030c09120d0219051504141c 72
    0x13400034080e050241d00f550701c08000030300d418507582000700b24200110300300c2c48000b0560040d5043e64030500c014040c03980c0d144d03908005003038400e10814007588031485619020f4001d40380350140f540185006004801142c17100624010846045c2d40c2070382800908006803d00601c640f0800d090740c1d4007030200e6540502440200e0f00b40d90040001c0282e0350448101001380e001e0350038008168841c0607105569540c0c42040c2c0000102c6100b9010a070050080c04062270803103242403040c0501c0b210800c0018590715846c414041000045800580da506414030385e680030080d102c0290712600c1d940d07a44a418011185c1231010690020b1046000e100c00b0010300da07004401d03601640c60035400011501c103070481c075254a903547c0d40074540108001003406a50034440c0c0c000c004824041d80e581080c2d800e030001085d03580c00d031a010343c0b0061b00100d4400c54018a1503521917960f0740903d048400040210038159485001941d08544100500707060011a80050150058074115158000c58880c0d905402034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 236316079 1250 236314829 236314831
    0x1203070c0b0910090b010e100f031112010f0e010b27070519030507020c0109050a171e0307121706060307051612030e010614121c030c0306051206 64
    0x20300d036070307000c5001030b074040b00403c03006070190040c007028084650181071402a80c40c0a00440518000a400155404010310000000c4403a1003144406643c0365460305c980e503000b034820050f0310940d13013020803001d003100340602d18201040340d10014400c4071584602d4210f034011400700340600d0034080c1080300d03280c0941c3d6081c0b02c803810026030b503603940c0d81000c112043e00c03880b000c1080340c82d5035654a03042140e040c1c0c05180324804030b0302107551380c420040055442c0c424511a80f64041e070305000c144008200d411703220401c0d441500403181d00c0d1101c1c45400391030b01c203416040c402c82c0d4000b0035a48144000c107261330b803915200c0c0c145400c001e4403031b9140c0d04180c000100324502566001002c00e4030b00d840307401104c0c25448586904c8031207020500e0304401c0e140c2c0444100000030f04140d100d121002c018818502251907942004545420140030b102c50341c43c00540e031071042c0c0500c02c0c01c51242030702d468100031084120303a00001e10800000010b001c136031043d00214082c079103c440d51410008001406 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 236317329 1250 236316079 236316083
    0x1051810030803092b0e03031201170102090a08010b150301030308042012060a050702030405090402040905030906040e0108100b130528050f13050a03050f0405061b1203070c 76
    0x290383d980d110000d00740340c00041403900a0301245198601140d0941710503400a1241d01d40e40c00310800680001c03d941e0340a0f081d00a4180764000f401041a0343c0760440070034000b02200c0000d03051915200004415a0080d8401d4481c0e9450f500d243d80c440c0360003096040000100c42c4024250350541d18010020880200010f00384002d20024000c9070a92803520002000010040503203071014008054a9907000d03505140c03480d04050120f000c040c00401900c064900191424a00390f8681d0208405004003502c1078589010420120020751120720041001d00000303040d9051a5140c02c2529203444180840d12086034504045e402d401d981d0300d52000c0900748101000704142c0c450754402e10545094082d21100201d140c0c2101c4510b640541125108200802104146989101c84614040c50b00d450042103a040340e00c035480004d001d06d000d0a06034800c02d41071800d0546402c0410100e903c0341c0010008a4450b120b081c0c1d040c1c2e0100411258865240c184a0550603d0309002c0c0a00e1445100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 236318579 1250 236317329 236317343
    0xe090a0312020f070b090a0b060a060e130e1c14030c04030b0a0b030304120b011a0f0c0f101a0409150b120d030b031902010c030503150a080102030105181003 69
    0x100219049141c2913420207504000340e00c006040504900d692500312038001c480c600c2e2614002a000e00e40a02031508480003034131001a4400028100400801240092400342c0d5503031402d040c0314007041010b00d00800e84105641050304480758041c101104c504002482c0e580104104000410003200350f400301e90f404100d41056881e4091300b03202401910060319011301c808900040c0d1304440040c600381d00d034002c05401c1c503243d0b02e451101d54804c4102d1118003c40008100c8078452603020703801850350405043c155a2103030146000e581c184680c42c0300c6000e0942d110000141c42220174191004503400443d0100100720302d035601c08001e203504d4411441d2103980e4140d004840e44403120042c3c4210084016034100c3c40c05082e010f001032a4048845001c1c0c46075024000e00d904054020040d0a50141c440680b80d41036070b542241c03203a20003000c1c02e0300c031080b5688903c0941c4070b6250141c05401c4900015850758144400d01c8001c070180e094401b2111109014840780d000320700e002806980d0030000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 236319829 1250 236318579 236318587
    0x905070219050d050a020a0203160f0f0b0316051605031b03190e03010e0105040b0906071407080a0306080316060e010b0f0904060b12060106090e06031b19030c0e090a031202 76
    0xc080e407c01c80c1032440607406000b00700c0084c0920041d86221401d0700c464100b640c2c049030b140d07142d0380216141030060788078800d010804101d14411185048101651074070f00301e0315018202c40084440100200101d5585c2e00c049012240c0040c01400d030804031401500030340c1401d0381d1000e000b054980300c0041006210510703904862a403802c1d004140c401030b00c00024070442c100341c03400d00c5075154101e5000400b406010f010599861091024810301446400064103000311516262607503070103d1801024142d4640c40000c8810091000c0c0c83d07400d003400310100e81c4c1215400c00e601984d401c211442616454141e03880c901d41e03140226000d00800540b07c0a81543d154603011003b0152500c400354010084448102281c90002d81c2c6030584030f1795a5481d0783d083e510243c2c10710141d429946141c0c950000c40084034030b010514000d4102c060001c180e103500c03d01d20401515540042d401c00e0310f4190342c101062094400c0c83d42c00c41d17000303068840100494540c07603d0050201d0200d41c030002d5002e40001e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 236321079 1250 236319829 236319847
    0xc090405100e1e0607090b030a0207021309020a050f060703050705010f021603180e040212151303181a0c0705060d0e01050a150612020c01060905070219050d05 70
    0x4800c4401804691041000156000902d60343d09440140d02c2c0354941c0c0881403a0740c0d1480410720500820385078944a103001e00b400900819600024841e100603542403140c40056551000307080035155800c480000c01501500610005020b20380107240211910201220fa544a0008a5040c5501407802c03649031016860040d01401c110f4207c0034600707001088034122441c400c510468283e119417a070085924030150761444000503403040070070ba11083c80000c0c026090222070380030003400b440280c40f0341d10000c141d03030720301d1403020749001c099032820020060401d600b0022488081c4201d2a01d09174040c500010141400034084074001c0418010515051104c0704100440280c140204100d440e005001c80701d1004001501c00c60700300358280004294070801c20b00c01d51100506c10079034014802e0901d0b106030b40740300034800c40c4c0544607030800000040b02e030b081c81104068480c030b500c0402d1908200380c00a00d4100c0f45002e000c4903409000101c400180c0003c2e075801d0080403030800e152126031032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 236322329 1250 236321079 236321083
    0x1020d0e04060905010b0310090c020304030f29011802091e010c05030705030d06051e10020a0b0108100c2105060621010503190807081b1c0f050c0c090405 68
    0x40d0f4008141503080400229600c0044000b640c85070501012610020350349840800540341c0f034140740000750300100b00500104d0a0b010080d00c0c0c80c1d0203110103499002c0c800b42640d00d410070280e10198070651050060289400300c040040a40e500c0480550030600c1d00d40c00030b9000d250344809031040030407198604172a44d014208020407190040143d0f610b412090400780e4a03544150303c03540015140020108491404520360a07113491a051014035105c3e144042c08461700150180340c0a5209904200c1e0004109103101d034040d14207140a000190081c090b5a401d40b10314111800901c280110410f600480c4c00321052022445110085001c0e11a507001c11600d20400c00c0c9151010081d26100b207070014040c1c0403a048401c20340440e041514000101c496a403184500181884020030245001c100e40c00090651503000c8004080308100420b08545400c03241d0113498145894101219209500200081c8071038610b410424a0000b010420a80b15240035180c50311500307070940890184001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 236323579 1250 236322329 236322341
    0xb0c060a1505092d01080105060307050103060602060412020c04020a09091104030b15060403120e030d0806060414190303121103040f0834050f030408031e0d051306051501020d0e04 79
    0x4d0201240300c51350711421990301178541110703041d000c1e12806d0310000391548203104070070481d449a4080e042c16180c950341e081da04603444040c08214032852050702c0c01c994840c4010007031600240c4500c003280c4e02d00083c03071041e90403841110290010600040011400c8803a00941c804d41680e0041c0c5074841c403a002941500a940010f0200640c0301542100c040e080422610442e5045040b1003002180880c101c6141d1811500c8540004050104116440c284003140d41c040c0c40083c04c092203070030150805100c421590b401540060020707034000d00591783c0c52042491000720003c140e465071419456100081e505106c4c01000c001000812540d0301210041c4441c01105d62020490065240403a040c0250704c0000e0075a0203005040103025282000000c4a08031080c07240a5801c1ca0502118074181c8806081d5003c403030041040080150f0744e00d031285c2880b60721050540c0424228500748030b0210f4500810382d8094000040c0c1244003680c00140440c2d61001900c1e107558001c8a101c0030070083d00e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 236324829 1250 236323579 236323651
    0xa0c0c030b0a0e060105130b01140a0201050f101d04080d0e0f010b04180210020f0106091b1b0204110c06040b07020d02030301030b040b040c0b0c060a150509 69
    0x1400011080051603914a405500301d40c2e803c1c0091241c8400c07064448500b17100d4150b128060746031080001c5141d0b040005441d20505003000c03003800280300c1c07104076880651200d0041c1d5503007080040c040034216080750018500c0c0900d040c460b00f08009420006640750122440030421400142040150811581c808103036042c280300703803401340020307035507604e0400000c4016500301140004c850410344509000043c407040760703501c0700541d50284440f21000300d41180450080035400d00c0345810074060b0400412178443c1c00119203110311040c20120008000007010001c03080c0c540d0003214451010071800e13580440340042d10444058601400380301d20300d140d44143c0619420031080c000c6142109105209507000d481803d00c5601c000c030b89074032003404014680c100c00d40118021546540c109071740140f10b8511040b0740380d00c40840c0d8103c1e0700a6070410119500660402c440b030000340c01070450403402040b00035a52810b100010342c0314807000340400002c4601d8800514a00d03200010004005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 236326079 1250 236324829 236324843
    0x31704050304050105251203050c180409050102040b070818101d12101e110706050a11160212010501150305040206040f0b07030e1507060911221b080c0a0c 68
    0x40c1da40307000540b556801d10782c07c0100341f40a0004048200510803900d04902030741d07c01c490180c01104020042440c000c003078681d90b40c280300201c1d801041500401ca40380c0180d201c15294003201500c4114115000c1e0071070b0041d0001ca078030310b66480c1c0003a45070082800403012001e8045005c404240c0d0181d103000345403807601c80c15000c20180c0071260f00040c2000480005440301c00e005030220f80a80b510613144810502c003c0190301c012602d0355008079001044020301040104c04903103801c0050b0821004425a003924000703030310440c80c0c101d04031030150540c90001c3c0021b6142441d0031a031201c01252810034142c9950000342150f8034081160050b04001000c0f0720301a0f03c525048440e034011210480201e020300c4001001031800d103510b079100000c40c2d0422807405c5503666400e00540b800c610101c035408020240c0209603600c00b0400d081e40d03481c21104c2c4202c280c601c0e040388113860b03469403e6492410200c880f0000e440c3d2101c081603101100740d07a4142c0c0d444200744102c80e07d80c20407030702428103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 236327329 1250 236326079 236326147
    0x2031308031303140f0405130f02030c04050907032a120c020f06070e0a050618040606080a1503053412030905040b0901030215090301020c0a031704050304050105 71
    0x580c03490201020540e029544610602c01300c10181d83d083c2c03041c800b049203840c070300784402c002904d0442c0d100c1d001100c0b0404003040d0348071010f031407600b42d030003d42d12030322001004a000c2c041030420045055104485250601005000825015907510150041e2a0384031500d5101400301d80543e0388000c005620200400004025a2000751101c0071900b091034240607070008035039441d01c54804410300c82e00040800355080e01e40810844141c1c000180c1c5030700382c4002c000300a0345686a02ca440e0007445151240c072451300c0c0c85964481194410302e05284a49180345081c0040703000060400c4480c002011400c1e0340b92000001c0e0102e185100079182a215892100800d481500352800328600e4401e0711400060354854003000259010008460382003e9035500410251510740408086c0e0030794079010038540351055002c242a81e02c906c2d41503001e5404181c006c000c0603031220052030f980111001002030b5082c140e449076101c0c411407203454108a008103005507403a5051410b0355000c034011f9101608 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 236328579 1250 236327329 236327341
    0xf030a0c0e01020a0b071809020703030603020103060501090f05100e03071707050109080c2b0b0414032b18030c03020d1803080c070e01030c180b06030601030203130803 74
    0x90940210000002410481141c0940d400041c01e001019400038030305501d03581385042122005220000c03d0540340c1f00801c0010755842030300c001c2c14068040d96000c102c59007180005001e44086900043c1007000c002c90030041c0f10a000300c143d041d10313412201074075100322800040703841e20304400c46150f250050789000540d00d4140100c43c0007140c0c103d01540c0b080d954503401519074000c07520800740e4507007040c11070b542c140ca028101240380801010809050090b44c440780640c625202c50b048031701070b00c00010700080c8203134039024407000b0a900e170066150502903622205d4404408851080441c400c0007680c4a4407400d40000107042d94141d00c481c2d03030b41043d04004081b054020401e5015003c4d0342c041034116072140c1e40807800f005040d0101c000d21851640ca01c00ea41e07004514000c3c8901401c007011034407080035a44103008600950b0550599401c0880701110000c140c00c00064040c500521049941c6480303050340d030301001c01d080050f01e039a941c0500300c14000c4a0300c8000c107404400410050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 236329829 1250 236328579 236328581
    0xa0e0403030b060a0906180305060705090a090c0e010503070309021306150206041212020c010203010f080d020703050604030e031903020d0f03051b21010801020a030b030606091504020f030a 83
    0x48214025035090124425000521095100e40c5034200d0000f950380106000490040388000801d00356448144800d9650b40c8846081860075202c0d080007600004101440d07162824000000d0885031004100a0200c0a00034101c0060005240d041c07050110000e10128002e0348039200c160b401410414404810f6207888000344881d000e90820780006014a04074244001051071060358401070325010100c9590040c3c4540f493305c0300541c4202d8080200740c1d000502030003d94007e00ca076104072080d2a08108400d402d20705184204000c65000443c1000807400004e2082d4209400d81070444d0400440404641800c0c0f0381d40100c0034036039503642041c0400d54006620409090117507110384a80f0142c0804505070303002a43c080907612844000d00408404140082003e0b41900c0150707040015003010190750b05100340c1c000d10301cbc0d07580400c501821540500ae148010319045015010a01d00301000544c642001380400a043c0107442600c00e20b511558101d40c1c1e40004480f0194032854075800c650 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 236330935 1106 236329829 236329831
    0x2041113170a06090c0e0105061305130207050a0c03352206050903060a020301080d030f0e1f1a01020a1101030912030203040b010f05030c0409020604050a0e 69
    0xf1014814001c160348202400d0314003d10b40b001c04111580141c3c01070380655000c100040744094025072000950b00103c1b10001f070a0480250300c00240a4100020264864081501c00b0300c40c5409110044920a014007180e80440c034800c0f1500c844405d1000100c2d201d011040513400b40c01801070544c4500100303d500d50b03200e00351034000c05408039a01c4440070440000da0f99100341800d00140358489031f040400d51030b65140c4030415644d0303d041c0600c0e008056480071000582000e64200541c444101422141e110071541c02c0402541190503901501c0f61500f01c4050b910715400c021015000c1058001d0002240240c44103050243c0c5142c3c014101b5a80c0c0c000400064041141284e02c41c000c0e0364010707160b02d02440c1c0185d120300b041c2c01c40031081400186c204610341d000540c8040702c42c07042d00d0125500da6244046041400760760001c0b44d01107d00034001c02d00c0740034241c0071 = true := by decide +kernel

theorem cover : BRFrame.Cov 236151079 236330935 := by
  have h0 := BRFrame.cov_init 236151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 236151079 ≤ n) (h2 : n < 236330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
