-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:25:56.447781+00:00
-- url     : https://prove2.me/submissions/c6f3e3aa-f59e-4ba0-a562-d71f292d9c03

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 4676266 ≤ n < 4856122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 4677516 1250 4676266 4676297
    0xf020a061d030106080601030305030405031201030c0905060306060a03080315040f0b010810031a0604180501052d0105060a020a020603010906081501062003191709060601050a050a0909060305030307 87
    0x1300000c40700301c84018041a440c50f2020366440c1d00241c03003680d1900041058035110400390550600035480384822928042c9480a40c07803c880b00900ba01d84242c1208052020954801c4000010345e900329241e40d84d2504c9980500710200ca14808041e00141040c02d4800e408800750300140c1c2e20740782038032002c43c180d0b03482e452041444564000201040c0b8404c00c01e4001009102d9482e612040203000060307400c0703403070110519007020b00d442151140e45401c10070030242c00c010711001400140700030029100100e1082c0518505050150703d01884001ca4100d200c11b100f0440803c085801070030b0290345c2c0d610b0380014405000580281162449140032a2005030444509903040f07510f01e40d10b4000c5113040134000e00e01ca4490720b0140c0307510f01c0140300385060119804c90010313002c0315503264000841e21041513509940001410244550811420002566009011244001c2492500c41d17542c050191041e20f200a0940051140a1501001104000001000354080c0354140c0711007180010095 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 4678766 1250 4677516 4677521
    0x901020309060703090c030b01092003060105120a0228081303050301120c050907030c0201180c030f06020408011401080f0a02010905060903030d021321020906010c0f020a061d0301 79
    0x950841c096480080052040e9209034066460305100388414082da5969403101040ca2030281c1049550b540d8071072014110090100c003048000d003000d1001811854114000381c20340c0152103c0002c880600c40004044e01015811505a9049032441c04001d8128400c0e1245a90440201c04041400c450100e4903d1500b2a083c1178850341c580d03500f52841e800e280d4800d42481d042101200d40403202d98021625568034168a40325908990b0001140c00200d840207003542c000b4a0080301a10f21042e030080484c0e0900c0803801666049800201d80d0001d500e0035400074400c0341d0001155502c5c0510610004803464500d81c1250b07850350072a1000040d151140d40c0f1200b00e01c40c0240400c60241c230800c100e0514070040c2030903c20040541341080d401001e40026170780588030501c0079002000f0f0a11503002c00824450300405a8000c0d90100411070380400c0b0344002c090204c2c0e041c41030400c8a04200515800d070703001100d42c098240001c3c0c0d076450b080a00803407010841c6020600c10400d40b4205e0b8181403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 4680016 1250 4678766 4678771
    0x1109120111030112060b0301050403030b0109050d0203100203071202070302030a030605010314010e07021603050705010906020607020c0d02040e03210901020a050301030602090105040503070e010806010f060203030402010f0320070b09010203 105
    0x1d20300900c2e42e40b030a222400078030b24030745040303d8580d140c000c0c0d024280d03020f100f0365110b00e001c4d0b2404a04000a6400100710210a4004501c01c01c408000301d4096100001c41c94560146440c0c0107075aa100d01c17505480100400d070308102c003076000181c001e0406501002600624420782c80902c10305d46c9810066058441c0001c03c10244a07038039004100c100f6100c41c1054101c0514015212000c408035a1205241d0041c1c0040d149648080c0c0104047d592000340c10009251510150105042c960002034441203580e101c3d07442110295101401d56032146c0c042ca00c90301a9200700c2e0b581c1d0188003501e41104c0c40300040241d503400c0c80000103c0c0c0c008180200c5050091941c0d84500d035a0070b55840000940004002034100703c3c090002003907907201006080c001d0103000140c06034030340c50101a1031604505801661440141c0c040c1040072540000940ea000340d42400e211303001c04080c50013107004050b40c0c40300c42000041c03612501d48001f032200040c00c01c64040c94929084d5038502c02000d0a1b031000b0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 4681266 1250 4680016 4680041
    0x402030112060f060f0b1908090a030e0102030d0504060e060601030c020d080a060302060403050304090c0203070f080a020a0606060c0317090a02010c0501090f0303052d060d06060911091201 83
    0x408501c0c0300203200d580c00004003000d0740f0000144140c907900051500c0300030f500800068500083c02d85000034800440001d01c000c1440e100900b80343c40f1041270380341d01803400000c041c03058070020f03c80140c0c020300039a5290303150342404012910b01410048041c248400012419000d21000f01c0c20651090141300210f2402d9001008007054104089443e020001c018855030342e640c24000c0f0050351881d0041c00294014070040d40c0ba5404c1011040885510011540540d4000c00c458000a20320040000340700e40c10040c4d0a488403104c14060742000d4440c200148460300d000c0300850b40710b801003036009a4030700a43d00c0c0c100711030f1141a0b01c55896800c3e01c2d0f880503584031044000040d84149100300e82c0500c03807400800c00b90701036a180e50b20901c0c014021002b2986480401a140345644598442c43c1d41c031046480000c0302036003c90300b454070080c20190184410090031410b10032250048402020700e68810014585102e030074043e00c0d004104414402c90150020400d42001409400f40e007100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 4682516 1250 4681266 4681289
    0x20f191707050a0e0609030a06050f07030213060c0303020705010606020f0c03070e0a0b0307030b010303020105040b0609060901090e01060e040f03020106060f02100b01030b03031201140102031204020d050c0a09060303080604020301 101
    0x101d03c000d9036058140308299a01003010420214140c034244002c0383d10320700c80c510100f0941403d00b06e640c0c060781c00804500c10548140003080421400720f50041c201d4942e410012018050380c10110042d00c66081c01070841c2d800c1100004940b540080c0f000c40c01407000060701c220140130010507845d003801c0d12568080d10a0703040425104c00e800e03440b107160100f000b0100c0c3c441c07907901d0303031140550302e4240e10540250350b5502c100424070039000b2a4a5104004581c170a485103410000a40021418040d00308123340d0b074400c04405400942c40300c005448200300d406503d162900e00040c0f101044c010840c015400c3c41c0002074024010300e600c003042c1c2000c0d0043d1003887c1c1c6661040009058450741541050340b280c84400013924140014007500c2a031400c9010395604100b042581c2c0741a41d410141154010854041c80810402d01aa001541100c107445000c0071400c00d1494a1a0b000e031050b845182c00c40000f5001203aa4080c404072886070f256151540d58800402089020901c101c1d2a00c18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 4683766 1250 4682516 4682527
    0x50601050a090e06030a17030f07030605060712030b03010207052404031407030c08030c09010906020304060504090509030702030d050a0306050f010c0201050714010501150801050d0804050d0303020f19170705 91
    0x616000049034001300140c121a820710190b21401d0400c0c841c400841e4012a000050201203207111003181d501551609041c051685840f0104500e8455520042c180a684002d15280325100340c0140000000040003503442d0304007414617544603540101781c08069401c500c2411840b20100300000c0c0300d15010340f60704c00c02c001c40c2c0705c9030003144d07000000407020484030032910000500ea900c00355001d00c91a40d9016240d02c172034000900329190513040f0703406542c400d000400800f507111003100c0503904416070201d455144d5013000341c40d42c0103440c4003c2d410b005414080850992000141c0724401d203d5a040c0b0140d40c3d60418008032416a040c010300188a0500c03c20140d40500c000b0a081445201c40d824a03291514005085900c2078110101000c2d80c2031081030007990046529000d001f040f04c441e84248400d0f9148801d41c82107106684c05612580c500c0021f040c0241d068403490401481c801c0d13501c900e42d45881307903100710301400d29000c55a0207080000d4140390a00f007900c6041c25496461416 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 4685016 1250 4683766 4683779
    0xd0204051804020d1401020702060301140108060307150e0d020d0f02130e0a0602090d0c030b060112021c111303060213080a05060a020d0e0307050106030c051203070305070f0206030f060301050601050a09 89
    0x4138402c524031170441d9002c2180f140180c440000450080c844070103c0103208038403000042c801c2201920b11846640074150a03c500c0000c94101540030500341072000011080e0710102e00d10000c0c48201035403043c0d690303c1070428051004903c0d07080610072914002d22000c2c0d15220320845006094010300b80e030080200c040040c1ca10f900405040c5c0c070040400e440709009650f010010300e080d420448041d4031b518144040c40d40c00440f0a004504008425401d00a100070b0010a140c2000750b103407000703030301d1740c5016024041d9001114205c01148107146401e80d140d080003006940880c0f80e00302d18a021000010301e01c0380c042880c103090f680c00790141c40682c480720242000b0350444600d007241380390344200d50140e40e181000140300c0b4a20600020968510b907040164506d0740c00c0d40606e000304c13401400c5040014012045400040e8141044c035280c0c3c54074203102e01403d007079410094100d130f000024001e00303260103103c0034030510b0210000c0c81315640b00c0c40116580e024003a00807011440303403141172258 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 4686266 1250 4685016 4685033
    0xd05090103020a052a0d020106030f0215040b0a080103050d03020304050307020d050102090a06020c09010503060105010903030804051606030b040b0609060405040203090307021804060b150d050702010605060d0204051804020d 98
    0x82040389032131401c0100728846100c80b40300c01c0459503054039030741507406071041c0280010b44400d04140000c100b62481d6840b01d446d0f07548009030080c4505201030402002600880c1550060402d0400c0543c84080c599809009101c2c2800155103d02c40c440c0c030100a0b40c824000c50b80700d2984500031b5810034040d030742070006a041c810403c5500755020312141d03a0503114a9020801040c540e40108503084104007032100b101010f802c480d020380c10040040c8200c0c0d03004601c1c0c40c102c80d0b05180034501c40d6644e0508074100103203c0706c03903080c846010a0019046a058000c005240002c03141080100341040c1008018171540c0c16140e040310080c0020040c43c600740d80a154080f5108003940d240c00340aa0005203890041450010070300b80d06002e0009200c564890b00a801c40c2c213490704190400a00482c032464001c43c200031403c0d036214000a10303600d10079002040284005045a5258800c43c003410f00030390801d01880b800b4100300c0144044e20080c3d500e203c0e02464011f420291240750070f4488509 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 4687516 1250 4686266 4686277
    0x40312290109080f03040906050f0108070804050a050d090602010c08060306011202010c0203060703020304050708030307050306040f14010902033304020a0c08070b010302090702060402030c040507020a061505010e01020d0509010302 101
    0x18809151030005890f1418000703116010003600282da6100d0516004004691068128a000c0d01c0c01d0441e03075115981100760035400c0559814216625540c500d843c0d45040036901c40249240100390004174000e80100c1c41c02d003500ea107074001340424006c4100c11910090200c850b1540369108070300400a95002c0e01410360385034010302d84046614600d0f00482d2800e0020349018001a600200300014401c1c00d12070b41015088000245181d0f0410600c0201070340400303010395105d940d540070002c580d4480d41d80001c0c1c140181400c100001d69440060000a40040f5003469490200e03c6044064105a00c0e40780840c107500109040328120001c00e010080d0480c0390003d00388042034a140c0041030700900502005486001600b15940c19441885034030354010344682d007994010801e0000580d400726100300686410343c2c2c0001c442c2d90b0040120700d4100d011070301514161412144590f02d203c2d692100301540c1082c1c0b9808800c4031040d00481c1d551074650b40503400984140145400c640c030a400408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 4688766 1250 4687516 4687519
    0x603030f1b120201060801110403050708061e06040207141b04110708030702010605031207030306050a060c02040902010203190206011a09030706030e0106090e0109020a0f080709020309010e060103050604031229 92
    0xa409501c46e40680c1c01c486041914400031280807404000f04881089000058400b000141039039080c400c01102102d5440c18000c0c12103803442e40001d81e182c407907078141c0c3e080c20b4014400458090801c6100e030b4032403d00d11880100442c6500c1e00300440d0415000d080a000075462a0b82c0c42c21440e03881d0b0303200e5504040c00400465490380380c0040c2c00d81d02084614000c42071041103a50300d81c001d1901400721030741d07940918050b58034a81c0401445030004108010903070107a80200d021030091004074152702c10801e44040708400c00c2c2c1c684030110388c005820341c141d036042007140c035070b4040051031581ca82c000d100d18203038036501524052008078460303081074074541c85801c000314106840b80e0012007a503100884405042c0c0d913406045056140000c003000052030010020101c2a0500c80b1240d06d41c017140c01003240f03c03500040481d41200c000d600c40081d080c00f07070069a03250358480c9000c2c0d4880c0c078181c90581c00030351248405030f0200500d10969103030840c0800901601c1083c0c610440c010989203030f419 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 4690016 1250 4688766 4688771
    0x20301050f150d05090d12050f010506090a030b010b0706060b040b03190b060a030221040c0501050705070f03061506020c060415050702030601080c0a1706070c080d0903030603030f1b120201 83
    0x61000c0702060061038000d00c5c540000d44141104000000c090400c07202420444030b086c0b009124083d00b601c1c4400b81034400507100741d44c0d56400c3d003010a81206081d03100411410000c400010391103100c0c009480f507144100e0303050000e176640704600f20244c011402202610802000456542414082d51141c80340d0a44400b00311000e510f400145140c0001c0c8040e03011035000155920388039005203041040111440103011281441e80318200c4145140c02070a0500c4030005080d0244201000140010000c02c0307802e00442d500c0c4e1809a003c0c02c41140b243c508a940e03844081800d030300100f00000d440002501c040d091514000c039200c00121800e1014040c030400308080001360705c041c00418083c0103580014400341800301d0900004a045a03c1031180c5183d421741c0419030310003c500c40c0d030014210310b003c2803c4030f400c3c140074240d4801d20300302611151900b2a200d08058045d005031040740e00030340320000c9042c8a8001a150319030320040702c01803106040248000104410000d0540c50341a1000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 4691266 1250 4690016 4690027
    0x3050c040e1c0507030807020a050a080a14040f0801050c04030308150105040806070305010512030a080115030b03070e0a1103060d0605040611040e060307080a030215153001020301050f15 82
    0xc141021242e003148000042d80010300c0018103811040d22a00503c0ca0310050071071000e00d4440742e0721408094002818072800103204900782d13210f0500748585944e98070016a44954580082c10406482c0c8500d90182d42404c0000c3c5424018406981c11250951117188240d524010800e944140c0c441449040c000c061101050300c0c00204103441c0b055409480002d1254140010096800c48000480d4001d5100b0081508401e500090241c11555031941044c0c204980c100182e002c2c0c1129a00795426105041f00051341a200c80314050040140c008100300d01c1c41c200e443c024903440202c1d01c0302d8020600160b41c90000d10396510240e03015000319000a2071941c018039500c4594456807000440e103648100b070015070300e41445510000c0c10b00310010492540241d901039103d04485849034250b04102c0e0028041142010602d40e1402004101010340c1204c588900101c001c400798050b4005948030803291801014403c480c141e50004020761b10301d40184081084503c0388400360b92103103106020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 4692516 1250 4691266 4691293
    0x70c1202070f03030c020310020a05070b06120f030a0305071b11010e0901090905010e0105060a060f090302060a080106030507030606050405100924021b010e09040615080303090f010603050c040e 85
    0x154003c2d43c440d5a8100220030036004052821034822140302215204010740c00c166500501101c080c194030941c001444d569170300000e1103907001c0049000c05ca0181e61754010240078040000c0602c0131803510104190b8440c000222184414401100419280290404040307105d0f0125003c2c80300051400d02c921003422804034402d00350a80c04100c00d26100d004501c02c0050038007030f0440c5484541c4c0200b00c18a810303400a008802c01c0d105810a020b42c1e81c8401400b039110300b12910241d80c001d4552555100100c1c00244030440901c80d000000745030002084445102c0c0c09143c084071000c0d13859600b002e01780070030400c1304240c4000003420300010090004544040035080c5c012015000c0d100301c0e4900305c50401909000c002c4070350040c21401407500000302da0b00401554000103050318000d0480e92079281c45c00041c401c0ca403c1045282ca003200c000344a46000008510030824081580c0d028060558403d007030b81d2603804010840d801c005282880c90619030300c103840c5103d8050032607007411515107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 4693766 1250 4692516 4692539
    0x904061805030a0e0102010207020904060b120a0c0608010b030403090603110c120c0607050313030c02010512090a0507061103030a0b060403020904030e0a0b030108030a0c02060c16090f0203070c120207 88
    0xd421109900041060f21200f50001d100682002c0280002d520b00002503001582d402002440208040d60750315000c4001d40366048810000150ba4003250004682800c0a01d01c0114520805000440900020a400c0d6404c0150ba0040d035041d01d0351004c40d800c0040c10380c0030f0110740e0004030500b142405880441c4c103042100421805904c4805543c410040c0b09c500c1c18214010071900c00e0000030400d1181524241c241c004030705400d4a45a8980186880100d91034071913100f502e54410640c20074041909804900c9170042481501201d1409070b4034001500c131044114443c02d02e5030014000540800103980240c84c0c6004000c4c010344c58243c0380c0d07001589002098405030300054000400c0c141e54208031510350003034600c17001c0c7c42d07082d503141c201903c0c1d4a1150510740300c100b0203611203410440d00c0314020303a4501c1e40020190341d44c4503040941842685042d20600034240e05014080680901e0b40c401c40740141c82e940d9882a800d00b5a46580c040702c1d00c0107076484114071a00d040060a0544c11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 4695016 1250 4693766 4693811
    0xe0316030605010305070f0303020307080c010f02030901020306010207051207030609020f06071a0a02040311060d0b03060a1410080c0d051f020307030f1103011202060702030318030f0109020a05090406 88
    0x481c0005100d50440c20154500005a0407426840e520b80c041030011030740000580704180d600660095450b200e00c00c143d409081080d88414803640080140031a032034046d009580303d14000e9088806842d0742c0d400f00400032a05503804038141d000b144060011802c9500098030317650002c0e0a0040423500d000104070380da03108580554500b90f68100e02615180c0c1c1f85021600060198429410641142c4454000c1002a020b5034030615001420408412140d0403001d01900700038240c500a01d0302d000110040d1017011040350301c0c1c0c0c041d6800108003010884910091704c4003a4000c7c040020442e051101c241500138094465100d9080840071300300796180b02d2962004241c2000d81c990a01d0a00541520b08841042d9089814501700041c2110380c001540c1c110f50860010000c078180c03074000300c1c44074868040041d4040c000011001c0c3d80f00319240c031b48801c0283c141d045800d030040c0703400f00500b00c544000c070027503102c19800020050fa2524070b040d1508a0702a681c0055124000c28910b40e107032032103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 4696266 1250 4695016 4695023
    0x9010501060906020d02030f0901030e1605040606030501120305030601021002070303090b010501110d030f1401030b04110a03080708090402091f08070306080601091104050a03060902040506060403030804030e031603 94
    0x48000611506a01a0761000202800c0c0000e01a08155402c0651240070342d901c640540900410840c1040e8440d41040744580080001d58803200343c040c00c410000849405024011420840e0025400744203105240c100e07030450001c012828030342c0c0d0742124660b00107400e00e030451061101020305071b8054401402218481e890008140e122480c1c00050400140e00c4241400941601e45640710004180c04800000c64680040c0d4040b00380c008100510107413074050b440d0a103000011080041d10400c0600036401181c0c00213101161804000101c0a180130040041c1401e021440014007000060000c0140051016003020aa0030104401ca050580580180e005003408440c0f41900201c055401007103030b00e8140b19040c10510480d43c0e07400184984030201ea40c5240c4450380314180002e07500602402012101a02d03a00d041090150034550800c1c1d111318500408a032103450110100c4040700d40c10303251200070b07a4583d00d0907503440309451603041d010300841130000d0780c1d4440b03042c05401a512 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 4697516 1250 4696266 4696271
    0x12010204140607030f0c030203040b0a05090301060506040513020901121107060b01110a020607060207170703020106080601030b01050d0c0305060a02120604090807080f0408030a0f020c0a0b040902070206040803030901 95
    0xc0e200c0024103020301c59806500903082040000e0100b540840c8002e088900c0e42402c50000940f441c00700e103580308550115070781120101c0e01c400c48540c410010100c4100480007800b513540c0b00d104115051066104059004403407503003a18507000247c01515100d44c0506044800754254a050740546d54101480841c4072000200c003000c00515101e40c81c1d60010078a0a9000300101c01003003555030400c403802034400c0d00041846010003620790120345040c0e40c0b05058912803c0001103100103500114411400b40d400c141010815801c00100c00f1704990304007514100b10313403905003445000300010b4001e071210031030208044003054040003194001d030303010800143d8450048001c1d4860a2025103c644500c0c10304030640302043c01101582d080f02e400c15a40c0d659280c590742c6240181c41140e00c8121a400042a111341040d00951080c800018030740941740300c01400820442c481c40280588040c800e02404103003c00506c960140c048144041d0000d460261508011031560f0070450341d02c5102d03034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 4698766 1250 4697516 4697519
    0x12270303030c080c0901031e020409060303020607030c0909020a0201180b01051306030b0105041d06010308030f0a0203100611030c01020706020903070608040b04080904061203020109060b0d020d020f060912010204 93
    0x181e0511a14022030b6480ca058020341c14003004540702c2e44140ca0a440c101070702c44039048000703800243c48503000e00c004101196155624400b9070050442c0344015030240c061200010f08003400390051030307041c03c07441d5522a049810b104a4900a41012241200b1507607500f00e09100d1580c03140f55002c1e03582c00307440d09a030035624020070031a500c0103040d00c00d900e80307042c000104000707046c2c0f01c9214150380d000c42d8003082c0c501510711003080600d0407516250403441340da0300010030b000040c00114080c200e007403070000c9075996130346c054800e030710050710083c42034560f40c0b008002c91841060b2111030030284905907858034117003121036401e80e00004403e481442c2e0028062900b89410884200200302c0750600d00d00c640740548403001c14640081000e0854580041c0d200000c3d80c0315808000070f801a0f8141c07c00500075070800a009000341803045804d280f030840004082e01d040c40a614485600410900031451b50754280062111040c1d60140c00410a03c003408507652110b4000c2c16008d48680010b8640e07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 4700016 1250 4698766 4698773
    0x3020708010c030b01020601091d06040b0f160c030f03060b0a080114040b1c080912030903010b010e1c0812070f020c040203060a03060203131407030308090d0c122703 73
    0x503400002c0c40c1c001c0c18603050b16601d480e42c001c15901c1c1152500301000560901c0d00c080c0f100c0b00004000d9400030b50052608010400c8600c0380d1190040e041103290038229a150f096845a0614580c40c500101b01c40e02203000001e40b1500301d20441921324640455802c1d6240e1455450703801441c070800c0418590801442071f04052856070b408810100c40c140440328511010614111558161068103d50a5200c205119140d0101c41c034080024040c1584803d51064442e00d07034100c140742e14801e50030101c5440043d031103035840c1003820308020b03c0169028445100c2042503044144200e90126080c02803508039074015141a101b40705030b8a03070144e08111000000c3c14800380000082c4502e105105014507900d0710300c180000d90b68020001a07582c1c036844111201018280340c0241028051400c900c1455000300d0020101c1e442600c903194a9240c0c00c400b00c2d1190703040ca07102400103000070180f07408900103142411100a050428002040307240c031484540000c10088401c02c10451078082040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 4701266 1250 4700016 4700021
    0x40603091407141005070b07120b090106020303060d030201061e06020607020303070503040305070501090c030804050f010309050a03050a1403091b0108090c04050702030913060306060803030408030f040804050603040302070801 99
    0x6111901c0c041d20380d81d400e00008801e003902c1d1820b000d0044440a102c0410680103404a510301e9030449000d0f205450103000003081181402d03800703006213003041181185424000e40d041d05840303107a0083c41c00c0d56100024405d454000c52030a170115034035040c0004040c001320640068410340f01c403002804e1418010084e1401300c01030811001c551003013080100341d69002040e0f98100f82d061a18596070601810400d024088003200a404000c030b00300000200100f540050040f54002d0740d455407180d504000640894201ca58081c0c070603005841f00d1000a8440c80041141043c3c50030505100114070550b040290403c079002c3c0c080b43d0181006179801d1030040800c1c0c18400d030920f404100d92074081c0034640c54ae20a0403549000b00d8841c004140307054028010f881400c200601038010104e11440b43e840030301510310082d94601c3ca01400801c0c00c54000c42243d11803500310079528659150f090500c1d8001034000c00590705404e040c4000b03e42562145d0066010728001c1e40240381e030301c1c10b100b640c908 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 4702516 1250 4701266 4701293
    0x6020705010b1206010e01120305040305060a0606020c0a030201050f0d0213030506040c050a0510210e0304050a050306010e0f0406020d05040302010b18090d030506030a0804081c0c0b0f040302010902030304060309 93
    0x4580c2c0c0903400411030f082c0c1040c1c001f415540c0341c0003289100340c42458160f03420b01480d04000c0a80c00380c6000c00c800d544460f80542c04881e0580d003203400d0360801d401840704011701800302900280b01007107541c00500039140200041014410010f1911039900040b4800e0892a00200e80710b8103c2000e00c01400700380c8550501814084a8024221f85440c00090b81070f41c20a5114041c0420356640034507031000e610301d507684092600c605200f020000043c507900c99200d801040e104801302ca070049046e00340010554181c8040e03030b01e8505147c80e00403080c0010200104111012038007000f40720900150780c018280224825000481d0302d503868410804c070942c1c20300e01201c2c800850b1081100c0302c100011901c500603810300740000c068940c1030102c1d00341308840d5801b03004030400150015001100044806074051030000390900c203032591804440e400c01043c0060005e0360900c020400620481c42020f41040c842d000006405140d0750100741990007030b62112004c030b940c400820b0144001e0303584485 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 4703766 1250 4702516 4702549
    0x1008030703090e0105061207030e01090c17070b0c06010b0d0905030406030b09090609060a020c011506090f0602010501030c090203060102030d0920090603070909170c030315030c091b040306020705010b 88
    0x600300f070b080144085c00d551f0024000320030551204400440300c1001c0d40700d8106290041100c0710b0998662070400c2000f603148800301d266219142000442d6038203003054441c0c4400200c080c01e55a441c201415903e82c002c00c0c0f1100d9801d030794140545c005041080140028003c603240404c40880000400240607401010b08803a50092020420040070100b107441c0e014545090050311410f01901300ca00408420780e0140500d005004003040840e000000f489c119002c01e500602c590f0384800080782665020300c8001e01c08a29182e050003005115006103911a0041c411242003100003000b500559409074400d90702614103003c00ea00910000d859550340c800b06070381e5032042c1d04006001c20380d500c80d04d02c14210143d980d502d1100811503807a100d081c1d0100001d041a455035131b40e40307060751240d00036924131800c60040400c07003280d42004214209295001400303c145aa00c1d05c0c0c000580e400a0003054400d207004110210001c4c10500c00792007664081c200004015501c10f09110002e854501201d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 4705016 1250 4703766 4703779
    0x4060216120327050d0b0603010b01020d02030301030209071413080c0102070302060d11040506031006020607080402030307170c0a05010501030b060603010e010b0a03022104050d030606090501081008030703090e0105 94
    0x1010a03080800d42e40504242201e01038010720f00210820b551485401c01503100416401c91420312041480341c4d80100c20460080005c0c1c03036020700690b030343da505010160260f04184010005803801d400c00035408012410100340c119080d4504507500d41c04101c524003030040480d8280800c803420071161003000307001e000410300319085800007003103030040140d9000e03059155940740365580800301c19100109005840c560f2a03003401003c101c801d000f02d000d104014401c04c1e0024800b68400e202c2d29001d90f030060051480c040c02907c1d102d040c9401e01c0507440c040745007045900c5103241c0c104216264107000d40000562541145046e190794500644120301c110000d10050240c0b01c0d080f40746a045035080c903101e5a46060300d030401c0d00a0b02a07002c0c0c80e110301441c1c105d170802e080c0e0300c04111841240310300261040c041d16040c055040350802e0041d1320008506a1045c06154002c1c0100c642010301184903909190782c030800f00f403843c0d02c42141140060411030003004000351800344035015020403100b0b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 4706266 1250 4705016 4705049
    0xa0501090204210602041208120901020a050a080718090e06130206040b0c0c040213050906100e010e01020a050102210a06050303070602032205010203150105090a0b090102070b04060216 81
    0x100300c0c05031000f441d18084061640c0301c05041200326411900244600c820403045242541040c90158100b0f21410481008000c002141c1e04018422100c05600b035859990174409481d00480344103500821903000d100c1c4501d5540120084002003074010040d0030000314030f03030744a1034005040c120042c101e40443c0407030b0b040c1e14006035103410599050300c020120440c6c440c0200c0801c50f14080728001003507045440004e40b5580004580d980b070301641c4042d501c591060300c41d007003800480b0924001c0f0100080c041072481e04a58800c0c200e0402801c0144100c035102c2400752611800ca900218a40e1041449480310380781d2514060001d0307034400030200c8200041031514011035102d10408038010046a0b0000000c1c0d00314082e1507070701544110850b0801000e02552401c0ca000b5403080d1083c400c00a20990240038562280c001c54021031400340401e941286000102043c682005003c103040d40030f18180401e4000214024000800700d503401040b81054040f00035044894a07000401d14a409000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 4707516 1250 4706266 4706279
    0x10060f03080904150b070c0608010501020a1511040306051306060b0a0c1e0807030e0306010b1608090402090d1110031b0c1104060605090405090604051b010201021308060a0501090204 80
    0x58442c03001e8162808610701d400d21500e809501255042200b00d043d000c10b880c8107020900d2540019600c55488803182c0d47d807030304010b80c0d80d801c403d10020b201c140c44910281110b0000d40103806811a1904041d0500d41c41c0d079600c109842c4122003c050141c0000050010300c00180070b00c4008100103d4143d1030440c1d40d0302c000700004009040904022405041d459801c4c0111894900d01038000d0f1070107841e03003154640245150303c0d41c0c0040d4440e20480380080341500300041218440342a1240b0b54030104002d80e03803003046400002307016511031b50901c40d550454880781b00240d105440b5100a080e149003090070800d19000c400010000c1502d00485210400e80d8550003540204030b601304403040c6205803800514400c1c0c204502900103092510000b030150300080908580d00d000c40e024000c0356907100b841e82d81e690040790040c005a0040c00841001e038843ca80f4400900c1c1c2c10300c0050710704104611850088283e551228105030f000d0003c1105007550380c420180903040d141c0c81586458a40720 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 4708766 1250 4707516 4707533
    0x4060f09030c0305090a03020603190606020705060a080901090f0b0405010c0203030c0301050d020a0b1c0e0309060901050a0504030c0e04110102010b0916020106030501050c0403020a0b0a0206010315020c010e10060f03 95
    0xb00900340480090103083d240e0714070400400541d030041c009175030307850007070080384421490703ca2580c02caa09200c00480d0312800405d840040e50340c0a000c06040c040080750071922920098404800c6550f1581d0340780c04100060b600c0d80c00940030345074070741a5003014030f811404c441e407804240c02190170030710501400a148030102d0381105d008983d014200c205600000f08609050b41c800c9081280c0010ac641e00c070300c0d070a100a000c51202d40010400b04203c01d01d465124840c4036465540220f041040041c29802140600644400d501d450342c02e15850780d40728845003040f41c00c6441c02c101000108800c0202d441c07102024941c081c4028000800300300f010032842c900213462409090400c442c2c25482c54403d61012000350b030080024061340c141307020440307401d500c40c2c002a4022034941001081c40c488060441703a58108503401071899a00c2d54880792440007007101d400c2da0301d5808105059800c0070034003902c0030f01c90024000c0c003404008007500d00c0803900554040c4129824071141040401c0b140c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 4710016 1250 4708766 4708787
    0xd0e030703021921030b09100f0b030105060304030513030f030905040b01031503020103240e04020910030308010605030a020714010c08060d0803040b06010207080706090e0a06050f0f0a0f0603020304060f0903 91
    0x1601e03062400c0e1654001a0054150000d140d50401403241c00c1188102043c1c9904c4201c807109c841c40340145454031001c1007544030034001c56401a60800c0400c000030320480003407003e482c403840807003e25600ca50707500c0c0d030711000d483e0150300103454928140041e1400c0c4c4101c4c40403103802d090410403206099078041e00300480b480040d0505684d12007503090344103481400152003040300d203480c00700303903e41140c8040d60005980c00d0340220030b4500002c44601c01d00190000b1f4980503200da080aa180903021242c42d0f000418010f4807e40a00206c0001342400d0049440c1d69070f5400042100b40c4400401040d151000300360368842d400c1104c1c2c0c4004115500c08594106030403160800903903844a00607840e00e09507600030f440c0d0b44154040051025400400801981d024203030079912920f44102c900203544544c010380f940f145070000751051510f020480c209841101400a40403140c0e940060041803810741c1c00100881d40000411080045910908281205a074401c0012290b00e031002804003225 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 4711266 1250 4710016 4710053
    0x30c030e0d1206090f05010e06040c020303040b090a06090803060f06040f120204060b07030918020a09060c0c08031b0f01090503070807080903010f090201020c03010b030c0103110d0e0307030219 85
    0x200020b249202031641c000030040c1160a006004508903018444000c0c034003440390002000d000004905240307441d008031402070740c02d580194219111900c40500e10b101c0a0880c00ca030344240c800340c0000840d18080d007010180140810364407880c1000910041a500f202c00c1841200e080000784003c1d03200284650595811103a0141c0c04903070707071020900611b980d41010b042d03a40c011503e0f00806070300074080070981d04425803500c9480208142c50040e40a10040000403801fa510b040c00070b180b080160b8046603001c1d00406c043d20f03982e038950710f04581c84244d00709032070308501e560201411020800f415850742c04500801c2152101d850789070b107a00401c2e800a01e10301c0001a19010701110b5010794043c000010001c1020040703d41c401c1c0000c1a0195040740540100c0d598a60f00d440e044c482d0111560014000d01000340e500401107009210795004041c0440c41481080d4200600d0f20403040c2d02c440300700055645526505019150000c8250421506409030728440006183c0c0ca02d80c0250112 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 4712516 1250 4711266 4711277
    0xf1002030a030e010605030307051f02031504020904020d05010303030507022109010f020a0501060905040309080d0206011404090b0c03040204140114150f030f040b0106050a080f090106080304090606030c030e0d 92
    0x3032a183c880d000d40140d13441305074540700200310b510074810007152a8003683c1111405412101784600f0380030036400304840003050a643c60f8500800703400d081c3c00134261110000c0c801880c0003200001d6804440003038109800080d901c50030010050b03010031407081900c030003100320940c84c0f2000450f107800e44950510300e81040686156000348074000c00030780d01d160303900400070b01241d41c07108150402060200d45c00e4000070420100000d0b01705000c21024414035503580a08207507820220240d542c101da120710b20b508256550820350210b0084d120850040710072880b400c1d96401c0070b00401c42554007400340c60074070042c00340c010400c000f500190311500c224150781c038043c0718a02e100f040c43d440c002d10b845500041400400c11440300c100d003106c10f11541c819a1402013690b00d50308101c815001d030300200381c0494801c0000c44d403182c0381e9100303542d230000c22200049041500c0d0034400b429900a544592180c40e207981050101c2d40c2c042c00f445200641c2c81c5401c00803070030182019031795664080202d009010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 4713766 1250 4712516 4712531
    0x2060106021f0b0f06030a0213051c030c0201051b0601090b030313150504030c090209010306061805040506060c070b070308070201050c090105030423150c04030c050907030e011404020f1002030a03 86
    0x31503c01e13121003000c500911150306c920342417800d0006580801e4680d084c0c155199408515032506d08094a024066201c03520544a020b54040e00d00e0380390b003c001e80c140034040c00203092025078440704103ca0b1414a018000b154500288542903036113490100e8442e0b00705100d0b0040d039604444480c000c4078041400d070861071404420680d1144a00d80000d04038840201021039517400540003020164402e0341c0c200084c0d0365275a4102d840d401000c0310060b00c0780f00381008221300e1034160801c40d0892070042c8154506050410b180d40342c08207075406554a4540400e1034020306421909907540305003240028005440d0044459000e40b080c0d0700d21070305010000c00410f09100104a9011203194031040000d1301140c0b00300d000f5600c8901045a1030000d1202c030001300c080b0700107000d6130102caa00c022003080030360411040082c6120020410820150360340345800c2411001d0080c03c1c01003100005045031410b190040c001e800100c1003515008070441300e10568900d07400011900340e4030540c5000900c16 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 4715016 1250 4713766 4713769
    0x5060f07030e06040306050609060301050f010603020702040b060307210209060702010f03140705090a0603060506030106050a020f01050a0b040b030c100e03010921090626040303020d1401050102060106021f0b 91
    0x9200c0c9960a400c03080c045008010002558001d038000c80301194270242c9030b85c44404043c20b80e5022503a810480c81c2c4440108000d40c00f80d006040c25900c001c1000c6282d0f41420081662174004482c0c50000880c20b0840078400d400f500c080d03210000c0d0f0200203501d00007410011071b100c2d105490b0020304203c40d5520500f6160701ca0391100740d00300c00000054006060a01c00141960000400e10388146c00c8a800024440d0107403040701304403040a0f00c4103085a1030170364241c4880c1c010a114400f94003841144085040d02841103d2080e40f01c0000010044400d1090000300c92202040c1c900980c400401440d0710380e180f0100c3d00030301c640c0e89003001128292002090142903214401003050518600300c21010350300209001d13003407946903101c502c80ea0361002e0403141d840d801c20104610008040200400c07802005034a81d01900034140507103031460a40ac507008641420320790b40e441c2c480e00300044c0110340e814042c070340c014641d0b44020f1402009030f420740340398400da210018440c2070b0b840200e40b680e03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 4716266 1250 4715016 4715027
    0x10903050f060103050d02070501020c0603040f0b070203031005061206121f0f1503030504150215010b070501050109050106050f071103010227090f0109020c070503010606050405040f020405060f0703 87
    0x55540803058030801621140095a6140e0a02040f2014082c42d107000c072549200107080021144160300510409405605004656202034000e40d485070118203a54040b40070f07140302e1405800a03600660fa00e01e07000c07642c0d005c6090700342c02c03040c03103440100700c400b0070007040061342c58201d40112191103040501c44441450040d07042405415444c0400c817003c00209140c0c0200420b5081107418891040c0d6100364500d402558000140030071410f0200384400041c4144004400d412401100c140000111140b002100242e00020702d0460000b604000c100081c0241801082c10b00d50a00c0f13154104a001b44c500d008403800c6054128000c00c04105100b008c1c160b03001100c8018008542d1940c00810b16001480301c100c0050046941e4940051a8101040507034451003910760040f0050342428200c01c080e45c46044440054801c01001140584d828800c90004205503142c4513502ca14000612040e10320004154500901c140300c00c00c0191100c00481e1102500d80e203800383c0d14407040c80c0c103884 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 4717516 1250 4716266 4716269
    0x7020c030115090b0406060203070308100807030c03030f0207080d03090501020702060406090509130b0402040506030c0a06030204060207081b010e0109090527060402030c0103050c090d120809030a020703020603060109 95
    0x40c10340c24816014031041010a07a04161041c8220070f20800c0750b03c4080c030055030440c1c498a030041e44104020b60100b44555201508410100d0f41616800d80d9541c03500d1800909800654000103100c00800c00c058028000c4002c613101341c00600b482a161055403a195400000010305040d282d02038001041f800794100c0e000f00354014851610f07141c9400780140f040c0c0f03540c000d26025000280108048c00c0911200c6103c00781e201c1c4103d09159500d03804d02c000b4240141c07409030144100e03070713030442c1c00d595100300b040240400d6500141c4031450301400a180c000c0360ba202e40f4040d0400c0040301104454404a081c24030f80a09204510242d001c00480703000e00d00760f121400a070f107003906204c100c84400d19011394000301420980e440b5482040050340360f4000380c40007945a0b1011924207140c0d4000d400c007542c0212404011802e080507000442c0240c0c11241045660b0321105038a820081e800c181195045003094004600b000e00008000e550f9040c00d00000c3d00c50f8001000042c1668480d0002c0c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 4718766 1250 4717516 4717519
    0x50709062001110705010605030604050d0302130503030d05060108070e030304051908070b12010506040e0a0504111309050613020a061101110403080a02060a02090d080c0109020619080105040903050406030507020c 93
    0x40031107200039542d006a04013400c1120715501b000c2001a4618001404c140529084000390594200c0200154000c1d840601544000046040700044c01e41e03041c0054055a5240390002c11145801c500040100000070214810b100e0100d032041c510340c0b000001c1e9819901c003a5100c001d0015005840d81ba60307100d0742c1c0181c002c0d101e1201d0104001c041600a0b1030640e802d045803040f0741e40c80d00200b040b1800740b802541c3c0c038483e84000003840c0c0003d5070002c940040c041c0f10780000e01d100c1140402e1007a100f40070403d4003651540020020014204500740d4031484000340c03a032200c0c10b90340c0002e10030122403181e0740806c6607445000d44102c20a6000c50200c0810000b000c0d915640c81c42c1810150708194806805401100d000600000380c0d0b000729089000014810064030321243d45074142d5030009255022150342e03e0402100585500000340800140021100c0110328042d00040070200160403260045090031715010020750450f040d80c0c00d845c140c0c2808034031680c850704201d01e00000d550a00707 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 4720016 1250 4718766 4718771
    0x50f04050a080706020f0d05030402100909050a0e060a0903080601050307020111070b0f18070b07151409060109020901080105090712050711070501050903060406050c040801050406020a12050709062001 88
    0x140e0320900003407203c1240d4481e002e4a2906155010844d2a4203413000c0913030204a0410008005113481003c807604810720381818840144c80381100300807910f044400c0003040717030355481d240c401d00f40c00c0114581c4a802040144150407072550b00920684000d02000e05101d000b2021641d118001c5d04102907400005140c10b40383c00c0380b402d004065101c142d98844a031000c0402103804001001c0d0030980b0300b01c00000800304540350400d80b00a03588825015a0222200712407002882e019000d2920110b1041d207079034003a41000f21546041c400180e00004640f0320402029100d40d81200c80141107a5007250b1446103995003100907104020007a4209244501d400308104e625504400c10a89a40350361b421100301c2625500195007510031055a00c0d803603440480010b000810a410003580003031742d824101c0c1481c0d951840c160a4501c1900c0442c2d542d0b030007143d44d200481e403040c821084610500420300c09414401c00180c00140e0b103014242c200150920340c0d60f24011401d11301020119200000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 4721266 1250 4720016 4720019
    0x4050a1401090b0a0b030a02060f0f0f120f1306050402010306050409050d030c051216020f0d050304050114010312080a0216030c0506060103090503030705030405070e01030609030e06031501050f04050a 88
    0xc40d8000c084501c822544600007a020650702402842500d4200070050000d021501054003080242d0f0001a45106008010007501140c220544003038840d605100ba001c940f55040017a918a50f0040141450054407900c0e00704540000402400e0801c5071b04500b0004017900e0707a00040340907150a40145800c203007400004c2040080000720180c080005603802c02051110580c212400d03c81c10201c00160805040480d010000b070b08024a860210703030040782c00203403440c440282405140110100031400c040f040005004c42806451803135185402607924540c115564052800380d840c6082017084030700000104094810b504440440a565840b11a1041e407850b005000d417504140468a1b03003c0c5001040f0107500a024140b10781d03620001440c11980c41000440d140d400041080e5170341c0c490541c000610360032480106020b10b00401c030100d0b0107505424003408100350000c2141c0280700400c01c01c1140c4034101108a1040001d181440e516401420302003642d004640010b541322001050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 4722516 1250 4721266 4721303
    0x3150f1612020403110301060807080c01050c010e0f07030506010f03021005070203150901020702010e090f0112030c0b07030204140a030b060d0204020403021005070201020d05040e061302070b070509040b04020c0304090504050a 99
    0x18405203145c04800a2040b5911080c209403211100d2003942c0a66205a8000c034a560190010300080120b0100014448007910707032142c50861040780501103034001410a20030701909110507409402e100c03503800a01851903000c2041800c540550008106011421b10304540d424400410510f02d4030060601506154041d14004e503c00300c0100d011501280804496040859020340b284011a2a10300c0507842c081c250f100f03203007030740a00318208202c0750300d900d0008007104901400b660300781d81c0068079581000203a031498001420840c0c42034079004c0041000910329503555078058801c2d9109034114240340f0100707000e40180d400c0290300c54900f008210455a01c030000d000024001d038201d41000c1062901592940300d14001d081c0380002000000c1c02c81c0c00c1150101e80c42c1d4000b00300c01498000d150300e9400e0081d40a95030b0300000742e00010700c80002d00d02802a00b016000480303045107840c01c000400307552440790303120391031005803110001014000c050090400150300119144a840301840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 4723766 1250 4722516 4722533
    0x10807110f030910030b130e10050906161b060c020709090605070813120507020607051615031103010e1506030103030305060a0e01030803060f0f0414040203150f1612020403 76
    0x1012070041d1180001350380342510a014441c0b6404018101400300214a41ca00f0082c00303aa00c2000040d00c00c141800d006400701d403280d0307071056040d100949035134280a507507003260308980d42000080140e400100d581c00c0740402034848050703a00034000039284964210507424015aa44542c0c1698a0a101c0c1c40c140311080d00302a100701810f075218410f81e503580c81c410b0350b4502c0c2c42c90050030058580d8041c0d0f04141c0214010844140010036080c10301006580e6280361110001c040f02283c21192000c02900107200c5080112040c83d0909103c03580401d03502101e540414030414000d0302c0074101082c60070341840061226488080c00340c0340e40350784a04000d03000d464103980c003134040c00d01c480300000c40c4101c103608241138079404500386143d40c0300c610810a17200780c02844a644a25010038200488c1c0d03903407041251081c4500a0580186090b004150034040260316005103000380500700080000043c1d01c00c3d900c400c96880001c0c3c0a003a40204542d40f070803410081035101d01c0080c1c04020b214282 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 4725016 1250 4723766 4723777
    0x1030f060b040f0e07030e030f07060204030b0a090201030f0c0c0f020604030203030a081504020a090302060306130617010e0705010921050102030106030e1c0801050105070501021e0310080615010807110f03 90
    0x70204421355455002c000c804680c50a180032050350414040c802100d10740700020300885018080260034a80c80e61110007420b03509840c05811241c0c0c0d0880c0381c04658050241580c5400040401c0200b410910400703020346c80c4500009022035440800780c000c55607140242c43c040e5402a0440b526025110380c00340c182881500e07492081301e42558106c0c40c6140c5402200d442034138a40da12400c0070b1a40c0c1c280220794202074043c40d4031840c500f9400750b444810f44104030080814240d071890720100200c03400d00b120201d00680b011a0458001480943d8024070324004031001201040d56130071140c000745d98110100c2000901301e5000200004040303a158025140c80c01082044d02c1c0320515201c285410481120f9052003c900542d00402c050340c0684050f1043e14000c00000d0300e417601055426204003100020107605200100601c51100282c01d1503d01820300d0034000c080d01e06003280d104081a9883c60441d041100960010781c2051042c4020403010100310100c800c4031803002445604d98004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 4726266 1250 4725016 4725029
    0x21010b010809030c07090c0309051506010f03050402060f07050a060903020a0c0603140c0906070b04050304060305010803030709090c0c02030d0807030f0204050d0609030309050607050309010b01030605090601030f060b040f 97
    0x1c030408035850312004030884030034041c10002002c0c068540740d0300402400020f148001071580d918050400f259060181c0b0005c00b0380d441c1464040c1c9051800588901c600c400e03050b0805203400708000050311518212200000b1107854184c4500c01480c019103030583c2908003c05460800b014202016000201d41e1041d5109450724011103450711411002c8407010000801540f01084c04114600c541a00400f082c94020b405580341102c076854000740c1ca01c003560708036619400003c0400201d82e1500c602c501501c0d04102a501d90300384040000c00044440c0180000941d45000c80c11000c2d02484522020320b901074103481c002070314030102420b0004100c840e171000c03d042031b80d03038001c841c1c140c800c0790305039900100602d0100320300d0b40b81c0400408030000c04809040d43d41d11040081401007140d103200340310b07a84c0c401d5902d203041842d01e425a01d03545810740c1410700f081410f0041daa51405110fa100c3d90a10b0000340814441018501801041d40700881c03a01001901140340c4038500c03d01016541d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 4727516 1250 4726266 4726277
    0x5030a0207090207030206061009090e0304050906010203040f0303050904020403060c1d040623030f01020f03011e0e06010c0c050603090115051906050304140313080105070807090b0921010b01 84
    0x82d98000079003a48100701c0f0003070050300013074006805458048015070444609182c81c259542d00ea1000c80210707411481860b11582c03010904000901d01a000c00b40d00480a01c0038505043c504840d500ad5192240030040a0002c045900403003030312994140c0f401190006800d00104a10030800f500c06581400b032880b8002110141d50140c0c206400b404c0e0865a2b02c800925508131400b03a81c1c036007030001c4003e042c1d05018505520005c00c009001078425411040c251300e40d01d516007000307021008900140040d018802610800c40056000c0b1216070000e030a00301032201134002c1c81c000800030b40f55080f0582c032001c08005e04c02c00207015403111803100310b40501c080600343c607071040041c0c45221901840786a94014028407481d0301c0b601c051030b00103100d01e40742d00d0303249240394001e42103030030080c000056020800000c01005d0024000c9940120b045c0c240040c45040c050b0004000d09c8050113a00100500050780b004e054950714040c00c40ca8007100b0b805880c3d00540b8280e41d018101c142c1c12140000c1707 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 4728766 1250 4727516 4727519
    0x70f022a010f03060305120a0e090702010615020106060f051b0a05010b0f030f06071107030605040b040c0b03061f020309030105010306020408071d060108070c0206030a050702060a0209011403040503130305030a0207 94
    0x40c0244070724400d982c0c0144c002d00090741f04100c0c04550340c3c400a601401c03c11680e1600c03e054031002d89031400780c491600085803c508001100d40100070040c0c004045a060400800c200d0350000e0302055028403c0c54482e581e00041102050f043c120f503405c60700e02c1d204081044040c400c066204c4c54400d03008a4504d014051010304056844e019503c1005103034000300f0206400394019000c0c00d40f03c690900032341d4100d44e680e407603140c01c80701d0440c0e0607a001d00070401040200150b030f107810b074041e0a00c0d446c843e00f503091100c041151a1417080505140986d40d52001c20080e0003041554840342c00280240842e42e10b031f203440c070f029411070710480f8210700c034410707000c18405e10800240340400c006020a03103c550301c83d0f0044600940141c20001400390000000c405a21313244000c40c8101c003a1007006c0b5803818203d00c02403400c10014803241c0b110b407050050f01010380e404141d52001a9210781100d4994903117082080c114800c4000030360f00b100329040c002040103804000303070414242c05d03020b40b00001d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 4730016 1250 4728766 4728797
    0x801060207030b011203090305030307020309030606040603030e2101020c07090b0306040203030a0819020a0507030f020c010c02010302030c121303030605190320100216080d08070f022a01 82
    0x10342107408010001d03c0302070b00500411850356003610340c290280c0350000e01c80350f0740d80301e060551340251009001608001900042d908003013001c41d03000f003025a0100722491231078400403c031100340700380c440c81800450b0003444400c0c928406440080c184400031035a030781d988401c89540d5090f91064581c0141020030142d000e00d0b0100c0c005200b250007078003070340c0f81640505044031950401041c1c1516100003031500c40c1c220b6054800b51805d0003203510340e11b0343c4903244c3c140a0032880348030150340210f603c861800801640e1100390400400d9080c02c1c01358a98803000fa91600900400d2010322a8070740140400500010510040c00d62602a407020021240c4403030a119010394110b100754941c840740e000c200b00040c0b0400ca010204200344080110103110240040d01c1120b034100c85800503842a0340e125188060f038004003005120140c024120101c81c1940503054101c010725880a0002c60901040d03070900030320405a88410301c1c0115401c034140751020142030309000044600080c441e44032403643d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 4731266 1250 4730016 4730023
    0x20d0b0a0504050f010e0a0905160504050f010305030d0903090302030109050706110105060108010302010e041503030302030105120316231903080708070e040b0102030f030a020909060607110103091a0a05060108010602 95
    0x50f003450003014141d6820700c50301820010380a0803014619654451074000300e0000d001030000c40000744040c0403112f2a060400040c3c0e100540301c0041e03001e01100400020f400002203450541140e6000301d01486241819506d120856201070f400d9402c2140380010803001140140544165886405001e0004e8007a20700305d500c119202d60201e0340d8100103001540c099600400304000084c008a51803480701204210852954400c6001c01d401200610061424000701620034044500950410480345690b2020142c4500080c0c03903400d0000c2c0f07110207a050130418901a020303840840f13000050704009a80c0403150980207500140156022a801c82d10134940c0ca8010040d0b035441884040034001000018001d180301541544000c001d021180103508006c0c42c8210080c0d800180c4880e0702d00240003030b9030002801980700d0001000a24001200510b440010b08403c3c0307400610a4100d1a104451408010101c0c0501c0440410044801443d81081e44128401ea9800c00542d90f00c0c01c041c0d99 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 4732516 1250 4731266 4731271
    0x901080105040b07020f070509060607080c0c040e0a0203030d0f02040f0602030703090f0803030403030c0201020408070305010e01060b0915070623090706050301050a0b0c070b0a0801061403010e06040b030a0501020d0b0a050405 99
    0xc54224403030421403271620003841a00440e0081059180c0310302540da4604582c086a10302580f90400c0c2d85044961515105c1c01040c1548e10300a809040300550000341c40384141c0c5d8003080c2c01580d44400c1030450f0300c1c0e907043c0c601910300a985c1d0881c103501e800d8040e5076504060001c8000825404010500008001c8582e0480c0c900c1401181940c0300d554090f0042c0400340c0c1c095045650038400000d442c00704008a0000b0350284000082d07039024001d41900b5212160080040d4a00410001302242c690080050b45034922000c6540c9407616458035802806041c0a0102740b1502c811500403818030011001c0d0007072034504229054140c0d41c180940300c6010034800c40b64803410310101080541281030040580c07044030404e80d00c45603160f0401e01c0050b04920801800903041302d0061044079040891545014001c0d010316003152b02d07046e4909180392005205601840d101c0c012018207450030040f049445074404001e54480702c0640181e4000e00850b0010791140c110f800d00001c0b2410039214850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 4733766 1250 4732516 4732543
    0x1106040b070f020f0411040602060a020c07060c03030b0301050a02090405060103050108030306060d060302030303040302060702070b13060c050a1403030901061a0d0507050d022206031404110103020403020901080105040b0702 98
    0x1d080c5000d5446489801620b28416038100c40b102e08a0111507903140b150b054069103041580d80c03100e061100c001e180400081014429520400030b00629600005041040303840c02d103001c0b400810f541c40c00b20080d0ac2a10314054040d0b003000c083c00804031498008e003195000c151001c0045daa0b580b001181528002e205d45804c5410400101b0900d04000d0020842d081a10002141c3c0690341c4d40400e2450780100c800382c0058000001340109590305115150080c460709407a030f401c10814003c0da00f118406481110207101d075280c006400c21000740300d121011904050408079041d441450152641d100b15011f403080d519044000c01d02a0648424003090060084140d0404107026021002404041c10798020300c0003d0010840ca240e00e070004000b0450190240030311411564030000b252013140e0403400074942020a42c0c032004482e0260302e0350094104048410718848400180e0080c499034101039000880703140003142c1c0c07003030540010b4007480c458440071515940d901d10890f101d2441d00d0030312 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 4735016 1250 4733766 4733789
    0x9140a031403060f060409090b0f01030803060103020a090b0c010b0102010c0c0f02040504020609030a08090301110a0507110a050a14031207050d0806180906090601060f090504051305060702030304110604 89
    0x25156207081001850744014060040710a5a5400c00007030250381050740540030301d5407120030450422402c41c5243c7d030000038061a801c19541160b540e00c0c0140401003041c0e04043d0b0100300307070381c40c1d510072030b590001058007103000d590380e1341d642583d60701030485000103601560810b4210780a00748030ba00901c040a400c541c0301c03e1036691a608010291601800c1030f6480b11051113007d9180d0341c28800d015195204801d0246e440324100c05250a541007980b101c004808184840c0c1e001d29000801c0b121a01e50141005500d400c0c0c070030029039000304030341140740c11118507080814604190303180a120540110125004268180b624030658414804020200e82050f06242492402401c00d17039003284008100c80741005072802e180300301010484290045600070018003d05010502c010780c0500705d98506136011105090000d44141c00303a00c2600e0040e40da80c400a182540000300e4040400c2e0b10400795046820030501c000d650390030556040d5005085e0746110213091800310111012110031a440307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 4736266 1250 4735016 4735037
    0x3050906060f0402070615060c0b10030b070305090f030a0f020106050f0604050d030903150903080601080609150a0806010e09100e0604080f0c01060906090e0102070c0e040206040801020a0309140a03 87
    0x20f1101a41002404844041d00e5054510300c5d240c03245000c01c0900140d903141c1c490741c41c0f641052407182e00c0107052035000051105051000c100251001759000440d81001b140d1612041002c031f1070541c04804d0000d0501001c642d1100348c1d076104007600c00c1c078002a402032090a84920801001c61400795209511050400003000b10341481546c0b092018040d0501c0c0c000113a072500d480d12208560307810300e2000c0f91b640042100305074002000980201d400e00e044100c5107041d20105141d8000500100c0c2c1e580491410300c08503580b02810200600042401c1d0744880d692140f20030b07104641540c3d00d8865029480b010180128140701c4e110050030004014900c41e00c3d2a240c0000a030b00810042e258038904001c040c000c07038001d001e040002e2130002c0c6d001410781e1030300e600e0404544411340c100701c86900401c800c001288a81c981602500c00c40040c01c403017515240b0000384c030351003070340e1081626500204901d2050340d00740c2e10400c0701c140584400c0050b100360f10714007a2903400782d180080c0400d440d26203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 4737516 1250 4736266 4736269
    0x3010302040c02030d0606020a021003020901090504020309030c0a05031b06040503040303050d090816050d090509040602030a09020a06020601050a050603010303020618032104150903050a0e010302040e090c0103050906060f 97
    0x12022454600c1e0054902c0c105c000f001410070346606802100260b403003181184110f05107164654070100c0c45103021810606481e0000301079030218400c1d036100715000f00c00300d03042c14010300441c1c9140510800300c031150522490696103a42040403040041041081d81c07900001b00440c000b40300380d9001300911b18090039035034140c809030040c9444440075aa5440688002800d039002442c02d281c5c41001851040b0151900f207190445110609080200d148010000c0e41c0b124000f0320782141e401180903889645400d0020002c2041d02800f0b580704001410001d10243c01251541c103880094072004245a1070b10140b180d036120a120040052b40300200240e00c40c5070400640c001000c0345d805480c9003520240100380e40c80251600c0d040030f42c10090070300040018540320b09005501d515800d1000300c0b241c2e2800381c0640101d007803003c1882016000045141c4c400c4d81101c0240940080100c1c0340d0074111030f041d0717481c0b010f0304059001c640381002240b0b9404002032180e114440051048840080c0d400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 4738766 1250 4737516 4737521
    0x10f020307050706023f150102070303080606071707030201060801090c050103051807080705041808040608150a0306020d0507020c0a050d06020418020a0f050405010207030602031905150a09060b0301030204 90
    0x3840710105024411940540309100c280d440284400d400240d06c0d820f10780c103443c0c0304001c000f03003150f042c1c0c90160102082c40e980104645045a0305420120410341c0c1d03510114803a03210301007004250311036000714028120318907005461114007a6000700119604d6440c02400c0b40c80081018040841200040029610070b1f041907070302c0f1149a000403076100d000301e00d092074041c80e5001030086030001c0e8020700403418140302c2e02c60501d0011900e40103045603901c6018961048c0d0148004001030000060518241095000646000030780b4403500039980b803c0c840003d400400e1040181c90400c00810302e51840050880702d01807000300340c4c4000030320300410001200d2400d1400ca070159028400051800c5181c02c1c1080200310400000d40d440380d4000f001400056905001400d200044c40203020a0740d000614000352030f4480d5005030750303440f00c00c01001105001c88800340442e00b010200140c1d00c00903108100090401d8800291140c1c03240d09a90030399956001d1b12410280910040015103040e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 4740016 1250 4738766 4738777
    0x403140304060c08071115090f03070b0a030e1e07060905010e1e030a051506090105030f120d0207120f03060b090108040f0609050d090515030702030d0b060408150405010f02030705070602 82
    0x110648504141002c6c08240b0104485a20313410400000c150007071181407401120b0305406d405c41c003402503141400d50b40f071480e006000007582015500c8607141143c0302d007003014050700c200320ba5400403055034002000d41e071114980601c0300040d6128030700140b20b5024102564410310018070050310507180824030103e0888150341141e00d07205411002c0b02285092100a08121245590804a1a144051140040303041c2d100e03902030352007a20f402c0d42008003c0340c600707102c0c110084816510300e907145e00740c8040c4c0150391029103800e08803410000b0240c0c0182e0280344086c0503850a001c40b5540f4042c0f000f05001e50150240492078400008002414400a00d0320880c070641c00002d00e104141c071040c1c40d00c0c1100e04c0e40700215003829024070103844c1c501c0d44c4c40300e61215046128139500e8651b400039100e0150720b0703054100e44c0e210b00d4899003541d07400e429103015142a20440f40a074012203401c0c110300500343c9040e40c03d5480d0002020941c5520300840348651540d8940314900201503407028000d5000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 4741266 1250 4740016 4740023
    0x120b030d030f02040b040b0c07120209070804030504050a080c04051b070323070804180203040f0206070201020109140c12010501050f1903020604030b04020f0a0501080601050a020309030d050403140304060c0807 92
    0x30400440d8000541003e080506647c200b0f03561a01b580d1945586001c0c0702d6040500b001d08002e80e890010303038807028165030007070880c80d00c0881621140350980d21030103103400465000c4842900814014000290541180c0c0100d5050003170b603c41c003180c01e00c0c50000800f04400d00008202c103001090240c0308001c0d00080b455614210f00103840001d200b190002a07003214020400982001485126003003600034000700d030021440c3d4182943d80312050301410303134000d00822002c0307040015a03000f03511041c00e11790408030850050b0049400b840e02d8007042c0401620800542540d4003004c00c0500c280b078161a070160240300350079103500800816804c0141100294100e2140100060f140c80740504000c512802d4a0303005030400d407040051280120004a002e190039501c1001705a074040700c003079041002800c01e241e458414a03c100d0440c46446e4420b41c2502c0394030010100e25501800074011640151011480380340d00c170f01c1c880e40360b218501c60b102c009a13168540401060340d00004154145c403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 4742516 1250 4741266 4741271
    0x303040303050a050f0417130f0306020a020607050c030901030b040213030605060a060504080d0302030603030d090305090103050a0902090a0f02090a0b040806070908030703030213030f0f05010b01090303120e0a0206031303120b030d030f 103
    0x27550748031002e11000ea42c008039081c1d90046100389010340c04008241d0072007500e080c444d04101045d128203513a4083c0a1095042503100c0003403140e1522203a04454402c40a91003007103505840e0301700140505020f903000750041d5001100044c0e1a441441500c0c156000034010344030b040890b000440280d00040c0045925010810403061891041e10030044031330b10130344070700c1d0b20741c1c0400d0009811904020144000281000d8198005a8400f051954400c0000c41e000802d2180654004020301480811680200c04004041407a030407100c050822944000100c40c00d6075146541115091154410910258030600141001a000790050408560100300b8008026666105c0c5d10600e91050400d032103914040520300280300081c054544d4010081c20203004080c91558006c1ca2380c968111302d810101d5a03284010140242403110b1561182c004103000d40741e0410500701c0580d00e12110003280404c1c4140d45280c1141141d008400140100070050f1880620000c03090700a00394504030502c1056 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 4743766 1250 4742516 4742519
    0x12020c01050301090c09050d03090501020105070311070b0403270311042717040603020c010c0503090c01030f0605030a0308090c040b06030a02030702070f06030207060f0203061c11030303040303050a050f041713 92
    0x1c2341e881aa0210700d02a070f03503103c003540c9800006821103502811841c1010708111a800340707508040120b49115a0200b000001607490f420222400000c035400340d10090340c002081480880f0608102064901850040580e44030703020801c42220656030640911f00700c041d001989041d00341d211440c5140c095101800c490703040e076003180041d502ca41c00110109a01198460841001b40b081c17803205806801c026255040101d410f603070310155440080d04068580e0258110703d207a80d00300b000140005030480704114110325000c1d100c0c01c02220003849600c100583d0684e01d29281c041c3c40401a4003034500c40c43c5480708074422000e0350004058a080d489981c5000400341e4080784a10700070026aa00140c5405141c0b43c10002d4412180c007441c10240103005000941c0d44100814007800203e448401580c1d11600d40801011610021280e05000110401c03060541680015108070079101c4204001c0e5610b280951002c1000c0c0c401401001c031041e4549000c210110081c03085603800744131007640308d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 4745016 1250 4743766 4743769
    0x10804060209040c110d0c030518060d0903170f041106090f0901080f101505120708010204030c090c03020a080705090301060806041208010501020f030f030a06030609060912020c01050301090c0905 86
    0x204e1142c03600e8000558002c155115401d810301a8107150403580ca099070912101da1002403040c0140180ca0401400b8003080601036980c1c1c008031407464110880070300000c1003a040280004402044c030b0061442d1810000d00403030240c504140c8140e5001c146119012140428060150401d4017140d810444c10168444a55204000107000f485d004001780688050403003480c0c20301c0001d171000442c45081441440d44810314601190658909036000d81512a201c0b40081c507003805903210801c154800140807090200c5054004141c508002d00dd20520110f00d208400301c1c442e455101c0e000815010100380680d02c00c0009000c0850001c0000c100c0d1a1076202880c10128140c030212441001d044808480c150004589030041c1000d0001d40080704002c084181c4030f101c0d10200352103000e0000b0020b00300c0040c0e648054040c0d5040602000112910719200c801000b04a10035108807040c020b624426910000c1c64003045201a940c181c02d60346058801c1d0040d0281001920a01424000210360ba = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 4746266 1250 4745016 4745021
    0x90f060509040501060302130905060105190e0106030507030c0c030e040504060b0a06020a14060603070b0309010f05090a03020106090506010c0b0c0d090506100f0b070b070c1704060e0603040c0501080406020904 92
    0x10b0340c00f036400040d04074070f1441000248482c03440804c600701d080828220204501089150441c0c0040c0c84020110b4903040d200c0c0c2c0422075540080c201825104004500264151301980c802d20494808105000c135442003550007518225004001030056030b66035259040c02d42006812900c100d001091480c505000115540300540014005074007400442c0c00b4000c29100300200b64003d0005042107052403030200351034050900908504010000108034064400d40c8915000807040b64104682c0c18040e02c1d4a4031114444025401982025400700c0c24000700e10945008a005031242a4101c26540d00c521024000810507602c02909020a12041645000360440b840c030841c0030305514584400500280c210350b030001a41d000c0b550360144108090781003241c24a98100d10065030340d0756210000c50740045409402450485d0744030b00104000440009402612016200c107005030740303400700307220280c00704480141101f00c040c0c000700583c0d400781402e00d8000340036560151501c40184089401d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 4747516 1250 4746266 4746271
    0x703090b03130201030f0507170c0702040908030613050106120b030c040f0603140c06072013021b010207020607020d0201120905030405010f0509090105041a030a080a0306060f09090f060509 83
    0x25910b205240010441d81e051142c4d00074024920410003060411640c01003034014410b82c014000d20011000c5800514454181d49859030b000300103101d010003038940402c441c0c2040d242e081c01507614403903004c0d682c0c0b0280501410303608039a450742c0b680c0041e880c40001910040d800d0302d0701401080f82000d007503100d0303020707082000300c042e14041852031441c03078812007405c80d011420000c1e0700070802c2a88555260030480d4a0340b07801c82040d0056588044030403030900fa0341c855180c2e00035a0014101d1004455401411512180d110300400c13103412030306254241c1c45000070096100a0405c4150018586400b590343c42d14010714008103a00c001c40c0c03200040b217a000300291030660011808020542c1d0026552107259518900f0505044507480070840884c1c046c0986849152103c10f41c1407a000c42d41c06a5504100050071206607402c14100107034a0380c0030561040001c2d04021000c01c0305400340001d0340000445aa400c520989051104002410a8001c0104154842c40d0004881d0b0b1032141c2c050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 4748766 1250 4747516 4747531
    0xd121404031509020f03030408120702040f02030910050105030a02010509060c0102040b030a1a0a18050601030f090b04051203040804030b06010c02040204030302030c0709150521010203070c0c05010302031504020703090b03 97
    0x5010f980d00c0c010450b0101e69103e16510a500401080c0b00d21540402d40054070381090340c2040d01ca88003807000074003421364943c89000561022081000c1c0c0c0800040b407a6031100d42c0c00b0100701e143d803200705041d280d04e900e14000c1d011890030803442206081000040c22005951000141065142c45201c2d805900c2543d20328081603c40c040e541c0381c20380c40d90004c181c10750201d40c0740d2034080c50068080164110080201d440607560f40028038542d0294005921005240b5070410900c0c90074900590740d02d074180d4040e500c5126071841000e012500a0849000340d03003001c001802d1910f1981d8045c003080e0003c28003810491006d54060058555001800280d0700c2030b005503803542284188186003101341c0c2d104900f100c0c1854000ca1482d00d1905004080e1401580c45011104004c443d0100c031986070304442d85250b1000080101e0540d0200340e0740403d510680342150380c07503034640c0110180c3c0002d581da60340e0703d402c0038084407141c50b003980100042d40c0303c0c0c104002c21035a200c000343d805410894071003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 4750016 1250 4748766 4748771
    0x7020319050105010b1c020c0f07060c0506010801020315090a060b03010b07060507030b010e010f0212030f072705090403020c030a05010614041103040f03050408071508060d1214040315 81
    0x5420030a0a00481303014000009025003445103804048058201100c500102e0580c001110400210b05211305254005244119040540e0301e4000038a0110200c0701510385015010010500ba103042c003c9a00401c0e100b580b4508225009040052098024042000e0345944410006a20310810040c60007070400c00e414a4480456003411425034078000c104008040c07601c6405142603030010080c4105080a1a194030b1850f465041a80f41c251030000300704400c00048100800c80d114420304902c62440c81c0e840c3c03207034851000b114000d4032154a0002280811044c7e040c400e506200364034583c8140248100d40182c156100441c3c201000440296002e944601e0b00780300c080c9000c118002122010b840c10410503822403010090380c04050030041010782e058103d00117042c860010f44010308010b106032401655242182d00001403680000c102050b83c8034001006864900c91060010b60400d11428480d10b900b1800c49440000c1031161580d50000e020200114110900b46481040b002c0d400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 4751266 1250 4750016 4750063
    0x50c01030c0305040215030c0d050c0a020111030705120c040e07020604020103050105030c0108150303090a09050402040b0f0916140a0908060a020403051903020309130c09050a050f0105070602070203 87
    0x40640720a0420042890b040c40d00380801611105024440300300c2c03004403583c0703030f440d0340300c0130566880740c110158201400c180501c500c04510740d000b480c3c0d101343c2e90001c0020407a000d5914610740400c80302c5401261080c4050500c02c62801c00c0f00e6808194115076500c2c241c3c441910201810095800c4801644288204001c550301803040078003400c0224004d10340900d04100090200c20000c00340105104070301d46103406502d08100b9640c01801c0240b400e02c540c0d464150002c010a03040b60168411030500c50400c00034200150300c1130500001610034141c0303682d105000c1c1509540d1148050402035150082c8420001010150032458410b07603c00150600c3c06000e146020005084100035920400c0104005640021800b680794800c8a0011030307481c0e103003405e90450042c031400c031f82c010000842d10390003c1c0240e4001d020095031398583d04001603d4000b40180900a4007035160848a0100d20052560280703002d000164860640940b9040542c0e010a04140d08582c10005000e0f00020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 4752516 1250 4751266 4751269
    0x204090f1413060b0f0901060c0506060607030509040b03070306020c01090b010b0a0206060108191104081614010c020d02030109050616080708061005130e010501090918110d0f050c 79
    0x340070141d0641e491415000d051040c2080c580718414074008080c144d4601000c00d490300c500f114444140720083c041141e541e0b4030b00020300080044c44085510b409000b0000b0254039010090701d00841e09540d075641004a80340c2804014101d4481640d403500c50030400100081c0d1a00090040f07121602c0082218003240c600094100c60680029840301740901c0400b100940c00201d02e5400b40382460700c00c0c0c65454421700c039812001d4504180080301d0030410104c20f50150b140090040312524011035041c240380c00e4030605810800d01442c0c0e441c40961060044e698410340d4080c0c0030900041050b8a08242ca43c00242110304804040300e007074000cbd401304000400500044d25002505013401c625601c0c1c4460002c003085401412284108a000d0300d004c1d49512610680382580100d540c0c0e4a0850740302c0141c0540988244100c2d4002080380700045280b170b01c140500b17030000c616000c05442086003551840a03501e608111035820641c3c0421a0000c1401040ca01100034081d03809441458040ca0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 4753766 1250 4752516 4752521
    0x504050c011106010e0f0c070f06060608060303270f030a05280c0605180303031005100201060b0d0507020c030d0e09010e0106080a050901020d09030e030114071b0c090204090f 77
    0x101400c01c540000e40100b04804540e60a9641b01c80c4c1c0407120210b40d40c0d040b2210030503000707640d4094200808091804e0801c8220760018040e031380607455042c41903540400f0595681303d410160200120401c404420701180740440218924000304903070880c0000d81c02191424520000035112580402c40358400e410b1504800946000d400750fa804400110b42c032804070b0059684144420410001188076104c1c507886460070325000000d0942c3d0350307400c02100340e0f865404103008040c80381c0301c260100120309005100d00c01c04c45015000c10b40c1000e4410440000070400104500d0650055181101d5030f07503000d200c2100e0940c21502d0b410300868207030081c0521004141c105800901541006001c03e6800094455000c001c0e0040401c880d900c0900712406401101342280f406800d18600e4000c050300f06c802c0c0390513410242c0082110386011801090341e41e905903403c0010803a01200901c142c090810180300b0b1500501226030441d80d01e00741401240c0c4a40e00000702c440ea030304003050b04200c060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 4755016 1250 4753766 4753787
    0x5030f070207030807030507020a03140105071706131e020403050d02010605010314010909030e0a06020304081506010c02060708071719090501080a020c0a0501060603020307020609010c0503010905070e040504050c01 94
    0x10301c01450720504642e982c0b0801d210b41840541400800316091085598101c4840b010355880241c00d0107504102c0d90b000c0c080c1a064412a010507100569020029524a000b0348600c0f0001c041d400c2d0b030764280b1960b100401da0703900300c4440c032040c41c1e030341c1036101b0039500051008620403401040b01c0b1441031402402c481c02c03504660b0415040c10890b102e005030090801f419030f108444005051405858151003400400000c141c001c0401000040c005401102500468894074295030b032501e0600d40e0a6180c020407200c02c0d0110303514420649c054100b1034041c1415510400320103180c05c4840c3c0b1586001c10414400740d41c0c0c3d03240000d951001e0f4403028000d005049844c00c0101d403050a000001c1c00454004200781d030a180c0c00304070600e020104004100c85103400c90001c00c021602da0708020080d40c0102c42400c0580314950200c1e01d580302c14403076682440419550181542d0803c034010000e42405410f403010400300308070142055039140704040c004c40c0301c0c400030408000c803078002400c0c62160b1b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 4756266 1250 4755016 4755031
    0x40216080703020d1b23010b0d060e0706110303010311060d09060615020d080a050a1d010501060e0a0f05040506010903050105070801050306070207080304090b0105070c0906080705090106020a0b040309080d05030f 93
    0xe17074000710005840307001100c40c0422005020608042c080c1c901500401721403050a520004c8a0050300c01e2260981c054003421000000351581141c40f03820039100b411164480c010729500420041000c00d030030a01d00302101d50010b114625004e84605944103441d200b050940d581c5a42c0c0c2d00c100000200312400110002250019080703c403110500503258074030040c4a807014984400024100c0884e0358888101800c8140301d84407030790285c0b40001d000300024010b08020481260700c045440c41e2100c685000c82d91002500340d01581800c042c00040c00002d048103050200c624000702c000740081c01098424034465480940340e41c074181c1050301d041d402034945002d64010240602203010027004440542d5600c54010543c50407610040366244200070005e890892001c0700071907250f4494008104550071030013200c02458542d01080542d00c028420313440541d02c1180d41c90005070750440030035031150007400c0201500f961071842608117440c80e400703500042c07000400c00039081001034000e85c11126 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 4757516 1250 4756266 4756307
    0x1090507080a050402010e0409050c04050108070e0403120b060703020a030e01081608040c24030f05070507030e04090b0109020c0601080708030406050304050c0d0807050c030c0a05040216080703020d 87
    0x34441006050120041c000070b1996480300002410359010310010b403e00d0320040c0040040107540c1c1002911800c030070315064815800c00000003020580000e003141550340c499030000c140d40b03450303500b071b031310807440c1003600d0140354580b254030023566500c4c0007401406010740c025007184d4074a49002030106580029541c10301c00b0300010f00010078041181a0100004da00f8101030a85450501c4090039500c0d9210641c10502c080d0a05005038004401c00700301c0740203032801d02020380f800c030f16501510340480c1c200d000a1018001c80c0301003849190280d814a401030030014160029440d001180002600032600c050b8002820f042001d030b04000c06801081c100000e4a040c505241d5025224070581c460b08040040100206040c02002d02c16550890f000a09034003000003640352803030250b0450202a94240544088503100e410089185035400340c00400c001d2242e400d1108200080d000f0004a40c0120b003010600800a80820300038164140207400030140300e6082000145081c0c01c921001a83c0d54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 4758766 1250 4757516 4757521
    0x10506041103010603020703030b03060103050705010f0807021203041b03031808030c0a0b0c040f0807060906051207030c02010b03010504080c06071d0603060427030905030a05030f09061308010c0305010905 90
    0x81c1c0200c2034a06440302c62502580e24505030074110050008440c0c02540341c01008000010080300080c0d200484030700b0b0700e82504241e1944d00c2642c3d02d00d8101d0f855009a00004100200506040000c42d4000e01c105c2d244502c1200750300303201e1102403039a003044001c56104588007140d6003d0124640003010003000031403510301e05100054503000a0f00c4018044051a400728104060407000d03a400351075124032104d04141d0b603a06c1d0580c0e5100307602c81d200c0850038032076000c580c0c1e91003203085078038891002c0c8600c003441c0c030b940d81e04500400003610740400715540c03010b4203030b904c1c1e80038007441c9d000c0c50140d00701540703403540b41c1c80d0181031800240581090240b4150403540c0c1d101207214000a2070f400320ba015440340d46102c04200604a14140401c000045d03c4004100d0320304c0700136100f2024065640e4000042c0c96400f85590f8000c9004007038095401845001807402e0640010078aa9402421140c20700e00360310b200c12002c440d02d07000148565103445442914540c148120f50041800d0101400b450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 4760016 1250 4758766 4758791
    0x4060207032303070302010f0f020a0c0311010608010c0908010b01080708040303050405190807030806010807050708030a02090423070c020901031101020708061e0603060906010b03090a0f0305070501050604 90
    0xd0189200081602ca1a49840038001480516079585075042c0c50a41e640d41c4000e150003402440c10403081d0300e00c90300c1c1081682c013141192007a030b001c000d40d80d01c80c030320300c625261000c0e0ba2102107251911159900c0d48400304562000f801011003510329515003881d024201381413142599500a44241001100f00400c02180e0b0702c0410160420342605002032942c640b03062150034401d2001c0a1882403880640900800503140e00030403c907402555502101c1e11a00011901c004040e102c01000601c103101c501c0c0401c0041c0011070300194007076401440c01c2403900100d01550003030603428028040900c8240c1b102900c004c4030300c1e03124140d4600201c42d0411a80050480581030101800b24a081c801a41081e4000c100000160031180111a010310740310b0443c2031070140021241c44001801000305105003000141d050180c940100602026030070410300b0101508014044841445281110004039030301d1024126294040c0da2440c1c4e07200c80d941050ba083d103401a14141c025442c0c804000031700c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 4761266 1250 4760016 4760023
    0x503010509070b0c0304031a040308060409020901090b03030409140105011101050f1501030902090114030c0111030a05070309122609030705190308120a05060904030203040302040903050f070308010e010b040602 92
    0x43e2046841c0b42910752850768051440d601076500010120014800c241c480c101d031010116104510035513807152199075000c284400e4420310280250003044a100601080b407003038005140d8200c0207002c03207007000c4d616a402ea040c0c1c1c0c400340340b403400160140300503c1503507407203400940c0203002d45000780018280018210204800142a01e80e065194000c83c9180d03882604501c0009070003c0080c0d01e996125a141c001d0282982c010a00c83c1c4109001c03040e665000328851018001e68401640c1443d500301010794503540a40002c50400080e100042050141d0000e0040c1d01030060000800c400500c401710803200c00580420a0a81820300403000c4c47e980004a01c02502c5041d034000c280d40320540c0420b0484c0b5150780000f44039038400315881c04d040007205000d0b44103041541081c40b05490301030511039234000c02d5402400503001007201b803001d4201900002040c80c40303442c02030320305104004842e02541000504a00103035880c4010842c800c11001c409001d401d00b070303030f04034501403400001940c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 4762516 1250 4761266 4761269
    0x11100c08030402060409051510030c0203030613020403080309010c12090803060d1104091103010c0c031e1704060902030f030c03040608090705120a0302010c03020301050609130905030c0c0a050301050907 89
    0x4440000001021900c40f40c4c1500e00800709402c1c20f00441c20f10f0310074040301c0900d40d030031107014903040701129550b6803090080003005480745e00036516580fa408280b1100e100d50040c01c00780c050b020000040041d024000840c0f0071246c40d40002289021031000600501c25412031003030b568200070400c030100700710b81e04407500000101c5080c80008402d16003001c1200740c04142e141d129141c45190400d10180039000c03081103404070000c00c6841e01580e4283d40c03c2452450140000e8240b10013003520722210030004100c1c03001428100010701403c0b040c1c00616900325000c50b003e540300c0481c90114101006000070b0800c038034014504002031184500e949011314404c600420441303602242c0f48180c103000100181c580602400302d00c1c040140c88a42d10340340d00f0b074101c005602e005c2903400748612910075a8141c03003004108602c0c009003c0c04020b100c5802d014010380c02d9a0f904070800000b1000c20091010306108030280100725101c0c4c04005000e8055031002d4040e904040070403035000c901160600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 4763766 1250 4762516 4762523
    0xf05030c0604121a090a020306100e0c0d0219090503150103030e04090201030b0d030906020d020102130506030403050904050f0a0b010e0604030f0c0b0408010f05010803070b0403031d1911100c 84
    0x98146a0f42001c981040c449138501d080e01656030184050550003060f442e030340718001e40c210340b4180c8800004108113012031250640340e0390303d54045080070400300c00401c80b00486900c00350414034040420b600110468182c0004500f40c02c40070011350506005001c50040701d6810f041180d032454070054009000081c032588030395550341144046a000358040c00100c0f0000c3c120324898541850042c003807241c41d00903600548154001d502d8458414001c03207261150740b40c0034010552514082c0542074001900c00c4013404414807183c0e82a45840c4107071482540c040746c4070421030410000305022100d03540d04950401c00c02072003200081c2c8441c0100e1b421aa0302521110303184200341025814110f00750000c002c005400940015802e01c1501310035a0303103030b0310b80c820000c2d42d0f0317642038003940ca00c00c40d0f40c002c0c000070003880000c0c003103802644100038111106901c4500751200c807050506280d0048035500c4010380040040c400c0c0805083c3c00561002c00385c44060160034182c0000e8800c071000312005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 4765016 1250 4763766 4763789
    0x603090703080f070605100602100f060506031303080108031201051201020702060d020301080606120a03030509010f020a03091209050603040803130b091e031c05060a030203160f05030c0604 83
    0x9115000200842002150008902601c42a91801500700c990107814151003041c20800401c84040032503203100215420390700108000388101d58030102038011040c400121551310702d000159525086d0056100c0e0542584502c0050818607002d4148941a001103910354401c4c8013003203201103541c0350075040d03800849510b9650541d284c00140039202c0c02100940104011403400310420f0b094025506075803140d81664003943e251018030142c2140f400700b1105590200c041c0c0004a80290700090708a4422000401c91001301c2d4180801e90380040d01d00780002e42e80700002010302c4400f04001401c0c800603d002c4070729a14120002c1c28501001c3c102070000440007004c6050010150382024480760301ca880e50806152601842d500c0e4103220018500038803448240b2801c5c03160101c12228031040080c280001100014120001003000810b003d0301700141c0903011025a03400c1121003240f084442000f030046040000c00e0040c008650700090084d8032007100c00c03040c1d50f915415201910340d4003100c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 4766266 1250 4765016 4765021
    0x1090b0a0501050c01180c150c03050a0806010e0a0605071104020a050702060d02040e0406050105010807030b0102030a11070302030307050f070906060903060c05090406090b04290d05030408060708040201030605030307020306060603 101
    0x803240140182e0846c243d01e000c8049000b41004603040100c011140070302e00c031300c860001507007058942c4d0300d115800800003001001501c00040c099114150880c0040c900120440c00b10000b04101032030603002170340820340100c0c80d02c00b000034040ca03810950406640c1581064419a00540f80d4003990100078447c020109199803c4a00c0d981502c00030002d1403050007590401c1d0401c2001031030280255400101d547c1c0c0042c0d0f0440c040c0c05120321454040c6d000b5464000c0002045840c455107441003101405450000005603404002410400340124080e21405405d0094103281940c5031f4090b850302400d0450800040d030700504260100ca4101070086a0010940b204850700e2040030842e542c000d103064004103680400d0740c4150000002078504005016402d000c4a00d000000701e410766042c40860705c11201130410110501c079262040080724201610780d02d10b941800d908581c03200c00507441707a040205569040c001d4400500d42540a14940a810740110340ca03204014411802640004007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 4767516 1250 4766266 4766287
    0x1203110601030804090501050904020d0602030a060b0c060105100801030308040b13020607110102070902120c0702060c0a030f02060f041101030b130903030518010209031005100e041202010501090b0a050105 90
    0x1005028000a60240e406668503850b0402c000c0e0401d0086001c0d40c0c0c600000862241001007901d400f0ba0340050002c40c0400a541da0b11002c1d40c00200340003122501d0f40320001d8410f0080e000340c55030100d5107001d001258180000d1009881c0386444031020001e0032001000070a400002083c0c002d900000103041c035a81c0c034010034500c42c2506500a4200c9000210f000501000c450840b21541c0240d00780e03031f0155610180c0308103074015000310444440098010801c4151247c00400000d07101414990416440ca0349580c10200720a1b0240d01040b00e5601c150540c590501003d9400705608061000c0703801c0607165103030082079240301c06d81459668194514190786148568400b1b5060040034000d040051400402515094411410754001d02c0029a540d103010b000765490007070084c000b03042139410b1040c1c5901512000e000b1143c1c1d00c243c0032010440361461940785104900450500200300d446e00802403c40d14142d101e140d110740703007502d4407845a40d019459800c0395024603095443e009a1301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 4768766 1250 4767516 4767527
    0x8090703080a0c05060108010e0309010c1104060b030406050610050703030b0a05040c11010e03070206070b040c0302100302070302060906010819020118170f030909010306022a0606030d030b0a1203 86
    0x42000c1c1400c2000718244684079800341c903004815101d00e0550314203903a0303850054240d80e40c2103190500c5400a0180c04c1d119441400780014550189042c0c403010080c40010400300c400c6a0400600c02c1d600004100600c00a03006654000e86c00b503031500025480450000c0140c001c00400404040c0c8a40302e1181d036540340c140203000740000400401403100000c8019005035002e8038106103950038083c010700c3c51580482500c001d00d4015010f18a4820981e40b00445284000c00407101e07000f1001c400300250321410b42e50f5202140e56140113070b0301c031a2420060301e03040c2c000301007244551140e00103101402c03001c02c0c1d0703035602d0b104046000611510b074401a141d115050340981e01005102c40001010446584240c400c1e1683c0e40968240100ca10343d51501c074030400c40d4054202014000400000314258003d01d00000030354102c050380c2451403c130129100c14603900c07403100d0f481841400004d140611018002d01c40a0030f003084a00740c07070300204002e000c5600c2270070003600d480107842041c5030041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 4770016 1250 4768766 4768769
    0x702040c05030601110304030803010303270902041404090c06050c0f06040c05090117070501230a0306180603020f0607030315031202010f0b03031c0209040c05030402040b010206060907080907 84
    0x60051040280060004055030401c8502d180026507aa611100142001c0219001d594000096914503030a43d20180d072840c02226804500901c2c0c4150f8401500c50816104003a0080340c4000d0781d41c511b480c01c280e42031602000014816498004802c00045420024004450301400e0a0762034103081402103040c890102c10440a60241c0d104110800c0700d100780d08410740d04221400b015598840c440c240c80103c0b500036a5619511045017400740750f019004140002d280c00d900030110810b410840320541d000588804007103a12504141b16521007142002c00c1c0703c001030420030920b032079600020100011394403d9801110700244030414944031b6080324900d82c041181c0070180c01c1c2d8902e005481851603084400c019480d000304504414002d0140201c820801002581007010400c038001a400e03029808080c1c040c2d0800413400c064a90707000300010115152140394072071800d030040c0320545030b40401d0310f41190040420030505035030b20f030440c941090142c540f0208c26a22a056607107840c040307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 4771266 1250 4770016 4770019
    0x507050405060c071802030402130e0c0a06080a0c030213091e050106110f0d0c12030e060109060306060905070503010b13030204020d02091002070303020d030905100f09051209060904020309030702 86
    0x240310843c0c1500042d40da800c030b03000140702140a265183c8071804901050b40d00941c44012400030140420342c1d030300a0340400515006581c0d050042c03400180a860060f440f6030082400300040110b4080c1910403403010001d54201075180038461001501002214003031071903080d960386003005010042002d500703290f030303903c410030841542c48243c003802a29140403402000d100d1003114040d40d802c003003005406c1006580707a294083c0c2c1c4076070322030307290640801c494020140d039282c0607540b9003070400c591303030081c060b200c4006802030039420540d095640302c1c1c10400e281c2c1c0c1440103007ca00750307211045a04441c50100c5240e01c4015000303a50781090315a40c0013940c814000b103040000c2c214541d0042c400320404948980c50000651000e03030721a0301c07134070001d000340c6c00c91000c00700c1c0f00703010340c02c8504002d01c20001e54a0b5070420440b02400c03906045014100c541d0b41c0c6602a04200041100b221174140341540309050200800024545114032505980680d4004c00810040d2000b001601c0600c2d0b030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 4772516 1250 4771266 4771279
    0x606030f1f020d0903020703020a0b0c0706030e0f070e16051206010f02030d020f0301061d01020a030e0f030601080f0106060212071b05061b070f050609040b0d0f0804030b070305190507050405 84
    0xc01e400e001f03659200b01d02050b8444d20301103a00240c40c201c0202100c881c51070400150004a152502c19801800071201c40c44c550300a054130600501001d11501000d043d0102e00c808175070400070040700c0c542d001001c40c04103001302007051240d00640b05144d107030310110034078028400e1150050128294050300c03d400060b03d0000c909404107000f102c01450684000d40e031030900781c3c3c15010030100d0f886001c03d01280903801c601404800b1a00c1480b00b40385004016105c01212086080031030b2070010241c0c812042608020211155140c003070040720000c00c6184000c00c9407949005042d6280d100e0000d00401a0510086001d80c403100c14034004020030001301441d03203070000c000c0a0241c03850700c030813041103d024428021928005644400042e658050421810308800c10240402443d002e50b4007648844100002c0d000241c203940c1003180e4610440c001e070741303a600e1884c0024040038098208000c1c14208010014000f91b503150300b910510038401c2c0840d81d41c0b5140da040d2a613100b9070708400d42201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 4773766 1250 4772516 4772531
    0x307080703030509010e01031e0f020415020a02030c01090e0114030a0c0e150307060905010c060902060705160e0103020f0d1401060f17010b01080c0d060e07110606030f1f020d 77
    0x542140280c000c0304c0c07080e201c0d1001d07205010011000c680c50021610b0003014100d0740c900c3d02401592017012000e0417100010b1074580c5a40d44032038200c45942969005074083c1303040c40700b182000c0c000040441e0f002c1c2080c00c2054242102e02d40d28100501401d03000c4400d4840e54185035408100b8100b800350041d0700d0b280c0d101e4403640c228540c45400c840c200c40d0412545400c030003500f40082c0c10002c070794150f47c800e00e21900b00001110003000c0c41e441642c1ca241c5032110f00c00965038141c010055548100c0003000d640c00b000c495503151000d10703440134464400c4800108096100c2250240034800102c1d030500414070076184c5a0001240030785101c1d400e40c17910001041a030090701c1e101d03081c0d6107141e06c45145a0300b02140107098907403190f41e1500207104d110200b940000104041c2104d0340c2070740004103105840366102c0e8841d010444200300041c1140f00386e40310f002d40c01e0042c030750000c40c10350241000c81e4406100035070303820f943d045555041c0f480c1c1f5103540158006505860080301902d50912106 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 4775016 1250 4773766 4773773
    0x4020d0305070606060e030c0108010e13030203040806010608040c080102070302070506070302160308090406080c0307050607020a0803030a02040905010e1308030618010902030a0b031b0919090b040606080d0507020904020307080703 101
    0x40542c910780390700238499010440784540c01a00058120786051280880c80d03a6140a40c141c60451402c007281581b01c14000452107060500401c1d000c0c0144e80c2d0358120a10306401c00c1004488280c0c44070960380d20403c01c11010960105010059400a6a070749540301500d2504070704d0291003900c02590120040d07000320400560600800030352000715000d006494542c0040b541b1005079400d601e600d030f4803515003000507040010140000600050025070142c0d6203c04082c02d41d03004a440000c040d43c0064140b00c810390902c14240507240c4082c072030002d4900010700b0b15480c0140b5102400031800031000605640d10445042020141400344220703a50f506d40742880603410564030150943c1c10b16005010b10b04000552074000e81640e8801d05000c1081820301040c00c4011b0222641c81c5401c0408a12244040c0034951503070348103610204451601e41080d000700d0751b0541114445800007408a900280d000c426910314640403100d50310301d0b417034510000b072502d40950301411a9014840000060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 4776266 1250 4775016 4775027
    0x1c0c050d120e010204120b04030507141606080408090405040602040b0c0604020a050916030905010b040e030d0f0b0a03021203040e070203030403020f030301050109090b01021e010606030f0204080604020d030507060606 95
    0x20548140642d8001c801d206081c4d025070b00138694000414001100413032840e007011600b1a001303051140c58103515480300c07000019866098601c95100b4103046201c010350400c05802041249801070041c01d0540d07920740d0368411040302620480d190030100e030500c211a81160700a100102103543d6071480c041119403202c0301114180c0c801d1144020001c0c51341402804103201d4519001c6116030324080340b00075801003040c598296403542da182d2070004640c0342c40c8582e080b4014044025030b00c0d0f1001c0410346042d1400910504101c506000d0b0002caa500c580e0050710039298110b130485880040210340b11b295009a5210003d50103104d401d0040803a0003000450107903000782e0a6850020840c0c00081d940d20013803140c140042d140080401c11100d03958041110494144140e552080505002c12400b5200c6022501c49135507460301044541d40610480015008110083d07081c603103085081c0e130700c43c00f00400203070003401d02d00c03c0c9004043c07284003140d10303040e4010b60400c80c40e611504010700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 4777516 1250 4776266 4776287
    0x1803041203080109050103050a230625020c0105090103020c0a0c120209090102070809040b010c0b010b0a0f020601030f1101090e040b010302040c030212011e050301020d02030a05181c0c050d 83
    0x20034407650000c134244c5403900410341642d820800600e400744e0b050303071276181810002c0c002010300080803100c2e00c92180140076403402070940e81601407807041200c41c00042440184445010b544c80007103e2080c80c0d8110b011350318080e20900300140c80384a10160a810310182001c0100030185444002c10700e00814003441e40c60320f0080d110550660354407042e030380c201c1c13090314405880c800c8140550f504510300340c0c0068540c44c2c81858040b40c07054003a43d0b5606d400c0300c00e8006520208021448045c41903000b030b61b4010401c9984003c4c800341d45183c03034284a50040c3c400c064140944044282c2c62a400b40e522034006046025100c0842c0c030702800d0010802d03000380801c80c41281000d001c021801c3c401d0007a04c1c645004507020350f0f556441d10390310321211900e182c02401014000c0d41c0c0000c49139020700c040c010310380e141e0401583d01d142805101e01140d100510b450044d054003034024504c0040002d100c1640c1c864404e00c96072100ca46a4107650f4000c040500a2a031b115a503c40080e05d5401207400c1c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 4778766 1250 4777516 4777523
    0xc060403090e01030506040f021804050c010e18010308070602040803040602010c08010e04210311070602070c0503030f0d050601030615030902030c01081e04020402070204060f030302060f011d18030412 88
    0x481ca580c40e019102c032040d40038400640795038070130710200d004650180e943c00816403004080c0d080d81e4000d4075405a121030112015280e40e003041d4a00c282c41d50b0030401c44d4900d04001c840300c2d955400205540c42c01e428041c08003900021010400a003080825411a0301070a0034404a030740780c0303685c2c4100074060504e40010788005a50400006400e03101000040c6c051a0b11641e038440300d20fa520110203400300b10141d51000c05807034130983c400904034440185034550141d403025a0b036621030b0074920015042c1d5845203000717900c01c001c425288070005c0d0a0b40d10300c0c080000c02066607101d000040300504019000300300d4485030b4010003454560154803194003203200358103940650b0300b011f00540307074160200d40c600103401e41440c200040d140c0070404158402c1c4010001418020130350082070840e4415040110840c175449403d02c24103404000e01a4000e074807000d50300080d0304060008040744603500941004016203004950100d0b546100c03103442c11040d20469441e66540c3e122401071040e07110040c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 4780016 1250 4778766 4778777
    0x10e07020d0503010509010302120c06030a0b0f0a05060715140f150d0302030d02070303150305031c09020102031e0d0f0605040e03070c060e060f0412060e0a031d030a0501020c060403 80
    0x22040342c000c00a0740e04031040140300ca64940e00c1d68081c84080703a28240c04031104e00402c40b2400c0c1a41d03880b00a5402a1007403000068041000410300030040074480c0c03103a03c0342d0b02c1c0e002c040003140d603003a003183e0485031b01080c881d11034005603a40304050140c0301000c0e046442c82004100d10b42e9a4459070604c6028000c0b011007985001000b400390104a9150150050b0002c01c89980700e05039540003050498032038a8001076a5002d04018001c00115810441e401e400018604040c0144028107044074003000c20208004200c650002c0d40d40d100b256071201c43d911005102c004a44851001d4641c1c0a030316040c180010132140c0f00200092155001e020b100b58a406040b946818000056414150317009004000d040d0500c502581c00d182050a071a50203002005900b12488100029000605e410a001c1a900b0702620345241582c50340b6100e0b0380254800205a000720b94420380e421b640000c0d400b110403400c242207010a0500440c080e01810540c00020340f00098000002c12030301c00d40c06550703207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 4781266 1250 4780016 4780033
    0x100504052803140309030f04090b1005040b030112030504030203010e0607030513021302030a06050d05030304020102070501141206030f03040602060402030c010801030309090c17040b0a14010602030d09080c06010e0702 95
    0x3800101c0840000a0005400065030701258410b5400454010f9200001c40e800c02d07002e00c42e03d03c1c0da58040d4100e604481e4441c19402d01c5806c006100542e0381c3c01505107141864240381461209001c1489102612014500320f0360030725015604407409180c025001b40404414400e60301e545140544041001074505030000315407800007012085004d80c000d101c2c0003242c0940c02c0100182d0406001a40165a2084001a982d03a40e00100303c806116801442d140c0c58680006824000c10742d100c00d05024110440340f10714413080084441c1200c03600201c403155201c080c00b292a000019490385010b00c4001400b09400e80c0000301e140c4903510840444040b40d55072001161039030804c0c4001404074801e004188a02c0500d81c00411144480313140c9038180005414140806034001e8402740c40030032803074060140d00301c050300441c8041c150590701009103502d030a030000d42c1c80c4034002903540d10550749e40d41101007058803001c9901c0c001c2e03a10121041c0e940c4400f00005583d000341d62160152052042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 4782516 1250 4781266 4781323
    0x5030607020307020d060b06070c090606030510030605070210060909050105010801020a08130f02030604060506030613030f030c0c0803010605031e010302030c090c0d050a020406091403060106030b0310050405 91
    0x4a0034490021503001c0e50500300c442d824483d01410803007045070810703118030403c603c50321118081d004141c001c01810b6085481c11441d441121000c3d00f1101c01c040c100070030400b070780c01c8409010342241d50180000595039260f210490410644140300e100a504082c00040c1e81d00407034003d2800a40510020051070760b85403150744c200e209120390b0300c010441140c00214400402900301c42414090556454442c00307950009052a0b0b045508a500650360024002c1904042040e95405001c68054446400c00b40d14003504035892400400b0401d034403030000c140f4441c8501d00303140000344c2c8001104e4495860f0000540340703400c01c5490041c241d01d0010107600203000e40f0105412250060003500d0410040703810700c101c0d0500200114100300c410018681c094420303200d006e2146909041c016250381c00c200c1c00030000441d035400391460082601120400307940100d5003a0449085040c00203041d40c100c030219003041c12026202e56824a004200003c1c0500400d4503461000d4111a4402c1d9010040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 4783766 1250 4782516 4782523
    0x804051003060e0105040209010c0b0406150605070b040b060109090204030b06040b0a0308030f04021c1209060302130510030902150301060305180307060509070503010908090a0f06050703030c03020f0f03100503 92
    0x70660f0b00350705000780100036500b4103a004003104401854101c0da2458513072240b80e1a2003090f281200c0b01951500ca00303000140d03100580e406040340e0710300a45440c0241d05d5080f81d00e180030b0000340c8014041c901040c81c1e070380209800c40081c41d40403825034403180d880c18544c0c1403007c2141c41038040c078148114100385180c1841c103d01503940c4290f03d02e046072113800000c5811000180100d0300521030800700b170304501c40030444541d004d201e000c04c0d028500d819040200001074a42c0031005146c01400303100d6140350100307203007429560706451000c000407618504502a100c000c4000c0d41102520b1048a2400e900c0c6000f14141c52450720140040d8880880805c045c488203426107055030024018100000d009800c05500828a10b0485140a8030b80700002d0844455000865034407400040304038041c140b204090000700208080d1712059450454003400e544584e0000404155581c40b808000034040d80c19600180c50106110340c46038581d004482c100e510540c0d0b034005071800c0880026075441c001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 4785016 1250 4783766 4783769
    0x15030605100806220302030d060b09030c030606010f0c021903030203040e0601050a1b1401110c060604051e0a0207080301060c02011b110411070b07180602070332060103080405100306 80
    0x260a1050048192115000740d04440c83c4c04500714002080700000b16461402400040c101d0020045da403004403030105444d00c81207506090003030308180e04000250782c208080404d480c1850508801c400214800140a0000d03682226842c4c1030f030803804014035a0000c09001542c500074045059502d4050042d9518010b0480d030030006203c240142002c41c01180390803504034803650080c050791020710306060030f4030549034aa40c803211001c0f6103c50001c400f0880341703811201c140e0303040019007032141c0c0c00d82c8411100c001000c2091007400c04280c3c4010b656048038002d43d008000c8079180d58544100400301494920140d0004e5501d90121200744004181c0340010703584281e03122071008050062001526a040e0114039081d001d10480b00410b14018009120303100035a60300c18813160311000351328926480d8001004540c04040140000b42d84800d06a0410b9644241140c03091007a021a41c2d0401440705689c045d4000c40000100b00304c0140301a005403101111940c401a0520354114201e4184d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 4786266 1250 4785016 4785031
    0x30c030103060b030a1703100603060e01060c03170703050f0a1b0e0301020702040e0d110706090306020304060b030d02070302100215010909020301020c060408070204050a06060f080a15030605100806 87
    0x80004100181c0300e544441c0010b10043c040d10107141e400d0b100c0c040a44401e15803c0801507000040260300140b090b6020080c00140c201005a2820240002951081402038130180200d0701544002e143c0504d0360030303210440500b050056403800d580001e0160009070351101c1656a21804244a20040d0240e43c14004d0544a800301440c07140c44125040d0082e440301c81e805541c01c000c1c140c00b40c0c80e6801070f04100c664440050510105000380205220107a0884183c10f0300440f8061260b258440c4511084079003040015840e0344a50800c05c00402420004035454451700c01e01e90407854011a03c41e044034000c46401d261800600030607030f141c0200065543c032911840005203c0c1d22a02d41c092541c1c903002800060a054000056610b0240f081e42c0681d1101000b180c860b003140b030103001d101d4ac01000c0550520020345012805005c1c0ca0391a980e04090140820000c1c2e0440821f81c4070a42c02204114094071907a524200a030046c070040d40c40071105170091401107074410300043d10f00d02440e030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 4787516 1250 4786266 4786291
    0x1020c010807020307030c0312230c0405090f04060204050409110102061f0302060705071a030405010b010c08070b13020402040b070501061202010e01050c07080a0309080120030a02090a030203190b090303 89
    0x5140c0d80031600d000151f9070031018003903504424450301d41d592103113817400d41381101e007103410740e40c90409904854402800360750540c04c10402484641c980415641d0024107203070700740001d921103281c114040d000350b42101d0f4000b0315081000d0107000c0d0182c620301e0521020380075030311582c5486200e21080c1031880d8140c000014040001c10042c200040145a280e0062040e0b42c6559207407110342001a1480c0142110000d003c4140418001d0a00c6551042c08090030400582640c03965516410b004528000c2d08254203900015810707800c2000450095030b00038421540c0b1511081c40d0030b80b41e00301100613100d640c40c2c03d82c007207501902110207070030f402d405031136440b444a440001110302e640901c4903001180142000000c8a620400a92681d40c0c4a074075242005414180c0c3e160849121011514036101014843d941d186000821a6042100b10f0009a643c07150200030a00c01ca0581d0f100a405204000c00403c018051030300c0c442c0054402d072045112601c841081c0c03030ba280001c1e20490074184 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 4788766 1250 4787516 4787527
    0x31505041101050903011d06040308090a0507050904080c01050405010213080102040515030c0c0d0804060c210209060702090c07061401030308130c030212010e070504020a0504050909070b030406090201020c0108070203 95
    0x40c0a0f2024003c000030080c008203044002c1c24401c0350540c0c44401c859207507403201d810f110070190403000b00e0350b018403540028038a07101aa00d80340e07034600c00d902ca0680500a91004a420710070340340100c0302d200c080780c0024840743c100740c50014004c4d88141c109640796440b5050116851206000302c0b011228002c2020300d0480d42042184881d07440a07010544010017007016411050702408800031205440d152864286445d007001c82c2a0341c4401e04080400c0f886400c0d45145060100d946075048169a500584a0441c14085181407154480196100c20b07800204504003459500428400d88108010301c05442c201100d03004050080c04000c01141905001804200700c443c3c24242c018000c0140d05141030f80c0703130007250002c0320012000c05265102d4116940c40c00342006030750020042558110324148181038001c1031350246000c3c15105003401c002080324200204840c2003e824a00034880d924206440c019004141680f003c070b000d80110b0a0801040d07001c0d2250512071911900070303601c0c00b07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 4790016 1250 4788766 4788769
    0x309090604020702030601240c0b040f0203030f04091b08060102060109050405030405040c020d080916050904050c120d0e0103020306090103081308100902040e0a05070e0a02040b0a0305010315050411 87
    0x180040c00c064000b6400d110740c40169030200103640c0208105001d001603a0070603220314010b883e40140441c14011900d0f03a40c0000342c1c5e100c005642c8683c0108450052014500c0003e08500c12882c9280701b2440218010401e41d1140e4001c02e40301902c5524505201d0510703105448002c0304403013083c0942c004030010007024001da00860307409072142065902c0c080c3c441001904442c540e90b031860060380304084611030341d600005100d07080552030006169414810700c90110041e031901a0310300030030030103011508200c0200700c9a02c44100c01081e030b00c800c040f2194020703034403030000d03400c00c000a2910440d121903500900c00c803405170b0710242c210012a070964442d0080c5500200882d002e070303080d00e100091030b618103110603250700c207451034040381c002500d004200a44d8044100d0881581007996401d00003600001d195003120070b0015000101e0b5202c0d03203020004c0c001c035031011880d40d500150100034664141c0c0814141c9114801d031302c1100c01f90f80848000c94004550007400708621185200c5039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 4791266 1250 4790016 4790029
    0x12040b0a050408010c0503240a060509030a0501060608041a0702120f21060312040e160908070308030708090a05070b090d020604030606090606020a1101230c0d0318050309 75
    0x3984910304140b071030070750341d001203e08407031600208034002100481881004204802125820f070843c0c69080d2a0b6518080003034900e10f40b912480051100c000f858024684041c00302144850b0030200800c1099500c2d0341c080d098502c211422140c0c0f4041c0035806060010581d4080e0060a0039801010070108050003402c81354080380e00b00f102c00c40d00b44070507511180c0003004442e0301c46203480000c442d800d1800600d40b42560314040165071090502c0309001e00341074200c0040e440591250b05031909a132612054a903d03141d0742102405001e8007c011007444007240046d030007440700f40e64043d07850395454011a240c0307050800c01021b6420842080051030382910141c11002e000400d404204a46640003441c3c43d803242d071003114035039221a8100006841c070b100d8000217200d50b002030000c0488541e20001a000406c00706030500140030000452102c407840543d0289000781941c60b940d0b0720080f00c9540c2c8484c28010070700082d0902968458010f0014010040d081e80040114101103007034040285 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 4792516 1250 4791266 4791277
    0x30c010219030e13050703060f0902090f040f021903141005030604030f0e03030d0603060e0601030305040306050901090204020f03060a05010f2a02030a20011403040303050a09060606020c01020f12040b 88
    0x5000e213030446024054115442402c1c011002500c1c005138051034079202e03c800d4001540b00840043c410712a03c030079038982c1440102c980108a6000901903071042060000780280201000300310360700407240c000c85815901101c00004404c2002500340d440f2984210003502d107008098041d00660007250010340160901c88501401e8104052030043d26808a0b1840d08804011070146032074802c204103100325480b6405405050170041d0020750b0450303c0c0503040d4411440001d10069a07a80024110743e401c1d48226400340d0700420035561a01e40103203403803098006a400a110301c1e00d04100040d1907000c2d81d0040c1032440640c48981503044440103a05980d034581e05084101140c0341c90b200010707034061003402d101c03d1040403c00e9001c90007020701c100c040b6100c21814107110b0008142d003485da1040081e6988140c0c07518005c01c07113a81d00031081d0050310415100502050401602003082034010909101040e020fa080b1102880b0044140390f507135610b503400c10301c40c4108100070721072010380800810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 4793766 1250 4792516 4792519
    0x10203280902040e0d09080106060c02060f0705010603060609140106021917280201020306030a120309170405040b010806060a080903070c08010b010306090b0102100b010c14010902030c010219030e 86
    0x10324401c50740c0104040d541d04c3c00c00d0b00380c2ca400884002100740d07000324803100680140c0d0000c009580c01d01c10003504d099024100684100307404038100c41e41c00d044002303c1c0c1d04290700500070700c882641e926017000500341d54025200e20030b0802c12501041c80008035514100c940340d90050850b00304e403d00540c104030060109441e2510300314041c40030b0490480043c1840340001542c4a84482403105410410240110f0314086900401c00e10000c3c1e500002c48a4005401036444214800c807182c4c181e0080409101c01014900c1e0801b01801c41c2c26148042d00c1207c20640d07003840b50f80c0c4031030011103904004a50703543c1d01030740900042002c140703e021200c1c5c0c0710380b0000403685040a80c0d214409007101c25448000d07142e454120301c4400f0759040c01142c0c01045180070034028410802c3c0040e46038078010035080e440c2913940c09402042c0c1e1203852603183d10b40d00031070b02c07254504010340250b01900c03002d50164024411401015050b51001034000c0e1a0f003840d080780290a1250740d000c0f51550100c000d540d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 4795016 1250 4793766 4793771
    0x608060d08070b04020909070b120c04090507030603050c0d020d060209060f0d09051504050a030f0e0d030203030f01060903020603010b030403030f0501170f0102040803120a0603060e0d090801020328 87
    0xc0c00044000006000c80ca00449900300c4078a043d10400880d414002c4c40c50015810240e000c2001e518079a0507203401400f2160506903135940d01110700e03441e0081e07030710070f0158608000611a4540d016400310080c1d034080c1040d03c520607481400c0c0030200c9051840290031900c2400d40c0404110707654060b05103550014141ca144c9003c3c444501583e400c5080320942c616501d55a500c20040100005510300a1181211000346451307101d103604c41c2420200a800e01801410340c042442c4188004102c0500040001241c00c0c80707400c0003503480d0004c03101e40c41c0030f802c0000007081140c025105401281d40c020012461603082035289085504054403c50505407221080d51049450b8043c0c58064526015250b41402030a90381c50b1400c2031030020b10307000c2d0344100800c6c0281e04010044400600f403486c81a00940c640d02c0340c642c020031155002901261170450040c4245c000840d10380d0402c8807903a1030240c0f15844d00743e954203e02c1b0560f454160051026441152510340e005080c151850b0790000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 4796266 1250 4795016 4795039
    0x602010507140d060b04061106060d020906040b0102010e03040b0a020c0306060d0206070501020d050c030601030c08070206010510021002070515100506030a0f0920010f0201091a04020307030c060206070e0d030207060806 96
    0x31400307411035001100408c100d100400856a401c129440e408441183e641c1410840303034010031180305014055a0046480e60503540b1164000d4225008201c4000b088075030b91940c03804098150f030460b00c00300e0300600400000100030300c2c00041550242c50001c05c090f00c1c400181d401c01400754040171040320365540a02c02003805401c01d00c80e840c455841c4034441ea46d02d182100c0010100c84691920707805000c02d6505004145a0005a290544105641d50703851300d054900300342d00c0d0000c0c034165140c410b0300000700d04042010100d4a03a0410401008605c3c65031200c5540c808115880c3c007030706400c6041480027544045058009541401001c140050142101c0d00c400803401031842501c100340c4c6200310080495640200d149410500e284020041c01c04a0341e180120501008007002840d81d03000e000c0b900b9550203100b40c200460b400100400425070ba02c401075118074044a0a80201d6003030703041c2140d54180541c0101307800e40d05601a02913282400d4040c0e504000142a0907002158402c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 4797516 1250 4796266 4796279
    0x40c09020304030e0f0d0309090518010509030403020405060108090a032f0105010e07050702031b03010b03070e04030f09030803061302040b0a030204030606080a0f11040902090c0706060602010507140d06 89
    0x10750003a40207507a01d008218003907060049450301c0c1c2100d58090b00e908080d02004c2540244444c00717441c0009008140707512003246200030710b04884d400821a51074581030140340403000005200f01c0703200340c07428090780d0348040040d901201c04035084816034011284510000748100c60741c920f03005030581c0683c0d250400009070302c204804500f00e01c180e03a54910050044040b0740c6186c96125a191501078607185035940440e40b1101401d00000491a415080e0170701e9950a42000045000c0502128191595031010a60f90002581c061300031a10403103005128503c1903840c5400c3d2070b04100740754910b4a0b04000e10100c200c000d00301d0f07142a1b44c20b01000c1035a4415a0081c034034112156005a120790940c14204211420795110078841da009003900c100048182e41c070000703e0f91300400d00d6054030100c3c0b80032502a00050400035801190a002c1000c0c0c0c41c042c0c0003510102d030040200700151500d4540a90803035506a0340e0070042103010703a451000741c9108008101c10750381c403100415125600e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 4798766 1250 4797516 4797521
    0xc07030c1509030305090705060405060913110304060b030102131e030602040602010b01180807050d0609150f050a0b03070512010603060e0f0d031a09060f030607030c09060206010b04090203040c09 86
    0x2214403948410b40c03401071607458003c29401080c200e01806800b0b01e400e0000d60148a5441454041c4a02140d445031580d6440452425100c08090500c0317045400c01d040c44069004030740071241203180840085440c10140f0075100b68520400003403002505207800710360881454a42c08400402120011000901900241c0000c00c240c1d000814807100000c0090702002c0b0218840c1c06c03482e890082001744000c00180e100031200c054550141000700c3c1d040c0200540084000074008c82c1c540c00d640031041c40168800310080426000802c0f4948604a0075025500390251541d0b159200f00000d100328136000c1d10303a500407010900001512a0b4030341c2d0300401d9501605003001c01ea005800204e01c504401d000005050303540745410400d410b01407940101c01040f001c0500c1c001d550032000592640c8400443c0050210018200c405c24a080500100608142e61500001545000d0002505400000c0c1c043c10307604080161810a400c0c00608c00081d00b0007001510b13100d591941c00504840b603131 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 4800016 1250 4798766 4798793
    0x2030a08040602010c02060907060f0203040305150403031406030a020f040e190506160f050708040b0304050709060803070209010905040602070c1d01140108061002010b03030a1106010603060605030c07030c 90
    0x603000c860721140751090180c00c4407008110381c810341d0803070303004c0011703c003404100c41081d11031500341030048a40da460b080b451170203642c00050061241004200d540c04c001c0400700e11692090f6020b10047c5e2000f0340280e40028140c0305c180d09980708100300705c010f1038040620440703d4000340000500c0c07040080030303a1031310001401031148903102c050345000b8044180059540000d0940310507441107090030000380039102d50800c01041180c08140300f820000e151048800503c1010450344e1241001e0130f041d9261002481140c0da024a010800281c456010007550100c90b0000d204c0794080e880c26401e0701c0901030060045500e190b00f0015100040c01642031f500c042c1c040410b10382c0c0f102c8111a1000f01084041c4c001080d940400d1080c03660981e48001241d60240090b2003040b000500510164054100e0710840c0d940741c040410081205548290181a010019021030300f80d641e03902800d40846e2402d016100010324104001010540400014804584a8a00707070031140704c4d540302c111150051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 4801266 1250 4800016 4800023
    0xf0a0b071403030603030301030609080405130203060316080d0302030a09060c0206070806090103120e01020a0803010909020a1505031b12070302030a0e06070f0f030e060a0605030f071206050405030702030a 90
    0x4500042809103803100344584151000c002c51640c1001400203659010500c80144030301d0f155807100c400c0111080a0301c000301400b40003c001c00081540c000060740040700c9080c060300c281d600360003100c1405110001194000d101800d16500c0108044001c0d50000b017a44d01c0c02901c6001542c00122148544014503503e41d002d040c0318203000740020700a02c80608014820713200d81006002085c262031101460505506250300b0354040680140d04085908801404032000400009000d490f00d030020740d12980300703d54500c841c2da2100701d00004100410320150000d0018000101c9600e078203001c40c00b0301c10541644a013031600001c85580003460894103140040d40100612801d03186a00404205d60124405440e441c03900381001003000e0b140340495002c000d00500d1034103480b03020760b0080d02c6025590090325401d141010b00340c0d01a02c0103205003402881100c401904500c03001c10f02d0b6040c2c1d82c00c0c205042e1480040d8540304050203000d401035907680004c020203001641e0070003511001d60310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 4802516 1250 4801266 4801289
    0x30201020301030b0f0910091407030302010b031204030c05091308040308040302010806040212060f0a0806090f0607091202041a030303070306031502070201020c090411030304180510080c09060f0a 86
    0x43d403800802814018183d1034210f0000803e00c60000008510040e1818003004001030080041c1011000004a40207404030350103019808814964190444060200240c0854904c1c4101140c0705074144194440a8400d0400607420300030f034a494280c140c0c211204c1050310f141568541c03528807983c0c1c8241e0080b101940005010011942c100c662150b10100c02c4404600b0320181134054030030058020101c602c29a401c0552444a23502c980c02c0f00c0180000000300c0f606031404c030113100d07078031201004011342a2046800181d0700a10404a400903140141481100c4110b41e500303000107001640314070507541c080c0000380c0750755880405c084c0d071185145950104006107941000780416134829610101240100301c10b9001d03076000a5032141c8400c080ea54010070307585074244900c0b40c0c1030782c041da00e83c140000500061404803000b070103104210a09020845501c1c1d1105950540c81c20b4460480d00340c000b0080302806140840c0d0059000c04090a0000d420b00c080b00059401500c0b608420025503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 4803766 1250 4802516 4802519
    0x71e05030601090609050f010c0204110705010603110901060207060e06070803090607030b01050309030f0c030408030403030503070908061003020603151504060305060901030b040f050a02040f05010311030d080a0b0f0607030201020301 102
    0x10b078482e0710f100040205080080006081a0218141c1411950114140304c60710540b80b00b1500c1c1e83e03100031140c080060040c0d84070034803843c2076070181115100581c0c5280c481c41e801030141c5804200d0b20304071844c0c1d400070400d042c9414000d588440251282c4c80e03109e04248250008038154500a5101c0c10402014046500d42540cbc0039040314604e001030ba04010083c0100600d0000004c115224080c10800340d54460340504bc1d4185184079503081001d01e0b000104000080580242c090b43c081c440700d84a0000180c0c80d1681b040d960722003240c004540d00404c40c000c10140c106040110380100c2d800141010703600c0f5074402300310703220381c1d5059094404000282c2042025858440c81c1c0c0c02c110102d601c10078a51444c0c44142e0300e10304c00f8201601d00c5820b5101902080300c01c010b601c40b0300d0383c0070b013051280c50480d501d405c000349424030050b500740e24408410f464919002c604c058110307800d92039075440f64031141c04880060542001b2035421034080c80442c04181d8a40000e8941c1c00d10980c00580d503076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 4805016 1250 4803766 4803769
    0x15030b0f070201060b09011803080d02070c090b03060408030402011209080406090602010213210c0605040512010507020d050a02010902090906070e010c0c09020d060b030f010306050105010c020303040905071e050306 94
    0x460300400311421a4074001c81441140d4104046030840082440e07c4065080c0113a1140c400700c0b11584014100074000030300c000300c0b01e0b07141c015000d0f00b07014182030400380340d450900400740c03202280c1896060300701100023000200c1110103550468010724081034104003100c401c100300c4042500c00c2c0c480b040041002c004003988101d41c8006088a07100a6061402d0002d40c0c4420500500400c03059003980b40036080908400b4000304045604001c035600c400e5038410740a00140e020b03005240c00f4004031a8400c9904805015050103065540d009000070110b03008210345c160440180c40301195203a0364080c002d80c0e52070141c24020010074001c1e01c928184500c3c06442c06035100e44850502a81001800100c0c0300c414009040310318000700541e6072101c070551580142025000380300487d00100070312020300c0400150340c4c10707648110420011a601c400040d25981480c40000354140d008010600601c04180c10030f0b900004c641c185414000d01c00c80010181c50249441e0100141d00481008040d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 4806266 1250 4805016 4805041
    0x905060108190b0c030703111903150806150307050d150f050f0f0405030904020403050c01020705040b06040b090301091707050601050904121b06020a05040914010509061315030b 78
    0x200308811101c003407442c840755100d03140140300810414180f140807000952180c02600007007a80d25003082c0507690307002c1d40c4010080d241004040c89000034075080c0141e2004508140c500140c1f0000300041901b59107901c1301598454407180041d40501601c6c50024142d12000d4490110300d2150020100c070301d40561100c021601c0b100c98850a06080801b442814401c11200b950840351b0100c00d00d01694460400a00e5881342d00c6030705070003d00c000303000000d20102050a518074102603090320101a82c8104000c142c0710b040c070401e54000400c000c1017115482800081050110150003c01c0f01c0c0c2450b02e03007500c021585805606540d8001030210104401442803501422003245c41c9035007030500e500d60b011141c1590040c0401d01429600307006448080e50305031403006501c508155580d450b0300900030804e4001e4800c1c0700c8940d040c10009094040183c0c034150690b1000341c440b000701c1c1d40c4e0604124650780c0c1481901d46541d81c0c0c0001d009207800303d440c0000618010f10b003012a034100341484484 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 4807516 1250 4806266 4806283
    0x204240e06090403050403020904030207081903111f0b010909060b090a060201020301081002030a0e0601060f03060602030304050d03090f0b04060603020a080303061e01050d05090705030c030a0302060103020103050403050d0905060108 102
    0x219408002c00c00000a4204064400f1f481d01601c4c032803010b070b4942c43e0076450300c59990460316a622484014841c42c08030a038a56002c1442a6150910303d214521990307511500d1104d8081110044002c04511805582c030107080e0040500d0803114459588429504581054000f0000814001040031041c10560700704001040b45100851442d03240c500300e00d403a000c0440030100c0298001000c550f0021f00f5410180540d40756070700b580c00950b51240040d140403480021100841d0601c2d00004600b800401600d100d5a046005040303841c00182e4200d00030440502c0855040074a1074048002c6140d0181191003203200385400140c0c0b50950040101e8034280d5407001595a108004010071521030b40080441c1050040864088803100401a600d900031450703004400d510700750421518003800624a011240c0c141c0c152013964503442c052540b1010480006001369001e0401040154801c0d440a64440d02a01c3c0040c100043c80d28a4000c1c0c444070142914290b0020f0014449c0c00402e011410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 4808766 1250 4807516 4807519
    0xf03090d0f050901050315090901050603071205030708030a06150c050705040605010e0f010504050301020a2304030b0c030a09060204030f0303050f06100e040b03030712140f0301120204240e06 84
    0xc1030040d0194020300b54810200f0072810040c0c0403011802c0e01c44040c40030070349480000d00e41c010a107026142c50340241000c40c0e44030320030f1050050000d010708244c150b0048035038100c4051450954a0380300c1c1551640701610045010365155000245900c4580d4000000c05065840c1c801100b00d6007461032422116801c0f0610582c6801d2081107640e800c44600940c00100b9a0b42c0b030500c2600000580b4140641d0348070359050f5000141000c1000e50008501400c804800c04052090f4a005803031803903030140f0300004041c030302d001012801c0e13820148007440d4044180500401c0c41e00d41551804c1c240d030010351046541c10002240e40c2d08043d00740c040d103503201c01e00040308010303440c26100207540201422281028081107010030310040e21181c001490000014080b0782eaa460305160102c00e001143d00020000359810420404079280c9208a600c910218140c0a0550342071a0740c1190000195000301d0b40590f841c0213410012941c0788103a101803546410300c0c1030003842c009042c240d6600061145 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 4810016 1250 4808766 4808777
    0x90d08030916150e010201140a0b1806060304150608070303030504051e030906130f0308071509030905010e060904050403020115060516030807051e07030f0c020a03020913080f03090d 80
    0xa00c04041001c502d440c00410a180813160646140010703401080028034a00788a9105000c008041c419504031081545003610044403007051070b2a15080c40806461140c0c3c420010004030340402c4281c0401c80c8034445c591000590103641d8102607142c070103039601c200c022903106c03002c1009101d81407003941c0100007140d5450312118a40b0001a40f40d00c14040e0300c0e80b00b503801280e06c0301c0004c41c040c1c903000076003080c40c00c2d840925103a0620810365041a00c2c1155040c0b4072703110001c1c0100142c06031134103255040e02d803808a241814015586a81350400851b0408001c0c01000c10560b624044d131400740d8000d0b0000a04201c2c0c10b09a01130103401c0b90051001c3c007804101c4071034100c501d41014441c1a80601d020f40c0d0b95201c495003250756210340441244400c8018000100c4e424030800103017001d500c6a261000010480c0005940312180c00030082d5102690107800c1015080c4400c4107940314011410082c20b4042690781d12445400552074490445d5000c170070441011000c0060b00304103000c03030405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 4811266 1250 4810016 4810019
    0x11040506090601020c15040902040b0d0506010f230706090f03020105060105070203030708090111070303030c030f0621021f0201050103050706080f0718030f031710060903030804020303090d08030916 87
    0x107559000d4621030345011b407600e03141d011150441c04050381c019100040c81590340c2d95590200d42c03400e8119441e140401c0b480e140100b2030560060500b03441491a076140d024a0319a8180e581051501107070540c503801004000305000100644200510a0310803100707040100d80c039040081c03c6030802069079050100c20015600540e5001040d2102c89601500700c60399a805400100c8114100c401c4410107481000070200c10990542c005c0d1490355925a0100600c110b2081e40c14144c80c0c442c400e41e0790b21440741d0900341007400313440025080980080d0442400c5414141280a00c0308a40c140c000184d544000600270401c082c170503070703004251f603291000b01030903c0b180151390844007500d00030a10034050490a20380004c05800801181c0040d10f41032740126038100902441900f50f00e40054415510010300c00d881c02c0c40001064810b90340e15000f4280c00c0da50142c4001101420599043c84148002d102035514002c1070700c2d48900c04c0700c11a85904010400341c1c50700c0348020071b01064211b40c500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 4812516 1250 4811266 4811269
    0xa020c0715020a02060318030301030f05010b06040b040603050a060f080106050909010504080405010804051009140d0914040902040605060304031e0206070e062107080106020d0c0b040201030e030c010504110405060906 95
    0x20099082e9804485e19030b0380fa15420030942014000e400b800040d4000440000b0911854202080e030f0f04d03000c1c00080c00040900d130100800391041d03000d1081e00d984248800e000c1d1a21075031010f54010801c100c0058156203030742c8020000b031615030064200345e448100c00c0c003860404108442c4c100390300f84000d00940c2440e03603c00010340207074003445040106002c0010240300c000c0040c1041806000020030814009050291500c00300e42120700c09031041c2e213000034149206c0d0102d1000c030f50301001015259071b1568100b00c09002d40c201d0580c0e00c96101d0b140403074141d5a0100440c0110701c02c1e1a28110b04451284850b8180c01e549024030070354128600b0040fa644d000300c00c0c00180c0904031007160b5119208603000384001700400518811503080c400300811290042d10040c16a045502142e004200f550400c64003502248001018140f0303074404200154060b800030241c01450790140d17400c2c00f6442d504603084440403a02901c02000009038150242442c2c030030941c0240e01941e10800074a4000d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 4813766 1250 4812516 4812523
    0x1e0301060608010311060309030d09030804020907050304020102060a02030a0e030409060305010b0d0c0608040201050714070e0603031312050a0203060c1218030315030c040c0e040606030b030604031b06050a020c071502 95
    0x45c0294001c000000c0080c8022401b442103d00c2d0424444003040384010074140144507070380c100e41c200d00074040c0b000400c01a50017030065a00c201c1c0e05030b00400407a41c811600380041e410103804000c1c55521a84801c0c11b851007400500060020560001030403403071400c20300d0039a000344030110b0041003490114800b182d40e240b800001c1c2da03124100104582c071648012501482900405061201101c0800c00e90560102d4040d04a8081c080072070025105c9101305900c03841540009480c221074030320208403a440c01c0d00410034a40c0a1400d450141c0501c0d0086410060200c808203922403000400b00c18050100381d10076000401d00c2e54120810071001501566803101405160140300740c829074030f8059900b00800105580040c0040c4031400280e2005480c04170307000e403081d2260782460301c041001d40c80307481030b02500140200286095180da4605403503605885141c0c0d080d4003014030100c8080b40c56030280c1c03401880c060f440103a0b10724115001070308040498100713421303106d5044034594141d40c2c0007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 4815016 1250 4813766 4813793
    0x20403030c120c020612040b07020d02100b0a05030d02030c10020906070201200f070801050612071203121107050f01050105090a020c0304030f1407060f12020304111e03010606080103 80
    0x190302c0550303100880d40283c420100d841c034025800040000d1001d00c2949112205018501c142c108110b1030320750301410380c0c40711420503e031401684440300e2132002c150250802c0c44405805820310541380d8540000c80d04000d001e20100c405680005076032041981e0810110141c0d1020701c804500300040c030310008072140b1031400302904201890486245222503500b25180d11480207003241e100008442c001d54482a540c0f251030f0095182c50006a15818119805c03021039800801400105061030071510708012340900a404014810301c05100840040c802c029101408004242d00c5070325500c1d00902c0c1c080104504038550341013000401070f03501d82c02c804d00d40107140d104000d80c440f841242c11a285005650019001c003680c0120700e001d102540c141550104080b50680350031a0301c40b181901d0240e4507809520015250102d480691081540615081882040a0080124001c000480c050414548550081604442559585402d108560060a1034208140e080d890b5854084081184 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 4816266 1250 4815016 4815023
    0x506070e030307030509030f0a030207060210060308040302040507020f03040815070f0f050c01020904020715110406020d0804020109030203010e0c1e010203030417040b040b04090b040b030c040e071a030a0f020403030c 95
    0x455001b1150383c00b4094607815030b180310100c888400860030002c0d0703038104620513580035001c0d00c224040d202080b03010755800d0726044003100e464540385034280002058010207560850250240c0b00d10410000d00007000200039500003000ca0681c0d042c24540410740180c1104188841443d250380c229070032100400048106060071601c401070221010701a110300b0405651091000480c0c80400100188218141c2207203402002a040301842c03481c040c0c400c0d8003640d07003d03070310580d5003215641c46010316541c094810326000d51129544e5010070b003500d0780344088200941008070140040d0820703038481c016001000c0210980f8941da0340000c4c0d107921001e40048d00000c03410255000134082c05007250000c0007000ba10326590755031070400e0440b9403c203010780040103040511118403490240268100e01e00010082d1580c80104800c0000070301c03041c1d10030780c20360081050000f441040001d0074030714040c00d1003403141c1c2c07454104a444100c81d1103480380c0484074814881480482d0b4080c9140d000e1960 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 4817516 1250 4816266 4816277
    0xb0402010c080904020d0f0606030c0923040212060f010e0a0302060304050f03030106050403110303040e06010302070c050301021801120c0512040503040f0b120a05071b020d0602160506070e03030703 87
    0x8509115200f07202e2003a0554200d070002440107540907050780182070626003120200041354680000318140c0c0c1550700c0080000d0035002c0180881600350609a904000d8680e85003903940c1c0c43c0b80400c0c166000800017068550f080b20402c0a14104850b000d0450704003480c0114000e240c5000042c0c10a2107800301034050800480045e007004020000c00340388110680880b6100d41e50380400401c1035200e408120340c000408040b01045040000c20f40d01511071100c14410155245c2c4d00450013908041c8041c2d03a1401000000038a0351000c3c4020000351074080180d1207419400c00c0098054586c03d001001c01e50f16002400c040035030b0080c19034040c403541070924602521b450a00c01e103140034640000f4200d0000c50301c0080c8075840c4c200105000410002400c0b141d648801210080311030890398100480c80c44c0380d9040042c6121130311440c5c928030042c00c110540040b070700d408080340c018010403054000445034400c00e100d020408182c0c05880b920741303100c46200100c003290703e074021901c00409005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 4818766 1250 4817516 4817537
    0x1d1003090305070b010e06011404060f0509040f060306050601031404020d110117070503010e01090506090601030c020709050f04050f120906030402040b0d03170105060405060f03070203090a0305010603020117040b040201 96
    0x602c54001c5505580d04040e8045a03940c460350601000c01098070418003141c44840c1000301a002e0900b61001c907241600c0c0c03c000f00ca42c07190292101c0d400441c00c0c65025660306120745040200c6d2080d10040c3d030142c032000500340b03040f80c009411102c01001c07080c03144031288200030040ea54100000143c2c1c4c2c0c840380c06030f010590a0016115042010080441070ba285020003180704e5024000c1d40c100d43d1003078141c80490f60785c3c00d1100c044450949105402444010018804e54043e80004414110310b00c12901125600c0d140402120000d441d502c002c2d0a06005110a00c0000c1080d0f00f01a40102c0107030986c0d07c1c96004071140c41c403404a03540e0140d1008000102555102e174012061041c0c05440202005000d28000340b80300c04604000c6091030180d80089010b0170403505641c10799802a046903c0c003c1c25a28030221034000a00601c110301c010001c05005403610b00349980214452400802c101c0e0842c40050403500607007071115850400902040041400321180c990031a4081c2440084034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 4820016 1250 4818766 4818773
    0x90906060b0307020109030e0a0e040308070203040810060302100e010c03030b030c120303060306010e010b070b100803040b041701180b060a03020301020a020f0105060a05030622060908040302011d100309 89
    0x4200c1540108069034010080201c619010b4124041c030a1207640c91a00741c1561400b046420788a601807419101180000100080e0146610300c3d0040814012642483da55481e00e0f4a40060341c00849c0d084d68032464100b0441c2041d040c1c418400c0303100d0801c9034980b0304610009201078882e0304050308042d112000c0710307690f4406021100d10b0300f401809004440003030081c00c640e25401038600900a10494000064805024000b0b5050354400039800d072410325640c981c0040c0100140241800900d03294001400900801c018001000c07980c0d5807648880c5001030101801410700710202a81e41441403900e1850100000b0810b01e03039004d0503000103500c0700030110340c81030016000250952b1000911502154000800e0f10041d03140c24001e1003203039900d8041c0305032a1041e120f459059030085000c58402c0041c4880d401804030003a10001c52442161985d200791b95060f14155043e100018007841556888400080103c000078503a100d5513001f1008600c519601c1001d00040541ea94540d9040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 4821266 1250 4820016 4820021
    0xd0b16090815070c06090803010f050112090809040207030207050307060f02100605030705060f0c0d0810060e0f0409050a080f041716030210020102070212070e0714090906010504080109050606090903070c090906 92
    0x1e500908508d4496031585142011803207035000740c602042281d8910700341804140241c12061741c0c440007103824901098184000b82d08002e100300c00394003071040c002c949910108810801040e580c2d80742c0312500c580c6200070b401c2000f00450090a40c0c1014018843c80d100050380302d0496030107880080c4c0c0c842d40b4007001051401201d01c1d1710b0b8a40902c5980c0b1107102c1c2c0c42030845010b03402d0740c0d4111540755078a90341038a0507104c500e80035070080f0700712a040c40c05103002d40c00222444d0082040c2c1d00207102aa80703201c2e0642c080800c501410760085801d0080c00c01c010020a031414100340180300c0000c0c00d04015880b050746100003440783c00801d07000404140300f0740540300d9680c0c0c050112459940c000d0030b29a2105001d000300d440d00c12540c400244658440d0a84a0300004002c11440c544680705d4148120051b008003d1814040200400070381100240700c0c0200b40341c0a07101904060070140200034010380058040701141d4402e114050202e105200ca5908445250b0b200198200d0b0b1460a80003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 4822516 1250 4821266 4821281
    0x30e03030f010b07060e100f0c02010e0c0405040606030209070215010905010302010c02090901021303060b040c0201021e09030102040512030d0b01020705010906030510090207050303010602190b060607020d0b16090815070c06 98
    0x3c1d0043c00c016402c00050b5810642a4481c44d508c2400f00c0c0380c200300105d00701c944540800c009035025455041c901d00b8182d00c4250001d0143c0c0f4045002038a81d00411244c101c1070f0313100c20040e4400c03100150706941e8401c00c0c82c05088030403414400341d491500000e00b0320001a5001c0e215004000c04110300000c2541141c40d10300a104490f00328980e20b060000003441d10707204142c050350071f082c690003006106208661540c03000c160803103040e0408070346812075034000035400e5405640c2080045016038803800d2034021f02811030000d50b501c8441e4081103064542c40501e06055500c4102c0074445071f83c00005007000d41d407052070300003121356031090803100c1d1940a5104094880c800103022007800780110065060f640d0b2034013140c501c480c0311588440408200c1001906c405969004540c840c0b5007031008100150004160300d01001c40341d22201c0019a040d0740c2410903404c03a2a8030012207412210f40401010142e000d030400b56070703501e02841105001442c2408020b2411003102c108592580042c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 4823766 1250 4822516 4822541
    0x1020c090907030213021201061209081215040606050a050904060b041203200304090e010209130608010b0d050a03030903020a0605010609050a140a0b0306120604080901030e03030f010b0706 83
    0x318908018000c5611421070740000c1e409070030325030b0551507004002c1c000c0310046d180380f04201c140ba84c6010002c0311344500c00e400116440d40c545050b1004180400094800699810143d140d5801c0501442d03030b440c0c5e00312054600907428a0307000c101d425001001e0703aa0140140c2400c55440c504079000030000c00703c035080b10703000000118011541d0800c08200c0114a482a01c800d014000c51030303101201807028520700324096004203c00e000300c200b6604401d10000307855001604010000c00012a1605502a600c6100741d0f1a002040341d444240075000240030151507030140340e000c0f42c4406449090261000e001e05450720740000c1018030810208200581040081185584680300200342071524400c0510401c0006c0340411070548070444c4000e2084d00412071041d4a10380b903040c1029400041c8140e07488845c802e2009240c41c0107108051040e8856514156645054800982111140c0080c610154024810420100391228210307045d558031641060319071055152210161803c0806031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 4825016 1250 4823766 4823779
    0x140a092003010306020a030608070b070609081c090b06150d0902010905130603020f060c03071103030408010905070e0106110a03050c0a06020a020105090c03061605030a0608010c17010b1201030201080601020c 91
    0x600c84c03039601810f81c000055609000132580d8095440d0385c0d841900070458004010014a00022071a9228401c1180300d48695030411800d8403070502000c080703010b0341c0c1e9995160f0490004008400468580c000021280d20301039550300808011180514610702c0c403441e94404946040d680142422801000020301900c0145941e11550300542054030040740581001c10b4004140d180c0041a182c4d1902c2e904011400c0ad03503e40c85010210010f20842601400200004219460203006c0c0b00ca88034010700060064510b002c100d00c054410503440b1504006000c941c0d6042000c0124200710020f4051400c640c490550040c940c2c240500342800500c441c0c400600b03211040c0c4c064211502c5060303100142c500b2441c03410240350b26804e00322122000030742c0d59810115868000c01c099500201280b8000500503181c00f0420308641c04400c180d004101010b040110f0a00407410f01805000c1075000981400114221103171811410b010003818806040d0001d603040c1d108101e03161490000800a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 4826266 1250 4825016 4825019
    0x1006180801050103150c050909041118090109031101060501020c0108090102040504090b07020c0d02210a0f0503031f050a03032006071d040504050d1419030501050109140a09200301 79
    0x70242c4003044c5e11131804014240803010304454003800c11f650704000c01904200450b40c607a0340b084002c0c03013140301440c0d00038050042041c404c5401d0b003515125480500c00090300d0002810040c054405100401c0c40c00d0381059014803442e41d0215a55090b8002820141c45548030148460f019019035000306801c1841c109292062000b0300d0f44142c01203e094082c0c034803003c5200288505000b40b00c0c000781d0440150310301c2010b200c100c00303407105c4000e90407415104c14180503601e41d150f0400b5400c06a900313a20110902c410380010f0105407400601081c8054031312450200410320084907488060140703c03c40a10701c0307e4000c040e06542148510321705442441c5801c56018203400310170524211401c1404011140320b06051007100c1c080c5400100400c0103111100b81168082c07072104002180b428244061104480c1d401001140d240c8130761000304280d07050000040c032000c81c60740541c445002c4003280e542c490703c5400c120801d880b0803460101d644250750700810741c0c2e540807031181074100100000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 4827516 1250 4826266 4826273
    0x30705010b040f0207030801050907020717030a0e010801030b0a0b0609101101060b04260109050604030f021009080a03090c05030a1a0f07051603030f05090d080c031006180801050103 80
    0x40030001c03500442d020011018191207980c1240281c24004011580c442c005103c5860584040c641c014017600c11160a1900d464000921280041907407501d5030000c20342d80c02558100d01e11504216082c030b0110303661b61464851f1440c10b0070240c40c7e60380a44c2d80e02011140740c2c070760710119905c84901602d0030a94003852a001045050850b9041c05154a803100c042100c016441c202c40454054000f070898000c00340506012814018a01c000950341e600940c07400601c09002c0350784602d01940311925030010b04200039003031007415042c82c1e4103d031a0848800008084c502038030800141c030b14000a92244902c2c1c1070b0114100c580107254140b01d401d03020b40410894400c4890b042d030050300203100c1f64441c10000461880141d4008004c0f81007400304450204a6819490489000b86000f151204113480c1041c2250b8040d555860b080d0032015000180c19000780190781c1000e0340c0b1801514616040c55803240c000e0003805128108116521040c420500d1a006007004d00b202e00f008001c0d9503524903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 4828766 1250 4827516 4827521
    0x70c06060501021b040f090f0503070506061504060c020a03020306010807171902060a050f03040c03020405060a03020109140a0807080f070b040302030c010302090d05060708070210110702010f02070803070501 91
    0x10049800a04140011803203510100310a159804099100c001c600124820003000d800d01040540011ba510a00c820200c0c01000c0d85c0c0d03003002d0203039002d19681e0150341001820003000906113401913088c031031103100d8030210100711011a02c1301d02c3c1440303481c0c2e114400188800c00c0c035032010350725100da0380002c10f8007500405ca00302100d4000d018018044020451300d611800d00c01c8181d210040b001d0109400b50800c0c60081c8400500b40c5802c0e460710360400007a4185801c15542640c0d00e56075103a003801141014492103030060350403110002d02600e540e000805042c8680102e42c2121901c8003d01c0042e15602c1c68040600612025a4445915403000550b03560f9042c182507414802c90900240b0f108414045405803600036020f4004160210015030203940441403807600904c01c40309100c0444c0041c482d603800341c06550398410271070400e508024500800d64544d07a407503d1408104070203403034640046550707095081c2032407010044400e00036420700319654071101e003e00002030f080c4200a41035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 4830016 1250 4828766 4828787
    0xf0109051006080708031222110a05010305060a03061805011805120301031104020f0702030102071109010506090303180303130b070303050703020a0503040204111306030204090c051c0c02120307 85
    0x3000c080010595039089150785080c181700750b03e0540c10400040d001c01ca8440c6002c4e6100c2d08003100082091a11041d448054078800000e030341e0030b202c4450110352440c000541e01c0040009182c20300440c108031001984900700d5100c0103002e507030b03941c0f40540d40080301b04000802541040c003c0110200951414a128082200450b0140249031014003008100c00035a4141c2e504001400400713001308003400020740c821070310403840c1d110134084c0f0001070350240020000a171003041c0203804694a501840702030702068200360701c15031051000400545000042e50b0481a004885407440301c00b40d808a0304610410a46c01030038943c0040c0411800c220000504d0424480e5030100155903c03107a04508074014512014009842000400c015140681010303404800c054900c03071904400015042000c007803940050003294000c6000c0002810720f20841d008500c9074142689040c1001200c0300c07030703060030b140744841c49550b030305d04030310398610811507800c00365081140140c0e81e0400040c051b00348140c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 4831266 1250 4830016 4830043
    0x21030103050f03160f02060d0f0b090601091a0f0705070b03010602060705090117100f0609050f040204030b010b1e031509060409030206010515090402070809030d0f08010b0703020f010905 82
    0x20051031a80c0d8180000455540c1811205803410007030185d91080f03403800500b01c2c20b0f40e203c02c040c8428000c1940d02e00c6103100b0280012400140c550709101882030000c4e00800480c148100c5c0c01c8100644141c0c0401001c544004115055946480300848035071409416000780c1644070b1502c0c040760020340c3c07200039410396890f5002c682c859921040304580601c44e040c403150004003025030a0790040000b0005030341045213a0b0a40b2151a10b8a04c000c0c021221a88408002200d0000030030460070050340340568081c0985080d0f14250070f548660740022012b01c24280701d0540040c14000e184210681c030039000ca0301c038030b03c40c4d9a4100b01e400c3e4000401804400c903c90300341c540c08110b0700c1c50700340b08640445605402602d1160718000410034074200d05003580c03140060400c1449055a124030080445901c03600301561588564001c2c185800400e000c00424420307030146044005070016207041c1125850f0892603036401d51860102d00f401402d540030b00041d800c00404004115000ca0440d4510f80b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 4832516 1250 4831266 4831273
    0x10203010303081003081602010201180507050a08030304050309090601020f01020a0c150506030a0303020904020c07080d02010617030301030809010e04090c0302030c060a0c0605070905090c071208190903022103010305 95
    0x16500c507944c402140900c80203011103801c00081100c5000070154418040c014000010700c0c80d0444801000e451a08000701c82c141c0061405200c94500400340d070b0050001d020046046180507036499591b8415041d1280c4903002c02d03000500568802c000e02082414658005e544807500c00d000034200000f540c0040755241e00c05080300e03134108410300c54030341b003050020000c154a2400d42c50680003503104c0b07050310b9007283d002c0000b0740035100d0030070840300108050b030002c280e5202c4565000382114a00c0d00301e543c44003203086200070702c00400825641541d40200d165962000e10800503940305054681144d0400e0a240380002031283c505891000c6a0080d8107031881c15800d0800c2100d02c3c4100000c41010801440d0300f200412059480107601191320309001403040c0c0c40d400043e103041c40440d202080c820b000613101c01041018070004c182a003940c00c10441600344010303c440c0031b20f1102a903007411555808400705042c401c004d000c28101c0c0c0da00e05070000501d02c4071128515070090005444920 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 4833766 1250 4832516 4832521
    0x305101506030902060313110409031106090a05120c0a1707020420120c070b01080303070306050102010b150a09050a06110601050a0b0f0307020c04020f030106030b090402060d150906060201020301030308 89
    0x60003400360f2035000e94028012442d55072252030362041c400d5600420354440b810a0400035403900d940c410180413a0094481c0c41109001e01403103450709000804000081d00040c0d800000240000f0305040b51400f411256521040c2a100662030101c003020003508104220780e4901c1401030480c01050031318000c2c1c0701809140c0b20039501416007840c0e46404a5001d004101d2030302c030b00180401c02c9405c407519102507850010703035459507040f036003084c1c204038401d03000001417244c0c62341c140c41103800500083c0000d0200c91900000200380d0001c04003000407030000003404020085c0701d01030002c09444000c040c10a8281c40300341c010f182e0b5418101122083c400d00c000401d0341d01c1c1008180007122240c0c1030360740c64000f00d1107003121903070805001e5506610500308202810f0707465001070310006400e158001e0312503241000c01070603100c000030218000c081520078440540c540000b16820012010004280030002c0400c004d8501c08661203104001e00d015004101d950b4103400941c100d07400390b9078184098 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 4835016 1250 4833766 4833779
    0x905070f020604030206010920030103060506010908060c120403020c030a050705040f06080a02060705070e0406050a05060108091002031b0d0501030303051b0901030510031a0f01060c0302030d0509030403051015 92
    0x484050f107015025a000300300400c10455aa0070030001e4a809804800d0020107994402c40d85810030b0300f044448c035842350100b11103941e000742c8440040c034000c2c2c01000e003802e2406c1540c3c0135101d5840903101c0ca50000f400502411700820102000040141c00c88500651504041c1d0303d031100360180394400e0b82000055411031500e406a4420303100500003601c0541e10690030090140d000d904101e6031402048000100ca08841c061144118000c0c440482d407464070010241c100c40b001401c480c1400212703424040c201d20000741c4242c070a111100d0060360307510755440c003094401c3e03601004407081000041c07015804410790080fa0403640f080e02e060000d9280c600310525a0703001c03480d022030150000d2103504180e61103034000b903402801d0400f2403003000c2d40b25201c40c4035000303082001440115140b000c0c0900d81e00d80b070361010700400003072414025080003690025100e10030030030210080c80c6c0700c20104c1c55650041c0100c80055911030101c034030500049400c0301c0034103d44119000840901500017524 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 4836266 1250 4835016 4835023
    0x20405010905120a0803010801050103030311040b1803030d0207030201020705010c080103020306070302030a0209090403020102070512040506160203070503030304050a03030525030c0c060c090302030105010909050c090403020f01060905070f02 106
    0x6452050312200760180c1090280086008280e032883d020b4807489001c2404a8084402180a03086d4440081401c0d030440c14068255280c0d4500b07080d000300200010008401071400b56104400152210104062200002031035130042018040d940c40c80080c548041580540c010148684110001d20070041380c6034055070032410910000e500341e00000300150101e8402d03401158400104034005007048034060104441e92030032642107000d03070360028041007400800c00440300000d848402d65840e003420003000c0b424038068200007044040d484202035085507410f00c0504050701019049a46910301400e00a944100d2000264040780c500400b01d0032211003480315180d0346000c0c04070a0045815601c0440c0200001c03444082041500000840000d1290040002400d403940e40c0e036849908500405007104d8060703000e21240c9240107000740025030302007581e0322038003c11034510354282c1d6181401d9090403510720b096201c0d5480c20002080300101c5520842c001e41c1c00e9616260506000b9109994 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 4837516 1250 4836266 4836269
    0x905070206010308030405010204030506100302130b01050a0f03020702030607090e1b070b090c03070603020a0207051e0f01090b0301080304030311010b130509030706020403050708010c0f0503130f080723010204 92
    0x1030700680d0051010800c004011a0007511440c001882d2541c0c070388803181090010390362058582c40c8c11208000b50b04e062961010200c140e1310b010010301c402200007030003d00c9903a00000031310920076035400049000381d0590300410b40203003e4840c140352000c0020041e81490044d42c080305406008509010301c112070034458010302c09269490300d04580c45100c45c10f00b008122031030f1031040100c0501c1d242c40c01c3c401c0d81d00030074540e1030140c1c40f0240f580c006030402c2220b403c0345006800c0c075104403116542c101c080840c50340c002d58001c0203d10b181c800403114042035420000011070004000a4401070010040c401ca9019a4400b45103c91511000d400d88420060490f80480d001d00900440074055001c0350300078118a085a00d030100d203607030f1402681c001e58016107581c1c200050402c4141d00038003d1510707000749072600f80502100c1c40e90107441404060501e142142c0908008810800f9282152200302c0c1c12600260702d4248038584181d1003105003a21803401102010900ca1142050080d01c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 4838766 1250 4837516 4837531
    0x4060b04121106040503010e0a0b0105030c09041203020c030309160b0708030412090918020a0b0408060703020306010c0f0501020a030b010e03030412020301090605070c0b01050a0308040605090406080f070509010905 94
    0x90000c0c0c0da540790400314550850620f544840e04000c0020310380c0c2c0034420a02040c5002025010070b240c1820034918945050780010300a410541840038030b9940d85960340d03802039201da441030031541c14070f40880003806091a4110f45100c000241b210040c000102e20202e0084e00204044942e22a1009503050054050041081800348042400164100e00e09901c282141c50300e4032025546004013800d849000c042140c0364580d03c5098001c2d410320f00e404001800c12210007a207424500402581d4404005048100301a400b20100f800d40c1c3c401d550780c2c080142c103c1401080003155081c410300075400311220b00042842d00300c4402c0194042e03c95005404d038000c01442c00c20303160076800b20703e0b010010380c100ea040d540e8402c14400a0103030310425028180380d40c1d0301249072840d80b401c441c2428041e0041880341c407001c0d50410014500c4e200310f40995440c0d1030311507201ca032400081005029181c204008a01400851024030700c4001120401c440044400d645240d0341d8200c0c85040700c0c42680c1c2130 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 4840016 1250 4838766 4838789
    0xc1b0b0f0a0c02040609060306050c07080304030f031103010e09010b09090d0315051509100806031c120e0d020c0114040b03070507050d030b011106060d12020307050102030c03040204060b04 83
    0x80303401a480402504251003682448009100c40f90300140c211051900034840b81c41c3c0c3d5070030500071b21606204040d4491385110341c10340b400407035840b510310b01c1c080104024100076001c2c1c0000805442500195201c0303804100c0e0548a58403840282c5811208940c2041c80350719140b42448540b502590b00ea00400c100c801400b80c00303c03901e80480107000e948806402603110900001351b9034480c403d2481e41518244c034055254074400f41004102215003201408009a00081c02415500411107600c122000848800c0d9243e400d8400d07100880b1ba0111181c0c02841c0501450128102140d403c824861690031b940c005000d00005440c004020f044c10b000c0d060382840700340482d40703014009640000d4a800c0c41401e100b0340c1d41d1200e00d0600321034a5580003a40b0384990079990750308440c1011581d142d000140c4081d10704200030a0845d010030700094070345000d4802d0007910302d000340100d50700c25801400070356403480c00115030304280c0d1090f20700b01d015926001e030000b120b5004109880c00d4a0711000030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 4841266 1250 4840016 4840027
    0x90405090a0309091d03070f020f0907080a180b09070302030105280b030a021002010b0102061008030a120b0406091505040c0503010b0906040b04080a17030105030c0103110405040603030c1b0b 84
    0x1160018610051085d116203000105c400940008001a2000d03a100d11007034014645030348182700c104107001d000207001c0c01c400410722040f00d410001c000c0d48405caa804c002658080c80b0307803213203d0078a030501c060080d80c10641032224001c00408ca0006481c020780091100c0e40345c1e40e8680590411404414014101e81484501c4103d04c0380c0042501c440001e00b15200312200d500080e41100c4030655803000340c0c1d910701d14002c441d60148a5680e0004181082414042ca4241c00320740f00c0c440c808507182040b0716031641030302e001821b42c440e03140803074098410010700303899105100007003003518038900d02500f640500003400c1c503050040007981d07005030751040d0843c1d11b4030054603119040380c11859400300c401d00002c648003249002030001007140e030b401040c01c000c0a0070040b40c04000386450000c800800c100621180e2000181102c5040c0203107030009449140703001c03554031070089410041d03100f030070103000100b4598000b440100e0f80f405085501c4601903401c1410140c03810340d20460720040e505019 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 4842516 1250 4841266 4841279
    0x5030316060e210a02100203060109060e0112020d09030801140d020904030203120c0d0f090c050105130f090b01110102040f03030f05070c080303090f0102040e0408031b030103050102090405090a0309 87
    0xc03081000034410211483c90004010441c1e0f40f00c1555040f40740702801162800c48154100180100034484207001c500e1401c0800000706012170034041c17607051010070f11142c0c0140e4840c21018020440f64003046403581000184000a00811201580018810000820982000f2000190005005140b688103e80603400d00c180d19a0051054003075000c14070000344d4041c0c0c2100d80324403500108001d1070303650044244042c100c0340d4421044610626108030040003d8094039440103940303090801c0740d1107014180f030703c5005039129086400f20300d95140380041c4183c00b68000d6100644243c807880c0e005203c101500c0c0c00c0740514840c840780710140f00000c0010a000702c0d040c1e01141c000780780591509016440d901c0e81c0c41c80340e60012500350300010030404c03a4441401800b0303280c840c95009502d072501d444d1082001c860084c02c0501135820000200e0070b00d881031080101000040d003c06500c07507a403401c20900070b4000302612401103040000040741c1000218043e44041d60503100c03801124100702 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 4843766 1250 4842516 4842521
    0xa120215060f10051902030306100809060a020d11190305060105070b070507170a0906020609010e060a0b010507051002130504090f060903030e0703080d110307090303030b010903020d06050a060503031606 89
    0x1080f405021007000f1840e01c10a841c00f80851a1a207600296a04c2c20504180002140c0c541101710400000100f4816250b401080040d08a406c42c88090b84072004440180010000302c9250720301c1402c0040d0a6650020340081504501d000d91001c1185a941d0750040d0b49503c80d03150000c00e01b01040f00020b81c0240a90003038007410b4002c10302800329448103160020305600a14010010640c0c1480070042c85504101c2c0c161302c2845207009004403902280380340e50314035000d0f044984a684520540403964894000e45440f1900502250340700704100744840d0080d4003009021318003810412001c00c4e80c5c102401140c40040d0b112004402085140c0c4409008000f0002e00f10201038503403003108a030a50130824240611b000b011030a80d926036581c204005c0710b8098940b880100c2d0103004005006400c4524101203e406050100d4a0300c09000101c0d40a419608000d60121221105505102d9a81d00003881076220620400c4096165002c141c4e6900440140f07a54140324001d40c080003640c0c94 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 4845016 1250 4843766 4843789
    0x10020304050c060d020706050105061602040b06120709060e0f060304020607020d060f020d0510080c010f0201020f0a030203090d0e030318040e0102070b04030f030608030d050411030a120215060f 85
    0x260240c80a8400b0240040c400e6480543d8801307a0540218442c4107014445c818140100380403101145005c1c4503907901001c2218004010348156a107400c01003c03a141c81c0c00300c5000d1500c0c1610300f90307030340741101000c0c0c507180250140c940080c203800030207e12400c06041d40c04a4800c020025030035582c559003081660343c4003450403038020a0001e60440041c2d0140100031a000e404c040242c1c40d042c021703400b4070071198010501c084a100003e02044510004a940c3c4c114041c00c1ca04803003001c4590a060380a4441c14010140c07218001595000966065010b0340c0545150f0b019100e050756008001c41d28440c160700c2aa905420030465804545503a900e480c4000f800580007140360320314170040300c1c2246c010303600685440001d10200003c15030300203980142110725083c1004a1030074003220b1943d0b40602c506014105035030b00085020702003040c540348501d1070005c00b110360401c1d03685060307821145035007404c030050311843c418015481411005d051140001030308e070b13800b504200340400c018140c00703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 4846266 1250 4845016 4845023
    0x30615041d010c02010c050906030109020702030f0303010e01170d09090209040e06090d0311030106090306050711060405070f14060304060917040b04031b030b04020405150d0b0420010210020304 85
    0x803080303080d050714000940150344140040000600400005020b42541c0020404100f0480e0412801022366200d4059a043d40d031b8000c00140c0360003051003c07030702e8415000303580c0031148030103c000100000d08944403816a002602044404050700b03440d560344a80040031800410403888060000f0700e5203901602140c0c0c00104080380ca4500041800d042c49000c0e9040ca8081d0005000ca1240c641c06002d4880d0941140c1c20b89842c541c50800000e00700c2819020003014691981c0219160603c1000300c003440800140503560941454030305907565005a108880d20494040c000142c1c0e500811110382e4400809401d00303107181e41c0c030f43d6031034014081401c088038111001403407060100d11050140020307050540344980e5031411400c021085840c01c40b8092040c2030703a44d5051002942801d0316035080f6505031000320341c40c4c88483c80720400d40440d4511540116180c031402041c8100740b20850700030303406100d8104490040703600d034600c1005402c206d1405640040c400504008640e0b004592180c003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 4847516 1250 4846266 4846271
    0x4050403140a02030301081c080f0c040906060509010315060c02060f0705010e060109111801050d09020312070303050609060307060f020718020c15040c14030102040e0703060f06050903061504 84
    0x200e405180c0e82007161210b00681c40400144030500b8104004010418100640d180042001708010a60340d001041c180ca00380000012451b80055442a40c2c00b412403480d0a0044548a40005003135070480082680084c0c00c000041a034504d12144403010344025541c0c2141c400000e03000c0c48001d038441c111803240400100035410101c0c500303124600341c4080340c40c05010154500940c650640e2044103280240b5141003011010309001c84803ea1f140b14801e00b420f039250500000044000c1c0810940690140a80745903080724001000c001c0455030b10036203040040c2d88402d03003407000305201155015050703440080184120781c01144000f0070f982c80f030b1048482d0940c0303400030541441a4a103940c940c0342d4021071400c440c040c040c821500540c5a0400c2c6595030300c0c0c19165481d4100704d030f100b4100e00e810707a0301c508144d03a1000e40450300a017141c084c00f44094200444014014402d45c0304044103541d0040703011400900c00c5085501040c0010020107564654044030030015a04c4000c1da6441035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 4848766 1250 4847516 4847537
    0xb041a0705100501051207081509030702090403020705240304030810120c050a0801050601020c0f01020c0a0e04020411040308030601030c0903050d02010c030e0304061b030207050a08010506010207090c020a0204050403 95
    0x24002c2000030300c0711031002004100c952518003400b0b070382c04000c580c003100c5400c000c406210880c400160b40c81996034080d09227a903519811700b03582c10b520031a500650404000740c1040305154000649604880c0242d400c1ca4000101c3c00841d4107014180e221594054801c01c04200030074400ca000c1c81d0003410503d031403c01c3c580d640d0b038034280354554808201c071400c00c4540104076920344900220300038103c41001340310626002c030000f03494078030f01011389118502081030176100d42d100f0001508200300c040c0c103c0c3c002030340703400d828104035104a4081b1f100310f0030468a0284c94a50717601f680c0840c0e9110340320a045031101e40040d4007800140408608100360200700001090040081c0c4104e06030580001403015140e100040a6450100b040040e980c810003040003007a0340315001d030001007864150401c1c1d2040b549800c078217213402039020541c40001040080b66550301176102d240500760980072100c1256a5040c00c0c029100104184405a0842d165080250401707811041d0300c10f22170300d040020b01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 4850016 1250 4848766 4848773
    0xc09040e030301120308150117090f0d0e030d02010903051206040908030106050c0601060f0509150909010609060f0804020108060d0203010b10050d14010b0403080a0302090a030807050105060405010b041a07 90
    0x60b0000d03840060541204d8503a5000d00d03800c440080e400291411014000c0351890001a00780e880e05000c00042c0d8400c1c8002882c84903043c0200c41e22911241d0a960b00091280802060401d0070049244240240c10b0449002c41c014400d0102e42c2e50b15440711402d0042400c118000c0e036034024244e641083e10b80300706000141c1c0354402036003e0f1000381c9a0b103450781501d6400070700d0124140c02420901900d021284040794000301620b01807101143d0010340d602e020b400300d21281c0189811950170000c12400400c590750009003520175604c1b07a644160940d81034100032240054190f8000c4d0116440c6c602260b171504140c00005043c0703001800100c0d14105a00c0850011803c05000c43d00156021039148200e950030f010f8044036100d00ba09003900b9505003403145000e44103500c8024000d807800519a1281c0340250191070407448001d210b8200030381c3d07a0501140c680e028400c01c890300d51900d0700042076440c2c28482c860680d0030400c2014141070401e02d40722628004414101c0c203151041c003041001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 4851266 1250 4850016 4850023
    0x30f050307090b1204030809010603020306060607020d0501090c06020d090608011802160c1d0402130209120303040501020a08090307050703060f02041707030302060105060a0507030c0f02040c080609010b0708030c09040e 96
    0x3084130036481006442d003800c00401c10038018020100c5070b41001410405607800140c0075400800444c0d2030369848000d88006800920184002000d5500b007030400ca06205900d14910112405502550071034020780780125021441d600520010a45001c018003030b03100e0126500b0030b51403c07800014074040c440e03d054405603210f0607044402910817641440318440030040440b03030100f0408405103c4c1055070014881c444802056280c51b60b01144c250400d03681c010300304881081d1441500c0c0e030b03410142000d5000c4d6000059000101e840f8001081500e00000704880030f0a4100d805801d401d1300b10340e44caa014201200031112441e80030b00c00451110348528000d4030031440c586c02000f00070714501d03000c1c0c10b201d8140e0115207c0c14080c01b181c00026040800c462900e0b5140c034004003051128034060500038400480603412901d05150819200d400100765405040d00701d403040c406a80c1c83d28070714000c3c410010000e00d200b80a10100760312070a494060170345004018004a0180e210000d030601c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 4852516 1250 4851266 4851277
    0x70807050f1603030605010201020a0206010b03090705090405010902030105070c110103051b0c070905061009090b01030603080304050313050a0602100f06050303070b011401140403020105030612010e2107030f050307090b 96
    0x42506064400100f01078161040d0700007003601f030000b9820440e000402941302c2074140708103a00d06000000003801d125003030040502400300181070008508103807c0043c000d09001d0000c034044c1d86404d01003000640500140282e19a1050171902c55481c0134004501410b8054142c1040200421441010205d01400303000c1d0701030400000c00c400303442c3c000341c0021b0751409030009004503140408804241c4c4d10549800558440d002e012030058007580049000301803d500c09032280d04040280000c0080c080020000b02c03110441100150761203d04001c96403101c0c0c401c1e00702603408503204040382c0f090fa8201c00c0b04041c82c082d0014a8a590343d02003815540003d07021550b040130203005008000114140c420000020710b070044c110188110181d61a1041c2c2c000039042c081d0200c0003a01954403c0c0d45600401164002444003500031030b1815a500400e142c4240030940e40c0c02620b8241128009541c281609507540002c02d4151210640b4503500161400342008011000416135000100081c80c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 4853766 1250 4852516 4852537
    0x4240908061e010f0b0306011404050d140c01020c010203030a090f0203100905070605070c03140a061b030b0102030903071509081605040b030c030d03020a11060f0601020606030a0b070807050f 84
    0x18180350301000c01040c0c00105800003020051100011700c103c03601d80301070b01d9100e002824110380c2018103940c03008250043c0d50005030300c0070800380c021040001c2440c3d103401c1200542d0445000c98504801a0303150f4626005a0380164400e00c000b0700d180074107400c5076900314011000c40316100c1d25a000700f41043c0f2802c2c0501034454503840107800300401004850000d0006181c09408d000c1541c4e52800603a40c5803001424a030011001002c10240a2004043e06a07203e08200a49800d034141e61040010004c260030100786080d21085041d40040200c59103010000c3c0508510f909003024081c01c01d466010b0030081120071500409c1c80e180812500b40d401a0036406403030b0340d42c5840d0400c000d503003a03419803034004d400c00160708015840010340016050183c0c00d025886080d507105c200c2c0c0300034138500c60403200d00c100004d102c04440c03140c03641c3e4000c51080c1d00780c4442c0d550300000c3c181d03105510403000782500741010000d104036206a50341c5402800030f19290345820390107059550302d41c005000c1072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 4855016 1250 4853766 4853791
    0x1020a090e0f04030c17030403030b0102060108010b01050d050c07080703050405041104151409030109030801050301050c0f16030302070209040506060108070815010c081201080d12020424090806 85
    0x4000103600400c0040003003400d1040810036203890001c4022541c40a00000c040c403201008160820082425403640c04e184441000e8480c034060400401030441242e41e14058002e0700000705540b20103000781c200e080f03010703107c8516102e81050084020b0070010200c000f03406050044000140c05d0000400304035000b0368816031164100420401203c00051101e0b440c440704110410503800394201c880e400070b890382880b01c03181031120000042403041e4075440354994640554082010380040149050b500158000c2019a5612448640c94031903010440100b031001e00c21102c841c9114285104914072070320b0058100348040d404078200c120180c0f411500d03a0044020003c1d00d5078040c00840d4003075114034041640d400c1201c55101c80007000032040303040203203501074481070100813001c6980318511145c00c4451507a4600100743ca4111848004001500b00150401740f48424000c2e642601d030300540001020201020f099200c20200451100f40012580006621141800014030500790352442 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 4856122 1106 4855016 4855027
    0x60c030807021e0a050c030604080708031009050c12070206072307020901060819020906040504020306040e06280e120f0c1207020418050a020f0a0302030304080102 72
    0x10048144070055200b440310400182e1130310014002d205481d9032403581e03002c02d0744581c0c05481c050b0581c2018804400403d40d004010b68100414201a035549035858412400303131001100e900c008000c0c0806c0040c510000030b0500b503440400c9101400003482c095078043c00c01c37640361024120101d0001803000c0f00e00440350445031340c1038009101603915a903400c0010702521040300d404421035603110820580d11154003e0741d08200c401807040e030509081c203050000940000b00740c954000e0711003141301e0140f4414090b1342d00440e17220100001e0402c00312120034245008106a0610071701d44203141281c0200480c01207002d1514809480c3c1d2089018244d881074006c100100d8058002c0541c100c5004060a00800d500c1e442908d05101900c1480c0f014288900c4d000c20180403500030441105c018503101d02e0b0401900d0004261421064403130700424030f5030b0401d0b0440805a98009413 = true := by decide +kernel

theorem cover : BRFrame.Cov 4676266 4856122 := by
  have h0 := BRFrame.cov_init 4676266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4676266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 4676266 ≤ n) (h2 : n < 4856122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
