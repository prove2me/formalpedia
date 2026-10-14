-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0671
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:03:05.591712+00:00
-- url     : https://prove2.me/submissions/997db828-6077-4b67-8331-5185bd04ef1f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 120503597 ≤ n < 120683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 120504847 1250 120503597 120503611
    0x150a0b0406081618140310060e0a1a041a0f010e090703241e09050c0904090c170601030606080309012010050a0f050907050a0509070c060f060810050f 66
    0x405403d05407000320386151403079040c1e12501c0496032000800c603400e04407817400540150103881002a40d1043d641c00c8a1440c4940001d104a910003d04040b006510200c070700b252414400c4490015040850300302e4042c440c400008181c0c81455401c0c501c0c03c409446c0880c0c1c0b092901344020240e01c000b043c0208000381c400e6040c1034485078000000c800d4a0142240c2111001c0e443c0e0a82c0c0c0d407000700c0300c0803510b00c0d46224441600d0b400c01041208413070207664424032601a20610b810311020600c40284088002607480d05180d507400b04814804070b40e8440101450707402020154150b007003140442e07643e94000c5039039031300401184081c1e1b6080f4007070f1703140181614014404586a002407030b040c030340c244040b040181c3c6041e007044800350490384043c4954141070400c01180d1b44d0252065070b61025030160691040c0268410480c03032038040c1c0410783c418554a0001004201551100103540a04481401c1d10b03488640600510f0b2041100101c0312050807010301c81ca080080c02170110880191410b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 120506097 1250 120504847 120504871
    0xc1b080c0306072708010c050a080907061b06020f030c0a020d050406092c040b070f0c050a06020a0210020f0304171204060216050f0706140711060304060b030303150a0b040608 77
    0xc10502c0e13031408408010a800710007807006c00c850000007070080d44541c402c0004030341c56401040c0c50030000a01d2606680c3d4546401c041d480800103088003001640c041292000d40800c0140340f0726401902950181ea00500c09544400010b20041e040c011480c080004102090104000d05a07000001c801140d00c802041c4203030708140204050602440b1141b00c00d829442c80901042100582200d4400d040c0d82d0b640100c90f0a0030307641295480115072000c1c049074401d418420200320641d0003810311800b82d00403100d41c41110941c1d02e0583c0c00a0b0300d809078002c004000c010038864109403849200642210507498070b0103541002c0701044002d44060061940462400be10a0100d225041001d820004680700d44510441c4159030b007003a8092300001174914aa202c0010040000b551a003540c09040500001180d005000e4aa08000c1040d0303a20754031407001c0051500d09000550240060440900105400700c0912004500301c0d8030081034421701b00b20070040560700519454201ca550004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 120507347 1250 120506097 120506147
    0x2a020103020f0a0e040b03010216060e0c0a03050601030c0909050a030f020124030515091b0315040303020a0809030a020721050708060405010f05011202010503070c1b080c030607 78
    0x4030000e00901400390214000040c00005031500600852442482101c1c14410418404245801e03806012600c8038040031501e12000007030915040350042c08503081c111102c01304000c0008910f95865070060750560460130043c0b06002081013000003070314541d01d050110424070f5030b407260b856503401805420010700d603404014080c03007904521841180c1ca070a07100c025050741c0e24100195000d1008403142d101c0c5000202d4021804583c6910508201004d00500e60443e1101c0038a52541c484450f41401480b02405485020141c8240036034000c1c0c1c0c0041c3c40d080c1804015203801005095000c40354014484030361500d90018030201910555890249e209501d00b5480c4040306540800410074042c55101103115003001510300c2c40745010b400207000080403098600700310f9100f0f0180640142000c00c0d00800741d40910020764000d41d0f5454400b04034015a11480ca03000310035600c0282100383d0141c01c200c4040304010f0022103e02c118041d0405051103240640108810b45050300d000440b00c01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 120508597 1250 120507347 120507349
    0x1106040206032a030a02130801090f150906020a080105041d0d03020c0f010204030f0201021209060f071a0f1f180c02160b1b0a05070306110d150f062a02 67
    0x10300503c0c500d185010b0a4480c28025a0070000c0e401c0110000c80c542ca507035a00090045050140c1400b15820030340c0d030804442c1903141ca81e0030440195281e2141525000030000042c0540700409071045655030300e03041c95042000300015150080543c2c100c40c800c03d080b00080500100d0128a012010704005079201100c504d494101440c880d0000e416506c041400002d00c914120410b4605200b64280c8036195030f074240f001b110b13001340700015810020620840c04070440180080000c5030040b00d0b240e002d903402281010781c88004a40d60b00300c210100007488500c040c81e91801c400c01078441710301000c070303804d000d146110800b100c080700c00f01c0358071180800c0c4c0041c001d02000c2d0100900b0740d9405034050721015200a940d103c4084c10a2a100280001c00940008507100003182d502401a1001030700c0c548550380580b0031b8821441c000d510070044100c440c04a0b22079020301c00d41071112056040d00c1c00c1d8644a4114869000d40b091042c14030301c1c0c40010041d504001c001300d8454262116180b141c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 120509847 1250 120508597 120508651
    0xd030212280f061a040801060503030f0901080402010903060e0c15070b1b12070203090108070504050612101d090d020c0319260712030b0114030c0702030604030f110604020603 77
    0x581300c0c2c6080b0901c1103000041842e940000c01c25204104002e00015540300305040c2d591141142541e4010000d01c01e0000542c0b00740d8409030442d0051400c1c0c1205500c98481c0700c112446031150300c80b0340c3d0041501c04510700300a100a032088105038145d5041600c280c0310180c100c0d0004114650201042580c1aaa10030440a03103522403e1014591541d280420000e03580b58420b03080316001c14021000034107007900c500101e40c15100041c001c075041c40510741d40c42a2510300070b404a010111280c0740441c2801721181241201c6a52011080290614600306c904110907460070600315086603580204e1b6844c00143c4041e643c140740c0070b644500a15051075030200010100b24010501e030300403c1041a003151002d0003195009034120941c034001e030402070b011038924044c954081000307030000c25121617a0764050360380030120000d005d103400220f50000e42020021035080713002c0303a0fa203014400030030362110040301c00800300700082c03002d41801e03000248107000041c0710190401e41e109210190106072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 120511097 1250 120509847 120509849
    0x1a271806090304090608070b1902010605030111040303030b040501120311030708040303170906070e01140408070f030c120201120209060909011824090903050c0d030212280f06 77
    0x418261602400d141c00d080703890303501071320079140740504002000c181400c2c04107002c3c01315000310500c0d500d44600c1032403006082e2900000c4a0039035585500008190300d00303010300040094100820f6a0311401e5240207800c460b020f4107801e010708c0c5070100501a40d424941c80380c0745a901403c00107003110145064518600c9000307001400c2c10004a400010180c001007901c1800981960307a551981c0c4800803184e031280d0440d0020002090100f6031109540980c62440151980c01845881c00b40c42c1e14806103845c4003580a8140c9241041e030030030a0101d02981c03100500310005410141b03030050b400003400e11243e080b481400342e60003d5000007035554001100c0050300082c200c02140d44e520424802d031000b444504030241410071821001c4940380c2c83d40300158040c0c0a210044181c100101d120007402407103c104e0a10400308001c00c07680740100f080c000400b210755405641c460300700e04598840f90b0040d000e10301822128034030105031800201d00a520306200e4500180810252500c00c0103808a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 120512347 1250 120511097 120511141
    0x305130f0809210a0b060102120309033a0203060103060512060402030d0504050a0b0c070e0f0403090e04020306060f04060504020d09021008040c03061a04020408011a27 74
    0x241050301020015040042c02040d80101d036680b400ca01100340c04000c940440650111a4002918010002d421201120b42100c2c040c0704862102c00169090724aa50003505c2c098641d40c0301103040700012408000898090342d801260050002d00291510308030b15161600440703554000c400a00c150348a58000b90040a009100359401504102c002e03888910582d02a030003030041d036041d8641d0038040c000b190104c580c00351200da0424a0184440c645400580c031040540c000d0580000300d4002103008280140042c0030210014245480c0140614460350303c15130840002e00308200142c0c0e008a405036020340c0544210711100503200020303004244540089a010b44082031a030004210340d480310130400e1007074074080c00018003581d098030000c20449004103084803495007880081c20a811a0107602042c1007240c144000220009090360440e4102c0321580e9925401460440c00d8820300716880c0800340c0300741c92203007006082000b452a0721410302812281c000e0100d5204a19902c2e940e10100d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 120513597 1250 120512347 120512363
    0x5030a090821060922060f0606090608070f0806220e011d03091507051501060807081b0a0e1302030a050f0a060608060f040b090f01091802030a0201030513 68
    0x40007140d001181010742080079410300100b800210705041c4205000e014016540e403001501da00d8285880342e181c440340003181c41c1b94455038940f00f1080c03240a140040d00c001d40307500c50304504108004254a5006102c0d00400004c6050304510f603811501064020405a81902401ca030180000201340d0505a40411003403401408080c2ca000c10340c0100c21900c9009040c09819210401b01603aa0141c0c075000c40e8852403a59000d103501ca4500010041706100f0420355040354100c1540300500d80c400d9001e140030960b20010080c0c402d034400d002d03903407040d042030454407081c0e44003030502498020200d0380310900c42c5c0701d03006c1c2c94113545c0c403000700b800c00b801894150740e02c0c03038031103440b602030f00041d152a1410549440455a100c0c032a01401042d03800c60340d29500559075400402c8071a4100540c03043c1c01030b596415007505a1503c00025209000c503a1141e84c855140010200464120030b072010041c502c41c0130784600581c1e01043c85c3c03045540900c0c0114194031501c084a00b070300010310006207106 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 120514847 1250 120513597 120513607
    0x309140d0801080d03110a1b08210a020c0a080c0703061104081608030f090d02091501110109081911030703030c09050d020d0209090705030d02011a100c0305030a0908 73
    0x281d02142581c10f0765800015039080ca003c00c082541540c603071194044000006102400361644a0703000303640501521250404241c202ea19140201e07800800790080c403c4409080520a5051105007500001401d00451801851048554840a8075940200020030008007801180c8080104001654019504100b40581400c645209a1003031145401c40e0003110151840300c6081c00303201c0100c400880c0610710307109c0c41540c0e001d8a039100300a02584207084119083c0940c451020181c03089100b4000c51a48410f51800500840280c04040c0b0050381800300314000598010140c401c41c611320b1180320b100300000c66040d5415100c01303581d004103110110b070080a240d45a004007001b030280d9191b4004c455203580601101c035141c40030103504003000c20703149001810a45000c0307074001000420b5400040e2038000090408006d50817000050307440d007155a5417007a000b03103501c400702c030115003030240134503000000f808a5a001d0720180030320001000240c180412508108907099004803000d58030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 120516097 1250 120514847 120514873
    0x1401150e06030d0f02030409020703020114040821130f0c0302120d0909020301050a030f020a0906060c02150405091317120103060c020d020c04020f040509150112090f03030914 77
    0x40c00c81120154402d00c1050402d60072640100348216000031543e000d94503090926180c5030103540714640031402c40d96a01101401c4443c50703c1d0f22801144105506c0b643d0300c064a01c1c0d00000d011001c0503204141d03030602030044c6c99002c0012040d480d40c0c0142c0101c00c08030141442c1c0c8110007181c0c000b942085440c4c0d0070070054600451801100d0801d0f8465540190300c418a9004900003401080d4110750450303070070f10110785810356082d0842c0c8010007400d6001c2e2102486010340f04d29070700450110b480c0c0a508400c61400d450100d07940004480402d0519103020300040d0081400b40002694169150303880c41401049034502e101c000f040705019a8030f151400c10300c0d605000c01d21050347e43c00d20f84000e40301410b1011881c403106520030750052500c007040c001000000c0d4810a002c1040320002c00000503c0e44400c1000d510450710070032107481121010001501610a00c2c0c00720402e18904152039000850885c2400d59881d018070340001d0705c0b0307503d1401106988140c0c1c4c00d880b02e445114942908 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 120517347 1250 120516097 120516119
    0x3140c0301030b070e010c0803090a050d0806030708011404030c1704140a060c0f0311031c0f050c0304081608041e08010b12030f0307030204030812041a040f140115 72
    0x102d03840303802600c2e4280d4078010101c030154022950740d800030356a8107400c0f010440c44000340d90445503070b03810346440401da85d5841d80340c005130400100125100c5010071043d4541480004001c1c9100d00003030000003d40d00c240d500388100100003d05104290900c4400c2c0885044402001704410110030b50302e0b80c4403c0d8081c40c6032441c0c000b03103100703190700c860201d6101d1040080c082c2a80c0e201c0c031044001416076405841044089c03140700c665210a0200050040019040d0000000a0740c40000e02800740d13400c0c6415a44001e0522040a4040050100042541084902c9140c0b0702003a502400c0052901c00032520580c2e0207200103041814480721026801d400110880e41004001c00595a000e0244003004c0040440055160020300035400207142080c000e46e88482c203803400600d0a5200d942d011866001041000d04615203a01003204000b400c44034070740d04085010304008a89082d079a0040c84c1c900d030380001012072030042103003114031300309402c18045030501025128540f5141c08102c0c003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 120518597 1250 120517347 120517349
    0x1050402040b0d08071103030c070f080f070f0311010201090b280605061204060908040f03030305070203130b130b1c110903060402100e1302091e0102031903140c0301 73
    0x485549421030b10303040c03840c16415001c002640b200105081948540710150090f000740402e1390107000812050304064410320070070001e05a249569a01e25040201103460114080e886008540c403601c4c0038405800341400c1c54089a5201290b1418548080d004270b015040d0450024171031032180041c4003c120841c0002c080d650007080d03a44414491604034001640e0745441951b80001c41001920840d41030b00105950150180d4004604a4003540e0784818690160b80184401c1c2c101c0704050007015803500807540c00124a200650600001305d0b1320000b0841903100c2d0b008090b800107040b56070071452440541c010803070b41e45e8045d183c084038078125221000c400c00c1303103000500e407000d40300b030180000c0281c408510029004201036940e43e0b00b40410200720040d10300500421907003400c2c555444c100f1820030680810700c09038070340180e08107024403a00da010a440724100040300030803c80c3d07800001d880b0920a242d032550311030350f41c2000540040401400700740c00381c0c00da0020451102540302c0214 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 120519847 1250 120518597 120518599
    0x4031208071107050901050f0307050604030321050712020c1005040501020406030f1107021c0b0901021201050f0d20030714031501030b06040915050717060a03050c06210901050402 79
    0x5140300c02c145008070f4907254039000d100d42c00710500e4014007150034060240c00c038082c00501201c81440d01d400010345030b604581e0040300090310441d183c1241381403e5405442210411000380030b10f0030036010207041e4402104511750440d501203205403040d10104071104030b800f00040c00b081282000e0500d1070113075200e4010980403078101158464005103502c11450103110001c00d05003408400c1d420082080c541c01011440c406804030f007000882c0c102d243d8280101c0c00000010381d01c0c84d00418220400c44140c0c084d511619008035071200c81d4550701e10007585c0070b501c03240040ca8001405100c0140d42c9c800c0315801d8240c03050714008203190000000175011810114207d40e000307202c0d202158600c0009010080c900c2c5844c03000b043c0f80d818680c00001c1514403d40d01c020303000705201c460340c0c11078208540d020f00143c00b0001c1c50400091216055402c042c1c00c2d03803c95a11400c1da1586039031602840c03038180c0500340020b092190a20300c81d4009803040d821152805d030f00e080c0b440301c4a020707041c10b079410307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 120521097 1250 120519847 120519857
    0x15090e061c15050903040f030f020103060b0d060f0e090a030c170d02040305070504050106121509091209080f070e041a07110607030204031122110715060518070201020403120807 78
    0x20130790040000090320121080c0c40811a0b48a00307503178034040c0f08600c480c0124141512102c0108079600060060540380b000480c0001d040fa140c82000c04070816190b016241a042d00030503c00507030400b143e00310816400d402d00c10310101440c6400030005201c041990f08051022411201c1c480e60342c2c00410843c1c0c010401c0340c2c4543d40b120204412a082841050003140c2014508400340409800101d000500080003031b900369a5082e0000070703600201400c40e078403601d00c1800800541c01103040e4024203810001031a94905001c110b9070b0300c0c0c226001e6103100030f4005001800300000c4503080c0010010120010440e8180f0341c03c09006a203804400d484c65000e01c6000070405446803083e41c048a403c9030000c071441103c03106005e8004450410460030a16103402c552014200c0c1c041d0802e4650514686a039038621804d00001c03514030040000c08403818040200655601c1004516020074205003c10b21030712500380031380c0240310320703400100880501042d1015068006108920503079103a10781c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 120522347 1250 120521097 120521101
    0x10605181c0c090c2709020310061806090b09040b040f020310080d08180309030a050c1008090a02090915070f0f11120309030408031201050a15090e061c1505 69
    0x31505556504130000c001550001010740c02c40705400074014140c0540a001c0e04460705c03001803030103a900403110103000303500704074041028035404183c80000d4a4600c4074072075800c0c10300e24014541d80b2644541c5191817404541092681d849601441145c07000410800c0a0441e45088501039002101c40030040d40040d50001020140810301c00e40c41b4285584000c55682c0c0c103001c00008100010307001501d031001b0b0003107132080c2d1010440c0145a6000340010590b030211b46042101c5140b4041030581002903820510101100015800075880c1d8100c640c401c1d140e448003002454500e143c1072115104040000f400561500306603241c000501d00d13a20856000000403050310014032440032201194030075401d9101d0034140d240516081641d010a40e40340560f524403062454205001e00000403403103100401c6181b42c1101e504006041041c000880142c4403500501404443e128200503809200c0000f29641c0c5c0303c070300003000001d20000781040b080d000e0410725071809200c80d03885003042c90040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 120523597 1250 120522347 120522359
    0x120c050f0607050c27071e210c0201090803010902040321200c060406020601080105090708060403050d150b0a2c06130e010b0a090905010608010605181c0c 68
    0x100e802c00d941200052010141a800340700240300300003551844101e00a104040f5a064100d00a008484a6480e83c03007500c10b07800710480080c40d070701d1100188803580842a038104840d42e403d000000180c04000b50b8200043c1003a400740440940c001c0c80c50380f0000000c07070a10303e01e03400382c01582d0040c13040e80792102c80f801d00c01090780001c18101c4041108400b0302103c200324021028504400301d81a91134280c81100070416a4205801440250b00318500612212409100381340c0d00c01c512100900c095803a100409444000c00761003d41040400241404101e10f540c1002803007005200f41060380302e03500e0400200076007118a00e90001880084502101d91640704000d011800c1c0b4a410300340104040b082001d2644081550f11112000c4880050507640f00071480740202804408960381e54030303509008045440c9500400d40003031604006222840d4040001c034103491050414a956000580f607031103c456000680075808089001c2a02d217a44006c0c1c181d80803d072140040c9400070b92908 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 120524847 1250 120523597 120523609
    0x120f05060d060c0210020d060501030b0904030507120e0607030306060e09240f040e0109031101060f050405070e03100c11011b0503071119030f030b01080604020d06120c050f 76
    0x5940180e1080c1401c20101c04142c85a001e1460100e0718012108a084c02a0241042c1c0e0440c2e20302ea410640d0b43c0a0401255030540500090004216101c0c9064030b0070303030f81c05000c41c003820101030080400c00c100e14483c94068001c02030340040c001c201d00d1300c6140e81c1c41c0040141400e80034000c00200e00c41512803250800f1001a8000d402400e840c0c00042c44c00c00503a044000f0900c0075a6001000440c0d4480603100d6206100c0303500880800440d0840316400e0180c64240312050700c40b81a8500f00d01005000ca440011100b0b03190f04880225031500c0d007480444d81c0e460310362000c42c0c1c5402a440000300514040d07028081c1c0561544070f00c011442003e4985080f650b80e420107900300c1007620485410140704900031544540c00e41001ca0f0391280110826140c880c43c1c0240498401510a040c0300341600994a4422141c00f441c0901c0441c004c3d0300000c061485c00b0b4180ba010b1034002c541c00c4213007102502301502070401d403d012100d250560605e01454a01845414082d540a82914a041c180300c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 120526097 1250 120524847 120524851
    0x909060c0206070228020604080601030c050904050607080402060408150114030c130c030603080a11060606090d021003200d06080f070b1e0406020f06010f052202130303120f05 77
    0xc0d00949005c10200010b01207540d000f008400004440c402c60f9070041e44d818000c1c201800891008140300c0d811403401d43c81012490300304e68420312201c4200300004000041c0a903000d0b10030303d81060342d52a9031001c521140141e410190030340c0943c0058003218044c001110f81260410307460303d90341140c117606058540715a2000c2d0758005024010400400e009a040449050140d1400040e40b80c6e4945548005c4d8010f5240240041c64000c00d1041180080003c5500554100c88182c46c1c910307a640024020108c0401c0280030360326600f20300c000c0303601070340c03200c10104040c51079850051410030212010764030500300045818070302000030039103450002d1141e428010100003001c0340d03070500124000640000d80c001c8641c524041c0f51004525002001c0c10062a598009000724400603c0003401c20b00140c01060003041200420030940c0d81e6001803984610200400640002030081100040d00c41e040c09060580b1500710b00108040d0b0000b0204160460710a08102d00702d608400711040d2201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 120527347 1250 120526097 120526111
    0x1c120905130509240403090501090b0304021002010905100605011715010c080c16090b0904150207020301141503160602030403140115030305091e06190c0803010909060c0206 76
    0x10000c0c075515210340300e500881d0000110404c071402d900344914070211400c0621034818810300d400c03050004240d013007040080035080900301441e06600342007205c2c0480c000240046c2c441c90840001c50b41c00c60007940b00e101d140d90801c06845201da0130407400b1010b400785100d0b06001662406e10001120000d0324414041e074154070060342403034580790044406a58005c03098031824020006103076405070401141c202c1c0084860015800740c40d008454041300c26004509000710603450030400081c0f64048050014281070500580712a07150020a00402c507203a921254122040184003034034500c0181810740f02000c80807079aa4810100110307036054118420800540d00a0005000184000c800d1441c4030303245100000b0341070815092422419020341c01540810400107000000c1d0801e52140c01011500b260140620742d10500440c28500ca00d502040e4424401100d045059210340184117405800c411250f03120f50319911010018420700f5402c4802d140742005401e42c0b580023040051141c41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 120528597 1250 120527347 120527359
    0x1605060f0403032a050105060112020a121d01060306050f07110712020111010f050108010b01020304030b0604090206090a06030f1406090610031803021e01020f0301170304051c120905 80
    0x114642d42901c10550130707040078105030754024100381c2a00c1c06038110401c0714018000420b290034480005007040388c003503031803190b01401040105001c0d07800c0001ca00c800d005003000020440b0310007035030040d8411210b207404455400c2c50f80020500401d0f401143c000c5003a5030a850190312040700560315046401c0100d940c03604040000c0240c2d500c0294003104550040c10900c841c018914860f50848002546641c1c0a5940e00010700000d0000d1107400c000f40d00a000071803400d429a110741c002e003c4000d00881c0b180d03444005107001c5444d40001d075000c2d03260181880540c41e89428014015280c4022001c01491900e00d084100d0125000c42c1c0380600000703460045180c44030018040343c001140e08800506441d0020b0114100004c00c0802c00c1600070360103042c101d0700810303002e4045030041e0b000101d103038010b0252a00445034602100c1c111404151498904408000d81070300314007803a17104075880312109290082602c100380c070080c11544500f400d218065604402901c1c41041401a550441 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 120529847 1250 120528597 120528599
    0x20703080f07091206180804090911010503190504050114040308070305060a050f01030b0103151e150e120c040c170601020d0807030c0e0d0807030f0203040503100218121605060f04 79
    0x4000354086e03800940d50111a00341c0a0582e1518500d0303a110341d008580c0340740e450780c01c81e00f80a44c8018844800400340f81c240d10b0350619155040090942c504520000c555a0002c50100242544100c11501a402d0342c9510740c03400d405d020b060703223904440010201e41072000080d41c40c5441d03940e002c1a2030f80102540b4001804070011402000c10821a034107256580d12044050360700d0036845d400400706100c980d40d04600d001c000c2c14001038a80d1000d001108410416600302e40c104100007030942064400d0303004607580d0a0590700e0200c100e5062500b0520f003441705034100da4801000101503a05004d03840350340d102c080049a60b82c0e02d030812080010420404a00018403e400ca8155080d00e4580a85520341c1040050111644480203c801002c0040c1d44001c140d001060000c003103400d40041c41c00c0c50326200c040f170f481c0e0036000642d5560a600041c0f4049401c032262403000014030140c8081881881042c3c500d80d0307184100242207413070061940010fa90b1610404030784108d00c40b038403014207003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 120531097 1250 120529847 120529853
    0x50703050f160506010f06120209100806030a080d0b010e030a05210706020c030307021e070501080408040905041b0b0403020604030605130206030a060501030c0905180613020703080f070912 83
    0xe6084010b8400409440d114a01d000c2142041928043d01c3c1c49001c4180c402e143c101d010702620094040c422003e0b00600000c180b56440300003c0500c0d4026042946455440d0b1001034201740010030010202e54021a004913070301c0c00c030b83c400803c110080e2559075603503c2c25030801d130341c500060704020490b0740f15880210004a80c504031803001c2400c07102803400d015540e40d5003010b176004600d6454890b8004010001110307410441210803091241c6110503240d010011039840b40e8450049505125140b8045800c00141e54120b030000c0c500d00da01041076007441c1ca4100c04001c00c0706510441e44865400120b00581e804080360100c0e580201039600d41403640d522a0054000100038403d151425140c00d03000d600c6540066101da0701241c4009001414a03001408580003800e01404120400d10f0a20442c0c441c2402415a004642c40c0040143e4800d000a500c0e0b141c0c45411140309800440c420003090b800229a034040c014520740100e1980e141001110158503034442c0c0442a10391403100404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 120532347 1250 120531097 120531127
    0xa05090d210906061a1c0c050706022116031d0c01030b06070b0c13080a11042a09060e0f01021e0c0402070c0305060f04030815030c0301060602030306010f05070305 72
    0xb284107900105125990f080b803001c0c02c00030301d1821607100e540000d481920700610805405805e441003001c0105804c0010b00529a00403e14010700701c9500040c10b2151101c48400040c2240f02821788010b5442c1030907901c4025441640c00101080c1008150710030703401d0f000704012440006000908a40c4e082400443c080c180c6480d00716040b420400c00b20021480c80048240304000c000703d440d035904a28041d10540ca82c807684104610b4210114040c000f40c1c8042d48034007100421035002c02c403495000c0035050b900d07180303441c01050350040001040ea195000401e40c0d08407602520354450b603036140d03014402018054812180140c00c01c1014440802d0302c4000c841103903100d007080b1882c000100000c00c049034024401610b5441c0440020010410208200c035845500108440343c01d00302681c014200c01d50140c6685204480700101c08419201045a00d428003c001c0090050340d41d00d500281d12a03000b40c9003103001a0011001d1070705c40780110116001c841c0c1c569038246c40d126202c2c8003200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 120533597 1250 120532347 120532361
    0x906061701050906190b03090c0a06030b060304060914070618050301090c05191703040f051c1e08030a050a11030c07080a11100606020705040b22020c060a05090d21 72
    0x2018a0b032401c5d0201e20030f064040614810441e050080480351118001c0040850300d984c0800101810031051400c10385882007505d400c15444400807800b61101d1605070481c3c1701c030001d0309456100d8000006100c903071001c520801c142090340c0e4075014076207542c00c0c107081c0c40b40201d025007258a0700d1005c020a00307080c4018140801100d169120380c1e03407520f40069014201c00c00b4940c4503400490306100c1c0000a06c90f602c0201011101104000740e1206200090205100064800c1c2c82c0c5558240c842c1035605050180c940e80011748036981d182c001c5da0507008200c2a02d604030b035148ce01d40d00c41110103402c0100c0c1c0c026880c05001c1418045c6c0e40e60380048507402181c14400304022114408000d100c01c00103803441440c16400400d1f00c07414150002e04c2d003000b9900c010721507824092942c1003a01d55000c079101c0c006118541c0c0919610850402c400b0f0310841c00c4000051051104101c001c50b0140e20050041d0741d0f4400343c64008104903401c4919401201600b040d051140040c0360b80080941c1c0411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 120534847 1250 120533597 120533629
    0x20d0206090d021509012006040215091809010b04140c03060d0804061e030204060504030305090301060b030405061e04020105041415030106090e010510020604020108070314010906061701050906 85
    0x44030781c00581c0c1c042194a0b20b81105442c4c851004503c6007002c2da0400c8400150b0142d120760300c0080221803c03415941c02c4090400b90042c01540000e180e001c0c07003072003101d4900e103014043d60f0603030401d16101407003102d04031743d0807071503502e000078005103480d0501034501c00003084108181a521031035544440381d400945100c0d070100b00482500c00290100c0080c0000b0a01911468805100b680b01c0b60031007018100030000300751042206008a0b50000c0543d029130b9050328085445011101c00710f0b0040000e50002501204040208400c000e40018800d21841e40b000e501c0f01410361080c0c034800800019500240450420b001c00d0107402c100500c05038440d40b00401c90b0803400c90721b00141c100c541c0203800c544001040403030180045000003048038018082515500d407004802d440003500c40e40083e100074100f05214002c114114030940007003241c2c41c40c2410030981540d55240d03071380084c4454401d400c0880c0c90340050307000310142ca011039812102c011b05152503c0e60360000300200341100820079 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 120536097 1250 120534847 120534859
    0xb0919061d040b0a060b0307050a051c0902030706020c090a020306040902120c100c020607030e190b25150e010e03041203090e0103050d0507080705060901060302040b0409020d020609 80
    0x15228116607080c244180014682007a6041c54107184451140c0180300c0d14680341803281c2006890350700000c80360f00011518059445c1c0007041005c40c1c05104918509910041060034800591040c3d80074000c003501c220b048404283c0c3d150001d980310248940311640c41018040001c1400c0c00035001180d100000410000340c441440d03000904003141d06c0d100e10700c07175031060200b8003135402c20003044005a03e690400c1d418482c0780e0740c0091f0407446083c1d401030801090614034202511010003003c94002812400280300d511003031000c42d01d801441e022016880082e0001030321402c101d04c0010340c250854146115030b4517001c4490080c0517280c07102c2c43c1a6507205103046007a0803d00141c400350070011040040d481c100c0c14010290a140d800103048998003000400006a0000d0b42e0b41c26203405003046900d5121606003e18140a03410003d0410700550080012100040d807094066a100f00d40800483d03800c2c03170910040380c6041e84000e4000820f600703c01c0251030828003806e1289402000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 120537347 1250 120536097 120536099
    0x1401060909090f230d050903031b0c10030c030b0a05030a1704050a0e090d1e1404030b04030e19050f1917030301030b06041b050a110105090d0306090b091906 69
    0x182c641342c108991400140000d0034051402c01403014010302910845a250003400c10000000080c3c43e4490714034201243e0f018141c0001841c0e0090001811140008015002c0c0c1070842c4000340280891081d0040041c0c54040ca980b60ba04d800024507096078000b038014100030716103640e00c03940c032241c00d55050741050003440005459030ba04003101d001b40800c40383c1c42c2508c0c185010100e02d40f20341020118180303c644d08180700c0c03884246403954601d4401e0315061035400040718003c00b40788070b90f0300045c022a581c42c0400080c076800c200c01c400c52031416a03801e007982055200d4039126110318003482d44d122a102d003042000340f80444050100601c60030054007026a03500800d581d03082c80c611070781d1641c1c0020004106120510303901c03e0b8030120542d428081007000700342880d9441e100079200c00a004000c642c6503003452017401c054000020b4103008202c1424030b0a100d990b0344240314140d000190400c040429030034124010045080c801a1004049495500036912850b001c1d06c8607051455490b00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 120538597 1250 120537347 120537353
    0x504150507090303020c030d0e0d1401090b0f06100f0e030c030d0309120509060d02030a02070218010f061110050c1e04050f090f010510020c030f07091401060909090f 73
    0x10030180a082151181c650041c518500a1b0074030412000300c520176000030306959210390300b001c00c1c001400021607295800d8034051800d81c01130f01e4450030f0340308950710741400c01c01005141c1c01014080c1c41000d180100307130780d0381c2c80400c2440b141e000204000140c0300110750050340d014086903800c03840000c00780c44101c5001c40100340313040000303029500043d840c1c4c003581e4240714090b00c10240120141ca4810719110032100818018804e41618074003940d40000080c402c0c6c503955040e9038080340d0090659401114843c94030b0b4076072000303014803ca01040c4080015445000e1016044a003007000007800c40d00701070200034002010014441c00d00c0ca24100001c0b17032504d1124541c020100c40000c030382501e0354100000e0003d280400e8480d030340518000342c180300d41b60160303014a60451780f04448107075540410f50001c80c20081c0007000356802d885105041e07014040c1c04650b040c00d580d0b01d0344e410822503800d0010703001641c600703104400220710020b00070301000c1e40507040b051355580254850124605941d0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 120539847 1250 120538597 120538601
    0x50c1509010f05060109270207080c0f0601050f030a020927210f030a0c031b090518040c030b0c070c060f0f030213090504051c0210050106020d080604050415 69
    0x25a618001d07592081e00c951000c41c180705180c0c0107103007031070b20300001c504210355003000040c04060024002000071050244802540484e04a00d030320010540d151242c072001c090361448007411300801401003900102e01420800b80d102c60841e03004000f070809500640a0084011000d4608050200712010690100207100511404145d40d1801007000361a1300c0a105c100e00d100c8178100c0c1c0d0070340c0100304a5200d040a5000c0d20781050303007603a000901c1842100b06400800c1007040c003000c2d80700054140742281c0d412200000031603000741c2e00701e1b60004950345200001ca0b812070b80103010515005090000c140340402c1f5540c4a51403403101c0346862110b03100c686d9901c859a000d5000a1024824000125400208826490f0140c201507050000d1900341c10280f084034064800240d64410005d810f10804115000358071410704040241442180c0d00251034032415441c5002460410000040d80c0740b000564001e126203a0303440242e17640b511403c01008c4c2c04007510581d140030800b035030641c072401d00d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 120541097 1250 120539847 120539851
    0xc0a12060b101214040201120b0a030512041e0e4311010c02102703030204050a0803090307050105070311060702070501030e1902040b0a0308030f0414030c0d050c15 72
    0x552100400055244103c5080d01c1000c0c0c2c014040201d968103000040c1d80000491502404100c404903101d550034010138440109a400688a445040701a4010344101c400a000703842464680d001c501403501070700c5112425034800c4c03441c4400454001914040c1c104610440c0780003000b00c0e080003201003088180c1d01c0c5181c80000408a8034411088400b54008408030400d0b00981d000740001d440050010352117041c5232102c0002641c0307a031881c04200005120100790b040070510f041402007203a090050080d00030740100390251196a4000c03a861100009170348603810004c00900c03081c0c0c00c1000448583d00720003002c40a0040c144207084c0702810501c210ba20404040c3d00820280b440d01c0c00040c10ba51004d0b03403d09080e00007250710008842000180d001081d015036010503180c0010340420700c000c0560380040c1c02d01c2da01000f4010f000c03003040140c0b40100e0151400c40d04881540d41002c0d100d102c2d01429140f2175110946500c41680a007001e0f00c0000402000d0b03915a10f4001c510b00080704017 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 120542347 1250 120541097 120541129
    0x2100909020304080d0e0a0210030b060d0f05010e0603071a0702040e03120906130308010b2802010203011a0c030d090c0b12040203061e04030302130f0b090108090c0a12060b 76
    0x1045941c5a4178552007a6840d40303001c0c6c401810016103580100d04e4031380ca0307659800105a100c084000c2c0343e4031210110707403645404520410010050320740c0c81d00102000e001b800d104603440345c0401c01c18a0009602401d170b95501d6003440d4005101d4281c200a17602c140000c0340c005840340021103000a051000c1c00752040c405846030420b00d01408441d0400714004c001911040320010100d01082c0e1190003a03043d2400100003590325182100c2c0c0c0200d03001c07545150000d40300085180e5144540c190051812520683d544103a07854003002d000429000748114070003907034804d21400b010303030105070007844996020310030a00b402902c6a1071902c40354010880341d005085440306200443c10300300503180d131201e0302e40b40301380e0321010b141d0240b4118080036201078209600030489039516042c500c2c8420051191251790401d00741e84904441c501c0d00b100f032a1a010905500015081c02004942801c810400422140060381010f11015085a00c000192580c036607800c01442961990f00b00c00200c809 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 120543597 1250 120542347 120542363
    0x30501021305010302130612090b010f031106030103030f0804030e03160611030301080a1403040f06090303020607090e070c050106030804060903020307080d2a0f08030907080703080702100909020304 87
    0x70811850300448481d581c0325038101031041207104410030100710880107680052608803d0031a001482c403000c3c14140b28003a1449040300000941100943e16100840e4410720224201004910801089000074440500030480160090b41391622407c0c103284d0045c8681000c03070a00d111b41c000310f4a0100d0b07550001c008860310070401c2c003840d900041704580005120000350f10355814441c1d0144c5031000c00300014841307009800244d0698105000b5a0046c3c111007944070300031603030782200a05811644c8001d8015025030400304d06030a00c50040602a180016488a420f440c1c00301c00300c0d24142e4044041e0780303a558940c2d02000140950000700010002039407444444c5045004150500301c0302ea1203139411350300043c6440c0364640c01c00360004002c1d11846000541c41210506500c544d170028034000d0800440700750076810402c04201440c0a080c0c1c0004803030b0100e440307010566880e2a2030002802c030700000e02440c40103281150031040354180c5498503040e001d9907908046e040c0d81064038112000c607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 120544847 1250 120543597 120543607
    0x161b030305060f04060503070e180102070302070e15101107090f0b03010c020d02070b0306121005070801080a020102030d0f02040503030c100b0a05090f0406021603020c030f03030f070e041503050102 87
    0x116080003d085040c00c102c404000091800002960306e050740d11079904120001c0c000203d1500840c1070912000c4e50346230007550784001c2450001c3d11800b4a009100150b141040440d00ea40b0521320b0f8541c20307060140428141c50360801e0191a82c804c2075944a206d03210300c1c04041914400350041d01980c08030014042031085481d400c1509490096142d0000c550100d0041d2141903800500c03030048550f0122800d0b035036110310740032443c1480149981d0791188a4402081c581c0003c80e80300504c980c1c81c556039031031242d0b00d0710241900c5500204002e401030b40140104c43c55101c4a5001071508401a0030061030140d41c1c1e0b012a0075500080c2400440b43c1001030540c0c03984089020740b880b2800101d815189244c2002e00240b0803110191014900280c1400082d003042060340c1111294a2501c110400e85403003882e0007542c030754110000e6402030050400101a841000094a00aa0750140a40f44543d10107800325072a803141c40c482c55001340c5034082c441c2221480b0f241c110241d4090360000da0b4030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 120546097 1250 120544847 120544849
    0x30090e060108160e0301060e04031d0609030c120a05060103050a0309080c01140705010b0301020d0f0f06031e05070e0c040e09060603030f072a0501020607050909161b03030506 77
    0x10000420301070500c010241081070040c2d02c00c01d1846952a1810108803076814140800d00410050300302d50300744502c1c2402e21052503008241c4c81441041d580a240c40901d48005200560207900c2403d070305079014516009903880c00140040d0a10289011103c4811140e1100383c41d000003a4000d440541000d80100e05040d4022140d40c0500000c1008140d45490350000078021040300c1c09071040c07034a010602c40d0030400b0a4002c072501c02c5004000355242c003a560101c000604800001b8423006243c0501d2610807403003400750004481c2c00c00003078001246c1c0800f03c00d80f401c1480104171040c0c06a07050206103141014880381c0a00c105647c495225410301200c161000c90181054207140c4c810010046556000021510100f11024006840ba4038618140d00c1c0001c02092540342502c10b100d0740410f004000880c0000c59009a003103c45c00c2e04d44100540d418403445040541240916001404840160040004050079031411500c1d40a1013240703d60540403d800480001c1d860b107040c0801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 120547347 1250 120546097 120546119
    0x140601060c051204060c030804020103090b01090b0f04140109150e010e160206041119090203150301050f010b031506161101021e060411040b03030c010b0406213009 72
    0x5036002004105240c5410200044d06c0792811200003000c01c51400c0000301164800d420a084c1c466000381c50800f2561202940d8010303002016251707000f40b01d0a0794005c814506400762075201c0d4550321030208140d007030407203c0c00a80100e903904000c080c14030780001ba070100e10f2a80e02d8000d04803001c4040707107824000e0900e81307131182042a06045600c081c080c800401c0d800d1240080130074045500c854096901900c2c00d500012580c041ca00c041d102204010341e1426400710600380d298104c008200917603c49081408014081c043c0c448124400c1c400103c0711314a8880d8005a458002c0141d81000c2c400360b01c0c00b5082000d08000c80d4004140800d130211960100009107240306441342e0748030350200d1001140d6a841d801440074200744003604804500392256400070001c0c41c005010780c0c3e03440b41511003080c013802d1407034901401103240250000d280d010000c40300305501030500b80c1c06036050781a20b40e003220b04105580d4101110b002c540c641680c0d90402e95211164180b0384038108402e2600f000865 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 120548597 1250 120547347 120547363
    0xc090204060f0e030708150405060a11040306020919061101060608091207110303131e0605180f0418050708160302091506180321090409140601060c05 66
    0x4014014003080c00304980101c201030700e0400b00c3c5401c01110440100180c54585281d00a501d14010300120b02c90646003607075010300c95402001164003a0311180640e8049440c1d201010807002c0701404140001403445d0010103030441e00800c200d002d410890800c0d072003400c8990016010541020701c50b28011000c1c01000c000b00705604086841d4a006001961180142c44610580c00070000e100005c12200b59141803942d00c0150031a61502c0200d50494910315440c011042152820b010340995804600050300588595076103240c1040c010700c104418085076003014a90090002c16440010349603407041c4402c1d5000f1600070740c0700c52070300e08106003400829004062b040d00700000a04060021054080c02c40e40d0503900a50b4a41e01c0b810380421000502503134030340c8404005110310402010f00a41e4910220440581e1101058440c03c903e044940c1d440184c0d15a405201c88402e45ca0700e640203183c000d01405c060210324091788881c60070203800b60403a4010030403110f071400501c02c0030004c0d09 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 120549847 1250 120548597 120548609
    0xf030721050a0515090c300111070b0603100606120203150316090c0504031115070b0705070605010503060402010914060403020301020c03040801060501052104021305040605070f05040605031816030804030c 90
    0x11300105048000801610011544c40e001c041650003443e2104001d510110709c00e16040f00d01e507264040e83c134040d101c46030199841440307403241d06c4100d02c12032014401c0d503045500303035151502000340507041caa000e50801440c0307000c400c400c40d400720210b44003800781800c0d00200300050105c103420658000101c4442015080c10801d05002c1400014004001c07285201011102c442d20540d140600070308902c51801c00410b241c84100900c510141c01c100503080d540d1046400b40400c0c0e0701c0f44281030343c0d988200d401a00241da101002c101945903c503442d81c10002c0580300600e0f141d00d9801003400e992000c410a05c4036480000c0400140c10f080c813036003018207024038020b440d20900c000108088035002140d04020a55036002c2170865848500300030703454024200a110741e207494241080200011260355000c24813844140d0140d5100e40200d401752544c54881b142162124484000d00304800d503403400080c4103100f1909400039080141d5001188100b41d036a544074290701e045080454a58480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 120551097 1250 120549847 120549859
    0x9031707080402041a01271e0503010c05120619050a0f090c0306120303020901030207150c08010801050c043005031c110a05090a09020310050f030721050a0515090c 72
    0x2244442c1e81c0250307607803103010104028028102400000700c1f10200b995004281d600b9039080306940c0c9122145000301200d81c114020040d48001e603000340c2d0584201e10426900e032011100048681c0741c402009a0291404500d201c1e01a442e907002c1380c0c01c111141c0001c0051403001c001000480303441e0140100c08c00c00c80c03405100d914500740300f2215225440d0b5009041c9500450084c60903440f07075040d101000d4101440e1004902001140c000900e420081c0c1c80019407039000106110360705001d1180a2168902100c0c50300346031020550038240404107000d8030b09902c0b10350514108000050b00141c03030168010b55955504000c4001500c18003840703404043c0d003895050051451031005803000c654081c00c00b943d803581c0d144001007080a050b048961101d20120911144116880600060307031825982d4058043d0b5240415a944e42c05109050034241140d04810105d40480700001215200380219490303d15980c0d14141004a0150081400c0d144001004032000e000c210b004d48402c0d0984417 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 120552347 1250 120551097 120551141
    0x10e010207050f210f0d18030206070e01080c090102010f1103072717010f060305010b0a050405040803070e060c010c020d12020a0f08060a03050105010816080f070302040903170708040204 82
    0x400109a10b4890341008010089440e2072400c4401041b50b15014150004005401c1c0340d03000319840800c03100d401c0d001482854002903816006014868020b9016111007103240d490f47c1c8044229405507900780c0c119500c94044400d00051800761062001c1c541a03526100e1134607a100410882c264002041268030b41e000e150f042c1f01250102d40305441c201c81840e0721b13018043e0111800351010f19441400c07036181601c000706022040d80b14100f8800100c1e1940b40c140d985070200020303250241c034054a00f00040000c902c1441c020004648802006859203052100099a660031648545043c00160300b01c040c40103001079110300d1150304000c00050841c14074000c1e4600900c4c1a800b0355282051061200120303007640d80341481c480003598400000c0c4000c1d23855a0320103494928820b040703510040c1d000e2001c90b07000d501040d21540d00b0440d034014484c140c91038007000050300d00c1400560610800c0d0380d01c10654443c40c1c413020700c14070301900c4110721414144140302c1142c803200a246a02089090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 120553597 1250 120552347 120552373
    0x80f060c0f130312030501150c020604090b0103090b1303080a0203220201110f15060d030c03081f0905070206160c030809070f0609080705100827010e010207050f 71
    0x4292a1003508403004907032281000503000c1000c0b551900050070074905000902c400941c0b5803c400c0c184c1d4902d00c100580300241a400355100407501900a502580c02c0c0402d0041403515030003d4081117052402085038006900c4030440ca910075501d54040764064031089040c0340e00401816040000103130210f255141010908515040440321254103812a4084c1c0e001e5a1141700e0410000b00c0c400d003030f1492801c0300002d195944410414200109800f039001a03003e00c2c00c50b03911504c05406031540104008255070403030302c242006200f01c26440f00545c10003800c01d14510242c000c0d042c40200042d9038100300301c000c1d15094005111254200d0784208882c0e00c0d59002c0e03070003424183e06003031410068986007046410701a19803c6001409041d0a001031140c1d4030200303010445d100803090b104420744503001c0c49800310381d6410110100d51148041840660740e02801c111034100401c2007048051019030300c07420b480007050622100e0390040748060910809100c0c1200700e20f006401801d0450a1403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 120554847 1250 120553597 120553621
    0xf06120507020a0b0f040c080d0c0309050a0b0f0a020a0f0c092a1409030118020a230105090d0c0906060e0a1518030f0c090614030606120c040f0204080f06 68
    0x109006982d085102c040340402031500181d20107030a511090b9030903016600401041ca600651092f00003a03200000090503043c1101d00c07501b5118120a1549000c480c1c0c4007014203079201c20900c0b4114440c1c20400d4001c10307008003614000e94030440d0040c001c2490b0070511415039102e8001d5440c07400508900d50018409004040b0b07201066007000ca95140301c40604a0302c500611034026015400e116945485103105020b080540f403007101c1007285103803901c840000000030104040c4400c1c55030407200e41030b903025a02410750040010148041c00d2407550f0343c00310b04000c66118441d0a91200001d2008a40285d85045000402d4404041040c0f410650103089100c1c20b00840921a1180110051030107400001010b150400d05101c04045a482d202a15681904c249008135186c020301054141d1030280c184040c138801401040162100d104001025000301580600b40c428040d0700b0005131074600400d09110f0079002d0060b115490b10080d542001d009000302c04040d0414410000603466803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 120556097 1250 120554847 120554851
    0x801150207090c0c020d0503040302011e020303070315050d05010c0e0303120f0a02070b16020d030509060609061f050711060c0304030303051317031e0601020a08070c0f06120507020a0b 81
    0x403601c0420b9480d1000f00640e001c0980f42000b03500444100030083c10f2250010041045a1003030382c2d43d5800c0d0303841818907845030000c0462840140c004002181c4520320a41040d40707000381c9503912514560703403200014501207201c04115856510b4466684c01c0f03940160310384000c02c000f034011358030306a4602c1005102080003010a1034102400000c00d054110550503078a006601c56490011810900b44004187d02101403d000520401600100c2d80f0321031302401c0d004208250081c1380c40d0b1070729801c103d00c215000b00780c02d4125203011902d510460005450b0400d14a05451b099903030038441c00c0c1500060485c0c0a5207010307010420071100320240c0001218200c83d01894001407d8445840042e94014100805842c0032030b40f0400038800c0d88441c00850250211004440e030184c0711403410700c0e24030012101c490240c2c00104505010501540040c141e4502c6061a41d1109441c0c48140544040740e4000000062034070100f160028540d12071140c0100090000305644141a5a103501c42240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 120557347 1250 120556097 120556109
    0x3060c09060f130b07260412060e010e07090605010e04020c0c0118150807121127030a03050310080f0c040e01150308090a050607020f0d020a120b0103030801150207 72
    0x800200a8012642c3d6600341015000c42100b00e0741d42c600c10305241c0c008039030485c007110807040000c03402030b406d803440c0301111300300c0d003070040c0c00208101e0f1038603000010403083c200c0702d8180d500c070b40a90850390300603c140c0d405402c24042c006812801c1c44001888528041c00107401984100b124000788040000c2041c80380ca001d18040c040c2c140000c2090346d0713510341c50384140d4440d2004d02e0311144480c1c01071070840c4074891035641c030291158012542c80565143d0103001000b410200880b1001079014001c179102a452342d10000b42014202012a00c0c2802d900000c1d0000342c004000c0c410a54040004a4020003840c00100103034141044203d464a031540d007481d101302d0b80c03029180b02c3d014003034000313500c0707085844400c0d01e940d0341e603040c44c000301e90250403018880c041004020070305140190036210302d99000707070110803a00c43c40018001d60070351071141664094080c20000071411207400c085403080b84120400480c0d9451490090546107041e00706140741c68210900c9841694001494021148 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 120558597 1250 120557347 120557377
    0x30312060307180b1003200307030204080a05060618010f1512290d0b220c03060f06050f0607120e06040b07050706020102041206050712020a030b03060c0906 69
    0x120303203000a1401d040d6500c140150f40350945070080c2e030a51580310802c4143e050700e420301004101d0008400700c41d40c1d0f124030280089034100c2c48621401010103194411301a040040ca0305407a03981c400d00e0315843c4841200c5a9110408010990425041001c40100031000315131540d4100101d04048603d03038000d82c16403c0d50020013811140c0701d507100e0b1110414811040140e41480044554107a06c01072521038a0719401c80364000d54241004a150140d800003005980d580b00da180668030f6403803920310240f4881e90100403d000c07804c081401c1004600c203290002e41c1c846c081c1d029600791400c540c40030384a80b140c0c84032044a901d4140c212003517113510402c038181c002200c400985208a038000e4080c1c0044c4042800b0840182d444c0051584c24028004c6038429a5940c00c107c0c02d030301c81e0f40030b084c071305001030b681e400d000582c0c40d005540c020303540d420501035902c2085801c0040342c0001c8135906c0000e45440a84110b42414012140c2005100c102e283ca84203911700410341c540b050100c5485181 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 120559847 1250 120558597 120558601
    0x20901060e130903030e12040b091521040b0a0207110f03011401060c0203060901020c030715231609060807120b0303030106081b03041502030903090406170d02010b030312 75
    0x41e0b103000a00c0c00780c0c42c018500300060f0300c82e41001401841c68811950b0603116443d460620703562010161070448006c854001e152102100500c00182021402440425000e01c104031450808170181d068041251080704e005c0d203403e05003002070b00c90244c04a1655841000148086051090344525510040c0c07080c030b10700450b44002c2401403c0b400c055031350403c0c0e19400481d0b010391000d01a25424001c40032200d80d82c039420540b074200e01c00d15851031210752040000b1400105148038a4000d5041880c2c00110102d483c0c020b0a08100c090301c500100c1202c8008021010200003120580080c86180c001b520904000024010380c0703001d041c0d1401d2140c43c8008220100158201a0b0b83d40301c050f003620b45a50352010090f0940b407055a2000b0003040c00400290030380c40f04001d40e0320071a0040d80c0c54048044048003130000390720140800c0d000f0300040021a031640c6031402280c0c0100b140c010b08142d41400c51060300d0a010041c01d41c00f0469062a410f12115980001a142070400310305006a150b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 120561097 1250 120559847 120559849
    0xe070503312010020d030b0103050f0411010909051003021e01090306020c0a08070b040201090e0405030d020a03111801020606030c01050409022808040c0f0501020d0807030f0f0b0f0d020901060e 85
    0x142c2000120103030711112a0340c030302c18001da0100d4903400360141c1b52014082c00700060010740684d001110b2502c0032200c81c0c0001808280c4442d50702c0760000041c1008648561220104019964121765807640c0c040e00342400c03c1141000c1c4d440010340240311180c00060034284000801c0e065061001a0a1030b4002c0f85078003000342c0500030014a554403c0509a440c8081e180111880b01c04946c26070121b00c00c03580010306d01260815a0740f25a6120000c0d51034402c801070b90000940080300d82100b0959101884441000700d440203200326040c0c40000303403903456002c000a1601c800142010700a070064050311030382e40d07002001d440590f08038440140e00c481c1d040790f405020b0019002010103460b080f41c602c000050700f001c14a17005a0140100510a82c0c50b6605540164641c0c803505e40164003c154480c1e509201c2c80340760f5007118551402080d0242d90385907c03800e460a18039240103446d581d51a100c003501d4000c9107e40f100509551000d840d141d82e80004112100511503c420711510840246503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 120562347 1250 120561097 120561143
    0x91e05010618060e01090605030706052118010c0201110d02070f02060307081501020318010305070e030d0216050a080d21020708191121040e07050331 66
    0x501020810001034001160041c805080c0ca44181003110980400104030321b0214040c500954a01a00406000c1d14051040700d003a400100a8100b5541e0020400003203024035041a0043c07c690f0140c102a40c08244000d084503044002c4800b0b5a140144a8480c041e004042d41d5101001c4c443c0184c4949813410314100200c0d11400c001e5100c200002003004058100031030710302030760316502c00401e075034031110059139640302d05030300e8505120842100e00c41d15846a04505d6100d007080c0b07070030301070174085102007450070060f000c942e030241c0c010b80690402d00340200e9402000b85401c0720700c003014510b8021080d45415100fa21901085880da8207005a031274203814104d09908491b4045540301034a090140e00e41e0050001e410410584506a00e4014880d196a0b1a003000043c00381c2140c03001c102020500e0a4030070548103600c030742808001120b0010340381c250720940c2541c0700c06580740351038401040607250700807460810810403131041b00310440c21458402d4240e800076020007480100500c9401d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 120563597 1250 120562347 120562349
    0x30908040801050103050f030406090302060f281209151116030f030b0f0a0b030a0908030906150307120305090409080a02070303090609031104021e03010806100504091e050106 77
    0x42100000200041c0d00700c4154451812680034105807040c40a1540036039407a80b01c0d0344104000680500c0741071001d840c1c1705006124580d0a0404145404440c230190f001c1d0441022200010352003001420710324a030080441c40f17040d06202000c020240701a511340040030802d140a11110782c0d1030301c0381c180f1075100c402210b140060b5110349088001e80c3e0b10700101010000390800f000a42000c0d9a01d00c07030b00740780c40541c40c1408006c000341d144900b00744191030280c0004081d80001a207034004100403c00c480001c1d1700a0340550080c01b114601402d004900032181074089002303038002d035001c01c4042214007624589a0303040ca8070719551140d00d00041c000e080c07049005816400005218407400d40c0014012040b6486a229860401da440398241c2c0c41150034031000e4109441c4aa8010091409a0091040d4511b034001442044900c030700c03000740c41c1c00982103a05140e03c80720611000c069a01205030041c20304541c00d01101095030f640b24907828282e060000f20000740d440a004000087d00300b50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 120564847 1250 120563597 120563603
    0xc0f0601090b03030901020717160f1e15140405060703080912360a1205010501090203100b210405060108060c16021c06231006090b0a03020909070f030506030a210309 73
    0xc41c0303c642f075080e11001980180300e0280070b8180b01a00900d0101800c1201c0b0854400c40c503050502e602c0c00c80c0680d06008086011101c1ca5010440031803281d4079003018001143c00b960300c156040c600030324003902c2d001020003100f0040205010348c101d0022400c40c60100c40c8030041c1740411a407905180c1c40301c00b0309240300c0b80d98002c20b41400803680740610300e15800c130240107000034040380c4d0340d4448000407440183d400b000d41c00c10002082c00903100b00f00c01040561000c200d004081c40030721190f42107134030081d60308a52980040c4010417584804015480d00440c03404001032a01982d5000700c0a851a8858001c0c019840c5803483c4001c100003240911030b0680018040c025000c01c207150a40120050001c888500f15290124001d050f02c00381c0d900c2a01c1d0951950300c20681000100c40c000d40040044030f0400d502008154603546403980340500906480e02d501c100402901809030544a0040046000742d2107004e080307001c43c1000100300c100075484444940c2d01001c5803030440140c1081c170800707 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 120566097 1250 120564847 120564883
    0x15011203210212040b0f0610050f04090c020f120a050405091513020d0c091a1e0d020a0e010c1a180a050d020d02030a0518060c0f0601090b03030901020717 68
    0x1d120b150250012079072290b44503554514160f0361b1144048450301068400b5034004040040c500318040c0904001d00b0543d024060175810700d80d40d0300c0c1c41030685003d2020b00e40140c10450052807409000c02800c00c500505401160404600101c0104907003d248180c610440740c580c0451603240b411080c0b522144009880704201c61820300121b0081d43c03000ba8841c0801c0c1c500652a52040c3c410040e24050b5103820031440c1d064210b43c10109031030b0b04581c040e400c460301f020400145082951008064950790700f00b02681743c1c600b1a0000d41280d02d0a0001410b11440d8140c0500040125154825000c449050080661a0b14a007141d40a2414651000c0c074465407d40d04140180050000401e5149500300d41882e40f45800403031312406900d01c407034007040c02484112640f800f004542c107044103000d44000e00700b4201c05061850045000041c064582007000103200e00c5400e4001c0944084094000310700d06040200002e50b1303038010744101a000740400368010840701c0140b01c050788500c4103404c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 120567347 1250 120566097 120566107
    0x209150d1a030a0201020613020f03030c010504170418090512040305010204080c06120403030911090c0d050a0c1d1c05072d1403011b0203040305150112032102 70
    0x100010014202081c403000340a00d2100400d240c0016081c20041d4107a01828403510380c02d455420b802003103030b4200c0c1d112071910b01d4084140c81c204040c0c40c5c810789550011400f414541007004081c1d102110780e661383c0804000500c03025441190840e01583c8184d8001250502400c0641c280030b80d0b610301c01404200002c001080c450150054016560050305076000d60380010100001c9228601e2402242c00300e020010b00464080d80c030445ca11030160080510700d054020000e40070034000c0742c1390703240404007107030b41c10a44c403180c80f80b503901120502c4100b05004003c0b2018009020034400381c210114100c24400e6651100da210840b40c4c0301105d50411400c82c0c2c3d24101d9100e038400c0c020b2100e9050006004882212500c40c911240080d9900001c10641886000180c403480c0110907030701992160b101c8602c0003a980258951001c055014584950440c0341040c14003030802c170210b904e5030101c0014480c0c0000f030b4002485590340f5080404444582c042140d03201c80203941c40c040390601c0855 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 120568597 1250 120567347 120567367
    0xe010912051b0726010204050918070503010507050415360302030a060c0f08040b0601140702090901150501172e060210140f070e01110106172e020915 66
    0x1500741503141c112641d000c016030311314022401c03805079208495005100314081094640960704003803c11841c0401d48209548541c04203081d5007041d1082000203000081c2003010b2005522500e18580c07052510300a1a80d4058580954015042c242c03214030040e0080304080302011451400115400303010388040b010a82000c60003081035200e21404a00110034501285101d0800b884c85164042036a0081d61254001100c2c805034880300c25401100400803c000343e500c84441500ca0700d4804008603810030065211144c8110390391010f03042c04401e084030340c0c03034540c070070310741a031092504055501c108042c02c803628000114440e0303040c0a65030424003003110743d800f20300c00a400c1d4000c1018000400482d0340586100b904a4440c610a05a50003282c0e20520507600c01404140514100030300845040702e181c00c48925a00a44196403061a4507802200c280254000c50010640f091070780400d82d426240841d50070111601121b1f400200c922484c1e0700c0c102c0c0c0344003030b0354410f2481d034403495005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 120569847 1250 120568597 120568619
    0x9010c030302031003230c1002070603020304020a03080d0e0c150304120c080d020a030501140108040b18030f030f0a0b03070b0703030219030b010e0a14010302031005030105070507060e010912051b07 87
    0x1206c60046802088031788495810201070f441c03a0141554000d000c01131925008034003e4001910403039012085e0400040404c222901801d60030049003c001240c100c81281d09181031242040180207030301400c0d08454141d1410152540a0b41109609145442030041180c5c1150f214000a0070700501003611a0304801c2c3d54098000d00c00e56403410031a80e6211007654120344c2c40c0701c04842c0007650550004002072881600503400c5417814040901c01c020407038245085800148134000031403408800c211214011101d6543c00042d140c03002c005840200022a0b00c0b08980e0042002886000413240c0030180300e5030407181842880f20a4800380100301ea4000c0143c20b8041c013580c00550440032080440c41d00001220850743c0213943d0b28502850700c0010f401940000300842c83c05050000001021f03102030152902c9030903039035a102c0d603464541c917040c0115501e020b5160344503850080351100281241c110047c0b83c40700b5003403e540381c0c940440a9507100c1764000d140820360007007540028006070f40ea = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 120571097 1250 120569847 120569903
    0x609060f050f04060b030c0d030f23090a0b03040c030b04050309041811032d0102070f06061701020c121c140a0e060907060513030c030c0e06040209010c030302031003 73
    0x213002d007802188143c0c0c4c10560f6441211800319800f403001d882150000303000740050803910076242801c0000c1c1510384c6420b080602c2e84000315a20032400110707241e551400301c0c003d50190240701512411400c1c5030300d0b804001c040c01d0200400c04190758000c1424004100141c900c0381030b008005000d4441401e0320140c1501d6655011234035640e1112126401d460081003000c1068030310340c0c141540e04190002003d040940c01c00d10b00c1c1d40e5500300980d90111341500d0758201698003e00e408102c0314504108001409100a5015902d03441404000303200704000c2200006444019a525100e400351054901c0c0d030040400b4048081d85040c00c0b5644d60001d00c401c82d8860403050208010500503440f0f030584a00c2c040b2080c00642d00841c01c2070120901039006889540541c50078a60b0040d220f03a6030140ca00303c2d40e04191100d5418000070410741096080442c0d00c01c00998003035007004030110000e01039420a140003018190048000b0380b00e0484084120025502302221100110141207030880d90065 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 120572347 1250 120571097 120571103
    0x3180807050a060507050a200a0e0f0c1314010e040e06040b060a0e060d05070812070501060b070f03080c09030109061505090106122301082a0a030609060f050f04 71
    0x7490030b00140c458024002c0d01c09203a0031401609806c01c140e80d41d04018500c06921005490100701601c0d20754850800000190000e0134801c0345c43d0505010768071350880010007050944030304204440320360324503a0704102207601c1c0390044407102640070016104031301c0340c0a0903178005d4900002400c01c1d040c000f5145014a0191008108940710f6100348402e40d0a02c3c0603440030b0981c200041205400c00705102d4185600030001d480031039890705002ca04024a400d00b01c6181c00021980b903091007820f115140080001e220a45d11340125940c5903c0c02941c004400303010b01203d94000703558000b600040340c6810303030010004c1048000c04e01d4407500900c070084030b001d00c40b0f884401c00b058a0512204040c1070f03d44a45132000c0703c661040c06100500700e000310100340d03000d1640d400040304000a90290182a050000c1d12105071000e2440c0e9100d82000c500354030481403140c02840503210a00e0807800c1d81c1d0400d070003140782100c0b41401400b902d600005058251700e07250401460228003030825000e144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 120573597 1250 120572347 120572359
    0x12010c030f02090d140a06050f1905150616050607050706060b0f12070504030c0b0c100501150507030201140c1b07440303090106080304080c010c0318080705 69
    0x2041c02507100c100d0107104a019001300c401d01510b004a0b41c601880c1d08400101030894507080c04c6075071500143ea00548026056100c82e8003802540c03440c0c00410345480d01da010080080786090300241544030040344005014100c00140a40c14101c44c00350a4229908002206d10741d00b00440001c1c000c1d404070300166240c4d481c0400102e20948514101c440b0540d003001e80070305005189612040d2100090f10a00030301008101c00000100000200c000a041e481c900c2900c1d00c8020409504216a103015100e46529040060250000c3d034203c2c10140b054910b06283c0360b052514040e07006012148940d804403104000f0440558080707030060400200160000a05040020744c0f16600c3c003144c00390007a000c000100e00d003107800006040c041940007403482c0020700182c1c081541180c00d0080a507500740d410000070003086010034002c80004042c0d4000442c54203240c0341d50303d40c40d854100c01c02410007200d510070704140752203821841e004411419034040380654403c0d503955548058416140118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 120574847 1250 120573597 120573611
    0x314090904030f02011d0307020f060408060c040306050609060312092b03090f030302060712090602030a1d0d0507060e012a020118030e09060120070e060d0c0603050603030912010c03 80
    0x7211290201600051100150706201d100c0d801c02c0300c802c4010840781d07040040cd110004020380200301047c05100f070030f11281d81d01c81c15414000155000140400c1c0208040c02c2401069200028940c1c00000c0c005d08090b21000003a0018401c60300c4000070700c800020340d14041c100c0f03051209004450603c6526080c041aa07200e51004549080340700140c050b0b00180002040c85002d5580108000820800054004c1c901d9036458100d0308140c8000e0402e5948090b0b0164203c00322a1503007981400400400caa034900d6400201076114410f0b00078062511080d80300c4ca441400d400c1418000d03440d0170584000904201414a104010b400c044015824540800e01e804c03c501c00300c210040e0190380c1e03101248a01c60074030031049000713001c0b0341c10420081d00c1c200701c40d112140521104000c501c0544505840c00061050001001c1c2c403061040d0300d01901c03c400034444140040440d44c140c03e0100d40c0380d84840000303040d030090702c1d501a08801c220b0002900048194441c0e00d070f29140d501d040107c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 120576097 1250 120574847 120574871
    0x206011503060305070e13020406080c01110304080318030106030b090a0b0a050105130e070306060906030b060406060203070b040618030306081b0303090d26041d0903070314090904030f0201 83
    0x20b501c1500c005003140e040041c044c8510800c0a01059020b0040d41d0340c0c0030080001e50100701194040c1c0d0140c1d070160003940500c80c0a40e805000c0316030200848004500301b50400404584911489807c00000d101c0c0101d404403644085d0041c50056030062650032003840d2444026441c1e030f4811a04803069290940054524801c900c90181611005010300003412900d00c44c02000f23290f003d05180940c41614000400a035079070040c0e4010f0020014049103007481e6203000c111140c0054400c80c070441c10994188800396001081e03410181d0859002160740e103c03400c10000811541980c0d030003041925060f03409140d090307001002154443d030125003004402c0c510700300840d13001140701941508100801941440c00381206614180541000d071a550714202c011025035420001c4030031004c9011808204000d460050900880103510038600d42e450080f00d181c0e22441510401000d0005109140c0e00c40248401652004140a805014941841d0030301608906400c00500015820404482c441c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 120577347 1250 120576097 120576101
    0x8010e0703051615080a1d0c03010609060530030a05090109120506010510020f1614010c080301030b10030219050405010b0703022a0d06051501050c0a260a0206011503 73
    0x4803260070841410b52415000b007285d0a41c0003501c01c1091580700c3c840c81e501c074603880305407000e8001c0300c0009000c008029000c0c1402d50350305074030458040785840e038100100e0f22511059040e1508c0901025152250701030300d1200b210601c44080c00910000c501140500c0c0c02400402d002c0200742c9410703035581c0d03a413039403003144c040302c0d40f401041a000400104424201038241c026015003d00650300c1c1100d0800d0391a10b000f0724107013051054006410304104846a00d0040501d005080c81c00800301c2d100c50311a07c0f034070320040c44020045500200040e040808401c500c10245600518510041c88040f46424048809004603031060740350200000d03070740c2c8100c0d0884100ca80e15070017034000c1c060030303070800d2a0b8103268a1000460007680d0090840a42e102411460020722592001400f03050000441290116208545041c031101700b020009041d000500bc0000c0c80e03000c40030284a01040c40385909100a0401c200071134440070860340c40058000c02c645040e00c00e91205840031072500c01045007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 120578597 1250 120577347 120577349
    0xa030f0b0a050607030e03011d060a0e0d02060103120e060a05090a081c11070e01062a030905090615040b040801180206031b0f1317010e07060309020a08010e07030516 73
    0x30f4800c004225510000b402008080c942c1c0703d000303000045000034401c81c4060340410104102c180c0c0c0203002017109150540c42038242d5106220000c182e404d07512007002c0d50300d49046c080540622030011011212600c14411032583c00c1010705203d85030702c802040640381d9080064401c3c0305105540e0041103800002078440d4030181c1400c1d4460191215940c1070721003607440e2029400034002c4690200b06401304140d600e0003490035070758412202e002d0003001c3e00c00c1c41c203103c207140d856001c0311010f101103a801006032080e900c040f6942c03021034076080d0008491024113943d4041494001c100000c041c04a000548103e4140030000d2000710200c0f268008846540c21000b940080e040c40031030542111610103614103002d6060503898802c2800464020b90403451680f10300114509048c0940b40300d10038580a03900c400d000900c120000d20000b140c8848c4140162002c050b80d508100c81599103040b510001171141c0d00003005100f040070b05040e1103250501040c3d4a91040404d040c0350328103071500b180c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 120579847 1250 120578597 120578599
    0x4050d030e060105040902120106080a14011b08091507020c13020f1b1e030a030c180303030c030b12010501060f1706011d06030f070206091f200a030f0b0a05 69
    0x302c0260b01381400c2000400080c00f044c3e801c0165140c4126510300309210f82c03000340c100040242484460b62504c810340f207050303818105040c1d040c40b104540c1000728054071200c02c205410250030075910203001c149061a0400d001501d541d01c00240040c10307030007043d6411781c6002038803402c180352025205079099100760034000903030950402501d0503041c030305207051000c01500c40076540b207810f004807d1549180501206140d50300001120b110766900b5200e040301802d16030409000d0006500c2800031318805c188000b07400d05848841c079006152082c1d00400c0440740003404c0170200580c2190b45ea000b003109004000200311025111034a0074080c94003243c90031054070b9010310540c2c4003030044071006482030345001030101208c04541072781e41d03880180d44101d4040f0b10a290b2441c00f400c00910b41000984100707141c1e00300c02c3c003d2500002400d501e03282d40400c0800440c1f00382040f40c0b45c461401040940840201c804985200c1307455054114000a0448100c14400c0003075400802004a103140b08079 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 120581097 1250 120579847 120579853
    0x19060510060504031e0c0e0603060a060501021509011104060c0b010801090c090b0303040f270516110c03030a18050f09150d050706050c010e010204060c150603051504050d030e 77
    0x20070014481102002d1850004943c540b808822036580014035a0240c000d1691f100d81d07442044524102000369a5100c8806102402407618140020f9107881003ca0312520103c00840026403005003504480040d2a8039915030b0b40d10390351100010200f021103c400c0b0740c8054280c00008403010b05000c2c01e141143c02214482c42949003808140041400504c90354040c0824440000c40000381d4174080010105050000b2507803801ca807458401c0910322121004103031a26003030029800a91041201e81d81c401d08040001843c0740100502d007101c05d04d00c0310342c11310000505d815055485002c840340f643e80841c507030114540350000c02111070040580250020b1a0303200103940c16140c05600c51000a024140303030500340312521030700e0502c11160401c1011500020325070107070100034450200e190242000850906003810b000030440b0b0301000c0080e100254151002d02d84035216401a0011503001007212002450368002881c2e44c2c0c0c0845060f540e5004a60000810a0003402200540c420300c1001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 120582347 1250 120581097 120581099
    0x80604051207050c0a09020403060b0102072303010608060403021c170a0c0c0203120316090b0a03020c1507091403060f0c030a090f0b0402090c040b09040b060c19060510060504 77
    0x981d0209410500c01a10700f4420001c4091103a200c0088090240c03105507005030f603503030031401c142040c1c2d0601001d5504540c414042044411b41110100202c41c000759610101925031100081c0540b007280c119120038022101480b0170141c000900f41050700713010f403c0d41c40f00f1580f050240c410000c580000150400817800040081010380d10000e003c00c0d80b410b10007244065600428070300030703442402e803080e01000000e1100c0b401c40d40042028091aa01c0c119051a06150074076441c3c0c06006400d009041c2c0119401900e42001c2c40410030442e415811b4030300e1450046401410381c4103520071522f1807903211245480078140800c00c00d03c64050400010f034140c4560700382d10580e6100901c00152195504e07215000110810250104540036000710101ca0803d401049415a0042c1c903200d0750700002c100c1006140da165042c0d038041c0030b00300c44c00a408030040c0c020403003504c19010b0380d60080c09040e00002c60244861051400c0ca8002c010810181d03a900c000d0f50035203003881c00380d5000f00d901800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 120583597 1250 120582347 120582373
    0x606050406080402010f030612060c02060c0c030904050406020403080f0403170c0303160e041a040e0d0f0309030c0212010903110c0d0206090406030501020301171011120406090b0901090c08060405 86
    0x2803e80c03160051800048d82969211162452461414200c40042d120117460402541c100080c503000152030348043d152907413424985aa910418565502968803a8005010701c07c10794142c030002c1d07030000044c590b00c40b2102206071165001d03020494019040000190520019405951004010388020761440d100d06280d0910000e516038000d00708810240b542000d92280e002c0c5100c01c40c040005040502e10703682c03c00c0156180c43c1c444032150703442101c90450490f4803000140e00e41c03c5908000a070f500c0181001c48044005001c01794000601c0c0d501e64400720310541c0145c074040c0c006d9942c41c8940c4022083e0036292000c0c03051483e8015001d64011000d4a00b41c001408921001400050321956995645003a40c1090b886210908100146e49007003603014003102011148030707081007041003074010032417840340102c180d01140403c0d008005800c00001350700484810707412401c224031b2031070103643d154081c01001e0811a1445400d00740011681c0300091103600455120b806088161000030f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 120584847 1250 120583597 120583607
    0x10f090f110307082a03030c06011502160b03010305011401180b1c0c0806070c030f050a03020c1b18010b070303150f0b030402150a0f050d0b130f060605040608040201 73
    0x40740540d05000362880001c1c224400c0040c14295280c68450038001490b080d52040315048507011a8060780041006042c0c600c80814203a040d100c410010481c40040240c0480c078091402e0240d040c0304c010b40e1808240c0045074006181220b01c928002d1061140c0c1d000c204860210a01c07400e401580d145000c01c0c100025034100e0f100200c00604000c9810040e4420380c5019002504207032907a081040c01400210014001a40d00c00e0351800e103114580400d0340c0007460707100104110010040c0c0898081c00c0b040c030a0301250b0020a64808035a41900012040c034440d640118075688030740e005a00d8950b001c840e00051504071180c0181081c01c01801d5102074029001c003803d0041901c070324810208802c1d0190b1712242c05040c05044c03803030b00d034034051050028410b140d0b8502080c0e003109103c9500030b5540403d40780d0030402d483c03030305c80d49035886c00b03c00101404280340e1340365104409402c41c0d8242070403035001140d0700311540018031009a491809075002d10440c01440c00003190840018050b502072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 120586097 1250 120584847 120584873
    0x190209010e1203091905010e010512070807090b0a2c03210408150105041406100f020709020a05070c06090602152a0703020610120f0809030304030c08010f090f 70
    0x3009070f80c502040c403030003c0d038602c80d00b1032000c01e4944804000d00443d6882001c000f8106800e080c95458104482555280c0c640c0080c5458200044040010080ca100c0c0007600c00034580041c4194a41d0541c2a0242c0012210a11780c40840d9900c204408211140018020710300b0019020381a0066080c00300c090082e44080324a84a480070800002c03004800c000c0c011804030401001c0602d5414041004142d4101c0e02488030b0b841c0c111428466a41c0d1256080300b078011480c1440380b0744490681090341030407110352080c0c8c1200e2000c59542d15007078000000380350761407290418002036030310703602c2c1501d07848040d010344d00c0140c0c4010b9110145c4403698850740d40290101d0401042c41c1d0b121049007058801040c2c00c6c9581101c0486d5110405404000c0c1c990425000b1100400e4030742001c042288100300000c000c2e05c0b402015a40d03c003400805006c50301036800c05004c1d0b1342e456440c1e0810000c650f181d031084000c603610b81040066039206604c1188404ca50041f18403620180d80d4031540004044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 120587347 1250 120586097 120586129
    0xe0c07080c030d0f050c1611040f09020f0d0b0606030c0c0706030207021c020f01052d0702210606131e06050406090203130f0f050d0305190209010e 65
    0x200002808100c04801030150356190600840d80c50318142d5588041e02c102880d0101442c0c18402409000c2035138905445900e0401410b86c07500340c1407414122540c001044040303810a240803940c48140350950000e640780c6000740d80340c1001c05d4400c0b00b400240b441c0100003504920164010035000d01e0550010758000b07005291184c103180150911604084003980800046030740041c0940840c10140300300c000c40c0c901d1050000c109407664001c291551702c109510303810048001071510704800391072022502c108120310070300d081400705148000c1076032000300c0a07841000450884404071a0269411618a00d000c000d8040d40c0ca0b40d4091029200a101c00b00a950b500c80004090361201e40c12000b008055003071011813400e02d4542032200312800e035000300c01030a0041041000804112180450300359201c440c0345020302090420030000c215500004020b030249601c040d240710340c90f17002180a5804035001001c0b0b0024101c2003c02c034403803c81a18049030b003003004104185840d20741115031346c01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 120588597 1250 120587347 120587371
    0x30303091905030d0204090c090b070f080f1b01020c011d07060c080c011404030f0302070b040209091501120506060a0305210c07030f0b0109050103080d05040206041205010506180606040e 82
    0x80030300e541000380c4c0c00540001c406a5510707002d03041910340c450500000ac080420301d01e07203001a036490701102d01641da40090500d2200041c115080c010a0301107640c03000c41d6202c0800429118140c00d4040d601c0741a60013500d600b00b00c0440c2011860f000350b280001404401858098500241030301d1100c40c4080c10744410b1414000c0384000d200031f00a44004600b020480405841c1c070380f8020300784401c002c2640b010117105120f810002017003510807540094045030344800302c0c1d4820303000030724002140360440000c0c07071608000224107180d02440c14816204000350b45040c2d8034441440243c50b494071019091341e00808220f600d0300c000b40340400350308801090042c502003462650502d002c04641c01102c030442c0690403007041c89120040c0c1805000d81300801c5c00b04d545140c4466546010740c008941704aca0f9105e0104d400c558be06c100711401400b51209000c40d031301041c1002c1c0c0c001c2c00111492400f40081074503c00741341c05040111440340c40d00801d0f603400c15040c403a009500c900700901c1600840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 120589847 1250 120588597 120588607
    0xa06180c0801090c06020d09050f040f0c0807090801020f0405190302100507020103050a0c0203030c0f04030c170c0d08030a18051006180510090e03090901090c02070503030309190503 80
    0x91850000c26000c0c1c0101000851000300926041c40010f800f507000500715007000e090390100c1c907400f254280c1224802c44003144c0ba130030744038009001000a60b40d528882440c01c07409219042d00000b030b0512034aa1900e8007c1c0107a900c0809500740d10461144440f1648100030a001c285098041c80c1c007206080513500307006c140c6a601142d54030360640b8900c8082600803441340e0841d82d16005142d4031460001c018404804151400b030342d81c0c080500040387d21400450303484540e446130307003d680045810200010a40c2e940702034550200da040400400140140704404c003890411050004049a111501d549107070b5581c950180201070401c080c0e10341a0040d0b1203480415410032080c2100200c900300012018035101c8202880c04208491400c003500303103c10800391503502a900002c07155800000b141c503010000d2800e05500c141c0031050740c4441c011001003684003480d4084001d804854003103c5189440740c1c100342d1340e80021162401ca550140803117100c008038101201071414481c0084034141303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 120591097 1250 120589847 120589853
    0xc0916050418142a070b0105011103130e0a0e0c0306070e04060906080c01030507020604030e130605060d06060f051305120a1a040b06060304030c03030b030705040213260a0618 77
    0xe0b40241c07941581002d070502c035540c4035000e581c00c4460084903861850300e0409241d80e01c0d50146e00500c609414014a43c0207590503a10600c215141003400051218840391501d454201d041e000380d0b011001c180c80c109400344002030000700000c020b10300900800d1156a020401c882d514800b02c003843e0025210080051035000602540c006401c119004e4901c11300380b200014101c65008081c801123600c408103101c04139030000101654108180c0703035007078144040071085000d4501540000e40003100080c41302480c80160748480107651140e40e400c0080c03480584c044900e030080b074404880340c414030001004907240124900300302c040071a080d108000a0398403050740e41c003229058071400102c041c0410040150145007264460021600c803030035410700303840083c190003000d00f006090540d00c0d400c0680b143c2d420807104005084c000c009540d2014145a0114500f100c2d2140c1111034503031b100200400d061210424035150540c60040c44042e4490301c0e02c8002c1c00c2c0462000070310070841043e00000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 120592347 1250 120591097 120591131
    0x4150906150303020c04050c090108010603020a1716090b031618050301090b0910020a120222180b04021603051309060e09060601020c01080105040b03030d0504050c0916050418 77
    0x2c5002c0d0f0058400c09075841c0512042d628000e200d040b841c0c1d402c00c04254039a800908160564000d8a030050311800c0100e0140c420580000000c101a5200410029031034090403001031210305030b6a034004810741c0d41c043c211302030209072401e09000b0300b6241104801e41c8242044181062001001c6d084566104042401c489a04030281c4600291004004c0640d06c104010901442c0150045142c40300c1004c00034400340e41480100341554000484c030521100c51000350000c5082c4041d140030b10380d40c98000e0098548510600c04020307040c01e40d4241c0500d0f0030310130369241f070a1450b514041c0c04095a400c40b0385610046010640c16041328010030104000e100c0d01e0083c01d0009034030300e03150401260781460b1403801041e0034119884900010070603680308540504480090f640454008800300c0002d00318054500700035442482c241c200001e019000450a04c440025915414586c940003042c4041001c1600800c020902c201b00800605031a0b03100152642c0260900042e044401c00c07119803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 120593597 1250 120592347 120592349
    0x20f070509150d060614100503060a030201050922020a030b0d110907090b0304120306050f0f0f040b03030f04050f01022a040207050d090303082a1e04090e060109050415090615 77
    0x3103288004000703032484d0511910110440d1204d0408c64214900440090085150381c04020304021004c5618840f580b21310313586003020500c0031090003c6965040ca603c000b5005a624200000e080520b000c40318100b02000c501019005090503d4050300345003403000588001d4410301c01c02242601c00241060740001441c000e500c10048490218010900242a2401038019600c5900700c1c00122007103a80e821103d2a14460030345562410400340000500100511041d040c1c0500001801c0d00c100c20a400040040c4e4400310346c0000451903000c0120f82d180500185130360201e200e54801d5884400740c1a4042c0d403458024000341c50030440340e49281c2051001c011000125084075410720416407c01a440d03444081401c0400f80321001200340302c5582d10401c0791281c81e10000030140da07213414801400a5080384142203d070703110f546000102c020a0b0b802000c1d601e902864001140c2084103010b424041c0303401036450712040025943e2500100768011003200c106d070b9110511107007400028800c0c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 120594847 1250 120593597 120593609
    0x206070204050c1605240f07110c0a060513060e0303070602070c0324110a05040509090a0f150506061305101707020d02120906120c0d1103010303020f070509150d0606 73
    0x800c1300560351a280e20130386d01c5a41c080c0c9850780d40b0200705110031640c020541c1305072181340c17605508a885c00c4090622496415882d08001c01c800c0200302181c01c03100801554111842814500741d446031f00b1a402e0780303501410755240e0410001c07030012444907005041024010821001c2240d40d980c1c0da01c2044100c0303003100c170119a200a4203411100c461113080e180031182207000d450141a98002852403085000d618864481070002c9044032404100e10a4a15405001003080d00101c0c00d26909804000c4d02840f902410304002900c64240a02541c454a0381d12848014031780c107001c05c0002511a80701c040040148036803801242034100018540688543e801030041d040742510300900741618070488021105081040d4581d41c0ca4040c00c0b10541c0c98001081421070320b50414090b01072192034002c00d031060511042d428440d44e0b0070300440c100c902caa02220f000d1411000c0341515902c0500c200d0b6800040d801c00030f095a100141900b071985002003402c602c1941c13942d90b00b4200d4040780c000b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 120596097 1250 120594847 120594853
    0xc090306070807030c020c01050406030f0f110405030d0e210a06110a020115030c0920070813050d0b0109020c0f06040c140102030309060106142506060f030206070204050c1605 77
    0x8003d006815100b240e040c00c2039403010741400c01030032001822521440c869942096551750350005440004c1d440204800c101123014030a081581e11542540e030424012540f090007111052081240124960b0014034030103410520300c0c0590f843c00c101c510008034039002043c01a103510718002601849221220220030101c0ca445071000c0078000e084405c42c504c68500019980f50500100d40102d045e401100c251803400b040b041940007541060710480c0070740004070311010659800300a121406883c08a4990000102c202d40e40d0041000300d490103071300070b041c0201410051010307171550b40003010021a2031782222024502c682096151075821034080c0d503c0b40000c10103102400e130340041c0100c0404244019411410120202030f2a00d206114802c00e0101104400c11581c43c40d000784e410440c520a140b10041c210f060520300003000c4294119011440c0540c082402c0149012910649801a00c1d0b2402c06c4a913a00f404014070b0040e2070701c08588800d00503041080000300840000503c90000703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 120597347 1250 120596097 120596101
    0xa020715141612030218060703030e061003030f0c020607020f0301020f0c01020c01050109090510092103050a06060201110f0306150307050a080907061d0111030a0306030212030a170c0903060708 85
    0x1040f03d0310fa48803021402014010800d20320301680c655806000c200c03080310b140d613603401c003840d080c1c0003803100e007865046900900081040281d0700c003066004483c026160700301c007890020340031501d001182c10001c3d480038044c05450b0242c10300a00d600480072005e00010702d008070111495485800c040303036104040e0340001d04049050303420301032180101074004081c882c008240d40c035203440b6030000b01071341da4040e5516000000e101c0c40c0c491041d030034260081108081310b65490014003502c411608285414100440040e07554414442c2415140110004a0401d5019074000f00164000b500c159808212945030302441c003400d0000b180a20091f80300e00ea91080140f001500b040f80081250070150801c1004003c8142c210825458080500c000c1d00c80e80ca20360300040e200e00c2c8414000d00b680b03100218041c00043c3d01940940166802210441184040c0075880d070b0b901e214040c03100001401021100c1d0104c055007290f0b54200b1a540c00840c1482e4819000c02d1408d103040b1602000502c041b01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 120598597 1250 120597347 120597353
    0x501030f1a10031806020315010f0f051308010e060f0c04080703111306091e050c0f030907150309060506030607021507030f11040501020d050a0207151416 68
    0x4910180240400300521801c40d0341032007440c0030494124018081c4200b5080145400d101ea03010184114191910b904010410700303211009400440b1490031102050021445c1c0703600072007404003410765603558038010034440d040441c7d40f60024648455030035900880820203100070f000380d4100f040743c00b00424003407600c0d6600003645040603001a610a6041009220021011843c1c4040e01e40003400e501658805c00c0c0410752550004602c0000285400c401040c0340c1e040f0780003400c218402c003541c800d009070913900d00780031140103850740700980d0300030401c950a03000f0060185900a00d88030a0b152015640c1d4106904204080c00f850002941c440950080110911900c1e4000500f50010304d450301d00b401c0f01958400403e900e01088030701007000240154072070303003007a000300b84480e40610440060b1610429240c00c0b074080e0302c0c0075024280701031100510503070a803044e1844580c000e104030f503e40300c0d41c0400d0300b4103506a54200300050807149100e03240f4030000d0003881146c001151a032030581c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 120599847 1250 120598597 120598601
    0x1209061305070b07020a09050a0e0c0402180409080f0403050102030603121c09140304090e010f051006080901020f0a020d1206081515120303040302010f0b0901091a040e0106050103 79
    0x80000e0415414000000c0128400007003803000d0341c1000c20510758500c05800003825660195000300802400c100c00c004140800381c09c51200c5918400456246488410801c0142d0096109180001c80201c080003917510f4581c00c151710040c000c03070780d403403400701d01011a000ea035009030030030358060390000280090b500301089642e044040c031104490400109141810380f090324002d484800c4c580780e241c42d00500208a40040a80c100300301160341d125559101600607001d01e100400382d03540381800d44d0041e419a8010b1900c690b144805903e202401d0080039a00c141015192111030340d828401c81e030404032a03100400000c0103503001007481035000b2100411117000c02c0300005400e030504070100013070013001501424104510ba15900180d513070004440513000442441a0300114068121040c8040800210300690195000b400125880540c10042c1d490134103100350440160f0f0010004400c440d80129542883c80d0755103141e610760b0000180558400d4606004580d6441c1c008028568140c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 120601097 1250 120599847 120599851
    0x30c070509010e0a020c011b17150d021c0b24010903050d0c0f080d0203100801020702090402040b061902060601020706021203010b07080705060c190203091003020a090506120906 78
    0x225141e410340d6040104990040102406503002d5a0f00841c40c0c4440d4202900042c8a4820071811201c0d000e800300b000400880d07041000843c18005107000c621064400d44400c524a403001d00f81d0b0854864642c2803110081e1091010070076404209089000224840080790095110f42240c0c80040b0b9001e45a03070040300090204d0781405180101080080d0010400b03005090307050800c60300d50009402c0410100d500d00704c0082100d88006600d0521109a42c007071802a03081c0c0d020b8140300703522800c5803400c13031160074406980024544001801807174190804002c3c0d51002c0d044504203090b040c15070400030382201c0d00801581007a000c101d9a075904116030002406c40b031001300504034004003044030511044c0034a40451100160b66020b00c81741204031000d03947c3c800c0865403e40b4100d01051210b4002d10326020118081c070002d00f0400c0e1001058072112040140a62103051290205400a600c480d8800341403007070a210000701795480d60003801402100e8203c8007590300d82494018203090700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 120602347 1250 120601097 120601099
    0x1502070204050601020d0207061103120a0e0d0c0305071514040609030e040b09040210090315060305011401034205060a0812030f07021c050a020c0103050606090913080c030c0705 78
    0x31b2404c003417003550004904046034018100500c0d07220241b84102e00b1445103047c030700645200c100500c0340710304580c1d00101c450380c20f01c0c0030384144c05000d040c2200c030701c1c0e03140308081c0000340248418030115840301c0b1030341c04004142000080d40c00104d010301816032021102034544035074aa2a40080c540c0145030b280020504540800c274403518000007400d042c40190010b0701918140da1071a501c0b40c0548811000b03550001820070411108150001c00b8010a000403992035007418025584242ca0f0000141a40d501000000307a40b00d1103042c4000c4404002d130001c6c0040745614641084604409040781d800840f2100440d841c44e00005200000d1013951055905a000e40e690341a000c0161013a240c001c4c414030724603c040c2d204c07081e08a24140791200c00302c0c2146c4540b9080e00986030014018401d81c00d00c0d03000c2c0c0341d2000401d030055003250401c9500d5508840300304070704001450040f01a50384080c0c00380300000b1605958489441075044100d0025603a880040d010400040800c184001400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 120603597 1250 120602347 120602353
    0x60d15151710050a1703071e03090501021209040504020f040f0f110408031c020c060f01091a010e21070b030f09070b0d09050a12120606020a0f020904050a150207020405060102 77
    0x302d00f00100d131071840d1911400c180d040c401c0c501003041900030320480e14959003000c10500241d905618015201c0c8900d8130841c0442c2d0b080c400054254004070340030340150324020000d0705201c1d002c0180400b401e0000c00c200c0c0e0243d45c184101d4040d685612a90060603010311000500c41c0018030070200300c900c4440c010450310f0b07080c0010400f540001040341d2a034801052490100c603200705403e0081d02a805003102d0328040c130790400201403c0c800016049440c00700d024003064140003078000700403c07610710090000702805403a43c803506189003110301c000080d40e00e2403000e110b01111141040d0a50300403440021001041c0b00a40000b995901c1d0400c2c50303036010303050b92442e100001c201c034442c161607110941c3d1501c0512041c0f00042c0f200d414000d40042c000124080300798401800f8250032140c0a01c81c500e81100803a1304c1d0702c00900a17401d582d000c100008801041d030200b2100380c0d0001c0c012120b920031100245d0000c0e03040702d010600c8010b0081c000d41c07188160b03c10001520401007090341194 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 120604847 1250 120603597 120603599
    0x706210e07051504090f02030a1d070b0c03040b03090303100b03190b120102070f0308150102070b0f0c030d09030801061407121101150512030702060d15151710 70
    0xc034041050002c0b54030454020b9100180e0301d040602501496101c00b842d80c0c68659075598424007a0015881000d240d0810080c9564440642502059030846005503601c440c0f03003403140002250041015140000403203040c699a906c41990f0359004555800c810741001c410b10400b600e415807590080d0410050060851604403025000300d0212844a9900e0341c4801030640c1c40e0b246d011001260b118403000030f640d103086a080c0348445490459044001903900e8000803201d202c42c0e940d04050080583c040d0070401d02d04503d82649070018031078412482d00412030043ea40d841003009000c900240140032031040c851342005003400c2e105a1212050012140f044110302003080c0803255540d92002d503903141d208040c18115a001c240d6092a03400e07620f04001d40700c2100901d0b0144c41111001c035040b424800b01101c82c03644030700030303040b00070740002c402d000e0300503651015001081390052104001d00400e60b1781c051085680d0f41c8060607808511400d501402141540210f19400501a61128482 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 120606097 1250 120604847 120604871
    0x2030702101e06090c0809070f03060905010f05070206040302070b04051315361a240d0e010f09031b0203031e03010509070206090a02090402030f070621 67
    0x9032801c101005552580d030002c42e0b0401003148849400100740720020000e031a25040440c0082250382074200101d000e01001030281c0000207924801c1d0740b110308445c80c5175451070751f81d6809081885012900ca54890140c0880c2d0b0942e0300c1014420b05140e4028034503030819043c040d00700000b075000401940b0701004103200c2c0381c480c18000400d0000042c4000b60f410711403004402420860781007202d031444140701c2c400064000a100b002c400c041c00b901c107494103901070340d080700b140c00841c00d00b0101001038010007d00d160119600d40100e0080054007610900c41d00d19006550181000f9020a0750b0341d5846403c1000900c66220030507083c801c100304c1c4094685001c0c00044044144458034110440c0c58070840d1400c0c000c1d00e4241c01101c1c810304030711107080c5d204481600709004140c003c1041900061590b4400190107010f590340902600c5880116000e000800c900103000743c0c2c1510901110035030900c0200320f90303030041510750303146100154a00030b0030301404407101c2040f04ca903050001d08120 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 120607347 1250 120606097 120606103
    0x10f090f051c0605070908010e030c07030605090a0503070b100501020105061f020c2d06031308030a0b060a0201050403020115032003120c0102072f130209030a0606081002030702 78
    0x90715011216a41ca003080c480002c010129040c000802150802c000c1c01720380c42d0401d01c444240d60121000707128484111925070b607070340a04060041158071600c0c081000c54441d900003500901c04200707030740703407200c180d281c80d0f19540c0700340c8041711240404c2040050910424038981c3c09070800744000e01003402c00c040040c284002050300170150001c1c0590101c40103000f000500010600600710b90000c01051461020101c0c000c4411300c40500e840c0c2843c00d00f46001310440f8410346004100c50088200d50310744030003903080145100c25280d80c1e2022200c00d6995100548420066640013052501e4940360090956515080c5006c03a91040d400900c0012920049081e00503607500b4031201c00c0c158a0b00081c0b40650706c00b1420501000058401001030040d0000c110603030245414803450f51101c1070044803125042e1101682e4082080d0115039460807034501c05910101c4480542404980e10019080c0312000000300ca445603103010400200360144051100100050003c42c254500f800740179403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 120608597 1250 120607347 120607349
    0x4050c04033306080f060a020c060103110114040e06030d08150402180a030c06020d0504030201050a0309050c150a031a1014070b0a050a050a0603020a061407060f0605010f090f 77
    0x61006070101c078030a40c1166155080c07154541e9510188502e9a451807a585c9810342c0500800b12809a5400552501054000c40701c1c0300030418000e22890f8039540f201c404600780c8650705410030a05200b0001019a02c0c0040c0c0040d001002c0011508d042600c00c240c81c00000ca6040d8091000100c01c010410380b02440f14190002c041d1405030f07455a100c84180c002c0707810031b0155135000c00c0714040030051000040601068509503002c80701c460041400a07a091b004500c002400200c00f0000c1008007440b035040810742e18071600442e9070f1174548800082710b81c83c0001d000d50108201151400c1040d502d4090090390000f20342031044559401000306000010220040c014017642c02e0038403142e01c20000c202c032a1113411000011b0142811000755000c0d100c2610b50600c1c803400c1c0b1010801d9031215101c3d00003240e41c0104020744080ca80103098a0313a651348640254600010f00c23813000880e01078012902000e03000d41000907241d0800001506901780416840200800341e103050100d00c02241c1840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 120609847 1250 120608597 120608633
    0x70e190b0616140f01020a090e04080702210a080a02240406020903100f0b0103061403060115050d0603050d0206010f030812060d0f14120c0c2e050904050c0403 70
    0x100102c0030b082c0080d684001988004081c0301d203c40c08040c800040d805030007613117401e5840954403541c0c0d00c4d00d00c40036001a20058480c0104109010051404480803041c1c2558250610708204003114002e050441c1640d0903900b5503000144140c42070341c184200042040d182048111401201101402e02d10006100400d0305900049004442d0b500304002c007441070341c265040c46490710408032078010b0308d04a100507010a007803120101d84004d035148485403031070000d001482c481e803a109840801c944500c030000144802001165102d0805000c1c0002031070107600281440ea001c031400a02c1c1c41c0050784195480710007240181f0020b455901114000c0d50341c501203040c15210030001401d00030035442e0080200c0c02d000361140800c01803208001c4c083d518201a075001400c10901c00310301e4455000700025a1300700032003c65042c0340240c4038100c03860382c2c860003111200e640006000d41091a0b011140420804901b107075151801d40a865809451001da450801d455507032441400c2c80801110307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 120611097 1250 120609847 120609877
    0x703020f060f030a02070210050403050c04051008160f050402033912070f0305130308090a0b0103200415030f03031103070c050f070302010c0b0a0e070e190b06 70
    0x10640d55820042da0411410804420b640b42080d102140080d40300b03107001ca0044040340901c8074180e01404c03c0c5c400702d0340c012014010404040040000030540140640210322600601281c82601040203600079101d1500b0006d015092800840c00c087e41544910307c11401001003214019158018001080c080440070724100e0880b2000d15800c014218120b00c124004166910729005940420740100c6850302c94203145c10480d041141030b0f42085503040784103461211395000081c410000554003040900548804507102e41e03035a80500320a030300a64414880da04200030030006030059920f011701c1150208a91044d1040c81492109107101c00341030080c940c03503440141402a040000084040d00c05140e0b2480d002c40c020704004a0600c3c250340d80d10410021a028080020340030b010350790161103040b032000203640c0d480e02d01007000307144000d110b45500d2003c21141781000b104000e051164951162407920380a080d5100c10310000000c0c0e441c2c103010040f14192501d0040b50071003148003101d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 120612347 1250 120611097 120611119
    0x11040c02120a0e0907170a11031315050a0e15090714010c14030301080709060506030a020f070b070c0209070203030411090a02090a090603030e090c04060507060605190e0a0c02070302 80
    0x81511000080c00f109078201c43c00700c080250996101c5208121541054241000741c1c882c0c80c1110200c421030110042d031040b0400100c2c3c80c000e40d100307443c040c5d43c0c41803001c802d07039003007800049054502c1921400300c445c1c0c803103000c5140d0800902c51000c204c0341165021398245000e9002a035600341c54400c507403403141d003a1340c0740c04164411852503c0d201e402c40300181c03035035010408040d640d5000344161440c07030044034400308028850380580c108413400109080c2c103548844041c40c00030b5010564905020504001680c00282810251441000180c454140401c0140180320789440700070000011900108100300004254124110180b182038980b00301913500c001c03002d4002d02c1400718030742e07100220820014a10f009074001800b5a4404d40d1000140d80b0140144071b000380c5c040c6d85103084205c052005110b00f611680107800058050707680460100d41da0400b00d88021104a2841402c1c0c3c0c60220911040072071084041d009240450f0070480d4407205032000f51501002d0100038490b07080701d45 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 120613597 1250 120612347 120612367
    0x90f060f0a021b06090d120204060c0b070306051804030f080f070e03030c0a0507090b040209011b0c05060a02101d0a0b0c0403050706110c0306040803070e150a03020711040c0212 78
    0x98191a8918aa0448031303075061260b84a95207591105004000038071604102d000c0302414000d03a0300300c1d8130540300c012303100c5044e6031a60705170f81340181045c040694840002846540d00c0b8019294500140c0c07103003415003064140148221100c5d02d010041c4011003047c0030030b080c60306c40a1644213116103041040c0c603031240002030640c0308a1041409512916210005102002c1100d40032a400d041040149078611010b01c8140d019080c00103012607104120200384283c1d10001c0d0304403a206c0c0300b039000516148d40000300c054110800f402d006900c01400d0207200c0c5c4c09446403206440000c401c1020311981d00c200c3c1039a6080c2407000405000c10308008ca40130701d85141c1524041d55003c8141da41e25a240c2c20001e0188201940c1a2980d04ca801002c900504020032070502583c2c101081c1e0346140d6401e20309407441c0140184440c0c0002400c102025805d08130030107850698000d50b405640c600503403d03c005a0581c03080d05500c210301c0c0244c0400640e40004803a1500d641010703065440c1c00c581d42d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 120614847 1250 120613597 120613627
    0x130201120c0c02060f04080714090f0c07050318090a061503090302030702090a09030810080316020d052509051312090e04030e0907020c0a1a040914090f060f0a02 71
    0x82c1c00250042004074204101768002c0c1d0281080d500240121160f4035a03451031250940011090183c02914807030220740c03c1401100410341c070401c1084c40700c0c60f180740e5689180c41d50b80000002e000301112400d0f01c5110707243c214882e0b43c01a404c034005000940c04c02c02c1000644080f84444400c0c1552141103c00300740c000d100351503415800809140316403406a4a40000e0a0740300e20460000d40c000002801003a115105002611106001103007000e40501c1c2401c15420526403c2e0380c485401400440010030030405804084c000d02d10f0300c52002100000091154481e03040146002d050408101403000e404024004440d040f246c5174082e90032010b02940c040e02190030011065440e6070410080c0741d00710300444403008095509003461f6840710304c102d841b440001041640900e00795802c02c80083c0910b0001c0c2d54000c2021400c1c5040e90b2002c000f030880c0e060a02c8881060030b0b0204008a4ae02c09104078648a02100c01070415490500049000d0032402800640341a50204007400c500140f4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 120616097 1250 120614847 120614867
    0x3050604060e150a0b030f040609020604050402030a0c030e030a020c0f01030b1305060118060c170c010e07080d020a0305030c0c010204090203090f0106090c02032704060b070b130201120c 82
    0xa03102e0120314103001c0680c1d81200082204140521031300d00c000168641913004070ba114861524071001035407501c2da00d040150440c110141e9000700c0610010485648500c02140104500301000a0800c1d80b100c0180584800317001440b0b0070342050007141840f58002ca240c031540b10b0b080f202994071700700d10801039000b0828085031541010b031000e00100191450362025010304402d032114100440e41102d0918202d18901610300040d00740c0c90b1400010300c004c05104030440005840b2230a00700f0f107400c0f01f801c41304c01c045441050f51264208000900b41440840304000d228800784c6060362072070b20090024400a45035103400c00c0005880b80a0090030b5040c0c0300a00109081550340c0d00b0810200b594440460a8084095203082c0e40082c1c0781c004c501c50901105010f0300514140a0100c044041c13000c0e07103112580c40782c004c684400980343c5d590b219201c0503107680320105458000b582086918140014030784804c0e4982c0001c142c01507a041031580726510103000001c25220040e581c00c407000200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 120617347 1250 120616097 120616109
    0x80118052a04030b150d020418080c0703021201020a090b0304030908010c090504140906010510090302030d170f070903171e04090f020f0f1b1203040b010e070f0305060406 75
    0x1c404011814a50740000500459024862214540e00c82110b40b074158100345403003036800b16800c01c0003c01801c06401c0304501110b402d80f20001c84140c0d864198490340018a00c00071074000c01414000c500e030166064111210003c003c60410700c200e10080c014079911300901e6048500400014200340c807502003200038009810081c003003000300140c040c2c0240851f001e900d1007070f8189880d00414a0a4980941c4030304c3c80d20b0001c01da56440e01c800d01c610403404003000000c20160207008005600c0400002900e0400d030342da8032210300381d000d41740301d001075014042041c0343c41e448040c000341c81d0380402180c05680d00445400038480500d8050103d522810482042186512240202041c03a60740507004541001c0700038420000b40341c46003400c0f0311420039105241a02400401f61034005070b805000c0545000c1c05403141c1500d000c065610301020750000104041c800420441080000e00545c4e0042ca40418010070301d041031000034140310b144a1100c010195648000741150b5201d030000d100800c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 120618597 1250 120617347 120617401
    0x60a0813080c061005030a0b040201030209010c060510080c0303040303020c0114040905100810020705070905060a0e01151e021908040f09060e0609060a03080c10050c07060b0108011805 81
    0x2060100c2e103a00086030b0100400e036001310005118100442d911247c2644030705d2009143d40c440d0700544c025004414260304002c0003903503400000300c0910076140103120f41c40f92024040d10b07120b08c551030a904044102e0082e0020b21082001980028100c0d0b50b201007420700d1748107002400c0500006000d654000043d00e41004140540000307407004e41403e642140040e612508003240f0b03400280d00ca00d000c024907981c03000d0030800c90090300798481034010304014608016540e42d00490041c4840a1308400792003500c02c500b02c4506a000440c45560a140c00c05100e503940f100710000c0d4980c40d01c180c2124500c407916040c4801c200d0490b04840c09071000d001c601d0401da07281c4104000402050045076042103a51011680c41c3c5804601c2a100d42c100500e14a421415580c840425800034001c0d011140b041c80c4e42c00d01040b615006191180710861203d945481882c1429802d40700e004c181141484100c00052003410603400c02c0e403407049084100810700d61038030380303901c6000c0020030001a5014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 120619847 1250 120618597 120618607
    0x2090403031125030801150909051e0403180905010b0412030905030610051914130608010507030e0c010e0102060624040e1e01050f040911090f0601090801020702060a081308 76
    0x3d102c032005030142c001d584407800d0340e0b2038a090010b40700b00d040b00b22000c00e42607a0108015000784d0850ba5205e507602e140ea40c01140e9098503000450340030b4a04901145607020008922241441c10100034008001c00b4821540362100d4032805101c4c500401d081074900318412010f00d0f004080100c001e2001908407a480d150503002209001058000d4920414400300000295a90040050103860000a110700c040c101c0000b089001c4160140c0c20603219250400041c43d00300a21034188524a50384000c100e00c903c4503810b9040a84000c1124107110503490340390540c2c0d0f4001200c650003402601c02201610000b0400403414070109044000500b000401041d40035400002d64000c40140c0c10013050455081c4003da00e80d4400d000d1507811509840c005403140c6800e41084244900844035048408200b0f004500419421245043c1469506041c481103580c0202900014444c0d88001c505281b041d600044140c446c1294031000c00031040081101c0c0c06007a0000854954001440c035650 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 120621097 1250 120619847 120619897
    0x30403051e0405100207050f0f130c05030109110a02061503030d050a0e070f0b030c18031e0c0d030e1011100902090708040302101e090302030c060c07020904030311 72
    0x780d440780c0a81405510307800e500c00c01c0300e0300004a03002036071340c001d0048140f40149010320000e1400200c600f40d0016582038074050f000b580c4c1c41031039200d1256940e0342d90760350704080402d0107647d40080b5008060234108006906203a000c260302e81c101e40c01c01203406811010b130002030f2444c001d000e00300001b5842d25040c00070102040d48611240c40c4410b05a4141954a8200c0ba03107150507889007060441c0100b0010703090412190080c203880c500441c0603041d94070141301103460082d2031503c510700703002841e851000302c0c04200040e100c00282110501040d20203550010022400c00c0d46107801031045042c0070404501035a24050902d2a04040781d018468100e070fa8400f40009820980c0140c1700003022400d80d034850f08003184242e415030020110350982c4105003004200c1c03802460540e066441c0c41d081c4050080c0120501035000754003c5884401e1140b0351400c0c00006860144400f204114400060300da011740c06a1054041c280011090b15134001000f1a2003040000e034042120003030780c03002c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 120622347 1250 120621097 120621157
    0x151e080612100c05040e010801051b0a0201060e1306050901050106270302180a0b03070308070f14030f0a080903071205030406060905010312031a0109090b0a120c050907030207030903020603040305 86
    0xc1b111801381c252003590b0b80750102030803200196240c46400c0c9403101e1f04818511100020100b10706548000501c2680e03540c001b81174000d00350b4180701d10700411801c1409212590081540051441c4001c2005500d00080130b0800c0341c0004042050040c0e12086c0e2410141d136262050055070060809500590303a2407502d581c0042c05c41390700710100d1900c0c0b03080a1070700b00001e03090183c80e40500b04034070f81205c6844140742888483c1c400c1703891000810244010300400d2014049070783c1d0f5440010749078044040003402d5504000c0c22803401341e200b4800740e80800e0182c240c4501c640350904005990303454505050f80600f1490b000603030307641d040000010030404040011006044641d80c100040081400320341110102446e1242c0003a440c40000d01010442c0c1d030080074605402003214801c0e507a00c100341780264045174400d407102d0204c0403081240b130500a80c9d45905c24668902140342200503940a00a400716020180c012000403000808040c055812182e041511808081c52a01c6020b03504003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 120623597 1250 120622347 120622349
    0x8030304030912030903020402030c070507060302130e0f010e041a1306060605032403010b03010e0705040e030a09300f02040b0609130209010315151e080612100c0504 73
    0x300b01e081c0019000380c03c484030981195042c2d9901c40c4da245140c0800029410161141c00741c0601041900300061007002208000c141d561005a16280707514107030041810180e1107503c6240f14030b02000060701c811803c0c1c606582c50018550722030b4444c0c0c14009000000c00b01020303081692403003840503025a1500211080307200c0d240902c520f0391100000c036002e001c240c810404480003a44100c000f041d28800300c41007040b020300001420801500000d00b51006120303911500e41219000340f01034246030003481c4065190340011460050b4510740100561010302c030f502c003401900300c0d914140d13040b0898641000c0e0303403403045540d0081440c1440791302100b00807001c0b0301c103900d046003e5000341070030304c10f4031184900142580514034000b4601c2002c1d6112011081c10140d0301c14210078080c0301d092809000e443c941107802c00c4811414005000c40324600c0003a44600c240b2043d42000b00e90000c65980c0c0440c090303131005a0f1002440d070803840d2844081c0a54441810031016840705603000d00584 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 120624847 1250 120623597 120623603
    0x20a03050f06011508161407061a030109030c0b040c1502060a290f03030909040b0a0f11090d0213020a03021e04060e100c05061006020105090f0c010c1b08030304 71
    0xc2c6899986203d640b00d5440d40000403c0801c0003036000410f100d5400e40c03810408003080c180301140740550407101c0c0a990003400200d5406a42e0540c1c010a0748000411640c40c0e030b81980204102c08031078401800400f16524002c1c910003016000508000c2c480c2404402400420b20031750007444802c03006500c486080b1201d16030145803900782c1201b80039041d446c1da41c24004084076601840060b06000d064000d050a150b01031108010300615a103804070909e109a0040c1c1d984041c500700006003805459020b208805068100f141030310b0405520f20440b90350303100071541034401c1603141c400b0030301d601c0010030700500891010804480d0740b074158000300f40b01d07007a1841c4104d0420403c0f00c112241c0c0070b20b00800c3c3c0010b03100520110035007840d00302e1032001c44081c180071070714412540d03441f85001c4040f81c15983c0002d805030200040c607024012590083c60850192000c2c40d00030740d502d980d480180c0d001c14104040ca00000052004090702110ba055208452018044d110b11491740d1780e81c82a1012 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 120626097 1250 120624847 120624853
    0x14061503150106050a2007030c0602060f0717130b040c06032d18061503060c210b0d020301021602091b04050d0c0b03040f110303090a09020307020a020a03050f 70
    0x8104020600c100780c1601c40319283d00d4100099002c0450b9a0607201501d91a1600843c041d03d03403030700b420403e113001184513a2805000c0c0303040841c003d00b01300015003104100f40c910800d01000c01d0b0080c140280c039040c2141c9262041d550060b40d100703034101045d400f0f0035001010b4148003e01540c42d00c2c07a025a42243c500340082e1900c00801c03000f04004001d81303c0c074010017a400307400c52a060b400800c0c590b090704030a486091a03944621044030342c44018003100499000742041084a0741c05650109486824980c0c0c1d008908200c0718a0313046d443c4110300781190707a0700d201d844540c0d84000f05c150b00c54014000310b454240600c1140c200300c2c5030070b10a80c0308221141c00104080805403001c03605038008207503203007403a1400b0b06022a0034050842200c5111540d180405d41c45060005503210783d01a0b00c06080036101d50403c6064080911141c40c000e40081020407920303100d10100d0707802c07200d0760440160381359a41c0710100d00702500740307100a5114540d01400801c0c003100080c103405104c020016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 120627347 1250 120626097 120626113
    0x50901050f2a2e020c011b05070b01090902130f200711030c0d0b0c07020d03080604060614090906060d061502011a010804030806040f06080f01150f0308030414061503 73
    0x4190151a60a02c00c00e0f812050b1010840c2040b00e150040e0a00b99620300001c58080c1c0007041c2d40200310101901c0c1d0740000d102049500038021200c2e802c42c01080c100d14100103000b4541c000c1661521041e45001413283c8510180740d00c101380c0d500c0b0203106903240038046e60320010b49806180d00d6100320803d98145c1818031000d0301c2e9140202e28881c0d40c1c0f50040c0051200000d5076211070502030018015254804240003010258031010f80034001e041c802c1d0b0300d683d203d14000040000701d6286030041c1080028040725036800d01608001c9640003241100e5103d00355072014001807240c0310b4890010001303400d000e0001075055082c40e1400c00184103400074015500c10f007600740c1c00c40c0b44609090380000c000d074010401190040200c581c00100203800030035140a44202d80e015140242c0c010b48440e44184031a07032040001f0b20800c0f003001c88100844840328940105409c420343c1c9408040d04003007000001c82c00700501100d0300c00d100e6002e20705a030241d00d4010031120810100c112068000c0c090090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 120628597 1250 120627347 120627373
    0x301171b0109211e0501051e0a0b0307090606030c1b05030a0f0e030609160f0e01090c050c1b010908030702010801090209010203090301090b06040c02030406050901050f2a 75
    0x144000588040c0e5480c0706541c0b400795001a80351041c0d10f03003106103088140070300118440c00308152000ca50f12035080b90214042c603000742100c1c4003c2000140d0469401c0707103404d0071040e40b0500d40285a83e05d010441884000001c1c0c1004010b90250b20800c1c0b80050000710207070140c000d0050394080351240c0d180c001c54014422000900b4146c0104070760804c003c40500103010340b00c0400c049086241503070100354503101282c5040801c2e1070000780340d4030400000000008010a0501910310302184103203452416082402e00304040c06604040c07a01c4044c883d02c403600c00da0690741840183c9048603020740500c2180400075000c003603d640020340440012448001c00012a01c0080e03042c2d68074002c6a02e0502c0d444000d40140100c3d90441c0020007122400703660034000c0301085405120b05d2400c50908108110498007020f02d4617095405c20300082181c50303008020346000100070b08010351344400d4180c262a1501c1065660100c008101c0358565100c40100b070b210400c13004a0782204e181c848110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 120629847 1250 120628597 120628633
    0x60601020d0203040306020322050601140d0203070905070c02030313060e010912060b0f0301020705061501030b0907120f0e100608030f071b03080f0d0605010801030b0406020304050c06030117 84
    0x19072000750744208002c10014036103074010365101d4848034421905010782030706812401d805d80816a0994440c0006115625183c600746a039190115000032001286a001c251641c10318840c8511190355000050142405403800385440c0b0f07401400e80344c0d9048461100d100c01c40c50f40c0503060003c1d0494034040025401079220302c06035070782c0840c0c01d00d0100c107039952007018107509160a40c21142c0d03d40b00c2c00c0c00792000d00250007a14070660103040070b450942001210013003040c641604050800013220156107500c5004c6810481c0c52802c0940c0740420310784800545450320103d640c2502d00322a8800f00100450040d20801880c8020303c039080da10751516641c0d01519101d0310360518204080360000703015501c4602d4500a465441c90346d60340e42d40310508560880d00404e48084c900254a9400c20020300c500800760009003003100e86c650468403984612840103000402d915800000300d000e02c80c08000e4031003006001007416580b0760710b0307090302d01c03107510380041e0002c0f03910408a030010185040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 120631097 1250 120629847 120629863
    0x6020105060303040e0412021e0106090b04020301030b060d080f0d1407030e0d050a0c0503030906040c081b0d15050106090f170a0f02061309060f14100e18010e0906060102 75
    0xb0000c802c0084d00c0d45d454a01d04180307108915401d5115500002c039020040203009641092794000008041c0e02c0c040451040e104081d030300f1345c440d51040006200040c1c0c0c2c1c0380c03210340050040d01c2072649061940391202413841040402c0d03640e4400442c10181c2820203401101c0640c6a01c0121f5802c0e480c0c0c207006506440c20031200c05199002000014403041c441d01c041c02c0074141501d0042c0b504521515018215407080d6a51507a41d0030000801041c03007164081c820041140900a040100b140b6406401060074492058411000410b8075030600c4144801241c070800030900810141d65590005805c6410030b1260600e4084100400100f200c005c02c2c2da44050000d02c0080c2000041981c0c8410783c1c9030118008070b034800070a110260f0350100c07000442c4040c0c0100c000000f40039041044a62040c4465803181312189000c040300790349500c0e0040075903006816428807a01080c86440022099a92080c021022070091400003d50300e80ba00c1e0041e006881d00000e07552561625001207844840f1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 120632347 1250 120631097 120631109
    0x50a1415070e0f0901080f01061a0d0203060a05060a030903081f030b04050115181503050c131e02030412020a0314070611070302010e060f01050d021201240602010506030304 76
    0xe90001d646503000e40380c201420000107001d184003c03032000000709494020703080790076641c0c03207400c601c2d040c00030074810300015021189104945865540b03010301c8601c5110f009200050300440825100d84494102c240035010050405460303406c158070050003041c0160f41500004c08000208038134402c424140350110303226510300b1500b68115121031401041c0540202c1303403996107142c90079801c081032840c4800360540c07105140b0b074801500c1c4900141d401d0710026481403a402d10341040001d200140d5623201c1481511032000b143e461000b00401025500c0904014000c45918408484500e500461140d84115921010344400c003204983c0c405010b4001004141442c0640c40b030200c49102520b5018410100402c240a02c603a030f20306550080709044001d42c4d12a002141004004d0000c4c55104040c081048410740c90400000e0846075034100c080e010701144915080d02c0c000039000045410141c4480c1e99025000b090381ca1200070081c0319601c0107510740004145e603403901004907411110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 120633597 1250 120632347 120632383
    0x20706050c0d0e15030f09120307081f08010c05090103110a0e01080405070f03033516020304082409010e1018020907031d01060513090305070b04050a14 67
    0xc4030b100c00340d480e040190b00ca03035807100c0c0141d00003120807038110046101e01c200d49610306c441d040903da03803860701c51080200c402e0100240308219a01c1d50100c90194007601c444000410a03491100003285070704160008840703542000c0581082642040060030444030a80e000c00a640002c40507000d03500400e08000002015a100703441c0769841140c103c0c0e00180039006454a0341d98544404c0045401c56000320040388220040c4d07850303400034824003003e8207281003007614040d214680c4805684070082c034040c0300da0800502000304520030820740300508003910403601d0702c0382c00c1c2500078905045000c1c00040d03407107010001a01c151060080c011252120802008410040320003400a0141884080e0000303402c0c00500b07015035146400c01d40113030702c10b480c00518200642442c1d0480f084205034010168100002040700761595001c07800c8051345120002001a81454125181e100d070b881c000e001030100605010a100c03011680410390ac0c42600d18500d00c4000c040400d454100010107020048 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 120634847 1250 120633597 120633613
    0x1b0e0106180f050411040b12010e0703020c0a082208030309010b0a080a020f060f03070e040b030f0c0613080a060b03070603090317090106120323030609010b0c0a060603080307020706050c 82
    0x1080c503811445c20250f105400c242001d8407500c2c0c1c00100d400c00c00c803607181d20556000400015000208460f00f150581c40d05610b0300d2102c0804503941c01140e10005e1400c0000140080e04c11361200703448191500c40d201e8a2049642c81500c10b030360b0303081540c0000407540717468011342891400300d0540c02100ca55a000d080b01440c203030204840b041e400381826801c04410410308016110050080d0310034911601c4080d4104051000c4c0310031035a02c1d100d5503000e076001d141c1414a1010004402c0e04105003181c80a0362400700300340c4410014001e03401040b9a205118902e01082030580001c04982019011181c4003507031910120290b580780c0b6006004200e410400f4a0040b042c54002603101d0071510000c00d03616551a4140c4400240b48000e07030018180003084841101e901e02000d10390a80360544a0a5041c40030000d07508240600c40c40e105c5520000c0d400718508401d10074258101c3d0414000c0100564a0500c0e0340140e000321075120050169641c00b044042c00f60055402c00c1d510080209640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 120636097 1250 120634847 120634849
    0x15080d11070608040602040902030c120912041404090501050103050f0d020d080c0918011202120c0f061809010603020a0806010c0525050603161b02030a030c1b0e0106180f05 76
    0x1003c03026005841268003088003150b1480341e400118021500c980495556070703900e10800600b003e0191841065401c05413000041c500c905040c0c0c4d080d070f11600c100610741c0e469600010010504108010b15a5003064000002d001000c108481c458000c20161801c0d0780e0400000ca0305c03029100d00b904003140412000c506500c0b042005880c00800c06001101e004151b40301348807402009a200035800b410080c86201141401c1c2c0d61030041818020040c10710b0780618000820403518290003130b026a10103d541c0c0d0000100c1d1807203c1c40040d002d07003440079650319110010080d500c194860030120320a034001c13529135441000e801514581010181885440d004110803950f801c400c10709504110400c004941070342c0b00e00065004041c0115019511882000302410050b01e0640c0d84114400095241c00961004100707140c1040e818034050124804030711785240c40c0d880201a904c1c40216111022414120015005050300d40035240c00580c4284894909441115070182e0102403aa0714002c01403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 120637347 1250 120636097 120636107
    0x408070605070f140304050102151b160b01060e040b0907080a1505061b01060501170c0a03020c01140402041b021b01020304120b010f0506030112111315080d110706 72
    0x5054811030051000340352641300c030101c0e580d0305200c00b1351940000408100c036680421583c44184250074803110103242030703100e02e0141c42d00203070710940b6803000280052031012402c81280e206c60340211644c2c09942c54600040500b10f04480980c007c51501c2e4402071701e0701c0c0400b10684100c405a4034000281c5e100c6810f84060b05c402d07402095065106003010450340e8400010700200e100300007041c0200101d18a00900355103882d4071441c140302d0411282c204050800f030803203900c50360106c145a5a524071110403002882140c0a200142d4685004004c02d401c01d685058060741c000c40782404480c0441142500100006800708096030011003c96007001407201540c00001050066a042540c3d0304180351840075030311011205030300d60703034018411110f08207070080141c0f41c01c0d503842c0d00b950304040070110307880380041010b00191145825903c0c540d0f980100c2d1170140007214424005000b0f1b41d11850040d01c05400340d100070380111114460304900c10718401d243d80010f1001048100d19000c01569 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 120638597 1250 120637347 120637357
    0x4060c05090a0830030408070510090b0a050a05130b131205041a16060e0c120106060e04110910021203161b0804060509040b030703050c13020408070605 67
    0xa111081c442018580e640b10500760060103090058104400c0015a040503201d0303101500c0c9035240c400e410700340d04181d8102540e0f132140c3d00c01d0b00690380d840c66080080c86e06803003940c030208880c02c000c01202007103c140707035142c000c0520035818842900e412001c0407c1d1401202d414009403904040c03180440c4070b1024060304441180c2043c82c0010340c030380741c2e88500340007041004003051000a04205941c0a405c09083c502c0210103400e041503030080b44910781e5003000001900a40e100d20404074401c00a00c03802d03080c000000c4c07400c01011801c006050207032007903200311b00220307091002007019402d1600407a5234581c590359030103142c9801c50341003014a0a0283d212000c600c1101c003402c1c04401040300450090041002c40140f4070341c010001415049955000034017286001004800a0150000c3e04c065501c2400c1003600c0300c0b501e00200700203040800c401c3e6414802e40400000340880410f041010b5041a9510814080c03001100400d0380305520500c3c0f02d541c0107240801c0407920a2000e80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 120639847 1250 120638597 120638621
    0xf0828020403021206101403060105150c0a051b0301060e010506070804090e03041410020706030e0f030d0c02010501050919050c0733090302030904050c0c060a0903030b06030f0406 79
    0x141000c0d241d4011039410307401c22410383c3c010352202041c84400d1b00802090001499203413041c41c01500c0c41d50100ea2241d20600c0303118010100411042000481c003c2924000c08030390046070041075050804030f649840c03120300144403080075000b031032103418103002e110191210358500031001c3c4d180c00140071565003d82c6042e030381c07010240804240314071103019505080300340c00001c585460400c820b10390401d5403107415500c607002d0503803424a00c2e60007080340c004903602401e0002d0106040c000d0b1070b0a0080301428030480e40030000e4071142d60f800503804070006402e6980200315603030300d403810310685040582e94503050070b000c403d415141900c6500407640c0b00c091114114200341050381c80d009125521108800b004851510310310b0062541b070980c490050442d041482084000d8401a40343c1c42410122400740c3d0300c8100048401c0d040341e0899204600388412a1420b03d4551000c1000b00030300d8a0840009081023504001854940103490203960158081461520759a07102002080440030721 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 120641097 1250 120639847 120639851
    0xe01091505040f0308070c090b090a0506011b03050c01050c0405030a0b04030306180504060b041e150503060f190207120c1704060504030302060f0f040210111b010f0828 74
    0x11907004a2006400e00075841003001c0ca440d4001454181c01090b1a5000402340c03a1030000d40c0001aa03584141c95084072029000044640340c141c012100c001035040d54080701504501100c0030140c0c0607004182820109008002644501c043d04903617104900c1900c0d4154443c5010b00b0103d00700d103601c2a0064482c3c100000c0041c0d0313503140003002c21200c4900b114210b580e11308000c284121405507a2004000712401c0151000902c448209550901c0e90b009030107176030b00718540d10440100e4000c0050003008088451519180e22410110082200e150001003007035825144901040c4c02a0b481c20755105250502080038480c045410f1a003150741a02e84015412041480c00f00b100d000b400605460f1780d81d59520360842c24080d2400700007511030156440c040303040142d0f10301c020b8240380d0410350460741c002c407864688000b101c1d50304802480044034000e075910308021184112061010680c00e88440d900f005502c0b50960300d2410841c1c20ba841c1030303950884a08584c554010301c440c81440c946c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 120642347 1250 120641097 120641099
    0x4020d1502220602011b1e0e0904050a050f0303040312020d0b0a0602010506041415010804051c03050103030f0c0b281401091d1c11010507020c09070e0109150504 71
    0xc64110a42e80300240b103100c400040702407050303641c28000c5001e50410aa10f0701c0d0b107102c19a030024581026040c1c00300429240c5032550110a00c2104443c0c4000c400909015071810703c4d00302030741c9924442c9800c90320742c4901c01012140400c00300035a03201b903400d030311894085400c1c001100060350081c060310300020382c1ca407129005940e55005680c01b0342040e0f030000409181280c2844202c41d031868031b5007807042078a01008800031410000600000702031802d040d01d0740342c40ca0268a0b081d4500548200c0a0b610440c601c0030f02c1c0e06074002da0480303000c1e0b81e640000e404c000005036114a1114006003442c0c0d00c03e00001c2589043c180c0f50152500d440c1c04500d00311800004030000c42d0300c18549003070f00040d41001040b008850303001f403501004240401e03004003819402001e030303030354011300c140e400c044070710342c05404280d000c0d03207459900407001d000034001c40c0303005c03100292510b02c0401310b40d1103500110040f90041d4030030801c0000214060312000003a50400c00030304200088080d0400401504002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 120643597 1250 120642347 120642367
    0x80712051c030605030a0b04030f02070b1801050403021507050601060302030408030a1a040f02130503010b03031204031704050a02040c030b0102070303050714030c06010303030c021b0f03120a050a02070e04020d1502 94
    0xb03450080d40078947c0030003d410a4035008008800710000c2c42c045500c1218140840b0340079074100c403460f40605440035148150100140e6280c012541301a40c000810a034014050002000620600c0c0c410341c01d8410586e00c0e02d81c1130b8100d00064a01504158003440011401d10580c0d1007c1600a42c0e0f8411403503c0c2c10003400101580c401401c0d82034450b40204100810f107151050787c90140604400a00800b405400406e0b500d0040c440543d40c040349020201d41418000c02d0500403c4507015240748091415081c0541e0303e14070000224040e03071070314900320700d200d109200e000305952050340034240c0b0902d1511b00710f44a406c030800030344950312256000c0d90000c0302003008102200e00900580300710741c0f560034080d0842e44400150020764000307200b11500060b0381c4861101100c8210f43c0e02800041d004042481d101168040b01c03040440000c01e01c0740103030014041e00104c0d1207903007110782d040d0f01c6143d8074444140c1074600035049040042d071580080d002103143c40c041c02558100504080c4809 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 120644847 1250 120643597 120643603
    0x4080d0e1006050108060315070807030b04021818041205090f0909011e050403081303030f0903080a1a03102a0e10030c0905060c070b13080712051c03060503 69
    0x40e0380e4544280d511002000f5a503000b98045500440440240400d40d07510b41c08801201c400414402c20003ca5900207560030b0300a40c0190f200f154040c00441d15074480c041c0b007500f49105011401d220380d4280c2100b1030400754500c07141d44a40da000300005441802a01c041e151900b1024030030b079218a54205002c2140c03100d0807030380d02c40e000050003c1915107900300b01901e85011011003480050800041102090704421602d41066410b00d500302c000340d407828210024035001c900c503020a0305000b01c01051503031241d031013401200240d500b003048010401e07d098042e02c014011981640111003541d1540100b984605203459541000009a8000c40604610392000c50b2040c800300305d444035407294500740803402c580c0d00039050904020159990901521000d80c0b44525449441c002540b14509034061288a005140307801c4c01d10703146c1d000c0e00f0291041c6c50040c0106c0c8920f1080600c00a44582900b03001240240c00401411088221427600ca801108071030f80c6205241c3c440b4000182d03070b00c0030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 120646097 1250 120644847 120644863
    0x402071110050906120f010806070e0f01090803030f0f1602150417040902070b0c03010509060d1b0b0c010c08070f0509030a02120d02011a0f010309060f0203250302040e04080d0e 78
    0x45e101204c0d6240140010094180c10f0b04001c015900ca1800c20440580000032241c03034030f40c01c0740d42d0142c1401d0180100c40240150f08105c410340800b105118080402e802154001c0c030014032092081e41e03036400884112200c41d00e075200140e01c00000320844000242c01990001d00403071180412040300d840c0c041c1c16502a0340200c4174141c0c000f0b2900f043c4100c045002c0d82041405500502d554980000100031170360207425184541000d800d201c0c1000380c0c6914541d540214801c15030810399071070400d091250841410541c0550810034583c03401485400d5141c443c254603181e8040c42808084200c9581d002901450303098801c1201031805a41c610100a2450140758000c000d54071119000a081d1600780300b406260000c0364020f41201d1b038840044c40c203414020720b4002807070603050505001504100115251042c4000140801e10403004182c04082004400c4a8040811001d00310304034400da21490742c056014101250003d8143c40003040c5102c010280032503a8100028124102014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 120647347 1250 120646097 120646117
    0x206070909091524080a0201090503030c06160201020f1306030b0405060306010504230708180705030304030201030c020a0210030b10021c0c0524070e0402071110050906 74
    0x10410400011551010104000d8074100109015591003a55002050b0881d521a105402e807070710404800c445480320142d030700d5410071042c000420354458102e03480384101030040c3e0025140e0f01e008034443c100081220003c00846c0001d0220341d603030341019000c0c1c01c1003440010841d50200b104a806103a0400604806070001c2202c03403040345400700190032250510300c0c1e140124240380c10007140350341c0807034802d04441007590003040360010341d262012040c0c071404604031048900000e00902642c000103403032084440a400001c1b40ca440220340703685d560144100c5038141d00030041400103504c2500300c80c00d008043d0040303466556403640054241d40c846000840082e9848402d400309180455039075162659034000342c60f4808016007514800c2c242c0881c00414054112000f01c1040010894402d15165601ca030361b03030611594031000e100e802c0c1902c1420000b140002c81d240d0b1444d00d4404c541c00345500c4800440701e4400d200501041400d00000801440400d10070f00d0101d4403000c00428041c02c0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 120648597 1250 120647347 120647353
    0xf030809011d0a0e07090b043f021011010507030e0c0105070515130807050312150315040c0b07080d1506080118020409091b051909050a110a02 63
    0x5a5400106010200b0a00368000c03103045500315503c0d00c420100f1002c4d50721501e5503412942d90b00c04280c880740082c0d841100d81410002c2c001848a00a81140020110300846100c60100340074041005045000390f14003101d0f2015400001407070040014010602c103800d01000100f140403425003150800c681e41408a5260304043c419140e00780650b10800710300f403d00b40e01f805580d40b607969580652030550640342c20150046482030920340c110092069015150696850482c60096125000080d00315107445003140820040e01c10790b0b1148800e0300c0f020f001003145003500320149400402c060002e131b400c2d4010310404190035406200601e103107809410000d5451400500d0329080781c90f08010b0321100102201e00340314903948000d802d81125a03010032080c0b0b0301002c480c86002840349501c54081c05103030070003220402c9010a401c5000b800590203c0120341e03135035418400c1100c40200b8060760000c20b03a40900100074aa4081501310b02c60031340018030700852002203016944415403a00142e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 120649847 1250 120648597 120648607
    0x91005030601170a200f0d02070c0302040603230a02010c0209190c050717090d081b060f0103110405150409030309290903042405070f0b0603010b03010504050d030e070f0308 76
    0x201205003404070310310f885c006a85841840764101c0c4d05406038140308414039400040c50b00c207120504c003502c00a143c00030030810103550303a0300d01440c2e4101c0c07903841c1078881200502030b01001500420b00d40390b000c0d010b03183e000c0c01d0030f00c83d401c120005400510046e1a840b4038081c260f45415984640980d000036074941e240d441c0d21608042c5800f0320148020000c4e50010403030055240c503002d1510040e81d50019407187c8845c441101d41004004100b9010818821407040000307030088400c000341241e00500070340511800b100144020b80701c0403204484d040c4009500a151810301e0350040340024000d15002a0240c416940c041500c0c5a40280e101c041190300303080c0c00109a903000706038000180700002c52505103001012081400704060100c8000201045008518000d804540c0d1481e80980c5240c00d8000b640f401c3d41c240381c0d0965009010b0f40c84c0c040441c516040511070036001d1070704200244902c201058085025046017500d11603e070090410001d290109441045c021714400c81c0c52644031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 120651097 1250 120649847 120649871
    0xf0e0a0203130c2d031a040512030c030103030f05092101140415051003050601030f030e030d020721080304150902100201020406140f0a080a0605031b040f02091005030601170a 77
    0x2c1320001201981d60490074100001224001101071400162620705001d5485003400ba0070515280c040c10360ba01000810040d41d0301052000b103050f00d02c40d031128458030600c680304803250300a240e0601e4020380355030143e0401c00a009000903032021640c0011950320f040c558408041d1506460817620340480088601840c51280903880d440050030509404a620b5a15031a45e00c10040c80f0181450000741d540c04107040c8644105001510041c04550b0031105115000b99280c40c2441020008000c266080307210003641545900800e4001c070015007551200c0d1119180030003c03004d00c0032020b030340d1041d0000603114010140280511a000140c0700c520b4104080c180341a050100ea00650040004450007403201065400e0103200b031506c168540d895446401c000c2040b90800c590621412190010b11603000e4180c00154a00759001e0042d1160a00d490341640142c140203030b800105440880f942c244200003560b8031000500d85095188a651160016010161409100140c0780d14800000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 120652347 1250 120651097 120651149
    0x602011d010506130902040f06081e0309010507080f07050109141009030c08030603010e0708010e013209071a09010f08070503011710020a0f02070f0e0a0203130c 71
    0x4a84003000080c845403921000141d050303040c50f200606030369540c56180c1d096460380e60050320881a5604200020341d10390080558584001640b500b400c086401503541410002c0190740380d07044107844243c1000380c140e5500e0340350f42081c803080c3c000b95030030300c410303c00318600340500301e11a8000e55000214500450500f801e0510ba0042450390034102411b15000960092a21809640156140751640c84080c0000d000d40012611400c1601ca50a40441e40a0042d4480703040ca0b080700d40200304110303020781142036004140520048401d100303080c8074120781c2e42c1f080349940154841d0a5401d49901d0307007490100d113a29079004548585010403000d5403940c110007640300c00401401d0820003482c0c0b0107001030141c881400360b1203041d880206640c121b060100600768102d10003010079521002d6015000b0400400000f10b6001403144c1c0100141050406249500b510002581d00344c1554406004001a61014280e00100c92103103a40b05e021074950304820000e000d981030b8a900e9070b8201041122 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 120653597 1250 120652347 120652391
    0x111130611070602060106050c03070f1101020c0f06030604020c25140108040c0306021e0f0702150301030c0b0a0c1401201c0b031c0e03060c03010b0a03050c0d06060201 74
    0x21141d002e5001803042075000120f190440303446240c0241c2d0303100740e202109d065019100005010300000186074081100702c81504486140030b9003102c600711401e00805c5a004200a000d0382c000c402000403a1260a0540040000e40e00c0e101c00c44014a42800800ca6100d0a851450403486001e000c20703c01100c82c12006205034100740f901e000700741000c0c1c0394a04070b81d61610000b80700341c1d0f0000310546203003003401041c00d201c541c118001d612030602403c01562648941002c0303114400e80e000c06a0b04205c0801900d0582c0e400050010740d05040002c0d03004e40794403020402d02030007030f240e0300c800005006c0904c0100d102030120001c592410303003200510b00302c0d006040001c4036210a004c0c60360151444220f2224200840c003004c00e0f01195000441d00749440903001e05260300300410218007264108092100381c000540840b056a6181825285240428040d115079060b00300050b8122910942005030018100c2c01910304c1e24079100e481e1130440383c0f581c1c0074101603511081000c4990700680d01c070384 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 120654847 1250 120653597 120653627
    0xd020f10020307213212180708060a020a03060312050a02010506030d05090607111f080a05070509010f020c04060f0905060f01050702190308030f0103020910030c12020301111306 78
    0x414040c603442c07020740101451140181ca180210404221805c13030690082008055620819544c40c9908265108020101c130002c900c01d641c5041a411151700040c1681111000e9020b404d040d110300b812003002c4d40c0000e1f1954101500e43c440400030807000c60303140d418400c0f07a481d01baa43c1d10740b96502078252440104080c4c483c1e0021001c240c011900301c0101c1e0381c1c0807000c882c00c0d5642c612524081018440308641541c00440c5244000d11074042000c101090111a841b00030b455550140180d044d1a012104000010818040c01025500031010b04034018824010303102c100c49001c010808941c1c1552280300c002c0d9548000f008005180d1007016040041540c808400d51521400a4000d10504c18001d009400d641d00066402c2c00b011a100041e56001d01c61903528140380d0060100000280020780c40f4041080124104600c100d03505402c8030360158074800d800d031400e00d021220901d0310006a03015500d940c01800c1c0300540400401c0d00e00c40080c1010103c030304001f4000c010310130121101d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 120656097 1250 120654847 120654893
    0x30a050a050403020c010507031101050405031b0105150402071505160e0a26030d0606030209090a050613020c0307020301140103120f05030105130e010e10051e060d020f10020307 78
    0xc000072130390201708400c8903442800c3c119911400340c0b404030b52091030003000d0707051540b0303010501040140110040a2403480740b04c40090003500b15030010308844042e00d9007078024026540c0c40180341020f4004d003024a0162071040c000410801e0045e069030001c944243d00550f00c0d40c100003e0540118664407607000648640f50041e0400d151101e4144c8880344002506400d186c1da207010503020000c69103440040203080c002c659031544060080e4000c020924461021100050054500b80c0310700c42c07003480c009043c4040c0307c8182c00d421000798040090303e000c5000402100300562000d00501903001c9400d82d5044071580346040404000175417860b418200720b5451501301a05602c031050700d0540e80304072000d2038400750110899004049060002180754200003052000e19800310301c00c5540e644401040c040307a074980032a8111400c107030b0070310401001180c0115a203070500c861038000e0701d4405409050038044d1782000a140391800100c10006174000580343c400c000c6007001c4281058456405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 120657347 1250 120656097 120656101
    0xd0e150c0a0809031f02040f091112060102031b0c030c0405040305040e1306090312060b0406090e0c1312120509010c08090d080307020115050f090106110c060f030a050a05 75
    0x10160300d036260300030301400c10140030403c05100e0f40e0604c01d00d481507200700c0d210050b08854215850203500141b0035a014141030070300000301c0311024080d407012580044d48484ca0003980400c04c0c190408040c110604520090000044074a8015516503851b100c000080140c452082e08051600254412650140381410305102c0000e401006035001c0d500513500c84000da948801000000301c484403000303071442c0c0c1011000024582c021924408e40e07504100c05026040d12124440c2a134482c0344076120000d9110041002880401508036401214252000e0728202000400384003410705904031a21050700a01d9034010000b07054a02c2030f4100850400c14148400c0c0c0002816200320300001034540303100000d905c0c41e035544083c05044a184d014040c5500d0742042d0300c00074001c044a003151040703620751101c04502843c02d071031521810107000303040d514180c0c00c4c10000c8840c05440380051486208554194403a0359034613005d801244002480c464a0740307481c1060030305580025100b94481450101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 120658597 1250 120657347 120657367
    0x11b0201060e2202100e09070806030c09010503100b060f0403060b0102160308031308070b010f080d050c03090f01050d0e0c01080a020c0703020f01090518041a070804120e030d0e15 79
    0x3001014440e0100d0b4a1001e5605c148010b03940c42c0001c01d0040d07802015641001a04c50f00440998050b100030707411124840984018420741450a00813254964400301c145204c8184907000300303505078130241c401421702c001203220002a4006400403240300780c032203662001da96030401c00144518002c1c003a071190301d491500c981c5441d00c006065a80320124031400030040c0001041158040b07a80804910a2983d50300800b02201350580114800d030f000f01c1e140141071078400e00a44010b501014059840e040611003000090881c122080b8140001845a2031a00c0c0e5144034000020030080007500c3c0541c0c030340000505e0008003e00d02c1e0020342c0b051144451841e400034500c0d0503240c3c1910701060700701040006070384888641d400036601c01450f0b07103484d510007079150303415000300c2c810b140f144a4518420003141c0e650f10221100000100a500020046540400b0b80c08030002d03a07041c00304007003031082c01003030811800c0110180806c500c09840035050505281d4520540c110041143c10044009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 120659847 1250 120658597 120658651
    0x120305090715050904020f12090d020a050705190302090c030604051608070324060c1202070305061506070b011509050a05100c110306070c0b0604060b0a030e011b0201060e 75
    0xb41400100321010074001044e80f40c981c111030800000707421940d00c1d40000d42c55111020011110100a8010b4400724850103000084040c965603101c805003401e2400d0600b03005041111002001e003910303520800102580310825002e009011804140d640c901d003400900003611350140145c2c04512040c504001c0842c4e0004401e90401c19070314000c80c4481080b0800010842c1d8000b56042d0b9010380300e000184a50010711200d1803030320403010704000f81c0c0001c900703980b01d40044c40050401d80102001946402a12a002c3c00640c0300a01c20350500d80b85403111190f4403070036007100c12280070b68660780d09010740016585000344011100002d8060401c40420906c0b002d03008428180080b000c444010404113031b100e40034440010302192090714241781c004180c0c0e60b04900659007603d001c004202d890a11f030045d20b0a8407000841d40f0301d8030b0b4110804134024002c000d0406529507070350400040e03000b0741d4032090203c0d141c00d500129880c6d080100000e5106c801034200c403412000c8803400380408a2403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 120661097 1250 120659847 120659879
    0x307090c08041e020a380903060a1103060603130f0606060e0405010614070503040e1f080105071407031106070801080111040f0308090102030f0301030606091802030a0b070c050601031203050907 85
    0x10303608110880c800701c0c50500c1540f2013620307030003070f12020ba01c1000345103100000f5101f10202141180c055403200300239001103a00e802e03141070080c0d07002c01c0018001d04101000f150002c1d12066000c0c4020000c0e2a20300300e104141c20b08031845502c1e04001c1164550002c0140c40a210403942044103500d00080500040b50f014028410302c00045015410b105050080d10f005000c090825803240c030700155500d070074000b01d04980b01000c0d90751902090302c0405215041c85101c454483c2440b00c0010314412820b03030825601141000400070040c0142c11003400018066400c9403144141b55040c84c4004e800d590708851304d510082000d01041010f5165100780300b003141d80014060390f44c0d60039000101d0131440341f014842491180000000704210315039102000311807016204014921901080b2420f550b011800031390f041d80f0452802d00440c200d50b00654110b030b60350605140b841210b9440c181440400da00a66880c03940c00b2884400c03a8041c003546903c2803074280a0060a810512120214904 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 120662347 1250 120661097 120661109
    0x6090a0b0c49050f041701060819110f0d0b060312090f060a0c1b03031b050d1d0a06110d0c0b040609030e040504050102090a050306061e0307090c08041e020a 69
    0x302c62442d0641c980101c04540a0514640c0ea82e55101c0e100c12141008034052108400258608403002400e100042800326142031a40300d9441007904a4584100640040a10a07440602d200084c3c980381d4440740c0c00c0b1041403003010001d440d80f038030a04142c1441e038400c14021501004100c2c0d50360540e500400061140000c07246240c4403a03900070b080300c2c1d12200d10001020f01d000001c840c4643c0d00b40c2e02d440000c1f00d103c0d03a204044100780c500e02e00c1c01c01991800007000303a48540b801000c503e020715200410711311a66902b1045038040e00004404204c194800340200d001c05411320a181c000b84070408001da05410603070b0182146a45166603054010405014540d0f42d9004c0c00030103100b00aa08908100100103002c0c50400341415070013988400c505900c00c11120b400080c00d4240412514411207005040511070181460301449918542c0100d0303905000e500004200b0310042e104444210b05c9a0b91030740898503240c6480b011040242c11244d40c048000d0490b00c1c010780c5c80c180b080c419074031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 120663597 1250 120662347 120662473
    0x170903120706150e0907080a0b010b03150303310e01050d050a0b010b0c06150a060c05010902060703090e0106030e0d0f170103060e0714030c06090a0b0c 67
    0x74107080000003055115420215105004400280d804501003214050300d0281d06541155540f0700740c0c990b480c140b2050092081140300010015001d107080a154420701110b1441c4522006200290440c0d2040315001d6a4801d0140800c0b04051088900800e00c113083d030b0400c03a5241030112440220a0510416225092520800c0704101c001e200780c2c080581e0042401c40c10356180c4491f8000b81d0007640305070230680f2139200050400490f65400150000c0064001c8440c00d041c6481112880d006c000c06490039900e5000220040c1c40381030003404458003a588401099040c0101c10f11140010ba000004044c20328529444100740814070101c800401c1c01d1000b8003081503072007950901481c2c8512203600c26800c0001080c001181c00804035241000c2c25500031540302c0c40f03401c03881e00d180b480c0c00b60075074064080c10540e422300c00001c00c101140105032804032940d070003050956600c020700d00d840541003030410140c4459071284a914160041c2804c0c0340343e603a481c11603030030100701c41c1080810389 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 120664847 1250 120663597 120663607
    0x50d11101116060f03020304020d020f0102030708030f0a0b030f0601060c11030a030c02010e030d12110f0d0b01021b090406050612030706050906100501020a03031e1817090312 77
    0x34000c03010654a49035280690b900710484818003441d4060521400e03010a650a99500d40d2510038030891b8441c0d54001c0280103801a607800f031012140d005010301c0d066110401c0342e1804524044095441150344050080b03147c503165102c4030079100651320707031030095201111013404206d001c55003605540d07107803a00f51076410f030f00d00b0803c02c00360800b211b41d1f03003500800b5000c07000c3c96808003041420354008e80303910a005104005041e500c25581c614500001c219108000c40c01c0d4441d0011581d440ea0003044a0030300c190703040d10600b2a8030104040c2c60b045e6503070102d441256018420b0074180151090a40d90040e170110104850303080c01130005100d29616000a00d9640d120007201d02a2041c09040b42e880d400315250100047c80199100310540c842c031000100c3c0c2c10b000d146403000b502c0c41070b4040c000117560f695080d0081e01d844150030318180420164042502898420443c07035800700710304a4072518503801d1443c012a4211405d00c811282009513110340d07203000a4030034511f00c801209554071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 120666097 1250 120664847 120664879
    0x190e0f070603052e05060403110f06030601050901030b0301020408060702060a0e01060b1903090501240b0702030c1c0b070305150a05010f0c050106030611070c09090b070c0f060510060306050d11 85
    0x40d0704a41c10242c2d2003000400c001c42488810751821500d030b89c0c1035800700b10440e900401c00840b030004071202400200f08218100c00c2c0c4d4070a81041c441c07044090005400c05454080c2c85003052001c907110401a40000c0800008c02014021081c10403042da00030025182868001d890307510842c02507005050080c00318031031440c421f5200e000810380000080002241c44400f2090403550300c0c1030f1017901261085e001c41d207071420f0006c5403a0b180e4010000e149552914081c0055038403244441c410340c4441c15010004500c0c5030308080c0c0b160302255030000c2d00d4a401c6c4005c80c10003000c009030500985444205210701c0c1d800c50304105003500103003040303008550145071890240030580c1000b0b000038184000200311088a03005032a00380d1080c0745156000d52141754202c00c441403081c0141454500d2400320b41c189000c0d0081501007409418213071030740c0c1c00c0b0740c4a2130251241524401c2c0c3c084c000700030400549a05101c0e80c6c0103004110b525000290706e54603514190720a072603229120300070758410000c0c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 120667347 1250 120666097 120666181
    0x2033304022d01110c100809030c01020408150f060a03020405150307030f0b0105010507030e061605060f07032003010905060d021305060301052805190e0f07060305 72
    0x44502d60000d0b8081440009900100340c0c2880512a02141141503155500c1102040b030a060140240200b20850308504007103842c0d40010b00301d51044d000420401c1035000c4d0a00080c409081e84100501204412a40300c440c01c58000b40102e400d210190180403040d500c1d1013112080b241c0440c0c000c42e840e200d20385811103c00704011a140c0c10700c50503c000041000302400107040500034000c071260340c3e07a1040155410300c1440c200800040703211251055504e0041e0240c052030400e49d140c40302c481c7e07095a50614000041d82c1e070341501490101040104c9915009000f03602d00c1c1501c440e00d82d00903868000840340418001c010280e602d4200103001610380c1154241c0c3e80d500104091078400b06402d501c8003c0105944c1d03640a542008002560b0321441c103e102c400020b00740d140c0e1a200c007050300501c014807014005040c11040258241c2100995004400700c40070044003414081e0707038103a29540b078141c0344e90002c014036003014108403040300b4249540e4600d5801d0ba030380c0c03888440401c00d4031007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 120668597 1250 120667347 120667369
    0x604030c03091d01030209090607050a0f020c040c050d0b10050901030e0111070320010b06090904060b0604090609060e06030d0f0203040e0a0f0c0e060a0c0c05040c0302070203330402 80
    0x550031268070030349401c1c2e2000e00f0050b4101c0e402035444e0911034030b92030703001501c0760700841c1c0150104004110042310355100303412824540032148141c804ca0301c0444001000d42c2c0c044212200020b40121b400340401c1428450324414034400c0301d00b08440d800f800070103000c0c0c2c080d441d8114103050361104a0000001d0a41101c0c64000d4080d20180c1c0c0c0d000d09103000340502c02c0d43c0301c0d1044904600c1100c030600d0541440b80d80040c0e00002d01080c180042d8030204074566800034001c50785a511480d9940264807100301900181c003e9460106d4150705180600003180d0746940000d5010130100180302441d203000c1191010b400700d916001110f214008000d0f0305d144903542c410210034880e441040505c400d1540711400c1400311030003e00101d003000320129090341e03418005503400340081080c00e00302c85c000e01184800030320488010f1001650364000808480c0074064100100ea00040c902c41103280501200d807401e0108800169052800c01d41640701e600903400c41c0d19903c0c180c401050540d070701d80c51480303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 120669847 1250 120668597 120668609
    0x3030412050f060a050f04081b07090204150c0f0609080705100f06080f07140f060f090411042102120102070f0c0b04060219031b05030306090f07020604030c0309 71
    0x1040c03109500c0c001c0e58411581201c0c0e02c0c075000c1e0001007455041d01c0d004241c02034000140d07004c1c1940f02c5807100241640901e40c8a001000d01000c80481e4000c03d2004e24001e040c0854016110744c50001200410010003211404002000da144000241848901d08a141d0800d20024a0850518103965248180d120290003441468800d02c05020113070410b0454441000382400001d9a500a040d500d00c140ca6940466030451782c8207000f20180d0803502103000b2001000c1d461484180030104215074003211020b0400c8000080d141024107050040504691703c56000b28501032522010405500080b02101d0440840460481c00d55441c0c5d02000b13940048203008655501c1d05141c203409480040001702d603484500f84002600702e140206807000c540c46900504540d9070000c0303051038a40681e03030b000c8080c0714198009119402e08a800b80121a1290004540d80c1c20603008002a6200007402241c2900a20040007421507000c901d881e00a540740c00c02152044a604d8160342d02101e0350880707 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 120671097 1250 120669847 120669869
    0x51f081302040e06190f0c0c030e01030b06070503040f0b0702130207060b060309030306090912090418081b0625030b0a05040e03040504050a0e0c060d110d06080f1b010e030304 77
    0x40071780f40c0d107a03004502620326200002c0140a0501c10030400380c80c6d54180d03100101e0000604207020034000c464020128805140019440d0541341c00504141c00c4100d0070b44480c0c0c00031505000c0c94540c854020040c181d10070105081002c20f0740068041e482140e0400b07901500800c1510400000b030b0461180640001c1480b6201d1901c2c075030f45603994008448080c1b09801c00b078082000a20042408405041031541c01454042c1900034071016024035903080f0080c580c00215407002c20200d20207428042c0e8400d08401d410041e02905600d411406813481c1c1450a0040300d003000700d1034602002c8444003a83c1001700703480d10880001a2324501c107602040d041403c02000c10983d82c1d02200a105480e001c940400042d2265280c2c1011a20601c00092117548100030158061418001501c014000300f6404207008010b07054600e15034201d103400c4080d080e04c60000b4041014140080105645042c0041a01000d00580a2001401e420000b4140002d80c04031b004152018400c84003d00b68170611 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 120672347 1250 120671097 120671101
    0x2100f0528030515060906090a0e0a020304020a1d07031802040e0115060305010302210a06020c1b06070c0b0c0705040501080d1e170c120f01051f081302040e06 70
    0x40018001d100c8800300c000078504800a040d4908a29244124900241002e0309081402041c4041a402656004d0748079005400008104806d0760040f4800c810035800503072030341094810300c0494582ca4114048008040c0d1100110b03041040c3c40c02c0e80038a032490042191410a03111100080212402031340103801c11141c042180320540101c04061600010a40c095582c3d59088049a03801e0000075400f00307207841131409450380000d4811031610014162401d2a0481d40e031001242d01415201001d60800401c40015046002c8003500b0005c0c151003851801c01d1561b0350b0301030102e050150340d40c92240443d40c0c1901c1c09040150802818001c0c00030011541c450b00303016550660206040006070780402000405040d15490308a94100c903211140c2c0d00040410101c01c0110082000728a14400d0042c0c1911900007580c02e0700030305450224003415414901480998148003011062680b1a005017038030095001450b0755001d4000e0171342580c41c85052000a010f81900c0071510414410102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 120673597 1250 120672347 120672397
    0x5090a0504030f1103090907050424020c010e10080403090b0a050d0f020906070b130b040311060702010203060312031003050706021027110a05040516030b0d02100f05 73
    0x840386009500a803039426035400003040441c0c0c0d21012000c41c41e03481d0000d02880302281440b10b426500308095050850825480b10941c20388002107990003403120003048028507125805005004d140c4c3c0e07007880c0c40001c41c5480000306190075016444081004080c0c0d0006081c9032003044201d01a288501800b6540c400c414402450340e0010606101c600740350100007000c091232482103408150700030301141e050001d10784030a4841400104800c8981c0802a81d01000034006403200d84981c0c07090701c400805082c24030403285080001820007056a03c10414042c4c10783d0300040010100c00f6981c145aa00c1d6550344000c40c014a040d40b00411030300c210180861000d801290041c140c006940c030410080300c1a00d41c030502d9000325400340260242071000c1c0008100105141000305202034401d08900d60b88202181c1202c40460b450b40d10700d80c1c025001c42c2003035803500551150280c116200d01404030560002814488550001710a218501204040d2a80910282e80c1c0628115900b0200804004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 120674847 1250 120673597 120673601
    0x3170c041d180d0201090326010608070e03101410080304120510060905010e07170703050a090b09061503011506050a2606130c0c030e010c0b15090702060415050a0605090a 75
    0x86e004a0201c2c61040308210503d85450707181801c011241c0c5826201c0e440c019054805400103860032003000240d040d803e250b514100489041030994440004465810f20100701401002a00443c0c04460a001c01c201d0f00c040001a103059400b4818040c49103c0245030880c50500f41c0030a403415581401030000350381802d076006074100c542ea540d041180790f0b9400d9040b20392014410071688100c4004001c80c0c0000c1c0329900160b07014005402c0041c1c0307402d02c5e440700c0c0c01c0102c040306c0a068681c085030400c0f07011205501c000903011004d90003800000c0851200ca40c1e11803c5010b50400c110000c14a800c1c90352240554180d0304200103c0304c0b008101640c0c2040c59004c0480701a40143d502042d00c0601118901c5091141c8506e50b580c05640d900326501200c110720080f0a040c10000380e5103a24020440100525014043c0d02240f400d0440140303060120801b40100801d003950484010080807031002070300d640b042c140b81c1c079000640c4d54890000c10300a00464000580004946e0100300c0c81c0c1d012a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 120676097 1250 120674847 120674861
    0x90b130e0405060601031d0d0c08040305160512010e06040f0318090504020103050c090102060612071706100801020403080a0305130812150901080a0f0510020703170c041d180d0201 79
    0x307036800e11403074180900001c903005019088580541c2302409181b071040c826003450089038850f02a4034605962074a4140c6040111110750001e41d1040d44100228176084070401611030340700009201c41c1c4a0071086a071288002000582004d007640031010825218241800310300c0f00c04483d1400c0540c40d40d094038000c00080f03c040740030a03d050003083c500f2118506503003030302005038010502680c415013401143c0b8644418241a442200800b2a040701c1300711280900ca011480144403916245200c4100f6110a601c1031030f25134410841840800c10f0502242c800300c2050a0114854949200c640c1c8030388064003000d84083c0c4046900a14100e22440590081000c5020306080954000130000c040c6d0081c80751400e16030001e6124000109441c1040250714020402c3c1e0b0764500640e4071110a07030303018140071400280304581d85542e07660305501d055081801110701d1410603041803030f86d0b04121040c2200c410601030b60340004400d020381030751070b1102c0c500c0141921412001c0400c00381c0a4603036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 120677347 1250 120676097 120676099
    0x6080601061205060d03030e10050916090606050307080702070803040f050f040506031b0a03061a090106090e0103021e0a1712070f0f051e150c0307090b130e04050606 73
    0x2c040002998510902415006100040101030003c460350307429001085a0f981e90100f40c004c44001c038008444900c0790500c903d002d440940034040d4411215007c0c1c0e0119040f6103041c07460038000748182a4080c003901c0e80440541030201e80c5441e5010141d26116040e4030030b042911001038080360444034500c04004031b0b0820350b4100c1c100300c0c141c0108025141c04407069a09584401038142035000044101e139146103014205100c925102e403a034070103940f400307602c04007c070844c0020b0700201d0a01c0e401c0300d0b0062410b880c0c1001c440b801e284c502001c0c160306200291283c81e80301d401102e2900c28110030080110010178810a0941d81c128900c2d01450502814441d030180d949039940802410080302e0b44590300c1040b44244803c81da441090101e00d40c030083d6020b120b003204c40b0010b44055802a00c04042d11002032150020b0812541d881c40b20042561041c0c1e9030610500c040f540d0807101420a8038050700c0b115498119900d40001000c01c01d9000481c1c20507004c080c04248040800d0365805190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 120678597 1250 120677347 120677357
    0x7030f08180a1506030c080705010807020d020607050a1e031a040204210c05030a030806030105160e09070302091908010e01090b040f03051c0c020105010e070c06020c0a0203010608060106 82
    0x30307500090146440341c028028400360050011480025851491101c00500f4141c2c0000c410b612611a4054440580c004040982c00384805002660f0406e082982c8201d4910051080d05203580d4020345034100500310400b448000f0840302c042c540150300310700041035024031034a082180c3c02401400b408840166501d00c42c503c040700c601605041c02103406880c004400101200400c051402407509501c43c00d4400e5100d0140210f80c655003803180d0100c2900030394482d049410503002305030071940c0190007038000503102d072111511641c21031040000c10f10225030000d0181d454941c150060321494501a90103c0320940aaaa001c040402c0b00c06440700000200708841042d21407608070b0310188405001040341000050004690f03c0d42e28910500c24600141060036040e2066921906d0f01e80c244800f984030f03645490441d909105040c010440c180e420785403424460350240c80799110706800340403143c00140c100d404090401030701c1d00056019008000c03c0d0303551281191198020300444000030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 120679847 1250 120678597 120678601
    0xe060a03030806180f04171305090411030304080a03090803090a090207060b03010509030d0e030f1b0c0306240d020609010c140706031401060801050105120a090f0c0f0603180303091707030f08 84
    0x10070340080c2c40b01c8d034503003c20400b829401d0904108401380e00a200b10796501e0241107a640e541c8003400a00003c0c2102e00c010081541e00c4d10780501282000d0f00500b6444c0d2050000e21803958400100c1b00c120385090000581d50891414074401818000d40101d400d5800e05092291400001008200001e00e442c41000503070041c124050b124401c002d444602450306100c1c03405221508030186010380a024100c5041d014960301281c1071050403110386800c0c0440c80d007142d040701810040d100b0040d00842d22041c04d1011640058000d00074110541d0402500546810400010036001c2010b4007030407085600503903841c2c1004018044514254202c503c40d400000744060252a159043e100145c6549081500c81c1fa203110300c03154010b02c08130549460b100ca841c0451201b48160381a5409094600516420000200c034960803640c410350426150080c10003c40703803010000c1c9405641803030082041041c41c10980001f0a04083c402c1d41c2c448001000d20400d80c01c50269048103400f915041155 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 120681097 1250 120679847 120679883
    0x40e0a0809040c0504080606060313061802011103130b09060d0f2406020706030f0204090f060806070e060d020f0405190503010b120607030f18060f060e060a03030806180f04 76
    0x10f0b0180c1d204411040e40400b021134009d01d007174009103034458000d0100d402c00404640703803c03054914072000c80a246041c01880025542e00c000b070301c5140e249a000440c541205480c442c05030610714480c40042c080d010942c03005503520740e011101d82c460000014081c00c000001010700030705511080355109984441c1140720070303c901c85880d04031030054000d00501c501d0540140d0241891450503001c0175800c10000c2446203c43c440d00503010141d410000e030440c145601b1901d055809480724080c44054000100a90b942c6d00c103e03001002d60040241c2c4032400300958031054003e603000b240d0703c009036154600f12001d03c451044226001140240603014074003041c420b154600c0d4104144030b40010b40002c001a000b900402c40e8250070540026642c1030589009402d4042c59800311802c6440c0c0c0e464041d019251f010f1a03004e01060461140d00d401c00400003207540710703d40300003401d00ca0391500103a01503450b8100c0600d001c500100c04165850050b81c524a1620102d0302125018114030080d280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 120682347 1250 120681097 120681107
    0xc0106090e1c050702060d0504080a020105010e22050f07231c02011803050303011205010e0625030b09040602070b070c030207060c02030f1618020a0f0e040e0a0809040c 74
    0x8400b0701c0b03451a030000070444000b110180d204480036a04a5002c10403801c10308018864244580d000354078180c3c0b5070300710314002425290107038080e02c8680d00310030521841501c0c680c40c4017441e20541c51144010441882c1007402d020031719280440702e0050342c0c000142e4030780003203071115585071044d040d95040c12940c01304101c50303e200000b00b03010b105140002c0c0065010b044560407014028102c0700075141e0325540c6501d5039009030849041e1982e80200310003001002d005038406410407002510382d519090384a901245100c030300801008499a05100156001c0d44c401c1c90440c0b0081c0c0034440503e041d0600ea40a584041d40458888000400040c0d55a01c920100c90705c0d642c0c1903015104c02403504904881d90b1130b03001c0080c0c0e40b502801000080c04034080001d04941740b12003640c010b10600e0300300001007015012850720302e0319004021440d0180d84c41241500700c54558101039070380d0307541c00303000c107000b4600704840803c18031032422090301b030100719005840c1000f000c9400740026901d201e0100c903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 120683453 1106 120682347 120682363
    0x90a050a050c030106050109030b1b0409110a11010203190e0102040b070c0501020c060408060f1803070f0c0906030c170f030a090e010509150909010f020c0106090e 72
    0x380b982400c1c041c4d00000c003404d0074000300036495900c4011900c1401800c0c2c0e4038148802012407103103407901e02070300c0c0a0185201d082040980380c410b404199407044c034101c0081152402d0a050142c414002c176441750100c40e200c2c0d20301c0a4910081c101400864003516403654080c00b01142103040000585002c1d40501344e80c000003441e02002a0614862601c614003801c004c010506c0000000102160894550901e00403150317515008446030445444c03448030540400541070080c8540e116140141c3c5001d20020144141d403002d10008071201440001c1440c03850b408100000001c10881079140c0f5611402d895410f9018007100e4110782c010700c480c0300850320f00c0c28248190320984400d203000d400141c404c90702608014180c400c4c02841040308620400c0c1e004c00080071408290803848806410080c190745840007690828068a12400303408589840d00b03042c0009002c00180c116 = true := by decide +kernel

theorem cover : BRFrame.Cov 120503597 120683453 := by
  have h0 := BRFrame.cov_init 120503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 120503597 ≤ n) (h2 : n < 120683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
