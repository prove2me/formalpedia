-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2923
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:08:42.250648+00:00
-- url     : https://prove2.me/submissions/2789ca2a-23e7-4170-8dea-a4e24bb9a339

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 525539568 ≤ n < 525719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 525540818 1250 525539568 525539591
    0x1409060607032607080f071403060a05060f120606070807111c140637020f030906040201030c0306060c12030204171b0a0f12050106050405180601050f060708030a 71
    0x1d00c0380108030a402084110812031101d401445446d0024500e0308440349a10348000010401c0095105c45905220040041102034a039010202e02510300181443e8580001403800c96044d0443c2c140300e8040c030000804a501410901c04a61b9401d0300038103a80e160240c2520f90344071301001041003d03000009402e4a41c0c004617000d8102e02c81e584114444407020b03415a0401c1d2801d0805031503050440c1c040e80c044c4003081d06410514101103c5800d000c550341d540502d0f201c00a0181500d1081064000010001d0307416001c103445110b05d200740c80810031000a039070110112101c6002d801c000c580030005042c0418000c0061802e901c0f0b442c580945402d84030014080c2d0440c440074001a203501c803120442c03e441e000d0342c080d08294800c2d40d850032594600360350351000c00844d206000c48424001105418880290403401c0030f40300c050418000341c241601c5d002014000102015000d00826002040b185494a0942920900200409e042207440d0300c41150a030701c050601641c26a03689200c0b02c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 525542068 1250 525540818 525540857
    0x80f0c10020c030316020d0c11060405041b080a091509020f030d020d02070503060c030718050d03080a0e0a0201020718020c0105040309050111030f0a0507031701030803060406140906060703 83
    0x1c0c2440042d014503140d0408290241c1e00c1e844001c012010f54000c082c0580303405038082d01400c440758103c1f49040d040d50f010070100c0c240e84141d170401c603005420840391902a840c280000d8040f4030050380c1c1c0c075406649208222040319101070f0010321401c2c0c5081914036907079664102c0c07008140010300e4441c0c100c501100003444d01c1144803003240035801004000300fa00f41c040c040b00c0300801040d80900603a143c0004258800e110040c5510103114110084c44101c02c0200c4142000e410040c0c500c0d9011092424041d002d00c0c8100d40f00c0d000303642400342c825030341100810580b4030284e040e0020100c003800e20351940b10280d6030701c50301c0700c03c44d80c00c1c001d40c1388100d400d0003414040c2d4025212a651300f0300300300c001402107542c04040340590303004202a01c0c0f901d409204441d41e0107000d24005458041c00d03c0c0c11620000f04440b07850090042d40004018000d1080065000c0c62040b9010000b460f903540300c202d01c1500c03002c11240d00c450040c0015005040c044002c107a000c0c4a80740004400418800001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 525543318 1250 525542068 525542077
    0x304063f0c08130b22260c0c1e0411070b0705040e150a08010516030c03060e06060c0109120f02070f0e162a15020403080f0c1002 57
    0x40650020186110644141c8100007001c595490000c2881c6801d0321144028644482c004120b0f0010000044c28044c1c1000311329042180300e400c00c0040f05060038102c0207603004510343e800c8803221200c51904080110100e550841156010b004221040020445d81084101882d0003000110400c0c1400c0d5944e48207001c6012010380140c0e0f00e601140c2420340508800404a4003032040410050006282495000d80d000d41154094003110301c0b00d07000b1a58101c1d0b02c0e4420301c070f25803d1009010443d01c2d100f85200c6c8031800d6940801c04012661000c5058a24600c103140c0300c07800410105045080140c01450041103010002c0f0301d0b21102e9842d040818005098540082c03490706420b04041e45c10300031180200503104900f00001c1c20715120760784460740584101140030110301c500c0350300b0707014a19000d0345a0030b10148141c0c1100013803802c07200d0304107000101e0f505600d494a00d443d991031403007620306070390f04004941e0030510301400c1540c0691240c1e0b000d41080c0300b80144012400d80030b00040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 525544568 1250 525543318 525543407
    0xb0604061802120117100b040b04020403050114160e010c0813030c0311060301031e1407060203070b09010501261c09090e0c060306040f06030b0a0204060909090302030406 75
    0x143d680fa070686941051100c181c00c0340d21001641e40300c0e8062640d00180d91728004051010004908028600140080060ba0036040d000390010800000340310040d400940074139200140d6414a43d5000000c1003a240381808150221700c243d41002c02c42e52084d400c2d204140c0c0b00d48151031030b100c035802400340a0701150340100c80890491500344108200901c3d0102d04c88416a40c5500395415507403080800341e10041c42c0403070803a1110040c400c5c0505128002169171180c0240c440d0a911010001e4980d030003880c0c151500384c040c10200310204014030846040f0f69007000489040e20398141e0301469081c40082c44980c51003074140300040013000d00024541001c1c0d0b51580d032500c5240082c210241c540d103400b100700b40d4200070bc03079103c16221501200c0c0e100004035400150032444080100040a040d0409004d4100050401180c0315280d8024026a40c0c00d46644c448030740d0b610140010380b8030303132400200140c20500c02008504e00620029800717000c102d082040c4050007034a1528424904e0015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 525545818 1250 525544568 525544571
    0xf1b0d0b040c05150703050a0e010c0c0f061d030a0f052404060c0c02130f06080a080d14220320010c090506070305040e04050c030a0b0a14130b06040618 67
    0x4000d1450700d00390402d40d410400310311324104245514040c06034020303903008000707000719080b210480361721812540c0401540312050000d195218041200000c0d101d028500c04900f1011810300c0740d2000d401c86501110000f130041039181c07000e64a5018440d110700d0112118070801d80702500c6a1103030000000b0800302c10340c0342200c6243c24105082030743c5203082c41d2818088841c0703000c3d02507200c07840f0307141c00e03c0804880030406a012546240003810035502c0300303406000d00908101009070480c02041401c480800901224141c20101c0348080e500703544d00022102d0010380d4203014030000406034540c41c001d0a10036217410103d100049036010000c946100b5941d90303411501d0f01f83d008000200500300a0b03c0c000d08198056401070a640720700c0c0190103c11000d10700080c00c1120402401c00b49403001303010381300e0b00a00352500726150700082d6140d6071800c0c28110208100e000e002400e5200740c004c0d500c0203094011540b40c0746403040d4003609140d00107031207000c08a49110750844d100b0002c0d004240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 525547068 1250 525545818 525545843
    0x6040f050f011407050c0f040e0d030b0f1201022106011e1b0311010c03020406020307080705010b151309020a0e040f140c0705011a0117090a02190602010e0f1b0d0b04 73
    0x4203e47c4103c2d00502600c510b242403a015801000000e50581861300f9040c0010a18141030019044580d040745980d0300c66003030b0040303603101081034001c0c0001c20010703018024000c0c4100542d0040d14030449080d40040d400e01d034a2120391702182e01c1000c001e40340f81440e00100c007101074091031120302c010003a404100d40f4406821000c800b489208100c04a519085082c1810044001e450344600301002c1c00e401c801003204014007200303501885d01850002d00d10b1108500b001d0740410075411801e03c110f00707d001038070005600c100900850302182d00c60b0791250351400380741c8108001401d500101c42e01c0f8035034440b002054001a100c442c1d000300f1a240300b243e21204145000c03400e5030a0b00040c941010958480c50f003c1c0e0342c002d1031484403541460441d800507580c103d003181c585080c846001e5848540380d020441e0441207030f103a034029a07039542c0c0203010100c102c81c10250389941c204010041d650105004201b1000f00f001201041080104013290005d0322740c80309201c0c40f07804d59055070354117480074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 525548318 1250 525547068 525547093
    0x31315020a021b0a15140d051605160b090a0f06021b010603110120070f050f030d121a1801061106070215101206060305010b06040f050f01140705 64
    0x20110383c4001c070210314070590b0302400450110303100d600c9108044000c09040c0c15045d40104207120020729040200b50b150314041c104032002d03000075a04030704640c00b5100100e14081c40b4408071000c580d60401c528440c10440e94403540c3c20340000381186450302403408400c00042a84580780c448034020340025845518140440300811055180710240740c0c0b420108000007071200351410310014003400d2050000d404410b4904e03042c08101213000d05402015400f08003c5a45035a1301c05650007a00d0799407503000d49800b815a12045040b201000c1401030180c42004200c40d0096407159000720031204440b01030402050702030300751410610890030200010b01c80a94840d040c0300030205200c00030122410a046c010351615920a00400201360410020303190140301d01441c2c0040141ca94060952a0a07041141c0140010300040310607501b490b00d440c101d07140100903602640c00071008040060710704820400c1c546400041c07141402a03001c02000300128043c060724a981c0100040c0418802c0d14 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 525549568 1250 525548318 525548323
    0x7080409020309061b071e03020114040b0712050606220f0b190503060904140a020d0609030905010e0a05010302090a090e1605030d080f07090503060a200c0c06031315020a02 76
    0x1000d0141c00088203002c200d02086d4903038400f100d1400c6407e503050250103a420100e001d8448442c0100410707401d0f600f0312082210001440b8460407182d40c0d83c9141220200500c0181c1d030080c0c2d50150301100074001c058071624102c502c5420700040104c40b140319955441c1c003207041d40c3e140d0700c40d1b0450500443c94105010283da03803005038480301d2804603d980f03050700010f40c0d0500c006d0f06c082c0280749680b1000b00e071180c040180c0c0e80e000350020620081180d0618050001c2d0160711011400a9202100021194060301c08980c01c032900802c210101418000110001e4004501803030340800001800242854144501410240b040014007440e26920369030340215501640654001d0f0f000e00c03014803007694002074454106142031154071854a5900302103521640503041294540203010500100300741c158040e03c804080340e018101c084400c034164050318020148040000d82117800c9a05a6103400030046921040b11418000d0301d1605855031001c0c0f290340041034583c00e0740010581303041c9404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 525550818 1250 525549568 525549601
    0x50f030114011e150203070b180105010e04030216080d030e1207062f0f0309010212070509011d03030403081e071a0c130e0615030f070e09070807050708040902030906 73
    0x11302d118030742600e00c03820081d81d134468004060000600400450701c900c4854407621240918a80203000c6540c59124142da124811303a812000b45c89a81e00d03414084280d28500e800316416580071b440c603000032030415406403001922400d51401401c00e110400c0c60365001070700b00b0709d0184800055103a00100f45110040c1070015000f42a070054440071101000081100c401c02ca00340034845e01c80d00e681d0310050190203000002c24107180c4240810442d10f0307019000d099054002d0340e900307100e00381010217402e12645520109070981c100f0001840800c0e00d001c001c100700c541983c4c110041406224844040b43c2110300210b402124400c2200110300b0f0700f200190308500680003885ca803c0c448056100700007003500c01c40300108052800240550b545500917240c0280385d074038040e07130b901d010b021050f0b1056003103034000e000ca4110060015581044003542d4820301e400e4541031003035201c642c1d00f60b0319a00800d20032196900200400703da1408940040c6001c0c8100000a2169003020f0198594440b00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 525552068 1250 525550818 525550829
    0xc180604060b0c0c010f09030b0a090c060309080d0b0109080f06040b010e070e150d0f09051216030c02030a12120c0311040b1c0606020708060702070f050f030114011e 73
    0x10702c8000c4203d00007048015080000b401c04903408004490f05070f072445413a41c005442c0301e80000c00c00800104c0c941064515078401ca50003400279842d0034045d0115100320401404000c4103000039280c80017564865860700c3e005040c0b240d1401c3e82c43c040e440c5040110540412190031140500013006291240b1a0140680c04180038161502010050101c0e111001141c49503101106007603a885134401210040e501f001c20511000d04500000c40103051070160443d442d01c12086000e60200b2303181d0950390050b09140b54444840103980301114004903010f41030368076014100707295002408600301c00d81304040d980c0b90310314081010000749088a0450501c4810701d41014510b0007948000004c6409913102d4031181030301d40549684101e0281c3c05040180c2200e4a85440800d00a0700014501f02b1101c00200303c410345e83e6042412610b80d40c480c8901041c00350058018402450511034070140c101c40a40000b034844401e0008088070360080c0c1c0904010381034041049500151100304002410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 525553318 1250 525552068 525552089
    0x4020708070302100902131d0d050a110105130f0302010f2a09030c0911040510112404030e010c0b1006181a03061908010f0501090c08040b06030c18060406 68
    0x100c5801150010307c0014007800b2055503081e04e80300b107450058614803011402011142c0e00703804e009000d40709a01c41302e00d080100345044200060034605000759441070f100058002c41038001e80e9a913551718607174444210191b54031807403600c0c100465881480f04484078601c03201c0c05a00788552034800241ea070403460040006100f000d02c0424058003403142101c009034400103041030140c11500f200d009540129034090240f40b40d500f210759000c1002003d0710011429980e143d200e03259800740300300e1607445882e40c072020800000d012038000c2740620020344042c140101102e01640d80c0d5100a80c0840b9040d014865002c014080d0f02d5200c11080920040210703140c1e0480e040080c202011801403e00a01c25800007001415036182e25801c01c4c40690a642c11101082e12600d07024081e254850f048410b1a15000002401080034000d403510381584e510f440700c058845450700c15022030300500f980d40610603100505455100e4500c442c20782c0d07008016554070342c1085410041036680c00d034014030341c07003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 525554568 1250 525553318 525553331
    0x30c080c0604060204090c051206121504300207030b07090e100f171908160302010e0607031803030b010323060415050102250f08031b01110d09110402070807030210 72
    0x12707180c2c80d0404c0c0d0000d00440d0000003400c0302c0e0421500c1d04815a081c072100802040600081000481c052100e505005181c0101c0645609420460740000b030402c00050340300003070410215558003c1d40360809007070315094158907103901004181a4050301c000ba09490940300400034001d00c038401c40081d065503158020700304028403007980e80d5016034140a01c101840e000b40700401500f40100d07903a921846094484115650074081d000780400311002241c0c0c0250400142e2841c030a101e58040103c4001e0701184803041920110010031691406070b060555410310300b5160111581c49207c8001082e0840c41c0302e2510710203100c240c4c2c81e29070103c0c030b041d001d540e03042c405030380c012038400311601d0603041168003090040038013a07a80c500c0340e0081e124001d01020115100c80040010200441a003581c405400d02c00a41e140c05c030381d000940018510000d110154610340250049210f260240301d0030b9805109450001e41264080c1400700c6090500090385010160107000c40c81c00c1e84400308040125 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 525555818 1250 525554568 525554587
    0x31805031209060615280c050d0c02060a0f141c29090403030b0406030308040b09060108100c0507020a120b09030316030c0c142d0a030c080c0604060204090c05 70
    0x280300c0c050852980ca80c00110714429481b1a0340709010000f6851000c000e001840c003c40030784810f03910170782515580900004618070314002d007494100c10768090203403850700b241c122003211245014440300080100c039002c40c0d240825544003400c001008004089091003000e1202011240201c500040c0d0342541240030360080c0e50f183d052070b41c0d8132095078030307200560700c81ca411401081d504003071303940c002e1400e003001c410301d948407062a00c00c40c0320b00100d688035100c2c00c40d0207603606400d110711003150b0b101c001460882c0d80b01c2d8201c02d20f6540345060040c2040706580c00200b04040e0f81c2c0041508810082c19203040c0040c5005a580242c54640610310f10f04210f0342c140b82c94031080040d403083c503031a01403000016100b0400e582303240b40c11072055241c94103c48051a107039010381068081c101601d110080c0c041107804c80107030f800d0407030707078000d2010f13145503503040d684200d8409050700d00480030b0154200350702c0c06110312031049200d8040140d407107040a0b2800c2c01c481c031807940d1004210b82406652030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 525557068 1250 525555818 525555829
    0x503070b030c0f12060f0d320615040b33070605090d1808070315021315090e01140904140307151805030a050a0318050312090606 57
    0x15100c0d8200300941d00d58410030703425102e20804424030301c0c6490004010f503126040c260340502030b96013204c0014800c0d0204040009101501c1405040440388607074840441c44104d0318918505120100f405500c5103c140150420104480d1100705100c0803180c50341a250510420215640403110684a50005140f548050605105819180c1d2b07000c13190012059400059500d100e034010000e1041e071808040850716100d40510120100c0c50034402d000d070402045020f075085d03403000c03c024030f4000d1075521001003540d01c0c0c0701180d00b1141d0800c1540f0031500071001000240111034002c1d02c0080380301000403c0303c0c5190303216044c02605d06005000305079042501e200c1c0180201c41c10103050701c4a09005a204001c003c0310700680c070000404c0d008120a200d645911290446010480c0541050314011003000129009199070010016404102e0103600540340c1c040c154030f400100c0040c150340313078108180e005200362010751002ca410009500d11042c0303541e0154520024003402e040c2500890f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 525558318 1250 525557068 525557083
    0x30302030f0310030c030302030a0215130b0a151e0501050406170601020111130609090605060a05031504061d1e01050f1f1e03020702010206060f040e0d02160f0503 72
    0x201c07a25000400306503440c035080040030180d5048402415950b0b0380f480c01a690764480c01154026020342d00c03840740c000d46184146480390094003a0b04800d0500d0f642c03410500b03e03000304580042a6940c1c5900b54040c2009100c0000e0401c0300c0e071a0312030240b125459200070495500c45c40c1040707002c1006201d00780e404a480c2c8903060801d500d400e40f070349421005034007400c0e103130700d400c50f00c07110104002d4a4075101e41e004c242110300d9a1101800c441e2035107141e41c244d881c1402480c3e003103403007003184c1d40e6440c0c440c1c80103641c070014292102c9500d01d172072000141030307440f668818904e0b2224405149114840350340c4a68011610040150340d8071115500520000014032800d0301c40d415140c119009a210010415080034490300e004080e200505005003040245a03034012641e40c0117480760110600a108803282240c05800410007551260304105083d942c9034005900b06444203240c445010041010230740104417500603141001d4074030458110202e10ba032111004000d090b0b41001035441c00304004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 525559568 1250 525558318 525558337
    0x10020a15090c14210c040f021b0106150c21020730030e040608010f0504030e03060709030605060402040902161e170304080903122218050a060b13030c0f03030203 71
    0x4056003c2d40035a0107041140f0b02c00300c036401c6406d040041400c91419402003a0b000700d407042746018428010680c40c200c030120700441d8035400315000070050b42c5d27010321861300010b0311448090f40c90b5a82c0b100003182060031000d185016a00c02c08050150900c02520503442103030014418072203c425880d0070141c07407030f050000342c1840200020440341d51180d40041c40030300880340080c001218007481c91002850300b114103900140e0650103480780b92401007070407801850b1a58990502d5829502c480b801040c0290540368019420880041d41c036205002401c403010300000c036455481c6080c1095224002d4402240500da805990750200203600d040780c05c0e000c000000354440e1261b07118a09031100e03128a05030282c0c1881000040c08440600d00b00030208010712044c8014443c0042181c0010b01031103010b900c041c128007942c0c2e014060200d5001907400b45104c0d101140b0555074840c2065140d000004100084052400c10b006208100d001030b0006c20070129529050342c65a10001d443c0d02036502030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 525560818 1250 525559568 525559609
    0x102062d04060b10020a02030f0d12110403020a0e04140607090b13030c0b0c01060b040b030402010c0204090c0914060618011214010e040b070206010803040510020a15090c14 76
    0x2260a00030258400000450f010b03001d140035038110040a0768420070f12204902c6131041030300344008880e022075445451249038650065030301003401c5c0f10010700040f506210b4079010038000000540d80740c00201005000030510756038103050504011102044001c40d9004951007032090280d507607800120340007260696803526854502c0d0744c002e400240003950014000c4001e070000861101480d10080c002524003200030803526589050030011806684075003000c8030b00c14000600594040c241114005200034000107820782655940641110700c2c0d0000e0b80c0381503441c1c5200103104000507890b030708000204e03982070900e0310724007200c00b004040040103030400c69684400101890b194003c1003003039010181030a0b0303079a143c03180710000b40411241a95001a0440416092800404c040c0d05071401d01d000780d4502800d0074140a548540c040400045104089021001c0b0b0a40b0103102d104003144500451500700c00d042c511a800080d411060803002140c81c0754403507030b1b00d6011174004241c1c144c91 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 525562068 1250 525560818 525560821
    0x818190b070c030503040303080618040b01120321060501020d090308180a03060207051005011530020f04030201110610181d0703052e180f050303060102062d 69
    0x10b0070160ba44480e400201a888003050210801d40c0011216101e0f040955000d52f00141d1101c03c10b0b00164180c4000d89040c1015005204000003d100c113911640a4140f05200c1400148040070340d100010903904240d58854003840290ba050000b009141240d14103e1001d50560312211030600c034840440280302010725030700c100c41c0c0301c0040f810011900314400715240e40b054204146c07580640f2480481451421001062030000d507c141c1d484102540e0341c10241880c0518022502094540040298802c1c0c07981c0d140c030122a0700041c90b40c855458030480d100c0d072840c80090141c00000c1002d10454002d0401c01030302d400300301d165004584042c11025861100b11540d100202221800f160440954000101340c000000403144200c80c41881119501c1c200c80055126000c006a400c642c80301541042400c403400d80d800130014010810501d0203203094030340d5480c0d80441e0360601117900317400c04000c0002c65a014080c01e1362005c245149030a120701d0f44015440995400e1405101b141c00450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 525563318 1250 525562068 525562073
    0x302040b090d0f080705012c1005070509190302030d020303070f0507080f0a0305040b010b03191a030304030f050d0e0a06030c03141e011203020c010c0f08070818190b07 74
    0x504a05269412111071170741c4105609125000e82840072851245684222990100741404031211601090381c0020b0b104101c0710000c004082d00002d0024010081c00b4007042e22030f541c600c40e00b1250041400001c00076140303144141400c0a44000040c42550004e00c1008451a0044692840000d031031814517919410307460705041c180103000d00b00e0400100801c0828803241c141e40b117580218003ca41c0c0c0d448984e69600d00c8050361108448d0101110b102050403c0030b110a900701c03201c20000f07051144c02c00d668400100f861500980d2084d00c1c010010703452942801828070421018501e03518009941c40d1074000405d000d502d8a206040c1016039a45200ba020761283d4801035109030130802419582c20403202042680003404e04100c2e210301c47c06c0001540d41017103c82d4204003a410780140c43c1c0a1640401034595110070141655800310300455040080c00341d0005021282c405c40400351a1280100e00180c644c4200c3d40403030050b05103c001044056508070507008441d01203254554503529032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 525564568 1250 525563318 525563333
    0x30809010608060a0506120d0f0e12060a0c170f040b0a0e0a0809100201020304021302070f1a100b0309210c011a0108100e0a0b040209060d0911010302040b090d 70
    0x1035110030202d029003003e00a01134603170b801c003500404044801030089004814520348800700e41c00c0102c00302d1403040010352854003c4140c0b90541c10300503d000307580d00c0c04060391410840211591300c003caa0b5054400141600300d0340d007001001b0916184a4203161078075060101c9280035101401040f01000012402e003920342101943c20300020580b43c4511007464080e40300d030401c2903007900c01c010403540c44d0192441403096920490f001400c860689a44c29400d4000b544007040640e60b001c040b40d0b0703802c04281c024003204100b07005075080c0111450103070b00c00543c070702054202001000040090142e00c41000072001480c0d10303604400500b4200301c04880540740f28462030143c03a9424080c41c001035900d2682c0c490b050030310030b0f2101b00555a42d201520002174a038002c0c030400c1c0f1031007800324182200ca640907041c020784c050701c01450710300c0302c80c0024925049520324004940d1902e6840d010410320b4810744030303001002c0c28194202420688100210700803910102e00a41e02d45500070180502e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 525565818 1250 525564568 525564581
    0x105040e0a0f1106220509010b12010b0c070b070308040b1312110c1002070e1308070305070614040501050402011e0e01030e030d050f0f01050d110904030e090106020a05100207030c03080901 83
    0x500003000f010700e1928a40110a804506c5824030135000d030b4000158800c00c10003114200e1041807058000fa070300b01111207000d50010401c1d025103105003100840c81100b9000100b20b4140a0f8680c0c481901e400e1800e44480321005200081c00d0030801e01040c0040ca6034041c050403030126082c10402d40742c113100c1240c944141601403a0380008006110000d0940100c2d601080d248040840c80203a1769403011521820445400140300c0d42c0100620804a4030600c00340c030140303100710030126982b14105040f940f841e1042d1015511650b61700103100840da04501070400c2c0b0942c400001c00038a401b501c02415501c3c03a001260306140e1500d03156100e613103040c001c4030b1201011480801c034604100041e860740c41d1080710b00c1d00303001c0403034800441c1604e0000d0704c1038085d0341d210340640c108151034000d00403a41e81c00b030070071410b005044829000d00d507164a00d0a029280b140d00508804045003816440d0001c0d003d040010184100310360004a0740c440c0030804095010b04000c0381c0d076200c40301c807540107018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 525567068 1250 525565818 525565837
    0x5090420040617150604120c0902030415054609080c120c1b030109050d030510090e060105010e03100c0801031103160e060604090e03030105040e0a0f1106 68
    0x400040c0801c089403c2072500c04115802d00600145a50364000d04014030407801580d5405401444100b1894102c3c00801c06018868880d6040c0301e503444d001e04007680c01c141c81c1211043c8941030249c804041611603203600440c41c0c02084103185115403a2074500c4030582c50b10845407603403140500040d00900c0a407041e00503421041051541c14182102c0c40e0b00180d1300003055011b81c031044500d40780c0d044141c500307051005000d00700072018044407000b41c0d0108400d5903055500d80000303802040307041c071500e00ea005c0b40d03890119851800300c01c0c039510040950400303c401440c1c0954400810000030b803090656000b03080484030065040c001902e00075a286070041658140030000b50440d80c0442ca0b01c1c100c0b4899040d0854101c0c0d0b590030180c59407074140c0c2c0804030407619202000340c0c0d4418081e4582052015110600d0140c03520b000500790740701e0714235107203082e07000000401c07140c1403610410340d80e000c50002030314220b2140e90300e07180d240018030009441031030030f500c03140701d996078440840d81d2104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 525568318 1250 525567068 525567131
    0x403081e060f040b09010b0405151903050601030b030d020d091505040b0a030914010e0106090e031210180b0f0301090b0f040c1203021e071d04060e01050c1c0606050904 74
    0x40c7d40d41c9080c0400d60082c042c060081c11154500550b407501542a6020b5060341c400512440c42d90000c120014800140401e04041c2c440e041d014490700c0070302100b0002c014540c0a4003203e220b60070b0280c42006281e0109a24411012080ca9030b0356100050710161030341c2001d00c50b500c040007001280600004107018103444400804190a400150702c4081c40c40d42040080c403255544d03150705411035403080311080580c2c008001e903a43c050319038150395078000c941c1c448103513600352141411410310000308404600c00303644690b0b0000b00e18044846900c408800c4009001c04502580c07031a41045003d800d040300e28a4840124080210240e2590040c14441030381c801505c9040c14020340e285110307a01d06c001d040001d0424600c0c050003054440c20790b250150441019040d03e08103410a030030040040d100269103e84040c02840280102401000e1030144c841d1142c01c0c401000e80c02c5880030841c040d030301e403401904010480e001030964050341c0044034001500c0003103128a606200c441407041365000b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 525569568 1250 525568318 525568321
    0x12080c010e070611064503120903030412210f02030a0524011b0b0115020607030e0c04020304020402130312030e300403050d05030403081e060f040b09 66
    0x340c0000b2000d0440c1c9455540c101030188800d001612007105070749505003680b0300ea90180c2504c5036009080720702010700c0d003100181034004240c8100401300d820240c0441d08001038078204c1c454181050390f00441c1d100040d40c80c50620790f484154034200740c4a550203218074107130414400003034201c8400c54000c03001020b204421503000b00100a40c4112200000310745000081410310080f03a64248551001458900b1040310280054800712109041400f02c5083c084458000404205900c3d009200716200d003040640722100c0a030030700c035005214604043c43c058250b40300050008038480c2d91181990016520703150703400891302034031078100480710a8980c400000100f0401090800201810756020464080d1401c0d5403030b281c01a040c1d00009110320f500542c0c04040c481e00f19007100a079280e02c01858540c2e650343e01d41c2010000901a00441c001004010034941c220a00ca46d1280e125480c04400f41c06003448800007107005448680155400c103111980340d1207a90150800c05001440850706 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 525570818 1250 525569568 525569591
    0x402030f0f031902160603020f070c0906080d11060a090f08030f06040f0b0901090f060e040c0e0a0209090f06010306080312090d03020333150901091e12080c01 70
    0x282e91202e5551a50f83e82c11040a0b80c0043c404a14444094020400d000d6150300d00700045019401881e400788409030308120300c034005803032072540000070700321001d020410303a24104046082c15001c500000034448080c8010041030404a041a0711400018000602c890581050080d400d0b6880c0001e00701c1000105022189012092680c07240c4030031a4280041c80024400c5000e9071306654806802801e000b00510056405400103011000c044000088030f03591101da20102c02d40648042d100041c0040017800004c0902078400d6105051a9007989032220307100200d035455500809a900104105002c1111a0b109400c02d00041400208603619003804110f8161510000d48a10450740f060103820a0418000e00035a031040c607030501ca80c1032a42c0640700000c5a0500c440c0440c01c44407100c0e07030300c54942da07a40c010b0706000c1c90111101c81d240c402e11b40c0090b01d180e48c15005000701460444012807480b4420032082c05803000d40c07206940c520028a45031405008141c40300555500301a441e440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 525572068 1250 525570818 525570823
    0x30d020d090c050f010215091c1206050d0b0c030a0b03060106020f1009030503130f0b0c09091807150314090a0218070e2b0b0603010b040608150402030f0f 68
    0x103060055280794092582c034000c000204d05080c291902580203200c2c142601c2c40800303503443c1c3c420341c00c20036223560030405c5001c840b41c120040340d1a004690703814a0817a00d480217101f1240500425220003003508159121305c98120002008004c036030318000300013980d00d01e20340c03c0f022100101038102c507020350b1541000713034440020000c03030312291140380c43c8415200c884e4040d0602054140c2c40d45803450f01c80d6480318031421140c1d001a030b0140001100000000d0401240e20f01c9100341c0d0b40d090761525401010000c2c0c500d40a812580701c1940c00c2a5025402c00c0840c6401c110f40c000300b40c131401c5076400d03d0242c024000c284007000c3c2040d002010485803c0000c1580d0031100c0c400c5504840402c42c000440301d04c81810790780e010000d01704041401c03603814007001e1168070b08031040c0340b040c818448900711407000030f0155003250030383e11203414010242000d0091242401080300c0521003141000c40d0980d07500d095200680341c00b54100c02080c15500e083c4035020b11001d4010588603c00254100c46a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 525573318 1250 525572068 525572081
    0x32d021201140f1506070f2604141005130e0718030609032d18150c060c09180207020a0e0c031501030c05120907260c0109050120030d020d 61
    0x240940600504c41ca15150110031a11803a6201410781e4520940d626881c046003400c1c40c1030f40c598401e0000c06011800c841001d0f000901d45986241d070240d0904051003400c0800701884810310405100c1107860b00d5503152544250307111394014441c56501c03124111880b8006007100c0703c10702282c250110504c0034039000508864001e03121580403200140109021503880c0f58030402403508a4401d03020f00d80309aa10444520000f14007410550311410304145000d00400309401140b50004400d08224241c01554114841424484145441d0003220050780f103c01700115105540013940a086548865104002c0c0000242d000e605190084c940d8156620a07250200101401c50f0302c02e0f41c40d031003405084142c2130103648050404494421041002102803d420200c1c0202c040110388100e1071180c40c000c600c00e102462890b50105803a0f04e0807c0502440c1d28108244a402440b1a98000c21039a016260340300001c0c80d23403d1004149030442c050720700c4101c0d03524000942124031400c1c036000135 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 525574568 1250 525573318 525573331
    0x30316030213140f18040b0403140c0109020a0b19050705010f0203010f061e050d05100302120309040e0c15070f0c091a01032901140d06032d021201140f 67
    0x549658404104124036411016407070440c00c0121400600010b81403080660814840d051074407000d84c0c42c03980d645081d08440c818201983d374402c4270609500c0d1419000b8000d146a00c0b94500e0402c688021410500707124511400341300c0006244d4003084000d5018907409000030104544958440b4103440700d9070b106100745000203901e1b240420040001c500311140780b00035522030300c1c6820740e0703c844840603090007002c82c0d0020852090000250b15415006007884105030041c41c0e0300c009000c2040220707516101c50a0b02d550048458608030313111502d00b6200d00003519030b00f40d00c4201c50f2403c860114500403004040d1a001d140c00642450030b0303004140130500c4880380d050b82e1228407004604845101044242100c4c0c101441c9080e4052800d101003641c60614000391040030103c1c5100c00750380f00c2010491300c0341d036441c1c1c20406e0000258420780a20500850700910004920304152080310300384c00607100308c0703a811b11051010340035409029520102c4040482c10300c1c140d00503519410044410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 525575818 1250 525574568 525574579
    0xe0c1903020c0d1b06060b1b010e1504020d1202100b062a030d02030108060a050f040c03120e0306192f090f0306040804030c0509010803031603021314 66
    0xa001094068000c0d0350803412503a004081040305142c040310303900d6503480812140c4100c02560004100c035402040007801100000960312880d00d8120034000c0e04040300c410442e4905082030302e62031404a106a580800746908190a481d1400010342002d0490801032940740c4d101d070900a0150046400c0c028256038603400c0200010090510000d4859001031a0b9541c5041018801d80c180d0b000c4050380e580201c404481c100513501e09000c1c126070082e0013198465028a0070002111080d02410754400c240105007991303410b00b030b42e03944d21a10745030000400300c1350421190901c035441501d4a0b84110340c014100c40701400c01e0110799407a491a90b5506540c1d5081ca05041c04440500d60350001e003805c1070304010200300c81600c100001c5c0c0c0004a0896001e03407113211141c4507603002c000107401940a18261903940e40741d03152a50321800c0c2c2d5840345000d100b080740108aa1200442079035404903c1080440b428458124110024401e005600e030700c50420210114510040c020003242904c019280c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 525577068 1250 525575818 525575857
    0x60112021c0809120c0a031a01090b1815100f0f0219021201020708070b090f0d080a0e07350303042303070215070b070f090501030e070e0c 61
    0x241408205103220000d080b05200f0460b041d03140c146144007040d240159016150007042080004060b500103500070344a44052031801d40c2d105051a903001c0c0102040b03c010064a200140482c603c040701c0c05000c0400740ca6040050320b20280700c141c51f590464020080c50a00800c0710020b0a01e1400040d0080040d060030b03d00e42040d400090080d540d0300116140c00340980c0c0e1982003159560204a403030149540912403000050500310207414000d06c1840041c82506c1c14402091a01ca02822a101d9590080c6c00e8040c895070001c4c505900100094404560440d403074010744c0c030308500f0368041c800010125100102841c07000c101c0c6031241144850203c103c210b95650245e807404140ea0140c400908010301c0000119039081d20086e8a0b154400c1d01c0c2014140c4d000240040500309810f0502180044c5500410602c8009654401c03c01d080032a42c890842c003009240c0300361f80c0035040c14142d5600030212807890800a042c010201040300441390b1410101c40403160700801c80c1c0c80c00c500241076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 525578318 1250 525577068 525577099
    0x40f06060b19172703190c030f0801030209040803090f0f010f0b010c050d05071a1006030b10120e0a05030c010204081207080a03022a0a121106010b031806011202 71
    0x4500f80c01031810f08050300192a8003481090220f0240e08100d016100410090f8920950340c42c1d4100010001d0712445404801424094074051582e407001041200e91001880180c0d2000c19058109410851182d101e5482a08141c40c004c0ca054011296100c0c403d46254411700c1504200907801c4030310800c1c00600214030040d54a080b84080003000398010131400c50700c49100d0000351221500505542c804001d07100a40c200640b820b0b82c07045564143c13080103028054050140c1103807000151544c402000c0e90701e00082401e9802c0c459151056200c40e03419188150410155a8442e0420203a07503403810180c95a6000f0341c4644101c1040e40a003104042030a20030b01c040e240741c00e4200074024904940030b9401c6000754007010745218140118040f00f0401007175100018484407082000780745000e010b09100d1105010300050340c0400074182c03082418004003083c05030450740e440010903100d03100d08100c513403980152039248089100e94030000801d0110004010a514001d65154544040d0342 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 525579568 1250 525578318 525578357
    0x20f0a0308090913020a1503060b040e0718090f0504020306091c0302130e01030b1e010b0a0305060d020415060311090d12020a0c08010c020f07060206040f06060b19 72
    0x40c40081c107420390500c40c20b0300904140d060607602035070314110385640340079580c005a0041071b250031003045403a240303c1005015400d80700300e03400761500c10384046c107040c40e01c0c21100408000409000c10030039156000e151756189115600050401247c090004c5e1000411020041800300c030180d00c64418000804c918110208030b00d03032849401441c21003c4c04440d8000d070040c0d03002c011f0198000d0f515000001702ca40c001c050707d0b03028520410b03992007541041891000d00c207900c40b4088100c2c80c0c402d00100000d40600c41220203400450a01061f159a00c4000440c100040f00c80650003a041c80c8010310068054020401070f20440d480400c03039405042e210441c6401000314442d00600d04081c8500458289608419001c6a500c100d80204080786d071009140216a4020901691503910400b005234042c4a18180380d80080300034200341d4175240000b540d9000c040e00107000001d144000340f042c0b1404e0307044000588900308c18655690400302d1070a04010b00e0111080010742c0c038820061203203c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 525580818 1250 525579568 525579589
    0xb070c0212063d0e1e192a0f0509030604030309020a08010b0105070b04020f030a11010e030307120809101505042706020f0c0712020a0b0f030112150e060103020f 71
    0x1d07500701030000c0c03c259184040c0003000e49221080140011000c6501d461240c1305071081480784000742030a188541c00c1c50a65400c02000c81032020710b2901b0f087e0b081c0b0544000c00008020341344c101440c06001d4801d40d01b600c5003100d0150103001d150200028181c041d001707415941d10039103075207035040e40d80c242280c00c980701d140441b400190304202c0e000100381c0da030b00c0da03c0d08035000800c48030b044040100024a4070141890840d00f80302241e80c0307542a50b80008110300c60f01400e030051840d100069442c2502e003981900403105010710280072840a503000c0006c4001c1065a060402c5a59170b0399048800071280d610070148907a04090a00d06600c1c003051200568800c1e42c2d159001c100c0072903440401079040040050600740e010b0001030501c00003008540018070b070210300001c58401e0b41c0180658401d403508200010017003000b9441c04080c6c4441102e04640c1c800030640b0000c205490800040d800107100000030504000200c042800e001c141c96048a2088690034a00d405504c00d0104040c030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 525582068 1250 525580818 525580921
    0x60f19091d0d1d0f0109120309150203090f090709051504080106060903120f1b081201050603070503070c030e0a0608101a0405040f020c010c02030d050a090b070c021206 74
    0x128000d43c0b049038100580703101c039500d80c141030001c0c807141c40b46800d00080542c10800d8000492501c020443d0030900303101c400345036066101445c03030011030030045084600c040107854010f821203c00218050302c00e608001c0500b03001414042a4041080403030315540250007000aa5460200005506070140d803a03602140e60000d10402d4804007000180c032904101015003060200059019442e03684015805100030300c0b482c2500c1c0c4a00380d021207070025103070580129010304410018030502c2900901541c0c1d00c03140900e003076000d4400c1d42c5021942d25000d401c8840e0462414040402c1c4250031040a0b44035100307002000c0700060741d40f0200382044444809850722400c080000340414103054025100c0041010f0000d40b17041d03010b800c9242154016464100140c102140340e031112001030003101e0b0032114501080c48040e0f41900d0300345241801600e10001d0003e0303208084210348030703408400500e183e040b0641b020751070305000100f1081e03484051720081080e070508410150000c0d100011003601c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 525583318 1250 525582068 525582107
    0x13051008010308032707030b220212010f09030c14070302100e0307030f060606081008030a05030a0e06090105060a0b03090601060e03191b0e060f19091d0d 68
    0xb46940c454030f603160700292449245038511951201c21403200046030300ea4030703418002400000c1c41d5007020350242c1c0c0c020309200c0d203002414180006070351503455480569501283d14101e5248180c29140c010910b5003000c01985003403002a105064000d4000c209042c041c0d240580c1703130b5020810564440026001c001d6000d40344141c2c4896040c42007407035800c0c0410150440300c80c07544076103403800c02612840c422a040368070740c00c0900039513902000c015000045038401780c8900d410f240505403030b8010301200c0000c0260200000b80516490b81040414450501c107494039401e11030900c0780030341000c4078118011201400c000542000301c1c000c580c4130705c024134041c1c2826400c2c5102118854103c94145615215205580150208480303101c0b5000d0b1151103002042a1500480d2848141a070300001c440c954001c1040120b8482242c1e8404d034060894120b10b80800b000d14400130030381c0c02d030000148103123031104c40e022403d9020318040d410184202200c0d01c040c140d00c811110541c50142158014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 525584568 1250 525583318 525583321
    0x40b04140a0e1501080304140613091a0622080c090411010e0a09020d2a0c2102010207060e03092202070b0f041a1308070615060513051008 61
    0x182825800b1682403141076042d1802000c103840d400b216200301307801c100c0041e00000b8007007108105180584003581c030140c4a20f41021480c40c5119000c1c2040e00c102102d00740c844080011004080c01c0c0d10130310140040010f610359980140b0211482c0250482055010f1001000f044042e000561b1100310342e0000d1803d13100d66182d40e1600403c00e10b00208078180110074030500d4a07079544075800c1014003000800140ca40c2c503000480000c2d0b440100803103a814a02d84814406080203400c20400142c00b03081c034010294151600000c106035149200740c1003020a80070f141640d5040d0002e141443c01a041488100440201191a4400c10808941c8111034441401c50b03446a4a40b00400b02c1d140ba000500b0480701c1c0d1a038500c041c0c0105c80410340119071404104c1003142440d404070360300c0c10a00650b0381a2401d600f0150004802c3d200c05010428046013903000c02085801103000c0b40540f000001600d607840e50050455001049003080c08020b62101144070b02f400140da0085118555401806 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 525585818 1250 525584568 525584581
    0x6091e05130f020a091e0b0607020607081b03042d08061306020c06011719031d0a0314010b09010e0702030d0209011125060311370e040b0414 62
    0x24000c51100304d8110b45001c030700042110082c82481c0c01c3c0c0385a41c208000d400d00310026201103078004501c40e4801d04090180b41d015883d0002502da1095004508030f50300c110b4801030720100100c1005071000c0d48000200850100303102c0a02c514003450503003400306c070054030721032100c140c2c4441d0055400710342c001e000284000350350365078440c0107230301070b0100501c0d00d0400204035003003a000b40c00c6071303110741c0844158451204080040403440449801350404a0441c2e64009101c040c40312520002e802e01000c1d0502d0581d150920300c0011903110380c4142038241d401088034043e000760769038680300d5000080001010740d410344109102ea400c40d0b010303500e030142807502100290445400c8904103d03288004001c0c411040001c00300c003507076090045407000c40940486644500c190449002c0604005550a20442e000240c4464458510784e400c2c010800309240c00710510003404581c680c0b40c00048500b070305d68200907800f8914070140d0b010b10544000005100030b80b01e9000c00220710040d0400003c0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 525587068 1250 525585818 525585833
    0x908070b0c0d061221020d1d04151505040e0613060b0703091403011514011707050c1c05030402190b070b1e0907030b04051006091e0513 60
    0x1d00c02009890541040004541401219400d81001581301d4828000300280000e000c00e01407011107070340800c0844010480b000303450b070a50500d11024841d02d000c008880843c064090408801d02610804c0ba161943d0b03900d8200003914801e40146426104000ea00300e4424400c560980d903810502e0201d0b911404c00780295905e0710b6482c4000d095840c40b0101d100760068004100b070302d009039101a01d050421941140754841c448226120342c2c54002000c440c2000030001c178044960543c50048400728074070040c0c60000005c8509010300c8083d20401c24015040009070244a0f000401c8541d400c080e400c08003041696804180c002c40c00c240000380043c503003404004410480000100c0d55036548040c45410340e00700c0744046072440c1890040168404100c6911a40510b40c00e2819a00d8107101100d603840394004e0001030500304000c40003c00348034007001415601c0341c00400030040c00e070f51000110700030000170041d20124031680c00242c0002080e401403601616400303070420121170540e03482d000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 525588318 1250 525587068 525587071
    0xe0a0b0606030f07121128050408100b1216031a0c040b0d1b090e0a05060607200a0b0304050d0207050f13060b030112021005070b070e032118040908070b 67
    0x85081e031101c40d55001182004042d1612242d04054030417400c1507c605000301c0007001c0b9484c2c081284c02e1004003e00900001c490580c0d151001002610701415004505140c10241c510026485070444400410456040100489018800c61120340c0c9200c5060f0840e114269862041d1007400c0c0814012810080c0052882c0f03000104006000000196101821041c0004000100d03a880c0001c0140034621188075501c218000c10070041e0380f424a001031440c0c024a50090140c860704180c0d00c111030100300e912101c041e07000f46004540e42c0d80c1e086c0829158030403101202c081c02104004401940006a46425240002c204000110022003840640c80c030300303105c00c04031175183d10001469403110002903019100d0304078020103141d210300501c002d640d00000d450040110400c0b40340041000c28004c3c0e80c00440c1881c00811400700400002d190911203603c00c1c0745022000c068940001c44000208109107540d0085061940402c00700011581c003100003a184100400401000403016500303203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 525589568 1250 525588318 525588347
    0x106080702101109030709021b0a0c260a050c01030b0d0b04080d0618020301080111070503040509340305010504140a050c0c060109020702040612030c14100e0a0b0606030f07 76
    0x5820b00403004d0000c0e00d845010b0b0310210b0101c0c0e0016145416040c080340350100005003400400688005035164085015503104806458400c101030802000c50008903601d80720202003100c010004a040c903544461025607050301013841d110710340c801c0d070500503801c180c0039070000808441a41ca54a40b1200c03075000c0c4d0b441203403c80d501d060114283c0481a107044202c8548030005803650305019140c0d003103840c41d40312183c480c1402d200e43c0c0002200007080740c06543e01a5200c40f465100d007185089511f424600b03003c0d4006010f402504103441322151812000381907602880140d03038400070700c0200c2e02d05000d03c0fa9240e0360280003070181340d01078120542085c0d81d24540e0b0f04e0005510109802c2c444203070050515181c0008964041d45003034041d480107810307250ad20b1010504141d402400c2c462110f4001040c0542d01d84000e07803c0c00092110b40030205d040c0a042c040651301840345030700d4a40d402d000303d07151401040407030400d082c48000d40380300d04000003400c640c545422500313840642c0521500c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 525590818 1250 525589568 525589601
    0x70c09150302132021100f090905010209130507181d04141c02010c080606031801060f140916080408031003050a030f120b1c0f1b0e010608070210 64
    0x80c815090a14002848070304458440611180205240c4040302c1c0800303020141440b00c048007e002d00e00910341031604860100130005609102e5141081c0a0701500240c241d200720200d0601c0700c450702c1500914801d064955a045142c828162101d5060000e0300a592030b042c65640c688000020400060340c226004002e8481c010088080d80c40c80d00c80886002c902c0c400d0703030700e406544041c1c09009400443c04903040114103440d12001043c40d9020083c485902180310309103410380d1850030f40c030481c043c0074000010806627456540c5080d42400c01d01003203000361401000030304507c08011410f200c4085545d1060116121500e4561f00d6400152110000c020030a000000141041000303019039446615400314072200058080c080c01c0d6440e40111040d818909003260986d0740e41c41451240701c9880091111110354208902036071302d0540010590b031185010354141140e15294101212110002c0d00c13084d03030b01e50408450040d4140c8141001d40d002e9181e02c00318500940181d003051003c4040d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 525592068 1250 525590818 525590861
    0x10309061103070f110d080708042102011a06040302060301030f15020309011e0c0206070f020102090d11090106050f09150903030a12060f0810110f070c0915030213 72
    0x341c101095006403000c00100c0c41d80c80c0200d540302d4000308605044444500903200c6511074007409003c084c0018061820421000006410840f40d8150109008038206640b0291441c41001900038480c80303006064040303a80b00c6d8a2180c2c0f409070300f1141940d5020b0700060440c1d1842d03580c14224028010115101d0b04002e00500210000744051803180f4940d00c000304461414161008048407503940401c001802e09030300c2070145400281d82500038480b0f180c03641403034a507039604a0090007601300069100c0401c42e03054050004420404050000444107150140d90780c00e01502c49100720250034640000034810b1240603c0c001078480903001d010381e40d1602d8908000006411540510000000700b00944140000d8400900c0b07404090401c03904c1300103200703040003007041d030312003407a01d00d40003040c1c84298183d50002d0607400c2d0388450b40d81d098403507100e240920300821044501d01590000034545525000780410b51150700d400c40390050852282c440108588001030051103082448403844a403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 525593318 1250 525592068 525592091
    0xa17030f1803030c030403060f09082a010903110f030408070314010f0612050105180c040b0d140f1002040501090902220b041a03040825021306051309080901030906 72
    0x402001340084c0e01303000c0d59440c1d081d031400c07000b1558070580c1c010100c0c1c03904110200099000085079111120042407500d91000a901a5110207450300035008035420b1107001c03010150022040b8680526420a0380c84024070000130f1036503401a413007160785640c400c0300100082407600020717000c18003080d80041908079401d8001420b4401070303403015100b1060303d4540d00c03d00c00288110f5801003e40e91000040c0d400e2882829030300c4c036006c40c1d4544569503c112142c17050317071101100700c1380700d92084801611540d841111034440710440001c103810b010740441d000010246200321425104140c581d41721040c240613201000b500305001509078203c040045ca220b03e8400001840104041381e4050707603d5041c1240040310006c84242e21080c61028014000040d002da0192402c6034004540700c03102e494100c4848145074640d80c0040d40107c00c404034032440b850b1940058045d00c9007510181840161074103c4400c80d070540401401c40101404817807420340c03017908401c0d0f4031405010045041d01c600b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 525594568 1250 525593318 525593323
    0x303082508041118010506160f05010b0102101119051e0c070501032f071a1501050310062111070b060a4505060a17030f1803 55
    0x22440040481e00c607504000800148185040d04483d081da90006901520310405103400418040d461040f81c02080070f55003030f14035590141d41e940e0860284900318a00741003c0c0e00030500910124018000c488600d400c405140c06503405110005004900e80540b4074407100321100c0d41090001082000c00500e40d000103868074940c3d4511600382c0440e511581c00403040d1a2080c180e200c5818503007071100c0d09040d13000442c41c4c404059005205000300c4c0300d081a281606129040d0020490000028034450f50a18200b02501c40d01e8800c4500314104650f000645042c0011611104903003a01041803007594030405916402c071200c1d914504518079010108000d5503243c08a100103032601003030b108180180000d5090704564240c0d0000c209504004080c81e089511510500c0742c03c0342040580c20320014440c000010341d4005594151075482c1d40800c1e00941800e450307051260f01110f1010440200385400c000c05c114074039009610340320001c2c003d4100b903000305404c00890b20502c0c46841498506 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 525595818 1250 525594568 525594631
    0xb190902090f0106230405130902060d02132301030c1b080309070b040f030803040c2c1b0a030506030c0307150809030f030a020313050304121a060a030308 68
    0x103290240400c0d41c1402402000d07a80c45051030401080c0e100c40c421041c0c5c2440d0b04036001e4a0003030340d000580091841403007014081d0309030025001940080c00600d83c1290368090a0702c0d65008040c6c0340c0b0107030350300303610403003941ca04034100040c540091008505602a40c4519081e07030351030510716010243c99800042819121405513074941000040111555041c05104090010700f4011420541000c003000c00b0183c29000003801c65400101040034040c040c1c501c4802040344031000c00c002180b8420706003140e038400d880030b54404004408500c0109084c13201011205040881a040540111080740580b00107450780746c150080d40002001074a09000d0b143c050403102030020ba0002a0580050030b90600900341c0003170750400d00c0b04241b1a020f040c1100d820404078000503840343c8408400742d403070803000140100076210019000840711101c01521005500178a0320442030521100c0c00c0036122000c90304a03501602500061000074010f14146800c51040140103001400051035001c02d441c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 525597068 1250 525595818 525595831
    0x5090f12010203070e03100509150403120908041401090b2703011d16030f110f0d120909060f05150c0607090528060809100212041407030b19090209 65
    0x1030003090b013a507400e080101c0c00b1f000c4c0780e0303038002c100c0b52400d42501915101c2515440c1440c1d1303071010125090611940224038207030300248042090303826600e0320940e2035200c0d1055440024a01510102540c0070700ea0150840350b041800e20725240c40040903080c2c05030b044240903000c000700b204401843c0c5003445148046602200340c11b081202c02c009092528090201510600b02529414000608100c088005996006940078141d000300c800081c040c0d2180000f0340d80201c030050124040c00004580d1101d503a40c2070300c440350941c0e1200b140300d00781d1b40d6500400400316a041700802040c2004a101c0d016001c2e2241c1d100d0820399004845403c180e81030314003000140194500f030020b0724084c8640410312035148510207100e80701034503200f4464540e10440c801c1c0000100081c9641b1828090007000b0f0724070700011550307050183c3c0d000682d4102514140c030b450030320030840080341c3c10005042c41920741059503610303d66503c1043d085401c114001440f81c0301c1c0c88100c3c00d0b00580751600c0060042c071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 525598318 1250 525597068 525597077
    0x31816092d1e18060b0a031101050901032703031107050a080a02120403060c032901030e0f03070305040906090e1005061f0203030417041a0706021e0301080c010c0305090f1201020307 80
    0x1400fa0400fa0180e4020400c0280305040180040000446419003500307600d00a0038419218800300c00180c00809240b49c408008080b250540d03100c6000c8111075021042c400d403400c10150b0f403800d89401e00c9001c0d4160051240d4002c1c1400000725801d94050700070110184100d500311110f10184408540055004940250301c07000e00240c2660503024442c900910307074400d203003c8611511104800210114054107055407244000603504091011850115035041129038031000d0b071034001c11a034410301c035640d80302c1c2c40c1c6030020038807030054092560580708030700080c5440700605032400020700300a00b10320781c0103144800c814443c410001e07404c011000150041d645034a007605248004002e0814210008003081005102c03101c0346003e8080030300c8007246101e4860b260307490100d0080c0f056807170702c885059007850b020714400c01020040d816035104209541c903510700200192040009503030021f010a109001d908641d0529040030f070007a80d0000c1c08c031a18074130444c00c9242203138802c2d2401c0e03000a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 525599568 1250 525598318 525598361
    0xa06020304030507060f17040c03061a0906030f06180102091908100603050d1b060f0c18030c14040209040c05130506090603010308031816092d1e 64
    0x6400e0040d200105441d081c4290018036484000342030050311031b01d01c500c9083c158023003004e12402c03082c40c40180da80030404120562810081e10410b014440b5614170030000c280000346541808608603004200e604010007054440b4004442c42c1050b60245d00b640e99400c1c0118074082e078521a0004074000c1c61035121300c042d41040805801c124900d0101140d407420aa01040010400141c01032960030750302e4540c4c0b40c0b44441038024004c2840440c06000d80c2d062080d5404030040b02c1d8003503c7c940b070300c517101c0101120722030200c1142404c00e8800034101c2c0c140603800b0002c6060b01d403a924400c4c0c0004000510300300d10b8600090450ba144454840040d1012945d91155042180c40e200541300843e6064200741e02880020024401400700903c00d000100c086400800201d4040a24100103419100c049240d8652610414440d1169a0038a424820b07502c550365080b00f0045120110000004403115200006002130f00035240d44c4808415010040720103154144902c4d541000343d8a01086035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 525600818 1250 525599568 525599573
    0x40f290106030e07090b0d0b15010207050d030804112205011509050a03081b0303042414060f0111030d0515031f050406110406030b2e030207060204050a0602030403 72
    0x20420160071000606140c04488205024009100d104643e6800b0020030400352420204512401090004004609000c140041c00704260b040c0c2d040502c0a0307086400c0c0c40d5a400801156240c41c101c090b012030302440c08940820f01340c21090b1042c58025041c504c0d103241241c250301491103403458520440790f07100014002c1c400c41060400c2019130500d08500824207180005061009510000b000300c4c00020340081042800b07460780a18610080c1520348034034080c00c0050340200c0c03c6001907211854001e844c0c14001c468030400e0607081e01c07119603031040d43e680e0003482402d11000481038144107600c00e144094460400081144003800d0310b02007180e0038196070081c5003c94a04200317100ba000340c120904001188035001110b04441d0801180c0303a2560300b03028004003180c0d12605145080042c001c0b6607035070103420454a0035010b030350a000e8400c80594038803c600c111140340c8100704102c04d410442c01d10a8000c1e0201c58002c0e0001403520740c5d2940004c00300c1016a2001e0056040807900300305 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 525602068 1250 525600818 525600893
    0x40515121801231e09030d05090708030f04080606010318080a021614090105120d0f050d090b04110d03080a0e010b0a030317010b0309030706180f0b01080f0c06030f040f 74
    0x2050320641c0700303010641041001a6147e000314206072070b07200c1e85c910000d1480a004c1018100a0100000380e81c0e891521418600607540b10703015a40441c41001c0c04214994403903c03443c00c0340392440403807000d8003015940d51038150f80044242030862244000560403018642c82c2d54009201001c2c9030344496803c24240012401c05900003442504081401a880c08020a1074000300000d403400c40214070070860240c1d036034003541400383d40b128506071b4a4001c024025140c2c034016400fa540000c100142030003007202140d0300c018020f0000b09c0210108940721a10307004405070801400001c1040914003007c00c03594440756000340d0000b80320f00300803051180320060060141c00c404a074149186031860107199288110030700100301c290b540c00c03184c4900c6019547e401400e6170200201689480e0f50a095801034070a00030221345004218100020080001c0c0b043e6406d0341c09800a030841e0340e1420ba90325500d400402c16102c840d0590344510002b400100307071142c0076031070010040450030382c8207001a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 525603318 1250 525602068 525602101
    0xc0b0a050115050f1e0c06011e1202010c260d0b0405070503070801030807020a03240b0307050a031401020f0d05240d1506050d060204051512180123 65
    0x200340f110030820128501d03c4041141c0c018010704054520000c1348031442c015070321810781e13442e12501403540081807040b0050500340200c2d44111072404020340354960704001c2894504000c1c0401d5501400c540015910880403500d0050510003000c1503586058072200303544850390624082da91a140c0303809520305485000e4006d900c5103045c9081d45003d002c0540560010700026080620220b51030342113542e5071400a01941d4880681c130000c00800301d6403211040d11102d14041282001d4610010341800106030085500040c0750190322803464a0b17003d11400c00403100c16465400300054010707180d80c0f00041c201f5080ca00d0340003801c0e141800b6002d84541d907004015800e030528090001aa2380e03034100e60800c0c941c01c01280440003d0341e8401c14000c109aa1010f608140d60280103000d0000d5a40500200c0c0d20a6032101120003000360038461500c110f407420700d401601c410200e1101e28551844a800b001c44100019503008401111904903070103030040da600380700840800840307060000881 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 525604568 1250 525603318 525603359
    0x30a03031410030206030109020c10020c0a02010e0114091c0605070f0801080105010b0316020a0611132112050c0a150c02060402091501090e071e02070302060d05070c0b0a0501 77
    0x1030b0115800e41d800900702d0f21061051300340300c50700420080c007000c2061100e5821445050b400b195601c1d401c100c0c0949032545c41074140d0100700100d103074400c594019402d186410b001c1944280c508100c603020400144a6480308003a8a039290104000280084c4106400b512403611044d10035808407000801100050f040141da0764108030040108040030000d4a4021588400c0e001c060702220004914040000d0000b400f018108403800311310300c60010040043d01000c3c85241030040c0c9403402c43c82c0349450700c60350340881011564807101181950b00b01c40c805400710310f4a61304d001c1d201500545400000001a100203032051102e45003c0014411494902414005441c00c0c2c40c01fa0001144074000811018812880d0200720256a1080c01d07114040e245100c1c4a078502d0030074200003001c16050300c040a107138900c20350750b03140005e0000401754212603000342842d15110b4542d078000d0144c40094441d00a1105420303551002400d115241c40c40f8000200b0700240d5580350400d4070b141c1c101c080341344 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 525605818 1250 525604568 525604591
    0x30f0302010b270106080604140a061703070c0308070510021309140402240d090f110108190207240c0210021e2a01020406090f2d05030a030314 63
    0xb00d060f003a074011200d411910756042002281e1341e000007040180400c8035007151144040400c00085001c954441c000343c429141d46581082d074040200c03652031040c0000500042c64804080000030000001054040c0c442d8003030b5002e040800c0d0911050740c1100101c611078100d03560f0309100c240742505c20f0300c508050910700c00055090139000305000d6405d52410b030b0500410201c59040d174030344007022201103506004003001601004d08142c1843c0190303443c02c4652012080e12204151b225a14160003000314030511001c184066030352400a40c070100d811a05d1003500055003a00f4002c500001074406610308021a01d80301406000b802c164900d80681c00541c8180300004200000c03800c000072070a4034040c841e07038a452a24595640c110700500300c0b4a00080307041442041d01c01034010340308440b071a460b84144d442d211104605060b43e18016030040240c40c45100d500c031032808205039030014801c041083c0c51512800420304006112030f00390080303502d0f44980803480c1481c070300c0360341c1c84501c2080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 525607068 1250 525605818 525605869
    0xc1706070c030e04050a0e0d0e040b040b011205040c0312022401060e0118050904080418050106080402010e04200a09050405010302010e102604031710090e07030f0302010b 75
    0x40180054800c00c05240c016945c500008014080c01d40c0300145007007401e0200d07998403803c0b40000b000025005541d070701440c04d10f44400d0340c40c24180611708540805856641208060710150002400010000d6480e02d51820002001c141040240741c0030b4210341c0d01524003242054212216052050251403140c01201d0040205903440203c018290800346000c2d5102d450000c441013800c20030b0703008650b00c65001024082002004c500410440d0300300c201030301300402042c1c00b00c01200c02c00d104482c04141400c00050041d0711070054880b58a0000f8400518003d040e02d24609000c0b00801c43e00382e00c00001209042d56801c400320358018a4100c406105540c11540020008400c40740f54a004200d000d2450100d9800340702c042082500c51000d12580c4102c0c2044284100c0c410384050340415504181c1040040800740781e1846410801c41e01d004040c030b8184c40c0802800c1c0002c1e00c10307040c01105c202200141b0340303040b1101c890303011ba4008107000800508111100c1c00700f56180300f100d2482407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 525608318 1250 525607068 525607073
    0x10e030f060601140d0e0307140a020303090d0203030d0e01050709120c05040c02120304230c0a030b07020109020603150910270914071802040803030103120c0c1706070c 74
    0x1d20a41c0102d0a1038001c80c031000c282c0c0b07004064064071895202c038038285040b00ca0746180000261801c00d001d2803102001e803407050b443c692180804500079400d034104100c4003c0c1c038100390801144840c40641103031b1800016a4048040b10341030096624240d4503a801d006540d07a01c10030990180448030705d10385500d1304565840d00354040758840e95005a403140d004602c0c9074000d1100c020000401d2400907540c2c546864030031310300c140c1500c0031607800107502041d449003c400a182064000050442040e179070568941c044c107148020030202c21507407a00c1c10040180c0342d0394061406802041c03000104d0381c00310002c0100240c1c0003401003911801c2407008201881c0901a00000030010711103d03078001c1c0c500071210002c0c002c107a00240c8220f648800c051940c0c80001818000ca50001c04d03408a400c1365072094000b84c0c803552060209548c000c2c00140b0100e01916100c80ba100000c0c20007082514056a50307400d200c08c0e80d801080f0340441e01c0c424005448040c070005910185900d0444412101076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 525609568 1250 525608318 525608323
    0x3050f15090a050601020a020a15080a0608061b0f0a0306080607080915131208070f09060c08090310050f0114010c0218091f02090102010e0a03091505091509010e030f 73
    0x188180b84070b42d280c10109805074020b10a220110b0740140440c460251502c0120301c000b1902a5036034002054080058502481481540242c3d4424400742049480300c400e2599401043c815090081c801048003001c540002d1004216818107510049502490808800e081c494000e050209001d4910b0422480308008921410300600c1c03600302c1c1c0d405441e494034010004000c080000c181152408884c6459504201c00502c22825540c0780d046000302035400701c64030340d29803003080c0101d805007250000040341180074210415000d011121403500340d580d000107948041c0d9a0b00705400c103010050010b1070442d80749402c60312003802c0401c4600004e40c04518404503103442d60038050041404036591b01401d22828100158480303454000c1e580400b00d1600a44c40000240e01640c41d0810340e200842c80403892020158240d1145450780d864203508440b0600c2e0001c52100b004403c122110883c3e680d868511114420004c00399101e80010001403c59880120014440d51259100c0e48001000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 525610818 1250 525609568 525609571
    0x1a042d090f0e01112a0c0a09020d051b040b1e130f0e0f0a020a030e06090c01020c010903050a11031e030a030f0e0a080c0f07230a0303021005060a03080a03050f1509 72
    0x2d80d0482c1e800d10000250b10f03410030b0365183c1c0c503917401f1103440c0000850320200e070042c0848a220200402168545d05440080c0c003024a49000e011401808100480605280a050324504d52030b0018803188050075124103582c004a0400100f00300b401090055441d0328100102900401c80344070480d050001040403c0e00b0300421310f01695400045038a000c40c8250058100c00c041d59084820386d0401c51452600c0e10356400b1110300620400103155031561045030b07500201d9070404d002d041c14140c7c50710b40418011110401d150540b059100322308007045c1ca070300803490152801c4c000d103482e002082030090683c1d00151800030150308010500012820208902c055980d00801013595802002c0005042040402c4104071a0090030400101094902c40c41404503800089450344010614104403001c40e5900002d00181d00c1200000080f91540e401660803034801032481500d20340d00c1d40c42c1c2d0a1030b0700050a810010391a0303028441105401200607402480c3c42004030048840000841d02c004c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 525612068 1250 525610818 525610867
    0x1a094b0409020409020301023f0a0c0903020904060f050a050915040203010b0402040e161b140a0f1a01050a080a0201050304020f030d02071a042d090f0e0111 69
    0x25210111402c5640340d50144080da0342c054000d54031165903007540c0c0740d2030b02d2a0f80c0401013800c0b0130040c844660624001441c01011810381c40c400c5c0d49400356507800408201e081c1000f4055100000310140e680c100c10144501d105400c0070400348640711900d0181e84010b440440440d00f054140301c2c01050104201c040e01070070b501c005213503685a0000a0245c004590015001440050042a000c20010000e0700c0744003010700c1c00d42090b81b0310b107044444519411024980c1c80814680c0400510f070050101418040c0d141115098901a103d840b4162000c042c00c81d2442c200c204600034460b4462480b03401404100c59100e451032503c9400d0303448001c1d000000381040f2000001038115a20030580c016a410701404a0704a03090441000e96641c00034004d0410200301c1c1d101d800c0d9882882c4d42110150341c0702d58000054440401c01d803c1001c0101c0410381d1207250345000114070b1425921812401d070380c0c03c85010955010b20003250f421a1b40d20001c1c811810420050914003044440c48110241c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 525613318 1250 525612068 525612071
    0x1150201061203120e1c05040501080c090f1005070219090e0d0807030b06040f08010902131b030207060905010504061d0303103605012606011a094b04 66
    0x800a00c4a1414071149045d46d45041072008120a06240d1041c00f0780142c0b842130b00c03030344080e44910744105894000c1c1c0903840e07030216a4034059200e502300a0420224501d1904255080c25099030000711405100c6202082c5c2411075031301007095001d540503003003d900d2404042d00703a5021b010742c020840c100050008051546482190b5901d4580c80111001000d040d20890030380b980325444140a0020604242d03c280151000140314003824418400300000c0c0d00c02c4200c0d00307103a016003500030f500f040e40f007030ba18940e0703032a0604040340c028051244914802c1d44000345088a201b900100031a8076403000b156540f09008011044014100783d00070354040b00006080350803a03e003c1f80100c804050a5000c030010f00e10800e070580350740c4e00000c4c10786421142808845485000845062640d42403801e5160700420041100d000c02d0740340901d04203070020109241920381c201040315a02130710000680c043d018a541403400d80140400300d2301e4003440241d0400c0114980580702d40b100c1c0a81540e200d036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 525614568 1250 525613318 525613331
    0xf0c051c0206160f051c02163f0b0c09130b1504171e0606040f0e01092307080604080c15010b280909020c0c03060115020106120312 58
    0x101d107840183da4040d507200540c264103c40500d005929a030803501d0b40603195407100b554501280c0082000d103d105550f1111564a42c40c260302c0d1285144025880c412840e00c108060411240e42c038645141c007030100e58105910a4286055895140300901c5d008400005210304903160b610102c0043d202001c442003c100c11201d5400180400c06004082003808000200020261403284948481241c502d0613511050090042610341490007503141895070008400500a0b240961145584002e45940007075800400c100b80c90031138820742000d54050041d203140300003404e001401d10384604440d80c007411005140c580000e0b6202409000180781030004111480c0390402003140c000c0c0307110b260f000d1920710f50755110483c0b111340c0800f84560302c0010184000d0028000f0403071400810160740e6840b0302c07c07031400c00e8260094000075004c0003a40600d9440381c1e03a59800304484d0340606032075502071401000458000c0c0c01c40340e031640134004583c9c00130030410100b87c1102ca810750900c200c013004240c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 525615818 1250 525614568 525614587
    0x901090b0c2d060c04050603010902160c0603020d0f06120201050a05221e1a1e0c1e010c20011407080117010513020d0f050102070f0c051c0206 63
    0xc05044240e0340d106082c82c1d00640342004610088403111904550580f04a80c580c401054500c0c0f2550089a4101004100400901149034000e000200b501341c00b411100300903666425800d10640c0c44100001e40104000403500414407840032034071060b64081001605d8034011484000300e108000e4140b18011400d03801090046040361a10030300405800814815113a5400c1c00d6803142c010404124850118454040d02e6a0050000d4a130110358140e540031001c00280e03e26401519815015185495458184100c0401400d144c034000c0d4040c002e00f40584614071210800c40c1090710190381000e50b41c40c001a04010326028640c81070400020b1254004091805005031880f612050722100040003011035000e90000d05035160381080d546900b050031080e50903504e00382c07101500f039500295000b005140014610030f42500c581550800d440e041e84940382207030824001503444080d03c05160081054805000d070203480c0495141000c4441c1d000b02c4041050038030381c003d005139000a200d150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 525617068 1250 525615818 525615823
    0x50105070c09061806090b0901140a0b0f040509100e060108060d050a03020f0c0303210604110a080405120c0d11012009100c02031f020d0906150b0901090b0c 69
    0x1d40032220b400e002042d40e99800d0109880d04002c6920a07520b40301022862035001e0080d0001c10200420222840e4240307608020f030640f2a105c06c0740e1020343c103c00040d2540444028000d48070b071100c503442e00c4526010901031403403c024040c9011544a250903c000c1c0e1444141c40c2d0000c000386005141076449001041c60030a41e50b102070300c644201201c0700205603001441c3c0f41d14244007000e03075401c041c072042490364901500244081c503450740030000b125032a444c035401e135018000400228043d954110b001b4065071000b003004000401000070402488420054540c29030701416200e4541014a042d0941b5469000310f0349082284203c280310b1004425001f80f541420716610008000d500c6090350b000782d41c40b004500780920b940c0000c0918060003411a8012182c010b00900b0003501015600240010000d07100103902e9400c1c0001c0070201c0141c414824080d204041c00651030b040f4259100003103c10740d1002410180800151009990100d0020221011a60403640b81c00b00031009031f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 525618318 1250 525617068 525617093
    0x30d022515060603020c0705040b040f022d0403030504120204150b09041401030309030f0c1a070201031d0d03020703123806030411040b0a080601090e06090705010507 73
    0x25800d003860610300184008407002403101c2022a07010003042c0d56881d020f4060703008203600c8207501e40242e502045207007000c0e04507281040c002040090050030345c0000320102d800c02030801f11003059410080666440c4c8283d030103084600c543c405810589540c0c1d000740240b0940c040d001d81c030ba00050005d030840d1a141c01094205229604210b10281c43d880b110f10180c1050300400d118605101102000381194419141681d4040d59565516415a00e07020320456403000c007201c4400c0255000605a02c03100c00d00b1036500c00c03101072540c2e02d0841e80001411340d20b840000c00c080c41c7c0003d840b40c698003400a03880c50407814a04025032500a50f0409464242962000c602c3c0756090003c850448074500d200c01810744d1541030b8060b400c0107107280c0301e42c101107854a4650419400c0000c0380c080780004801c002801c000900c04110600d4041c00309140c070b003082d4442d20b240d0b40408018400468036003e200504200c110062010b4a4110925075403801544100c90502c00c2c002007400500a002c50184d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 525619568 1250 525618318 525618367
    0x301120203060f25050d0f0f1a09151f030209040b030102030708040311120d020309070e09072303010c0305061c03050d0908040512030a0207150c060c1b030201020c070f0602030d02 79
    0x4001c540c5c00c600038031019010b04958601409d00e8082058408a21494864520700b4040c290b01c40076552101c0d10a00002206041c503485110039000b01042462600007600307000041c2d03405a100c2c6002002d04c010f03524003681352842a4018003c00c0b801591014175598490341606d4403215501168007003c1c1081c600b682e214210010000d03552020380501d0b0019030180000c203046a4203242e8501d803001100f441540c11031020b0f0081c84040002600d6030300c0d04d100310000c1c0075401e0b00d8440c0100c0000c1c01c403130701c130030810001c6a224002c01c0203901e021030340c40e22406d40f1525401100740c41e66800504520410703100c0c1d0211607850303507054140655041540c015101c050070580c0c0b010302a400c402c0e542e412484125006120308074000c02c9100368040391160b54041c50301d50000700581a41e0700070240100311801400c00540038009070400500700c40c90100e4901a8000580e649000744407242000442d40103c41d4128050a00308005580042200c20480a41d4001078403030310105149841c1340c4001c03002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 525620818 1250 525619568 525619571
    0x219022d0301020408012f0409020f090a120308010e06060a030f020405210d0215070507050c1e040b18041412040e0a0c0309021c0609080301120203060f25050d 70
    0xc1201c200c1503001f030501e00c04010003113000100015048100324090088220340d66002c3c00100084542030300a8094070514a4a19041886040100791000c005601214403065111200018035809c208424050061000c405183e40b0340a408562941704010002d810141d480c2c600524101655054a0240c44001d154a00c0c00300c045880e2984444a1411564140910800f02d68098000a4403805c0355525083d80f000d0b1b52340e00b000903a403d0704100710550703d5024421400c00ca80e0348003030388003240da0340500c0001d600c0595801444100c2d1040621540941151002c04c4a015136400002d60f1103076021003000c280780b401c0c18003242010101114080441404038002c145458250300c41781c032400c10010704010611404201300c05403401c0c10006034001070080b03218010b112030b0000118110b0b02032040030400c01903035660441caa610036404440c4e0413401c8503940301145400d00c156070f00300301c2000402c010342c10940070101c1c80d00306520302c0700c01d00005c502c4004802401007007076460f2203000203070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 525622068 1250 525620818 525620827
    0x1031b0f09170601051002010501030c031202030d060803030916050d0b09161d0702191b0b2d180f04060b0d050402100f05041a0408030c030a0219022d030102 69
    0x10b031035503018280111846690840307080f1141a10521816040f607400030380c0742c4113107443c40d1520324083c0251109581140000c00a83c604003a05001d424014003070740d00115500c0c0390000c1d00d1414041c280a0144100103115001c200035910003441e40105500080607480c152541d41c01c8920385000d4078006250680e440ba800910021b030104210315003404507680d10b010741d8540004030b03111761614551000c00256200b10b100847c1049600080c42c10000002c1507142d038440706c0d41405c43d04041143d8070541440d8208401c41046131000c0385100310400d5500781030891101c0b1545122400d140681e0240b03061003504807817039039940c0003e802400c554072919030300d4501c06500c070090b00003160140e01840040c1801c40c0c19031712510380040404003d41d11181418217012998030070788a000004c0d03007004418040450702c5407043c0001c040c106d412000031a5150090700c006800c114405d00b41444000340c8030f0781e06001d80c55403188000d0505074000e981c1044a40420120b0b00740041410a035015880840d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 525623318 1250 525622068 525622109
    0xa1713170a0e0d03081e012106020405120a0611040f09020c030712230a050904050603010e03131502070f050f01091e0302040b0f0622051003050601080601031b0f09 72
    0x2480e0782c01041c604003080c07101540124a8541340c1c03008c1c8148030001c60000d0181d072101c0d5520f0f10840d81c02d0f100e1080545460341c3c42000400c0042240141921170f0042580c200401049102d410f0b000a0215052400c04d4135200540f141c100c4640320300c0340090f400041001c0820424011a4041648014110048100301c2c0000b010810011444088032034071003d41100204188150384129080751780b044c1c5072400c003e040c0405010040c00540e011341d01c1d1044060141c0050014042a62582c964004082d24122400c0c03c1444448081415904003d0049c49180715018410003903030301c01d580240407030a1000040fa0f4260242d440009213921450b103031000d0440314940b15003202e000700e03000c0c04611080001c01022122980c0141c5d4040420006c1072400c240500742844007102800c2220400b42d44c4201040d450302c0f100503101c0009a903441040030540e004a80250403010a1a0801240f444150710308501203000e000d10301401040c0510a1040780704482c1e07200580b446928204081c03000c0c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 525624568 1250 525623318 525623327
    0x19080c011a12060f0a0905070503012d0c050f07140d2006010509040209041a04030302041d0f010603050a060338160509150a1713170a0e0d03 62
    0x100321a40c8568080564641c00000005041c0d004014000c0c104e032158907003810701c02c01005414012107160144100025a6603001c0c418840000300020b00d2845200040781030b8200042c41100100d090781c60903c00780d4000c2e038404141d85090303106400c825235038001c5080400c15a40d20f026625000e2080b04081c150f469802030000c41c48050301039100500c83e641c2074004c0c0c2c0b10b602c24064180c000c6945000034003d4506019802d810a0003808600c4011543c1c50f03140282306c0c81181c0c00d50120f43c0000d01000300c0341d02810043c1030030400303400109050400040c0700000381c41c107100701001c0607281d10104e040d2136800e0344010300543d0b00003c1d00e085c202c800d1440c1600c20a00e07101c0b43c03c56142e2404117540078865580e4051180350365060301c180c81040032500b83c50503000010801c1d0001c1015624440c170350720420007021005540e4448100030460303481070000c0c8200c02404900900b1007441c0440010700f0b0324003401e1050006a502c2d0b51100f100500c11210000464501640007158031442010305401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 525625818 1250 525624568 525624611
    0x70f02041a01140a0e06161703041a1303030e070b0406020604150203040201020d031e020301080115080309010c0b0414030403030f0f020114010b090a0b0f09041b0219080c01 76
    0xa8880e440c400c149800107000074000c40c40b241d408544a05c502146030310b8282d00803c204d440d500c0324481d604d050354443d410f008075903040900c0112400014041481072001850005c0010b00c6200b52492810388000c5c0f04c4405103000082c03e041d01c48480c4100c40c041404114041c14200040c252200e1b51104003d60380c100c1910b00f80d445141c0d000b004081043c16008692003550107070018481e040c0d2004d01100141492080c2c1113400038060007444c91400c00b40019402424098004240e1246400704014140300d80c0e400761a195004020300001c3e81d8202c008424950f40140c080c47c426034071418200d242c00401200c240c024000000c000c810190040c0401801b060265210500c0c0000e0304c0003a422244003509080031b454100c001000460030701e80042941c0c801c05420400103e540d190744072159008400900001c45000c00c9110181c1014801c08040c608494500450524900c07000307510703950b014070b0001300c0d842e4100e415001c0c01244000c40b03c40600c10402041031a801d8154690071010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 525627068 1250 525625818 525625871
    0x203072c06030f07150302120103060605010305061e06090a05100c0b09060106080c0c0309041e0f05010b040603020318030a030911100e1c0b09070504050f040f020402070f0204 77
    0x102003000c9842400c000030446460b040040081003034034107140020340304160200c011420541c0030003016044000100b10540250f201d250086622401c000c000b405555005000c82d000b01c6d80c030b944082030040342000c0000e508609494003940d66155102103412035800f9008907400200072007801079065802041c441220b4010705e11000c103500e4503400251103220a2051a000a00e01d8003c240010748c0c1c14000c1042c4400281101d24016241000c40c003503034034003d155103c400c0709101c0d000c0742102c14001e81125200c0604104519818082019241d0003240510400c241e80440091a2801d000c20038a88444001e012240c030340b051408010003078200020222018a04090206400e00346009101070001d110703283c40c02c03084d07080310600c50690146606902c28908040c007140c0450540341c2003d005d0f4072408003410410b4108000e06c016140054190390440c609403042101140007a5914821194100c40140e0345644904200e41c6149010343d02a40c098580540b13108072421140101c203841c0e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 525628318 1250 525627068 525627149
    0x52e09060b090a0803030115050d2d0f09030219030509061611010302070f0314190306090501062105060d020603180606120c061315090f0906150507020307 68
    0x2a04d414240b07480707000c2841200c4003502915017003240136008030007801100c0600d10001a41c030741000c9420200c0144140d4074007281410b0b01480181591034040d0050409a15500303210092103994000c0da14401300402601c0d45c7d0901c0c25400405114100b01d80000400501842e01c6800c2580920700b808840741088a6250042c01e019078594081d0080c1e42c3c0454110001044080306034405940700900e080040074085000c00072900301105400a0100484140d0f80000f00a418061020700b200d1040c0c0010b001e00c07800c0c1c0f042c0041c0c4480d4410200b90754407802000300b115200c01d000300d88000e2803107070001d40c0070030040108026407060040c1c00301d02d800780208980860726070800384013000206103412409034000c10f82c244020305245008020b0b0600c41100c4550a0b030307071400805540e011000300d03200000e0b1644c10801141c034448090901900004004020203490700d080c1d0749018000d0307520721003404008500030b0f0540d542846030781c0c000d011404108109112200c106401c3c5298030380c0340d85040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 525629568 1250 525628318 525628339
    0x73021091404051003110d0b070201090606080c0603070f110d11240109020a0e0402030a140f0f07110307020405040c09060902070503092b15050a052e09060b09 70
    0x51500340242030190b6440707504c038a549410340c2c4070402e5140c0310700d00b100d820490000c428000140d406010030310482d110350000454054600d840380a940441c3e10507100d642c84405050000ea136404100d0b07410000c0b50600c1c818401404606030755048208440c083c642c044d0388554000320340c12405944031262010155140e0101040e01e03140c4404d1241c180021080744403005001c080f60507401803083c0140c0d8100400300820400015060b680100c7c0d03103548a40e16918042c0b1031258903200f841e000341c510f084400461400f034400c002c3e12a4010b0102d02000b21510113498a80300520881d030019030060003c0c072480c60312b420502003504840c85010503540c6080c40016002c03085109990580d503001000d14601001c0c0c1042111000d400c070000e03440926003900f0070645003040c0010702080d6105135024510303078811081050485038001d010307031045410002085440e070841c0c5c21108000b40c00d103006c024099001580b0044048160300b209618500c0c0210110b40070400700d0180210b07000403507242014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 525630818 1250 525629568 525629609
    0x9151b0807050d031b0c2a0305010c0801080604050309041104080d1806020d0903080904060e040b01080105070801080c091b0a0509040b041509050a0912080907302109 73
    0x1d51110285d000300203010700d40d40304000703180342d10542a118640e212800f85112a4109803458074226401160039a65a140d624030740c941000181c1d00526802c1d010300b035245800c0d114071b600d07440340c1c001300c82c42580e907546410b142d100494240d4002d0b000c0c0c074040350381c580400d90001c0e00d0740c80100488404902003110025000d80f001410144000d6590741d526515495561054040c0d0080041503070300075250040456005918015648280e010300041061945084c3d0201d00b1240040d101008000075200140007115001890800000b0151100c5446540748050810782c61800c1c90740c0c03001c0d10310000d40c06c00d00541c4000600002c4004481c10081d8145103003c22007110300c503200c0030f07050b13011800c003c01a40c01c003907004540c804c02c4503401058010b107564500b940c40701c4059102c004180e01c2814004d160104011503c0039143d0030f0500081d06442c42d00400d13080012100c00d908410000c9140b80820107691540700e120300780d029840a16280052015041000d00e004818aa08031041031156 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 525632068 1250 525630818 525630851
    0x80d09080c010e0c12101d010e0303040326160e060309070f05030f0d1803050106090203010311040b06030a0207030e10020303010806090d09050d1e0c1509151b0807050d03 75
    0x9800c01790402806030f540300d09945405490001d10304400769544030900d410350102805105010b00700e10010b140d80e4942885d001d030103040160300a042c0c1003407407000d4a41c61510041042c7c1c11107055045248a103800b031104039001c40c8045400c0b0740006001c4144008107200180c0042580c0211082c041142c0e1941e06250340e804020b8091105544440e606a071100e015980d4001c0300c100da2602c0700101a26600d400742940d000303070300c2200d103070740d0000040080c040000b9801c41f04010850341805600c480e10005800c80c040680a51141c503070001e13120b410035000304141907100d4130280005c1c608041800e00a91203410921520003640510000150784000114040e6180607039038446080345400d003018014881c12010045a01c461030504010b03030b8907118040b544d540ea110720030ba001c5d240e040008103c41c041000381e0340410320078580750034000100404c00d00650b04e4220729000f00c442c448100c80c0e4a01030010100a004d5a0000400d41d00740100032540c02e050f01c0d1a41c07002c0c00703d40101241c495 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 525633318 1250 525632068 525632089
    0x60e0718150312120606170603010e10020904060504110307180e040305030c1b0601170c01080a0b0303070c080102030906010509010302060d0f02040b0414100206040b04080d09080c010e0c 82
    0x12121944034424400119003030a0b480c40303c81103150800844a80700004421680c454205070003007895a50300d50400900c004910354400f50a8000b4401c400c802d001c260b660b182d0030034940c59025001300c2c0032100e903226030340710400415004200f440300071241c0c040c46030b0036402a02c2a0000520041c0094105000154070000701e50601c0450101d40d43c8544013280e454101900254041e0310400400083c80801d41c50341001c00603440c081c002651600f0101d00198007070b1400d504454025004881e0310340c1e040108940d00441c0c90401140c000800c100182c11071203941001020803190300c0c00481c03511815400fa61083c03075480102c3c1e10b07590301c81080110310796007440000e600040400a00001444503005281d82c6d04694401604103038440442c104190419001082143d000380d01d10301d0680b5122500c03120685940c000f9208504094640070200d1100800140c0350303040c000f0340ca40c03005405602c00301415801103222a140e003405a2a140a800540b12410381ca110703500c080391051904100c0b40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 525634568 1250 525633318 525633341
    0x40507050607050307172718011a0d270308150901210c0b070303050a020903070536090c0f0913110a0e2202150702030a060e0718 57
    0xd5042c4040359445c3d44407040c8a4406c06040c8101384610008810714001000800380000c50740d4800c183c03610140192042c10109051000d03030201c0042100000000301d24210b5044200696640c040d01080b44004e890030b5030f82c00b010b4070210000254440c09400c0d03c21206413080d40d07030250341d444054040f095004c580c081664010950303001008520140407810240b05009061203481417800d40398010b880c241c81d8002100b4000c00280001015070500c00c195019603210300460500098101090303440c0000e026140c0038214a0002c02c10742d412039a03219070030306d01070440d48260010465803141c0705d001c1644d000c4450b1140d0003074400585801d0311041c20300740780545080456a1010080c0700c02d05a82d40f8156000315001260110b5501c41010310005000703a12844030141c204003c51500302c0903001045030b0040c04184141006079101180b600381480c402200303030780f01d00d103d00029040c0a200d0a004100c01c0c0b62080440d62603c0100b11003080b00d2040030300d408400c150506140c140da01e800d091 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 525635818 1250 525634568 525634573
    0x1b0825180815151f1701140315090a0209071110061502010903080a02030a110712080105030a0f0f06020f2a010605010e1003110c07091505060703081b07060504050705060705 76
    0x214003140134050412421140f070020a25040007100c0510102d00b130b0005414198042200c10303107070504001f0380100c0446800104810301c2d2142d041e90b02c030520300000070701c240403240210b03120501c210030441c0a5000503081c2c0301d950344408502d00c000c0956100d000f5444128a100d41d414500603c1001800381d016110a0403d540305036100b0700941c0010b1141c2c0d0304550f80d0310b141c610082500702501c4094070550b00721001907003410f80038202d100140e002ca0f2103603000464200002e1240c0c40000d0060354400000840c1c03800c280b8150000c0c2c000e010f280140d01758003242d16490400404141601ea5030f00e055529401001c0c42d0801c0d0a80c8d010b40266804100010307008100b609201c0d0f4a180000750f1449c0000b209207185010715000e50000050f103e9690015009004210192040b0124005a6030300410304902c0d0401041042c0200603000c1c00b4409200000781c0111208400028450b20f501f404a60f0b500062600714000d00058400340c0341441800400700d042c1c18220101c0707202c43d800800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 525637068 1250 525635818 525635839
    0x10305062508061203040305010b0405180d0f022b03050c09010e01050904020415051b1b010f0309081b0601080a081c02040302040501091b082518081515 67
    0x3426603200102078400b5400200111381c4808000c020310240000d98451000070406104040402086d1100542038036002c034049a0030365910500001c011140e0302c3c8504061100700035911050b070400c01c6248600317000384016500c000000440e034817103c0340c0711070700c0e2020041030322642034117080c9000340310859012410f0061007030004e41c01100034002c43c010060000d803400d0f480b2881260155030950344100801c001181000026000340034440940f400f01000f040d465210900507404991244249410300559440c1201c40d20300c81e0304981c401d80c0d04020340d955285c0d40c040c0541d201700c00829040d51940250000071809490114118074203d4001e40075a00742511170384240d4084005500b00c0d03456680c20030000006803528000d06008064410340080e488002c401010002c01091100b14108280030041110910004441114510011404261080c101e030016a51040e0003a1340d00c01c401202c0100141751040001c698988070358000791000b164072085007408440c000340c0c04a43d4000540803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 525638318 1250 525637068 525637141
    0x1a01080612010624020709020310030209190c0f02070e010b07080f19030c0801091815021e0c010e0a12050f041d07030b06180d0201210501030506 64
    0x840c84000c0d07200c1d034000041c0b15030356000009903107501c50b5540003c03101040042c108407034061103000c000b04444c817000e500c2c600c0c020b03060092400c02400024421500000071070030641810300d10f102c007001600f40c100b10a00d1415002b0348141803000320f60f00140f1481101064190302c40384514102c030290344540382421a65502c443d2550020152440b0420042c0215400d1042851140b003042c0d0060324000b961814143c0020000d000582000072141e0130041e421103562010307080d80303102c95000b620710440c84000fa4a100c4c040e10520380c7c4e101010244c4c03480c100d0807240643c02410000a200e0082080c881007a042c0c2d40c0ba907148001c094075441221a210b450399006100509180c1022580a454143c0745c0c11000c20480140008400c00c3d00e124041080258061050102d042001c442d01c03404c040c80c0703680100d0360b005280c0c0213034082c2094590301401c59010740c2c0494030100b00989103140100b606042c42c0c00901e02407000344c4207446913001040c040c41d1200c0c50148508082201041e04200c0c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 525639568 1250 525638318 525638329
    0x9180f06020c0d0e011d03031803070b0403060b032811010e0a06120b040615050d1104030f061103060d030810030b090d030b0f01050a0f0507020303120405011a010806 73
    0x4500a4811076002c12400c041c0c0341c0c0038000c00e00d006010381c444450038001d81c0e0006100c454a41001c07100002c0d00c243c000029034000050380d1420320018202c0b1480480e1402080c1858615401024148070100c4c0c04030411005400800d03c0c144150221140003182007401c152070b107501818140c00d900c2c02607005010401010780404592018100b0345001035900c0040f0b404d10075954000000541c01344110784410038039004125002900325807c1c08076034203285440104d11101e04a520610100160207503288603207400c400320070744009440640f100d51b41c3c01e0440504001e41c0f4121360143c42e02d644400c0c010f68403c1920300518028280700d500510a13581500c5014000e048109074043d168400400a0943d800c034520414500018040c0c40781060406810380c1c140028180c85120308190307041e82e50364071a065030321131b2806180c084254510044151058414198080d40500000401d800720200c00d8000728080c42c07140008111550840301c0002c070901d81c0380150780c001007201000c00c0031031605c0d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 525640818 1250 525639568 525639593
    0x30f1404110d06090b04060903120605060a1d0a1d1f0504091a0702031806070203030a0e061606020702010806010c050a030e0102160909020f03150f040c1508040204060918 75
    0x8800010380201191100181090200c5080f01d916884a50230000c01d0751020420885402084060207400e04250000d4418045c08000d030040084000294804582c0180303065108000075043d2950745803500c00c0c0c1c1088001c0c01000c4c0403a904100045141003402007a400e120300840254200c6541c00c0404000181c105a82d00b69071440c817400400c06404031500140380100c02e290000d541e140040701000c5802d0420348500e92242a060102d0f0016850100071600020b00a240455540b5503d80000d0791a0003480d10030710b6451030003203604040004643c01450028003d880743c000c0307650380c0b4004666440110741c008103190801d0a0704800a4001c8054180e07078581401518064915140d0590148c0501d0380446038142d110900c5a0030340c102982c40c1070b00c1600907000b62404d2413042030304841d1004090022245540c20100190078040c40f102d0160280814410b80341100110030380060044009490a07441307149070190014004580b84651091140c1140411100303800644548084291 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 525642068 1250 525640818 525640823
    0x60903081303050115090b010e030c040f110c0706020714031911130204170c06040e06061204050114010803190525080a02010b06180925030f1404110d 66
    0x8450400b1000581c203014078140b41414408258046140006035000d031140c0c042014144900c0d803071542581c0c0c401049144880b4025280882e1104815000c0380041c030003d9000c58800e41e000c10f201c2102400800d450040380d15540c21660a40e450310821940030034030088455042d80241200401c281c981c044542d501c0b4000c0890210395220440411811480507003901401d950000c4e040c49401d8410441c80d125000500041c2100e40000d40414418401ca02480c5050008100000c01c0c03560b07500220b0b09841c140c100341035641c0c103080c40c0842c064a01d6000324000762820400216801100100ba01c6200031b5410140c034071151a450165006c1e40803091140640d12904c0415083c01c103020200c0c0c00b268403a41c2c0d682e82d01c0c002e02a00a08568140552070f00c114010401d445132003920030350800465030110355030400f03500c0d240c5000310860600d2091080908116018004c069010340c006c940c404551001800703580000440c03101809001c83e8001c2008a02800b540c2950070b090807052807251 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 525643318 1250 525642068 525642097
    0x6230114092e0504050a090603170d24210c0b0d0e010614100305090c041113170d050f0a0309050f15010906080312070e030c090c030103020a06050406090308 69
    0x35501d812066a03001005400b001c0782000804010b54203000c1c0e5000004c002c03140017084070b85d0441d90381d985015029850b03071060410102e429246070005500c280503440e052048070f006440c0f4232014074034440540c45100600c0c14100c100c1d1a0070008441d12000169100c4554045941401070804064004800d1420324507555455840111824490381d0042c114110090300003070b200d10300b0069030070000e84a480415080200340031400000040141502e0001c40c0e01085da521044030030411401500805102c18400300ca00041e4040200c18200d260f0515105682e404980c1e4142510a4842c10318070540d40341d01004891000d912aa121a80e80d9100300169100903400c040964a80401d880d40c8404e41d0800c1401080028101d102c1d0400920000c070185080400301c60603184009070007000c1c1c03018056640c070340402a40e8140009060700d000140540c071581403100180600380c01c00d020490181151070000710380b4500400c150740c00c9450a9803580181d40c00d50b560501190081c0c5c0405070340d031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 525644568 1250 525643318 525643369
    0xd12020307090f0b031021030e0f0402130305060c07110f0303040f150921020906060d0906050f06010e150d0213090b040b04020408030a08090708010623011409 70
    0x5032083c04060082c021004500c0e220704181b070700c0c44001c0c141944060030049072102212031001d41982c2116006400d070810001c00503041c000b141c80724401d0038210b54494400103c11381203016401c88a000d0b2030064089508030350b40d005603030805209a00340906600051680d5980516002c40404200b0350050292420269106080c2c0ba0380c2c8400c0c1c0100c80804206000740d440503900c01907280003051040400c1c0154460b40300800060b03000760030041d010b0031401c400201142c030b50500b1916074042c0081c0c1040115242e007416802800240d0b0034810540b01000890001d6110369000e00060400802a0503580c800003040ca9072648844071780692a43c00b0312008640c04990703000f40c8001c1c40c4000022400380d03000303803c00c000c49000000c0c00e849184148020310032902c00109460005802d17040000c4d050b11560b40302d901c1d1000c558810403a540c20560f0201e0720b8800d40c104190100441c50350300804495800043d00e02a01051040150f40000d005c0340480b0302c0e2001c09014007088055403607248 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 525645818 1250 525644568 525644579
    0x60b030a0611030f0702060105130b19090e061b16050a02030a0609140f0c0d060e10020720010203031504092a170c010c17070b01050906030d1202030709 67
    0xc0c2c0d011150b9240a1120100401000380902441e055114200d84042c0519604190018203000c88040c01d0000c525699401141c10303440d01100e5040d40365041e61890045503464010501601400800500c0c5015039808241709180c00c1c941810301c6200f0b240d4560605064542c00c28140038044000e0341c0384d2090924250158405100e000301f1a40101c0300420403940ca400d02c1d20300c070510000b0103541584510305900054402081d2610030001c22100040c00c1013142c1040805090302c041d0051650003400066000c9070201d500402072548500741c101e40211408100c0140184502041400b40e00300700001628503491b503000085c1440c0050000030700141c0e644950340181c0d00c0b281c040302d03115884041010380306010f0941900501c140004c1740641c880e800a051740360071349014098180b0074451040350802003000b502c1501030461a1103251102100d0030560365400d401e02c07507907010b402007202152450501107aa04002140c0b42c89260f13400d2a0f04224a009501c0100104c0c2000305401d004140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 525647068 1250 525645818 525645821
    0xb091002030f0103110f0102100b120609060a15030b0606031902070c0602010509070f1205010e1504030914011b060b0301020a020c0a0f0501020607080709091806050106030501050607060b030a06 85
    0x90580402c0303000241d810343c540064078040f00030291b8858460304030740c2c00c6642c0c0d002801c00502c03040c1d004003044400c00f80c80441c00785c564120045066014040400010110003e4001c1c4140d090f00d05c18400c807445410b00c46070300c0005000c00361800c0d04c100002000c50038454015038002e587c02e1800524004140d94100898000381c0c030403207170160425010400c06078240070f01500b01c0d00c0324019200301490600c4094102c0c51030300c90305502e001c0c000c501c0020b2000079400100300c3c032030010640f036220034400740010480c0c80485084001c02e00c00e00020074030f81b50041c001341d00c0f250181c55030310000681c208021003001b40c1c08811541039460310f00c00c1400d91070030b0020b0300142c00035800402d0b1054505003005900030300340d0048103a03903548010802103aa40000c6281d005021b03070404417044d03240e6100480385004190031040c0b00500384a50b240006110031020014a030194a0410003641c035080b08030290742c401e1140960001c42800140d0100d40250b11a040380000201201c0340c408040e42c4800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 525648318 1250 525647068 525647071
    0xb100b121f05130b030c1f0c060b0a080d1e08070c060b03030c010b09152103040f26011e18020a060e19030b070c1a18070602070b070b09100203 63
    0x2007043e03456a410344454182042070550402d400c80d100b40c1c1c0e2012a40644180b0200440b480c020131600390025030620080e9803095030307003a0380501030405141e00d0b00d101a540c0d0402c0031030200042c82c5c200021701c025000c6540d20185a00640c0c907540349480b4510b0842e038030034000409940c05a66203d0312a000d07902000201900c00343c86002064140b0b8040c2003186074a4000c1c4041c034100e4404030500010b42c0c81031100f0540c8030311118282d9a0810000090340b80d4012030f04003a5040030300e034201241a002c000f0f40918091034840e007000780002c10a43d4a42030350000f0071001c0f400810101c41c00c000b08c1e03141d00803c4100600034000842c0c160381d5000070740840c036507600c11000702d0080ca0041d8868140040c0c1d0b0030200d0702c83c001c491030151031683d9803000c1c8a0020724070820004048502030402c40d17050f220500e0708005030a090040d042c100c1600c0c082043c560440322880c4590000040d0303250010500404444070803951500b0048103840728008200c00a2200815020380c070358001c035104449c8060f5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 525649568 1250 525648318 525648349
    0x70807020f0a1b050301020c0a0609033b061801110f061609061404180b040905010b03010507090b030402090c09031605010207091116140a0b100b121f05 67
    0x781d802114030024125000f26401107400380c0d004100c07000e408207001502c0c00703040703a004800180480c05401c0840d020044004981c2c80c2d4a150249400340c2c1120840c860a0500580c1d9036140a007251004c010451051803d41e040c02d0101401003091580148100840d00c00e0400c00d036483d40f0010300e1580e0600d0f030110761210020380c070703505000d081345d51148100c8042d10007420aa0021210201d18907000d01031445043c4a030380f070303040503840388203400d030032000003098041c100b4040a41140740c01d901800340d1b41c80c854000d42c41c20f4009082144984150b0040b82c01d540000e601e1601ca030303001c1c0188508024640444034600300130011064401b000710b00c0392055225941d01c05181060002030500000b44d104104090501002c0c210740f0841200319040c00c44d4507049100f011320780d03180c41c0a48801103000c83c20340e400b41220a0051050440801c0d1190a444144644d19a2181440802801142e0b46144800340180c0010a0301088192103134a40910040560705c0b01e80e15400504000c0651065 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 525650818 1250 525649568 525649583
    0xf0c09030510060b0418060905040b3106090c0e09030301081b011b02010201060b3903030613090f03050a080702061b0a050702042c01050609070807020f0a 68
    0x100300344807040c002c03402041c440c100c0038030009107812080010341c02a40180c2c0d54502014040e291441000e51050000740b481450a104500d49401c0806128030121600303c0b0035007810404000007265106981080401151441d41c559426180d81d401014082002c0b10380088150b80441c2845880344610703c03401c0c80000865481d81841d05150400c0c2858002d50520844400115421780e004205000020789001e0009183c0e00d00303000403409002c0c107902803051b2000c00900d952480540d584020500448280c54070141c0b007503800407058140c42e84003a01845d81050010603254a004c084035981525244004074140419403102540202228070840100d0000218001c00170340281034242d01203e9030001d8000c0e4680000511507810306110840d2042100095400c80f5078080e1050300c0029801902c1000003505280c0d4407110840021024890200c0c0381400e9200c0f8101405034610401c4040c0c0100b000ea101d0410a0720300400250002055001c0d003a181d80b15202c0c100010700106001d0b00c030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 525652068 1250 525650818 525650837
    0x11103073912020f0d0c02190902031506030402060d0e0708070909030807180512010e030309010603051501060c121209031d0a08060f07181202040c031a010e03010f0c 73
    0x20100781c44040342c0800700039500204002c00b0014000b14074250141d00c541030a00380c0404510000b01e01d00300b03000b6000f12813a002580459030340c0031a4041c501c07446407640e80d8120700801408003c0c2a010458000b90b2100d030410540521030902c0c0c01c91408044094102c9002d143c84003403190610300c00e43c020902482e52498403206041d800040f091b00041c0b04d0411210fa4900e0718180d01d00c000c0039001e1540142042c0c1e92651001400754081100100c0382401d0740d0b00c0e82000d042203030190080b803000355440d1240e00d02c40041510302d00c01c5d9604a900315103c1c0d001091856954480300e250f01c03425007061280340000b038401d0405e00c2c05110300c00c52003660381002501d0764409d9007100450380742e41107002d24010f41e41803008280c0010100d401488003a440751541c1c2d01c1c2c0d50700710346402c0c28001c00740420190b09000162040300a86001505100b00c8080c091581d19070b03000c0702140c241080042d10001c4200f000d4109501803826141d1814028001180c08918819910181e4000280810004200b05c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 525653318 1250 525652068 525652073
    0x20702120d020619091e030908011505041a010507060c121e0f06060203070327080618120a110a0b0c090a050616121704081801020111030739 62
    0x194004d60750048a508000c2020251a22981c41e0100307100c5900d00000540d50401b0706000c1d14000d0010a00c44000b405000000b06540000c00d100c2e2092600690401d103041d0800c88450b03c1000e901801030390340300e06141d095203e100250030400035810038000c14050004a40301c05004000000b584100c3c0c030076031040c0051888084409060300d05030350602d070503070500030a503020080710b0140e50123242c0031286071101c2c4090300307020030000710085802c0911800050010808546180318a018110960070520b0303059503035455034a84440c24401c00020002108a1402070072140071300d0303060358102d03078002c44280d0f11805d00c9042034034040303a403000106581c0124681602d001020b091305031813542c00c2c030410001c242c1410100b007400401c1c1180c0a00d80c01c1c0c01074400c0c42040d02c0281020600800ca00742420f02244035170140301030f10050320203450380104035401401000c22440b020744040340746650301001203502c40c003003c400d858032204075000d03186400f00c1a00b0b2542c100c051400303880308034460352 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 525654568 1250 525653318 525653341
    0x2310c0f020c0105030c0904021207033603050a020f0f280c0312050f071109061206010e0a060305070e0f070c0f0f03030908031612060305030d020702120d0206 70
    0x22032040c0c1158009988681241da10109036500b03c10082103c03500d424030707140098082e0084901d00b40031983d609040203a00f0754035800203002c1c8070110340340a41c0001c1e6401c0c000b0b0300314171070314503100d141071080500710009100c0ca0082401e8003544c41901d44c0103070310886ca10f081180c201c05030905a48881c4280c04070140243c6a03010440c0e840400400c5c03400266125404040d4912020b444080440c1c0e444103100c2c014070465140094540a03107944000e945082c81080c802605444e00481150f00021118100740030b154112012050040815a10f052910108160004c1c21400d40d25101c0c2c00010000350300b013001e00050600d041e145142841c00900703502100b20300407e91b9040016403c4d00d04041401d04080122054200d00e04022840c0541000d1f000f5004c00300008000305000401c10140700b1b0303504004c1416451583d15100070180c01c1c07103640152519404060282d40017004610340d40071481d401802c40701c0c800303020418205400c001250038811604175520250f00000200310850001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 525655818 1250 525654568 525654587
    0x8061b28080a0612260301031506050603090c042d0501210807060c022407020f0607022a03010207030215060d080d0c0e0604090b011b0f02310c 63
    0x10344020443c0f1407400c011210329002d02e1300d000e0556080c0070254070080540c1e03450000c1011581d02c0c220b41d256502c1c03408541400f80600e006d80d07560701d491004619850b02c40d08680c021400b40d4000d01a088480081200400008a04902c81602901c03090800d00d0811241c40c610107281c000003031558980003005000c003550b001a551600765481e1420002050300068605030350b0408000183c1d0116840140d01d4208020904c05042192a0242e451041e00000061044400e80d00707450070300e100104003d6980e54203541c1480940c0119607001d4141200704a0000204180410358862004107000329003260310404041e00107030001c028058402d040300c145150010700c2660b481c0c40c159011b031a0b45034540a410001041300c0e4460070b504044034810903121090303a00091240c0c2d95075a5622404000f481c0c00c4610901240f1a100713101f640a89940188c23000c190000d44800500b15070b50b0800c010740c490741180c200001e98a0112803040c4c800d032001d8040c2c0d10107194000644400308840070708121203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 525657068 1250 525655818 525655831
    0x130e01090b0a0e0906010b071b09020903152809080705030307081b0f0c010b150a171b07021201060e040b010b070c090e01060b03190b030708061b2808 66
    0x15034505000b02c613600051002d0455041228540d00c40031075160003888001c01400388035912200000201d030501c5a03900030840c0740802c600f1911014645005019507030803c560708200f01002c0c808004a0114501c8041007041074020001200410b42e510030001d030f0054a810399107a4400310800400c2070300017032000e41010b9003416051608a1540019805105800c1002ea5401003c503607101080025001a504e81a0040203500c10810b50000ca16035a00a000c65000041c40011b4009ca00a40703039070013501038084011820704903441e62140c01c400d036100010403030704600241403200e0701010a1181001070070404008000034101820640034420040c2c200c4841c810341003000c074001803026032204007200e411341e0002c646101400306050040c101c0c0d9004c1206c0300d000104100c290803000350b920008842c880410451021a4004c0c9503a8140c00c0c0144a0141e000d100402d0154908250307150515903190320a40c50301401c024000082c03031201c40b051511050b201d4010190310380114030030350f2041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 525658318 1250 525657068 525657089
    0xe060d0f09060e0708100b120604050a03080601050a02070504020f070b0c031b0c0606040c091203270602100b04060506041706070f0903170d02030708100e1b130e01090b0a 75
    0x174100a12251070703440107140034840a6690b00620b81a840d4402c00d4290481c0c284291150307481e00741010b544415200e0801c400150031400003644540c0a1400d4400d5915998001d0079403030f0504003440003c0d4801820603110040c2031092000044c102050544198070403121103859040581014522884210105010840501021148031000a000f43c0d0203a07040f00c010800c4204d82d0400d558640c3c8503040100310380c2c1390006240505402000240701444400b900094018003840780910f041020702070000140c200c102c10301519043c0e60412060804000d000240313840d43c80d800182c15600c658040c00c442080c0c01c134140d4190600b80511540080c80f4201750121280400d401400460310340030042104086180e0092400180016500d00020310041190f40c0d05203084080d0081404851100c0008101c840115035015041c0000d802442d5070000440b00d01d42d80090f0015540044d8a640c0c480a80d411002842c41440099a170080102c800000b5035201c41c641405010440707034000c0c2d074121 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 525659568 1250 525658318 525658333
    0x6081c030b0a0509161101050a060503150601140307020712061b03140105150702090f09160f0b0903101401091a15070f060c0f08160804030e060d0f09060e 68
    0x940b030380740410b035100d0b500c0040c00346103c0381d00b20f0a6504030b48052600100f07600c0c1404001005c0401c1c2e0202c001e2f07038411012a042400101d10308100390340100d4000740090440302d010440c0c90808000755402c01e0080c01990f9049440d0140d400301c02e214103801744d560740d80311107829000001018903010102d01d18a02409000070440380c0e100ea010042c0b05660141703140003841c8034a540c01f0300c181c8203071a030300034190141814000703642010501c040c1d03480031141c010500070400603003260750544100d62810411084461031f00011003203981015011030703050b00408042088113903070f511840c0c400e100013840c000038030750414294074112a900c2901d861030480d10007070340f141a61070703584250184902d031800603601c60351441e1150b445031440c00020506c90602000b00011030300700000724081140c96549000654034641818001183e401e00350300850402404100803a100368040c1000d11005040d90785040030304040c80007240e40d0007601200081d903c0084008210050064200c401800c01c001c010342e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 525660818 1250 525659568 525659579
    0x24190507050d080912030903030412050705060a05040c0305060f090d03021e070606050306010b0405150403022202270a0b0c03030a0e0a121206051203090103090606081c030b0a 77
    0xb0384441c0c07a940c9040c4190000040c0e1141c200300070301a10418250f1105499040c9101c0241e170340d410950701200c4601c643d001513803503140f081e000e50318100d170007400402141e203603084405c00502c005041541c8160300040048085401000114080c01d80c1c0b4100d0320307481c0b40c0240c1090410b02e0b0b560510003014010000f0441d0341138840c40481d02c1004d9040c86940c0d40100c1c0c5442c000621040d4411030700340c0903540000401e4071041c40600201c43c0291004460884402070a4803244102d01009600400710644800c50050945041142c11843c240061401c429040b4032410710b0b440c030041e0320040202c0071140c562414420644001440346903c002c0c20400c41c0c54146860703000050041003083d6440f500d419210702d003048103141e010f8103e049501c0034400751034002c0c06a24404240345199042c803100168500b0004000a415000203000c1c5040c1440360004401500c1850002e40d90700307848240101e980a030600114485568600a144101600110203015104001104c030f00c00c2c0b0149400300034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 525662068 1250 525660818 525660823
    0xa05060a12060e0f0f10050703051b1605010608010c1101020a020c0d08040911040303110c06030c160c15020615091302060d0f020903010b0409050a0803062419050705 73
    0x3003459110b103001c10316007494400c403860a044560003110502c00c1c142283c018240c041600224121654420701041d5524082070382600c00681d2203403245100001ea404000d010030000e03110400a400007810607048a80b1010300350780c3c0542106401c2d9640e80c6148402d0b94104620300e040e00d0201c0001d50402c6000d40000e922a21000001750040d4010724000c410484000c0c01c4030b01030440303400c0401c12455001840c24881e0024002100801c0705c810643e00c0002c000a942910135200900c1d05280d6640c0841502194001174901d905490036030314044002030061092502030841004840076120421000034513260003e0508940000907006001c001d845800403c0d5021203042c021518054080c40440d14510440008039020b900d8000820440c11654000f0845204200e0082c041d00c0701c18020402203c81003c1c0c000c16651000081000050003100035540c0403400030b15888100c0003911085880032030f004c2c00b030384c0c0300c0100280b50145002e0740414160080c0c868a010b50034aa415500e1b035a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 525663318 1250 525662068 525662099
    0x4060e07030b0909061503070b0307030203060a0605070c1e08070b0904050f100608100b0a0801061e093303290d0f170a05070c0b090109030609020120060a05060a 71
    0x880c40c86d00410240d583d403820440b40c0c00802102000e10707924905854020000d4005503843e0b071140354007a00c0010807504c02c00c20f4681050b00540e03d098080d14200441c100780b000514490307107100e5203107000241010240100c500420320358010b82d5407048070f0700801c0116a03000f00a0721034401c050b01401002c241124030207040d120700b41460306240d150045c41e503010703601a0f80005000d5000281c2501c181e80c2c08001a412900103459070723061241107860707501851017141103820008183d132008021000c0c400c1c0445844440d000e5a800c1828260f0640316200b0348500e4602010036101d050303200c0742004d00000c0c1852114102460301556004000040003c19000070243c10803020102d82024400d4440420b809080d503240025504c108403000544690003004055074075400c8140002280d001c010202e0300600b10580d18101d1460a59541c40e0051012550aa04008a000e010720050b407007035901700034006103000101400c0ca00307030803910b059131401000a401240154410041da600300031600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 525664568 1250 525663318 525663331
    0x606040f060c020402070f051e011a0d0213060e0712060501050f21070c030201060f08031911010212040b0a0b1c05190b071202070c030602070203010b04060e07030b090906 75
    0x2e002200d0507000180190007080e00c0903241030b0030400604104480000c40190340d04048550317881d00404400814201c80820704080c6e0400703290101e0680501d000f681c520a424401840c0405034605070218000f281e02940102c900c5440358020701030307041e070058100c0651283d112000d02003e070900300004c0c298014000007403160034001c20405c03844900c0080038152038100d29482c00c49031a1142c802065141e050800f0340155103031803004100b00031002d080c1000d446900c0000c0d450302003500c01008542d8140700d01e800411a46510f07c0c484d02e07000f0b0005000c4120b034000f4001c4582414207004a03451406002a07003414a00b84002d1105e44032030000d903003924900c9008110144090521500381040d001e110300c0411000c1e02d50200300400f60020390301800d801da44400b04403100c140020b040744145000980204044032003000094044e4005003002407015002054549000c004901030302c1a075045070889682850030480b51940c0340c03041c4052001c0071940002c40c2c3c20884880c9480341c0f00138000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 525665818 1250 525664568 525664577
    0xc051c030e040513151e02131203050d0c05041403060f01031e150c02010b10230f070303090204050901200904060b131d010e0708070e041103010e0606040f06 69
    0x31300340020001c04440c0c1c19000a4004c50100d107211020001300006298401a038007402c5003035140321000d109039070215003202000807641d82403854095001041840890810030b0821000a00343c0a078015030341800c0c4a03445140d12142000f41010031001c1c070002c1c07140658042800c000c0c01c086141c410740d0440345c102030b281c3c107203036800c212000800f2004100545008914424400400b540b54800c000900107607008200c1c83c5c01000802a10350031050b441c00c000303003a0460706580000d0201d412003041448041031807a00358400303000c1409400404003500801d41d034140071800c1d0b04243c040c3c143e01017850070003007181c0f10391415440d401c0042c103000d200c180c0101090300c00e103a840390b50100d805450000e001e5500d54030700d210440984c05646c000d0408100c05411201925060148114140d6002e910641b55640e1400c9003200e007001d000340150204629840011919181c511950340405103482003181c1d03943c18103551800c6824040c02c3c8600641301000300300100080c28074000103071a4689070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 525667068 1250 525665818 525665821
    0x60304030806100e030d080f06060a02070e060a030609030e01030c0e06070f060e0313092a030b1813031112090603041a131a1006140d05040c051c030e0405 68
    0x401c42e042404d801880e40c15120383c1071381d8400184c005400c648102c0c0c0d08800c401003903035040180040b9010b61210440580d01542d0144240f030003c040940c0d100340f01601c98014030303a480c3c89050696804c0311069010030044400c01c1c20551f07040c0200e80c41440d0505050000c0450080400e02030300c2081d401905e010103509284c41000460741061401680c3d40c0c045031b4072660316a00c0e40a202420707104142003a8500414501703000d012042018841e200464201003a07401c01038140c0241510000c51039000c072100005101a9100e40001800381c6d0400c1d110303485031042c0340b4028186861101880700e05074032840f000d0010030b0310841140d8400741c0c252070300b075203d449a00c2c201013022540d49038200c000c11007208105c4512401c900000d940350282d01c2d00d2000d844001d605807142c000a0f070703400c100380e1041c5405000050080d8000d5415503184d441151610b50014552801ca40080d64103c0d0b00800d00d84003000301e460102180240c042854820484c0c4003681d80e801340c02c41d0751440d4868012a200e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 525668318 1250 525667068 525667099
    0xb0109050f0102011b180e06030c04020f270103060e0f070c0311101a06032a070203030c07080c01022e0209030f0d02100e06060411091201050601080105060304030806 73
    0x100440304810070240d845c032140d500b20101070b00c1c0310212007a1107451000000005140c03481c5500c200d003c0c0c20054050140314007c0814032000e5841556921180325007004040c02074260440c550160700022820110550012000101660225809110703202c280c4000d1000303000c03441030950f0f0019194100700507100d01519042e20389110360b182410b103d000d0b00c1382441401902d6009003a150a1214108262038021010071030030340001d80300360a4400c891032141c120051080200d40007240ba0002a07410050310742e00180c9158400c020b4200c458100400030085e50908102a0941a40900141c040d84440b0102c0340c03c11030440080d0f004003004c00e0300e28100907035036504070f0384198406415541420b801082d602c0d903134800c070015040140f04e00c5074076011543e094410f204220607580301804c03407901c0345002c00020f0036684012034020f007000c0203605105d0303842d9120403509100e042c0c0049014075105001610000d41603224078002c150800820000a03400300c64141d201e0401c80309903250001c46d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 525669568 1250 525668318 525668321
    0x602070b0c0f0a08040603230a0e0c032e0915151a030f09010c0e010819050115030c020d08040201180f0f080115030c0501121503080316030b0109050f010201 69
    0x9070310080b0341d00607008043c0601410000070802d50f2150b032406c1c4424058203400c004069501c1181c2c0c0e0000c00c151010480510382c60b040809406030120807905600c030072000280c101480d00d442d00801850b41c0b5540018180803002240120360364200800c0b0103c810349032074240b540400d40f0301c1106641c5000c0341e001060340a100b1030180a03082022803441801000d44100e942c000d603084100ca080f1032002030000f1005001d16400c41e02c0e590b8030020255000001910103e402030003002043c03000c94648401c0740d100344905402032020b03542500300c2c0c000860003d070441d035000c4620021500200c05061084c4e030005241c03500300783d0a20384000384071100c528130a20007003590082103262905c0c83c000180c15040c4900802034403102c1c4001c01001c00b4015401510460070f01c002081a042c20340300300410741c0140003085e50400800008203105560540c00b4981350003540040311045000310501007580114002c0d845045190300381000748284450011700605168031039144030782200c2c20301c1e81859100303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 525670818 1250 525669568 525669583
    0x506091809030f120f0a110405130b03030a0215011509050f01020a0f1b050a0e150a08030a03090303050604022a0a0803090601060f05130b070f0f030909050604060602070b0c 76
    0x1402222903c1d5204d850720812002c000365640b813000113000000c01d8003e01a8401c01c4060000444024601460001840380003481500300e901d419540b507000350f4080c0c509000800015103150b000c0c0044021009010090b44810303000b40300c4c01909820200d41c456044010f4070181d9404540d5440300c000c21000403850519400402410007075000070400c1001000c05e00120307a041030008000350a030700c400503c00300d0b1041c0e00c074000520702c8800216154035035214060b80c0c2c600c0c015000c0d052311030300d551016103194444202d01001071742d960006824164144180d540081085070203600d0000307040780d124000380d0318003010b1030301c4c0101800c1d0040c00402000340c405525842011240c4a280c1107a40989403c0b09102d02008245400742c11180542704800302d9a15441c4a016540c020341042d10011003500298422204c41ca01c01501c01c010451140066450368826901c00f1101420800f81800b61140601064002c80c28050701f44406500416010240c4500f02d1600b601c8850802c4803a140000c2c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 525672068 1250 525670818 525670837
    0x80c0c120d2c0c04091a0601030b0a1206060e0403051e1b01050f011a04060c0c05121f0e210702040e07031a07080609190c0207050a050609180903 64
    0x10a4092101c1d60500d601100c01c6110012003a504881402d1040c0000ea03031034914010039200d61202201d003203004903c2d078240c00410616000811000345c2b400b04682141540000301d400071a24900702c1001000e000d41c0c0301a2140d00c0d11903420703040990b80a8020f0088440e100740b41414020180c00018082040c1d0701c0314041060310340d01046024a00600810055400351005554034001040049030f80407206c0c45411280781d1b0519191a1210440d44603044110450300102ea0f800d0002e0196181901086410701c0c3e98042c041e10610701003c51038000b49a0f4209a141d030504045404509020840101032a10024155140c07500c82000881c2d911981a0081d0b0140c6440510320070f8207800180d40701501c1c81384c01015074246028480d15000b00c42140c009000400d0307180064118104078540c2c03030b004444411803440051001910000751000c016035840143d00055080001f4607040100d0030040c5403c1e50381c185010030303280128120350820101d9407800d01c1c01001003050100104200c61160303a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 525673318 1250 525672068 525672101
    0x4060c020c060313030201050a2c07090213090b03060601080a1d0102120106090e0606070609061e051b04030503160503120703051506120402010813020a0305030703080c0c120d 77
    0x50944c00f50b43c40780d0035080d001d070b0041d860580022030900700c038480d50300d030141d042c0020140302803030f281c645104012031240c40d0745500a885000900d80c003580064000070b0041115540c407141003088131000c841d02e540200f0b1103540302c042845240d90300502866000402c20030b020030038452800b0304490006106241c0800c43d0302c0018031040004403407181d107041c1d83c59940c0f180030941c0c3e29403080303d440740c069610710b51003a401c026180014013541c1c0600c0001d849814045211082c400018010a00840800c165261600104803903502c0713008542803c440c21000d85400d160854850301d46c0ca001e100440114013414451000c1441380400a840401400d03000c0c0340894500307800c1c003e005e00400e139407102c92084c1420010072940b90010030364140c96000540a6103d5540b6001103620140240226915280d6080d186016072510000400518007840003551781e0001c518008000c00001000503070a84000c0c0041000090081103030340f60034070a942030706d4891f0030180c100c00060400010b12480e41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 525674568 1250 525673318 525673321
    0x1e0a140f0103030801060f021b040605060309010603060c034b0e060604020703020604060902120f030405030c09060334080c1906090603020d090b130605070c0b04060c020c0603 77
    0x461011415a041c0c0380f007507690184036640c3e50b000b5154081000c41040260b0000d0010b03000c83da64a00082c42c41041c0204046516035a447c049001e80d4002c4e150882542d454100c240b05001080c01041e030324068038602007251100e0b241e01c00200b10b080b10300340400440024070700f80300c562001c104402081c2010546040303150480180c90f00402c10016007084c0d0b8003501c800075810303142500c00d41c0c1d103140d011340141560350780b15034604c0c0041030301a1040344d1100c050f0700280c40b40c440410003410501007500086544505000405250107280100107108191807010003103292030100d4070847d0b842c034040012415091407038428542000c15604450708103008040003a03400b40021b5600e44418054807944103031549205000000301a5005e4400420380032841008018480c1c2e00608400300f010f2000100c66103c2d0341c2e01740000e5415924039282c0a0403a0f80b0301e090100e14030815400404a041541800c00b165880075602d14004202034106556010403800841c000c0c8010801d05034000c00d04c03030741c0703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 525675818 1250 525674568 525674581
    0x90405100303030e0d1718070603020408190c03030f050c0613020907090311010e13090812010801020336010c110f030c0c0f0d0807060b13051e0a14 65
    0x10421034071007a00001d040c00c074413041d01e04020444001c6040242d8480d4030582c0240001c0002d01009013065401501e40c9200c2c0c517019809100c801c0c0a0081c660740943d84a190a65041c50030302c003c180c0c80070306a41d00303569000080c0d5190703580084a40c1810440040c00150806981c1c0d40101180b0703582a001d000c0c00c014050405400d02010749108a461070364545136040201c0384c080d401c0c0802006500c910781502420341c041d02100200440042c6040d50307405032022090203441981c00b0440d00785d000070607440d54005801c80601e0140c8040002107056140c076402c0c001c141910f000400c1401d01c0056585e2103860450059024200d08181c0240845504044000c01000b60750b203164025006410400c158040c0110440c0d01d2078413072200400f000408001004143c03d40c108030280c4c407060408044c00020304207805004424051400025030078410ba050000340307500c05d004900524902010030403659030b020010008040b0070b6080c00c11f075550700c10282000340b0004290300740350041d6004100c070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 525677068 1250 525675818 525675841
    0xa050d030f171005210a021909021207110d020309040203070905040513140a0c0b03060315010b0c1203010302060304231506030f01091a040510050103110301201c02090405 75
    0xc0395402e90700300c09110701241c140017245001200402594110400c0440585002408180b904d10340140300c00a690f0780c0e0300c0700c4080b03900c490046200148290100101147c0114281c41040444000384c030046c0701c070701c1000f52a4801c0008152240d503004c40810107d51164681c00060100a0410400c50405424030a0010745501d011201048140241109010040b81c8440400d0340822a110782c507080505d0740000c0d41000349810b805206032061050b00590b0700c00390314000c02801e400c4555441d98420010300b080c008040d2400e82034010001003005840c0e41007107a9100341c000c0c020076000c100d40042c400c001401c02d0303c17403001d910076505072070428500400c1c09401140c04600b01c49070344489454650036514408805050782c0000c5a00c456800000c0c014190b0080c0701c0c3d4142c0c0c1c0f201c0d01406040d4115a8281c00c280c40028101c011381c840740c00d0900c83c91030100c01c504021484001c0790f000c008442d101e0303c840307460241840f140301c1d4002161601039079260707140140244400d1030b02125040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 525678318 1250 525677068 525677101
    0x2040207031805011d011b02031e070522020306010909020c07140307030308040f0f02031212090610120606090f02030405151e1528050a050d030f17 65
    0x11502820002c0091a03600408440e0240004081104020000f040054480080305420b040d03030300901c8020480182d07030038400c100000c074010510b0350780d0b1410000164a03006154100c0c0380100790f90703c0e50034103240000d81c1c46200f1000000c0050b07038940d00c42c00102c0310035032070798056410240041280f004500000c034500056076000d00400c0c1109481404250340c074061884080e000c180c1c054040340204d4188440c04101d1801403000c070301a030320385601107481c10382c0780d6590224810b400724801512242c1004096000b031001c1d0020940c41c10410b1032540b402c42039205420102c040910640108020b41d04220b00501c0034010412142080240c031001070b42c000c4a00b110980203940134a0050801c41c24031a002d00f91101648061186030520001a1000902700c030140c00d00c2c6044008955881110000f40c191805650411054a10307200b01455100f5400c5a40300300074600090013151681038410800d2605440d1040c1103e000f80c000b521240d864140f00e2064840e15030400004150105111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 525679568 1250 525678318 525678347
    0x26070f090c090b03070c1a070807030b0f09060609042a020d0c030c08280e0901050a03170d06050a1413020708070209040201030f0c12050114090c160204020703 70
    0x1406048210542180c04440070f004038141d0700c40500108949910031005030280c584a004060f4a5110500000ca89240200c2c2e007280020320704402c100c1b82c1503060194043d100c030306031042178481d80140300103103215000805a9014090100d40500c2c181e41c0c82d00320760340766072051060f00c06000405c000500605000d0a0740e8026114407998120078511440010514030b80603071b11aa018403159980044590040710540480f030003200c148101c9800a041b00140050262520710003e00751400784200950140d100d948544410071080003c140e850f580080c4031141038001c0b035034440d9042480340040509821940e00000c801e44080381170010300707a480111007800c8890889071188400c8030802c0e4030660340e000700705107810700001d8010b040403c3c050360410300c14100800c00c00d40388140e65088070b0b203d00c0302c400000d0b007900fa0701e00b200312070b84102030240541382ca11004801c0060f02003501c43d080a0681a0f09000c002480c15520340341c03145444010350b00510666940300c050900508004600e50309 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 525680818 1250 525679568 525679571
    0x2090604030f0512040e1303020109021f12020a020d0e0a12081201090b010e0103020a020c1309020a0b03010e22020604060f020606030106031113020706020f0307090b120126070f09 79
    0x12100441c0d981041c1c80484011509112a66070340e076280300026162107c0403001d42d9281c0401c80c00681e100710110501f032040140340301d020169002c004044008444254000c1e510420111444d95408543c605120b4450300301149065081d601142c0081500d5001c0fa1149110215038020018507600410412005043d5141103076294000390040710076008540d80840c80e41ca0752100e507035000e5005007013540b00c6070055403a074010b14008661055254580156800c2e40c0f42c8c074800862820581c503502030012600054290360402c801c1c80b2900c08003506501c0100402098201d640c814954441c011640c09003003991920356a4070064098801a00c00d800540030309030000320141814403811017229000044c10700325000200a200343c2145442e11068401e4082107800003090460000304036081100110704e5403031070024801040400640c00c1944106010018248040290701d000360540b0800c0f8025a85107044209100b03007100d8440b00c5143c18024070304001490421514550111421170b0030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 525682068 1250 525680818 525680833
    0x20309060a02400806010510080c041a0705010c05120f06010e0103020a02010b0d1a06061e090604080d120e0c130c020304051201090309050607050a1502090604030f05 73
    0x200d034142c0c060f203c00f0f41040501d60703045180080d04005030b0f1141600714050080b46552402c198491500990007107150313903000400401a6041407101000e640e203041c90700c0001828403c0b84170000d44510712801c02c0c15070000e0b14000f120380341c403012102e55640c0080200f103a83c19040b8058a9078114000217055180203200040d640c0c1c071241550f91107508140d403070f9003000340e401005500030b41041c0d2000007150750764515030260303480f0a0500c4c156640203541c4008883c0300c003e0256403460700181100d020750301c1400003005002251003074004800510300e026440303220003404a0014029540212228400e00b400000322540100c2c40350541011000c0a1001a0803540300b44d55403052028030700e4000000e20b1000b00c4140e100c0d40103202801d003601c1641d14040c0d0310300c0001c2e02d0307814030909034045964500c0b11100f01908007021000800e41a60070390304041c00c5031612a1180c186141c0540070441d040d07800c0c01c1900c42a030440345800001001c45845130b80702d040041d1020b00380b00044800c1d104180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 525683318 1250 525682068 525682081
    0x80d0e010e091e04111207090509150c070f2a050a05180912040611060a15060503060406260601050f0303090d050a02030703140120030105060a0c080703020102030906 73
    0xc0d401d10940c00090480c1d40c8142440d60301142c0381c0020001d41c0c40421703034030113050700340d6450790b02c0207080c8218802030901e9030501030303910101c5201038584402580180221040c01c0256000d56600c52503001901d6181c2482e42407041004201c1d080080003011204284550708441255416100100386520350285880d40e060202e00d111328001d0907031041e00801d000312041c41030f8415030390004495054074514054201d0384020764100d5002200031980c40791903c20040300400c03001d503000ca1a000c0612000200c0310050264040303d0080300200000000060b582d03884580005004201d803149d900303845500326800b8145000d4041041c0c40c2d50181400009140c85c1180113150301401c010003462034015200b007040304800c070320302e02245c1600a00f41c0001c05690f040c015040210f02a15a01c00c07103a038084581821207131840040c03d030041d0a400781010400c101030641741503c0c0705840c802d549101506064900348000c880051031003900007841002c060341074014600602c11a0110350f542d40314030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 525684568 1250 525683318 525683329
    0xb030c1b0f0718021c020918010501140a020f0d03061d06060d0b22060938031e010b0109060c05060a090609140d020c031b0607050304080d0e010e 64
    0xd10009003541e114550a010003485103c0c1c01c695501900001403400c01000402e03042001c22400c0242419400f007500106802d011001c40000a200c60003410158104030000e0142202c035100b450071401e0100380814003030b00820074070000c00c40380d900726090300180d405d004001d0103643c0106c503d0501e400f202030040d10007070050720b0700680009080500704450080800300801130b06610340c0d40b040030038080d0000890041c5980c400140910804185a810079040e1030030f4880842d00c00c483c50566004d0303203c074188081c94140c200049114980c80d9008510700092811030b07100a890000031040c9100d00140005500800c80c0e1542a201c10f107045a603041e055a95407110040900350341c10240000e0311190580d8000d43e400c51040c0c400180d0021140c45031b0400d000022169001a031100101004c0070f41c0421510403050000c40007840b0400822203003116420b6400704890040d02d000c100c09003080402d0050f00c019080c038004031068030600d44001000a0400b40c005070204820080e100710a0608 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 525685818 1250 525684568 525684583
    0x6090602030f0421080f0d06060903020f0405060103230405010c03110a05070c0b0c031b0d020a06090c0503030c0304061b0b161e09030b0c070f03080c040b030c1b 71
    0x203481c4100c0c28180f03000e00c031044540001c10380c001e0800c500c418000003d86900043d1246e019200c0e980c40d200c0d03071007500c088220345403030b0000030510000c2e03e8200010f0f69051041030380203078140e03000f060544420006801508a000844c000765000c000f001e50f480d079658000c0d610a0b0b0141000b4068002c8511b41036040381c0c900582c03447c40e1441000403079003080c040c100500d0614821701c0e40d90203a582d960107520071604002c0240606400001d0303000d0706003400107174200308000c505020300380b032840142c8060354031042c0c040010140303a29141c1c1d0b082808248411a001810b0280903a41d40f50403440890b900c9620601032035002c0707140e296100c58811008184004410350001d050007481e281d03210440c0380075101841d040200406e2400c11300c03a482004018030380c030b81e2094a80f40d00d146e05500d00456088401400700c1d007402d00a10020002c506081040c2e0b004541500344801e0341d84500c1215000344c401c50700b20005030503001003400040c0d01000000c110f44084200d5400c00340124150309038651b42d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 525687068 1250 525685818 525685837
    0x1120c051902100f06080d090f05041a03010e0d0f05030705030406050a1b03020309010b1207090b01050d0507020c2e05090f030a060f060e010f09050a02040305160609060203 76
    0x42840821844011120007054107001801240d40e0904200c6880c020b0704e00043e40b40f030a4503100d0008000094080286040c003500908182ca031303283c140101041141d15030322846102d541c0307866100c28900c00b1800c1c21640307101d0242c000d00c8240c0100480540e43d0307040303248a000080c041c04105809511510580e400751a1560b2500e103107850716140d45000d00710203007402ca11969180340380405101c416100148040c0f031030310050f0b100d01d060654107084403d5261075602500c1da9490403411131030080303044401e94072032038000034180901000485035801080c01441000317182c001400301b0642c0000700c0e5220303600d040b01c44803204500d03042032170350f00705200c905045079103011003100885500400180c614100f000c2c0c203442080c00d850b80040e1618650301f4003a95090750f6150340041003e101d02507640a44501011070070a945440c0c1e100d0145d404c0351007072100c0569030300f02060401529404941c01150080c003200d031048036650500101344881e200e4040400ca8001c5c002031403034008010b0305e10241 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 525688318 1250 525687068 525687077
    0x31503070b0712030615031a01020f030f03090111030907030b06040b06120636090109020a150504050d0821011a031009020c060411030606100e19060e01120c 69
    0x440c1c0e10000e040c0c549007580f00603d900c0b004d010410552200ca10301000501e903901090841c54581050721700651b0007001070440d0000040c0b801e11032000402c580f0340c48142042655240c2d61000001d005061b8500d0100001c140001449841100060781d482075074040c0b0410141d940720b0400300002c0300d40b480b030b449070010018011081e8140c1c0b4002c0081c0d110f54054100010b1215084040c07102d43d1a808250030540c0c0b1495490103101c4440300d4056001c0c0007500204160120764002645415041c4501300c0c0000601d40302d2801c41c1c1c4620203603001407130090080403140c101032400c0c00d2640c0110f00720b082e6a02f01e25451803559400032841a0480e184035200c4e5001d00100800440356500084c240304035044500c5001580c0c0d4014402000a416010701170308490909250400140c1c403102c610900c00da020009120032a41c40c8021715064039142d04000c850a86048082200602c1144040851031403820340041e100ea00050181200002607a5800951243c21890070854400c51030000004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 525689568 1250 525688318 525688327
    0x30c020402090301060503030d060e0f040302060103261206040f0501050f040c050c0303010f05011205040503040923070f090812092106011206060b1815070b010b031503070b 76
    0x10300305903000b0b10902101a00105000343c407003010034990781c842702e0f55002c0c9544c4e50368100000003610301040c3d0004425031b1100c0349402c1a440003552090180405410300d1160038000d03040741549031482d1f900f4103241c034949440701c10160141c42d51007401c848443c0180d0800032100c410702c409214141c140c1d1030050640c5102c031419824030009051191418003440001c104c115072500c0c0400180d4000c8c40032080082c14141044001001031007841d0f21100034034100018480020008015101990b052210014921405588080070445402152080712038041c041c00607d55100c4020050424a40c5920024641d1881c003203903036200744410145044014031841459141c40154441c106014080d000603a580354410541880b5080e8400c200c00800f10508104004480c00340b0002444090a21030401c00005183e0f040780881c090180e2240c103549000141ca0b2040300143c4e58101c2d08a80300c0b00c210340e124520060150300070703203103162607041c40c501682e800d00e4002084c1c41502e41414842d42031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 525690818 1250 525689568 525689573
    0xa081c0503101e172a0f040e06090111190e011e1d06120109110712030e0c01050c0a0308060a18050114101409060f03043014131205030c0d0507030c 65
    0x260341d174110341c6a03800b5040f009403050607a51406200300b401c0056002e04003a040440c8800e003128601f0446403e8480103200c00c86946c3ca506a90210034411405d00e440e0600354180120340ba00907a1102c18440d0701e488000010702988821022030401c8043c184130400b00b41d82d000c00c1030f5402030341c01050f00500030b01c0060051081d160003101507074001100e19400c05026a0f50445d801c41145251000660340340c20300c4e29924010004061008802c1c280149848600410344d500c90700d044101505229807100407a13201c6c0c4030090144e006160080340e034140b4000d00400c5070003900c4280709041078210007a00790406464400d078500c2856555860300c003c1c01088116001d001d400000505512120078028082e686004100440c403a500c5000300022500e0240c0e00c4551040401d42442c0c0d098a01903400c515030740d0410080c16140d000c1a035925261481c50311680001c00340c40d0040114500c2c085001c40410030000081d2200300b800200307075181000803a000300d41d0b07402503000c06400a100e20740749001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 525692068 1250 525690818 525690883
    0x4050c1902030c0714041b0519030204030803010e0910050a09022e0c050c0910060305100521030405120c010f02060c030703020702190e01050a081c0503101e17 70
    0x81c031742c0c00600041104907280003225249001c211020001c14800140300d0300f02c80290551140d1541282001c604181c20f58803541560b00050181141d850044000300700804c404104040d40c000c0d600405100614040c1409406010482c404034042e2062480c0e4002d01502c02150540e445580c0d000900100d100c000122081145148180c400b4010b400702c0c41801d0302c4a0500912030003080020383c004501d0290300400b2030310010a0580e40c0e500d040e9043c0050350354204500401c1e80d002ca488520030003498040c3e41980f15907849a603124442c00761489040f04081841840440d09882d005ea031001c61070010380e03c8050442d4021a091010030024040c2800390340039145190000e0070f410315010802da0070201500035071700420402a04000104110700c0d02410b02d401810012025056540c5c6010340280380740e160141c0001407050120000d44010380c00600440107001c009509400807824000c1260414254000d8000062400240c6800c0601c0080c4a81164030050803d0103202038004071442c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 525693318 1250 525692068 525692099
    0x1203050711030408010b1309020d021311070b0a14042a091a030106090903050702130902150a0e150a0f0302130303050c010b15070602030604020904050c1902030c07 72
    0x28040d603085102541e600c200301510162012000000d100014902000380c1400100403000c501400c1c000450016260300449030010b581c140d90b81424520000140c00140c00c501c030783c60030110b401161090500414522940c040c0d903034110208040c10300c034508070402a0040f20068000e9410f004e0070310304200b10128070704800352203038090520592140a01e6050760b10780c44030000402c81c0f811011206142c284210002840002010405002c1c55900a8903501500340040c1c402c0ca00081081102c4c1381c3d907017080c21420b600505416001c0c40310400d0580d2a000700c00361100040e4104980030460420f6090306400c1c44502c5512402c102080c401201c0f0034010844910800d03800340725015514032940042d4000d12f209031281030300d07442c21414180c00c44108015092140211803040c60700b44c1504002c49400e590800c00c05a40c075983c4001141c040c0c8540f24403540c005180c8406c0040c00d81c1e409015140d00c1150340d5164040902d04036007260b81c2e0058a801580c07d40044008200400e43c045024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 525694568 1250 525693318 525693331
    0x7030809030d0f050f01080615040e0a06060b04030314030705042312070501120c0504061103040f030b16030b03030d0b0d022707051801030b0d061a0f0102010504120305 74
    0x741c1c03415540101920554040d6000721140c2e07502d43c82801010b2000b08046030241100e20014003051810510041e40c9210f80c510304d43c0516a511021441d208c030500c0907200c000d40041081c40000d80e03802b03c44d19594000e21059001854a44810703010010510440380200800d03915603040908000c0c1281f01d49030307500c006002415090365199819242c5a405086003c030b01e002504410f0301d0500050b118a00d0480700d491090310f404c0c0c40c0c4a481d50010241c0d403e0f50714624100b08880d04460f4840e24611a0342c00110078010480030000c104040000c0880c8078000041030b03002510504c00f0142c0550300150003caa06d070300301b4010000c041103c0c2d4400c1c1103c0d880100301c1c1c625a20745401184c07054000c070f40c400084501c9142a100b40203003401140d50404441e140013850880a0604a180c5103940303500e6a040544030b549491503550b801141d10380c9a03410640801201040b17200da190080101c00d20b00b40034501106e031200f4690b006206141c403039600b0040403d40c4040c164070032002000b005051 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 525695818 1250 525694568 525694573
    0x10c0b0601030e010510210f030c03090f15030b010305040210110309040e0102220b070f081210090606090f0b0d14361506040204150804020f0d050307030809 69
    0x1180ca0f0100300740076060040510754680a6820300388610120f6104015596440b400012400303403000072100c802c6401407603010b2070285507400841c541100c10780c020b90700660411424001c00304040d44507122200000809480420002404000540607214201d8020754070000030b04909140c10701414501c501d60940f002500c0c902051a030010382100c02080c910b200300d81d030105410400d60200f00f100c0320302da0000c004a02d103052420010100e2485480c40040406519040350001c010303450090b1800f800081c81061f07860f252120340041015120710072111901d042640000b041c82c0100e1100e03054a80342643c00c803000e82458210341090340440d1084201503a101840d440340e924100303006014180e07054840441c4012040d58481c2000c00d00c41c030101c52a0609050b010030140080c005180c0c4407420b60350302c817a035590740015009000b241c1c049207074400110f4a07a0002ca0303022010500c00c62088a55072650a0003074180000818101c0700105030340d20405c0100007180c0030b1841d190303000100c1d204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 525697068 1250 525695818 525695831
    0xa150f050408030a020c18040c0627080307171606270813140108070c02010207030209090d020f01020703140d020f070c0501110d0203032a07050d0207090b010c0b060103 74
    0x1c400c1d00e103038444d0555a00580085050600c039141140c8445a00098900901244d041c0768480c01c99050640c030440703041c41115001503408010964403180b45100ca90307122001030b030380c6542c07550700ca42c0039107002c136800076008001d184200740d00416030b5a2032004419100440480303641c1c4100400030140b5500c4114604258040c19020880512056510554000d5100c0946440c45d450507441d64004482035044c4a4540a42d640d000d00d186a1110641c0b800c0f40e0400312900040c0c0c14035001d0740020390421440c104106142074001843d07049030005070300301c9402d40c4110b0051800c0f0700801c00010b0000344082c114081001e4a00c010b44810305040200510780252004043c1440d840701e90210707581c00c0c140c00200059a04440103d4081c2c0c40c00024000740c0c00d80140094882c4001400000c02148035a43c648030600c1416034081e00c02462a5442c0d030b21106030422550315844030201000600c112071011590503164005c00d0030740d0406031580600c040a60380c0701e8401000081c501c0b410940d5440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 525698318 1250 525697068 525697079
    0x60305060915130f061b0909020c031c0f0c111501030c03080304050f191502070309030204110d090b0a0b0102070f030303021c1503020310061a21040302070501020c0a150f0504 77
    0x1c15420b4481c8464400c922401c8151009013810102350300800f2054814009e0310f00c80d440110031a41440d4070940e212001d50581160030001f0100420441d04030f9240c1801c454015030840441603402d9160000c0310103010b91114a146036002c2400001c1c0200e80000c0c082001a08500c003030b41d005886007084d1017414481e640200d190581c1c40041c1d080c0f180c0d220382400d0600c1038205194a04020f80101945044030030b40300500440c0c0030b40310003409a543c80d5001049100100305480420b140c805050201c00602c2c2020014840251f6401d48818a0898a152650f00000b40c89045640c001610035469181d40c90582c0250854170f01d03443d021090311203810280100e4840c2c030b0140c070000c035031240386541580141480c0c41c1d1a1a10300055518000050005105100315070109100c0101000da44107141e1051070201754686000e400c0f40c130354020511040513000305100c0300381d81302070382200c00142c0c54804110039034400303200b14070700110720700490b80c0b00507c664215420200710307080c01c41c5029a0740 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 525699568 1250 525698318 525698321
    0x402030414060c031006030b0913020402130b0702120d1215030c0b0a0f26060303070209041410020313060c021f0c11030f0f0a110a06060305060915130f06 68
    0xf16484894204004100941e07030601008103800b806203441c00300000001003020444c4948040c062030003003010212400308540d1240c04440c44d100041d1402d4007a240c0d5425203440c5500305040891044940002c0b1442907000018403c0080103590748541e407224912141c2c0d40181000c11502d00780c4024240d0100c0030440881c80d44008150710750482e9507800072001d00a00488144044908000c54007441400900c000181060348407061081e5600580703c2034002440c61240090007904100d0050400c020722152428003020303104880c041c0c80e251a400680d203801c80c07104a40758035105049203956004110f55501520304a809801198081c400710390b20340042e0407280c01d440401e5600e800c8060503440d800080c0300c00300d45a400003542004003a52640f50a8081c03d072900d100d92201046802d0154031507000c1c5401d00f0030210680b4242e04141c202440508041e0000343d4192080d500800c00d06000098800c056000074441070101e44c940709120782c08483c00300c1e029600301030b1481e15400820480d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 525700818 1250 525699568 525699571
    0x210050d090c060c14070620070e01090603030f14120702010906050a0b180c0a0305071803050705090f091b040b031c020708120301090f110705010609060f05010905040203041406 78
    0x2a444440c040241c0c0c3c038143c5102c05440c040200301da01b02c2d64040001c03680041c0081c400c0040c0c0d003024900c1c0c404850819140401740c0d03016400c0001420000100b400c0c4551202080e40d000b5070b9034210880b28020252007810b503812000584400402c43d1a054040c40103509402102501c00412010156241e903029103000741c070300b042c406541c0c015100f082c1c40d0441068245d400a443c20740c1c4180f814101034400e6002c0d001c400300901d6150310010309101c1c0701d219034100d01d42d00340103903500c00350f2241400b82c0ea840740390140c103005040020100d0f00084a81c855036100d000d80c0c01c01081d02007003421041340001550400207411a840b684400c0c144d81c0d00744603000324003c0c1882d10100010010500900d880000ea10506041d00050448061600070108032030540f0000c8a01040b9034102c00c0d0484000c00e6010b020780d95642012a2580070070070190451421100002024040c182e01d0302503243c2c3c035081c1c5108190110318080010051400c0c15005194028001c2c2492003040080030a841d052500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 525702068 1250 525700818 525700829
    0x905090709050a050d0b0a0506041103070504061d031b01054320012d020606030102040f091e02040b0c0f0106030f0807320f03070210050d090c 63
    0x141c0c5075092149003400485100109412981444444220b480c0c0d003222100113415041c0c40d0347c6a900194aa84840c6c01000b4400d01d503014003507036481c02c0300c4000c00c540c100c3c3c05004c00041380c20410902e1410394641c0c0403400000103000d050b000c404042010011120031000034144101844004207459000c4685480e80c1c0c020380202e000007d4030703944483c3c41d40c0e8410340408002d6500a0b01c902103001e0310b8401c007800703290540c1403120070f401c400141c2d40f40e00717241c0b080d040d96001e070905680c49441174032030031300c1d040101d40803101c9580314102058241c1c0a64000c2614054080c1ca04008051098000300001c1501d80c801c2c40e04034000b112102c1c1640c2c001e4020708840100043d6003408250100700c404640070090000700030503415a604c0c105844081079000d031820300040750700410b00945c1c1c404500c501c04606040012003ca58000e0404a0040e040102441c0100c5004a10b58000482112180c2c0c0c0d00504545030a41d4207441500c85801071500ba0f040c0c255903005940020b030785600341101038070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 525703318 1250 525702068 525702077
    0x4080a020f030703031403041713080c0a0e2208130e0f0c0904020a020309090126010218120f0d020325020d1e020d080a030e0607050d0c09050907 64
    0x84640180520404462295800383e0302c0b111042000c260f020310b00c4480c2d4000400c030103599071114146a5001004000078800d03c403c001a44444c00c084000280308540c0030400b501c0024041504020344404288030303070640b00d141c17800010015901c40a100303a00141c2d4500c0d1010003002030711141055040303114204007500b58890244404281c001295134401c032501c1840300146000c0201000501541c03000e540902e40200c0c118040c0f80c0240140c600100020302010141e41e5160f5290404489403005500c1c800448220400000c406000311041d40000c0d80500405a08502c20301044001c2d090708540e4502405201075043e00040c403001030882d07081c0d40115140e8403522201421008686c202c03a2a0506442d01c074401030320f44030f039000b05e51508101d40c9950f50300b5035120100c820251090007580b03c6085000d9a081050300d0b005400c0000303907660100300344039841d141180e4501c001d40e08040842c0c414008884002d000b82c0100504c149140760013500300b40d8417030202c0d400d580140c0b80e034401324 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 525704568 1250 525703318 525703333
    0x120a0b120f01020d200f07150e010b09010501020a0b0411030307051209010806010f0e0904060e0a061e051e09120301091e06050f010c050a02030304080609060901060321030b060408 79
    0x1340080c055882c60007002c00d10f0280000300394070071002c02c0c07003440c5007034030030403000700c1c9503828010014000b00d1145c0c0904400d105078400c1d501528000c0403140c0400c0d200d0032044c000450b4030f500c005208a4029440807882040ba01d8a85800c20500b40c07031000fa07980b511081090304000ba800384074031030113a2001410b072504c03880340000160200000400b40790412031800502a9899802442500815400d90301e000c06619642410b4010303040c00e12141302c01d407003200103030b204000b05075100e0340015084650310811500c0c00303000c00c1d0555000b0342d40c0c00e04c00301c02401d01202c00c0b080a1250361f085801d0344110340a22001241055040e00300741d22a80c5081d9598180b0740052a00280441003040006001c0108505040010f450300d0507181955042040340c114880c00c204040003003405a54005013125101c640c1d038400a0b0360f440084882d018036005941c0440c003020414050307030341565030100d0900c5010b003000d10710b03540c0d400c5502001c1f8100340e00c4002045550303d03101c0040000e80311050141400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 525705818 1250 525704568 525704587
    0x70c03060501050316030b0a0603080c0d1b120f030b0a09090b06121e120f04031b080601060c05010b0a0803030628090b0604090f020717120a0b120f0102 67
    0x72644164840c1e40290007040030701030200c031400d962505495020f2040350845d01d850071458001c00040c5c02c0100a80000602811454000100102c0403d081e568000700b82d0301001030840c0700300a07810010592003014240c460450301075513010740384086074580000d206807581c00040d0005007030382c0400389140c0c1d01c0066105201d4000913295101f94183c4600051981801c4100c3e5141054901c5010034040c0320003140500c2c5050088500c10a207a44c101c46c0c03504000f40f080d0b6899841440b00f182c140d000c01800c200b4004251071418101c6d04000060041c503880c0500580d49440302c00000c0703600f55030303d0010400e00c2c1e83c3c0301080d0015003810002503450f4a8410280140700000300c1ca407207808400e809030070161491200209050b41e2540e840071400c2207110002c02c0d400e0040390030001180b400c080040580c488140d0141c2040c038082ca80a407801e503100c007040a4544112000c1d02d04420680700002c070503600540252075801400b030704084414000058660134408003a0401c000c0740d40010f049002c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 525707068 1250 525705818 525705821
    0x30503180d0b040b27060105090c1204060e011803020c19031b051c0519020a08061618081e07180f0b0f0a03030315150509032a04020309070803070c0306 67
    0x9050fa05107080310b150440b40e25160786d00f0b01407184510886551001540100000c810b80d5204c040e00442e40d105414585894409010f41c0601e4a0656107030082083c94120318102d50000c60b0740540140c4050070900e428803182d01c0b515a40314480040420b0004005101010210400900f0f4229200441c1c100300401c010502e522081020b19081c0d8145600420008a4004a0a6040e13200310b07545116900c00704004081540c41040c45001d02420001041012814120121440d079102d680800c0c0145440721154550b0086548560014560003407003581c10007036410141d107603003c07581426a243c8400c01400080080481425116040e000d0860380900500ca8442030885e60500c141c601040414a01c0c20300b40300150825403190103141318054200c5450000d0f21818150307118149801001401c0340d4861600c40e8000d100710600560391307409854104d0070340c2030f00c4581301e0392a403070040400019400c0501f040080340142c0b500094901401c01c014526030744100e0500005501e141842d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 525708318 1250 525707068 525707101
    0xa0f03080c07091e0b030a0b0106230307090909060b1002030403060b0402040308030415090b0f1603110405010f051911060a02030114060a03090b1906080106030503180d0b040b 77
    0x90001d410501d820404c1c0c2030030548488a210300800016541c0103a000007880c0c1409050007401c0b500b21600080b80749a40612490b109a840d00003845200d030320f00075034406501c030460f000c030005850140144014030450700b006090500070078022034031030441d20001d0003051803801d0744805070b44009420410049140200818128202e9045040c01c0c5151a140110320000704028112103036400521400181584540741c0c26410030400c080503c0d1644540e0f0301e001d0280c40400710101c030103446c0030707050b4460300821079100c1aa0301e010b4241441c08005440d043d51918800050000a00030701c8019a400f10901c9031500051ba0303484280c0c000044294140380b80603100740c08003401000140142d005002c80000050740540c0c12642d690040c1c681200242540d0b10028507044d0a036060041c500d00c01c4808400c03000351104100480ba503291040d50032113036684801003040d002071100822910000341f40030000b2001400c3c5c420f040f42c1d82e43e03405840d00b00480c0c0440300c05040c0c405210011400c80c0190 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 525709568 1250 525708318 525708329
    0x18060c0e0301110405091f0306050c0d0e0607170702031c05010306062913091a01032403080a0e030f010e01140103021818190b0c1c02090a0f03080c07 66
    0x21460a810030010410f5403c1c0240941f4030303240c00c40003600c1d0b0340256001680003141c03c104100458200300000802035449020300c0c40c4910b003411101060740da40895141d002d070403a500c1d05000003010000340e848032a002451041980020b00003203401403e984000d440d820141040042c45c0d40c1140340103070882c1c02d5a0405d0301d40250451809408484162001d584112035072800ba884d6100740005000480103034029411060501c0070b403456090441a102c14114802d8900317004080c80c00742902403c03814070344034207e080071211041011964400040c100f00c281440e203000782c00701980100b0302d055000302c2d410b591690746055420f40300300e080c41010120204404000c1d4103500d9500001c4285000030f041c1e0030b8036484000400c046c04000c00b850704c4a0041d28094543d0410400f0304460064542074056800f4401c240014180340d0b41e14044660b107444144044810751402c0c07640350b0003034000003a456040884c42101040003080103080c403000390f01c17424000c0d1f81d5401d40252981440d0907907014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 525710818 1250 525709568 525709601
    0x20010914070909080a081306020703080f0a050919020604081606030c02070b220f0b0711041b0c05010b09101e1505090a0b03100303020f0309030604020418060c0e0301 73
    0x2c4000604104c100c2c3c00328607092620313650940764050040d00d103802e031610082881d440003411004058000c0c00071481a01401c2d07103100e0517030303a0700c840704203440c000c0b28903c465421680c1040203a08100d020390021034000381855060548624030710b803810203001d254484181e0555020882180e06000b10040803d05102500c1207919000f0142850f004600c0c1c0c00380d510801102d214001c200131203e01c0d000344800a0301e58201d5954111164196000d03803001c0d40c03601c600300005000341c2040d00510350f148410440c488920030b9004400c4404480c0900200e27001e54035060b500f040e07643c80c00d8855004682c00100c1d070256900d1f140c490201462460300c134501228150741c0030055840d21502c16025000c031400c040e0f03541c0c048000060800350103034001140d031404c04428000b041e115411043c003541c4c031a8003101c446d22140c0344901c0d0340b4040c0c020b45944c10b81c40b003800540181060f03080350084050701002081e1043d400e030707190401d9412074142034002407882c1000320280e24090081a1100002d50003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 525712068 1250 525710818 525710831
    0x30f01060e13031b02032e1104080703030c05031c0f0e0f06190b0d0c05030d0c11060a03020f0c0c0a050a0509150a0f06020703020411040e07200109140709 68
    0x401910307991003004c0140e03ca075029404801551130505c96240b00c2c2c01ca5840084040b401c044d05440c0c00b16030710b0345142c291860140d402a400c8410400c40d41502c410800a1894910316981100c100c18440070844d840c0c0801e01500074041c060b06034101f6a009000000308410020a0000e4102c51042e045041d00343d001c0e0314035031100c2c0f2000c942d1507000f10302c6540c80ca9800e80d03880341003006883d640310483e4100d14840c020400b0f1002200d0000d066400071802c0d00c030141c6080800b120011140c03400602108101d071a1a280c600d080c42c000c0848100ea4100507061035240e03414a60650080ca19a1000743c0041055000b40c2c60711020100190108483c4086106c0c206400305000482c02040000300c41c0d00d050409545546a144101c0104a64812021440d03242c00e002034984006100c202d029604180ca144d40900614043d1400c4c0d0307500c00003240807503549804c201c9000f0f89070141002d01c01c46131194042101003e0080402140c09504001c03041655403e00e2890800580d101c030301041d18048 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 525713318 1250 525712068 525712073
    0x60d140a020f0a030b010203190203030402030f03040806130203011107061a030f0d08040c0b0412030f2303041a0109020703020c030d200c031f0c021609021602030f01060e13 76
    0x800383c1d10315a44515002800c4922000141d1852245a402c1c12000b03900010b03542140764000b0046110f5442541580c003441e200d44c1c0023558a0240d030140403a640c21000000ea40b030403103119484001030000b0008a2a140040c00700e80d1a030340f01050544130300d51240303801000c104924030203e0124405500504010031070340768594032090796000100402080321301043c18007090010900c081c1803900d00c242d83d142d0303542c01a1145a0030b150411000318503590001c1802d24003030004c3c851141d00301c202040a542c94a00084c6d11580010030440302508140440404413042d20140307406401066801641d56429080107481c01d0200c504641c4694444121440e05560000210130000400310705038940c070200750328035070400440f06011030f018401d803402550422020142a5030400803034004001c074a102650890710340000d020340450301c80202c5c20800140c0940e42c000c1032405c2c0300800b0500b45e00e04542c0080e003418034035946016207a4603a801484220b0303220341120703000600c080c40f540e4001000d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 525714568 1250 525713318 525713347
    0xe190506010501031d01060608180a03201c050d06080601051509180406050403090b19050c030c031c140127090807061b020f0c190302060d140a02 64
    0x50003141c0c1010f0b2920351240c8517000f00240030280c10605402842125101c0307500508503042191080c030710180070a50210004400f062006030103415990f2a0303148000c3d03440c1003034110030300421b60030300b445082060842c030342481c404803049100c0c07540c0700d0b6500c02c1503100d50019103141d904140110b4000c4d50041140f0ba6401001d090307a001714459140c0c0313402681d4009000480040d00c0004442401e90402040180d56808103115600c2900c442c02c04030780707840d4201d0150044c41d00101000d5589002114a0b038060307006480b84040c1c1e07000300c03454600d000a01c0ca085030411404c010003101079100000038030100c0c1c01094800308001e1020410f40d0b01d00410f520305440d40600b14154104610302c01d0b403083c5442d800c40d12050740c0141d84199a80c40d98985440142582d00340d904104001140490b44540301050020301d111030b00d001407d1101c0d00b001080412510824031a0306c12901d0b02e400001030700d134000604000c11501500048020030303001c0c400c480d5500184800c60301407040000f034a841502c1e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 525715818 1250 525714568 525714571
    0x1d2805030d1106060d03030b030a0c050910030308070c170d05040501050106050c030a050304050a06060b0702040b010311090f03071a13150c0809040e0712020315060d031b060f0e190506 81
    0x1180c0d600501400c46c10240d00400d0000c0316550035000300710300c4e94140494198420112282610b2185047c0d49e003400c0184402e00c14040100020301c03410204428500c550f41c185906405056811444151a190404241e1003034078058203481c0c4410403c03060090a10034180104850305010740f0380701e0030041c2c9980303c0c420b800b001014404044041800e004080240408041d8441d00800190380c69a110084a40281404900c100e0901c03101c002c2551190144540c04072142c00c14a0034003801c18100320303441411008407074040c46140d0001848405803c8420000100068196a01c400e0007000d00c3c5440800d410401d12481650302456010340e1020540301420b400400d49074860092000103000781c020081400c2c0300344078401000c03e00c841c04101000300140308900b2128040c1c603c0d40d00348002d02d01161069132144400001c170011a00400012905444215103961090341c5c1d5a030740e60886240c501688000b0b0f54424403200c40074010004c690001c8003070019460600c0c7c480d6610b5548600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 525717068 1250 525715818 525715831
    0xb090103020118080313080c031b1e030a12110c0904110d020a0b040609050a0b040e060d120c0201271502070306050f0f0f071d2805030d1106 62
    0x212920f5501c0381280e400300ba00c020f010f404080d29a5410710085d009980c828a0013810824040e1040861080c54002200c3e904000c1b44084884080d10003030402000891a08000d120b020209900e0f401e1503505102c1043c0192240d05034051180c03888a0050010a101c0c0b052541a400b4810400c0d2903910244015403040e8811040104003034503c012070401406004004d4004492002c0856051050b10241094078402d644810b21f2961f02d00400070240385911420112500c1008180403003542c60342c1c09940103c000d00300c000403506a6841c56054446a804400090358450f400c0c0c0456074824144e0150251004804014030545025100190864070a01c064100f11520740000e482c005d00001c0700443d00001c0070001072a29105049480200721580380c0342002001c0020604c40d11501943c2c0961506e545c0c00414a100080346c080550984ad501a0701040c0c58a944540c410425115030b100b482404600700194500014189080715200c00d42c424084100292410390750001081d039031000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 525718318 1250 525717068 525717077
    0xb19021212062b21050d090302071d010608010605070b07112a0f040c1e0e0a09291c060f02030c0705070e160507020a171006090b0901030201 62
    0x102c2e0a40024415042d48100c1c60f005242c03591520780c940e080c401c4444141d4094020074061200302500300d15020409010200850020301480c0c4641d10f15500c2298490b100f401114111612819168200d050383c0f043e0000b207805901c0107121440d40041e41034014080c40c20b0490030440d0598600c04025802030165040290358007071010203580810030400e20020400c0b82c2e2201d6042d841c0882d0f0040503178000340d8000c42418421440904143c4900786100d9003a03031300c280d5410711000325502c40a401e50032803c100b0803c90b20480320b9540703d0710713004002c00c452840098555a040d0100c0e0098440008420350078202c040320400c43d4940015500380070100001480048266181903401094414020a111440400ac00254440d030700d0080a849000c0d208444a65548035403007000342800315144410503603c241d05044080c060000380220707c3c8010803c0c8000e5485801c6441c40001103245040380342c2c082640d8030700940e018401d4030064132242d81d06004102e01c28020580429041c8070090411 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 525719424 1106 525718318 525718321
    0x10090b0909070b0a022a030606150d0b03190b0708090105070f300b040f020702061e16030804060515130b01020a050102040b19021212 59
    0x548214000701031650030204546040e411010741c600961060094036261492820518510380e140090311130701c041c6c4040205450300714050041d0303009241d039550a00e01340d101c032021220882c51500c000700f2400c0010000c13030715100103900300c0c99010030030000410400800b4011700d13005185542d10406645c84010f1400d0807243d003070390030001052150030304d006524082c6c0d1b50060035504520b0031207445448019400c005901e03910109544c01d648404601d0702d4905481110303407000f4504011400c00040d50301003005846400b514280308000e004034440c40e08011411961040c20107070b9940400d41662401820444055408451250030000016821030a181043c2000b00c0c0050840d083d1030398648401006014008826046004408003100403520900007030005040500c120350b5640480c41c19461012002014802150810303c080c01540c40b0783e6095807110025102e60031241d = true := by decide +kernel

theorem cover : BRFrame.Cov 525539568 525719424 := by
  have h0 := BRFrame.cov_init 525539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 525539568 ≤ n) (h2 : n < 525719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
