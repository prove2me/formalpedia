-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4732
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:33:37.447068+00:00
-- url     : https://prove2.me/submissions/4d3a95b2-9fa3-4540-bfe6-07755e09a2a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 850899280 ≤ n < 851079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 850900530 1250 850899280 850899293
    0x3050622020c0715120b040212182b0f02010c051b240f0906130201080a0e0615030709061811130609031520092b230304060e0a03 57
    0x7112034400009164606401c075a45441c0940980050215004c0d41084206042071640c03000017080d274210850304503002b4480100c203020801224a0b154240b11102d07001c3c80e40c40000c00c51900a1000150f910008201300900c18030621132000e405682c0e0300d18009003503008005020308100f1020b40f03400394001501210b10900b070342d0481100030a01c00000c600c0d06401952004000504031401a00b003001005100c0484142203040c041d42402e24524030307259155041700411406c882030000e13100c0d007414800b4096280c152058111070440454540c030f6210414002906c4051262140303aa0040b08003100109581c0c000b0085060b0b0340c000903040800640401c810f5844552059000c00c0c200c00b005c0c0103010b11010084c2c60405110000e0021040c078080c16030701c0040b103925480c103410000c40c0030405a0384a03604d01a070a8980d03103100d03000541700389400340440c1c00c8840c1164240038440c040900071204540d45407020030032001071401c09140c02d0054609a10480f40a6482038244c4c030040002940e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 850901780 1250 850900530 850900559
    0x133090509160b0703021f1415040e0c030c0f04420b03190f0606050315010e010203030103170f1c3b03071e0303050622020c07 56
    0xa0001010300c1507040c402d240e504009a005071214510401810f0007198000480c0c030001c61001d217461b122070840c80c042000411444013080c103407408020500c07003452101302c1c030b00c0400c0d54212802c210b41d403d0705105a59581516a41c150107410000d0b00070710701e00c2d00c000d080c0c0c1c50200142011409241c1c6003408007000f0007054500203620301d4021a6102c5081c4107090248681401c0c0c0360b04402801c261909615001c004d0080b40324404100300581c0c08041c0d604160101041d6079414414a40c4802020b0082c1c0c0013203c51311820b229004041c1c19541c41034132000a400010f8000d0b62441c2d00319103414a0401324580051240c00b401c00c82c03415a140d80303000621920495040d03151500303062110740d00c01d66401c501c0032a80040712001800402d42d191582800402000f4616201040c1844a090460040ba00050610321900c6c11000d841c02c5880700b04448a03100345c0c0c04204640c0c0380c008026024554843c0c40b08424804980011801e2441c2c1c024040c0415000c125840941c0d00d01c0c680d41803c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 850903030 1250 850901780 850901791
    0x50c0a02030105070c05060c03010b040b0c25170a0201211517060a0b09060127170d0306080a0605040224130f1211150f03070e010201330905 62
    0xf10407017507940a11806111320b81c0c100010f00c030180d00d99450425000e009010b2400384400d1807034005407042026004028007101c0e01c0614a444000b502c11101c0040c05154030b200301d01810311413444032440c8a90115246904650503100c2074850141507100d200500d22a2011580b101c0d5a01038481140124030640402029095a45a805003025074003908101c0c1c0908502041130a04910035190b40d034035007103554858820700c0d004802c510b0199003c004c00324a0300f03180c400325840b80c0001c640300050004070002c503004541140c00c40c2648400803022120184203034a030319000040c0c2d234000244542c00c0a900140024401c03004001015a042251000307010801ca9550700000c0c600c4c10311180801007001007444120030400e082c5444210b10303c143c0c45490080008034030030358000c010b03607662280c0700a8084031148075032200c142c6540651240d00541741e840100d610000785000d40d6105000c4c0b280f03d4191007405134084803800348a0401c030041011041c940e606200004540c0c03201b54410140300f01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 850904280 1250 850903030 850903037
    0x60d080c0c0f01020c030a140114010e010f120b0106080c07080d05040c140631060903110625060b120106031106041a090a0f030303050604060b1306050c0a0203010507 73
    0x1100354410801400d80c2c540070141990171811082440e50760104d22101881d0700030b409800c40e62461030005004080004a44210a14400020034422115100241a581d0703403a40c1c0025035844503010309548450510060501807000010f00c0701511419a55802842c4009400e0501f001955450700f03a07003124402091071940d074001c04c028050342464040041c004070808048140341d00d00032840138801d50b640012040307240400da1912038195804917002c03400c1074440032107403030301c84000a200f0b84080c4026a1110000910000309280c80c00c11030b12800e143c820180c511401a00042005480f00041911030b0b59640805180301e8580c3c148038030324034200000008516003140f8141b1a0300780840c100502030413060005002c2100c1c9800c00f844010400c240140d2580e00e1480000c1e0008000d4008140d4440d00110000c20150076802943c0580c0003110103009051b180d90749661607018803440114648110303001000307100e000d90b0003481c402c50340c0c10558a40308025004039096030780582c0d959001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 850905530 1250 850904280 850904293
    0x1030609031404050102280f0b04050f061519030602040f0e0a02070f0305450409080406030c020a0c260a030e10020307020d03032007051005060d080c 66
    0x4142d808105103000e2007000111074101424100002d54a4984045160148800b000b0038141d0300d5440c001070540340c0d03000c108046000c0c030600d0103840e090740580c1d08841604c5068500c3c45e155401049513446182005110301c0c10b0f84110b010000b040c60700c0101c06004d0780104502002007041800200080c001450686040d54644108144030441c000c0000345102d10601ca40030000b40140c0d0414500c6806142c055101e502250040404111b0b104005c590921007840605502d0340010030200900100041410310401c403c0c14402500e4000f04001c20b0140f08000c01c0c403503203001e0b6004064440d202e204503548440155501208010140c001b00402042c20110009003900d9551044904607000040d00781110fa0f643c0141c50500000c140c507108144492010481c82c1c0300f08151012560020b110f005506002c0c02e01500804607144200b8a0341d12014845001c11b0f280780496884e280e001000b03100704046108018000c1c14090849a030110310420240e021400c0007002c1e000002c0d071100074181 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 850906780 1250 850905530 850905533
    0x201141c060e060f0108010347071b051e010f02030109060f051012020a140706091b050a090b03030f0d06090c080603060712020c070e0f090a05030307052101030609 72
    0x10b458000b050130504005a2400500000d0205020000003180c140179001880340404260000c41e410740d020039088000001b41661704000071180340c1d004940a07140c486000604440d41b58444042c41809002c9a0241c214076400d1042c0700b80b07804a0702142d600005592410303600ca2410b90303100fa84401e03441c0c1d480c0c80c0180300900741c541c1c1c14002020121204a24180072440c003038003404074034040c0b40085034081900b0714810301131504420b01c0c2008180321075959055180041c000c021b285400d988104a55a0105615980321464015a20000e090f1220985000800d0002d006541381c843d4150005101c50795038014018060b2864134048040490014241095441100c2c1c01481c0f80f003c011408040c00130076100131400070303005240ca00d010b0040308441c860040c040d104000425116200701100000c0d0300c0111204c2034010820410190300799101d915030f042d0f564500305406402038000708080b074012400745004102120700303600c01aa00030b040008001140d14240e00640320380d6165542c000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 850908030 1250 850906780 850906789
    0x206010e0705041a0c010b060a030906060807080a15110304120f080408220e0a0603050f060408091009050406030b09010b10080a0f1107050f16030201141c060e06 71
    0x5900c00741c40d1412a040924140c41c41c07840a44203509800c290100003034680f407481080d0429190340c0302c0a4031003030b65000c140d0001001803038022001e50b001480c00304040b401c10000724803c411a07a203200103018442c0c01ea224103980d025011b0070841d000e6a81d030302e5028441d03460409988118058100d11000f104070000181000800807061820007105004100020701040c0950f4120b1100c08009441584031070b021040c0001d45410a800d11a0214100642d10389103030416010b407031088090f106980f0140501c5556802c6c10f40740105190341c1840b049504d4100820814540e000d54548401840da9420101d400c96000350025030b01c1000c040104562400c00b40030742c80910300240c4d4199031001c0154002464600080e110040702d548500c4950b4685800b50030001c400078402c12400c0c1d40d8601c1e0710300380b5903849030700e449900f0a01644003204104d121404000c4122601a1034106204154007195030050f0f20814894034100310714074407504210745c28070a54010701034400200c130441c20f02c1403c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 850909280 1250 850908030 850908059
    0xe0a15020f190b070c03030b09151003020f070602090d080f0a1403060a180e120409050c0f0f07061d0a140307050705041d031c142221020601 62
    0x94184090200715000000c0f0700e007a0240e884445071400421440b8240380490140c24004242c544c001030b90024000140f802401b92045214122a8070741031400588050f0264060300c002c004010344140444130109640d5001450100e4004060050904c1035541d03841c880d1300314036054140b2400200e11840029040f40c620005054105003582c2145442c41c00900c2c5034080340940701e05c50301500d00c601011641c9410621032006410240c40c04802c00c4248040290410320030f04210505100200310004c541e03d080351040d0040780c1c0e0039854611120f00d400880c0d405843c04036601c1c0c1d90f691300c03503442440b8400d010780c1a01c100c201034400c591441c1001c40010140342091152a00700700074850000b80001a91011190142d4001c15281813410341c04c1075064040d29800f01d64000040c07400701e0001d040c0e805481200550b07001708400312034140d010000135030458444038180d1410360581020754181c080701c0902c51149840c000a50001c900400190004840c541c016a003d00c0042c416103001e0400c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 850910530 1250 850909280 850909303
    0xb060301060b030f06100212070614010f060207062604060b0102061605040302042c032710050904060f170f0a0c030201080c0f04240c02010905010e0a15020f 69
    0x107041c29070138802c0d51440d00000140c5084d11580180c010405054004c1c40621800c841401c03d40352210503500f0170101900d96440008240d20920740003194034803d2aa560040d40d40720f500528001c0d0424600356035071590700c81116140c02054800144110191004900c11441a10081901c105540000e841c0600182804140d08125100c94a00d6540071042d00c080f00c0d0111000316030841c3d08484021041410a002c4420500d206500601001b000004054030004200c408844070b0342c50020400304010404196445050f4226010600707200342c02a00d8003400003407000407080c3d0303a0003180160105a900441c4d038442c10100103803e04400740504c010030110708000e041400c40c15607400d002c040707013400000c0c148042c54000c41c503034000003c20b0756501ca03045108269580c0e00e4020b00c03800e0824442c00e03041d0400d5158026814544540124010306074180c480c0103032a4100001503402039500b030b01d42608816440030014141550001c501100078454000d0014032100100d03c81c14192030150 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 850911780 1250 850910530 850910549
    0x9140106031115040305030a0f0f050301082a130e0c06030606160f0b04050105040210031406130f1401090b0604060c0609060f14181f020a0e030a0b06030106 69
    0x101000440d014a00c0c00c10800b070110394807140340070605208895401503420280c4644000302e0310042442c1c01c40c0a00c04030300b10f08e4984000300300311200c04980520003406292002e411a48180b9a0740d10714080d042104500054810020050080400c4846034051100c0040340d40320381c95242008020b00002107001000e0796520b00e0351070300102148442c401c3e40144a050615071400c90144a00b098400394441d81c01101290142843e0401d14042e0005550aa04c2282c0801380568524000d10400710789100900040120356154020014407070815415000800c0e00c92242c041458031604c03c01400b107164103515401035052011441c211800701c0f0b102d600855042005001094104202d0010341c1d0f808000072620100038500403001e4035080c0841c4200506040e0001c4d482201d0458051041d0342d0a0489529041c441c0d1140781d0b11401c40440c02c200d040040b0204110446e560000c0000702068182000c8074200030703000c640781c41e81e082d00a440c0340103c0c100340042407a0a01881c3c00910311203c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 850913030 1250 850911780 850911791
    0x30a0308150607030207051207030f12020714030604020f1c080d051021081c0912090f0515120c0a020f060402010e01030902031e0d080117030901050a0908030d091401 73
    0x203130081d581e03410501070203108820340300424408881c200106005141e014518507104245440c244800c0c00050300301801500500303c0228040f64500a8592850b03001802012692034580034411901420071010381c203c0001180004003420542000c5903141c800c945d040e0365401c404111320121500580300608058a44108002010307900b102001d440240c0d5141c22180881880c08078564840c1c003188407200b20501e000d21980b01d107258400d00c1f0716401806401c0140001d91011074501d0300500a0748202600c411040c019402c1c000800080070b00e454401034644003e4000094156500710f48000d85c80300001a40103109074103124088400380703010000d0455042c140e0000e000074020542d01410107503070b46401c00c190f550030000600c0c0000e049414220360b86100d52050745401c018a80c02010464072000041c281d071104915014004980c030180d42052000740044480d5403008100500304480c103030703022440032418070040c4950b054090002401c80d5031440c1003031900c042c0044414551349401c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 850914280 1250 850913030 850913033
    0x12050906060d0803090307060906050f060f06160203010e0a0605010303090e07020c040b0d140706110303010e0411130509030406081e0604110c060c130f031109070905030a0308150607 80
    0x502c840a0b48941c80340c41151a9680c150156207035008503140500358a040c1a043c1c002c1c00f0711540150f010702d510490040141c1d441c00144181320300d002800c250000710802110903c4a0b050340c0c0000020710007070011a0f461100d455070f80c0381c8154000e080d02c10301d5603070004004040d04402450001c08900ca001903040c0781c4048082c2d100e075851090180613688a6480015a41e03507407045085450b13011019113000740da00d144403039440c0740074016503001c1074080c06c01c0860080e001040c1c038100d55403c3c0c4c0150042e99156a9694552003041880da00400108501d284480caa4011184260160b100640d00c0ea03141a07001442518054081c02c40d10200c54030345960081c6051842d80c1c8030006407400300e03168600c2c821419040c070807180740301c0c03044c02040280440d042102c0d0040c0300c00250840300840903034880c03085c07a41c600040d10004040440c0e10105650718204603105907070081103418240182595940401d003440030401c03003140007860400800500512100c00300500c08001e5031001c3c148200e5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 850915530 1250 850914280 850914289
    0xb07050d150e090a031e0c05010509010e0c031612170a0804120801210201120c05090a050a050907080901090b090a0204051f030b0405210a0f0f0c0206281205090606 72
    0x3401c044420007601000121107031f00860b2202c448590002c020040d601e045092680240040207038802940a010441003e5180002e0f0b007034840c6034480142c2a03da403410281803007079444802c0444411280c103a03001840f21045004e40020f031401c2c1c039004858500340c5040c1d901280c1411005050240440c018001414071555100210411a15564240d4800e00050b0340c600e401c1c5000001041c01c1c54252407005501038058000314900b40c501000041d2110100a50b002840c001d0310b8002c1d401800040700d4070721800c100c81c0c20203074010000030a50941e0f110b0802e22081211030000b10317444060300004506180c810143d000c450030503150201880310b903104410802c0b900c005410180c8401c04039003442428444400782441702240c602500042650014042d0010342c100e00c00710714810b501039921402081c0c0010604103990f550305080c003240d420024160030004400b581c008003284402c0700305000803285541c810a944640c641855104021010b594000301911850382044c010b202040c0c58 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 850916780 1250 850915530 850915547
    0x604090804050909010f05070e330f09030a0605060117010e130c0f080d080a110906070f0b1510031a101e081005040c0c0b07050d150e090a03 62
    0x40445402c441c58859146907400741c1041c00f0190700c0a40f42400748009650002c049c0f0040c41030075950700218001040302c7c0d1895011040f000c2032400d13038034000340300d008480e20b0007080400c241010043c20080c40402080c685400d01d20111a25070b5101c0c18800d1560300296100c404485648a000082d810071401d04095040600014a00c1155816040c10825001000d0020300440f40c0503503803daa4907102e0a9440c0d031110008008121400c0208504c0e0f121801841e00c1d900306102c00c18984a4000280321282c1e01501c4141c034800b1010030440c000502c54800c0b5401464004510400b000141d810001c1504641c81c101040c1490705180110a14080707054203040d2000311031070310841c3c200740025100c1501c24410201d039140c444043e500c120303801000d9140120081d11111a401e902c80d024401101e0340210441d0200705145240c01c001407465220702c1e405695450414100414403580500360b414080c02040c020000c89824070940b802d0b40c0c03440c0e51044d00301d801080c10071750b40c0d140949844c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 850918030 1250 850916780 850916789
    0xf01060902090406080d140f040512010204152307080f12010302040e16050d0c1a190f05090d050309030d110f0d08191b1107150f080603120403030908060604090804 72
    0x301f010665001490206060302c00500c0050311144030300d660348422900030340c8940204a108203c400351014030328494151944583c94140310b4407280c03c200c01012020790442c4034102c610810410407202c04c150504040d1400d0082981c1c4e1703050b154150f104200584200704050800c0b903010b41d52641000303801d01c00c1c0e441110000e94200c4000f42c0c3c6810100f94000d52604000681409860804030b55050b00000344a9003050209000c8120407201044520b8110200c1d00d50005206001e4501140307061404413007000d00c0b40c01141d2a0001c6500800e09001c1080803600102d11010000902c0740300074803152038a000070300042c244c42940c200000d44206d0024210f6409004410030103094098a0b5100e0554020602001104502d6460300141040712000311901c40c4c1c00340c468000342c0c402d200312580c0c1c41d181d034680741c0c03801c0c50400f070a00311030310b60006241561520422400707070b4208a2000003040550302941d110700b040c80c04e1a00ca5444c0040103409580640d20b844480f0313002c965004140d40584 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 850919280 1250 850918030 850918067
    0x80f07150f2001050c1305040204060503010506091f020f07090e0715050c060c09040b030c090a090f1203020a020f03042103030b090f0702190c06110f01060902090406080d 75
    0x1940100e242c00038011200302241030540c41d202c00d01ca00105154050204030184100354560355440380144030590203688a0f25010410600041c80344e131030200058204014058030098030b0407071107400039040c03151440141000d40c01001c0c0e201c808a0703007800300e0302c05080200010300000c008807241552b50051440b4100d00c03600303102c60072620144140100c482d0101c0e50b02c1120a607080502e0406139541c006074510340b00300d280110404081c10003040c5030900100003000c80305155503460213500030300440182154002005905400080d480b0f000118000c4107980d001a1031383c461000c06460702c000f10b541480c1e207034400d000c2003041c1c6002c0100740448000c0c1d09460720800303005240540241190b8031314198403011304e034200180c9041c9140941c0c441d030708950890740f002281c042c1d8921000c5800c800500104a82c52060040a01030f6030003080302c501120881c0d12030b00081072020300715005070300724821064000a4484c0c091905018800103020703d00c01920104da4140d0025010119028401420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 850920530 1250 850919280 850919297
    0x402061e0901140c150705120708061206061003150f090b0306060109031e15450f0302070308070f0b0c0c1506010302190224040b180115080f07150f 65
    0x865209a0984104288d0712307440030705c3c03400d102758090b00f04034040710518007940c050700540c5102080014100e0013028081c11244898420030310032805400b44240e141c141d01d60101d000110180381b2080040104a05040001c03481003810405003030a402404983c1001941001400410440202c14510705240300c50200001c18078500184078030074603905500313418038003080c0d5428815000305030122041030030304141c0c0c03c0e5400f6900900ba074005032071540001c0c10306520440041c12140e04d41b60558000d00440e5042e6030b580d5580d6105501270b00080300e020484002c05030400c00c05c0c01c04142c003eaa010411820100c603400c40e20b9584010b04800e82d000c1840c8c03004505242d000c0d0341202c0c00140d94024603a003078590b00501955809025041c1c0c881c0700040c3c1b003500c11403904054035501459002c19805519151705030f01d05204215a002c501c0b02e5503031010040032804004203180c0007841c000e405003016144003006142000340c07607413024150694602456103080c1d03100301d400d50403600c2c40c20700116 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 850921780 1250 850920530 850920541
    0x9170c0a0b030613061d0906010b0d090c0528150f0e0d0b1e06030105040305070210140d09030806012f0c0301060b1b1f050402061e0901140c15 63
    0x100303103481300d545035079524228010840007100c10200d20076096041c04a5000d840daa2447d80c1d840e042446102d5102c130040c130294182c200540c1000700114050741402009a8941001070580301541e820b401c46514903c4010021200141c0700500415031009901641c0302043d40240c00c0745d0451170f50707a042191558024080b50b8075030340c100d841160082d1400c01d19140104d070302411002029031032804000a9000201d061505000b041d108641c507507241c40c00d0280030343c24403410b85841508103044c41000c2c118102c6469a44c00901444c410302d1030046481107075410003810744135002e40328a0400c441031251a50501c4801c9020708160f4458000c100081203141d0700c2c1d4140030340140402d0303165003030410004005108002800060154549a5403240104003130356988100c01180000581c400d00c1ea600d082c51015400302d0741c03050015019900e4030203141002104140c9010522071107440104402d14903580c000c003401d192800380c800280c9000c80c00c4005540da151208171841808622500240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 850923030 1250 850921780 850921789
    0x60e190807051c06140a1505150a090918030e09070c021504090e070806010b0304030c120c0f0f03090f0513050405030702030604050c13270501020c03040609170c0a0b0306 75
    0x12400b0381c0000c800c203d03c051915030000e180001b0b43c0d5900106041075815455805502407200c1150002008041071001d0341e000d48209070008455102445501c10002541c00302a0180c1a001c200391140c05501080c82d14010303042540082e1007a000e058518208110b40e5040091600704680454003c461006200941070b100c1c8034079089840600d0a01a4002001e4400a00001030300d41070f00c140c07081030307032a031502e418140000c40e030150020320a40c02d401c020034a003030701065002910340341c1008404c000e51100c2070510030244080340c0703140800b0b203210240350380403456001500c92a00c0d40c2c0303119860f100002c1c140c845081c180e000025034410100381000b03410030441d84170320744c0501580d141c0d2419090564481d284144068040c0c00703101c01211806149109120180d540304211030142412604a0340d0702070107060040728250f5003045041c441441c104098030044c80550340e80c9401038204045101c0c5107000780107400840d40484182030003a40d074102c0c03510966080c440c1c640e859503a03100008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 850924280 1250 850923030 850923079
    0x1b02010e0604091401080120030f09070308070b070e01110d050c0c0904050a05010f0203192004090b1e1c0606050904080a18030302060606070303060f060e19080705 72
    0x300d07441032504190844912610041303e040320381d84c42c020007600112041450300541840b0310f5010701d017400c00001c0c034140010505c59811519500403203e4481c2c03280d840c070000354010803003600c00d9041d41040051440d4008151000003000b0303e402c141928140c600e099031001c00380e0410013444408286180403200400c0202190000103101d0380715800d007810302540321800d202c0140e5542d420302c0c10401c120001070003164050044c244101d0350b400d85013880d0740d0040170401a5041c2800c03121b80c20b80030040f031150191000d04010301d000542c4000e424200702c0482010034030000c1c2854500000d80955880010400b050b920108803800e03400d5183c82c1480061080d5080300d94001e118800340020f00c60030348080c103841002030703d07201008150341c070314800038a20f64031000b4010b030301c5100015554103154000c0c1c6101442070070041185a200c0344914330305010798101c540051821400c0042528046013a0600003900c0c0c010035111030b00300040c0c80c1c1c40342600e024460040c4e1140c104100d4004151402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 850925530 1250 850924280 850924289
    0xc032703110a0c171b04111c05070201150b0409020f04120803060a061e110a06050a0b09010f0311040b060c2d010c0503010e090721050d1b02010e0604 66
    0x80c0e6182464518080c80c602c0f8242c010700c0200c40404003002a07028001404e1080c0e8035424a0742c0741007410080c02c01010300309044490081c4038051220322901070815500303040d05d5125107000b050518004c0c00003400c4400c1502d03194101a03036624108a40c002103c01c03a426229024400359842d94401803240d624440d550003d00c9025050340034009214014018600500040714220100d50396000c08071740620008081d42222403001500071084d0380191038100b65241da190039a0300a027819203071001160400c0b82c6a508050729160024080d10b010881940500307101c04d11030741154110340707a81d00d0035540100c006000329aa901d00700207507683c00c4150f8481a6a040031200c0c2000f01c5260342404017140112a95203071240c0c161428140410f02900502c0c0003680e440c2415a840e2124003904090041c0c04041d0314021000003040e1500352111038070450103102e019085038229071401300e1405844082e10701c100600d220000840b07001d9200e45040d417a40910700b042c10711306410300140030343c41160712 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 850926780 1250 850925530 850925533
    0x6070b061903150f0b010e040f0f020f090301050a02071a0c0706020f09040f0c0c08090607050f0f0c06070b130303141f0b0711060d0b060403150c03270311 68
    0x60010400284051003c910009400148904003801c1c00303410035107840d14995404211420030000c580e0406c6c0c0c1c0030138407601c190500410ba03802000300400032130303102d41810001c210f80051000610b0409016160704080140310440c40c0091644407102d588644071841e244e0f8601141c04241c882c20b00606990025821010442d50340c05223500309242e95010300c241500503030809807002c010362040c1c4944000d051480e180c46060100d41c2d601d001566100e4100994044030521008001c5001013180c0040c2c00c1c0c286000700100140d01c007045d0324140d80a07078810b20403002002010001107100c8841a0404036100d040302106003a4a4180c01801d03104c0318185850007200204010014600c007090741c00c010200c1c559074401e440c1c96010540d4460f820000d8940c02c41d00c404134105040003401400d4501707100900045104040300018001d500c07030352042d501c0d024a030700b103603100e041544503e40000b0300c4c40c1400c102008941c1520030015231601060800304110004000605000761462880d101c240c40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 850928030 1250 850926780 850926829
    0x80a08220911041d01030b1906120602031911040608060d05011b0e270601020313060804061803020c041e0e1c09081c0e1e040c090506070b06 62
    0xc90b11185500a0f1155440d83c604d04600003202200000040b410303260001d0b9900d080e9680c802a40e01d0000d0030b00303514254a0ba81d03210028101e0b88052040700114410780000d0303502e080c0b081110308000e0708a00d4484c0c10310315245c160803420552000701d4044880c28203054109070785210009411000814019105500707110356044d044c9080101d10b6a4803065860700c0250440100501a00c20085141c16514402c4120300c000c0034070b030094409900c00350520440f494031101d4a0048200c064507444980411080e6090104202444c06117401d524100700c1d04039515042600c00940d9442000303010b0b402207030740b030403208040304409459090034044060140203d417160071000d5540c40e07102e400b103240100d0f040d01c0038440c103100384a00e00454a11070b006021000c56071071040d402e44548078200d0103202c4040c41c100016118442008e040000588810240203150800c0c4030554207420703a00d408202201c1000c0c0035550b5010143c521160700a90303c4003d50391681c010440710395104103c64804050807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 850929280 1250 850928030 850928051
    0xd0201030f05090c09011a0d0b0307030203030c061b0711011206050402040612050f06033a051801020303070f1412010b0310050301090c0b0d0f15030507080a082209 72
    0xf83c071a5101ca00303417032001035607a1300c0002145020100745410342c3e0030420400300d5202c1820341c000c0c0c44107200003001d0383c0c0116642e07400030b86582e00104210184d034000074100900000440444d007a102032a02156203450220f650306584844a001402c0c117014240d003031070008204a60208014003000703030085682d10748510024040206040307850700d0050408000919200151078828000d49c1c01074001c10314050861408410350320341c050500702000340c00c0305c245810881403040d013442da54240c558940c0d4180800d6855404403d2070aa94155030040042c00140781d0b0000141c0044000341c6410002d04114414041c52803060121001c14074624070300104200e003e22008501440e904040403e015540d8400c0c0350984407011409455090500010070686120000500946584160026a200d00c0c1100c0108580c1c007010302e2005000060024070400c8000c00c0b1a0340139206060007071400302150f0352040d045100ea00f82c0d0380b2207030000401404200b003202c241c403805040d09a01c00e1001c1e00d0724 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 850930530 1250 850929280 850929283
    0xa050d05090f0a05032a0301020d06051f080c0a0c0b0405060f1003020f041e06081c081620010f020d0f020313030f140316020c031b0d0201030f0509 65
    0x142240d20038411001025401d182814243c012288082c0c040c0c103051818503034074030401078040c888202c00300e1741030340c0307400c05a03020303c024400c1455940d000105a403c05d818891462038200780100c000504a59400446800103402a48102c001406c1c0365107582d0500308403003a003a0184020030303004158092004010010903114841c00c00701c20340c3d200c250b40e810321070259400f1901c40030390080114001642d0500b0180c0101c0440c0c0c110a0903100d2540e0709640d00011a10a80d000ba0000c0e0402070868241c01c2000613000315600c01880c14090600307180b00c1c0804112074441241e0188552140704112480d4040300e40312104998000070402000f403102c620f00a075100c0e02d01103092900e05414180751403d2882a40c0c01820f001080701c10a0420341c1d010341e070b2141100c0e0600107114600140d003080c00e1491009602c511a078031020300f07810f071080c4800b910b000b0200b02c50a103e50801031181c0c0c000288002c8015000707804a83c1882d1b031584034001a40180107428811503414104820021076100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 850931780 1250 850930530 850930537
    0x903040b1c0b010c0807060c050912070e090c090f06150a02060901110406020c013911030d081623090a0b040b04050d020604080616030501080610170a050d05 69
    0x2020700a102c41c080d91001107440550650006254000500c14079010841d9644104a0950170b401e00c540b91407841000581c0c240b40c500d03400c0c691a400405c0c00d002c800603080318146c02151400051020b070080303100180300074100402c4e0b140c0302e00e44500000c4540e91090002400304007034a00c510340e1021506402502c8190482d01c0c2e00d203540c2402554041c00001604036800c0391015805070400400c06801110384a8250408100008994084a049036100c698147c0300791a8521541141e410700e1418150b00b00c51400b14912a8200007514401070750450880743d03000354081c2c2d5840351000103080998600022061001c12003045244810410000f40c00810110720111046490195600c074041000d10a9009880c0c0b0080140020000c07030415a1400480920062081d4281516001c2161921a080307034104580e03800f00c4448240c940d014425940900b840300080c002629094200050001761445419000e050032980c0028521080c02079800c40c4c0d03841810380c3d99120124900a03c56007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 850933030 1250 850931780 850931827
    0xe0309190609080633220e030a17041a0403080a0f05061c0f290c04030f030f02010b1302030a0c0e0f04110f0d140a05040b010302090903040b 62
    0x5001c810003140392040092150300c90f0b60980041415802c2d000d2a82052400303c640006208217410160382d43c513602c04040d10401d0907109030b0f0480c0070f40d40380f21400035190a83c40099003904100140d001466200180500880c01400316140546592038444e11907482c0410046580801d64240020594400f81e10b41c0580f61160701403000300441d40390f030381c112041581c03415400b0b0b02c020604004902c4040031000e90314080c6801200098040c0c03a03609000003001c1c00410202e0115000345c00d1800c1e040742040d044020340e440a0309041c19035841038030078449d40300f000d414408454102004a4801d400240d4044400390100c80d0418604460038007a4000707485044c442810514984c1c0c14134403134820031922803402045070b00c29100d04014800203195107250105500340810180c00301894403401800c941c00100c00010700c0724030710b43c203c60004002030002807000c0d04280500000c83e0705400140d0540b81c04450101c01e5403140620203245105a5100c0c00b206a808541031404401c288409080c42c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 850934280 1250 850933030 850933037
    0x1503060501090c080c2a100212060103060b0f07080d1d0109021017011517040f0611090607060c0306171b06040308040b0901030609110a0e060315040e03091906 70
    0x2612181c04c2031005008900da40c2c0c44240d080d4500001003000c55000c002000b841b101518010f403d0000382034141c1c1d22407480e00d102061540305006407541c1c14481d100080030301e441d120341042800791000c60340c0e120324000513110110114418004007141d50090800c680c40814896107580029030180c0030380074072042603110700e901650300030b12540201c024510384200031000407016820001b18113203000008680c3c0081086165501241900c005030740e17801503000f039061600d24851803401034107548142900002000c0284008171072511090b003036510716540706030041002415480101c4c0104242d500c4071003083c016200000d10044040780c0462f08070f0388112010181342d409424010f40d4030552100a00b0310508201c01c20625440c280a0040700070145004503030256541c00708825226001d4000c200e00307038005940c20400360003050002c0307100021707a8100e0540c5403010400000c803090742c2e03809019585031019185906c0d0f080c0200d13031414200031300c101581d202070b0768840800c081074003641011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 850935530 1250 850934280 850934297
    0xb040b060f0a0308180a0b07060c140f0c150a1d010c08040209090c150c0c150d0c02010f020304050703050601091a1c0501092f0d061503060501090c 65
    0x10341c10102516085280050040a010740c50f55813000e28591010201d40350b90904d030710804400d59104034001000f00241c00c009a140e919505003242140c440680070800d02c83c840680c902c01d46014004d07600f4100400c41c035140c03904103201c007007070030840380d540d400c151940a0001c00801c10300340e6001c110030070f003403401071504100d10040041c02ca42e20200f490020070711036070009006103003079900e00d0b03403202d4000c0c02c1d904008505800700d1212554902d401c0c070000400315054007164410030591040300b900301d584554108460a05407094810450701c4038500e0748810704001e0b154000d400464079140140800c550f00d141c1418441d07140c11181c0000c841a008000001440081e00d000d100c2003103101c009100b0005208804000304025808101203508518603404000b00e8000e1041c242c842c0d014610760410030060340c070350881480310f00c01d10300d40603c0741840312031950f200e0b0a00313850002c0c0e120400107601d900494444050400d0350744000c4c4018104400469204000e802c00940c2c0000e90321850788 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 850936780 1250 850935530 850935541
    0x61009060504020301052419080402040b0d0f030f0207050d051605150d0209010908060f01030308070f200304030f0309030501060608090c0d080c01020d0b102321040b040b 75
    0x1603100031b204040d0b0007000301e555180001404160422846588800d00f440e0100301c041412541c2010010b10000c20241d0042205501f09801440301d2034030f080340d425412100b580c1c1d074079170100c89100001c0c04100d0100c94104410f03000304840d001808000709494901140c034074146550f0411040004040e01412030005600d0508080060710f101c01d801c0e05a040c07440c40ea01400c001c0d0030240081c0c0c10043c1d0b0ba907001650710410b0160900503485031403030700d64540c1181005072a64a000d002c1d58204074507200089a915030242c60f40704600d081d641b00d0000c51090440541ca140170760b0300003402c08015800e43e1010140c21030407500482e031042d402445500d0b59003405075844001114051500d8211505c4850146072400190026520802e01d0303c2c108004501900d08a8005505644500c0d0b0b450700045403c0c40c0004030117072450b54900c0c11850354503119640504040c2c144c6041d07060804049030032111104158154a400d5080704844003083c40c0908000154076400d43c0c041c0d544000220100340d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 850938030 1250 850936780 850936789
    0x405150705160c091109030607020c0607151b121505150d090c08030d0608120415020c2215060f0e0609090f011505030103050613050f0610090605 64
    0x1882140203464141c02c181607114104001105860100d0b15080650710200f0b0506440c4950315120f08a003080c2e945407100d150900d460403401034040429584030f20702c04d004070380d505400c896038242c3c0240810308252180c84804081d004c4060b0024140e01703011450705003554886135081c10400e80e03c000380127030106064036814035105e80c0501c1d9007040400b4003031403510101c54001c0074150f0f03c04d04001400300c4103844421310b468607500700d0302042e0800a041f240c4449a401f07000302504000010f4441300d8240c2042d060140302c2c502c610020103103800d550200450081c031000c2e0390008007806040e1141409002c00100700c02000d46a09203a1030941100480066002e480c42510204c2c0c0f5800402e0113a5030042c0c42c1d14540c091829485402002001c2d161384400d54024050050035440150f69410300d0700d40d0074040e0290446400708002400104003084000905640003034040300740b0110400b80d410250700b4219080800c1e405441400244090310383c404900c203040300c031320b05400c0081540707580410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 850939280 1250 850938030 850938073
    0x11010221040b1008060414150a0f06090b0a031e050a08070c0b0703080a0b0d06090c05180903030121061b110102040e150402070b04030509190e07110f070e0405 70
    0x9811a44480b0018000401100d02c1089044000e0215002d485c050901c540d08c010040f200262a02d481d45401344441241d0702940e40585883d26040c042c00c1030301c601141e0841034500c0701030110041c9541c1d40713403003001e0039001401294201095402c5800d1508041ea8203502104044410900556000132583e0310b560036079030308551554500d061030700c52070307009000707008902c2c07005610100320484000001c205210310950188140c03c205101071400e001c200081ca14283c15580300c1001804211081c4d8000c0103c3c1e0644072010254840055554000840c1c0c005000e002410686002101d03201c001e007001481c46061720aa56010020a1100794982030740590301c00c44012202080204a9010012264088131100a04014204007007511544046403043d5000d1300422030005400110b4141079601c60b205600c0d10444601591505015290608004001804004101d5444202440300348010708002d8a11070480760711503202d10901d00344100035a030460340d51040c0d03c03605c003d0040003542c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 850940530 1250 850939280 850939289
    0x70c05040218100e130e01060f050307170102040509090313080f0a03030e1606090608060102030a050a05090d0206040914090a031e030204030507060e041404110111010221040b10 78
    0x2401642610000e01201c400f04000800a02002501e81c01c196250321126243d4540100c80118008003440010750131112203800c0400c241e8a607080901454070b0000f0b20600303d9510480000310425000a150b0084c0259000302e68040f03018401e01c035864800102600542c0450265004025902c100a079036403511003694011317a4012040080c007103130003036000755012440300d000d039030800741c0c5040c428400c10f58642186001c5410540c040c465507070300008583d48050203000961800c1c0341c1d104003038010b00802c040c42080010014007500a6180c2007448002188c0c0034000780c6e102c0e0741703400d08440549942c00319070340c550301d003100014801000001d40c8110550103840712000d441c2c980003109901e00d4807240d0202419000c02000002540410014004000c941d64409140d1541c50800042d2014a040c00c84455644807c0c4001f01b40c04101441c1c400c40c00342001d54800c902c240001e4060f0250015182ca40031940c1205007491362089a070904c45c0d4031500040c5002d43c2e400140403a4500203000707 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 850941780 1250 850940530 850940557
    0x40e041101260a0f0b03010f15140102060103060e0c03071502190206040e070c0b041a0604021206040203070e031203011a0a0509130209030a05151501020a061107080f070c050402 78
    0x841c5149483d0360001091490740c610118110404801003402d40d0000b040e000b00ca541e640c1400c1013400809002e48000e440090f1130304a404000c030000030342c0e440060102601196440354a042003d0040122101c03200700a016a2100f0740d03650b6001020018582c1c440d4090701031000c0c14003244110007201c00c20a0b80c0100b04504003410300e44040300c0400b000f0042d01c184030442440034085080c0001d40d074412031080c08031070800d07802164088082840500386502a600500c550b5004000c440042548804240c400580300d039128642140c0604140c1c03009609801000003d4000e1846140254161404140da50646254010b00901588108550600094020700080502c0d2400c03411001e401c03c0054009030070102c82800080c01c1c030041100031607190784590074182e00301d240c0800c019408203403103d500c08500510300010b910f9100c115002040326560340a00c1207400305010541c2d1106030083c0d00e250311003c10301140a1954001174040e20309040c10f1384d000a00c0d142500031994942c00d1b0f0300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 850943030 1250 850941780 850941857
    0xc03030306050f18040501061d0103051c0806010c03120c020303061e1e0a0b0a080601080906090a03082e0315020f0442080109092402040e041101 64
    0x61045a07180700181040361b940d502c071140010402035412042c40e041c201c3c2507400040c3e51551a00d0340c1b500008000d940c081802c2c81d0415800d917a00400c0040d4480402c1c201500075804914045038440d4506460500032841c01c143c0344100355000020f184a690240c540c0400a90f803c2d10611140d10f202442e81c0e88480300c000400b605440d560300741c1044000c00b82c50942c801d0345071b10f0b002900350406540280050443d004200d41982d02202d42a08802e109000e800c0c6030902100c0e03240c850311148406803e001103800800c84040c10b20303034080c030124024509044100400701034958034104c00e2109941504910540155a04683c804c6500e6195015125442c2600d00b84150001102420a810400381d070311b40c3c020b40780e4102c0c0035031300780ca40301e000c10082c0301201c0403002401c00d04040c1c0158603075902c0c000c0c266000401000d084401c244920304082d445080c01640c100103449150007080b10005d54900780400c0000c1050303290340307000342600c540301ea840c000109c040704504260340b01d008100319803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 850944280 1250 850943030 850943059
    0xa03021b1f020309130504061409120a12050106030c02100515010809030918010906080c0d0219030f050c01111f15031a04230307020910080a0c03030306050f 69
    0x7545000d20720001030040d03038101100c0c54001203c0b00101601c01c55515201c0c0108030070440c481c4107051414001401220303a40c10945131081e40d5100c0801e400034021000030300c412001d8020440c0410540b00b5130300038015981c44440c000c0103003034008413604c09172084510f054903a05060003180c1c441c7e1088c0d00203001c1c00004000444d80044084e01100c4507000c00c01c0b01c2c40c0030791100ba5240e4400425440300200c0c65140c002e01c841215080e5121407415041162035601540e1030803a00b6942c56011a40040b1600c004c0d4020300c82d90910b136000400d90150030b8210f07410420045140840340100b601c0f1903a03800150040b181d211080382500e4844154980f007103020b040c21550101e01aa80401041110766840341d89040d802c4400310041420250b0f0300e8204820082c0000b1444001c801e400c0b101312a1444036502c5943d28041c15100902c60b10301c01c1c00181e4001000b9583c9001000c0007011540120302c28100000d1400040c00180c0019081100204282c20310758420041110301504010f05040c21 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 850945530 1250 850944280 850944319
    0x402090601051b06010503100606090e0c0903100f14041227080303100915180908030c0903070e060a090f1407120b01090f0b0d1b020a03021b 62
    0x306440c0c14014184100031000d1002c0f9014500c1425000080150f0f5040400b01440c1c591703075664020225041000601c40c60380d00103030b0720f401c4900d21003aa4a080d210070140c62058001d190b000ca40502c14040503609071103564100001c02c0c80303014000c000c06d480f02d580000111408640141c6100d00c80210712981503c18280a070400d81140c08800300c4000d914000382010036150700c00d440950000c400d000d80c1e0844c80580600610380c4610030000e24040c1c5001d03000100c07aa119a00702c40e9561041075603000040d030070101d201a4403103c0180e89182c208070b510103641100030103034020703c03c1da54041000460524024003807c03000741440310091409052001416200310342c00c901c0c0b03842c1c2c03019071345040d0003c44a0f4000c624030f0f12400a0041c0440e03405c0f08803038100e05424100204a00100140d4612042400683e00703203001c00360741d42c007001030400c010f80144808140741c100c202c05016503090740420170515440c42527080d6210b940c603c076402209144000e000a43c0720180ea10b100107134020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 850946780 1250 850945530 850945549
    0xf0c070210020f0607180b04031a0901230a180201140901020120030402091f03061a0307031118010b031f0e0a05150102030c070905060d0212030405270402 68
    0x41c54030466030380e100d19041450500c03a0079904c103008110004a4241d03070b0403005166402a14001c0c0c20942403c0c952340342c1d03201d011032590800b5204074481c0d001c034032002c8080d005400030740148015940b040356407441d608041c4608503042241c403803406046080c00c1b0207094203035450f6501603546210503500c2020149a60f88103000040c1590358443d0025100506054164010a034050702240c0320300d0b1900500c8940c040051142c1080c0c0c07940c00044081c0c0703c0041c0c0100030f481c2c10200000310300c0500f9030010b103002d00303001d03140c0d52612414000000b0810801019010004103507107410b4031540b940c002c482441c0b0203000d00f01002c201440001d5984460201d000a9040c906e585070441c55901c1c00041400c02081c3c1c0d10b5140551200308200070904054a900c80024003817004520301801d003004a82c4030403290040308071090710f4001141840c5d0710b17803004840c00341d001407003000c25181c4070745050780c4d990040c0726060185041c1c2980068089a42d510303003a00700402520314005035a243d007000780303892 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 850948030 1250 850946780 850946809
    0x1008010c0504050a12050c040c03090b101d0421031e060504110901091811041814060d06050a060b0c16050a050a090209011704030c03111908280c0b0f0c0702 69
    0x642cbc800e22a80422803925603540a01c44400032440031a003802e40d1365000800380c94280491511400070b010002d00240e000f0b41c202964904442528440b00782e04401406d8010034501445c242018030452401c0503070f00041c1161400c407010880d11030f080c0741c21403050080c0c1d03030b085000c1045628100010145103503000c4803542c289000049500c80074051480c04e41194002e4000700c000104a0039074440d05126808214482c880800103500c1d002e1300081005446041c01024951508003082d00f880d00d07a0420340c05424a02040c5071240d90341800385554401400c008000c0318a008030004580c20720040a0041d160702a1192010504002c3d4160107540980780170f03030401603446203060780340c0c40b402a02c1c0c0c000c03403203603607003000d500b040d820001d2255890344019080c5402040e406484010301a00b109d90141e485081c261302c1d0f403609181c0e001c2c005d5401008000001c18200c601c02011761018030082c64910601c1c6125a903160f40f407030569a4070080350340d4441c020081202c0030161500d00100700081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 850949280 1250 850948030 850948037
    0x516081f06081f0b130902121815070c0309090e0604081305060d09050c011e0c060b03150106120504020a0e0a1805010b0f0f06030109051008010c0504050a12050c040c 73
    0x30820f4078407035440345003a0b8400c40074500c02152003501c42c08102c60039002010070300019414850802c0c01c01c41c0d00c12000e80b403501c100c01c2c058040003204109100082200c0d0b5803481c031181514010401130006040084c08030300040e00410003007020806482038288400c1000d00400c01c50f6120380e60720019500900d028010080c01440014942e40d90720003d26581400317100119011049140442c90b04007441d0440c0d051140100d01c032100c050b841d101d00c8a0300c0c00e80c0e251407280031900b828114010031641d0034098140c042c11100b404404050004541282d803207a49801c44403580c940107c040710003d540003540092031640c10420305015a014542001200c180003c03c03501d404070028010704135031003c0714140d441c0e40340c03801c091814143c0d190b4045810369030072041c507081c01d0000c0d005200500502c1606a81c0e90040365402d40461814400790403880001c211010b00c1035005896030f0401c0c8104d61090452200c0070482955024003a20344c40e600400611010400c541040090540c001182042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 850950530 1250 850949280 850949311
    0x308031003050f070918020f01081005090103060e070806131b050d050f0c06160f05030f1210051804110f03100e2104060318060516081f0608 62
    0xb06409125441c2c00040010040055515140c200d40c142d440c0c0400c100e040d06c00000c00d8401585464205014082003480c11a10703640c2d4003e03c040292001e508042c1c0c20003803040000c4104030040d44a0070300011b03e401242c104664505012b80e135240308071002c11445040d82c013a00001103100711100310603c1039500e44901c0b01e840d000800c03062210118151540d034002d003000c110004050101590303041058806074030b49015408540210000340320024210f8911a4000c030500070203200303941e030b000c4201c80d22030360300c1e58006d040003200d1105079062103180e4595800000c0300e25007a01d400003004c40800010300c265482c2d4442d03403000001c1c0b117200303a00003c0c1150b0700030f034030368051140c1419460302502c0010074000c68060103282c08032000c4418003034100d4809880b080c5400c0d50581e011600f940c6404500d101403501222102c2028940040001d0308140c1801004244401e8800e90700c421a903840089980d12a200c4510290f80144102c81d4211580184841c034884c11030b4035401480d49600229 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 850951780 1250 850950530 850950533
    0x3031403220506390d0b03070f140d120e01020a0206040b0a030b060304030203040b070f062a020606090a1503080307020f120c0706050901030905060c0a110105010e010308031003 78
    0x85504198007201e054110000b001840100505110019000c9111a000c02110344900b03650380c589140b044d0380d801001151081302c020301904a610100400703808d81d00c4940d50754401a12040c1c0d14014642c08003642801190039051400c069040b65421652000e201d2105540c00d98802d0ba00e442c1d0503045000d01e1502d00c0140e19403038000e00003040034014581c2d50310700640c801400c80345540d0700305d84500300800600000c00c0c3e001096905480641c2021651a1306070305c0d00e00c42e10b4000010040c00d15051840c2114501201c174440400f0200b40109000d1581c1049401c070307207a1328110350b140d034840d080001003441c000c070b1603101c1c452040c21a000c0e030360540d07242d45607004543c10480d143d00c0164445c640d07030442d411081c4100314070840b007400b4241c140200307001003645441890140d202040004143c04002c0da1098101c900900c0d004010b588550524504856299110003240c00215100000300708881c40140300d540d04940100e1241c00b600d03400d5a8440145174000351440e440401000800300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 850953030 1250 850951780 850951831
    0x30c0906030c0d06062001060e0f28090b0a1e0b0103110c160e0412121d0a0203010b0d080304020d032c0306130506070837051003031403 60
    0x134041c0849031a07000517889400d0703100041822280562110340d040500800c152140f803003405410404200b403951095031010072801000402c0001180c410810503544004039150350300042c0c840b0b01801c5000b02c0b995580f07403e20305489845514124518211092880e106107030f038849401c0c90014034001c00c400c59412242102d40d04410007100042d084210301840d50400c5620072030040004104408041c03926440b046408036040041c0414402c45105090031002194006100035034207014a0350481c242041e6a0b0780c2da41c455800720f02943c41d000d4900e405180506503108602d03409800b080c5156190b500303000f6038642d202d00480612012064865040704008a4005105041840310001014010405180000160003204010039000c11440171410125800d5030081150601c82d0050311409007400b40c861810445118081c0b0420b0035100c003110b0154000786c1c902c1030f1141402962145040301d0025034003444000c02285184d0601944010200003565001c0401404103591556200030a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 850954280 1250 850953030 850953041
    0xc06060d08130609080d02071805070c0c03030f02010501091b0c05150f0411010e0f042c070e0c0a0f0f0c020402030f010e131716120503060114030c0906030c0d 70
    0x10008109001000e05c00074408010f0f401500300e042c401024058031700300a110705207040350513966a89403600002030f00d030b50003000e00c1c00065a002c031103070007010781d281001414000d110482034015402e040000826800034040ca41001c24210125000e00040e08030564440003a003004a449000e203140f04107244011640340c51191401000c44d0300c9034a0146070484a21076500b240c141803040d42e00a07101c180c0c6940c80c1c03070200044280c40c0042c0601c01c1c41503404003140c2655001e174880c074003094907500381035010a44804960300e255841c141502c41503c1c0d034030a0700600320040001010012150f4042703100d4440300f0042405810301200002458001c50166402141c0415604040f03d004000314008840031540c0440300ea65a104040f010f9541c0c0d20814416030b9400c2c5107103c0200d568003180e500700701450341030b030343c86000c50b015031024039809001900111090747c04160140a2006e19040050480f44988640b0354214a4a000d0b0400c1241c070350005004035078010400c1c07203410740601852154 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 850955530 1250 850954280 850954289
    0xa050a0e06190206090106030b0a0914100e07050a0e1f030503040b04050f040e0c060903010e0609010911060f0910050f1c051302060d050703021603120507050c06060d0813 75
    0x2c051520a4404000e484d2010182c001102c60307140590030070204152a000c50f0300b0600f034403400704401c0381d541820840c4041c505540f8199003e49800038850368206d070f000090790141d0302c0a9520740b0f44c3d500100b049441c1244122041480d11400141d0710b04a204a05100c0d4440c500d51941019180e0322024950b0300039030000180b40e01c000405000074a00101c10030303100c1d801141c0c103000c07046080d0002503e5403c1078000078007408003c60a54904c0e90290801000050b040080703a14034a004100207002e02602a4151039401c600c4a98241505000303084841000032042007501d4070800c00d0038050480544581c4004221040c0500746030071252500404812440030341203242d5011b01040c1c0000c1342c1c0041d120041c0000c440c61144d006032222002e0b11481100c42000040710740c1c850304154040d1040c0010000408034110700401016003210b0950703040b43c58890108499680c009050b105880390349400b0910307034001000904d5078544640c82800e0140718110300c900b000204a00c0e09455080d40e0003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 850956780 1250 850955530 850955557
    0x30a0c03050d230d0c021f02030411090412140906030916080c0d03050f0d020a0801210b0402091009050a0b13140105211002091e01050a050a0e06 64
    0x4218408540c0f12403aa003054100042608002d51101450310b0396104010715892003e44840e8000c0e0114024000400d98007542c0316140c680403201040c0000a5000703d80481d5603101d000c244101d141000300c0210b215680c807030380c140944280303980150340042d40b035848406c503c0b10402c0314008949544010318044d13103040d0004d140044452815820034070807608828055806002d82c82d030560786401056041b59094107000355505505c8043c0600341c861100d00c940941e0002501101181e0b002e0b040314100d41034906c500410791510709032904541001c10020300035100050110340035142107003c0b030b81c001920300d110300e0925680c0c0e40001f06441088402e00d03030a0341e036210003050707500b03100340f1b00160b80e075522608015000c044440d250601c801801a14040c0d5001c0c009458600d007044000700290382198220361420321013020341400b039804004101c0c0104240d40c590070354001d0f540312103042880147c641c2c07401e080f2001e204946c40d41000b04e0203000c0103168624078456031a400000c1449516400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 850958030 1250 850956780 850956793
    0x1205030411090c0414030f01060303050909010618060e120f071503020f160215070f020a050409050c0402030a2a170709060f11100e070b04060518030a0c0305 69
    0x50107406045240c807074038001d1503584108101a81d12500700e8054810400c032418907480020040381c03400000c01049000c640c6040008401c0c580c00c10050002158100c809940303a070b80700c2c801102d02d00a0f0100c0010201400c6005111290080000400c40140500140681d00724031842902c1d0852480c10808143c00c82041403100c62002140207031003003141c2c10150300d400c0103880100700318800c410144002c0c242c1c990005003103580709090030301c42c0780082000e552921014141040300f484d550004a1052003841030004075801d1074003520301801c0d004030261214104400600029620081c400d14980703542c0c80111305203070200b64280c4455035000c11001030400003031001500400d690101041c652140030200000c0a40c080100e00c2610440d1400100041140e003090b900e1001c080c43c04400d41c011a548241c41686a5001c1d140804409003151085555203120703065a1041d40240c40001d0000c0000c4450003440c04804031b101c0b03502404a95001c0c5480e02d0b80f03244100103820407107440d040714 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 850959280 1250 850958030 850958033
    0x6020d05030c0d1d010e0a02061803120a0806040b18160306050d061b05031b0c01060b030c09040c0509150711030f100b10120e10060f030302070b03071b0c0312050304 73
    0x24421002a80550401051f09041030380008044d030094006040f05044039050018083d10103103d503c241c981c6414000da290000543d006e00180d104483c460700507850300c4240685881d0189600d840a014030b000b5904a8407201504003c80d4030348000c50080c1501c8031030004075034030760701c0c800d0207024016100040c50b2465030160f01491000c10100c001000010b005202c20105840390314042c80d84940d1000395039100b2009114023400d002d50104000d02008030800c10461030749401800a070004075020000950010380030744450040380c0c1444d4000300049070ba140c05c0040c20009002650140ea0901d1a0342540302c0028a80521440100355580156111310752001d0b0600403101c000318200d8244c0703a20048007400500d000c4d4050f100360041612048000201001407180403008010b6800503c0002d44a10305201c3c0c249070740c0b0003200148281800010b01c0324020060364010320300d40d80c910703ca203c840e501401e1071680340b00d0700b902c060300d114800000207400c80890810004103525000e0300d13403426 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 850960530 1250 850959280 850959283
    0x2a0804080c040b0a0e01062003040e0f0a090503040b09030f010510030b28020d0f06030b090709060e060f030f06070c02180411210307050109170406020d05030c0d1d 72
    0x29140c43c5806481014010310031245100c040c141580e020f4541503010a03400340405440100b0510018414000043c0200d9150031044205104020400e00c82c030303141d01c03401c012108960070284c0142c00340d041880140000f1284c503004101c1003c00900303c0c1c1d41912504501801c640741599203410b41c1300603150400030080f4522907141c1c84920030948900c400704001030060400310781c1c480c1011060340002c642c0c0111311150b000201c02800f1100400c1059101d00c1e10041812050340c40281c20320510f00d000441c25414043c40d801d80d40b0b142c031b010189866072003c0c88001da6403003000651501900354143c010790b4080050500c00c02c1b0680c0c0e0501c200050380103015602e5404a1000304114560b002c01002c211a82c840c0301a8850686900c4030038484e55a40910314044000840c015000020307404c0140003054115940e0640101c1c0c1c04600d03a60400300b98141ca00c101d20503600540c11007280b11080341d000c1c1016584c4070650b060308503d8503061410b20401c403600d03ca0001a00e490381d08060031580c50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 850961780 1250 850960530 850960541
    0x10c0f0f0507030e04020408030a0c02030105150d1106120a06030303060933080f1501050405073006061e02010b0a0302040509030d09050a140a032a0804080c04 70
    0x12182001260350059050081075803080c12005400c1c08010500e0348026261541214010305041099070f803100d00c034040043c056407615105034403d41c00d0002081d4407119001c814001c0070700043c1010255134255840705d500030480d0400b241d01c250140706015000f4001414030384a500f400c0d40004070642180340290803908c81d500100c3c1050b1800085174032850444590f2801681c99500d84258142140f00700607280e44181c000c04280e000d084020801d0000c0040c064005042120001e911aa00e13070f0140b00032031b0310440380080090082d0028046200f240031082d0700302c040cbc580015900030340603440801035031034913813005001400d0035542d41403e003c0d485840012924030310081c40300321124030004000c03e0301c0d0301004e48140e0b595000329680300c0c0c003002221101010740409110218440c205503071104110b400944440f510740b41507452580c00443d59400840c0d040e142c00b1904030305845400701c0080200005c481d1007001c0d004a40214840c2c0024000900c0c46e14002d01080c40c040c410300090300c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 850963030 1250 850961780 850961807
    0x403170910270614090a0302060a02010606120c020307030f090305011406030f12030a15051009050a080c031504050c090c0a180308070807031205090109111c140705060c010c 76
    0x4810b050a114865010f0601c000d01111510b11365298011900041c45400550380025030203c3c00040510105406400141c00c464a640300d801540e06c802d20f440060b948203a0180b0f005800c10420040000e00517146000070f1112842d20303140c0d658030b0b560784c13a013140c0114441491a8603601c1c01c200a5240411495a02540601c064102c50400b5040e00c0403501014181c014900e84512021400840700c1407804000c1c00020700c0b02803020200e940103030240c01c10b405424084c0700f038294007003614640000e0070b0382d0880010380100500a002c08080c1c1050001410844090040315440402035503045481800350445000495440215076409444030390415000c00208000c0707a0200049040c140a50b0201c1c0c2c0c010368103c1d51240c1d03e00e001c40f60701f504d40710600b6450b4601003d0100404056001845107031050200c80d9121000f1810400103151920b05584403200b00740320100096010441d60344c2004000017203844094450000a01d00d4001d1151600aa9500d660704111181c2c01f81c000303000103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 850964280 1250 850963030 850963097
    0xd0b03030903060c0d0906060b0a0201061a0901051e0705100b030106030804050904030915030e010f0207260f0703020a02030d0c0305030a0519110307080f0108030403170910 76
    0x109800120341c03940d03c01805040b4a20011a543c441400e240d0802502140c1c0f26004221040d00c0e5410a4090740100210600540c0303090004145c0b40302640501c10544041034805050006280044416500550385080140104866005080007040c060440c2c207100d03101402750355001d0b0000303108840590b41c2c8140300c3e80c1000d60400104440c6000c480582d401580c40f898140c0c1c45060544a00c02c81f0342c881080590076882030741e001d0390b00d42c2c8454650038140b4001d009500396034009805a004080d0040c2c030a000c46511440604405211042c0e41510320f204182444065004d101d50394010400550141e0420b4480004524090000c070404d64018104000820a41d031801410b0f8007006007004200c80d501c801017100030b80c11aa0403540300448000910845000c10b4401180d0307081942c1d620301048000001c100000350b0440c9041c141c0d581c90000790b0a00d45143c4512202c20007000c85807031079039020000020280c43c0c40c0801c0001015035290020804104001c802e40d00281c0e82d45240f50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 850965530 1250 850964280 850964287
    0x305071407110409062f0a0315030b010b130603140703090507030215071e11010807020c060304060c020d091a0f1c09050f1501260d0305150307380a03020d0b0303 71
    0x8510f001c054407d60a551f150015407105000700c0005060101c1c0c10141c22280740e40000641d181c5960000c007a803000c110b11355824241d41d4101a419a001c590f0481601b41003040000d8445119901c102d00c440e01880403500044e907030b90041076845034074102a02c110100051580705100140e622035500d05422104a484800307243c84e1503001c500c1180d0143c2c10800c452000c074100305d100700803c1000740d000601081c0c0d282001d140240c002c10441c2e1111015000780c480102445d40204149021250602c103011401d003600642c14030550f108403000d0300240401d000130744144030100243e40c0360708880d080001c0c1600150a09510301000740041e450179601c00f0001c6c0c08681d050f00b08280c119664850b408907080e21440d12109400c04140c0140d4007031094040003000a545502308074011400030901807042105401070589031100c0c0d00400c030007050500140404180c0e64813070703e150220180c00245580100807881500ca0740240c5200000035000314401040c508a880b802c2e504400440c015840d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 850966780 1250 850965530 850965611
    0x9190e0304080d1b06020c030f0301060c1e11041e1b0206131e0606030209070c0303060501050705030301141210061a03060916050c01020412050d030507140711040906 73
    0x300404c0041c0040c4915008508041a124101705980f201440032008a440c1e6844207401000c4040d407881c183d9140090f16900d4101181c4000325215094120500341d400030000001c0c000a807424111010800c900d1440700080143d561007111603885010100003e170a501c817030007c1c90b081c0c0c050140503901541e0600c0d040017404040d003206400500300d15034041034140341080001000d81c1c0d48065000a010802c020000754000e0b035034803c05110751820002079071503030011a094007030b844004140d907000b040103011511032044001031482d07004003100f81e0000c1c0598400d09000e41208014509600c03580f050000030030f050031454816007000c03202c0e0f0840c13030000001203a0351005400c00960710510038104400030312440480704241141c000a6503680d613078904d888444101103100780c0d41d83c0a200c0c8a800f03040c0c481e0290314000e40c0c0c1303582c1c1c030201d00d00c844140900980c0103020485001501c01120700740c5454600a00c1400c0c4d01800000800588000340340c1c40d4030411451031400540426080380 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 850968030 1250 850966780 850966817
    0x60f02030a0f0315060503250c0b060409021002100e01020304030519121505030c040e03091513030c15020c0604091e09080304052a09190e0304080d 65
    0x4014140e180b800340004219500240c0040118105034030034411941d4001c2800d60700000114091155106868032075545112042d040264551a0000058125081d5000316502c80041c0c2c3e006074004100081015042d40080e445481e80040100940c0002c9407441440c2c0381482540654851000254514a0316540040c500d104014000c1c0040c0c0d0401d811a8456210380154801e40e442a00100f00c0034620102142c0251b03490321170603200344186242c050705402d2074099071130390600c40c400030360401e05d03a0403c002e640030041d88034906049040c00205402010b01c08008000c5000e0b00342c4495080c20250541d81e8440400485001d640c02658002d12a4440804403002c580c5074400004515552000329000390040545410100d403c01940c07005102421004600aa1050b4102c0d98086150001001000da2000081a024102902c0300c01a810000302090780002c01d00100b5442140043d14141203610901c2d41c0101c1c3c0d030021900340b0500c0300411118210203c1d505040b406000326202a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 850969280 1250 850968030 850968037
    0x11030a05150123090a200913062603070615060e0303130306050603101b1b050d030b041b020c010905041103011e27050a0e15090304051008040c060f0203 67
    0x2030150700c4800001c3c20580d40c603802541140011146801b07605c034001981c51268102800980c450284050b420441c2c0f0350500c201011203034103501c001040040340c2992110b4194241002c0764501080216000140c014030554900e40e280d014820340c01030409000030880440000120700941c01040494401c40c0c1d204208030491307078412004580c564521001c00d04050155004a10301c034240321190100c0c10000d00c1c941c01c07484440c0c2d90b82800345110110310048a0659401334200d82140944448091081c1c001c0481e00c0e00c058008503042031b6803494040c03c1c0d0481e600c00d00041c1c12144030703600c0541c3d1014a07100140001c4405101d51148000c00e6280380c4018412180318002c2c486032140310f08240e4005034018854aa00b950b0008214181c40b2a403814010205940628260008070001042d12401c114074010700010080e040c081c0c0c0c20042010070142006d80c00e448180000503082d070301c6610403c003c0300d40b5902e80c079080c101460050401c4400d0b4200c802484000d1600302c005079800000c1c2c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 850970530 1250 850969280 850969349
    0x30c12030c1101140c010e060a0b1005180a1806050108091506030a0506090724050711010e0907030f1406180711030d0608150403080604020711030a051501 68
    0x98080b41d02110040c0e0303122203070410005032003a02140100c00000103611a158000c1c141084d2a0150380d25256403040f00c4040d11703102d620040d00302c501252948200090030203a5144940740c8800703c0700c0c10008842e4415588250395060179a040d01c4402c03546400307840000c040a0074070a01a023446220141c0302e804604441f80006e603010001030f1180e40c2000712018241d040780541e22103040400e2500d449500300c1c0a016824252401e41100945402d036009809014503600d050030a8855520b8001704802d4060b050f04101d18804011125900ea0341401c0c01103147d6100061044001d683c02c50589509041c6040711148440c1040003d40f0760303030782041340301000d101c0c0803241e07030b1b0750075025035031409454640d83d268030000c21100407500c4a90310040a5500140440d80100e9000060f80340c44201110010700040c002404940181820780180800c940309801e41e550f14085400803c0c5003040d8204180d030203501c41981d00d49100d0010488601416058104642c441420450140084280a40f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 850971780 1250 850970530 850970543
    0x30f07210c111e090a020c0f07050d030e031608010b0102190b0a020a140408070314030a2007120f030e150403020d0c1d04031e02061308120709030c12030c 68
    0x41c0c022481c1002000c2800f000b0020825002801c000404200940103030451841504c94000030b0ba401150001c2c4040c00c81d98003c2c558254070405070380846020b1120014640c051080c510ba820800190005440c090001c07140000b4440950100081c46e0411171403c1008003800c0002c21004110301019040d401040c00001682d104110391007200e402c42404580c02c0d007c000460085204800414104100d900441c2e0340d070a040100582c0030f8980c03140f68451008203c11407601c00c0c04088142549843c0c85140064501041d52400d0f9000a100c048504440550141000b0000c158201103501e409940a86015150503103040680380b06214601001c2d1046254011141c20001d05626910182604400e045440c003031030081e0300200401901c0480100e4a5031114520078501310109085080c003079401042d0b1901c0c0c01c5019003140000c0304098510000401089d100340e10710004150003841c0300d54403e0b4010b850b5080c003088581190b00a489005c0c81c0340e20413400300764491000401282c110b107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 850973030 1250 850971780 850971799
    0x52a13020310120f0203060703050f0604110405030709060e07020a02010207030f231507030203070215040f140303090d0203070c050103020c0114150a05030f1905030f07210c11 77
    0xb07a0304041c4160303034060f0400710540c0d44000c00b0405502c114501941c425022503402da1110101039040d80c4003110900b40d0319202200140310b501e002d8204071454400c28035594a01503d0360b012a06208075600030802503501e60b8010003010a200d41c4665001c0401d1010300a2505103500003034413220381e44001340000c13544d9940c0c0028004100e41c2164089044103243c00c14071100140f070394070780603008000216a02c0c0c280005040d603010b4000c880c42401daa50227000d02c5422458a40152440036105942c20440e40120070001818006a00355610f2010000e40d180c0c5070140349130b4038008040c2500000c542085c00043d00003030308500c0e034a003035400908015840b803001d4130000d40180020628441d440084000b0301007050a8030601055107142aa0000e462a4441e0300340340e5603060001031041580c1c00245a144184002412012010f1150094a20b815400d51181c1956004142c00707a46c682d03c8a0203005c00401c5aa21000e0340321210704006a1007006a20b98009401c0243d52a502510101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 850974280 1250 850973030 850973041
    0x60303070f140c040228030b0a060f1b1b0815010513140705040918051903050c0106060f2705120a0503030406020d050c1c0207140a052a130203 63
    0x5014899503e03802500854448030000400c009034000d481c840d240048595590565a078031a0240700f030b01d42e5026110400b0507152100488450303d119100c0020044410004829142c0004d4000c1166002d09200d2040010150f00702d20f000d64260302c8400302d075001c010424420036074200303600e046450462b102c12401c6c5110700b6801c050143c030451a4a20754055042145498004010703005541c0e041404208c8400c00c100118803000e06400c026040b9407260240034021040440085101c034800d00d009801c000c40001e0541c00c2d41d803160003800200300000180ca04555001c2402d500ca0340700e03a00c0107050f00509400003481e203207590156038018040c403501c04420400800c8000c55055000d422241c0d28642810104003d4001c144801403840c00c01c001700701090303410007c0e20740030312031008006403110a10540c40c0003540301140490b840c1301540391003207200b08103000071808107000d01e01400903600c12001c98825812084880598480b0030108441c89484404200790000740c00c0f80010303900c0d12078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 850975530 1250 850974280 850974283
    0x90c130317040521060702010213090207030306050613030528030c03110d08060f030607080a020304020414090a050c0405010b1b1207050a05190f0807030e130e06060303070f14 77
    0x1603401c02604a00790240200016107540042c3c140c40c4c51120a5a10a03102c3c01000c90913407003408030514118860f450705100c0002c0c10b90042100c107200341400201e003a60798012800c2504282c0c030034480201c5604003001802414048002c00f0f40000b440c40c3d040211398184001c2e00603d4001c06001c00c003042c909201010f01410001c198403010404450350384010000080482404460860048080d080012030710700300014824003d010b5612000010ba585518100c02900b00800690f4055240d484d505201700e0f0743c030340c010301903c00003001d8a030f48a21030801d90f103441000100b4600135440c1c0b500400c0790503c10001d440b5040c070718100c049010082c6e10a0a441d01c4605d042f00d80706194000b9501c3e042210029005040c41c0c0700c0c900751110400242d00805280c0644000030742013800300ea00d03a40026503880010f03c074643c070a0400500d0b100e50b40c3c0103d42c0645035214a50100b40da01e04a10f1001c0741c1c20030140b035101c5400c4000b540f805c04240d842401411031080010f208000b000d03680c843e2500d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 850976780 1250 850975530 850975537
    0x120b1003171e031008071d2a0a05070b0f042d0507080304030b1b0313030507050d05040807091a0108040218160e060c070e070e06030114090c130317 65
    0x54058000341c0f60b0400e40d02008200341584283d98081c421903200190b0f487c0f5040349105000c4030164202c0003a640d404480100c040c1c0152000700d1001400c50300ea0b078104802018103a845501d0f95003d894120360b1070855804a406481048082001d00821001408020b000150b8001120494000d9a20814650307072050b40d540d0000c000e400b4079640414400d03000005030003101e008030860320030703915406e08103904050b82c010b100516500420000f201c08100307084042d8454408c0c42c2c11481e00c2030130b0b03c441d4203140780300d615080003c2001508006075079080280f10f0150504080c20000d0b1103000001d54180640f0547c424140303c4290002800e44d661141030440b107404030b50f080013051410440100d410000c1c0006a4045003480d11000c1850400b101a6a101d20000009240c1c60781000c103d0030608034014000c6d020410155006565500d951024600800c03038042182c600440300c0707003040305021004110b0001d011050080e0040c03000f04007220701c01c0341d0b0420070308840c4c2c0c0d0000301c40703601c54070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 850978030 1250 850976780 850976827
    0x50c0105011202010201110703080103170415080106031118090a0e0609010e0709140a0914010207150606180e0603100e1507080c0a050c07030606120b100317 69
    0x1480c12000103201500005000200c6200764003c003c101102000f64043d8020a130b40500000c0344d580042c0000703003402c0e40c10808541481c005600f440d039501841202c9a490719442c40018407454010084582c06000300138440e00c080300200e090031004829290000c09610249106071540c0d03000c241440f04a1780511804208101501c3c0a49071441c6a10b000e803104501c0c00000d03100340100014045614801e00650003841110407241d40c49003002880644611181500d00b0741020040c5403440400744010403402d1700c02e0366007024060701020f00d14115400c070b62003007003481440c9e03203231ba2141c0f070060491034280c501d0401c030507201f0303110300300407030724190f80303825040c041c0b900d0110001c00c0f41a00003001004e103410a9a240d140e9a12080c00301c1c0c0b484070541c0c0040340840103000c8010f0980c0500041c041b180110001c480c88250350780c54100c19601c40c0e5001a40d10f02440384078200b8000100c0f400d41d0300424030400c181600d40b42d542e4810600c421608800c0060354040b41800d00303243c11030030f2209a034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 850979280 1250 850978030 850978033
    0x501020310171c0e01020c100c0201090e0705090d0f021003020405100309080f091929070510020c031b01060513090b0105010f02330c120a020a050c 65
    0xe152014184201d00024024001010036060401c2401c2000080d40c030a11000b030856000e02d042d0164090b1341e001c520314562410b5004180c100c0419465000d500c1584460a5a8074410a000c1e4000900031a0554003c00c032079552007001c204005402000f124040034003500e1400d03074140c203400d041305441d1700824000c1d40b15102078580c012031603064015005994044a081010403507445069084886061000340710b14001d000059850a03521b0140a0f000300c043c2c11101200305240f003012400a0b90341007120451204214005100b003c040b2103e031180075030710000e2405044c0d03120240d450000c000d01d140c0c050f4001a40c0b0052140c14415a07080740090803107014616105410742d40601310a00480d406004016400c0c60b1180aa00075903035039a40000c6a85840c0c3d08100046640d50360046044065210f9078030400c1441c0140f940482d50b100c14403007207211410000d0250b8101000c054900304000d8420310107046d107004154000c0303070820102040180d40d801c1102040d141c90184000b004902d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 850980530 1250 850979280 850979287
    0x1502010e060106230f07030e0306040c0504110c0708061006080103050303010e04061407020a03030c091d060102070509040f02040b0904031d030c0414100603050907030b1e040614090120070c03050102 87
    0x1645d0240ca20075120361580c06c0052180002d05599080c1187c0c0503000c07880702c01040005040c0b0b41c1c802c000c96880211400e01d407801d80840b081c40c2600c00e9002c00b40c00d034001000c01014100190b07072034001d040e49241074442945542ca0700c545c0ea00040c02005000b41c902e00114081200c036511902c5040c03154400040545425940651250800c45043c1e000c20305003402c01d002c1c240b04000d240e095034106100b120700503108035080303c41c07610010801810b511440c90089102c0d0307650310186100e0b5224147e601941e04143c8180403d48901c3d540e9a07018816070382c01e01c070019400c40b03c03128004d500f921300003501c1d8460300c00003840c0c1b0166007601a0400e140c0451f12035a80d110809240c4200049000801c00c82d50342e503001c800302e402c200d5030300782a0340040700140b0008034081000da400000074242c400245041d61000041d01030195000c86d9071540c0c1d0114040e0451240314183d41c8a084600200000d04810032009044083d00e814080c644800003101c4080044030307415103001e1a0420000c545 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 850981780 1250 850980530 850980547
    0x14040807171204450e062a041d16081b0304170d060303140f0a121e0203150d03051e0f12241302090402120405071502010e06010623 58
    0x1000d5488481342d0080b8100a0346100c1624002403150082ca201c00c0d825100307030580c801a084c13015092040e4040088204000103201c651002c400c081c02d91a00b90101d082c1c1040e122580042c55070402240520050002300054442c580c0d41c45208818a415442d94943c6d891030303c2da42801d484080005d1110002c83c4655030802c0c1540b103a01924400d44503040c0d9550195402a602d02403040d44500c161410440d80f082c05203da0603207012000d0300940403400b43c1151284d155458204892050742030350200411000d6043d2440070826200191504a080011a180103105101c0d90700c030241d02c01784004d60314601d481100b04603420340000d100b049480303054208000d505000c0c19a0000c000d0b812000000322445501c0c0c00d0310300e0b034035402081c10b10440880c121a0010750400400e143e0b225509218882c2c000f104520401d1091348030782c0113000c109003081070714604d50200070311200441e8074280b40720485a2000420a041d074189040c1040c9815540114580900c0d01231132400e405940030950b80c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 850983030 1250 850981780 850981889
    0x203010f050a0e06060d03200f10050105010e090f180a12090602030a080a0506040e1006060306171002030405120a17010509091c14040807171204 64
    0x600a030440c0c041480112040c0f04456034542c2c1c1900c041791b020307030006004800640558104e00c50024000002558100d1460019080007414000c0300644c2c0c0104102e05280241c52040c0c030b001d81401d080201c4440c3c0c43d00701056810100034190042c05c80888086481f280001340d4540104685004880058540f4034001d15041c00790f803414008103031241c1c00420580d0000c0240d4100408035034500429594603510b0310007814000e03101035003050740d805100720b0410051200907001c988000b0007241840c48c1c0b880c01411150350358007940c200120300f103000e07807003a00103d0326800c40b01251a000da02c0e500e541c10301e40d08003280d4000d041108800024045101c0760010b03218002c072182c4065808160780c2c0c40050140740c10301220880500c2d041a282c403008800d204c103441c08403125130f182100c140000f82003107892980c030640003407019901050040201c1902054400a441590409072054202c41040c541740717402107005500003200b10f45880c0548490b001000103000101450841d80100041140c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 850984280 1250 850983030 850983041
    0x20d050309062a010e0d0e01090e07020a05100b030a11040f0203040c09061a09091509010b09030106080a020d1203380109060806010c022403180a0c09090206070203010f 74
    0x4000f85030100d41d00c040c98900c180304444000207014050040c004441504031504100c1400340c42c10301041003408124a000500c107980300d0001c940060070440c0c90be080c40c9140052440d002c00c48030717003804240b201e2a10085186400740c0c0d4421080d02c800211180010003400400c2c5c241c20b5401d20110410043c855541491000c50386200380411015444240e000c0d0b4021a022840756151010041083c45040100c441c0c1e920154200e21100900100000240b100000f0b070f10103d981100862000c4503840c007845050b00030001e50004005491613940494014410158050441030380c820031211140d0098024107841c844220407000030600d80e104056900440201407070f214282410030340400e50080a01d18192185516242425503640b001196210010802241c001c01d002c04541e103818240d03070400d1015007000c1241c5490340750408180c001c1000b40d07000f00c035050f4448200307980032070a203400041c1682c0300c1000100d00c2c10320360700100300b86100301304000b9050343c13806030700789502a10755106 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 850985530 1250 850984280 850984327
    0x1c14030703030c090f05011d03190b07030e0f15061f0f08070804230c0904061d0a0309061b05030d0920030c040e0f0a0812070f0c020d05030906 63
    0x1200c41150300e815440c6821500343c000d442c04900e4103c1c98601c2012122341c20007105100030111000c000c030008881d181c02d0076484048500f620054107208100750180603c1c0042d6280100804040d0380340750006a6603180361a4014840030101c011501e151154901c01030502c0c0082c840c100400c08d0034030f00406469900700c3d440d00058928011582251041e01d200703001d2500b20310500800d0b20008080150030000c001c0c0791589204500f12802e26880c3c690b03c0714843d0f07014410026040c1c900141c0015000c901c0c0c40c6420040d000750141a00080c0c10511040540e00e0602d01099420508040e801d684101c0d81c001500170710000c500000718051941082320720328403581c000d0b13542e030710b40b038a8203082c9032010b9058960541040748400041e04056000c40c414100100440c0c290301884941c40b401c2080c001815100c0c2200011388000760750384420110303008042481d0481da00c0b400020b00a04203214040d009100d404890900703c107104040058030340000000f42a0303966458030b210f00f50481c401c1b00e4075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 850986780 1250 850985530 850985537
    0xf07030b010b1603084b04080d090c03020607050c190501020a0611131508060105070b0412140a0f141e1309020d0212151c14030703030c 60
    0x104a100c140b0707041e02d0708154400c4414001c00402d41d81a034002500804004a0101000d0207981c86a100c00120802494100001c448082c103042002ca0748003040c440b220180c8444828000020407110448005410301070300003aa901549c1b4005444004a520207948007002007050400d010010503580d0111204950160080301700248011040d00e0302c3c0f05a0380543c101541800200f541ca0b002503483c040c1c8110528031b0001c01101e400c203445d0458120840d041003c401c8070008513040b40295401010908145040c070000b030307440f00c0074400018002040e0310b41c90145060014021484c80410b41d03550782090b42c881d180c1410041403004030960250000303a9524890070314000c00000c03160200301e40c1c01500c07549030070401c0c1e8542660090103140e40300d0320300c100002680b402a101400d8102c04000c00965942d09901001030203003c040c10914540c2510403004235141c0e01c00021810241d400401104a00c1c10b80c10004101a0400d901c419207000c0060030780708056241c1d1000e80072187d940c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 850988030 1250 850986780 850986803
    0x905190e070e031b0303160c15080903031311040c030e1501030c211406010311060306011218020306100801050702060f0a181b0f050402090603060f0109080f0703 71
    0x641c11114080c005401e0364044c1c0241d01d6801d648600038140110000000d002c0702c1c50b10328000d03840351a03503409034401e6408c071100920600482ca0a165203c950886500c0c1c151020700303110704200d403a03110240445101d070410301c0d129401c2194000c1507885280c03004208128809003038001078003510002807401a21300598820280356440c1d03d0549059a0f000100c3c54800c3d420140701c41c80440c9644505182e0f15030010088001908981045e406103020002916903035145140c8a1001380c03801ba0428880c041c140100080c99034026407802c0c055200b580041800b02d240b4026950b0302144440281d09401a2000c01208032032000e0020121094400208843d546400041b40c454100340d983c05220b220000215030520b40a401080451188560030001201e0b07503500d010b0645494800ca940560092004004242c00b86212400400c1d05403015807601510720001070242c070009244503c034000407044650580d00c01e40650016001a0046580000301360b070100d5500c0c54148001c44071692580e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 850989280 1250 850988030 850988041
    0x2030706020a0308130206090a03110102070b07030c030804150c03050603151605090604090606210204080a0f050c062a0d08010302090a1104060507150501030b160905190e 75
    0x2d40c6102c103a4055490100b00e8403420b0320641607100c01039080e82c1c44002480b581e6038586d54800d52400070b6201d1203402c144890502e002a0600559a0203031040d418213100900100c0e422400ca00e886980c5460071074000d641e1850016440354021076207600b91480c0c46076420440360150300c04c500410048003110b00043c110117903401141012146060180d010a81000e4800d0044014081c03c45000b800309081c143c0720340f122022070381c00b42c0c4140c0001c0c042c01e40d08003000643c4d240b00e4011000300346c000c0d0303c0d00b030914003065a10408088002c24110010404a0a000c405c0c030030710040280081c5001e07aa004904213200c0c0b009010444414906a604483c0070103000001c0c04c0120801284c4509910f607103541c00700300c0006001042c0508840d2107030071990b260a11000108007030801ca48501303446882508010501c10301007545d04008501d45401071003c01d20640d0162750144070b0391702c04203035540101c0044036192095131040b900710640b0308856240c480038801d0b85060703030006902a401036492 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 850990530 1250 850989280 850989283
    0xb040f030b18210c10060e090d2001060e040b01030c0b0c12160203010501031b1d340e0f030a02130c11070b033c04020a0e0f040203070602 61
    0x2480e0b56004a81c0f00300020f0207400b140254561844146005050404406803030190412400c0701c80a00311503503c0c0d900f4014203652888154121113100000c191a00500320090030b03c40920a540d03242050b10228240700c4c3d1000d410160181420070000c4150381014a030640704081d080c00215440c0c81c01c00702c081008540c03c0c00342c8024104c444014100144070101d1104254088840a0600c6d244428100c0241e10240034281c0258482d41c60020b4200145420400003901500601a00c40e44403100b001e2521000d14443e401c4225000c0c4c0d030307a44050360050340d02001c1c6210018155400e40000720103200740c02c40c185000200701561708060204e00b4070200f60701c4554034076000b98882d586410300001c5280690000003c02c6041c200803004041e10307107865240c0041e60b40000103802c000400c210301c000d0b40030b0007005d605001c1140e13200e00f008500d003501c98208a0b1510582482010303800a420740d2754a107601c10041211400e40e401c1814664031842d0350007404c0394240c2c001e200340c201c0014140e10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 850991780 1250 850990530 850990561
    0x1c0c05100c0c0b030604020706020a1106150f090c0403050f06011503180b09010b150d06050117040f0305041802091f170901060e0f160804080a03050604060b040f030b 73
    0x7400700070002c000d030524a5148080e0030141604d9045a8207011010006100f440140301681d503985030281000c4541d4646407401390024180c41d0b241142007114541038442100c0184e803580e0854005419507030756451a0200c0c052540054814490280300b14810705000c01c107141078940c907045004090150400c02c1c0c2c02d88111030004040184010f82c2c45010807a442e00f61600894040c2c00403d01030707211000580078942c00031248501c805d0024000c10800014802d000c02450203003410402000c01912800c242140140090040c00c14560140c0806200c1c0084a010304042a548002d070903140016800070f4002040d0311f40aa00071600c0f48040c030b46032643c40c1c5661444c3d99180d00070001258180307a0030f9400640007102030764a0b07103408101c40520b1031482d481029882c10000702403805030034240c40f040e00b0090103400d002c3c040741408080b80c040c40c00c580f0044001c2c1408a00d980b80c4d000440c0042c0025031041031400000b0a0100c0d40040240810044900031140c1d80040d84441200350480306 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 850993030 1250 850991780 850991783
    0xb07021002070c1202040b060d0c08010e0106020d0516020406030309030516050a051005070c0b120703060605091c0c0e0a0b011809111c050a290f1c0c05100c 69
    0xf000e000300480c0d502484504681d52000d007000c104400c0101c0451381d541c101c0300d0000c540b503480c0e80550030210b901c10410340c010000210030303015a52400c0d2001e9103034043c04481008101e0f0005045684016a40000d40020b50103881008241d43c1c0342401415508640811203803070040407032501999280b105410183c0794005c0018003c030b440c0c0703820440c05030100c404400c18444280541d6001ca040b059116000742082c0a00640e0703021514480d00000c1c01c0109030714285454804244001e690000650f031082d202542c50090101d040b41400390b008003110f6004000d02c81403007021542c1001c0118640c05a019600c5c01c1c40789035482c000642e034901540d060102c0081601c40b003045402d009401c228128030b0a00d014903d0003a15000c0010301d4050301c0410300c0b00a440358140100c9401c1482071107810a9007101010711949111102c0e40308401c1048040d00c10b58220307400b210786684808030b500103924000440014980c082c9015410350005109052240c1d01542860007054020ba65115055 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 850994280 1250 850993030 850993043
    0x121501020a051b040905120403032607050702150a03090b01080a020102210405031b01090509222102070905090c030d1101092a1703090103050a0f05040b0702100207 72
    0x51201c21181c001c080701c3d08429548140c40f600d8900103d001480000d040703101c454011503a860642c103020300058521000000c8145809004040842c00500010307040303002c42c600141d03075112a00014910764a1101d114a049100103519107034181c1503401184854841c80b5a001c0c2aa84c800520740c4600ca0000c0190150b0401c044c081c0d8107880041e5480d5820b180c0110903820710b911100407a1600000341c01183d9000b1201c00b20384225070700885500001c08081b0380446240c030301503d0002c120040215440340c1d445542c40c0e00300c1000b503410342d405403d02440000d04607824070703050000d40e544414811113a02c145042c0114405101c045030000388104081e00500180300954411600c910140507e030103295030700d503440400240c503000c0020b40000f00d000d001c400e01c03902c60300040050505902a80e900c988581030110104030200a64000c203000b400c0c0007072541c0d00c0310b60810180a0f04400604494580300801042000006c601c0740198041c0e070880e040c1140b6001010224490198080e121 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 850995530 1250 850994280 850994293
    0x15050102030d05090102070b040c0617010f05041503170d060e0f06131808041d062d121f0c09050d150912020c03030403080301120c0b121501020a05 65
    0xc2c1c0ca002e82005070850503103000107240c813031161280004200c050b5011142c40d1082d1204100303071303644240b045e820728100d045100c256502d0040d60040c0e940c00b5120b0140140d4640f11011821040b000d01070340219001140d20800d0482d944001401d50700c02400707024180d05c0c061001c03981c000400300561040e0390384c040e0a00d13607443c0e900402c0540f40502c02894001a200c0c1c0b0144011408103080d131010300e204604598450342000304130703100070500e4901d00c10706030640000c0040c150744085206401028402c8000c0007044811001044814074200b0960014901445205400400960214000402130024000e00e448d840440160f03118403000c44001030789602c003880300b49000303c002d051640c446c194000200d100f42c11758205031049098141d4000343c05052008103190103200e860600081140990315003401c540d41c2c803c81d808180107140850f103044900c0420043e52100d10302c060400b0240c5103440340814244180a100103c4030340c106d90030101d00c00d1420354000206001c0d19039101d405000c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 850996780 1250 850995530 850995547
    0x80903040b0309070321030612050c0112020f07050309190e010902030a090209070f02060c0403200a031403030907050103090b1b090a080109021f1706030c0a181505010203 75
    0x9400143c8058050300511000000280c441050b1424020300c1d010b001c03d00304000600a4100e81c16a480a0342c6c0310b01500100002810100b81031204240c02d0801717668400089500b600280104032401d401c1140008851045c03100000203080b148108aa8001c980012100150321100040c490026140044001445007504c170742c001d1a030101c1c0542c1c0c000b4004a083d000141c040c40190b81c5040414034031503010541c1d550500035103500181209905143c05d140d5a01c4440c003040070030a030f400c85080c096000019079100c500e1340000359002651008607281c80b000c007580b40c1e442603940f903180e44541c64000910707501901541411942046162281c0e07903d1518059180600c182419003103601001110b0060b40c40715a454094101d1900015400c1010300c103022800802e00041d000300756068a0720990701d5840142c521a04440a1601c407094980e40042860312002c410300b142e111114440c0403481031480641200c0e804000311040c8110001d041a078080034099001d03450060704100039245 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 850998030 1250 850996780 850996799
    0x180a1b0207061110050c03060910120f021203040f1d070c0f030e0411071509020f100c08030f09011a0f04090816051507030522050312011e0608090304 66
    0x282e1002800c040e6842444c0c03081400d4100e80c401c0783c9203441540301205104603030422500307280d1b02005118500f011b450900303c0c004041154040001c1014088005180840d22903040340320000c031100381181c5d03c641c2c44485403226030200d4014200b0340c0d07000036801c2445c486403036041801620641c8035003038202c805417107040d0307030650164007901440400200208a41c6403481640080318400140380e842e03001074500902d1322003103000c003002c6450503e44803401613a1084841c0051000490300c9001d80d4040d500140d40301d401d140c8014124800c0441000600e44d002d4009a1050040c00000c12120100c0008a0702c0081c6004169801074060030a07407465007007079484184541c0c01050020304103280d00e184500d801c16101c0c4210307a59004443c4056003a00c1c0046c03201c0e00a40141030078041480c0c103400840e03010030301903800d00d120007141c4102000c0c8202402118008603d841e45c1881c41c0d030710360040302220300a0480c0410b03201c08010b000581c0c1440cc100c0c45020320220300180d883c1c5442c010109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 850999280 1250 850998030 850998047
    0x30816140915120a020c0f0a080f090307090203070207051002060f0408090109030602160204150b0f03180102031503060c070804120611040312030f020a08190b180a1b020706 76
    0x700010821220070100f050b1020075128205540b005a81c0301e1021940c0d0b410f192072400303850b6580d400540c8950006003460309841c3d140030400130064440d4103210000c0c0c40c2c2201c6500000a1500c000180000a40d010881e02c00f03452080d9100c800c179030300c072650480e6500400c030f03018000f48000c0000714001590b0a40104081401450f0400100e074580d00c46204982c0308a800c540140c8181207803900b1818240580d5441a2081a0b84041d02e45410a50350692094646040032031b00c1c0040024400d00c2034403040525442c56030001c546900e003841c15000070040c88440b061091249000041444d040c1404455120340d1005030320742058500554020049031a42d411240e80b5180d41561440c2103c0c0e000bd0401107020709050802048502800740c102d41da680c1082c90454010001c0c0000e0341d82291304d0b5908a003105140c030042d811610000002041404400340d880290380e4880741100c1546100540a011004820070400d1030b00451004440741d000e003c8405030304441c404009040c05230051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 851000530 1250 850999280 850999309
    0x1107080c120c03370206041e1a0702150a0207030207050603060a05010c021809100b03071202090a14010815160e100c050d111009030504140307050a030308161409 71
    0x1103943d400f00d0315103440302c100180004980113070f203c0c0d410003050005045070234407104030302d01d400072031464641c40c0c0c6400316010007940943c00704014082000070740300b001000c0d84000100e104404a00300003d400c4081c0d0303c880002c0d001403003140d002041c43d190040071a400340c00014860000740340b5210040d50301039a147d0741aa0310030340000004884601c291982c4c2c3c4502981e0000d080d0a00038030400e0000c9a4900101d5802a844000c0901c9000300d0705402c1e51500360102c4515455964618107a000b414280003c4c4a40292500000510003000201d2007101d00550409040030b55650386040c1141d10b10188000020b1350700c030420181828414600b41902d00c59140c4aa400781994460278580b545080c00c41c00040e5196104010440c0103001054401320009000d015421180d10000c169000b18014086603901c6003500518a64007000001f00521000d00501c40c03544d03070b90601034010001203841808100c861070310b43c142144100d80340c00c20034240780303151820300402a0610030019242e28032b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 851001780 1250 851000530 851000587
    0xf100306080f0f1b0306010e130236130807050a0f0c0608070c0b01060e0102010605091906050603040807030f050c010e0607180f03020609041107080c120c03 69
    0xc003192202050280c0c1c14041c10040042c5004110018100c1c81c1014500c109451004100c00c030311581c0e034022070100e0446a4030a48100079450310318064040075032021009521102c0220721201d108400c0208410b4a04069411042482c2390025102d00c18011201c0341c0014010100c42d00009182802403d2554001c0c01102d500e40c40a80e0303020078000c40c0b1001070307035007889046042003a42e50001505038004010301d4a19507840550755804030424060042105200e1b5505050615074802d40c0941c004240c01000e812990030f19041098109003611210402203081a07404515030500d202200e00aa0307000807018500011614202d82c0201c9810030b00d000c200c02000ba15211946c240121343c00410a04040d00c15070501c07010203082c48048000000484005550400c000d07400d07683c1600840e034050320065a2600001c0000b802420801c100316804803002c614030f01480f84040203020b55a01480440701408a2104410280e00a02103008625441040451340782000c6040266040a02c42c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 851003030 1250 851001780 851001791
    0x60703150b040909240207020f100f08151008010e0c070803150d0803010e07020610061b02030f030c030c16030209061309060f0c02190f1410060b0901080907050f1003 73
    0x5101c0c80105100141e41204150046640401e52a10158270803245900319503c8040c0020180301500006c98024800c0c1840066400200b541300c00d07260003104440000d05980e1651090350018124840a028000c0726460b0034001030b85c10304c170103001c40c1c840075004000203003942d4505a200d200d0320390942c5550741000801151f60b00160b0f0000145010300007a032020103441c42c0040e0020b00e0450014680f009080085004101c840d4100c40c8001d0400b400d00119040c0740154004a441c2010400d1a0102440002a11780c050840440508a0005000240e504054801100c1540d082450102079400400400890154580070181c460305056248022a842d4507035164001107030352044071040380e40d0b02c8141040f82c046d8140484144e05000e030300700081066480c1c4403411010007022004082c011070f40001003004000b04110400c40114460a008907a221840806d6940040c5051801701d417208010031800180840c554040e21006401c4188500201040000302c83c03400050006055851 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 851004280 1250 851003030 851003063
    0xa020d05060a081c02071503090510140a0e030c030a031401090c200109061a040f200a020f0d1718101a0901031a130f0201080a1d060703150b040909 65
    0x5445c1651503241c1514001398008035070400d540be01c4210b050514500780741454411100032102840d5400000001c400140f81c0705403104146144900a044400ca202c040f85101c0f80c980e054001020703040400380c1030400c9985c3c0d8015102a14020007290020030400b01001d4101500507603a032003816904c00011907403003802c0d11100c08864003112400c1c0044402e20500c4114200350203100b40c011600d0794104440c1c1c403d0380c5030300014107041d004110100c400098400807607100300590448a41104240c4c0d841140441016244840710051201c2e404141e00002e00003860518940d0a109090b002030000c1c021094044c10080140741c1b0380790034242c88207021180e5502c60203041e0703010f54454900202501440310b800e02180078010490109003d580308003500050050a07040c0400d40c0c20300340b000403510340c00c1c141800b40c03000700c00104103e061010ba1f01c20380e540000d60540107106680302040001c0d003406c500f4040300c01a000d40003140c0c00400007008141c1c241d5106036400c0340980c02e03000103109030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 851005530 1250 851004280 851004299
    0x415031d0a031d09151c0503070b0601050405031c3c030615081005030a020616020a090f0207030e04050610230f040608010905060f21060a020d05060a081c0207 70
    0x54866060448034505c1240242c1000c00c8010001c0520200d2100b065645540d695941e11540600410500d06400481e90030707405a800e95028120050a9403450041031030141480d2182c0006080016001d03a95040c2c011140030310071204d0b100c0d040c009800a61000009100c0c0c6200c0c03c400b03420581e40c3e140004444062050341c0d000c100039565140180d0400c080080c0c0d01d281f0a41101e0303c2508030380d031072400507070302c01c0304485c3c82e6040420002c0e040d140f0b5000154582216500c0380d030307115060400600a0b24510340c0101029440307522001c8801c040d40040c4012030302c044034030036007041c4107803032001180b40030b078512030301381d080c0c10410503c20203003c1e900c1101e80c1c00c0036103201294500450140911608102d400e0f005d461988810081454803c1c00140710440805243c0d00030740500440751004121031001d9504c888183c412a0381c6030402501d0840298031004680300203903d8480800d016183c0209020101c07000c02c0001d00217101549400c082c1c1281039000e41080d0703c1150b0001540744017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 851006780 1250 851005530 851005549
    0x201020c04023906071404031205030421020709021c060605120106020d020d03020a030207050a0c050307060306080307030305090a0c03060504150e0d031e020415031d0a031d 76
    0x21200c2081e214044030850300307007a207610000c2032100c20700424401c240c043c800100303140c2c09002e0f8079017a07455052403000100071b4421034101502d80e480d51201e400d13160350800025809030744603405080c04a460741e1120712018400d503010500503007199008018400c0c00760003600c52440030b460822101c14515409504403482d0350310410100d940441c1c01420000045035542c010045400501340355040701000a4075840402c10090500d07501081440c0f10a10940c140c6440e030b503000c003c0342e161079614241003003081040d124843c40703486031580c040b41c214428000c400444400000460411700c03665415009064010318070929880f0380840140466440c0619030000c6000380360000d45c07818a030814044a00034111681065400d050140d4240c24000403444040215032400107004084248644000090300c5419000d00f030000c10040313a8a40b6010303507400c6031080b685080160305e0001c0303071b40501d40c0c0e00a46105840e1308941214404a80920040f09500681c0006590109101c10000d038603c135 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 851008030 1250 851006780 851006797
    0x9060d0606020c010206040f0206070f080d061404060b070f0f0503030a0b0f0f1f050d060f090507080112080306040b0d0f0b010506032406090402120405071a090103090201020c0402 79
    0x1500c5030000c002007901400484460902031004e401c0500d41515040c540c0c031000600203020320300010b5642c082c440440010242582d00c020b0185d95120070040c03074005440a4061742c01c07004011020f00ca0149024896802210080d0b0303070090030000b1a40f24a100c1001800007075640310401c201e04d00c0003440078030007148130f000c2c941400682d44005000307110182550201caa8041c0d000350a40032400e6552052414020f08414001c0042d0b000c03100c01200d00c1e01a00e90382413400780c00d150340407c0f682d0b07035000d0440a41d00142400c219550300c0c140100c80c0c140d828072035040d040002c0e0005a000c1841c090003182c1c0000094004181d650602d0007041d2004200942a41c2c0b04804055a4040194079a061130040c04111141411401c0512010503494000301a514501c2440810342e41c064640320306444070024010302c01c54030703508030130154030114070102c900715940d020380d00020803151400b91413064500d40300004181080c0728000154010b0403808816030541c82007600242e81e41d0b50f140000c04c50b05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 851009280 1250 851008030 851008057
    0x114310219081006081218131a01080a0b090c0a0e030604080910020105040203120d090b0403020a17030106020a0209060f040504080a030c0302091014040b0a0513050409021008060103020906 83
    0x204480c03e07160044a0054100c1e0403140c2004611a8072100e0352402d45020f001031104000e100001d000010300b01d00040740034021814103000201a01c0030702d04e103011020400c2a05d40701c0c1e00c0c0c0e40700c01000c0d0485000e80038003688129604080f07070341d407034002d409401480c40500b400d482c040321500000340380000448003202d01c40c00004440400c0d04058041c555440d400340000d0080781460350020791140040c2111180c20b402c081130001030354410383c100c00945500181207a1003400d003810000d458000300031003956480341140e031000f1154240340480e8106d601c01c1e40a0710844440d50308100c100880540303500d911810b900100b400740d6480780b141038043e0f485101016910001c8030780150070790b40c060105009252050103080400d48034001c0301210103034245880b100c40c4c6186641d00901d40a01d4000c2c100401000c80c0c050340550304039005105021b000e591030082103030748404003c103a0f80329131002034111070a01c0940d82d40030300941c03100350440c1050401606084209000c2401e070b800c5495483d101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 851010530 1250 851009280 851009293
    0xf2601060e070306090b0d0213060b07050f010b0d0c0905150918060703180f1e0303020706051005061b0708010e151b040e0a02091002011431021908 65
    0x102c0d501841103800401000500740108240400059a0501c0450001c0c0c00384420426080301081d0301ea0000001d00802c00310300d6250394081c10200d40d100f20300c00340c04501d9881c00401c08070a113840110040c3c0546d0012409500070f0421130b1035005044042c02c04503601c214004001c425903501c1442c10300c83d00302501e140b0303008075040070218500000900300805142c507161248503000c1035100041840d5411038202010920940f410107961103e8900300700b04d038021100c081041550540042c045940130340d005201a4460790f040d8602c0c400544103255020404100140d8103000680e440d01c024841d010595401e00d5482c5411804e540140511041d6a0401203d10102c0e003010b43d4900c2d08004211004000000030101180c8903104074041e41091006400000740114516011600b0041002d05150540d40d103620380030b4003030b08001440c002d00c6010040000c81c0c05c1c070030404180c00141c0c20f41c510b182d88212103805c1e03e091b80c070b1420b046c0e0f0064a04004548800440070f05180201001c0004088 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 851011780 1250 851010530 851010541
    0x61d060703050c0a091202030a2301112a0c1c14010b0109030312091a070809060f0117030702040212180c0d082505010c020d090f2601060e 61
    0x480b07100624100755600d0600403003520130340c4600e190003a0340c1ca4041c1490506210700009180242c001002412000f031810709039000300400d110340c882514494001e000702d004403422000f060080d007242850400446110540e411a480c41402000c029141915180021000810785801c4003d400846911240804004219440c0c60080e01c4402e44d100812140340f21b5000245100c05912000e420000c40c056080c00b02203844d80003d4010340d2100c08201c0d42040484156485802107034448081802080020050302c1c0118450340b05148003444420142c1c2080d2102c1d160b411580120860780c441400480010b132a070b48000c1c106c00d02851088000780c0307084510008140b2503550071820700d401c80d49910b0f00e640c581003040c402c0a0b90060b4044d46402c004030180040b04000c0c1114072001c180c0c0300b808018041e0644c001c80c000c070b10940c00d17a8650003150409903011000c0c5e100b032280505030034000304060304820300202c010704031442002e142002c100b0040c60a40c0c03025084204d0b402c045005001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 851013030 1250 851011780 851011787
    0x70c081c1a15070206130e07180e280e010e16080f03030a1107051c090504060f0b0a0c0b04050f0618060a0b01030609060902042c0a09061d0607 63
    0x192404400c072030591804002d410700034080d0051000081c000d21000c142103445401d50840a0094101261206850304d4800700040600340c1420f045281d8070007401f0301003080e50745400c640f44a003201c40076100a003020142d4414000c02a80c0112000c59607541001f01c84000a0203100c200707125003001400464103e8480c60320300d8407294011451584811080e815400010040d2a4805d402d0400007850607022002e522443c0b1074400024000e025010005003d4203204100c0b81895110340c0d2011724094640e41404100c65031400742c030580b42c501b80010030003c5101001469400100e1810415000c5180d41c2c03800b00040c10b40b02150141c120401c4500c42242c20800d0550081e081003008032802e62102540347c5410000d07040c8070b5426114041c8803001c0c1d000b03401840041c4400c0e0030401160340e07514941802034105020300c2030700303018116002c10320740c4034100c9040d0440c900c030341510500d0302c499a0300d00007407a000b4000c0f1081910b0700100303150300d41400c038000030403103103603020b459285841c20004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 851014280 1250 851013030 851013071
    0x9060905031f1503151503020d060f2007060b090c0711030709150303080c0a080a39080c0901050307180306090b0f1303080c0f0f0d0902130c08070c081c 67
    0x8114440741e2034010000342c9d0700c010620303148a4005100084807045028010060301903500084641e039525034088112404110061001500802c000c1060840d031070100200c10100b504c0840c0101010f000e40b902040d003010754000e40e0540201221003842e9140c0d51202034401c015039002d0f40b4695100108285500f052015500c9074a201060b40340120700c2e070024140031070103001410b400303035620110340608210004001500c00e40000c40b141c0c40f09003400c42c115420113240960001600c2c1c03400700348c02c60403c40698400410503141c0c00e056643c4c46c2c0741103d505d0041c1100b103030000c200704000808110244103030640a405003002021b81d20b802c100c6030341800d030080c00c80c24807200304000e10710110350b00018103508a03d689d04c6a5030f40d50000d1402840501807280102c1d1030303e000054004a41490303034401e1464510a07070703400f0220010041c406085940da014000040340700c010000b220140300c1d2540e0708a180c4100740711428005501c0d901802958400c0c1c140c055503594040781d800d0b030703001d02005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 851015530 1250 851014280 851014301
    0x1709070f0e04080d0b010c0b2e0506070b10090f0504231b030c1908070519060c03031e060509130302070b070507030f030507020109060905031f150315 66
    0x341a6070b0078a542c44820f41e110701c00303a19104542e01e020b801401e0788035000180c24150060392141c040e0408000b06140f03191010400d10300560f440c91302e6087c04407090f080e081120700c020180d50908940d603e405c80c1450b03005210780d100783c034500c4010802504034030420603011504640014186800c1c43d008020301c290a80c40c030b0101d0f003004504800e8020004940000604440c0b14400e64480321010034138240a01c0b4045500190101201c194003131401e8a00c021074200f0400c4402c85503885d824041484400c10380790301560000c81061000b180285020070f02c8174400d1034005101198000162511031903492001411525502c003004a840d01e049001d400c4000501400005086590007039526801441032900c8501302007007a606010051040d00c0c000d540242d1040b4a0407110301c0c0040056120704030890120300700c4030001c03801501c10060f41041d580041d005001e24603141180d82c800d2407025081d4141141c50b58903960954020ba05c8160045100d2220800c04103400c8648500f50b03000b031000b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 851016780 1250 851015530 851015549
    0x91b0e060a0503100e120409021e0702060a0809120f091504080304050d1e030f02160e010506031f1220031f020915030402010e040c1e1709070f 63
    0x8062007140d0f00898803803d4484031038800203440740b0342d548240c1001444640980d02c8400414001400c00f982d40003848541004980d814000100c9841c16031903015110019401030b81c240298105203000703012894208400000b2506210340030250901035030f0000424100c0c0d1080852031002c6418440202a000c1d03c83c20f9006082c01d0410508660700e00a9110b080d00c29150481c4590511201142c07600c0f5140010b44450f11000382400c0103030900051450040c0103128510403104410202c0d100b100a45069002e41500f50b482c0034100060394002801c000c6110350540b071900810080755508500400d441000d04450200608000d085482d109403012101c040e40101c0c5956907502148200b40c0c0d03401c18080c8212000103065203002409a454045d03001080c0050b030300b0724028120007030342c8624404d98802c115094018240020b59107855001c401180340070b01d1705028003e8044d61244a9403880c42c1c9051108041615010146000c3d103c001360717900024010301950010039100c1b4060f05884c403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 851018030 1250 851016780 851016799
    0x220b0108070f03150503010c0302040515031303030f150305010506010e03030f040b070c090e03040f09020c0601060f02030c06130308071805010c0f0b0a15061d060d091b0e06 76
    0x64019100074082401e02e4101592400300c14040d003a003a103d18007824010f0020440c09044140150095000d4014a8071032100305000c10030412407001124410a40300344000b4011100750f0381507018003140c044101e1901d07100c0c0718180f000d114009202c00290b020b40f0000c512400d0403800501440304406070031b4041d4008000c4640b03070060078000c0b40c0c203d99a1001c680d07502c00f1142000d01c0c48982c03d4200740862414034510035440c00002020384259400e03581240d0b91659141c21000491082030307060360300b642054004000c045d020305400d01030b20185006403490014503c50704c504001003211500c0d80b5401080581041c160b0059985a000415003004031f480d40c20515418501b507085e106950410124510b202c04001c1110398507022142e104041c041e182c10200c141c8805054180380142d8010707a4110f00241c40740c41000300d294211111500b85059280407030502c01e540e4030040380d007a0186e85810411300081c90031200b012102403920190b41402d030500c170143d003c3c03240c0a40140e20603001c90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 851019280 1250 851018030 851018041
    0x201020c09060a050a0312090b04060206060f0111070602010203150901262d01110f09150f190909110d020c1c030f05010e040b0402060a0e220b0108 65
    0x1a844040000485a81440b555081d00080c1c8429a6422079500030011410001c00c01c008034640c00041d50307290320348046803611103060800d103001f0f52003000c0042e4071540108034942445400004030100601d0310041000891507414a40007850b1b0142c0f005030760010402180c25401030700241002d5080302e0355010ba500d000811503240d035001e032400c0640100001400e050303850800076030f0700d840b0003a2114240d800410006c80ea403c5803c1074129915402c2001901030903c0000c2224030441c2e411403258107150141062200d030788241313000021180d00420808030a800300101400c40d0980c03141c50f41810403100800200f81a00907802083e4160400b8a402c3c00500c1d004103640220884581c01600c07085d800007600d1400c005802d244080c04803c1d2200002a42c2c0f540022106100f5141d051060307990780c00384401c002008850180c20001c0f1400401d006280503801080300307121900e803105031009040002020000c0c00a0079000b890200b2482e90301c1a80341c4d014800c0803807400d08088146141c40d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 851020530 1250 851019280 851019283
    0x303060b0702090711010e06071706030105040b010b160f0b010f0e091203060f0a080c030d17041115030c070c0801181104060b0706090c0e0403051c110c07050f01020307020102 77
    0x103081c40d41800138600640c45e0f81d4000b544004066821507044a81c0d03400c0210000d020061203035008900c594502c0e000500301e083c14007507140150750040b181515a840c018807201c2c0e5422091801036889400c6044c000451000404204494014048a0f881d94500204240e2800056001c40f2490030b83e0000c000d0403100104500c6040c1e007450b44015680d942d9000011080403032003000729404032030000b0110300001d000034500c400442c26012984001140e04044d01c0c01c48140409030700d901d1001000030002041a501100e105101608415205140710441c4019030402c80d02c0034114000401c14809009002100d42c00400700000200060341c10242d100920354041c010140c8070181440448485481d958000c4000f8860f1041681e260500e03480e011000c0c15009406680744188100c01082c2ca41401880718000d0394141c868034076003071403400f2030010300200c079090508c105e554108241e14203c2030030051140c2001c0340064100d6600302400c014510f940d900c81d160440d80144003080050341c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 851021780 1250 851020530 851020549
    0x601170c100c02060a110a15180f1506080601080a1b060e011110110c06011401050a030507022b080106030213050415030501091202190c03080c01060b0a0c0303060b0702 74
    0x3c06450702e50b914552040140d84500c8032480000c1648a6200c0302c00600072983e03602d001d0340c006070006003c40f982c41402d40801d6071502201a05414001c0700540001c0c182c0c0744000d0024007001404204035544003034060406609910084c0e803908843d2100d005c001000340300115540401e2103001410742172100003802d4008440740507060103107001c0101401641013201006180683c5004d002035140407544a01c81d80045030860110300c103000c00400e0010f28502d8000b4401ca060303440c2810610448012006413102920850941c000c0200d407483d80745802d07040c6800f06220789404015003030888001003102c0c00c168041400c051051041e00e80b5803100315005000c41c0c01c100d8003c80c00b05040c2000d0404e100181d80020704c59841c04500c038003048200c102481401311340b070f0240e4026400e4808207030a40d44c510f041c0244180600482400080e041c00c1c0546408143c402c000514561103070300800b255803040d030003240410054003d0904240d41030264002038001c903d121400c003819030380415000030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 851023030 1250 851021780 851021783
    0x290102161203020a02061303061109010c083601120c0905010c050106092c010603050a120c02031e0d0e030703110112022d12270601170c100c 62
    0xd41e41c0070701c4400d1610070014010403540091201350354001e48040750052091501c400c440035828130741070305413241190043d5104254103031902c0c210a020303075592914075070200021030296210016180303045400c030100c030320442007041d5810101e5440d01d000948054181220800024200000b201103640d04c0764800003102c0003828140200c0c0c04074a452400740c1245e400440c0d8103441c003501c0000c0302c02100700070301300201d1014041c8200d24546500d2800d0390000d000282c403590100e0381d440300103020310111144c049858680815852600c0d070000e403c004030503c01543c07840d0f1004104c001141c0521070614248814100141046c218802291700d490061101416101b9109040c98640c0d000f0300d550340c104048082e00b1562841d070944002c040c100b0b115910850400c1d03250050800c07401c000102c0d034608144c01038080407a42c6644405c507201d501c0303600c0e200d44042c0400d030b1001402010030080d4081d01e01041501c040380c0c13480f500c0b1b6152181c800e107000d210303108007903450280315040307001c4c480720320b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 851024280 1250 851023030 851023049
    0xa080a0e0d051614030a1b0503091504180b01110703050618010b061b15070c141c0207080d02030a050a0807090b07060506010305100f050d0f020429010216 68
    0x1400e0a580d02e074540311082c1e03400351000110f13442480b40410301000500c1e184079251100e000c01c0000b01c90a081c0900e140400a00700e03441002001e82074036004890841081c0c82e060054581780c0c41b640c04c0704901d0420251800b086840e031071140503560b040203004982c0c0f1900401042d2961441e29050380d2a1005004900c8000c002034038100080c1080d00528204840901807594907040d07100c1030038044006140756035030f9018400b048108403021300c41c40380c061112560790301d04168007611401c008103540e010b0740c0c40324840c0c04038500613102d810104450a0300c3d03d4014100d103a00e01323079105040a070121449400c54008100081100d42c000d0152564040c06250000265171526010303100c00d503482d0008403040d080401c00c20108806504464403440c030a81c5e0078403682d00c0e80c4811542010450048007520400d41c0020310582c00c05411004074980038111100b04034000d600410220303099002180c01c0303100d40d403d5281c46030031790000b4485030190a06c0280822020b80d075000303c00e261f150041e5403a2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 851025530 1250 851024280 851024287
    0x8090c0303071721070215060a03080a181805060409170a111905011404020f040902010c0609051e1c030b13060609050103060902190e0d0f03050a080a0e0d05 69
    0x103809454094800c1a21349400c1600602150b0740004402e041c100c0348880140b040c0b80d007841028500203082c1d0300450b0040e21a01c0b1041c1150344084007600156000001c20000000e090341201008140000924800010780030004845444034180c4100400070cc0c0a1170518610600045a4048400046100c06892900c603000c008044401c001c000040742040e12440100c0035995001907810303444244220020010814403d03034481c4500c1c01280c010b944403500e55007031085400c00e0b030000403025105140c418400c1005569004c200d4000400a6580707a03c50b80c586904d030251500c100c10751504680c02040154590302c1d50140b101c1505002c0030030191075101d0100d080e2200060160540064003007406200d071030381d0000b003555045115850000742016000102c5251a200301c035130428500d146851100f00701c1d85c1c2959603614044003d40c02042440d0007002144066821a1030f09200781c0e50b290780e83d2036032a8004d060b49006030040480a03e813400000c100000044c10420000c803500f802e81c0c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 851026780 1250 851025530 851025563
    0x30203100b070c120b060418120f03020d020c07080f07140609060405031b0a0b0702150f0f040905010305060a050108150402280f0b030c03070e0a051c0308090c030307 73
    0x40308543d5074003c11380c10349009460010402a800e20030320a90040c1c03401c1080d01c05d10701c00001105414a00501104404410314038920306c51781042040208a090151620350050f07111400c80c2d00501200106804c17964081c003503903405200454280c01480c000f0410541058031290742100e40c80d0300c8603c04d490010340703090642c8a8100313560080000034240e50241c039440415803210310368150458491179542d100480c03000d100c0300a0302d07010b6802515034410410340460089a41e804400f10040c03152040c400745039285009401003001d07060703040010406515501c1d0003441c080c0e019101c04992410800140032036100010384002c4070100c000e045803980c94500100c1c01c503541d01c00e400800e0020450341c00f6500700e808008182110310300b10b50110b20a644401100301800b05803030501042c482000851802d5204d924044483c180040080e03d14a5442c40001c0c013214200c0c81d500e8040300301a16003018582c01400a9910884001c0038010b0f10071000006600d0f8030998000821203080c00d106140d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 851028030 1250 851026780 851026793
    0x30a020c07270b030601080a0f061d1609060b12060114030a0b1e0105043606050301051303050301120c030b18190506060607051606120c030203100b07 66
    0x5000c840380103038035100844000010b0780b40d0129005002410301208103801d040c00100141294150300c0604210740c15135031001e50070480d40c5019500c00f61151041e130042e54070140301030f0404103020020304448149035000380c0115000d900001c01c85140001c1000a600340204840100b0481046025950750364001030700c25403540203102c0c1d42e00740d001c010094a0f848a0b03000c8012b8410455510000b41d02c0d1403951071801400303041c6ca600180042c44100704084240001d51090280504003190700507410b00300301d8004408400d01e92603241c49000401a81c20284078154004c03ca500f114183d0a80341d8502820910062280c50034601d46400400184040c621000002e181d001c0307500041410039601002c3c03444c54030700c00c0f055903024a480003000b1b074050b2003013100c00940c000050400c40d980da4040180075009480141c48074002c082e22608108150322052000c0c0041d52101d0751200e04079001c0c5421541100d400c03a06144c4100240f110860100d65000c0441d0386c51200c2540e5580c0034500714 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 851029280 1250 851028030 851028043
    0xf130b012d17070801021321050d021b010e2107030501141017070902030402060c01020c010c09050105180f01020a08160b1605070b0c130602060a0f060b030a020c 71
    0x703070700e44141400800c4840c031014980354800e80318000c0301c0301c2d151528503040c00c0344a0035030401160081200204040b020020018681904913080070f00d038040c03540c07200c0e42802101c604103401a00510407003440103280440d14030989030700b86030020143d42d014010400619040e0f603081120301e189011072030300300000c109500286a01c0402403140182007c146140c10200762140311642c0c2039501d02103100103440a111200e10f02c1c80c0d0040c04001d2070144400b00030b510151050b0380111042080c003110120074002041007140c02800003800302c41c0920003c1051103e80c02c41ca04000d000c00c1080144826241c1d200e0111800b00c90740e80308007110500513482d11680349002403201e000405c400b0350201f600c200800c0b49500941d0342110944c0e03840c000b0b1010036402c2c3d020501040d014000d48010805c80b250707942d88460820490782c5400c024101d02806125141c0c0083c2c0140e205108014000d000742c003402d40c2608250384140301107811300c00c1c80003041c08000d000c0c000c05640814401360161013002031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 851030530 1250 851029280 851029349
    0x40206030403120e0708151b1903200a020709050601020d1d10111207030f0c0c05040e01021c0b03190611030c04090b03060c0904090c0b0a03050f130b01 67
    0xc41c2c00c0c203645c42c41001c1c7c441001040280c0c00e1341510b1b0028507110b02d01c09010b0480000340350341a00d0310500204030359101c440001da1350100b5075034001d100d2240c00c1070350355425200640d2024903207075405400b0003407901c5920f4110001d002e08100501280366000182d0520003042400d0044a84502480c00c00d030701d401da0f5020799400302400003480707601030f0440c9080b0880391030310003520815200201c5000c6188075020000300010580d1102d090717014420741404491500c10410b0b040115a104002170680d8002030841c000382e540018800500c00149030448030a00c2c1c8500c00340012070400c00020780312040c0e1150080204825640700b01000259800521401c14a4100f07507102c2c1042208000c90f071f0068000d54000501c0c1c6101c0c80c20700d10b0001200c80c8543c070301500751440c1070320b41400d20026202c040e000312540b80d0849000300710701e20a0409040500034076070b0002200d1400c50120144800c0180000b1040d808110b8800003042820500d01d056400d00054090f80d804810440c82204019065 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 851031780 1250 851030530 851030533
    0x3121a060d060e070503010303020d210e06091608070b03092434030b0a090906091a010e0112020d0203011d120f04090c0e28060503040206030403120e 66
    0x101404a0344140c2d02110507241455071150315591440c0e0283c50a100a010140143c2d224000781050140b00389001290740141d51001e0540e000e50720b41403000c1d210181744642c0213402420070003011000400990080d1203009040c85038542c0b03412441d039101d420600450203610741c0000064150142000502d03000c06001da004100e6140e25680c410a45600fa20b1451030302d80e0003c0031214200c480c3d8602042c039001894941d17031a9604076400d400414025040c607412020381e600000b46006c0a2140b138040b40c0c0507920201d00c0c0841032504c10024500241801038500e8541c00600520500034101c0b819100902c10035044000580000758203809400c00c020760560034511351580720110706031303803045161400c0c080340c40710b502c102d450080b14014103031034280030318017408100024102d46c0c200d00c0d001803481c02e0407011044c4035400300c1c088c4031849112030b2524590054504881c0c2c1c0181d0840300404880c175203c1e045081a0380000c6a500c03002d030010b81002030a90055000841560101d14030412100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 851033030 1250 851031780 851031787
    0x507030f08120c091815030f0f060714070f0c051f0305060f010f1211160c05062104110306070c0b090703050a0f03020c09070e030f0a03121a06 63
    0x5007640c060380c81995004079000c42c0c0404a80016031500585241c51002003000b214070004003961a03450600400000c4d212807024a50003044d141401102014240c540107050710300c130b40205040c0303000c07009404030b0100403143e0040207003004140241c555043e40300d0f071080c42d50310721800c040301301d4103050f0469036000b102110381e80500303d8180c0f4204031544040c2c409001036507440042003811340c206200c983c04201a1000d051249229450444081c01c00d0740000482d101c0c04004010160040c007851808a51729012510510481102c4c0c0386c0248000c54641d407034101c02e400b0651603e8540700400d140381d040000410308000c180001000c2c1e400000d030803030f0b80b58070342420011305151014800341c0c1c0440c5d00d00085070000d00082a02d4003900c0d000801089091480d942d40050070b81350460540460092040d003000641c1c4511003680203204699030a210125910304142c2403003801071035080b09510004100d0300198000d903075070310300c0c071034101000816410b80e0444083c00807044007090350266001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 851034280 1250 851033030 851033033
    0x201020c160521070b0702270402120105102c040503090a0f21030912080a090905090c150c060c0310080703050c0f0d080d0c030b0d031b0507030f 64
    0x2114a0011190100c1e014020f02d5800b0a05041c0001282c0c29042c850f0858132080c880842075100401c1e02e40e10141c1000c0b46180b086e030f003d85544d0303644240c081c0e2400f650401d1000754a441104a150f46150078020030081c01c0507590b030301c0c0d030131890300c110442a080c46692030144441207182070502a8500c0d2006160b240074903019490380c2c03104540d03500c14041c40340049242004110804240d81e0301e40b0f0000c65840c03280c140005a02d0051204408102c43d0b80c0021030410250b00b0840c0303e40788600e0940e51141c04d0518007500d900f42640020202d2442c000422031318140000303000da0300c40030030740d0901450b9820380c0c03071358459104151400c009441507605004c0d80c007074210025841240c040c80c078000910f440e180d01507210a5288000383c165070084040d1046481c0102d1024101c40d0020400c0241da9500d030f840e0712168000c1d80c0d2a028240d40d9594102d00a0b400d801840ba1000e4121040d00e4003801c80d030380c003801e1400c00048030903002e1460141281007282c100903450246422840c0d00590781401d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 851035530 1250 851034280 851034313
    0x90402030f0a050a02070206090f04110c0a020405070c1e050708120403060b01080705032d07020a020301060501020c030d030e0f01050c13060e1810031218051801150201020c 76
    0xa5a048032110b03c1d02001500c00a43c900c00d0b41e001c42d500034001c92038030040e00708001d09a1a0641040e80c0300f5540c0340d9019100d014140100f010601d1140030b4445e00d003440c0100001c6844c01000d5034113001d411000040012040d50341d502c58041c108541600450060500601e0301d18181c2204105205041c1d2500e00d841040d0040c1c03080f02d1180c01e05104038000c0030011541c803541600c00c1c034040340040c17012600000e01c08040d40192022443d21400300051300d091403904000a551071005604000070010550070b080c011000540800e00045c03240000580c04265100304a0414204146d9200d90800d80317030609019078003500d0078100c0207020a00b42280722001590085078003034980000c43d407000660a024050006031320000500102c40f81c400001d0f000002030000f4900f541101481c00003200040c40c5000c5100c200c4070308d550305803c01c5503240300d5240400f11a001076106020040d206207644a40305192815640510001d5814058406060780a40545660203145004036106c807040d1941 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 851036780 1250 851035530 851035561
    0x30b073009050601050d0309050114090306040305040509090109050601091a0301060f0f0602010b060301121b03060e011d0a1101020f03030703020a030c23090102031c0c0906023009040203 82
    0x1032003a1401e0303983e508100408811b02c0d03403000b000f1500d0407404228075030060a41d81c5100180250091522601301d0000b824420101d8045020400c00304043c412402e20888103a48103486030020004600241c803200c0e56030905100c1e8078034498481907804124502c8c1607803400c407440d001d00203110f41502d0700d01185e0000c08074015103c800c0e04001d80000d0b280c0c03050088031009070014001c1d0b80343d6424000d130b91814104902c1c1c2996200b20301d8400c146250390030b07403080c00118007170040040c003003243c1d0340068251018404440810300b0340440103d811074002c47c820003125070041c0b510011881840050307003004641c0715440310a02010081005141d055001031540820b1980c0c2000700e12500b080a0307030050120412400a80d0b880480d003500b07074101c000240140300050044901302003829203400d400e00a90b4210825094031114209605508607483c1000f4104500180c400c001c0c403106444401c08910814007220007800e07050071138450101045500400e0050020340d0f0328030b8180548618401c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 851038030 1250 851036780 851036783
    0x609040515190e011e03080c06060126010b22090504020102010609052208040506040602071a0a0813061d0c011e051b010b0a0e0f0c0301030b073009 65
    0x1030540300d0b0a0745207482102000e803480010410060390810240d12107143c24864aa94445508003010020440600140c11044070031030041c20701c0d15003040010409a641100c1440e0240e0444060501880d1106241d0640f54004241e54a80440000780140d86c18440c094a105d0120800c0106600446401c0503120314000c2c1c00900205580e840700a00300c81c41203c002c0c0c94085200b0050059040b071300300303c078441806030160f0703070801340c5840c0050203a80c800e03482400540e00081c400c0103520788454003002980f61310b0500604200030b0820103404c420000f49846070010180c2c01c04010816039a02c007909503904052150060600d17410300c1c55640d60359401d103501041852040f41c20f001c0f0004d401c00d2902c4100c0c0c0e03d0300d042c1000403111521400406503a204255206e055440164450284003401815403585185e01c80c1419840c1c0c0d85211409842850000e10804c010300100e4840f001c85608080d0500e80a58062880304c41c170741612135501d118150026002c03101400350380e4507411802e05a0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 851039280 1250 851038030 851038039
    0x70203120903040906061d0316030201030216021504080f07060c080c1c0509040b100e040216052b030216030822050624210a080c0d08010603090302100b0609040515 72
    0x212903600f010360314000074020003a1142c44030270a1006512075009807000141940d242c0103640ca07d6800107600c611301a031600c43c50740020404000504d0300300010340414107818080c121182c2005c40c010036061144101504520300055030b0206041c04000b0100206c80b4002460304803408050000d0040d444014041c0c422404c1581074070842c0340410300e90241504585400246550703400070f10000e0b401c60002604030540382c030490804200248052500e04902201900b41c990800016044a4003105018000c0520501c00803d40070110320440300c0c2c2e5501400d00300041d0340ca00c012460480c00104803940b01c00940d446900422100103641401a01a001c904452580c407164010280c01c41107022a8002c1c4a0b0500d01a4501600a40c1112010000c181c400d1565161141990b0390301a42c3da0b205668030503208a0509580503107510302602c2d2928050103130500540b8001d40c0c030701c444800c03880413030b654103964665a55082c00725843d01201602c1031180e440c1058410800c48804084603006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 851040530 1250 851039280 851039327
    0x1b0f0d030503041a01091b08090a11040f02160c06140405130605030a050d0e03190b0604021902030711011106040b06190906090b04231f120507060807020312090304090606 75
    0x240501150b5124407270060007009406c1543c1c031219641d0b6010490240c010b550380b0020100150640010400241c3e2441002c0401e403280c5000c0100144a501c41c20400952580c500078480404040310708032441150f290000c07860b2008510000d1001c0e60103180d06102e1020050100580401d034425043c4041e103604100d480340400f810303101d450390700102c1242240094014006845451450741100000d000107007000102d48420f03200c2110049004003503480440c12000308413003c10b200080507801c0ca0a0081d0b13403c0a0f260950790322010344014210350b11400065560f480303140601420429680c075140b50382c0c0d5030f1031038000104194080d0a90803030030300401d1216030038980030300c0340c1e940300500c070f0044030380360901e901c00c203810307000d00b0340c050110808001240a800400c048000b80c40d801040c081c0404003490103e00c0d03c0d540b80e01020601080c0c0c400c2203003098000c4103460903242d02000b0004c0c01d42d07580001d94218400c1d9040300c00c0d4030740380c4003000c520154400c460041d04200018107111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 851041780 1250 851040530 851040581
    0x40e18152d07050d0f020c0303070801080d0c0b0408070f08030703020c011d07050607060f050f1909080306040c180b0306130b0f1c0c081b0f0d030503041a0109 70
    0xd00d060855003800401c100f04422140c00c083e940c0000000341000d1710050070809610201420340e40241c038800c0c00203003118010300440c1020701100d0054000d90400603070707040103aa9602005000144003030300702400030650900b48040e10301c0920310160700c050890f9880c9070001011707000b034000419801d05580381c001d140300e000004c03100d0307040780983d501c0c02081c540b45458200f15007944003e8044841c181c0740c1c800003044242ea80900d0307000e4800ea46079640d040c605480c8420340849800a010490360a041c40300b80405c0941040325040403044da00411410f6415205560307080c9030007040b9000205207400050540403c0b40510b00810f002c03150301d4402c450160f124025556845003d940c4001240a100d8031403406100c90525096800f4002e25544600d4890741604480c40d4402903058201002d108031006106420441c45401240c40702c6680c3e82c640045000c4800c985402002d102001001c40d007030122190812000b0f00c400c1c00344403215038640c80c507140508a41240003c902c40d80790340e4009e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 851043030 1250 851041780 851041861
    0xa0c020703051011040b04080a02100f0e09090c12070e06180705030a0e0d090801110c0307080721020d0806040603030215040c090903050909010803040e1815 69
    0x10440e60400000c0c044000000180b0300100221034410300c04c0300c410403000034610310460140004005002c0500071000b40c1c0d00510000405102e00a020446088810403207070750000c1907004145002c0d2040c8071169240f1021914106c802140d25901400d00c8a4003a081c540018051040c4ca07015104c0c1416525030005000d8000c0c2c01c501c941c2031880802c0001410740e40318501031a07200750741d06004141500340410841c28041c48405150003e50010030504c010306090158949144031404844d180c240510300042d101c1c05014002011040001651828041301c10101203002490662000440400c003202031740da200134410f00e8000c6101c200001d00c16241c18459881100d030150098803103074111414101144000138000c0b00e40e661464004240c418051080032505c0b0700c280c413401c1d50f5814a1041110008050b0320030052544100014446480c55220080c0c101180640c144040000c0c0d00c00c046c02c001e01c05101452211088080040b44070340e81e202d42810703003c002c0403203030791209030540d18 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 851044280 1250 851043030 851043043
    0x15030a0201020a06050a0b09040633050d15020c0604050f01180605100e090d0207081b06070c0b070c050906040e0d05160804090516050a09060806030c0a06080a0c02 72
    0xe80560000066500802c54a8110b00d9021841c5035000a40c00007450000e105400181c81c1a10110b940b00d40c81c0501c03110074100849241e82c0108080390a9021440104082d0040e019080c080c0c248044254200138201d00c191182221b404000e43d283c02954030300c070b55641011101514988900b80d942103074002d042c0303d00700000300e401175250b061001c9521b815020b02000303042ea1020b00750508000a1054202506c0d40c000c04400c0c000d41805070311100f0091500c21240c10960154012009c5034040401e145010162594250380c1d05484900c2410868058101d80e030140070002400200070041002081d180d0054690440350321b54507071140c07802d001c21501e940301005919030001150892560060020380004040c00c072003000c01c070400787e491148a400c5903010b00006600c0d44284440b04000b0b0401c030140c2032543c43d2040c20034000520080c240320052003018140704800000c200740761401d00100403540301c0038020126481e5503640c000c0c1b854070125004000300d80303400a00b000782440420903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 851045530 1250 851044280 851044283
    0xb07050a08011a0c0d020102031602191209030807050c1003090b1503521211040e0a0c09020403020306060f0604080601080705040c0504061e050c1515030a 68
    0xc410403a030800102401e4000040e0691550b4035060113240761200c000c1101c0c04c1c0d1400258009a140d007401d0059103040e0b1241c582d0502550030900f009a0640301c1c281b02191800c0d0800e8002861705000b54040d1118580c030341001d49904c0000400409000340006c40c40d14103203059824140f5000e610008a0445d048402e00510480181d03012408400f848000300c405603c0c0113060350340e2030703040c515080c0d208040b0100114203001c6503410350400c1070000340c0d142d03040c1d03040a4a40c031a4410030300840038a2401402a400e444080342100424890580403c4030700100246c0b0030004500e07002c450640d600400401161041c10780743e008200e990442c002c0c0c07000c0720b45c064010840b940f03840080141448015800340c3d00040c3c144000030712100104031550017021040058050785e800c103801d001c10f5448000142c8240042000704002d02070f4810521040c41d62480b000100f9020080700c11101407184504a40c0e0b6446520341c0c00300d80c0340c0640d8555000304000e504c0301c030665250754145030319a1203c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 851046780 1250 851045530 851045537
    0x41104090c0320011b14101401080606010305040816030210020301060203031501050a0c021309350304021c020307090c05040906050a29040e0106210e030a260103030203070b07050a 79
    0x44180050001035104200700101b60039200c000c2402c09084044541e26000c88040e01419001003240341c2c0b081c00010b0300020700f071900380001e180a80340e42e685441032a03000701031078403661a044c007814428450924049a92502996256581c0000948d60b03041903404042e400106440082e082d801041100e5401c569500d4001aa51903078081103034000c2a001000480d41d25540d94000181d660007a17060150191111441010440c2150283c2590110800402034608000340009a170300c80f01800250001c10280050704a02c9102207400c0c400c150307002100103410441c01070081e0740c10201400a94118220802c15182c1e25420041c40c0c041501c030342204100011440200d0390000b400c0050b0014400c25031314505a91845200c0700c0003c00d03441075000400e03922031000329a04c840d481100143d0785200030b01034a442c40304000d44a01c100d030410024001d0045074600f00714000c000c11418003e882013045c006603540d00b80a03442c1d60002c1c500702ca60031240400a28114068015108050010f94 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 851048030 1250 851046780 851046827
    0xf0f063c11040510050a09061103070611090904211e0c0503210103230c040e010603140c09092a06040b03070c050706020d0206041104090c032001 64
    0x8460001082003402401c05124208008503198680c140c0001d510b40e116540c451751814060002400c09000d03400101c03c0200c080511001d03441c0000c03d54241e6500a180000c0555050101050034072413410340e103410118441c208001d0100d02d0040b010101e011000552852030030050495040c0100c000f5070001e8402d003006840700f5031040f16107580c0c0506c100120391030107551050b0a04000030040c800358041000a005004200c1000300c5007450300500e10740700c1d11400c0401d0400c2d403241c0722058a43e0140b0f5030b59030002c003021801d42240002b150407002802020511160580d200d40f804e0202c3c601606d440402714995500005079071544051900d62940612241c0c0707045003046408000503035010b4410f01c00460a200c5600c021401540c00c0d4490300300820481c5045801c003072007540050103640004c0031910314203401148050b8040d81c082e840b0585800c66000040c0140310801019041550841003c000c00c4100500704003200364947c0280204078061004503078003d01c0325103551188102c0c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 851049280 1250 851048030 851048141
    0x90303030f1e090601180204032109150507111017061807030905100605010f08090313080d1707051204031403090c0906030105060105030408070f0f06 66
    0x4a07864204201c04040c516241c1d5120307950002e58810346255940c2d40002004001d00e0540070848003081c10240c8080d81002d145841c0c0c0415403212000c13400e01d194046c102c00c1080c91042170440040c1a100c010480d040010354070003421908075170301c121214207504031900c40078034282c3d101c0c98a90313400799503c0e10000060b48009000b6030000c0c04140e0002000100d03101400120354244d0301c40c226a030380004200189003425850400300c1008404050310b030000501407640c0c00b240003078504145042c0080310303466040131546584184032001d035280402c00d101095428011898400042c119519034804101c0d05041c001440c006403020004902c0802c260581c1302c0101c031015078001e0007410039041d00f209615290326564012520001c03190402d60402ea114682954074a4014101350002c00c414680500080c00c1031001602c0680000700104a4034100322000c188003d070742d80e02140c0455076207440e203001c401605001c1d103022542c0e1044c5048031581c0441d200800518610100290000e0f50308 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 851050530 1250 851049280 851049301
    0xf0902010e300109080a0e01020c041a0d14010207030806090114101412010e0108010c020601120303090203032b0509010b0f060d06050303040b341b1d07020105070509030303 76
    0x128500350840d500c4d007500707070041808200038103070b01c18064a03000c0320001100700083c1400fa00140b554031a5240442085444504100300c2001ca1400d0358540c295012508280b901c54007000c440702615800010b82d00101944103900a018407000d0710103042a907280c1d0131044807000480c030b0b0990401000300c4401456480b031000f2112103542616041c0c07421030718034424002c01100343c00c2034501411078001045203003000d01c555401c801c000e1010300440e50400f00705c98171021042d80090308158070780303030182d0541d0740c1407046900c030210b0070400a20080743c02d0b410b911340005051a0603245458000010b0b074145041c058180400c40061010041c001c0d03100c02c20901ea086084804201c5603240c0000c500740c1c80810042c8090401d001c40c664644449590f51070010a401d500395a40030741c04503088a9070380f210445582c00a0341b01403a8110180307075004070051418103034009240b40c514a04026a11100794a019005031240d90083c0b03c07a0399511001d0319280f00701c5041a070550700c00c10024a41012 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 851051780 1250 851050530 851050609
    0x5240612060c03101224092105040803030f010302040f09030509011d03030c011a01020c0306070f0e040501151e0c060b0d02031501060905030c0a060e03100f0902010e 73
    0x110003001400341c0703855442c00d1484010030b500458000301010311807440030840d0300300031100003080f420a00580c6040e40c0c03100d03203003426400000148c40b4541280c401440c0502d0541c0d01901e40401140d480b440d21100b1002c40d00c07020301c8182c3c0234600d000c20394080d00001c0c1c06000451901501c680d0b151828035001140d1070b22001c075814491050052038144c559409000800c500c2d24903800110303102142c40c0b200382da95440c00140310305550264104900648021a242d58001014203086032070b110b00c02000e0350600c2d076040c032103039006107001c00202c4d80ca04104000c6940065a5880801c41c090845403103211210000d40c02012070711001101001646a82040700d1010b40a010304503d0843c0e54003080ca0400b0882c25100415043d41c0184240340d03100304040000d1000314006d01c0e00240350b8010403001e488034010b800c20031801c4103201d10b00d51402c0000d51002055050200f000110805240740100803c2808a00040b920705c41008280352a260160182450700c2450990385141d0051900f03030f01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 851053030 1250 851051780 851051791
    0x909120c030908010e012a1709030403060c08040506241c050613020909010516080402040b12030d112802071206051e091b010c05240612060c03 63
    0x8a41c45000c9100142802030002c0d50014500219107904d0340d550607400a107412600c88008040350726806121a40145150010000308c2c00705079003038413582e03000f40c11841541c001811960514405011103540601c200d8499405101581e5071522907003100a84500703c0c0c0c1d4046a203510310201c3c420030380750600d801d90341d0950049246007242041d0b078809040c03070300c00c4035200b60749400d6041035025400e000701440d50040b042c400802880c64802c1005100040c2026507008102460780040c0071925a940150f900000c000c128441400e80b03403583d203641e540240d030452051410410400140207041d800d8501d008006014801490003d064800b8a00ca50a400f68210310411400251950b5600c00700c002c22801840c01255919042103e04940501000c40a01c0503d48808102006202081c9400c40d011401c100d83c24413610040129001004000302804900540320031282ca185030031110710400312729010380c5d48555103801c100161015143c001601ca60000b500189440d003110000b1035108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 851054280 1250 851053030 851053037
    0xb0f09011a07051204080115060f05030402040209061602040f0b06040902030907050d030c060b0d020618041d1501060512161412040213020306130b12010e0a0308010909120c03 77
    0xc40e84401e45800d0700101055041d01c40000c0a0048003001c0c051808c1030040302d210140b00c240f0b03181c0001d1610b100009903000f00003020000c202190f985404070303018440004c040649a600040e4050604030311403404034400d524008034443c0741003660042508101008001c41c1c2001c3c40c01089170007950006003200d500d40603581c8081180e42d210b0400c0b0034a01c0c00b0703070b450b503400b01101e01d010030454628072400361043c881d0426110050b40d922044520001c3c0f03400d00000586002000b06000d0907030421b00c10510710500d000c0d400380040006d10aa100743c0c0c0015a0744a5903a10300040c3c44501c909595409001c80440c0020481c1c010a510700744ea5a55030701c0d00b03030810005016000d605402c41040301031650000c00c00d00c010361034100031040b81103001080442c0b45043c040b00260164440354030034941a912614a6131075951240c043d0f14086000c00e000307201d41d40d84400c4860311041c0e005d2040f0b0114142e1000840c010001c1c2c4140400344d03a1120725220029002c0d030781034030701b2805044120b040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 851055530 1250 851054280 851054287
    0xb040b0a091a0a05090414011e0e13020f0406080105010603090203011b051603021618050f0c090d030c17040312031e1a03010f0204090621110a080102030c030402040b0f09011a 77
    0x80c800c00800044c02400103842074824110103080d0076130000d401d81d000c400c4a030001c0ac180101c0001c6c4001500086a0446031000d140030540d01150240c0364641c001c80c501e5207401d000244039030b0103400040159100302c0080001d40d0160030483d502c800c62482c1c881c0000d10a03c07605d2480b0440c40310b407204041c060700441d00c03038032043c903444032003070601d500700210b90f040c1e4111005624141e4042e454100503803141c040c44030315042102400c2c1e40101052a841001880ca140040c18001d08034444856002601175064011000c04c80c01940d00500c812960041c05069000c1c01900c43e104124540f0f92190b05001805c0c9101000c2026103400f4484c82e00100a9007050310043d6403d10a1f0140c03156048005a22245449000b80445006501960505054543d007254083d80c038040c00207141e50120456500001400100e0b500d00d00d2030700240c81c0c2d5803000083c4031000c0c0c4050f014500c11342c4201c409210b00c4605a0500018801c907603130060300020b20000501007102d040c56100c0604103a685690309 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 851056780 1250 851055530 851055551
    0x120a17010e0a0b030f0a120e030f0a081c09050a0308060102060112060b04110d0603291807030f0503030103200f04051f060c020a05011e030b0103060b040b0a091a0a050904 75
    0x6d119403014100c4580c3c002070891000319400984500070310000300c01820302d1703e1154401d140c030b40da48240000d2841800180324000e4032400d084550411500d488104021003d503c1c0c000d07030b2070203d124160040307003031003000410a41c40000c0e038505858004201845044407a694100940703803040059503c5074542c80700c40401b54a400141c0000300a402e40480e0390b5185050110303040796800140b11900410303440c000081c0121078115a0000e0b5410555050b1818030f0a07400d0802d41d003508018090341c0345a10308402d0210000185050704e003d4940d0703a0031240302c0030300c140c00c6240e8080d00300d4028900c103250b843c952034641d1185500005106200650201030b0310030f0764107110507402c80001f0a84641c580d60030350a1202c0001d000d8070007030802c85900002d03d18800401c450398210364040649940200d00c0992098010100406241c0d407202d4580e81c0343c900740c00c4580c011100d001d001400f8440009414458102c59511180b404440d440c94100451011a1035134403040c400b5030855111000c060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 851058030 1250 851056780 851056783
    0x14091902011b1a060105090315090c030706050c0105060613060e01090e1317070201080615040b0d05011503062117040f05100f0207060c020d05120a17010e0a0b030f 72
    0xd591603c0740303003401012950060402c0300d209015200904201c006d025003041c0c0d0301e001420002068594410200b9941c44504540c40c04d2002610306405000302d6000103451341d04203010b030107000c10400c002d200e00e545500610006018001402c440081ea00d0300030801c05004230441c1c0d11a413070615015002c503888ea25040d154403c00c1d9180404840092485400d0041c54102c0c90245007100035031600d0059a600002c1810101501140c403e481170b19020f00e5895200081320b005102107041c0d00e44070001c1841c0c4070001c01007481054003103200400446440c503c60311424007500e10b03185034001e05460150042c040d00442e0001116460310044044141c100500c010f00020a159582d10401d68201820f104070b0403100b40c004814852a020000c0c01d864010030352900b40d50003071402c07001900c45400000c1002c002c4000c050820b000300c07443c00201c11468801051312208680701c941c03184601d45410151504240300741c955a21004000c6000d072050343e0049286404014103c41e007001a503026107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 851059280 1250 851058030 851058077
    0x153f04260903010c270302060f0c1005090307140307020a0b0a05041e0303020d050f0f070303111305030d0f0e040e0a050f210703021b0112060e0a1409190201 69
    0x601090b0b60030103407003000c2a6401d84413010602d40301c0341441c0328555802309207140184020070001c0800402c5a02a4540c20000140680c1524005001c40e0622100c10307500d030b91000780d0580703070401c400c0300c09c0e50600360000c1158a400ea01804444585180c40c007400d2480d04103600d03d46c1000020800022111080321084a403402c101c030303c04031070fa0b19528020345800540320340c1e14148101030260026220924003612003610b4020080307a03407101c082ca0128010840303240e00700001400410144100c403018400300090340c0065049440d0031440c89016504404055085c02c0002c0b81d44600100b81d0078540c020059180e4580101c40b2001c507680c5d5400d041c504020034203285540818203082e500a000d101c010090400121a01e103020070f030345c50084d00e0308550017000105107030920b101d05060344141400b1602d20b042070420003140380c81e40341800c050300c02a01c0d0403002604282c0414000c92910300300b00c4c02600c01800400c9136038900c00081d5885540c001003681071141020507051909d0100b0082d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 851060530 1250 851059280 851059301
    0x903171801032705010213051005071e020406080d1215030f0f120206150d0f03030216060516030e01180201120f022b0e0705153f0426090301 62
    0x4d600c44050480015189087d644400c0c41030400c0c403085c0512541280031a00c0041d005100c02d04030503a0f94106a1461445400003900145045400a8102404a000c0510000d540d41d80090b07400701c6040e41d010350b41e0020290101c1c0300300120410000f0855254501194450002130426801c1c5440d11388890b016032414401580004041100c050b00864101c1c0c51180200c03022030b00e18115840c0e220402200c02d800a040c10b40c00107107502c4001043d06007208481c1e020509001d20f1a05d118180528060b83c410500402d003000b80a911140d01800752100424200756481070b402d03190b400460741e2024070750040414540d245507441d4182601d000914041d1002d012105042d00300b025071090a5401c0b102900586140088a0050107c00b0034031404a60007110302d030f0441006041e01c1e080e00d12a100d6006101482ea5455054020960b1441c00041341140b6040d4040b010a5000198084003100c00030b10024042d081321355820450b01c840c880c4000c0403251681040340c62000300b030031240c0c3c0614 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 851061780 1250 851060530 851060533
    0x5120304030b010b0304050714120d03020a0e010503092e0204060903150c02100203090c03031204020a080312010902071104090f02041505060403022b030903171801032705 75
    0xd091050005194a0758010555294030519501c2c00d52105512400f00d40030b8489100342a64400a89035180b0030344071b140b00d903800191000c2c2005500d020b8000d51200004401186c02045265019030284064034418581c000c09031604590b90402c1c83ca5550107030750000220312401d9402c4807200100c1c8041e202402498481c0f060160450500707104480c00260f55040c007a060900c41c908060780401c1948045c1d0102001586030b49072440710078148512014141d07010f00c030100c0c2d01100f8581841d480c0740914006d441a80b02c441c2c40704103243d03e070702c103140385d080c498440e1400400c41130384a907008110340c600400e03540b25451a484c0000742a10410041030301d86d1400d40480100758036042c4110042040a1100d00c04401e01d403401081081c0680d201c00781c841c1c403502d116069258482e08009c1c81d011083c3c058a24000400d10700604400c042c0d010941da40046075941d00400c0303155008036006404070101a84511407a1070044000d4140112581c2000c1245658940150207008000b2000380c403400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 851063030 1250 851061780 851061787
    0xf0408030d1a1e01020f0d09090e010e060c0a03060b030c0304031206060e09190510031401090c05300d0210050105102003070f060e07030c1e051203 65
    0x8140000750b61011000300e0300d045018640865a9454440c100f160800c031002c5124000000030050b414600aa26041c80358011454840c02e00c81c0d100b24107000380d0b144000100614002404003500300c038030a88042c080c0ea030103003000c80c841c0d03104c1c2c101401c03a1642510b00030460a44945059055400540300d440102a01100b0f2004058002d200f88000c0c0c4403c9008204142c5015001401c000c861200907010f10759000100385100c640c888010900105440240481d050250300d01151411900c03081d50000f00c0068902c105460601500408641000c50b14614500380b0341002000d601800019005124210007051440c0402c00768102a90340f0720068050403024a002a0a0200c05100e01c441c46141c04010322043c1d46001031400039429074900403c580520350740000810381d83d200c0740c44e01840082030480c00c20103010080ca00b114461282841152115aa520307074440c01c50100030322041d21420700f80007c041000c0c4640e0014441440d03030500f0380da038001003015281241a808030580001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 851064280 1250 851063030 851063047
    0x40603020901030b09040224070c06080f010e040c0b090301020c150106030b090103050303150303120906010302130e0721351c0f061e14010903030e150f040803 70
    0x10b110740c0d0130311441910000715610f06580000c00000381c000c1000c0600c0c0f101d02c0210300c00c641000590b0790080d4025140da03c8541c07500400b80041c20104e40c44403144818400200f210500b0b443e1aa015680c424a80d0542900b041d40b4100d4035000002c0140e0159030a00040780e1920082002d60401514101190015410440300505a41881c410b05000c0c0800d0030040000070400404c50b54089803480b00c0040c5072007013500007070440c845c0b03400701030b202d51a1109000c201040403c4c02412a8400c54074000c45030f0080100c01c05660600c0190691078000000400401c4400c4500799030703520b4200c0802541000030b40d50507001100d400321000c0184c0490202d44440d0342000084010032120040302814248114440e50800f61615240040325032130341d204140d074002c1501300c4406043c5510085286010309a004e010441240c410342d4101c0d8251501d00302594055607008080c2d0b50195030f5040300c00c07508030600c03081c0006505c002c6601c500800c20210220340c19400340c0098580c0001455071390500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 851065530 1250 851064280 851064287
    0x30406050f070215060f0406050909031207030903020a11031e100606090503030d0216061811040c050d0221070f0806040507050304060e070305160503150103032c06040603020901 78
    0x1400c00c07007076600084039030b50f0f0004c9040440358001001c6541142500c4110081400b4040c1c507840550400454030a1026200000c405001c6042150100d200d0590341c0300300c01c800f0f0350944000500582c0144c103403000800d1002648244182e4080c044902030301d12000c1c49000100d0394a8061100c0d0400c10030410548607600900e4028402850301400b19401c0c40d0001c2d443c0d114089009061030381c001034422007002034004030036450f500729000700030130220000c1410010320100d10498000d00d410000c10124605807092201d12081a5140c03400c0040d03516803040294452420300d0b800442c003a246860004003803e01a200d0626669000c00c00030310014040d10708480030702480d220314100810001015804025254095000364000c9242841654110308168060f00b000d85140a0000141c1300d504586c00d04400316a4198103d13501c0c0c25622480255074038081c04000c0015005c1c503281035101000051074412040c101302481d211a0b600300010b03945a1165124030003003a008240141c20f582c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 851066780 1250 851065530 851065561
    0x301090c091e06060504060f09030b0708010519081903180807050312090303030408180409082a1002130b030115120507090605030903210103020406051e150f03040605 73
    0x15107002c1440700900b0414050301600442c05840308011841c0c0001e000184900311000066802c10342085c100d09184030010004803090055034090303c0c492003078241007682e190701c0c1c400711465000504100751200b00808646080d098042d0104a102c1c180e082400c94a00003c40003069068003e1090034940800d0608210309280081107114082c8081d500b00d0f10048106c90b030265028250a640d02c40104045401c00c000c81c0c00b05070031600d0403841c5000c01207184000c010701a0180c0a0403014050410300068058107140e542c422031b04071442c050b04180042d0041c0c440c020208a500461b1500d60f101c1c0f6000360400d074014040080d03652020b0781100d4000c0c1040681145000b814032003840e0500014100c00c420748214800c000d030010000342103070300500c159506030383d6410700909200f407030310300609000f10280010303131045183c441b0010721813030054440350304260001c0040b10808405800c11412080010b420f4040d20000c00200155003003502c003d5200b00c1c85840b0004560500e180344014514 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 851068030 1250 851066780 851066831
    0x15030c0307031a0703110a0206040309050a03030c06020d110a050901090e22210c020a0801151401120e010c0f0504061409062209150b0a0e0301090c09 66
    0x200603203020310101d02503044902e03c80d00d19641d048066110040d040b00280107046040307002010124100110a41c0460b03118050341c020381e1030b00f00c0c0c240c0b104100211504140b2008000c51091407040d4001070503034000d403407403e0014000007440b83c105408000107502141e524030024500103401c460b90340e0440000c0d0007420200140e00d8483ca0300c4210f001d49104440c0100c110244182c405404000140720140150f00e9103401203060010386103005024201c410008034400e034114800801c1d1550140300307e6036940ca41d64807120f481490680000d200c010030b462030341c0c1001900c1c01c0c20140311129016000142c0d05da03000014070b111072140300074440740140549400300a0204003c0162643c0200c10803008a020105150380d4560100000d0b128840c041d0340c41001140501c484801740c884001b42c0c4201d94040074140100312045951000c001454010712207030343c806021100001d0702c41e01e080d80102e080600002280e1160792100192400c19921515039151106e082c000401c1c45c6021501144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 851069280 1250 851068030 851068033
    0x803240d0b040f140a03080124050f070614040b0a1e0c35011205100b040b1302041502060c030a0b0105120412030507021b0114090915030c03 62
    0x11600000641110800300e006440030311404081410311500200700300c11240c2c00300626020b951034180c100c0d12000c0d060420f0700402c0e0004000604010780c1155407019101201e422010380080c4101170728150454100d01c00700c0301047c4038000005101e8814220010900406001c1d103207442c0c50221000c0f0002800c0b841c442e820801641c801114400f000c10310840c00c5400070921624000c011181d400300008542c000d110407602100d90100d1540010221214401811480e6a00e4400d2410820501500140142d2010a1141e01e00480e0b0b0b0000d202100b00600c04030300b00012400203030b01030381031014002d0300d180d0005040008840d02d034a80d03071440519001a03c800d19200702c510320079010041401c0c9a498680c00900c0031684a4412100d401c5c6550b109160642070900b058001da40703209441202084c0380c500400c1d04640005400c404841884e9641c08103044250b0044500d54a0200c961200c52428860b140070703560b074115081d01c41c00384a41400440040359040503d05181e41101d00d000b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 851070530 1250 851069280 851069341
    0x60631290109050603220b04020a050109030b160e030307203c06071203110702330c01140f0405070312141611040203160c06060f030803 60
    0x10742d0b00b0812510888108a0341c0c3c45d107035901c0040c412462041c044802d00000142c01c419401c00c44840660750145000351800316040d44c071180155640d000e10300004e040810070320001540420309000150480e11646891440e000343d64020901c0e5400822044428105400030199100d00c00e88814030015801c48402c81c0e28242201c15007101c085e90035140034005551000e009142c440380000a00880c000781043e076440e440703030030b05071912041030862100181c10702c13441755010b40c441d10603034001c580c004040c102107007489000c0028041204c03010702100b01d9030311060140018214007901014501c0d00000c100031300701e035441410400c4010500310301003240e5001d21000c41c000203100007c0d06c2d0701c00c4540101080e9594140ea42c400c00400107002d00e0400a6821005124400e100c1e80e10340c8a0405030704a07101d04410042071740030032512000300c1e0340d034021b0b181e050034403541d503601500303010fa0000500300c2d481d4000340c042041240c1055883d901b000040c08041c044a000d580c0d49560300b410751942 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 851071780 1250 851070530 851070611
    0x916030b360c070303090c0302090c040e010f031a07020115181d0c1e09100e0f0f0604090201050f07030503161b1211010c0906020f030c060631 63
    0x380e500610f4000f900305907558241504002c01e000700100550303002024514a864490400b02480d4030034040c0030007030070150000085d1302283c1c2160405499101703d0803007140d4413880040060b8440200107904640d00c40382c1203008800100c64520141403288125920510142282c100b41d82020b460088040b101040106048801062a1a20490481d100401d920507840c5c5510001c4030220a1640071100005000c100d28005102c0401c4840c1045e080745a659440c000c40c070082c20032609403106404150004080d803409500c2119900d105040040c00c04840c010007031481c0d008028206e000c00c0e00007083c00340c2c4070884003654041448520300041c0c4071130055403403800e001403000c008007400c08400e0314000c80c60180e82d52004005601008004100c034a0000401c0c1840910442e8090b000e40450341500e1000442103072110703440c0e0001013640ba22181c06001842c5504c003075203600f06040d200100312500000642079418a40d00c0700100b11125180c414903840101812014a80445042c4110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 851073030 1250 851071780 851071801
    0xa0e0f090106030c02070f0b0703080601030b012106030807080307140a3f1a04060806042d0605010f05010c050d112e05150916030b36 59
    0x40c152100b900d4041003419100740d0580c42e0010b603812900f8800142c0700c010504d190440040c0440c240680e880022075242c440c0150121080074154030f002908c10104000c02d10708400200c619001c42c51300000d0000e070307a81c03161001a04901000c43d191403000040c0301106600c005503029010b0010441443c0c45140e51029000c0403000c444405d11001d1510a442c07102c00d407441c501c13600386800041300841005100000c004200e4126400c401c200d21055550250070b0621840303007902c031142e0051010362039075110700351034079071184101d41d030300201c10304080b080c02c603001c02c07a20801c1c49800c000c500b650520414204503011501301904000300c0c1d1100c20003003003002402c4904a0070600740300205000d00824a41003629803840c3c80c0f0684410f008000b801100031908840480c6048002c01030380d11138400aa00400d00c00d0074107a4410024030118000c190110401c81c02c901d036502340020340344c000308041510256202504121603c0001c40300113038100c41d91241d02ca20300c400d8580d164078901480c486 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 851074280 1250 851073030 851073049
    0x20301120f060b12060f160e12030d1103100510081807050307080304240e0622140907030c14070c0305100209030f030705150c09040f020a0e0f 63
    0x580348074807442000702403064503442940c100b2005000401c03840c2d101500103507a94015920040714207441d100180d403480c188491f4114007038143d030b030748641403a15800308103c410725070308031a929010800854081c3c01b41031041402400301d0305041c0f901c03450480e4090800c0000c9600c603d004000030340b0b0701454107034414026a80645011590160180c560340b681c2d00d081c0781e0380c00031909803144c04400300c1e0482c07001002e4030440b0340303007480030f842c00404a0106414026040329200800d964442c078004900d02500540804c0041c6030541043c0503030420100e209003210b03400800c000740700380869015810000d102c80c1e400003003414148810103041d60001c00c0e140b20070064000212011441c10208030400384420019504501202c005c2c21840035038000950021501500c24800c0e28100c400c2014040152101380f0b40110290000384034003280741090581c018030240c011400ac001c408801e590340c1c821200112809400161140707005c641c040c103110082c0100600c6512180c202d080c55507201c9180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 851075530 1250 851074280 851074283
    0x40f14030f150103080705011415150702060a03050603100903031413020f1011010204032a1d0411040f09030e03030f040519051e03070b03160f02160b1c02030112 71
    0x80345d586c2d00c42d0170305600508075150300000c00741e103204c01c0c000313101c0b1081241505030004907403801c1140702051040d00030f4441d9240c0203400c01d80600c490104140a5844035034440d5010302900c0400c13404014180403121004012000b2a0b42e445002510043c214095680140e08180800c42c03040a5000101e840501d81c0649214244441640c080203100340340340c03d428120100299207680e12444e0107e244940080b80c0c0b6031101410030100ea181c4502d1791424201da5050748106041c0071f448500075030000b002001038505c198202e01403c12a21144907207031031100c000d10001003c0600f40740082027500c210302a01d01c29442400311101180f101c008072811124112a6081c0d49209000c4031220814580e02166006000c51400344100c440c14441140c8160f044060300c1816071a01c1c041a0a4002921f00d0043c0390007507101942c80c20b00403010b101c0c000743c15004880080c1518111000c01590a03040f041e102d800c04518180d141403000b000c1c02e0314106030030003581958100703500303e0780c0b482d00d4040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 851076780 1250 851075530 851075543
    0x31e0406061214120304080a031113060f0201150b09010e04230115020a111309051603050106050d02030606150909070503061c1214040f14030f150103 66
    0x8101045040d034403000041a01400c910b0b0350300201d0402d240300d11440d90520034540502c1401c180c40204a50031240b2865101121a040081110084000300b90201c1c610034413200800c00d13601b991481075035010042403aa40d8503100f01c030205100a003504d0313952960002e030015810302400b0281c04002622480300e420720f0030b21003402000b0000f801800c490b484104c0b00c500ca00c074502d0a030722228540d103410780d0f1a00c0d030101070025000300100c2c0e444140e52009415242d800c0d42d060300601c3c1c00012001c2c0d201b03004801080054541d2956414a42c1c15001130888000e03180c400c20401c1400c1c001e99004041c202e4041040005d40e40111340c4402c00140705500c81c400340c40b08082c0c3e0a03140c0c4141c5100543c050310540c842d10b046100640168001e81d1801c2c490f114207281045241455400c204606038040c104400d850600001076820840101414618100600000c104404000c008200410031441e50210002c410000c1c5402c0840000c08110980c01585c082540706040c1c10035141100e50184 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 851078030 1250 851076780 851076841
    0x70c1409070f050a2106030b1005090c16021008090c041415060d05070e0a050409020d0305183303092107080d05100f03020f0904020102011407021c0503 67
    0x35012202e41c4a2103000d48140c80741d2504518001c0700546c007480a0368030a5280043c035884a0368854800c0b410740c45003681c0030301070100151403003000002820780c04243c106110020102640020f00c3c80a0b08401c0700d0008000900704041c2a008000c004a00341c000d039000c210000c800e080c0c0080c6014002c1600c0900c128024007100d403074079110215034600c420244200614241a03a00400c407550068110b407188100b8400401c00749844d00c2101c03030310b6a000300b44000c00d5119a80940e00340e00f01c8619410305014421030707100d0a031034070950040e10780101c5100107080300c00500c0700e0820002c0c0d1050041c100000f031040000001c4001203a2881c40b8407429400c8038800321081c550b805104981d00106400300100b4012801c1e041904524012044400391014503034407603100c050410803d10010794001e00f44002c0c0591401c1410b20180c100e8010710002c034000084101120880509480f0440180e000d590b40c01c400051982084400c141e0360711b401440c44c01c2440c07010008580d803640684140c04c101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 851079136 1106 851078030 851078047
    0xf19171905011a0f091501110d090305120712080c0403080f0a1403062101060b12070306050a051503181f0e0c09010e04080d02070c1409070f05 63
    0x5d0810301003a0750308403c034000d90314640403c0b414803180c030101850403201031198180c8400c1c0341d22002c280d140745250040c60320401c01800b0960440c203000d03c0001400040c40351005202500d0940a00d0702c591504070718030311665000a040c10000251070940c04001d801900891025440349148900c20b6401da10b118881201c125a01105000200f40740d44062200d40420000341d000001d1219100c40b6400c1e01c82c0d02c01c02c021031304403011204014520b82d0501442c0040e00c0280d038001343d10361610011840343c41c1d4108001d150742030040b000440b044a8030342a50301400b11030044544240d4030324101c011840007a0741d0310034110708083e10341c4017859001405070400740c80a0242001c5a107452482295244003410454626000304071500125559001406c55240507501c8010007524121070180310020000000f8003400700d801c01c01032402e400150200b01d688960070866a226001c = true := by decide +kernel

theorem cover : BRFrame.Cov 850899280 851079136 := by
  have h0 := BRFrame.cov_init 850899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 850899280 ≤ n) (h2 : n < 851079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
