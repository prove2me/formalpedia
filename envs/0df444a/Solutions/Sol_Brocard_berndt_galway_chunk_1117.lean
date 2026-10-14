-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:18:59.107913+00:00
-- url     : https://prove2.me/submissions/0984bb5f-bc9f-465a-8730-49902641471e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 200719424 ≤ n < 200899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 200720674 1250 200719424 200719489
    0x312020a03050132040e190c050a09020301030f061112010602101a0901051210020a09090b030309092e0b070b01121505060114160c05042a0e030d030b 66
    0x651201e40c00c22100040c18885288500381014225042c6865000048540004114230034105005943d0b0a4548900060b2540f20000c2207101c00e0201801085589038803c0c0080d1054102020484c9600d072000d04160001045500855003a0806000f5800c803161f460800e48035445101d802001c0300041194202618011650084040c0107890040030001d240d100c0140c0c080080303061041000c5001c641e14189a80010310001450003001411818541e03000414940007041c1d0703108100c010729800d4281c5810b040b0b91401100c0646503100320402d6418144412501003c00008001d1006034a5895905143c086500001600081050354002010f04c021840c3c400e214904000751020010303490301e40c400140c4203881e428554010043e0f0000c2ca421801c0f03015140701c80e02a1040c41c040026903140e030200800d5a5850902c0760041000402e0300e50080e0344949800b84070401400e01401100414000c41e0601d100c0c0940d5174046a1030f41450001428445078000705600344801c504401c9007001030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 200721924 1250 200720674 200720759
    0x9011409071d0a0e0d051804053315070b010801061a0a090b0705011514010e090a020c150103030e01080705070b25020a030e0d0b06010503040312020a030501 69
    0x4010002d100e1107800211840107690001c10948031840448500000c0100014600e5025070307140b07900310092050600040c107042c000c0703e00850080c040300d4502c506141c0d02c00200030b0b0b400241c0d204d000f1b043c180c140d1280c40d81005c0004a040c5a441181d403a290f0f810004240d84040e441000641c1c50f108041100e0500c9809070350400fa40514450313501ca0008904071106207031500003a03c465400a810400c1140550054903100550b41c11920019039585091240405408030b044c08141d0700008020145400005150f101030034000047c05e10700750200c110f1601e503845180754200081180107109040e000398120341025401d203000300c804d2600460040986c0101440181448100f2001c20342010346190b0318800e04e000c10001444050603040020350310b04e0f40075021750210300c03c100001680d0410030758688905400c1400c0d071665485034401124241e00c0180113a04100030314942c00255211800108800840c1e940d02183c5541011405880c051f009941c1c0b000050454410300c042c00003480 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 200723174 1250 200721924 200721959
    0xc03072604120326011e06051c0603170903070b07020d0f030e0909030a09080309030c060310030f0510110307080f06130204080601060305130f1205090303030901140907 74
    0x36012860024030b4030f0161801c28114456a01c80c0d0390110391103420310140d0b00b40380e04030303800a2400d80980031000c545240520040c0a02c90008104000100c04440301e2a028a02e030700030789078001031a6a40e910390703c000440310900e082c550600001c1030350846c80e003007140c00003400c900640d1900e0300f0410b60000b0440390f82070300014600225151003005040c00340c0346200c203915000c3d0110404d0310700120b600b61281d20681c26400030407002c0f032010030604000000d42e198804090300070000c1c54400740800180c2c1c4c00003092807100300c070b2450012002a280d440b101d40486c3c4250020b01d800800340d1540310a490300e00d042060040f0f03041c010000c07019800444140c20146080d00700c4060b40786c44001c41d02c02f1020085162205000060000d4840c80010b0841d04035111a2790420454840410a07507003940c0c17894024169400e03504000002c507480640d00031070b28010342011307864030311928080390031600704032040e42c51399543d605107018135400d486c2110742c80842d45028001980c20424081c2c5a0040d08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 200724424 1250 200723174 200723189
    0xa020d0c0611030403121b0e0909070b0705010204140418020f120109110f010804122d05090102010518102301080d0f080c0a0509040b04020c03072604 66
    0xd8440c981405034503071185000700c0c001051281d43c0d25050034042c01081d00c0700314440440346051141c80c1c00c2c2040d1401483c02c2e96195075003800403c4020104295400060b000c0c1d126402100d0001440c1d4a2000c002c01c02c04c0e10134000035840310700d443d0304a0308092500085600803420000351003015941c0c2d0400c00c12180e1b04031071201c0920350000100d0342e9210505a04102903180500f510180b22032a54025501e2400b10382c82000d18054000441d0610402c1d5030060201d800707007a40e02c100e60701032591200841c011250007a40000001102d111200f018500c5c180841d000080002042d40d0a02415a0250504403802c1c4162070300440036544410346608050400d5881503078041c4030340b5080481a0886000503801c46558460401d29140d404c41c0c0850350110b082c0b0325102003d01d01034021148030300d4104c4002801e0410301e9001340c841e94004440503600c0f076618100c0b08125038a900c050402c0e1240c038401140c0300c01c60703031038803050601410000008a00032003031803410b8a0003407000c0300d041e81d000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 200725674 1250 200724424 200724437
    0x109050702120a120b04050130080901080a09050303070c060c11071403070b070606150201110301171e0d09120b01290301030605041208070f110f0303090a02010f050a020d 75
    0x2c1c02501e10082c0125011941d00508041c0001080382002d5680052715410351100015811001e40c0002140164240200345c42030502c085e084540c0909070716070340a800000007040c1152555a400d0946e03004480c4540411612445202031011501c181d034141e4105091041000b2603000c140ba544021724819071007038660482180c14162411300044005108049000e603c0301443d28205024005e913010f015040028017a81c8462688140600ca055088060605146900700019035003861605162441d46103d04e14194001c0f9800900d50409401098090114600380c400000e2486507684d1200a040e40201c6611010900b002c14803030449510b0040481c16503801110100e000c9a40d8914901c14007010000006012050704480d00c19485602041c098070fa441d50280d8200030f0030790703060000540040130740c0050b41c0203950544105855204451240307200150b0310f0302d03691040304c58101e035800107881c1d0744c2196085401408144441d08000d800c005030b41030029540c609007440f640802a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 200726924 1250 200725674 200725697
    0x9150631021b0109050d0914061b0d0806011d0303030f0a110417070902070503030f0a0b060d06030c0e0f130f0b0f040308060909120f04080f060109050702120a 70
    0x15154101e44550441c0b407886800c41d0000d030302060003404107072070565840c0200700f03208078114400c8111a0a460310020755440741c1d034101c001d203e80d64020b104103035a15a80482c40d070075240c1003007141c0c40ca03039211956203143c1071034810001442030015104000041d0100d5902c41c07095600441525880048040c129401d0340d42c440e514806040e0f0340d140c640f0074610018011518410201c0c42c071904290100c2150400f40c0d449900a040b44a082e1000c2c0c125041403010880344084040c0315500305040309000b0030b220800c0c1c00050965400340f6266411a50745a208004024034a04440700600c4410300306000c5141410700900ca694001f00340b800030401c491000d8042240c400040175941e504a0300c030309124030f001c1540d0980c0000076101500410440e00000b242490080c0710130344a00740e4540a0071644103654010000c0c0d811031a410414890144004110b01c801006000c50f4500020020310941d45041041400c48030701400c0501150004000b2800fa24080005c50703580022a00d00b4001145 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 200728174 1250 200726924 200727019
    0x603031209160303020d0f0507030e0f01020a0204050a091106070209011505040b04060905090a1104060c0809030a0302060601080f040b040231061707030506040303020f070b091506 79
    0x1030b040640003044101d0164003100349a4001280600100d007520742086800310003406441d14051054001d0000d4520b810320010f0b414192025130240d00c0c10b004513410061258005015600100c0d0505561a41c50182c5810300c002454400660b03101038454a12f000829008144c02d0681401688030a217040b8859070044c0784124102e40003000320710881901e0f252161801030212210388512442444c0e11070102d0354145851041408038008105011303c0c0c03600d8038005407801000580291440681231180c46040d480500051411512950140209180003800503024103406424140390f130362000100300004103a410b1054002d501100d50b0070070820201a8200d04600a00342c4400700240410850589802500000306581114448801e1144980e629940d241454403010381349600c084041000f0030700950042409098401c2110700d80a225128000e40400603a04126103500009030000440f0388541e10300d4000c041103070b01c107860804400d1030062203800c428480180c0f4802600410070320 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 200729424 1250 200728174 200728183
    0x12403091e0213050405070302040c080603071403070f0806010e100f090b040e01150e180309060a0e09150a14182508010e0714070602070f380603031209 67
    0x814443d00284400d2400e4502542c5070403041c80104d00450904a000c0c1641d80200e41c454407916014008104c41403602010361400a41c1d8007460350107000e12840844c0f0421008254000b400c40c0780700822003075140000b8900700c240f004143c060800d0b890a014002e112907001900c0c107d902c900c0011500c1b6007688001002400c0d080c072002d030650702e00001200e605200500c1d01c0b041390400d2031f2610550ba210340c41c14031106a6200c04400903001089444e49503d4040054400c64159140002c040c0d0b10b120007240f000d0105550103801c1940710014442d16180405001d0090510429041c041511140c04628074125100b6042041c41e01040001e0160212032a14114401d918044618600d000364000d00f10072400c0c0100014040200d00040307409019010720001c1d441c14520031880c001d501c0d01d514009411403501244e400140c0e04070400072410700b900114001040300e0a50440019029425065072400070105008250703038020040103075000b009540ea10203403449000000d64458a005040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 200730674 1250 200729424 200729449
    0x1801050f071209080105061003090c08031b010b040b010516020f040c0906120b0a1e08030a050307020114150f0a090216030923010f17012403091e02 65
    0x20414042485410b108500e001c10661a00b80d46411031459180d1101500703881c005c80785175420090b00a036125885110381d00000c1014041c0c1503400140780c4880c80542198094003143c0d4a0343e54814444843c132800380714954240b181101d0030071005400c400003a003940a0400d4654520b20100303540c4041d5154281c030007602c0e910040041140074050600581031200500030100001c580070000071000215105442401e14000e2602030303c20b2815102901840482c0801040c0d11000c0600268822080018200b03184298540548a207070000009085a255100e210440c0c00040107203c21400c0078051526100d07400c0d5110a90110b46501141c08030340280c1c031500d500c52001030903c0c8000340c080c0344003a01e24801d40d9801d2940d540c840000050160b510303412100108211010a1158029465800002007504001c1e00780500d18514502504003684048003c40d001d1170301c107081008000a003c07003107010381010043d1840a40303c003010017514410030203240b06042d445906658a03c5000200c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 200731924 1250 200730674 200730697
    0xc03091505090c04020c030706091a13110306070f03020c1906050a0e06150910150206061002030406080c0c0c1903050d090803031504060510020102070b0a0908180105 73
    0x40e401440e0360800000c0000325616a098000c07514100502c3c5000c2c0215a1843c1c001c5005500381151501c0d0080103114141e000c80d07030021301206141501d81c805130308503c40d450400c5100d0f0101d1a506015036509442c5030030b588260840410841c103160403001e8062001030900c1d0050302e507110301114034506080181c86066148608540004002558024a2061007440004e000e04420302090706e640781026a0385202d07030400815440c1ca1410500038460780700300c3d06800304246a540b84007101030321a0365400c01d00182c100004201850400d10b03c034441003410b501c000c520700740c50280c00900048020704a650890b10001e895030510108000001c58240010b002011801d200c181d05124088944012200c50081c1142c4501240c00303920351008498000c805035103595038150002400d580d0440510385d000356140d0b0089410340314036426400c2d003602a00010707a61159800c2818000b07000800c450b48007410f001c22400040e09050594002c6080b5201c08032183d000500181c5040c02a0b054494 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 200733174 1250 200731924 200731943
    0x10605040b100815180a1b0c0803040215030f1501020c030d050f19120b09190506030f120c0105010f03120f091a04060f08071e020a02060a0e10020d120c0309 69
    0xb82e00a114005c25070240c0740b03010b42005a0158003041605115500c104500820402c00c6038001140813080150390107440240b245c91701003544040c1900680003076815400d085410001c20003030950340c10000c86503100900052850700171003c0000d80d182d0801100404019000c90407442d101c0210040d07501e000c00100d803808400101e41d4004040080a4807540d4495040c4800700040c0e09088907a076002d0f18406811510030181402014060000903103110342500c20054881482c610500424801a10704d004580c0e17121900a0201d0950f8010f82010100c0440c4400c00c10015040e40c0e100300d16032001c1d0501019403161018245e07601c210b2940803054142c4800c004005940c3c1050042c000d13074401d910385104514428104440020b41169080b010a2125040614508080f0390b0000803000307034030403142c2c208001d40c0810110780005440c0000b041e01a65808542e04c0c00c800c41c40c05290680c0300800300804a85001400b00b11689020310300545d9452000c1034051080d04107030402900101080c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 200734424 1250 200733174 200733199
    0x60212090c010f090803181201060311120c060406031503170702040c03020c060c130b0d05181c080703060302061207020c03010c1707030b0d14010605040b100815 71
    0x1a101e01101c108140022032101c10003840324015025030042c0d071a4030009506055068100810504600c89a42c2e03100c1c040303004003071015809019910242d8071901c03420103100e81100910120800d40e404e4001c840d040641d0301d803080d44034401036030111200f916001c41c43c140042c0d10100344009640025100195400080764143e03071010017440c0203403080d034007000380f0b0b0300011013107089002d1b0781d80343c44240d004800481c0c09540c0c043c0103001444020010801c1c019900c1d02000e45641c0040510303032440e40c9402c01c000041005201c0512011a0710b40a0015081c3d0020380302d03a40c5140f0001c170414840f0341c0001c200441c0c0b281d4042c0029607405024559038400261284010250858036640144201854650181010702461381f0941294507406c021004040200d200c3c41c00c001c001c2420565160080c080c50f42d9810041c035800c0b80600070401c2c1c41c045054459003540d03245e4024034092030412821029507106c4e20110114008036203408585034584803d0b02c000482e803030740180e42c00f10303081940 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 200735674 1250 200734424 200734441
    0x8040603050103110603250504091d0709053315070606061107030303050a0209060f182202030402010309050d170f01030c0e090a0606060302190809060c07060212 71
    0x6410380e4090300c20303200d131016030404000c0c8030f120072600b0440101415004001d407420608500d13601d4180b50030000d0900780c0340d0f91100e04075506015840e085140048040c07080760130a0100304043c283c4050709201da803410201000e07030a8030380f1140310b0400b00c00c0036210704001c54003200614447c800070071a401d803c0f00c0000c00c1c401500302a10503140140750030700002d480350140103810381042510340a846094655281075004000c002c19a1040b0b603000c121042030b0f541c810b8020a01c040b5a1a0400d4883c0903a02e03070403812900c814041400317031440c4440c4004070a140380048100189615000d030303403030741e0b40c0c80101c010707043c2481c0081c4144603052000420b02d030806840020744068510340c4c0095501c21020085043c0c0c01e120190000c0b00401050144024201d061a40854513000f01c038408540341c2e03a02c2c1d0071644680c3c810400240c0c0410380303054410801d0400b44500b41e0f18a054240707418483d22150722140c015012158154000901d00c0400c0a51b1f0141d40c1001001a081c05d200d1405804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 200736924 1250 200735674 200735681
    0x20303040608041a040b070f0e040504050307031701082a15030a0b1f03021608030903180d11100c06020c010f0c051606110c0d030b0310020901051e040308040603 71
    0x1c04a812a40c8140c0c18448070f1485030810744134903000340a180c6c960300c54400945501c00308922840030005020040103058803203004840c0514400d00003155900b915080050540390044d00020440302c00d45e00410801b01d0000310507100310300824a400c079400c3c054956200c42c56010800e940c206541c1001d101010524078040c0d4410200d49205100a080400030003500142048620840c001115204905280b00346d01401e480f0305907240342461048191103100843c4c00c02c1759000019480003a60100d124001101c00b480c408094915100b880010ba8a82c01000300740c0d04014002e900c1030140d411064410b10300c0000c00c41d00084215070315815820082d004c1e00c07a10b01c001c2403c5041518030b144c003920500841d6105400c1c0700e4603808821182e40c60101402d1403000d601048c5400f80649000644103020340140c4200070b44001601c10300c50000c3c942040240ea1380e15141500c148043c00d03990344c2000807903054000c0c0e030001c1708507500608a245160b02940d00058413007040400c0124885170544d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 200738174 1250 200736924 200736931
    0x403030c12170a0c3504050a0b090d030c030e0c0121020d02210402011706010c0b0a2f0711060705030f1c0207020d020609040912031e050702060609070309020303040608 74
    0x1d4034031406104002e81145171104c2d001e0000754030400391042850300141c1068103500144944162003600d161903c0d02c461654064450800582100c3d4080407160f80505c42d601a440c4982810701040c042030089980b500301c41d0401c0390622400b0100ca400745d41d031400340c020050403414400c40d11401a02841c0000750094010380e034141840198030300c2031030f40703400c6124841c81e816902e1040c0c00080742c2c0341d00c588100182c400c0303050214243e1a0000110301785981d600c10401c210b000615482c010212015680c000c81d00d4a000c0104244942039802e806c0c0b003100c920742d80082412214080e2003020407410310a441020344070b40400328a212050041d030000784800900031265029070094a240d0074101d1040d81c030029407000ca02070b403801c0141004c1c0d002d8104d85400a0000540020507210355100e070340524404400030741d0700c580c00d00d55046840190b1200710001c0300100641c3c505200c029545100c00f41040388140603490000c0c0c41e03d407290300440c0d04964050b040e40d48640d941d10010b8040503054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 200739424 1250 200738174 200738177
    0x2004030204140906070c0f02030312160c0506071107030c0e0f01060905031e010213140a0806130303050402190602150a090c140609030f03090111030403030c12170a0c 73
    0x80d0800342120b00c1d442d0098000c41c11140a0492601c5850301510601d202e000102c8514601001c0000940d03400e00203800c45d0500d8215a100a1802080303c0e030508078140c5aa03c03d0045001c01c24010490005200d540510700c0c1c00d00e608044181e00300c071440c000b81072f8002401106c1841012900c040304010b218000c480c840b1040d017060742ca40391309071a4900c85018240d016400108015840d0320108898554000b000700014540010203022014080f12900700e2144080c24031150304550902c486020000c01112010308242d00307083c0c41781400400395482c0901055120800300e03080d540c4c0c01d01e030580d002d00501c0d88040460398941d0080e481d8040c00001074501c0622200281d00184035002c0c0000c81d07540f1030080d525482c00e0000750316840c404101e0f81c03a00100240507100141c0c07410003401803205c150303600441d141c01d80d01d0001800c01c1000796114200c0d030000e01c81000000c2e005a1230780030041d4016140101c0034410481101ca8103c01403e42c910780d040701090040483c5560301616002015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 200740674 1250 200739424 200739431
    0x5030409150503150f0a0b030316020f18131a040c05010801051804060e03090d06060e01060e22090206030a051504020c1b0a030206070c170111090d0201032004030204 73
    0x50704105034640341138030b11104500010f0300010340d0440070305001c250b00010000001400f40c940324040fa1840d0842612042201d0014081500703501d40175255807a016000c9810b041c041c1c640054900030030078054820304044141c25041000c128452000e14034218568000c4e003654641070400031203083c950302c41c0d9804507a41c0c000101e01c07410329040c0c104107010204800700460326180c0d03455004001c5001b090800b8041070010b0312113039541060301280350b40617600105000d42021080d42c1890010781c060005d00200708440085a25508610501d02010b110b13501741200041c11407a0250501c603500030752010340007007001400441a404280203450941d02c40c008140001c09110480c400c110003046507a000b100c68822496822031960071018016000261b0a56a039020a0003904401e000b05c44900c1448000d10841c0d50700603607410f428181c2402441a03180d0941b62200c1ca09c2501d41950280290150000075079000b5040b018080b01803016400c120802d511040343d10750418041240309905 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 200741924 1250 200740674 200740679
    0x2010c06020f0f032d070e0a210506090a2a03021809010c020d1d0310020a05030f13020a0911190305220203060609040507080d0206010609170c0906030106030503040915 74
    0x321260710445083c035541200205d40c030b680b81c0a60703103560544449940908041d901145803051441c0303d0b00c0751244000802d441105038608981040c50041108502d030b881913a004002c00c01d002c44d502a01c406015400314103540c041e84580d0a40401e0700065081049550481c915000d00091540704d8031400c00200a20391084800701e0b01c0e0f075815170760600044c1c8904081c642000c07941889089145008048504084442d403051050f40c05c581075070300c08521f010080004800000c245036a21400f4051800c3e419561070b80041d011a6040c01100703031080c0d8594103041d40091400c00c5130b410001504000b00701c0c01e60950000c020300030490b01010b00c0202102020030801c0c624001c90046503008000c0c2a0303556441c0c0030320840000c0104155014070801c80006142c407014000a0503034840c5601800c40e0350304101018041d01c009901c4a440c3c100710790404850400c0105841d03c0c807120448020304035417912400213015044a0f0806440ca0200140004600703038554003040a003042d1115480040d81d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 200743174 1250 200741924 200741971
    0x9030a080c07020f040b06090d050a21021b040b18150d020f0f06130f0f05060301060f030e0c0a06022b200a0606030b070908070b0702010c06020f0f03 66
    0x29910000b904a680904821145d140c15008464500e402520050500c58503a000462800c1516426517941d0044a030440501000d1403030103800b400500b00c410103040410900955401521256206602c1e41081c0724859540380d0b00082440c0c0740007001044400500207150a490398140c9500e1b050f00c603c40c00341c50982c00d10040c1203c059400400f0410083e031003406001c1003004002e0040d901074001c200e4051280842000b40300909101d060107900c460400c07886c000325800700d0b006140b141900340010480554040300080240a161070003099800c90550007620b0480103001d4242d004280060203c2e22982c0002c1e240b948000d1201071481e10b0541c003480c0d41401800c10740d40e8000ac0d04046800f01103020380d07885903059414150441e0740860441d12218200c40150300203c1e283c80710740041c03210705948001204054604000900005403402ca0188090300c43c0c40030090520007070124140a110281d03047d14819420406034076035450b050324650700c5a601c216245111007002d001c01203d60b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 200744424 1250 200743174 200743177
    0x706140a0b0303090f030a081209070605030c0d0b010c0c14010e0a05010926060c09040e0601051c03020a0b010b07031b050a0230010c0905010810120804090509030a080c 74
    0x3001c024020714540038980f01808486001254803681501c40c5480c01c42c00200050010074034407405014007107090071711070b0b106404d00c20741d50b102d4400c000c0b0138010301c55800e42c03150031119965000d13540000e0b120710020058603008a6020041d01c0e00c00000d4000441e50401900038905070700036641c0110201d0601c08004204c3c0c69802124005000c0841c1070044a00404d4000b91000d52071418501c498160300020f45401c504071004500c00740d0204404400781024019215100c070010040c015541c10030022a42c500c0c002070962441c0d8100001c8401454001c3c40198002c2e0b4002c2031214680da1181c401e0905503029060450001e03007240a00b00b400c1c441c0d1032850107a10341c000050410030542d0b4003084086480352140300709400c15400b141044c1090b00403a498180c4449001140948a281015020754041da00181c1402041070400214031038840b4010300380c40e00b40800f90300d00709040c1442e460340d0180d50495640d40e807520042c40107042c800400390501200ca595903204684c1d607161107d00c80d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 200745674 1250 200744424 200744441
    0x27100606020f1c0503060d060920010c0b040305180306090105040b070c0302032205060c060a0e0106050a0e090102130602060108061b0d090201030b0a03060209040c090e18120706140a 80
    0x307116a03e000103141504c40e0008540005000702100c0314010b0f20344030030003140c100543c1120103031541d000240d000100034903510115142420a000380620740d44462038402c400400081c00c0040014440f01c0c1c0c00703042e41e0745c20503d80025040302c40034076251481e14001d080940f42070f19100504800695000d205130305880025034194080c60500c40c1901e4003a042088803035403140c5a5103510b0740170a664844034060314007540260000c2006041c11241482100d41d04452800030340d050502c00c1c01161940300245044440b14143c813019a6140080c5500a008070000d9104440d1104400074003076500080c00d0f8140c400c01400c3e10342680b541a13440f9180c00010088c581015000d110698580340241d1100e12035500604000c54402c502d40c00107a403012082d041141c02540c0403c0250190815100d11400b041460801d0394149080460304900c01000a20000c850302d511088102c89140900c84044d80c00009207500d92100294078129010340307000000311000030b0103d00016141c62090141882 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 200746924 1250 200745674 200745703
    0x4030b13020310090f02041a0906030712081305120304060206092103040203011103070f0210020306010c14010906060e0609100501051e12040602070308010e060927100606020f 77
    0x1032040c40c214103c0c0030f00524402514100040d00d10580907031205e00030126100743e003c2e40c030404807400c0003c00200c070380050b000500030741c0546c2c800d0092821b031510762901e40382c11039540794882030510802402c400a541040f5000007006d840368141e00000000390090b6000381c0c080d65100ea50301400e19503942d100d4048034142c0182c0400a6003a81e40700c10041d90850300281c0085000304100004c1462948281d41820010b092900302407400c542c103100c040134003d17011605510b142400f1000800300141d6103c09803000440b0601002a01005d6205408107680420203220b540d543d18060004c41808841442c000c07128080040d0341c20142199010a9840c161266401c0484044404940140800d40102c4042c81008801c55000c0c444400a100324484e22000d681d80c459890018600401a40210594002141440100d40d500c4040e00c5e0320002c4102e80c103001b0400118001801092070118000c070f4001c40d810300d0540f1040781c20000988515408407140c0358514040c195841c1d859001509 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 200748174 1250 200746924 200746933
    0x51212040605070c050109030801052d010e131a010e09040c09111204050703020103060803030709150504050405070c11030a080306041a062209020412021201110c0304030b130203 78
    0x90010703400780d0280350400628078140c0f108410307036038425084540c0c00ca425000b00b6a0007004114916103030740c4400103601d035080c0706505000b03d6201c4a41c11040075013218140258031403044855140e40c404080804c941e0340c003c0c0301d0704101d1081081d01e0a841101540054460f250703805084c1041490305018503403015184040e01d10b0506008010b0902c02c41e00345480c8010401d40c09445a10500240a6401000602070a80c0b542c070001d0100e84895202d11010741091013042011504010341e08100c0d6501c6020200031a81d001048601c0c5c800c90300480ea015181005101325079501ca6900c0240c2807003402c203107880d80d101c281059921a0701240091040604200240c2c4c5414a600b2810714008028442c00d1203100007000980c580c0c0200d1000e48500800e28421161a0180a02c100c000c0c980c0c0300c000c520342418000314030804925a200603000b1a141d2001c0801101e09600c002c040f0300c081e500b42e54a44c041020b0700e0b9100c3d402440700782c481c00202004620340c2d502d000200c64082c0c0c0d0090061 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 200749424 1250 200748174 200748181
    0x14010c0206210f0604150b090103020d0606030507112a0a030f030c03031a0d0b0910020406110106050402120609070c08030a020403050607090503031e0c07030302030403051212 77
    0x11108102125812a003082041c400480c80d16030b000b02e440d015500c0c41c49480c21502c0c140b80401402d00008241d680b1950900c2d1a0100850070481c1c12815100741030a038640d82c1c40c0000c010b8010744103401139095042e02c0c001c3c0000340c05515a2000c0d0185001e50b071102c161924244149950707002103000d09020050b0414244555500102c402103001c4016060768a029aa5103c200c640c4081394819000300b95126194000c069040c49039420302d400c41c82a10040070350f50404aa50301484c00301c010044207000c40801c4503000c0c100590030740d45c80c4045055581c3c5848481c024090b8036001450a40f40d030034440003164cd49014000d4403508003030943c3d098001d903545410065405000b500110a0280e00d01c4043d0224000d03000441c41282e60210150349c907480c6140052800e100201880c0400503140810301040d54044200c0b00140c240d6601d06000d0386210b00311284501c0f035a041c803440392003583d500204058010001d07008407030240f002d4a040c205025140360b294070844681904894008000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 200750674 1250 200749424 200749427
    0xb041b030b130f0203070b03010f0b040b07030804140a080408070b0c100b1c06140c190f0e0a090504060b011b08340b0105040b01021b030c090c0d11041401 68
    0x60b00b2074003a01d016505400c66802003410500350384c00000c0d41000010040c00312020901a038070003080803010807850146010108441401080001410820884041010b00820b40328a5458807540e1094030389121041c9020342907944184110303000f5008a540c002814190202622150103000c4058000d180c01c11541c1d0000349420014142c0c0462900b86005222081b400400401c900c078403c0010740c2ca010150010320707050000c00c1c0403800e100410455246035840c190704034000405080440600400344802c1d00c2c1440710242241d00550a0100040c400383c49421050056000390700801440c0980d60046444448043c951205801c807103241c80d0004041c24001c01c54818110103035100520b20741a40494911a2090442191a01c9103550305202c40c10500d5401000202c400b0041c4140b690000b035261407050040c1c582d44540d02100404d15102403105d10003494004003108070b18a030030f04070070901d40c1184006041d0940b8140150710305048001c1200c0940300450f69030104545540d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 200751924 1250 200750674 200750701
    0x51005061f080408161205180d030c030c080f0a020129060a05070c0905070e0406060305060d0b0a020405041b03060f0f0e1b13030201081b0f070f050a0b041b030b 71
    0x1806040d0920007008017001c2921100c1e40300300750700720b075884a903969002c1e000e0340006031441e452144a0100c0510101c0082c0d04160020600743e454240030a002126060400250160451106050134001903140150b0f41c10761100e0601051100c0d040000c4040c56540c00402011301400354002c842002031350302c550b0141004d0310a00384907800d240c0383d003a1101c22030740640b101920300c0c101040030150128250324041c043c1602138030062600300800c0c0b40c618000360403000b80c000701074001d803071072000701c1c000e044140c040701d02400010380b051114400740e50396890010840c060000000c0d00c5d10a000c102039081e0032094003202c0071a040851468201840b01007010406460040798003500c100c00c951003104080a07020b4a80001c2c600d40046107140000362240c1c00007408039900100d0014444d00c0040c1c0c0209542c2155100c00c0b0980e202d160f5442c140b0100003103010041c10b00c1c824100100c040105000d0300314450380c403d280e25040140312009800340d45c13450b404010100b0002c01c0014076a41910391 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 200753174 1250 200751924 200751937
    0x7030515090c031603121119030302070803040f14060411060307020a140106080706090b0a0f02100e0d030c03050f0109180b0412020c06040b0409020a0903051005061f080408 76
    0x400380c03258185102d0009240c02058071241181d9a800c1004006012829a40c5510b407a00ca00301062514841c402550702c40d810f50301c0b401440c506038504032080c91b00c240d040e1200c01c0d07842000795a890825042c104142c2d0103465040750b464118030003105100d800822407900959010321564010740090041100d2a04002c10041c00c511407000c201000c10000e0a480341c40f0a1403000010303480b800e02c03641c0ca042c01010380210341807000c900c10820140803240100c3c0c100403000c1c41c100310030b010001c000b241040b00b0090004c62890810a6240903000013040348018011a61810044012200400c0e420f40b030b02241c1030341c107000d8032100400601e001c80e00040440210b06040010669159440c89070400b42690150381100f01e096801c0b4085070100701a02132160300308e583c103060078a000346403800391080d4004c90400c01d8001c140d511340280a60031100145603c42c1c10788000350380150308000208401c468051048001c0458002c05000c081e0b8038000005803950354044550b215258050558000d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 200754424 1250 200753174 200753191
    0x1110c011b0803041b060906020a150b1f080a05073c030b0f1503190603150b0406090b130203090309060408060405060601030c051204030c0203010c2007030515 70
    0xc80420010ba0745000851003144503030000d20204024007501460407a05402c00c8003440b15602c01842482d400040515545903c441d040007030410302079082c000741c8480c0094940056002203002d510030700c0c82c0d440303804052042c0c3c1e44039119901e144404059480c1a41d01c03801140380030040c200000c141e00315240c2c64036400d11001d403040c400000e54040f80c000040c01000000d03503803a1b0800413849d0080521005000c11910b080700c0305005c00c01c0c007515100c094100f005c0c0c0a0341901000180c05150403000042da001000140c0f00700100351100003402880c0380d010312440c90500045100d0400d440748a0103644040d1030500500050aa0100254005007403003905210034040032060b9a01d820051001d1f10b204405006141030a20b859031038480c001d00058113042c1404640d104269020094512804c03800c00280b000d900c4505003071b60b50300314800000c0d4040d4200b43d828043c080d0800550b104084e11122030741c03500c00200500e9030325400140402046608034110340d0320030b4001c12440780d8002009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 200755674 1250 200754424 200754467
    0x4030305101a091203040b070b0a05010b160515010603091a15060a030f02030a1b02010902102703110a0f0f050904031803030f03110909010608100801050f09070501110c01 75
    0x840c0c000c0d0f80303175800a07071065012010000d144006c0021442000d50090a4290280310550500c07000500328003600101100c04d1000f0140c0c5018000700304641c0161400281607072100b941c440c0303c0180036149a04040e2011005940f00d000f01c4450b007940c080c03207000d44001c10004c00200700e01f084050b910283d110001c05445019089007070303000c5e10040d8064242c8610028407107211248854000304520380c11015039250004a03009030b20b581d07c00c62403840c02464640500010b0502c503200d92500d8000100c52004440070200c00c0000c00c0074020041e0710100c0310742c0025640c8100c420744011881c0036019660005c20740802c01410829450781e00035100b03050810300100e56081c8051644070581c800d80000300c2c1c4a407004c2c0c0c0142c02d0700c191381c40044282d29a03441d0001c24004501000380c10320600e000c104680e8000f5500e4801c0c0107201001d4412203000b030186042c040041396400314250b58602032401460300c0001e0a41c01aa10a5401200c040280c03041a482000540c1c2c038020034400520036404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 200756924 1250 200755674 200755699
    0x6010f020c060f1213030905060403030e04020a1e020601030201181a0a020a1e03170114122401030b01091e0213090f050a050a0e1018061404030305101a09 68
    0x140c0c0f58407544030b04145d4960b0b04009020703003801048404640d001c10b00400f000c00003030001c607500041881c544002958007682e2000d42c0482150050110b008002d414011048100354055022a400e41200d0003603036070f0210304a0a0860340215101c900c0703100d049506030703110303104070441d07a0001d040002d401e40144c0e280801c180d01c9800c400701d21030a01c0406900c5c18142c141c10181c000a82807180c0140455010f07056050003a0310303886140c44c80c40588548514081da41a944040160300c40541001c1d1414203415541d1b5503082e504030b02030108882446a120010400a09078410300e00c030070501c8260300b071401d02550301d044025031001003010440c220283c1c010402c01c2c6180542c4119071284040040c46140014044003111005400c000000341025409003d0482c00500310640511200001460202903440c4000461211a0090003036003400303c41081c4001110341644074500a40f004d001035540c2d860b0860f603903941c50094184411201c03002c0031281540c54045e051181c0050300d0010b0a51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 200758174 1250 200756924 200756947
    0xd03051317120906010302060703180302150d0b090606070f03020c03060709090e120d1107020409060501030212010e06040b040201051e0d0f020c0a06180f050d0806010f020c060f 78
    0xc0328141c01219025001484180609803020902da1064601d00a0081c40d419940002e51510483c0b07009010040e010742e00d00c11521580282800442e4000d00860209030210315039241a009901100034503444c10b035001c00c06c0c4c288030045612a9000411080c5450640d170303210014500380c0041a0300310700c540404034a17280c5041000f00e00444250f16030540c2ca070701d000184030a642610132206600c4e0052840c01c11251050016030b0200d258100e804105101c40401d80c2d0b005000b4420007039840350500e414201885051382c829416230f402030f603010988184071804c071030980300d0707041e9004040d5101c280000d0105041c01849a0031920524040d80341074000601d200048118040c0c11540c507200041780c481c0d07641141308444000c101c182003581442c0405041a0321f840140d0400340c1500e4807405840501c807030744140c0c0c95425602c81c0c420b03144551281001603503034003202c10700e0f40800c018401003145903010704a500d80c4060a98018801e004120052120a4004550040700d5020900c284900c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 200759424 1250 200758174 200758193
    0xf04020c07120b0a0e0a0b010905071b0605010f1a0301141302030906060310090c0905040201170f0703050c03061f030e01090f0b07080709031b090c0c02031e0d030513 73
    0x24003520040c42541000b0325100201c0306002e007039140c1a41b14408240016804e8200c45044481c40794000515070780302c0900b55102000440c09802039800300c00032400f0460141d12042c1a600d41c0314400c2d8265455000b1803920240c5070151200e514070078801046a0322030b944401c0408000a8240d800c4c03208403003420030580c0c201b5501110b264201c4c0c4c0404c4000c3c00c040042020194107c40144034640e0591140e5848201a01519042940341c2c00098296401801c60300c1c6d41007800080b5140900d006a829003904805403041030000341084045100c00c00410309407030040d03c00511840151482041d920015260500c070700c400d01da180c0380d550703d69030000e128140c040d0340683c1c02c030f184040301c501c1e003403440902c020040303818020b0850500c0034196200000b04190382e031110f049482e03213007a06848804280540d00044d0b1107414544059001c0b6484541c62401d180709034201e491072200c2c00711035400d80e20b01d13140d40c001660000b69448000c034800d41003950000007400107024480b45507112090070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 200760674 1250 200759424 200759459
    0x203060d020a120314160605060a12260702100806040608010507020c01020f07060c12020a060c09050316060e0415030204110912010c1b0816050705010e0a050f04020c07 74
    0x1440b004081100a064200c18104002001074031030915201d1a482c1c0302c803891903001b50290182da512000980e01e91540205100903028161100203800c60b41e242c92656807050174600800e14080054034109481c0102c282c41680740e0007000c4101c016002c05040f61200c3c0010580d550058407018001018003080c80f0340c90099030203501070204004058006454048041614100c95000c02010000160301580915000e80e100c002d42201d00d2034032100701e1401c504002c0c003030515460b14505a4915410100c04001ca82094080e0350802418100781c3d080940148589004288881d4002c6254903055000c0072310110150444400c81d601d03900402c04940740d6041c0c00d1403e00c0001051000b41c0707080c04a4190702031a20000b0f00c40d0924101006282a40d21946284080001e801c84410840c0e441c060740c041007001c0d1f42c403120078411070401c1a5541d42d14130456001c0394285243c2021810f0050044003900c0d4041d00b01d91130b5403580342c2400001c1d8051084c8044500400201044420544145050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 200761924 1250 200760674 200760689
    0x703020715020a0e120d0f020a140d0e030d020c091e0a020301090605060307020d05070f140a06050c0a0507021908030703090305011109030a03120e0712120f0c060203060d020a 77
    0x3241c0c03081c900c0280031201410000c91203540d2910201648580010709072541c03071704611f000704e910760340703000142c2c500210401c004003040030140880001007800252a00295110b907140c1050401c454107154a4003074a210b0980141c01400e060511030411a18454100e00503519038540307401d10081640800d001a54074000842c3c000004000c11030260285c0d601425088481520b18103016001039a00c8030382e0800303402800380214404041c0003a119107078601c1c541200c00b000401f048103084d191a201040400c07117000b4078180101d09012101c505981c6441e00f55103034145040302035001c001c0303a0140802003801c00904c0b840082040342003030000e0544c05100341c548540560440c9006402d5035410319148914050038021803105560000b91040c0041c1c040c21b1059020072000c41e00c40107131109008102942c0304071903000480c12081400030000d1406801101040c01c00c00c14200d68a001d42d1a000c4009900702a00c0804158aa4015904003400810151003940150701195175201ca0303900412 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 200763174 1250 200761924 200761927
    0x20102030906100e01030b060d140102030402031204140609040906110318010b01080c07170318240c030a0e0615010807032703020a020312031b09030a0b070302071502 73
    0x15010200a11a0030003d00c08040314102d080c10341d5100b04980520018103028416400b00300076840d40d0720f0480d001900301036446035000d80021014081c0d84180c0701240a80720700684060703c84243c10958040e100c546034080201805401008000d41001414a5000d642c403c860800503109225140354401c6492a044c0c4928083d01000002007003800480d0b02a41441d01c1c80046aa200c015a81c0c0305c81000b1001da214143c604115410900c050b10708680b840002041c82800010713810100608500e100456441e074200b101d0003800006030a251444800e15000441d18202e40c801c040e650210020b0400170350000c583d0407107890500305896000300100844500700d0301e545e0080b01c403030348040c2c2410140f00918038101d2000341c5201000010140c101000c8000041620911060b00b045800034111102400300361521049640103807a404a4140a01100c01c0701e2000c480588034000d80040282c00c0085c86602c41c4951120014481403c01d6402c101400015041c8030454444000180c03006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 200764424 1250 200763174 200763181
    0x10b01020607090806130f051501050406051804060b0105190509010906030b0d060e0102040503010207080c011d0d0302160b0412110c1c020f0604030602120606030f04030f1e02010203 80
    0xe0300780800641000100b044095090015020000e00c8981003841c03490701650360310940c20420b441d4090140014106e004500c80c002204400100041c143c1d401101d0820840c0e0755502000040f0b900c00c0505030030040288002404554964030501200d4010305020f480c1242c0d686003041e4100c41c0010070f6010440208049140c0d5a0002c6c948014000e541410407140003410000f0741c2108070254020505900e550060900080c00e40640d0000d00000c0d00a644443c00d6107000402500034801c0700089601c0d1110071807900210514408800e00100c0281c04615460386040b000313540440d0340e02c11a401101030080001e0f858a010502c11030003525000e05542031000c000745003000080c0602c0d81c0c2d034040c507e50800c90b45d50301034211030708131180c13039000f01111030f0b101080180340802d41096001c1d80114001091206940080040d4801140300c404299681c0c810082c00380000d035040401007041000140000307001e2000d034825000e09082055945606088040500795518003010050350003100b031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 200765674 1250 200764424 200764427
    0x20d02220207061b1d060d020a0306080c01020703230a0b01031a011a0a081509041527060209030a02030f070306060806040b071b151b08091b120609010b01 68
    0x400d13035a42d0410900b04130070940c2c80c0d002040241812160142050000224481c03999050304482000321040c030199101c0e580140c0c05001040c83c0e1040143e5801040540145d030f62000c01e2040540fa40b00802d503403c403104a02c815114002c000c010402031203035211100108505221b041e0095105a030302110360140c10401c039680c0352042e8400740c401d41205149200d69124002995090f48051814120554a902c43c0340d5002c60b0305038480381c02001400070301c4144900c0c40c900c16145480401d0910003800c0169190f03610200c44c1401882c60403c4026a0001842c039030001c081101000701102d411858640001e400c083c2070030119803880e448041c0c10020040c8070300466004140a07005090307180707499100d010892000411040c201308949030005d0b0001c074213210350300318903422026a04000c048000c0381d070000e0681300035000441c41880003070350100b84248001841188081d01428100d841c102c0c1e04120b649416604a9120103070b0009612658000c12866116000038400460307441000c600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 200766924 1250 200765674 200765681
    0x304020418110103091a070215070e0604031707062a09180203060a0305070305011d0a03020d0f1202031e071b02010804080705030c010b03010f0e0604020d0222020706 73
    0x38240104a1a0711000089409000d2107807041c90203003404111410140b60804c6280c01ea00705002100050b0700c14400402e600045041003811802c1107942c0c80d4031380751415141d01e4008405144d0201c01000140001a42110203207059840300b035a40e030030410b60303503a80e80c141d43c0241045034119160643d02c8042c000a00c00c00c02c00513a10f03061100900e4203220088040c9900c0100070549607400002041d80e03615000075040c01103070804140c4005c5030b12460030a010b0001100182c2142000324545002094003003032801c1101d41c160000c0c070b5401d01610040e41d02c4501995950103014200941e0040c5541900045105481d10f0340300010f0f540c0f00422416003100d01903e000f08102017103000d10500d075000311302c001e0701c03a4090828420950f07462034441e401d84243c81000f40705000114003158020015040b00c01c60300c408400902100303610aa81c90200c0d0072100254085500900200f0007500705080000c00e002d00140074050311602d52061f5400e210101c1c0340d1541d600740d0014000003400100e21 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 200768174 1250 200766924 200766941
    0x70210090206040e0402030a050307050309040f05070c17270907020604020a12020a03020607060b150f0406050c0f0d0206010303020601060503150f041b0207050a09020301060819020c1203040204 85
    0x4040100010a4010540b18041c501400030280220804603080d075904000400c10582d022084903030300c00c0d40d45015038403a0001030035180100e04011024000e844c1034020548a46201e9a41c00741d082c4040e2100540701d11740703070310040205000304404103800514424030754000041ca18441d500100c0d0300144801c1801c0142043c04540200c0144401a0764103626a4100d0300e031140720181050940c00041e01418a5070f100a5109a000480303404101182d040454201c8080b00c00f0f1544600c1d40f600c99040348250b0202e03561481c0d0811091201d10b0080d0050b06150103031204494051021300740301491b24605803108400360744100010010035604115140c094140d502d002800c50505285100c641a40c600607075100c3c1c00d6a4040c0803460b00e89a000450310401c00f02c0c1380e0f10031403800301c01a40300e040c80d020b03e500030307040144003007400481c0d802100d0403540681d40b02542c55440e00104e84000c82c170b8040506006400300068a03400b6010032005c0f62940c40900c1040d605d00301b5104001c00c49102d00b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 200769424 1250 200768174 200768203
    0x20d110411040612060b0306060d06080102071a06030105072712050619060609180b0a0b0a0e060306030307030c050f06010b030a06062c0406090f06031205030906061003020409140702 80
    0x41020b1000621b06070949400500a07a5100e0716103580c0c40b0001b000d0581c94104603101d41c8085405010721501c2c13007050701d910310000c088004c1511000189400c1e12400c03030b0100302107103545270102d451a18010303c201495501415070800c0c2da440b00c0c6040b8090308808001d480690040c07050186c40740a000c1495400caa1850003000071524002004c3c02c044c006c1d2040d00c1c540082001c0d441c2d0b5650480c0c001c003410100007000c3d1022245c0b603000140c10f981003045604001103001030110181d041038411203019800040003503003486129038040b11007480720441203500d030050b410800740c071480402c241806000c080d685182c80c1e14000c1c214400f00c90b00f0380c1c054030400500d02e485d103c8030640d0410807040921071071a52404a0803e07000300b0060075071a48510480784c03038401084904036031071348248242ca01c146041c031030700b24005400300c0722808143c0c0c503440703d038102c2c1002c1a040c0c645030a01c03650030822420050304140c0d542c00520100e401604180c1c07491089601040001c99050010000d0103402c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 200770674 1250 200769424 200769431
    0xa170316140105090604030801030204090c050d05072405070204050408090d0602040801110702060a030f110a0509040c0302090a090c14032806080d0c061d2406010c020d110411040612 80
    0x6d910011f2080b030040c40060b000c6c0da5140c00c80c8043c042001207550203800007500000501030140f81079565601c092007082007030110f032211144001040705038007030b000180c0c3c1d603014281141502003200414015104403401c2504118044a40d22411f4982e0030441c040c0b034005854a1401414a0a580c00b801e210b10714000104010030050342c6000c02c3d44d101600700c2c0703000131382d00076000e030f00348000c1c00014600341d032641d0003144c60003c00768800021701d500e50060341d050280003803c01040d000da0140c0103032035034020040e81c2e0034041c48100f0341c46108440d1051408a569010b0060204841c3d84191102c01500700300b030402e1101d50b010403441c0240c0880c21142009201d01d440070164942c81c034248070b0f10401c05411202d905100c000d4201111908005409020800300118490b55030103a050a00c050000c241840300b992915030942c4911404040e1981e520502c103584c2040540700100400b2a601283d000314148251134038401d4503220703100803a401d03981d24107141e005014a020111240b907501c0c00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 200771924 1250 200770674 200770681
    0x1509010f09021309020a1e030c1703070803041b03150e0f071211130b090c0703022e110c0114011a0a210213080a020a1703161401050906 60
    0xc0c2c5001c0c203d0340890300b00000548a0044c800200440c005074002c420710b6045400102c030045a4081c1401100d104071410150030b55034a109079092140303080500705d00d13001400340d030f00401e00d01c5004651042c4503008040c20544801c000c001144d0703641c0c10980d8881000603207101c0b29900c9106486c0e400141c40000c1401c441051000c42c0e41d00202d004151030b03c010b02100f1820000c02c204625000b140041584804180031000e0350014404148018801d000c49008102009994000c4a8200c1d0301a03000d00b42d001c6240307406540d4100c0d21030290010030386804c00040e04000c5032203401161164007882e15510788a0b007810a0960721000c401c0b26041d114a001000b1106500d40301401100600c02281e45407800c10380284d841a030804003c012004140500190213040356008001e10100780c41c070608442d4503201d82603074801100178001d4000640325802d0290305114500103c540b03101c4806c5034a001c074000c42c0a844000040700444614040d0b07a40c8008601003806620750082c00c5d0001001d40d8038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 200773174 1250 200771924 200771929
    0x6060c0f080c0304031a060103200301140f030d1806090b03060405150904050a03090f15200d0207051806090f07020102070b010308120c04060c140307051509010f0902 73
    0x8405410040211a00082c0341000b03440034016540110b4000e546000c0d0200e07070143c2900340100444000d0700003440d00640f5003040400313032286418080543e0100b82036a00b0031000e8070601e400c02d5000740d400303c0d840c803000d25203981c100710003058090315503103500007000e01004481081d200da0300014103000300c03400240701401403034050780d070300c14811100404c080e21062200d00540d10301e42d60154208034807008001c180000007034502d4269119681d42a80380da980d00e001c1c2800300d218045d04640c1083e00003e542c11911030031080e40d588612080000c0c0c400151540d9601c0c060300802404056000114204800d01e009840e04002c8444480c0c00c46003071800e0800541c9041d001000703200180c60144c08101840e00c05d5051f10852039012980942075612070400c6d2500390404134034a20f03903030303924000947d0b50101d4206440868030180c407210840802582d680d8250f0500c1c1c0c0d245c03115840b041c40001c2c0401c50402c00249241211800c024940c10180703402030a54090144250085040410400040c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 200774424 1250 200773174 200773193
    0x110a0201150b031b03040204020f030c1e030402010f030915060612181707080c0607030204140a0302150f0d0203070c03020f0f10022208010b0a050301180f051002030702070906060c 79
    0x800400c1c0c004d650740e503568070006009004100500900103004020408511000001401d44a1021a461012803200100c1c1d00061000710f600900245c07540600707004090080d002805081d10070f0420300200c44941c0003020450f0015405280080c1040980003486d817030300c0c49400c00240070034900e59203001c1c00341c852840817600014142c2214000107200d0083c00740b0314083d194a05501025110345041c5040010040d41060044003008444c000d01c1009616004039030f40c080305c4c2e001c0c20541c0649104840304010381c01a4201c012070120412500b2201c01007407000354410092511041c0150b401030400a00c0e01804004407680b0340d100b613010701c83c0c0b04800121040c40c0013440c2409a81c8c0d000058414400e0700440418180c08000c0b00310116411a044d003000705403070425150710710707860766a104150903074170051400902d03001200c0810307000c9521780302c0c9031401500034411036104602410401c0c01705d13481109c8410060300440b0050196880901620b8010216840e100c2402190307615150703080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 200775674 1250 200774424 200774461
    0x11b090e1b0913060914010e10061409030a050d0f05070c12030309060c0309031202090604140102070807030507033e0f150306090603030a1e03110a0201150b03 70
    0x281c80c02092455203a9503d500615110100c40c10500031207903510250800f0303204410740c036507440020f90000704005031091020303845424100144401145040c01c02e866042100b0f1200d03101600c20000d0700d115031400c2140c126042d105800401c0e1500c0c035680c00030185262801c170035003040f0742045841c000c206c40c002110191600d41070690540d00e100c1c641a001001142c0000f00f9850134900340a08031a09584032000060180c2c543d480b040303840c03409940888c480c8603038040d40a0030500050080014084441c105048103004860303420391100d50b040e280007001e500889440d444034609200304550058007181c20f40c401c03107034880b8603801843c1c2e85100001d60140500805c85c9003e02903507542e198003c100d241b80000e0a803c0030351b060080d441459520444940303025500a40202d45142000012501c50b00700c0b581d2104200c00540c070a000e800c12001107100c0030540c441d0401e9043c1241c0344000e06501c03049400008003442051451040d00350b40da480709040c00000d000b042412501d181b9000c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 200776924 1250 200775674 200775721
    0xe18070e0601450510030b040603050708100e010c08010302090403030f02160c050607030512100b0a1e0f050405100207080d02071a0304020f0409030c05011b090e 71
    0x46651150700407103400c0b080760707484044007504414402c000101800d668101000c199128414540d5004041009120902c9102c2d00403c4500b030704281984240c4c004000c0c104010800329a0a9490f1592440d00340d150700188855003201100000144042c03080d400010005002400760020031000640094014840a03000f080140005020944243d03c60091041c40303076021512588141c8000c200701000703001c01c54860407240008201813034600300b9281001c4d4159100e5103440c0c0c086034940100c002c003a2001890301016500890421002c5002d080c0c011115030720081d0b62008000c03494030300c616a07071420080c80b18901c0301c581d007903502804840941d4010b407680000c480c10319034100e180001030b611030f201501035150000385495010401c0021200c20b040310000e114001c001c4840d05101c1520000e43c4400642046c0b0450b00300358001c400498024100808000d1300c6888150941d001c103280082056010f42042e0a102d810042200c041d00c420038030b03c0711a261a00d402c104501ca140481c10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 200778174 1250 200776924 200776949
    0xa142112040303021c0c30091a07050a080604140414030c01060e040c170a02010e0a0302100c05060705270a1203120609110702090702030f130e1807 65
    0x1d0600d03019404071442d484180000305c201600910368400103058040c0e405000610b4003a8400000c019140007203c1c0700d0003418a1910308004106100c001d00100d14200c9070b10f4000100b601240070b00b00002071003000c40f5251160394801c0f0060003000e51900400c004c0c4564a04404051904000380c1c006920a0f8000000b544c03204000620b60300e580950b9801b186a58240600440d02081c000300580c003652040d001c040065448680c04990409440c0703a04489a02c400c0020000d584074041c21612802c0141034908016225004600c400c0c103080c0c030100114400d00307011800c02008124607071788a9a00d01e4220701780a40f6072100d040e0981c0344a2110641c0103c01c00051484e55001c104100420041503605e08081d0103180240c115145030381c06003400c03440e000e00020711109600a40882903090300c0041c1c80e0880c00c0c0d080100f10030003d070180c02144428004c10300e08004d00e100600e40d5010082ca02110246070003000039040c04014400072811840100341030392442c000850000b510842032030b19 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 200779424 1250 200778174 200778181
    0x4090506040f061d0705040b01080f071b170304050d05040609060c06180b07020607020a02130e010605130b0301110901050324031b01020d080402030304140301020405030a142112 78
    0x144090991a000c10422210310318180104010009400041b60015181440740700c03142c3d0300540307000104076880c40100807480f0000d10014420320042d509604080704401d5444060348031040c5030310001840112001c4000709120030f001c0c040020440f070542c2c501e0164506410203100400b1030f6100d05c215000c0c0000300b80321104014054002c0e24032072826611f032440c50b040318201006070340c0c0d0a0321395001500134031000c20310044c400301c0c0341d55485d41c0180c900205910b00580100c020000c02c840e1403629542e4400c0802c030390f51012080c4071791003501200407820220000816003141e584039080d403104c100030415014680d800c08181d0b40d114030030030f0702c3e034000c140360513a80405030044003d02076040c00744104600000ca1210405a1103c1d402c3e42154500c41100400782c40f042010340b8080d60540c070900003003242e42c1d805036540480c56030207030016081966540209103000641038044907030502c9200c10340b142c00c10401500d5002114414085040c42240209080f94410700245880802e00e80000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 200780674 1250 200779424 200779433
    0x30405040e070803031003031106060315070e10050c1b0a090c021507051209010c0e060c120d0219050403030903150908130303021009030801091503200102010b04090506040f 76
    0x416004200031400e0302d5491038528540f510f07003d407d002c12008151241000414030600046641c402c42010b802400160702d1b03113101d6a40b4100c0181458100710030f00703017015000e8a40b031004481d0f000035a161107071100c030910300306420011101c8200d6100103011003441078955402c5221001c441300b01030001190002803800320f083c10314201c12012401280e20500060036070000041580ca5000035514026494500320f050a803840030303050b0800a180c6070340c482103920b44a001070084501c0c00d03040790940d008895070302c0205d805c03071840130382c04550201c6c804002c0c23003002211540c042e14501c1c100e8505420342d58041c00c864a98003001d040c0151b14000282900c0590b44140c02854014000b9922845502e0740c00c1d00780c8840780800c6006004000510418600070f00440c049240d150319181d5450382082c80740c0c00100310058140a404200c1c0c40b0010110300030410b00a03143c0200440e5105902500001909450342d00d07001c00e020318a0304c1c034800007042c008140d42d90400d620003e5203c1040540c00c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 200781924 1250 200780674 200780683
    0x4022b020c0304120512070206070308090c0406080a050105070206040b0c070303021e07060b03061302060d090f080d0605060406050406030b03070312020c040b1804081c06061d12030405040e 83
    0x1076030708903803000050110300068248403040000744100d04464000e0707040303142008117004201c40290030010601903280040d018441940e44106117038115806002c8003000a0290350007980491700c43c1d04607035007003001c2c4002070041e2640020140001c04040c00c0550b2403e641c201c3c01450003544138030102d002001c0511a804807200310103103110b10206690640340c070110b540d1203a50100c03400e600e04520742c141400c0120380e03e0300c0b400c1e183c00300e1411b00342c8503000d0000320b601146a0101090791500700800050101181c2c0d40040d0040460a4031030031b00e440513000b110403035006140f20b1781040c4000c10000d070b400402c40e000e4030200d00c1e001c6481d1802901080ca000d81ea508010b0807641040030b03040c0300c907034005a6094994000c40c1c090001a450344240078807406685001c42002c007030f01f0000f50104510310010011b0740c600b540c1c1003450356545a40d042c00ca40c0030ba0040c0c0001808440310821a244511403044040303002c8418100c001500382005603284580d209441c060341d160026122080d0f028070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 200783174 1250 200781924 200781937
    0x60605101b0305132606070e06090f030a1b08011a0d020f150a020c0103020313120c060f0203011d13140708030f0901020d0f0f0c0204230106030b04022b02 68
    0xc1c41c4400e80342c880441c4070010300e02c0b00e101754032914003101c070041c00d4a000401074003400b99600c03030203010f1050800f4801030f80e00c038044440e084014100c820985480c10070003180454040c64a0b0304101c1d050800645414820b68000a800c0c0e0502490001c40a407186000300300e0003044403495186c03079003071001c00c42440e042e1041c523521880e1005003450242c03c00000b090414260313400d60b04007064000064040b80400d684c04d5205803504c1000b00009070015011404843d081c2c20251011145503585200740c5203041c10f00000d054010004000c00b0403202c03050110030b0045c051a901c14070f408050f40050558004020300b52514070743c0040c0340d1480c1448100c000c0c040c200c058a64419610b89605010303032152202c24010312600f007012040b203103c3c5c1080300d541040c1350345401b40e0030451101112000f540004c1640c0c841d40e601c200084e082d20440c0d15601b25038000311018050340c50a03001401325250032903600d001d540104856284010a4000d0100041410700c1024142c1e0940c0a900028005c2c074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 200784424 1250 200783174 200783197
    0x305060a050d0b09060601031404020909070b040311010801090c051606060b130f060512040803060a09090b0702070605030c250f0b09061f09240603020403060605101b0305 75
    0x548441082c0700030400304074403561480e0b084520603180c2c08011800c8450126427a141d40010300302180041c50045c070180c0e040b0440750201c46c00e60352100b5246c0d00350362003544200c0d50740c6a203034806603565805c807891500420b04444200300c44491560302074000d21401130000c1104151050000030010140c0c4040301a01482d0036443d210351045580c0301008582d40907a4000c0035212900203003041c82201258080c2002d5540c880d0a5100c5580d000e40a420140010354490f08486011031050f1203840340c0b41c500c0d030045200b4a5141880c290107824200d040c0c00c6101008810410030070b2142e030311001c03541091603514800400b61175070321034040441401c3d64000d19002481c1d500c8420301810b021214041c1148005540f110b40719080c4d04401c0658104480e101600d440e0310402c6501515801004051012000c00e8860105507009400c803420540041c000309034041428014400c0a10a40d40030b001d05442c108040c01c0c5105d005809d54031043e803070291900c0e11807800b80802d071280f41514041d4040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 200785674 1250 200784424 200784439
    0xf0b06030109020a0311041d0609040201050a050d060509040c0e0a0501060e0d0204020409021617070f02012708010608010e0703150b012303010312021c050a09030519021005190305060a05 82
    0x1d41023056001c00083d0072184840d20320b503010681c1403420b13034006800303507078140c503924030b000c0341450162241d40100c1d41c100502952181d0000720b5407203002d0701038403591080464205c41400c000c007200c01c0c1c1c04084e2900c0d000510303080040c00300f20f4000790b1116610004990459902140e80f0014010b4131583e080300850038004074a8000200800303050038000c1c0e1051240c2d041001d0181a46005401400e4010300000300c0d034100d046c00741d4040e900401034901504146a0b00c0c200c0c14841c2e60b004a259405a0107580d918101042041c1c003c2c414820102c0240000d03008151030350b207610301c3e040c600714900d200b940e54858401103607a0080c48241c10403041103100003004000c640010880390000d02c826100d40511b6204501207910115904420340a0540405904101c46c4801c03641034102009400600041085c00b10100d0800c1192182e84c180c2c2c80004403481c581c80c4144030700006440020014841700740007840c09a440302c80c059180d0278032131a0014a90340c9240001d040783d807003a803209420000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 200786924 1250 200785674 200785679
    0xc0d09060c020c060a0e090a0221040b0702071811070203100603170309030a0c05010b06131502011b0c06110f03150a050d0b09010e06090304090f0b06030109020a031104 74
    0x3958000103071500e003a800f5100010004418415148a004c441600284030f00000c4400c5280040c4007a400400764a4010304000300d842c40b940742c8211000c01c0000c0384008104000c200001c017401241c0c041101d1003c2c040c0705140007000400c140481e00c0d01e115298a90803c981180e40141c01c3e0f580c0c80b0f8008080f02da6010001030840000c00712070000b80c3d540e00340550300d542ca41400300102d900503501e0300c004515110b0420390456000b0135810f8202c1c0c0c0c41d525804500269907802d0054000c440740301e4240c0e400d4a00c0c0a0310380105c6808140600e041d64104a40908108000070501d1007604181c00d000644454500e0100300404102a00d01e20080011a00014404125001e148200802000e084802c0c011000b0024a82514071a450b4007000a030074413400548480308541d0050781580c0042040c8111140d058180300082b180d098081e80089030410080c00a07019820340c0f4070f01503104020f460b66213000b141c010311050040d4900180c0000340c401601d8400d50201d804218400101c2c1d44039034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 200788174 1250 200786924 200786933
    0x1509060702030a3306050f060d090602040906080609161703040306150e1803040618030501050406021e09010806150d0615020d020309060301050108280c1106040f0b0c0d09 75
    0x49100307040e0480016101c02c0b140f50f107580f1744074900540c0d10051070a01c10504003820003885a00144a9140041d100d4010500150043c005400549804400822800d0500ca000c42c68040c00503c1d42070f09900c40c1d0340407020300d520132600f40140d0b0300405c100a00c0614844481c3d00d113105035403004020f07034980301300048041c10404102094442d100d071041c10680750b2015140110398001000340241c0c004000400c03103503008003440c0c901c5d00304c10707910064410781e20b0312841d085031421141514119000501c10b80e02c1c000060010100d0400200454100090600000c288400060449000c3c0700e1030200e441c0d25460700401e981300422102e106000c801c0d10b4254000303030918111002d00151280191515040b030012003034409104019100b50709681c038100045038038880141c101036104048a20701681c0d03810085644914540b21540031940310f294040060414142480d07911103174104c03400740400501142002c030b01082c0c10400103449615400b4040d4103521401259101041c586000740c000c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 200789424 1250 200788174 200788223
    0x9120705030d0e0303070207060f091d011a07081c0f05150f04060b18060c0a080406091401020c0906011206030c0513140403120b28051509060702030a 66
    0x15542c14020302c00f86030020407807507a80c0401d0b9821000740c5c1008000344161885050030f40c104c0c1c0c00c1407501044e92a900c545a40070075088004029003410f05d00010300041c2140180007007105600303041180b0f0002c66480e00c0146024480040020032403a100702c1d5104d02c4140c10185107c0c581c10420041402c0c007450b010301100392070312050301840c030080402c0c06525240c45441e0440d00c3c09400d843ca00a100b00c046241b01d800200a01e500c0348041c4010104000c08000c46011984200040b0365624105034020b03210302c0403075000d801d1900c2d44920016169a0118900078908410385002100341c84040042e581c03403000212148240e40342c041e002080c0283c08002e00102c0710300395124007409a0409244094a0521f0a9200c692a114000c5000030b4403420a021643e0103151002801c035092070b0001d101c04c0741903003140b5001800c150108048000c90342c0700500802c822074806910080d0104001e4103800b030020003e20508004c01e4075419900d0500001021961281440c1100ca805019813001c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 200790674 1250 200789424 200789437
    0xe010203070e01030203130609020a080f071e1a031b210a02040e0402010804081c0207021036170a0c0e01030803060d062009010f080c0f030912070503 66
    0x1e503010b60102c40303075000b4400c4901815011600048040030f0707032200c5019000703600f0126084030700b10300c1c00a10424240400310340b09610308042d01c031040c0f40811202401290400040c030b4118000c4e410402888012580c100e0f428040200390b45a40d01d03080c0c40c1c152500c51002c42e1110802c000740c2d86240d5545030404903078440400c441c800c50b81c0c9480040108a00030f43c054820741401660200d400740d8041c000480e4014410324040c0d00c1d200f41003207441c0f084101d07a800050b0484c2c020444004501d00402c00d010041603d20341800ca00700c035442100340c441551618520502d03518410743d41c0841500104c00050b18100b4041041d002614241ca03545001c8580150b841583d00040800d0324a441960306049a41181d100c40c00d503203c40080011428602601700c540d42d54895070348640c8143d44ea400f68100098103041c1d0b4454484800144c03c401c03a20580034100700d07208081109101c43da00a5555882c44051640e07140e80d203044481e40341c00c02074400200e0701500030610b034003001000401002d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 200791924 1250 200790674 200790677
    0xc070f0b190608060a180c062a0302100216060614010305010f060f03020912011b02071707090f020705030409051b0304020907030b0a05151e042103020c040e01020307 73
    0x1c80e900c03051004580c81c0e40a150314a40040c0d0114000b0500c9070046da00e204c1c45002c0f607000c4071615503940c8200c039100307030300c0400800c0301e2501c034446148111413101702c500070094522600c0c80c0296402525981c9010141c2045c641c04100c120001c00b2030802043c040d54407600801100340c8134100b03503030281c964040c414006403e003000031540c8101c40001000702e40e4161a045403000b05044150040e4100c94121500244040cbc440b2007014400d0040180c00070030032819101018150340c0003820142150071903070580001ea0700340f4502e141c3c009180c10071985410fa0002d8150303004034100020f4800c240028040b07220125010414001030b500c6280180e46083c0608034451881c043d01040f8001150043e51003030104000445690198200c4e030380400008000040207600e41d80011101284800d036420f0300780c3d0115005000360400401c1e180d0b0500d27110340640c145803500e500001c0361445050f008500403410603e000805000b08210031440e00c0040060007458403007280d0303c0c000c2d001242d0f03420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 200793174 1250 200791924 200791951
    0x1508010f09020c03250f060906110a140306040204080d020d0306050906010804080c0106150c020316080c12100c030e0610290f07050705180601170c070f0b 68
    0x14442114070840e11203010440c041c5003014410141105000305085c5500e0045410440500006004030380034035495119210000e0943c0302410040d017192005251905109410068625a2604143d001107544020f06505503a03907035078804100030b4090343d0300140b030a2141700800640c1540126006500c86900d0f42d003004110f07030f07030303000c0107540d500680d0ba460103d40c0480210300881d44100040c0312021040c0d00204a503555603521040810045807003c0c002100390034444218541403000341030004c40400d00342074240c00c0c00952a00e841181c80d200e0302c19101c0540548600c0c005103c2e400c1035801c1401d00f0800003d1300710000d005021040802149800b540c800900640d40d221501002d4401b0f0003e5000d80c3c03598511003501d40b08050311040c1c44203906020200c0b00c413403a0001040382c82c0c40f540142c00003528000502154950b00d03410451041c0c0b0303000c204461668089a22800a0700c03500c0340c0607070343d294810715540b14410b64034054200d2241c183d1880512101c4000b0302d008264000200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 200794424 1250 200793174 200793179
    0x170607020a031d0409020d122c040b1206040f060e010203090c270114090108061e040c05030f0a0b090c1c030311030108060a050109140402090702071508010f 69
    0x40780c66440840000300480c2481c00224149000c0a240e003203900005071001500c0c0000d0740010f00840b00b0640700721102100e1801d200c0304d09511440c0b109901e018510f680300f807081801d0004220510b0200301602076aa03036480559596a1150400d2804034050151926814681480c0e0f803024a08030059604604203644000061130500c00c4a21075178410028044080e60b94082100b480c01c842d6003600c6040c048941c0301d00304034010801900170304c40028a51005c800c10300c24400e01a105071312801041e0404000c0247c0c03400c003011212001c4602c0300c1419030a5a4601d0940c0c2c440e0203d40200c0c1e054800d00c3c0301c040140306c000803107034981d03409007820500a0ba103d0800982e58964110f429401140d40340d14a0303000001c000350004418820309010400c03801c0c9550b4480e445d00268080c042c20342c071000074490000510306c5103d015008182061180c110001c8210100d40700c0688001c1c003680ca41000200000d200740303e92000b07820400ea25000d040321002c1c0c000c0582e0400e0240c80419114000b00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 200795674 1250 200794424 200794427
    0x170406060e0f041211071707090e010603080a0c02060d050c0a08061509090411090705070309091107080d061a0c16030c0e0a0603050106060809010f06031707021801170607 75
    0x46501c25640a040b1400b0850807240480345c8404c00d00010081e8483c130000441e070300380c42c213a01400d8421240000c1075680e1418070200103895201c0c541b40116458100d0500c0800ca0503400c41e18400e01c030341400700d0f1080c07141c40868281e06ca08880070303503000d1616081c4912410b042008200c4c1c0c3d0000e60320021942c0360343c0304011240506884d06403c0c05810040080503003065040142c0c00b40c010b02c44840408154000f0039401101120643c0010714009066410035400c00226406081c40340300400002204e0210340c40d4034032070064013610b000c0c0003148041000c0440c0c0c0000300078040c016032102d4940c007101541c1c4460b800403105d5024030701907140c0c43e070540310f101800d0000710303034100500c44812441d041c050312160070003804480f07907907131608004030200d44240602d03c01441c669903546080e142c050a09030850300304480030100319040c68070800110340280b100d1504146100c802e19560340321440000c00044400804c95050b2008000014690081c140500080b59400054880a40e0748850 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 200796924 1250 200795674 200795701
    0xf09010b090a0b0d06180524061c02041515020613060504031103190306150c080d0f060b04030b060114040306051009140a0e0307030c020d03170406060e 67
    0x203010303402842407000a200c8012940210003aa500540032801340c42e92170b103131081039840c201441d00041d000c0d0400c42c0300b00b000411040c583e181071404180d50110407500301080803000540400c0c4150000c0803c000c0031035609042504584d030051003040141240c20400350b188030244038042d03000d01250102d0743d03840d0020880320b20078029903555142c81d9915544140041001610503010040000c0300e036522108104010103082c030070750302403a070307070500880d002426120b80f90070900019004201c541c6030b4a40141c1ea0b08511f0b5030060701107844901c25850361000384050844414400e05141001600c0d0344c4820040c010f03039000e8582e000c100c1d07071164019150080c0d107601c2c05c0101c8004001c10000b01d821640700a40201040d0341e5517075483d07520030080d42501d10525800d4052142001400120b02903880740700b86404108025504101203502c001c0d16038942850080d0107000c03240220001c161089900840e4141380100303000c400e05041c14110000c0019004070f4070b4401242c000b04034640310108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 200798174 1250 200796924 200796941
    0x31f060c031b060912050319110a0809010b0a06170a090816020409080a0806030705090106140d1d0a030e0402040b2502040f1e0207030e1002150f0f0901 67
    0x126504501ca54001000c0d442015038401641c1c004da840d00d03104001040c400300b600c01701c0c4a55a502e80c490500c031a4050b910013041d15840c540c2d0789401190000c1c80068400c2e90000740090820500640c0e82286450140009400203907002050f030401184243d0405903049200100b589000c1f855552640b454084a080076006090800140005002c0303048140300880d0252020300080743c010400d80c1d4041c0340c3e402014018000c04e03c10b00400c201400c040002c0001400100c0d1543c109500d80bd40143c00040001c2c88400f00000005281c4041300c00c2d074006900350703620044c3c10b00300e01d89008091611810400350403030010751ba000307200d4a03502d018001e84090341c2003c0c03103483c0b500c1c005110500386141c9441840c0ca030505460121b4015036540e21888d4040d01d214a4003040d0003155182c00001a0792140781c0f07252881c03060002e0f0000c2076010030702002c81001a142c1403003c905a0b9000c1e0700d0401903244034000e005414007003101c07100c0b060302450301401c810b030666800d07522203040311401e0b50b0110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 200799424 1250 200798174 200798177
    0x50306090a061505010912030e03010606080108010e0a02011202070f050a030c0b090f0705121501030602030a0b041a15070f05030a030e010b010c03030c05070c0305010504140d170406020f031f060c03 87
    0x20021f00c0300d00800390034100058400d0404501c41409030780880c1c01c0d1039076a403244c0c01041094004110034402070003006441000f0700094000b03611541c2c000b802e04c405410034000c02d982d004c01c500c42000025031075042203a130400120360145445241c0182078800d2648200c43d0b50180344080b404036200000c000c400240000301070074482c0e040000b030000341e2100c483d82140341c1c0326860764564245144040030b8061402030780056680c2c94100c2568040d104407040740303805a49454003003948403c19080200316100103c603541c443c03803502007190f0342d80e004403180a09000e005643c5d28081000000080c0b6043d60035403020b10044155610040c200ca003010782480c00314030790394a1400001e12913849142c0c114180d08080d0f052803044d8451001a1300140c0040f11240e40d120248424000c2a120f2a0202c0c09010014489928046001006130010803c20615804180b000c2820440d4076010b4400c0e56814403183d64683c505614808601005032480f21541d010850011414a1080d100d41080702d415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 200800674 1250 200799424 200799437
    0xb22030203030412030609021308070807060c020f040605100c020307061419141b060c04080a0b060319054c02040302150301061205040312050709050306090a06150501 73
    0x55071513507a00038200808050801d035441c100446d11000038809000000096484041d80030b0520800a10305401504900800c0e4003003101004850b40c4080304120b12681500c100d9804044400810082c010540241c1d03801b400320403512944503800301162000038000c40c1150b0807140c1d10034050796032a0203400e200c1a41c0382e0421000c03000c40300078055068110154034008819500036415003000c0e40001c1184421a4003103240622503a508008441c0c00c0018004c3d00e6141c24580786040341e4920030500010440341989001655903641800440c500700c03450b044601a2045a142c0b080e01c3e00c0e0071800801ca216140401c214000704521a07281e04000c01080804003440250150304036095420910008180c00304400310060300c1d00032000031514591604035881c0d506002d005840c0d44452034031074000b1840c10041001007a8441620f00400090010005950b1110042115070790480e4105a4241c07180f042030095284d00024045101070103070fa000c1010107010759180c0401681846428000f506 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 200801924 1250 200800674 200800681
    0x3080415051b0a0908060a1a0603060a180605150405030d020d0503130c03020a0b0c0715090302060a0e0d0809040c0504051807020a0605150f010c0f0303150b070b2203020303 76
    0x50000003071180f0b140c5810000c40e5266074140d140e1822404840380340000b9150b00030b0100e43c00c054103e046020300c1c1103442500354645000451880e04541c0716400d8000b6030b001640f01016101d51103c80034001c040c1024070214a0008030040396402486005d029128842d1584000752022610051525903035941911f1a101c0102c00103050b68011003e44640d01580c0d40000180d5450f00840000c0c452124003503191044189043d0a000880e4003034121152119404a141c80d0f00035844e505907581154211f459030082c12044401800190b2000c1c3c100103450b8900090102600103021071040403541400484400503080f1014040c030b2003556080803c42507002800d01f0035020550b40000329204945440300c054407410141c800a503444a0902040111031000f0300341034044540c400409c1c00d1400d41c00100e9500c4030110b0745034450250802d0b035101c000c25110003a1540c1200140390b881040d58407241203040441070904150303584615074402524004203c1c0319170300540d10f0b081c0c1680155007141c0d07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 200803174 1250 200801924 200801971
    0x1707051e032206050403021c0f140708070c0302030c04060518060f03070905040b0c0a080f04050709060f170105100e150a0b0a08010902090f010e0301180308041505 72
    0x108064001d405154002d40e040c1c4094105182850311a8061440416241800c0c280603007450500090716404c40c880c00c440340c0039203402007140155507055160003c200312483c0c080451900545a000b01a500c00107203001c240441d110448040d0390003241540d1132030860504001c03c640103480b82d50b8105038035640c1c05003000d03d01c060030b50740300c0300c064280f00720f00c4040d00000c1d00304001c64010658956407801400140588071861b6a402451b8071100c0e890159100005010500010300380d40b0755200a000003002c12400348541d45c0144409041032025580303560041110540314000d01003505990b8001d01c40701c200501900e03014032038544685442504000c0c44484001c2c00501c0c91060b0403c00804458940b00c1c401400003c0c4404850143c541004990003001154103900822a0500500c4003c0080c0e45803200100d0810f801d0034285c41e92504100805d015018440c0c040c054110941d21600905030044401d41c840e03446001c401d064020102c650000302c030002c2d10b040440c000b25001154402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 200804424 1250 200803174 200803177
    0x907061d040513080705100506012a020a0806180c1504050d030905130c02010b120601050105070213020f1b0303090607111c0f090e0405030f0a18061707051e 69
    0x1841c0d4040c0f098011a4980d00030750b601c0340c5011038896109031000c20050030326104041d0444000d1a1174003001c840010307907070050380585000001c040ba907460703650215030750b01c0c42d03880081460100751000352a1050309641c6ca00d0348580001d0242c06080b071444c0303040c9450712030110400d03603030603401c0e0a25041105010305041c0308a01242440b44c51900841c1c6560703461002e8007e00703090b800114540c2d003d00c3c402030a4a0071041c0143c001c2c0c6400c1d000900010020030524103440084c60142d13154102400003401c2009002c1041446910002d00c4a0722181e00e0f100030040d40050443c6443c0f100b030a40c185603035a00c0101d030f065440e50842d0340421150f070300c250000048556103800300d8004a80e603041085800381f40703958140120360ba407071070340c408582c02c218035a004040703181d54442c0700d24060319295103031b01c20000300d08901000060149603480c0280e001c1482c400c44510701504450711020b018115030386504c44480c00c1e850711310028680c14451402c580c6c0003d46401c29081d1414049100c5425 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 200805674 1250 200804424 200804431
    0xc060906030106030e120408010b0f01030905060c03071404080601080c01050a050405060703050408031813060f0e07021603030e04050f010501020c0d0c08012c0304060f12060f0305060907061d0405 86
    0x3c6000d0008103a4100406c10f0140000d030500100004140050400f005003412284215a0505040c031079194003141002c00c04640c0a1400090304c0d0780c039034403100202c070b00c84c0c092600b07040d0221000c28003144401c80010b03214162450700c0d044881c0e4054100055625000c1d5038040740c0014020442800a4203001020b040000c1c03090400030708094075030700b00d02c2c20754000072201c92101c00e4900380c410a80c81c05101c01c06c2141d90708042041604c1c1003540c0c41200d51524020710380300000c5400030a003080d10810001c81080d00c000c00e07800820b52240b9004200c00890030000d0302c15400d01c40450342e40c04002c4270150407070341c050300101442000d140c2803260a51513840d069410250300c000c00500c001d07017806072140d00511202005100d441d100769407904004c662080440907401400300f1301510f80c01c01c0d205488510f241c00c010740011700910340c1c00058111500001403450031640c0020070010001030301d900810744142500c1e0000c1c0c4811045038460380940c0655100f406450020020781010303805142c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 200806924 1250 200805674 200805701
    0x1080109150911040516030605040605010207090506060909010e15060301120f020d080a0302070309090b0d03120e031602031905070512150114011101090b010b0c0a0b0411030c06090603010603 84
    0x81d5945044002030448801b1202c048011418071010104580c2c14802d503400b40c402103c04010107401c0c240001d580d0401030140303850312a5240d002c0380060b600d038010b4480035070000300014050360b122100e00301c60800966807107400c405c0440c0d814020389004007d80e8140c0716a010305080c82e80260301d60303604062442009036001031410840102080c1c0080041004541d0354601680e118400d01c1c0041c40c0700c9840d0f0202003a140f0345085400140d6074450079034402c80d09842c10415101d040040a00200b040305419403c2d0712000402c0390080b441141c8d03207044580214207440703a02c020500c400040d082c12880047c01904503280c18005490320540550400e01c49104641052000102100443c4004c0c0c00034403030003986441201056901040d180580409040240003008643e560301d1902c0e9010702424001000104a180381c540c01005080720941e00040b90300400e042034200261201803110489010b4059201c00840311706054007111f540000c05041c242c50343c0e00e414070440042120340c6101d074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 200808174 1250 200806924 200806943
    0x50303030604020d1803200a0b0a0b030f030d0b040b090702060c0c030d06170d0207080a0f0f0605100906080a0b040210030b090702031306110a15180b040b010801091509 74
    0xc00607984904174800d10320036105c40303000703154160103500f5034003114035030100503070169000b000000e206c008541e400255551012a4665009000a05100c041c5c12814141c1c4008101000113001c50f4001602401050f1001c11a81d0440028002c1080c1c04440540c00f5900071001726298101540c0100f00300380c07006094070308044d15090000700352190383e4041c0c5c512440e801003199480b00c040c01180032142444c0004c00505180c105550b031030740d1200b000a070a103092103a043e028070064003840710052391701100410131444d09072520814403045d0700425464514080f0007181000380041c0c1082441d030420411045907070f496003085841d41301c880d40d070802c05843d500140b5043d12864000c902485503030700a5074036140440d55040c1c011800d50b020f202044151240803a10b22408103400e00c074150803c0c183ca071650480e9440d40064064000100704200c4040417040074030118a00d580c0c009c034400c0d400808581d0344c6001031401c0c8c4415a101030101d00502441a0546101e07a00080640e0701c84c60080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 200809424 1250 200808174 200808191
    0x2040506070807051002040e0f090a2f011d120106030c0608091606050405040930020f061b0307020c0607080304060e06010f090213090207060b01140301050303030604020d 75
    0x8a0035046441c040326040c4012a842c4104031302400200072001001008508203854400420740e4a20040c02440301d54403000042076918001388a04c0f05150b8100703030b00d00014601c044203c5410785d031001c4404500700a4200c1045150702c039040c00041c140901c06403001030070918040213002604149451500e40d42c50400100003810f84081d2001013032192240140c51401854080c10180d0805451603c19902c00040c0101d9821000b0b542c00d544099400096440e2245090703401c4040e081414503410042c012400580c0307882d004041c0d07881d242942035803000b68580c048243e64403015541100c11007082c40d0000441208800a10351240340d502c1110302d0083d9003001710b00154460142951190400000c0109012180c02800b25001080c002481150b15044545c2c0300306915000d44074040b6000100054420107105d001c001502c10034408656803049440c142e4010201045c000d4082034141c00424a2092050190f03812183c000d0041c62a5990361401c0000a5011078422142d284d640e03040e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 200810674 1250 200809424 200809429
    0x20d060f060e2b080702040b150901090b041a090604120312050f19051803040e180a0c15090b0c010603060e0316140c120601090b0a060f12020405 64
    0xa010040180c0d8452009610602c0148003840d008a08004005014a900e1004503203129900044041d0000348090702e50040c1d10000d0041c04890340059800307da5142d0481002d40018001c140320182600d030020426a9084105c04500580c80307003180d170711840c28680d2920918100144611100100040d10749611140e00d58585008660281d0000300340140315002c0c43d0380391007031540149440501c1005843c1c440e13141d015000c0c821004904840e00d030b03c081a510307034181056101441e085401e072601c40f5110b40c000081d061044441c0d032481c0070401c00c01440641d01203070300c40002e0f401c00d950140b00c5041c1900b0056a01006400d8000c000c0003c2002030301200c10006031400680120001c80c4c8140786080039002c2d00d914a07040f4002e03400400402026003104503245c2c0c0d10942c0280c908598610402c03c2078100f8610002d03887c2c20000224034810034400118031103058030b9507080100040342d80348041c81016100f40c01202c0105001907100c000c00c5010b01d980e110070741043e1070f0141c50661100c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 200811924 1250 200810674 200810699
    0x904060618020901030f0203091009060b03070314010f0902030307030f02190807060e010c0905122508010501060c08120a270308010e090c01140c031b10110409020d06 73
    0x40c40700d1060780c04621011030f0b40c1c0c140070f003406080f21202c003503055061016440d9240c1005804000c90140e841c0c500038104252500010041680102940d003c2a901e0509041022203010f54039959460a00d441504d107006104510b030164000d4001d40c01c00000356400c2d01c541d00501001415442401800034040c04007100505110703100c0d6240c107888610a01d0400700780c50600d00114403603418854181292a4000c00300411904100d860140c1c140b2030581e0103040101c15485001582020108041c4042400841d801144e080e60003c00c01680c1e5003804940706d10074140f004204884c10052008154614901590003298480300010300d10071500085145541c2a0b02004110940308400c8050580001c5c2160052500c504031102d1490103a02d03003615885c0311884181030000c85da24058040b8403150555015200d084105c0b075072103031380c4000001040116244180d49100f0741302d40c16180819030003407034042200c0100180c101070902610344048e405c10007101001503520070700040e68444115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 200813174 1250 200811924 200811959
    0x108090f07030f110901060c060e0616030b04140a050405100605100503180a0303050117070302030a0605040503040b160c05010302130302040b0d0501050a0605010f050f0301271406040e0a02030c09040606 89
    0x300c4103860710f001c6103027010550360040c0c000c100c10380188080100841550a0315140090749250015400b10401c002900408410640a8000c580c0d18100241041c456004600a0740214111400180810a4030090784c42c0c500a11fa046000f0000300c14a40340a040510381105001c0018208035905015051502103954002d500294035080100b02d8441412140010300e603504015000990460b00441e9035040c034aa0010701c8595100001001d0200130301c161409442c64800729a030750800c02d0190400b0048500701955514420000018250700900c211404500348520700107480745580c003000018841c3e040415000f14910304040c0020b00d0a20503a4894050f250380000c000b81014001400b20030301d8210303181404030800c50b17041050140d5096074119102c1c1d4010b00042e9855800307485000c1400f03000522146e0800b0780c54805000c3ea000f2851060380c06480401c01a9030b103001c0903948418425000c1d4050b00209522415070829034007042c0c1c000c0c01070313001145455584c2c114640010b00030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 200814424 1250 200813174 200813177
    0x5040b041b03090c0f0b040e1b04031a0a230702010b040f02130b28090512010506090f1306020705160f030b01080a1e0f08040f050108090f07030f11090106 68
    0x9030300c43c41c1003205100103c406400b81d850013517601420048607401e980301ea40100300c01050140c1c001440c00b00b00c0402c03070102c4031070705204030744071541ca10b8010916001c104000324407180000000ba50744640740300f610700380071030540401d40c0f50f001c0d40310410243c0e0015181c80708554a80750841910345941c0a210400c00c030801005a541c441c00384600e0f001203103a048031113040c1c010008080300100e80501d0440a824103c0e1428070207100240584401880b50310041c1c001c0351507000d032440c105040d488036100355015a00c00c6200c0d92400c40d8200d8030181203440e45145604103000c100810b90583c0179100e2140302d0812103c041c030f010350880c07040d403013154403469030760320002424800c004940c06124010b200c1c00000b0040a011565801c44910b540c0c1100250350b030b403042500090004107140d901000d5000381403035582d9501c41c11090401ea0a81c010280130032041d1012030351104000074070080d0078030200058911107045649010181c5c010b158113840c95505051042002da955202581c002e007a103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 200815674 1250 200814424 200814431
    0x109030b150405011703071b05090f0702010f2d02090d05070f06030513020103050402010c02040e03041a07020d06090f06050a060314032701051b010b01180b0405040b041b03 76
    0x3441c100010340300140c020810400d4402c0410342540800010f0780c0342d0b140c0c07250f0601070b0040003400070303501820b490f40025402070080701070214161425440d1801016107600901070007114241e00415251920700804135000311301201c86000702080f0502406210240c2c0161901d040e507000250703001945401951140c110711000c20822011f5082c6200615039414140410714241400445d0300c990180c000e03062640b0340c0b0005007168814280c413445264002c1c401c0202862400e000355603900980500c10300d005000c580b0041c0788540d041600d4905900500310100003105668a41c00380401d41c0044420701c2c03000100000043c12801fa01d4441c020090001820604d1400c06400c484415a1070389101e070001c10610303503003010170b005050b224606580a61041ca5034000103c501d80310340328410741c0c420344414400c110001c0c1904080444113090381c400708072105220401798050b02038492503000003000c00c42003100e81082e130031000581c0c5008100288000240542a5030804590000d800007a907 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 200816924 1250 200815674 200815711
    0x2010f0e07060315061209030903020904031101050603150c0c0a02060406080402153a0903091d010e070305070203040306091506090e0703110307050411040602010c0305240109030b 79
    0xf407503c10350260181201903116100e241c03c2000d809000f42d2800d2014450700d0385003072014140980502001158060709041c00c40c0340c50305004000f15031034181c0c4e859a500b81400700c0c0e010f182c0041c0f001d41c6061100d0b05107a940d06c40342c841401d99441882c001d20b0a0240a603440003582d5448040c200420280d182c04c0028a410300c10044000d039000e104882110051054200b600307400100b011080007084100450020300c15407812801c010304000d410030b9800c2900c1c0e03004250b804140c0c0d40407164462421032040322810105d072b80030306090003008031404001d0009042c06100c1e40025400840d5401500d1600b5169262201036580039101600c40070351030381c0350007010600d61103040c00402888108010014151020340d49039021440b0107006604c40181d81c28050703030180004801018000c0c000c1004010403600303502035030460b124510165280041d01a995400303030040c50301c640d80580e42d0100070f150501213082d2041c0c0c40d0744820704100c1a00004800038a0610901e8003540d0800c2c01c0c5030381d010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 200818174 1250 200816924 200816927
    0xc13060e18060705160b0406090803011511010203090a2a03060507110f0613030509031606110a170c250f06020a0f14120d05100e070e0105030702010f0e0706 69
    0x283c103100410104101003515100745400c0440415030084c0300d19003c0d199814108003a0104580161522070000000144035000c0c2c4800c200c0074000d81c4031030600f00d440420031400c03070004844140c440e81020b440c240025004102d1041840030b220b20901005098171034020b4503142d590801c07518941e0302c1c000d01c8070f51500b2032015442c000c20b07100240800c4080711101c6803107190103400c860302408000c10881c201402a0190b1349900809011511440d4181102c88110707980c07845004017140014065960782040880e40c40481d44e04410b210103004070040308031410b5486000d00d40c0003802405035282a454209804118810f40c50704842e041e2414081a001d4004d8264080419540100b0004002607480c0c5030b64111150040d19510003034540d69032040c00c02240e50039403442d5520005440304420400d522481c0164181e01c00e003411079498501d0360a5020040d1014804103482a01e940d14540c400ca0042d0350150661002080100d003a02502c07055902030b0030b4040003034001032014071016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 200819424 1250 200818174 200818183
    0x302010609061202030a030e030c1203030f07080f1611030d3e0703021207050d0e0d02031906021e07120503010e01090906110307210b030c13060e18 65
    0x101030300080d543c0062200c1c3e0000740e941641d184c005090002c408460042540e06022007040d10744007501c00680041d5007140a0307240d0f801151145040408440459071941c0f1404002e03100700304012080207191210707400c500ca40c015840e90300040003688854060040405c2c80941110281c0d100045800d0900650b8248449103000034080c014101008800c1a0614a82030089006c070300216141d50b8015030808138100300004003e210081e000281020400c040015640d030080615a82c81e055810000104100e8031002407001c0c0d40b42d4030a001c1003075030050b090303011030055210b808010701d400d10201c880c02c4002c1c26a58074000220380031403030740103101e421055406414128a8140d1440d0305040300d45814a8040c06600c003030694400e032800070421154400c816800212400d191a450a03040080c0358400100c1004e00380310a150304800c940d00c403030017180341e04d0740000d024010f0b03951202c043c054210080910f80d030007148c030f030000001c0403455101941e0040860b02c016a402000300138101e40790 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 200820674 1250 200819424 200819429
    0xd02250605010e100909080415051803010c0c0308060d05010f02070201030f050f0103080d0f060f080d09030b0109020904060b0403030503101205070320031218041e020307050f07030201060906 84
    0x540e4400e0f0204940084120900410356600402c000380e0708480d8200303001d6038042c079040074080c00050782c02c0c2122103820501400e4035100748025009844140710525080ea89180c100c04086904002c41100080c0a410003650214010300003600c10030090f12440e0079191f441058560303480e40051504290b5034103006041014081c26003d0145080000c1c120814050500c0b01500b14403010a44505201103504901c0c1901216881408090b0b224800d003000f1013503a1040e01c1c981e21560501c01c02c00d50095101004036504000102810b07031030702c0380361000381d03000e182041c1d4450f5032150042142903c4002500141d4002ea40711500d0340b030701c0b0042c565004001c0e0445044a424903042200140d40040c03003605499005c038484000d03c84001e4429894440c460202d44e1500803400307880040c0c01040d0241c9802c8541039903550002c0041d600b03020482d814100e80e135500c4041d1400e4250560000d4008603042001d83c5030162400c0303001403054034250009403044005035140d0f07000b0481c1d0440e074009c5501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 200821924 1250 200820674 200820689
    0xf06090605040501050901050111150906071209050c09070909022101050312030703151706040c091118010203040503060c03010306051008100b1c03090e0f07090b0d0225060501 77
    0xf1650410380000c049000501c5201d0400500105000c0c0302c0b00c0500014108409009021882e400c00a103070743d850303030421602040000c1121507140c200d00711174010703440c00c150018013600c211200e64040c00742d2110000c00c00c0092007500f040000b0b1a0710144010201c014011541c0e002e03020602c85500c2040b40103901c403500c654040c6915a52070300070401280d80004140c1000265103048a100c8070708030005070301100c01040d006036142c07407511000c05c415120720710903030076034100d55104c1003007904441a00c0c0c0c0100150100f40b0031000c200d5132142e6460581201401144c0c02c1650301c0d80040d140c00c50868000a4003034020004008200d40350103070642002c3e88043c5800381c1410440e02c81e40e505644000030700400e031951210802911002481c0e42c807071507210b83c90007400c9400e00740984a0403003403140010746081d0000003201440e00813101741c0140000d0351072580311440e06118807699000b9040c1e0200007582000b400c1ca0340c1c14001d01d0b50426030fa416040d54401d03845402c01900700c0e10140e0082c5c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 200823174 1250 200821924 200821931
    0x703080903060115170703090c0e061305011a1b0601150e0f06030a0203040c0f08030a11070302090606030a0b030a0f02241b01020c01022107170103170d0f0609060504 73
    0x500359030086045c40c0d2244454005200300d50b180070b4202c01130824070740d0180c0480e0551401244660040045d03611031b00d815210145000d041074080c0007281c2092283c0300c0d2046036107000e40941e60020004095454090b0155070721414102c3c505d41c185402a8841452021088140400346400580c4402c4038030085611001019090000c1905840300800c4d841c10140d0000010742004100a04079000d40541d0800000d12034890165503625803007d20350401007220600f00003040c0740000342c0c49007500c2d03001e01b094856888020602001c0d07000030b048400000e454030700d000d403039817001c001d1455554001e0289205003049070042c040111818207a60350449600c04d12466a1101641190054440382c1001000c815407441c0320f80c02409447c9807620302c0d50000542400d403070580e17018101000700f040d05006480d26440303030a4803008034031a501d20305580380074010000b08072003200d1a840c103118090b00b549010040e040520440d0396841251314038555610301840365816510402c070141c4429101007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 200824424 1250 200823174 200823209
    0xf0304061d030a0b0709060e0f0d030507050a1a010e0906070e15040306060308030a0509030c1005060a0e04030f090f03030203040b0f1303060902090a05060609040c02070807030809030601 82
    0x204104908441c080000019841030300540e00c0400c9031030211904003441800900b00103100070031504880c800d482c0080d07031390754001c10646046a82e142440358014014404c451140d541610f807508042820b03aa203000317100d280004280350307107801c040c00a07941000340c1c41581010011401108064100c0006621020800461035089082185110b50840d503180b118000d110f107400c4584507981004128508015000080010200c0550300a10050340c06101710307514800e03283d990303004060b43e00301260302a54804011f08a540d22040d000000603080840040d01c5944240400109440460005207494000308500f54008501e401421032082390050303403451601c00030359a000314003c1b650220000204100302c070390604120b41c804504000888440d560f0307400c0ac500141100c00d016409001a0000909801524415140b00d18001000ca9080c56a0a0140402043c18030039179401d6202d12500800c061201304a82c01c0154402c0100329600c0c1c07042c5051506021044c0d004100d08403e8100f02e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 200825674 1250 200824424 200824427
    0xe07050403110f130c1206151709070e0708070207050102071d18010e070305060f101511100c0219170f0918010816030c06050c010b0a08010c020f030406 67
    0x8912100f22100f4070500c0c908400104101c0143c101028010324280700340b0102d54008100380704105541404001c00c6907104444c400f031564841c800400181d5204486105410b42000c494000075080100c3d903a8035140c41040217203003070641d41e40001c101d10604100881e58100403200140c2020700c0a4101c051a00c444c20006000300c0041203400440900011050400e0b00825000500307080002e010241400000343e03100c0003c2e020a5940d802504001151240c00c100228007400c1c0704035020040526140101a42005180c40d441c01c10500e180b006040b00c208102d00c0324004810f210001c0c0c40c0e003201034080e2904005c00708110190200c0100b8002084d030315201c0e0008864a05900c0d0342d1a0008480e4095900c00d003114658002050b030000400700c15042030b40c0e81070340e2500301100c400440011004807100482d12004203003252040c405d01106100788054000e4100034070000c103680c40400d00040c0d040c0f4058010100982d035621410204990400907400181000b002a42c41c00d805c0510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 200826924 1250 200825674 200825693
    0xb0a09030801050d02040906060e10060314010b0906160b0619030206090d03090f06050315062704060504020c0d03061502212b0b0a0806220203030c0303010e07050403 73
    0x2845210b130011000d00815921180c0242c4080d0b5030010042150646500501c6c034010029148003007251340810003c12450b000e0310406042d42e5a003c500c2d40f00341c0c41c00000000940c0801d030358a820040901c500007514903d00800b410240c481e0100c01e40034a8203605000b045450340c01c64101d4800511001c20258a03003500b00c0e030941c0026188488a0440c50906540e0941070b5030010305444841c8000040669200014601440d0404444216200c070502040410300a403110001000d507520040e1111132810b0954180222000d8804a1146c0c0e403a4000340032a08814a011040d8101040d22118580d01d0f2044401810030b00782c20501c8420310303a40c02959041035450080c1d181c0740100b1126101c40780707070301940c10b08508410300f26000c04d0302c00d905080d040e091680d41407003141480f82c16102c034034103003c01c041076503010401080c584d80c81130310b0800d4001075012003100425040c0c00440160314180010f1010a400500555032949844c0c82d030030303c041c0010003840400500744030a100141d40c24a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 200828174 1250 200826924 200826929
    0xe0d081914070e0f0103110906090406080303010303020d02010b010906020c0d032007080106090203040309151211070c0b03240604080a14100b091302150d0b12030c0309090717040305070b0a09030801 87
    0x3627000351151501004540100381c590056034292102100010400d540010301114031992a4000e021814000c001503d2050312402444096080889841882d0610300340b0030340154001d00e005d2000341242d075202c403100e07680d000440b9482d4205000c1808400303000d00911004021a070811480c52410740c500034494201d6005940c5000128420b00511500c9450b062140c0211741c142001041429408200030b503100c040c0c00c8481000e03200c400a07a07215402c094a200d96804508400000c40401b02c10030a584810b1145501c00c009010104810000700000600d691190710380405445100b40402e28028048080c02205801c04090442c207448103408250040c401c036002040c1c2d6400d910001c0c80304101080300044241003c03804222003403480e00036465111081c0c4003259070076091031080e80c0300e10038060030004a501c00c01941c440350910789012544074104c0e10b02042c0c015504800c20210300700903030b8240e0010344040f485506100c02d640031250001d01e44c5000304940311590780c002d030980d281407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 200829424 1250 200828174 200828179
    0x6090a080c07030b010e01030210080c03070f09030b09010e150403021c050d05250804020d02010e0a030807030504061e090e060f0a15030e0d081914070e0f01031109 72
    0x8521290310340d200b081250091940441d8886072580c507020b584809400900c07042e8032074a4400c4590190341c0c0070f042c0050040c002c0003851481d582d21458251074281d01a18004100524034000001040e94600454090309408001081c40c00300902401d141c5a031048490a074071900300c0900000039000900c100f841401b00689905014900100b542e9900490040307803502c5081a00304444000500d0074404c80c0c504070b0205050400a10700d040f100150201c2d40250400c00c1c2211103805503004444601c00e88000603d004202a01c81d918003800f50031450f0210045030000c1014440907400500044540c464035000c4035400050140080880040e403290f0401ca0088502180c0c090301c8081c400800c12a0141c41c1945550b610b051406404100c0c3c414000000d1918961206141e0b000c252212120340e680e0b0707008902d8894840c040306555a40403420036441d5180905641480514079140c0b00350025210b03c1401f15680b4103101203d00324404142c100f61410301100304895508007685c800131030a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 200830674 1250 200829424 200829427
    0xf0a0c0234080a030c0507080a0c050607020a1706101208070b10080d090806070e0307171c03090210092d030c0803071506030c050405191b02070806090a08 68
    0x28180030381604280382d00321044901070b0f810038100381500007450109184c403610866580d90b50b50440303240c46c0d4000010091107040d010808225070301d441c41c007402249000420038030340d841c0d40b1140c3c00008169002156a640c000c03000b04007400042404840081660307402c1502403070166980c0c0039251262140040803121410b01050004032241400f0703000d460184219850303c0000f0202429807102442400368038440c5d00d0014505c98419143c01241410140041140b1340c00c003070300c0300500514000403624910400c48000a404061212844442180e4500113400b100b02c0c014051001118403040c000c3c4042103d08000020780b600003207059162103500704000040003410085501e040d03a01c05018000044c0300424a10000b100506a080c800c5904603074084014586500355903d510000e040815400c02c00c10150a050300642e0380800c502d804900000426640c40044034104454605409880c00d440b400f030b01c1d01080400c0c054200e002c0245031038039100450720b42e6030138034000c01800c1100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 200831924 1250 200830674 200830753
    0x102070809090a063203070f050d0302030f07060207060b100813030507020310060e0108150403050a030222060201230408090105070c09051e07020615180f0a0c02 71
    0x303503880400500510089201c01e21505c5101110841c15415045081020381c030406440380b600140d5001101c2d4810b4844420510349401c001c00070070303003200907402d500042000c500c130b559441c4010718055120f0840103894a00b00d00340b100845e45036403c03081c040d41264050002c0d01d600603003078991154805500109081003443c04603100d000e5408000e42511500400750800200e94101c0d601707441c4050080062607031307034210141d91034203d10b41003015000d03600c001c600405e1040c0000e1a08260390704001d480c185410500d151265015404400c811810100611000ea4207010b040c401e0030280a844c218240420140c190b118405803000f04084030001d02207001ea4003030816a601b06802c085070111b429500c91902c0f0140208460454440070a09445510365918804040c000e42542c2d0081c10b26941d0800d02c0c011071150044041d50190343d803456940e041190080480c8030b846502141d41e51400c194099505a81d4002d0024003590041d17000004c2040420070100c800128551740b80c1660308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 200833174 1250 200831924 200831941
    0x7020a05060c030906060102030307140a0504170c011206080318210d0e01090305100e1009060f0f02040b07080a030615051e0a050412080f0703081602010207080909 72
    0x8105050081036809807034100606080100701540c131500880b000d41c1e0050392420012a01c03840300319641c01c0455407010718810072103030b817201616034441c45040c550f14140d110248440c62500c804000f2600f54031651300c50010f5640503a004d4803038400384205002c22802c022000392640580740003103914410b82e90304540c1654a10310300e0801480400340003450700860b0310704292034171503444044011880d2a16006180d510540480c011039810901609c202d040c0309608202501c289031040c44035105045481c09041c1040c440c203046c1d075200340400589518905e1118060b07441c0300c01401802031060208000b5413444100b243c00d240c0d40980001d5840c1c2c0501e8040d8020139481e0002c41030030b0400b00b00040c125030800010300501c0d034014015440c04030784100c50408c42c0300303800108001400c04d000401c0128800c4403a840540e1041160900702543c0382c0440794650041c0390260000744641c004d0048000d1140b509844c0c46020344001d61a01c040c2d030703d407400188520b030207039030050030f0f0303040014041d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 200834424 1250 200833174 200833183
    0x904090c09050405030a0906020a020109031103071502030a200606011b0b01030f0b06190501050d23161107061b0210030b0307170a0219090e010c1715090702 69
    0x14240441c0402241c02c05040031941d9801c507280311008200300c10b201182c07441c00060000d0340d055051b5501c001c40c908651f00c220b00e90b010f00920640500c20343d54041201c182112014000300c4079a801182c544040c2030b0300034450401400d442000c1c01400c0707800c4004e0403010840e640d2051081c20f000e030950701c0601002c00e8858000c04d01800300b114040000c402c105441320070011290054000a1182d1110010860310352200d640c000081d0154030300400081d4047e0020b01401190407100162200f60f81c1c0f1002c101c04000e880324800c1d00003070010440700915030079171402d046030285410b24144c1c9508202940e184c0543c0a54405e001d0348800425407889a4682000c10756400341c013203030300080900d1020740609a41074040c0e11034007641e00c6c08602d281000c0705828a10110600030110308440e50240b021403505101420400f0803080070200c3d0005242c05100403161002c2c000141070204000001e00c100c1c0354040002c2c409102c41d0134420100103e0700e0217405050308584201590321a00d2059142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 200835674 1250 200834424 200834429
    0x50c1306121d06041e0503030a05010611030a0e06070606051008010515090f0906010c0b01030f0201080f1312091a031006020102041a03041a0c07050f030a050904090c 73
    0x101105040480d526070310035182202103007020002d000c4000045a400d45404038400842010362062001601244070000c0c042c104041c044a0799000380c20f682c580d6070850780103d85450803d40c880004000301580304107058402e0b0350901c055402c06038a410028203d01e800e1550503c40e850108503002802007560110004140050249030f0b44040441d001d0409602403090742d00c50014004007003140d810074000c490300108010540085200c414041014502000c0c1445d4104690300507031100040080d0612800380d07024440f0040075006510006000700070081602c42543c2c11141406800a216980d122230030390f011042c3d9815403040d540855000300c803540f12120005241004400200e1414000c47c002c450714481251100d0b100c0000343e090340300340d101c2d24405111507482c4619000e049006190454402e05403021000510400d90752481002c0c0e4030225140000030b001000c001d010080780c01c8204007070010314100b8002c008090014000c4281d0a80500d031100090380c10440403291031000f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 200836924 1250 200835674 200835697
    0x9040203210f0307020f010c030204082a0a121e02010e09070201140c09010e03030306030307300807120603020a05011232010603060e0103080c01020c0a030e0103061d01030303050c 79
    0x840f03107004800290f4036406400c141b04c1e00c0d40303006054940c0602c0b03402210207031000300700104041044880301e80e0307540c420784d02c0010310b54110070481407040e038440401c074009104150740810880e2450804110602a041c03c0b034505038001060000142d03000350041401240440d090701c030030b0390307112000c4c0e0141c03964407030314600c103041d102c100031041d6850300281041c083c0c20782e903540c4041100d4090565a11041c2c4605600d540144803820005100d503100000512101c100c5080c01d9041220115042000d8461031001c690303580d0401c900d240d4044660b00000d640180180107262541d000300700c82c007129000da00c0c10408500c2c80c039596500241c00c03042204d115481c04410481140346240c072540e880711b50802031401d43d10300008100d03210b4002d010a0310400c55511100f80d00c0c555403180b00d03501040000419540a0140e2900e00501307110504400b802500e650b11000203610006049500070307041680c0d410204a19145107910303000030541034075818100083e607511003404080160145d84005c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 200838174 1250 200836924 200836927
    0xc07030f02120a03110d02060c1e0d0e070e090a03090306020f120c090a08070803031501260a05130b34030c0210090503070b06040b060409021809040203210f 69
    0x410154002401c5000804c46406e946a00d00364003002c0762214410345017150510030038043c820a0180081455944451040000f4909259604128280c401800081000360407a40d0104007101100c0101d80d40000c000b40544000f00503680d02070440310807070101070501c5901041452030440c84408039518501c0a4405d00c21626001c0d0310142150b0025031800d000700920800014030200008181c0c00344d4404001650a50390b401c0c0ca03200b403d668000340241080601c6004802c035520a4204c540c0d21300b90594400c2c142d28000e51988242c510151400441910021001002c03521500706142c04c11014041c1590417101c0711920030794011004031000f00e003c4d44404041c00d203501548100003058154003500c0c2c55241210002c0121804000064042d40040040303c0c0040d0f04030800d01ea02c628018400243e540054012a02680040e0041ca1026500060341c0300ac569440c8000788101030201c034280e90610740340d8042a1070326250a100d01b210100c100ea5186202100c005441e9000301c0340720482d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 200839424 1250 200838174 200838193
    0x3080c090d0f0218071e0311030f0601090b0f090609040b04050f0702010c03150e1e01080f0f0d1b0302030c0a0303020702040e0d0f050a02011104080a03140c07030f0212 74
    0x44042c010b00c1001244030315480300101d0502e6942215991040060351110500b100d20352804411080780c00c009001010750f60030038200445072501c00b1b18002c0380b4842d2403010b2882c050f0000341690415401c1484003110901591441c0e026448c112038240c0c0003982c0460301d83d44080007103000b9198010108d903001d4104010865000048080f0320302c10340c43d5078020b1080d076140f03600980848031000c000808801c1003100c1845480120303034001d42c112081102e00c09011311400700035000c14000303800824241e0440e00c2101d11070401005903e103840781a0000e07299a401c015409880740d1410b011510f0606c0b0b14810400c24035000303205807290030804605031410901d03e460014029440fa09040f0310507450488000c1c46d115001591001c403800c9a111420000e030111030584041d0000c5561b441150740384c21225030a070350b4076005840100301c103070010220300c0c0442ca0080c00046440705840c0e01c82030144003d41030400d00240c072004403038000d00c8901911000d4004508006084140540f41d0320404020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 200840674 1250 200839424 200839433
    0xf061c051e0c090f071e0905221401152a05070306050408030118020306100302090d050703050d080c0a050702060a050d2a030207050c0f18040b01080d09050d03080c090d 74
    0x340f0843e1241e50710207502c0da9440d258007801b1000855000050406d400030300c043e0402031310512075640100c1c51041d040c0441d440540664000100e004c0d944404079004000000410122400259079800d00d00c00002050480750310300d4022100b280c108441502e06981404007d0014070051034000e6130601842c030381402c007100e80d030b0f000303124481c0e1040f40110b803d1000b00d1540b0a07280601c0c002405441c80b0500000b01310080e42000710543e0340141056450b00c0040d000708548401944240c0140c040030b005c0500103082c603e030060001c8a450800c1208448150748982215201030f0b0490b101d60721101c42c440300300c4660059040300d04100c0d14107441c0034809146140d250b020641c00c2c08000c1494006a0720031026405035244c010480e502446c5c45040a15050b10840140c020103440051210b58014542501c00001c2c0c07030a880800d03020b0014000000706003d100012801410a19822440d080118400c0f4a10000240408c5244404682c406c402a02201c1c62140001c0c0580d1209810b0f040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 200841924 1250 200840674 200840701
    0x20c030c0a1205040b1204081303060506031b0307090213090c021615053c030108062a0307020705060c010f050114150a02010b03060f061c051e0c09 65
    0x105962000803000c60350b061610400840342075900c030700340250815543d40405615030304050700c111560344080c04962180e00c004900c11000314020f0300702041078201a814142005111410038821030000c011080d4951000216075044803105007005990740c140144e080740042a6800015a150800400040032940040c1801c20914000148500950744401c80060540400c11b0180855400c1c8071000d01203a0b00c0b407000342c0390318410320760203100e010180400c04403c1090761544006103010006114012003003080d10f034003854520100c1804004208101c0079140c4140314503880003c0000052a000c0c82404803400030b082c081d2899407075085d2505603034007825824940ca01f2151034a80005400d0340c1035080b10f90344240141405000d600c04c02c610524591240107c14290364a8541ca9005910100320291045521140b0a111402c0c002f08000310b183c0c0c1c4100d02071a015003c03411001103400403e01c2d22000700703141c0c071405248110345082400c00071801c1d200e6911441400420444881100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 200843174 1250 200841924 200841943
    0xa0b030628090305040e180606040207080702090c3a0f1416270b070503041a1c0209180709050409050102180307060801090b0d02060d0b01020610120b040204020c030c 73
    0x2600d1842c90790751244c0350200b207d4202500c44942d00078000b14540b030400758004d01c3d10a004054040c50051687c0200342c08450a0b110040c0500c2c00203801003040164504081162070b003002e20707081c814a50184c3d008003209482c0d084d0456503035140410b5603410b07035a03c524410401200440403030301d400c0c110b10b881650014044400f00c0c02c207503104111000500b813001940c043e000f00740c1c081d050600c208202c8981161030105c0e401d20040101049240001944219120340855529961803007540e10070010684030b0800030700f40703005103c05941d955402d00a40d800c1c410048044425a03556503040b94240380035809507420914121280c0c0a229041d00140f00907800d005038001d42803070103130030300d44d840c0070a10900c8001003403c0d0051000a00345d400081a41d40010400c4010320100d400154a60340800c40305048181d540380c405010b540c041c09102d40c4512030321000c030800361421405050742d085914000b08100c144400150455030b40d541030f40d003a0260324040300c2d00c5455858205556a6681 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 200844424 1250 200843174 200843189
    0x60e06090d0f080c0d060515091003050f04020907140a26010302090a020309100c0e040b01030204050d060e03130f030b090102030c18010c0b0705040e0a0b03062809030504 75
    0x4620002164000c03029001062041c0d5035256540da41c820303000781136800000c042482c05407151400203103076403089002452055441c0e102c82d6a20042000c029104200038000400d0600302001c0041100c250518183d2141c1c040d00c90507107a540703454088903070f8802a1080025054040750303112040d50f102c002c103280d1404c20800988500030251903103907208401d110095100c03091000003030310400ba07034003d9508482e050341110045112403e06006564018100400103000c11780c014801c1d25090142582c611800c0c2411481e0a081c500800c540c6000c4100140c03260342ca4050354003040d6002c0044980e58440222811421502c0b0481040e1030110b500c015521032010300c010a941d5001803003143d0040e111071810901e4561045449003442e4602d54109040c00744880a11000c00e50400c620b502c10b0300c05985d85595030f030400d0746213038034200003620f82054a413820042d482c00e5140043c103560019202580942c80921b5041205103060030440c8000740281070102c2c8004241d0058043c1040c0d51b840c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 200845674 1250 200844424 200844433
    0xa030f05010e0105060a27060f020c01030903020c011103071b0501020d1701210605010305010203180f07032402040602010b0108060d0203150601141b0d080c040302011b060e0609 78
    0x2961070200d070707520b802c0c080c099100030b0800c0300c0440b00e40034007480385c500600780c5a4650484500c0c80d01c2071203842c0d1940024003160060035124101c07035050150104202d4242410030200c40d1586000b95107486084406061003007190302c0e522121740400c00d94115503030050218402e808007090041c4414086c0c462980903100e170101c200b01c100d015420b80c030110112031480c404603a180c00004010011051001d4001040065a036008203269004440c040c5015100251352802c0480705071030354504400a510310340e04803400e00f071480c00340414010b040b40e400c0400306140001c0307180203135a4441206610644648000b0740090216010b421120100000341c0f01d034902a99090140509520281030003076041c0c00810000e81403449200b94550000c1c8189414030080c03c007400342000603800080c134608960380ca03075600c0000350b0040080d140d04981034030f8560050301300340219007000c1c0168040281800f41005c61607101c503451850400300c10b0341108041c8118015140d0003034982800795034400c5c45005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 200846924 1250 200845674 200845679
    0x90906050c04031115070f050703030908030c060f220f03020c150a030906110706050103140a05060c090607060c12150f270c120c1b12020a02060a030f0501 68
    0x9401e03081e41c04898100c882c0c40e048040c4241004102075640c0080b40050000384800c5010038a8041e944410b41d102e20010300c8910b003142400b420207411035000c0c14081d0301c00c0110314581040841c49031f801c08200d100303034100c035124030085030701d80240e0f00c04082c20b02c4003021500d014401200c0f0b04042c50b42c0a9000c3e1811198500240a0800c80300014414151010811218001d20a50044228a000d8000001c010800c0c00484407560721440701904e0044e10ba400600900c0b81040380300300b83d05070075802803200540c0b980c0d807107460b420000c0500440c0d1801203210039294582038101c42402ea40320a04200c0d00d0032404028006080d0442c001395464900480d1184584202c10300c0802d0381c07519112002400e141c20b515240650070b8440c4054060800c0101138a142081c0c00f44109149003929160804241210044110307558241c1882c10403210400036100c800500e120480c04603040303d007030181240070000030707440d01045100094210000050f42d81006606030b00c441c45108001c40144030720399 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 200848174 1250 200846924 200846941
    0x80304060f0213050622080c0a12020d0b07121416020705090c070c0306061203020f060f131a0f0910050411121f050604180323090a09090605 62
    0x5680210440032001c99041c0083d2501d117028002d14600c040115120078003440f03403490380d207116912a00381e55000c4807851701c0501d401c0c030501c40a4100d400100d1140c28041c0c001401040240d580a0014050200400e68151240c00380d107110350a64801400708039881030a85011303800031561200c629a400f03101d111074500c041110005c8403002004440c00c0c0c1c69040c1131a81d03075804004200c804e24004800000001c00c01d01803040180b090390290201c50004e130a002c6d082c00010100c90300343e9040001041001c2d00c11200c41a00401c5404a5004200481c6425900450b2a44424200400241c02c001020082c030050074807488400060b0340060a16444c1c02040c1d80040d10010025412035100c03001c2400e00f0310f03440c7c01481400e0106e4010211422012290300901d4911802003500c40041003018101070150281c01c0090003080150200b00e914014540340d121861600180d1841242540c1402410113580e0302500c000c021003d41959010041c0050440d18402c035800345c00d0000040e001d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 200849424 1250 200848174 200848177
    0x90309080d051b1507030b0607020a030b0603070506031b030c0706020c06091608120903150f010e060d11150910021507090f030303020a171305100c0203090118080604080304060f02 79
    0x82c01300300c804e210241c0702d105d070039409440482c0321a60443d00c00c1c01100c0140e40c0d48d8806400460255505207118180007007490f0074590b182e0011400b803141002032107640e20030091600e013421044000303980c90782c403403210b82000342c4034189014001e0ba0000c9201004240d002c0381d00ca004003400003c42e00d01102c4080d071b03506c68074850b200d004603039049541c200d0364100c146001404200380050030750702d004420038440010f0450645540010b10032840062240c8114a0421500310b00102d944070740a90441d602d4071010320f0300c103400a015101d401d0300e00c01003950030000d503240c640004045484c0111205c200a43e20036040e9061031000c0c14050104581c0b9008030b00402c20303603185010101c01d160558800780d01940c4254000802c0080c5078042900700514a0200b40c0180d4100d01c00c0f124421640c1412458082881540301500c2d00d030107240080c503a0000f08440c42d4600c00c0c2018004c10501c03100c05e80f003240203648041854050001000104a00e10b401144a2403051008110114024443c00c049 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 200850674 1250 200849424 200849443
    0x20721030c030e0c0f0f0a0602150105060403110112110a02010e12070b010605070f05010204090b010f0f0f030f0b030d02010920030a0f080903070308132304090309080d051b 76
    0x5980000242400a0a040383d6400c402000500307440d040540300c10114418039140d23804440142c02581e41d92100d11a05c401d41d90040c4400c4403a141000d00303540740d04001d2020300c420036040c4001c0d022440350603081e5401c1000255044014691182880c0304c000c0e0103441400003582e058081c940d400031000904400765115540c1128004500e80c2c00c214003903404d41c1c0007410a45107801c5088074180003034004d000500c00303031010000218811300701e00e00142c02c0c0c2703401c861013000b4032400c14000802d16510501c0d0007a42591850080352468400c1070440040071800841901400b8041e01d410200307805410000301c9a10980480c2d0244403069007200300c00c05d40703420540d8103401800140c8041001d440707254241501400000385001000b400085c50070712aa8004c81d800e81c000701d940310305550700405010040560f03690605804191942c1c1d14401c1514407000c500c074a0740d550524090500c54034909014103002401c9a000c1d480b03011005d0303da50480e126035081c51884094400c0d5515020548020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 200851924 1250 200850674 200850701
    0x2a0c070603181e0503071a010b030910050c04050d0602030f011a030708040201092402070f050d08070606051302030615070203060a0c11030715060602030913020c01020721030c03 78
    0x95500d10b035a510701120380c2e202004600820442111404135405100810451303104007072580700e419080c03480000c0003c5c143c0c0034860f245418801c1000c1c00c0c2c2d004c180c03c55114940e413030000d41c550310b0080e00c201901440d007103190060020751512080060b6035000354020f1615008004081c0e99501804986490305503590f0358180c1d040c404902543d0003410140e03001441410034038805030312058600c40040307034400c3e41c002d0340d440000001c45a03034043c4020700c080d082c03001c00b0300e59041c01c081c0030491100c55550010801a0001400e40511469500c4000606170042001c92025818022103000c5d404c00e48030a40300b6181c034850f000e5604802c0003214007995010340a01595540c0e902180300401e0040814014400100d0081002150030b000400055121301101c00070a256000d2a000703e0b0314980000096500401294265a490b812800c81103240c0c1c000140c1e0350005111403501900503560001d000818040281c00441507008005107541c0b0150303000c10529200d00340480c1030b44c02c80180041c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 200853174 1250 200851924 200851961
    0xb060901050a0605040b031509070203090411160b0a02070503120901140103030e090405120a02010f050108060c071212110a0e01030c0801120218070206010e0c040b0a082a0c070603 79
    0x150340c1b00300c040c582c00001030541900e0600d0200204042600485010b0016040011458001e00e018443c2e2885070803c2030b08030341013000383c0740d58400541603844090001c8003400700040c06c0900300c1e01103490090388003090f29102d00034a030800016890640e000c40395075007025400703003503640001072160403203030166a1004242540c0c0305000124a010f0015100c2e402040c8019195481602c010280c1034403590000944030f00c0440018100c0750306810440c09500100c00344100300b030005055465190300401c456241c91110307c01594a801d221103030362180f0741004481c40040c4441800f400516030291100c200007240c0c400110115405c100300300b404980c5103001444111000740c241020b151019000c1030079001e0403903400f01560030444218006034040300041c0003070841c80184540050712503814609007824a80700e414540141d40e8640100898100000c400718070700c255191580071001021948800e16101041460388003950b510850310418200007075181c4a0301ca4808403001140244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 200854424 1250 200853174 200853179
    0x32409031903020708070209040818040207020f0613030c060f030606030203131205090315040c060503040f06050403031814011d0a060203040c05090a060509070e010f0e0a0906030b060901050a060504 87
    0xba4020f41004505540c4000180219001070319540150b86c0114000c1004a0312445000250003505401801c281e0080f80180110401030b110450780b50620b04045a0060f102e050707645a400c1c0110071a032002e0301d03442c0031190001e51190071441c8026500000c0c2d805001c41d40c0c5131541601a40300c16985000000800303840000440c0c0450703594500340c086468100e142810800000c0e1808103290118400d81c0c164000b40010070626a100400610085c10000c1c1145481d0312407100c290814000a400c8039120400902003500c05d81c85840c168407031000e05850740189007400090321001100309001c41d032819480c9401c034a00404401401038540c0d004200c550310a0380c600000e500064000c44004801900100d52a0b50382c1a4582c8590200d880000341d072843d000401ca40f01c40050b0140382071164940d213444241c0da015003040040002c07420640030580512010640506840c0c0c05950420315104000c0f08000503059194090745088846134030310b0340c039001001100407407441240e01081080008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 200855674 1250 200854424 200854427
    0x9050c0f0109090f021b0a0b010e091c0203092b030507080d050c0c01140c040509060f03100f060e090322030606090204090c14040614090324090319 65
    0x40c0c46985006242c81002c10303a440f070790030041d207401d58441203400da00840d8000c0c4400a10b00381d455140e84044c010800000203482d10600158103000302505951560300040c00202c08004100150a032003200700f01e450545800203441e0381040303008502c650302c507103403d4640e00c0c6000d5008130356414022844168150555007034030b941e0f022100880300d8172001d105800000645204140c800da4809000d1995441441d8409085030440c030344044402e20300105202ca0402020151001d450042c3c40c1507603191521400a80c80251a114a507814400c2140d07001c24a5180d40003c075840300c101e01c040c001e040d00c421800f0440c0c082211500c0b1168410310a603c40030040b200950f403240025940300403941c6e207a0b107900041d256070350418080300d03400090400409100f403144507180a01c07850840d031110014495400340e07220398807809080040c50030966045101d84c20442d46140c0c402000c6800807240100001040d00708000c40000201e100400503000075030100444091520171515081091001c510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 200856924 1250 200855674 200855689
    0x1303150e0c0f0f180117030a090501030f0f0510080106080a02090c0304031103120417180f0406051305010303031d0d0309080c011a0f0a0b0304020d0602192109050c 72
    0x9403070307103d00d00391004a816120000032124283d01c20202d14420f40c140100b901c0c10400d80d40116660350700400140382c1c2550711030a05000c2d03a10900e40070078000f6198113240041c059601140c4001803511003848081a800c09140d4100d034040c0c8002c1c0006d5035111207184c4c6603c603016029420981344000988003100400065030320610a082403612000c10310100c40c42c50304040178001c80300c15100b0078041402414900f231044641c82c0402c413403515a0305c00303440c407201d100c4240c424012011304c5030b00302a65407150407600291002401d00800441c0398201480602001c0c4011380110340750551100c121b02815061200e039041031002400e0b607a9050404a00805005a003901c010005101d0094401c800b80500d095030841c00701c0303070703080b0003411010054440e085074031940c800c40d5020010010b03180d003081500d03841501218054010566420b081c00030b4828400345603025800c5d2342c401840548c111400149118000c0c0100d41101c0741141d0050489042e043c0207086d40d4007001180c05185445003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 200858174 1250 200856924 200856949
    0x80c0d050102131d10080a260705010b090601090501080c28020604031701120b0a020f1224090f070e0406120212010606090e0c040b1303150e0c 63
    0x1400140381c990480f001600315020f5070044c483c032252200428101002034076649070850340802018001d20303d8840e14680d100c0701100e00a00780c0c249520000c0d011030740c00e03c51a418000f01194513695585a15102c1e00800007011414030603010300c00802c04a500c00e0100340300751481078503001020741b903180c201d41c02500f01d803001080421880c50301d02441150005406100e0007141c0003003c260400746400f4107a03038003c1040386e0ba803950300c000401c00084844107151030300d074026441d802d1540b14000000068818180307070300c0300400c0016050380070b9450445000c1c400c01d00505a004d64034403a041707049030100c080859a80c06144400030448113411141d8031508248281044850904903a01041c1519841e03807000c0c04030040940c03440d0075410042840301c07045844000030801c641c140324014046c40c41f64018806031195103000561849170303030400c9801514510100300c0d00c540f0344414690b4452528002110304085048050031030100da8041c240320701d0018800f800c030a2011100b03002000d1440e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 200859424 1250 200858174 200858183
    0x7030215130f050c0a0f030b060312030a0c031503050610060e0607030509060714060115050304050312060a030b010b040614072d061802120d0816050c010203070f02070906080c0d 78
    0xf81d10484c440e5030b80002103c0100310340395841004901c1d48c100308101c1b0400800c031501030740201c1440459030009008072540000e002d00002850405c11000310018014424100c504d000391460200500000191403403044290070703102203003540c5a0700c00311443da401a0100d80c2164050119000003401900680803651002d010786041c071005031900407049021070303002c800c5504804014800040702d007445460044080c20720031700d11708207030b42e40c1581d900c101c0003c80304a6481c00041400c554400c1d030100011600240e0380019541c54280e15201680300340704545c0418148110820600800790507a054130360801d6070b500703403c4080c01a80013444560810518110300803d00000003804a10804c5610303490014204072a10041c41445407030008110800800c0c2d100d0344003a400e10741d21003681c0c0d0380506134058907450a803405200b51000d018036070700c180c0c40354004810001025030024064110f003800d07500f00c0701215a290480d130115040340c00b902c10960450b021520403800c2c040c04040243e80f1a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 200860674 1250 200859424 200859433
    0x20c0c092a031509040609061b0c060e030f03241f081008030a09031106070506070e0d08180901091109190305030406051b030307080103020409020a081207030215130f05 74
    0xf03000010042d2104540031602c2d43d0340c4600183c00d000140c0300e115444c006810004069100007140a00501002e10b0000c024130349030100f07405581c40a1050f00e03041096018850748904000c4a046520b000005c01c01d4081c0e12a030300107002030316242404400c1c205803c040b641c0e40d0031702d8103002c445c1024020028404c00384941c0d00054020420402040b90711407a0352030034070150562610320001500c800c402c61141c003043c058031020550114581b0b420281e2030130000007d81c2c0c0c5401040c800d031310f20701000e030558401281c0c051811b035284005011102007184c1d1022a61389500081d01210038480034851046800e000356280d50601000c0c07606117420120700d525440d95699076052a40d030041c1c00600006a0216031028040060495901c0110084001d0740c118940400f000b415040148000780c825900e4201070310664840101100241115034142e841e0056102032200c055071201c074048006108448203540300048950072540240b07031003409881898542d4544a440c03108000d016100c038001d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 200861924 1250 200860674 200860711
    0x30902030d1d0a0510081e040b0403021027020d020910060f020a12050703031409010c020d0206010f060e0102030d020a02010b0f060306030a0b1009020c0c092a03 71
    0x904004450071094165070755100c0c80300c1d034031812011181d2420998010059018207002c142c2d500340f644900040366141030300d170a507159221035419a60a07a0041d405010740010301040c041c0030780c43e00388540e0090f000c443d000d90310303142103800302d0f07080940c0d02400e5110702c0888003903280c200340c602d81610b000030a004518038403600000c1c021542075800c01c1d413644840004010158101c1d015281d80c0c801b0380090084002562569050f04040209110400c0000100c00702054040e0b4000030783c80e4040c10300c490647c944001001d0090079100740b41409403280e668035a1449200003085410b80d02c1c4c40406141107231030a6019136004e548070707205038154002403007541301118052014040c2c14446034000b280f00010181404500481c0040b80d502807030781042044110303200000c9101041da4408800e003903542d0b600692400c4400b90340c000b00303c40c500009080e000c641000803d4505c03460100c4407051140ca59403800001003240d180c8085074000b407019041e42013241c94020f994865410704a0f00007886 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 200863174 1250 200861924 200861929
    0xf01050a0204081c140f0409020a030c08100302030a120c1a06010e1203090d06020c012d0510090506010c0c06020d02060a023406020f12060a030305031303030902 71
    0x500444480340e6196001c00c0401c03080c1c20400030040c4403120300002050841c40c98130020300440c0b8240080c140e840b000659085c0310a03859048174003e11015070210b4441400b154002c01600c0003000380c50001d03184c0d80203d90803482486014044030382c02030082907040030759510044226454210041070140c65207003107001c070782054a0280c03024001c0c0006812443d082001401440d1007101d00b502849800300101100080081101d0450400b00c0758440d19141c246000c81c040d20030a51010500d500b01104000060000c01d01d90003da881c0000c0942900204819074003181d00c12101e2400a6031100d4040109010650245800c4001854101191403160700d41c880c01d90b40513845280141e104c0b90b00c0e800501d41c140010354005081540962a18003800c105035115401c2c001c120b07212901000c09400320b150b21049913104241d000000390341b51000c0d44041c03030041d0080c02ca001030098032280061502e16190440005599240e00c40300d0954036540d2112004044c0307071100b24180341d0303284008c0000da0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 200864424 1250 200863174 200863181
    0x1409190b0a1814010c0503070c060b030c060c0d0e0d02060f030c040b0f040503060603060103021f03023108060403091a0c06010b030702070f0e0f07091211010801120b060f030f01 78
    0x10380c01280000f409030441c444044c02c640e0f10386200f41c10000305000380708466900034039441590350840c0001c180b866075940003e040225183d801544107070300040c0108440004600d00c03100b00555107403044201e12a5041c02403945100341e000754030000030030000e1010340c219005103030415580e446203810240c8a55180041d6403080c006119141d0340030030100300f10300d000c00055078480d406402401940d491907004c111045907002c40c00071ba050614204d200c506210790305540d051043d09515020094884401200c403902c140c103558010320484002190318140090018050391b810380d95404442d02d04050020b4403c1c0300760400c017221800b04401c2c03106041c204101406001c1154450766241840c440c080c0c03914030a503004080380b5484100030001103081d00c2d80d00303502810b0300c10009503a40c1c0d00700040301e0182c050b4001800340315240003035400340700313070140b103042500f1017a2038048403640c070b030745500510035084100140380481000001b0100d0800350a12080744001904a9640d45241036882d400d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 200865674 1250 200864424 200864471
    0x1021080c0c041d07090506040e010513020a050306040305030f07091e0906050d110d1a011e06050c0d0e04110a210e100903090e09011409190b0a 63
    0x19680991010340451800303125040c0303c0307460307940300d04400801a10f410391243d80340d01c5113104455440001400648603508802c246035180002004503282440c032040741000141d0082c2d000b140c031058041040d04000854500985c1c0680701c10b81150b42d054619001540018501d074200901d04074000b92101f654560f0301010450380231400412400c100c011000c41e040c0750702c001d03c04c440710103003100030414507020002580b030144e5000803103039554100406c03540d641d88014003003282d1101c00000e80401c8038140c80882e00e650349100700d04654410301101e85000b0701000403866000740c401c00824902449a082c1000300182000c110b2514942504000703402c180c1840021a100890300c0c00c0190140f410f84481d54080c1d24100410142c01a00c83d5842c0c01495200c0b11840d580c4001307406150042d103d020083c040205880c0c01490003a007014041c00003050300c0c617048079829000c615201c00100b010380d600290001022146c1016855094540b48080c0c44500045c1e520003242c48a6200416007180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 200866924 1250 200865674 200865697
    0xf070302010c0f05130303181e0306110414091906121704030804060810090204060e0907020a02100c1113060806070e090109050604020d0e1e06102108 66
    0x2a140440b00015000c1c820107a1550100402001100c810700c5000c01020150b9403d450056940e20000e44100145840b60300030703d024540b000305800080c81c101900000b5240320354070a12030f036100c00ca00d01c50103028a000d0b091803030280e040c480c0c00034141100704a83c0a0310701d81902d0b002c600500202c8040302c4035600203020046841d4404018000c010040c114000f6091290902e094510b4880b82041d01450141c070f402c100701c800114035042c855055035409042500c3d001c5650356610400070301103241c000034060180091100040c0d50703030300210b11464560b0300500b1111103552898001c848c11540c01c14101c490304491b980c1142c0503201d40c0310003201e110240c01c000070300300e01f07210380580f40100081c002420803132050070416040e101c004425045441813003000c1419110640010701034081c441280c01600c2c0b0b41481d05903183ca00003045503028410f440340b0700c0d030002d1701c0e10917603101d160803500121002d213514802c0104c1e14001030300d02c646500240084030080300c15030316403116502000d1000c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 200868174 1250 200866924 200866931
    0x40b130f0b0f01140d020703020709060b070c050303120a0507110f07080601081c05090103020c0607080615090105070f0c050607050105041a060d02040c12090c2103050712050f07030201 81
    0x20700c241440340c1c49240c800030900f80b01842d01d1804086007968405c24030340f084a1900130645c0020940200b00e0980540004581480701640300c0c000c0501d15007089030140e84070900c80c00c0000c0c103401c1c04030444030045400118508650b03254101c1002a080280c410320800c066682c1e5019010f00911003041c2580554001e003401c6071828180520302041a004030146030030001c5907000d0515140c8a660007003059007002502e6240180058000340140e844e848414007441d030070082d0455020650b54425042203920202086e01036004c1507644c05180d8599000c01d400700300020110360014465802288242d8034019507a840e20003060150f049602d046409a44507001e200800c402d128800103040001007168005142020006081403407809001e40210f0fa6a1400024180b25001c41001e88041900c01d04c0301891600e4411000d81451040b410583d0700400c40c44c0035690005100280c441d0140c1d01c1d142003400d180c4450303000c3c990740170f01802800003c00c007040230394042034090000c4500a40000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 200869424 1250 200868174 200868191
    0x908031201090c111905120d020318060c120a020702040617010b01020d14180405070224060906060c0709050a02041d0408031614041509091505040b130f 67
    0xb0555256518002c14003c20080024025100040e1907511101041044800092a0400c942849500c0400c58a0a140040c1c81c180e801d04030340085000d03200114103000b80704071076940d40e0307100c3c41c00b1742d0861707010402005040c4070030000d90355298004410010041c80c10240d540000d084400707a5100ca091048070300d488040c4c1441c2032040701204d00007070002d480440505100100103e900100025400d5408240c410b014820304580300c1c020301d00900208002e05051101035625030740c2407202c5100e40d40f040c00d03095807000c62580c868020701d03016200d1000c5841e000c0c104411740d0454050101f05d0302c0340c4000001c55a40f107000351030003411910030041c2d8481c14140358064800d0100c000c81f4581c3c611340180000103401c401120743c450049a00c00001c0028498222060640d00c00d040c0000100407401151013046003482100000c22520781c07a242c80e503108125820742d0405a044005c6018010f410030960074550095060f00d000180b0400c5080011f0394410106e40e031030a98058459580c0544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 200870674 1250 200869424 200869439
    0x60806010e0a0c0905090a020c0a03080a0f0216031b0b011d060607030c03030e01110403050106090c0f0c0201140d0203040c03020109140604030f050309060c06150103060308090405070908031201 85
    0x5a00b20701c61400a0105445002c00640107820b03a10036640079240140000d01100300d02e07419101704180140a481c141c0a05043c020101c0b10b0075229440428905050901c1100c6144212840040c0c5827800012845094a09903041d070003e0800b00001d20040181e030000808c04180c0601a028030b488600103c4000c803c40344000780003d10150062000708200004690000b901210780303036143c80c3c085400c0e8070b80b003040b50140001410b820034001000c28088100003042d0410020b179540c1c5030040001303d908444c02ca4424403c41092004103c050382100d0140d4840e14050f940c0d40340040c0780501e40180c611111040740e02c00c0303509079606140300006008560b0701001000c0188480b035404c1011842c0301000620034400ea01c0011b010007950b2a810080003014001e5542c0b00700c000f00169251000707140669100c480071201d23603100042900003002c580d03000e881444203480d00044490708041030042481f0007803001900c1c0005200c10784100054000d420402092015400c00c40d0001035450801e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 200871924 1250 200870674 200870699
    0x9030309060503010e1801111819030c1815090209100305063d0207030605011d0103080904060803040b180d020303091e040501060e0319030f0507031206080601 70
    0x70101c1009810001000010f651a101e00e4100540d401001e00308681c0000e580c1c010890407c010418400c045815424001500c003080c650340c000f680c4201e1082205100a401044140002400034650380c1c814000026805011048044043c80014185010440706101f000035a841240340740d40000e203080390750030b01c0d20745411030038034600b8103001d142070240000c1c0e02221305800e0249064002219484040c1c8990341c0e040c8007000e0031000380300341d03402900020f4480c41e440c00183c4401e81048000508950100c20503541c021068030300d014540d00750f5950300001d0303005880c000d9219031246000b00700c500c4240000c0c4010600e100010780c1c0c41040d0030101c5160718070506814400c01000c001c070700258402208450710030f1b0040340d0b00900ca044061a615035507400440b10758002d40b03080c001240e02504002c440d800040c0071000c03640c0f4000043c0203242c00c003590b2407004002034980800022500d000e080a82007a40c820306220a0001054a081040740c001b58440d580c954070820040084100d00f44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 200873174 1250 200871924 200871929
    0x10b21010c1409060c030d090305031e0405030f0c0c0a0e0a2016020607080403050d09080f100e0a0b0f0a0b06042d082407030b090c13030c0609030309 66
    0x41c04801c0080c026400c2d101030140844803405018006110001c244050044035208600700c481081500c40d18180280a504101d8601200803e61b140c040010b180d03480e04284100d038010000c40c0341c124a16460703a55034100700708910503807013504e14010f041e584501008000c0c14043d45c1c0300320149084070a240c180c45005544540c030002c01600e9801c840001301c02c903007181d91451072003110030f030891000c108588503802000d40111800304002c400c121001c1340b101440c01440d500c4100b540e4856142d80d8684004980010742c2c5d80c0801c02d034640440881d0464803c4130b071903d05840ac80041d0307480304088030f4012210480740c4940c05040007444d110030f11820340b00c4182607804508250030580a02c4014081c900c1540c00303210f0291882c2201180d20285e40f0103800044180c0350016912584183e903c030182100c2d404910380741c0001742417240f1911400040c0320f0010103500d4a5165001412156885507911100c541402c07035020000c55013004910008103500e5031186c0e00c42d484d604008000f2860364 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 200874424 1250 200873174 200873177
    0x50d0b040c020a110a120b041403040b04050109050612150f030a03050d050c0304080307141303050d0e1903030503090c0619090f03080d0b011e0905010e0a0e0711010b21010c 76
    0xe030601c01d0500f80340000740d58582c07147c42c0000580310350500341c8024104000300452480000f42c045644a4550301034801c5403420780f02e00481030745903020440035014100b0110400000540018644e50f4821800c0c41c3e90071026013250290071b655404203042100200041c0c010a90002d6009c03422481c6126842c0c1c4590540401c0307080d81801e50382e010643c4405440d00301040a42400640c0c2e03001c080084442d42d5022030700d5840e0156407840c04ca41ca640020f8400d01c003050340504a58201c0c02c02440c06030b00402041031910079039095a406842c990000350501c10540f1414040c030030a9101e100081c40c6000428044905490382c016009250a00c00e8200c07100e08040c1030404c000081242090320078282844030041400c6a4080c01241e0000d0404104612948001ca40003182c83e0000b9120050b00c6081e44d803038522400e0b0105000a1104501c43c0c0240004200001201c1d20302c1a0081c20100000b600007203050001e0314001820b003070414180c0d0602510441514102007024400c1d400000b02c0b9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 200875674 1250 200874424 200874439
    0xf0904030e010c060b03060115020f0a0c150e040504050c0307090213061d03010606030b0102010609020f040905130803100509090606010804080a110102040b04080c0d05030a050d0b040c020a11 84
    0x99a001030250340d0400d503080c1407102e801000f008100954120102001010301110442c1d80c0d03c40d00484070000c2d034801c80f0054041c00c1060104180042003600407642c009007040c1c0c1c1c2900c2c0000e80c10142501c0700c4a41e081110f004d1151145a4a0f40139803401207008000a01c1340f44203081c209824450243d122000e5075104015607003110f2151074409003141c0407810300c1307005d649580d4004242030007443c5801da1b240d46420b4010808603015440422440002e034000c104107611880e20008a00c200b91482c4840c0c00140000c000205064100350341c0000c0d840052810109240d8886070b6542040d43d1100d40800703004010310403400c04a089a0780003400c04010111170414100203019006c010744045e103014030001c2c980c5407003070161840c00413a1202d4002190ba403a82c80d912401260410300881600d401031041c00821803070100034181100740c101c0069403809165400595441d0b104c800c040c0450707078886140302c08560765441001403285168014064100652400d200f807003042d1640c00e48175886 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 200876924 1250 200875674 200875681
    0x306021b1f0c030e0118050c010c020a090c05040503030c030307081e0402091b0c16050103061a0a03090b0a050a0b090c0d020706021902070e15090a0c09051e0f09 71
    0x4504511903402807910600040c02c0201c500203d001c0c3c090400750b03603005d600b0039101250001090155005440c060416581003031518001140c07010345c0300b84007962084040c18184034805080c3e015545030450742c01c10700e01e8240d9600201e070840d00083ca1510045e00048200103e1540103940154000e11802ca40240000017080d040d10342c55010f4000313405800d2000001d120700b8190900c848902424600058036a20782c46500703650b41d0300c1c070342402d900000e20120005140d402401800700342da4030300030075400000c030b001c00400e49504158000c00070941c46402610100b001129070502401c2040b5011a042c5001c500310410b813079000002c1401200d01c0401c00c5400c04110040d9601d41c1c43c5800c0141ea58003840c04c24402a0282e0031801c03030640c2000c1d2454020a80001c1c0420403160346450702e00c12a039484104e0700692000044250304a040f07100069415412948103400c3c250701d6040c03101e8140d8541e40410b4442d02500d481d145205020a4002201c0c500804040310b0300804035101e4000d80b8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 200878174 1250 200876924 200876953
    0x180907120804081621260a02070b0c34030c05041b092112030203060112090b130201021609050106121112040203031608031510021509070f0306021b 65
    0x8454403182010341c44c036000150411100d2040040c03421b0402032652140240c0c000042c0c0390364021600040548038034003002494031101e1007a201010030350b1001d402300d416600003000c1034088401e8078a0104941c7c1003100b0000c0307401c0d8130503006540170303450340319201d801c04041c0310450b4801038000029600f50643c0c160559030000141e0300381c0d01000c000e82c4a4001a200c02c4980c400b550300c0042c00d1140c007001c00c40301164141d000c3c5100309400d030f891110525040c24024112010300c1030180450b10706100040c0e000c15280c1d80d90078440d00c1171044544540628039800d40414158000e124042c0c4c41e40010000203522400c20121418008030402c2620b00002d0300c040944200c2e2107000c0c42c0d1214200040541d5005d01c281c501d1001114403540111905281417038055000b25100702e040317201141c058610b42004c0030301c000000815001098680c0408141d0745001400900d074a10380d1080c01d03400302d2900529101000207600c80c100150315141030700391482c1d82c01c0050b0300202d0360760b0181080a20340e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 200879424 1250 200878174 200878199
    0x807120917250801020c0105040b010b040305030406300606121127060a02010204061808030a0315081b090c0c060121020d030e09151809071208040816 66
    0x10380071444812280002100005052142c0c3d2002c0c203194404150030320840710640140b80304a100d060114600c0ea200e1040c00c0b4580100d00000e003050b031081c0418014180a0320180542c3c0c000b801888260a42c1034400c40b010942d1024190341107504c4100070001700c0d400a0220500b1405100c0500081038064600300f03460155040800d402140001103006441c00030030071040710700e00500401c0d0740f54402c1d10082e01170741c003502c00c2c0800200388036151125018607640000590301d10102851501e00b1242085001c0c0418254240b00c0d034840407400900400d0411060004401103086600c210862200700f00d00d00034001c04c038001814082151200d0424003050130350645200c038031111030b034245d007100c0080385030a0000004e4103c1415200b07442415080b00072004408401c82da100300702d5480c290040080070842141c030f50400044159a0484807981a6940d44884524200c4244540d100c000142d50305100e4010307a801180040d060290401c28405d404950425040c010101842c01001c500007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 200880674 1250 200879424 200879443
    0x150b01050a05070b10080105070f020609160302012d0905030c040501060c150e0d05030105040f0b090c0714030714190f08180a15030b01021b0411070807120917 70
    0x78109513000444a0107051100c1d009040400020032079480c0499001c2c00d240000750844000d4401e5400090b510300000070b00c401070701c41209900c08018a1035005444a0342601b03440101300d072200c040340200c801c81107601d20040f6200d5480114292500f014941007503008000580500d08040051100a0308101c03d1a0304a900617106804080c03650100401410070307a9031071b0b949000d444000760300d9651160146044c1d403803c0702d003041820309801001c0708807102c0c0c1c864641c000514000041c8204c40132406006aa8001c5c440007900c12000c11040d0300b19400b4840c101c03003c4400340e5000c0d90010040021489100002031455500300158448200c0500070541c028100e10000a0b5847e410040801030412110301800d800e54094842003030700c44605032402d03240002480e0448900c039640c40001c02403010340c0c544081107484070024041c00060030741c00018603c658010850100000c039400c00510b1801d01940c1110b81c001c8003003000030142c0440358824800f0040d40000e800c03c001020588042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 200881924 1250 200880674 200880683
    0x5010512150303070501180c05031c03020307030225290406320403020105100e04020d17120f060405040b150307120303020403050c010203040303020a0b0a0209060304150b01050a0507 80
    0x40c45101c0400282c82c6114010005003035508100d20072200924a1001104c003230300c961000d5100c80c0d129801e00d40e42da00c10001c4200c028103407003848000e850290b4029a04000e8600c5d02500c2e0480b51000422102c24016008902400c409088005d001241c0c80d0503140d00c03031117800c51030028403a000d0b0003400e001c05003000d0300b03059550302a250f0f00f509140c030301c0745802d0f003000321443c030498490f8880b50300580444054000d035003010b000540d44400d08203090141c41c000d61410105496680a102c1842c20300c1c2d07003c580400102058060124842024020f00190329110b44014500414201d10300640602b030725001740c4c18002844006841c045109a01130070910b8043d0b5004085000a40340c025150b0000908112140b4820f051503415001402079238002c804968203004c3c1540120703945e110f00d200142c0140c00031261080041d412151241e00840c10540250914844400041e183c2d4016102213070104201440e14209103214041e9004501090030f0081c01d08080d014054118820444000c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 200883174 1250 200881924 200881951
    0x301180c1518080f0615100e060c0105010b13060513050105070501060308161110020c011107080d030207050606030a170d0204090f150f0518092505010905010512 71
    0xc07201403064441442489040d00808501c0f80e036111420703210b91640560550500130003000544281801c074400e04500d801070f002c580e2800d00c4010880302440520030499020804002107402d0342000d0040c07a0191003044e030007590780c59405d21014906001e40e07204005002c420300841124028400c1804d04482c02030070903998a081600c0c15a00400094100424401c80464981c0c8000b00075100030300464400c16000459451500c00c202c02454403510190050b406444429403651094200403210180c07001180d26141d1280105400c3c1900e00b2248000241d0100c0c0890900108002003a00202705402034904490b09450340f0f10064900800310319a00d0000071100b40803052981141d00500309624200200c00040704828003400c1120b2440c1c841c210529404140001609808000c0703030001082e82f003400b113405804000e503403001000712100e03001d080081c03018945085210368245000042070207200d403d020015080303084a0b0051810094280704060f500210740800e10740000c4c680c40320a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 200884424 1250 200883174 200883209
    0x1060509040b061e0307120608030f09010c0b15010f180302012006130615271d070602010509010e0a151e140105060c03032403070f050301180c 63
    0x283c091166402c0c41290908022240e49064802005503001b40b105c0d580d8182d2010301040010183e981901036802c15810401c0142584096032005007100034060411408140807515140364113102210310349811030400a03880360b95a0300c5034814003c8040c3e4140041c1c01903460780501740d001c44902000b4140b1458084210907001e049031031007a02090881121f500745000c00107001042092030b002c451039414208105001c801c4d40b0248000d40d044840c90300b809c13000c0328407200e20412491000a803a00d83e101d202e0000c1841c903020101854040100414510b494450300a0840b0030081241c015a40341000164044202003040047c09800c00c0c0c0030201000100c0c0b042c002401c6d5040354180b010041606408484100d030400d0360b8030140203004440680e038400500500740300301010340640350010000540c0b01540b4580440c006031b0703140040844c460110021034a00702090b00b010b00350f00c0302c0c3e210401880c0390034041d2081d402142c0d0301b5004c201e0199030362841c441c2c90b076000d490082a5003c101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 200885674 1250 200884424 200884429
    0x80711030421021516110427110a060e0114040906031a010e132913020f060a0903120e0402040e0f070903080405010e010c050105010305060708090601060509040b 71
    0x540340075241c40b2805120b02444412110414412020103d01a04600d0060301d1074043d00030035a64440280e8158a1031100382d40d98000d0700c0ca940000c1c150b40b045d0b5641c205001100800d02d00c032800f1090440da0405501503007809000c910a4a042c544102c40d00907050090503400404c800d8014001c1c2464071000d240042c40f00407500a0b0742004e41c0c00c600c0c0100000600018000a40c4c1607050f2401ca40c003241d881d40e00c400c0072501c0449600c4070003101541040c1c0003030312510050300703600c0840c2010f0703c0d9403010810040d03103940c080d2003d61814240708180c00561400b42010000e00ca012290640f42131443d50700900420154400130700800525100100264050000c110101d48000d000b15641c545648000a441a050342c00d045015400d600244846000c0c0c0d0504050700c4c0c002c00d811b17003414948001115143c1d0703007100e51030400400c61780290020b5024040c1c14043c510450182c4801d10300380ea0024503104004104000341c3e40003400400c091034000d01205d0f00300500359004543c03c0d104801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 200886924 1250 200885674 200885677
    0x50c0901030b030c0609190306050f01051008090309132003060a0920090d0f05031206030303060f060a02160b0703020606011812080c10060608130b0f040f08030703020a120c08071103 80
    0x4013500c9039003052b040000d15040c82804070f050310811107021680d4000741200b20b070300032011030300e20b00f4540c02000400303448d29003000304d4050148002000300b81000b4002215a604c10943c81c40c00d880310b404820301070b040c0713488071b000c5026146d152020000800c81b81c24450600b40b034004400b801c503000103000f160b5501c803007100d001e43c40d410115207030084119203051a56036002c070140c844003c507a01c1c04030b110780c5408011280501d000910105486d00560100301c82540203174401025031203402034004580d01d03011840c2d801002d080002c15201d0f041401d0190600000074161410048041c41c030030381c10480852024141c4214028150181500d07241046440c41000c11101040c4541e070303580c00c400400d981040060b40c0c0299129240c9494222603401a00c0d400c01c4001c00c4403031b81b1800541d01d0b403001810a540030f80220320008080310b0359200c895050f40306580210000ba000a42c0f448004e412951800c00322100344010406900e406200801010000d00758a04220416000c02c10300c800410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 200888174 1250 200886924 200886929
    0x1050604061a30070f030b040509030d0e011508030c10020702011d03030f07060b01111c03050901020f0a0c1b030206030f0601021f060e160801050d15050c0901030b030c060919 77
    0x202c3d81c48140c1404503020f081c40d4201022070000078184408160982828054240900e89240041d81444000200b59000d07140e8420440d0141d941c4e03401c410200000d11300198004c02c00c2d103024560b1036061109003410000090100000d46004011500042c0d074480300b0001100c501c1c2c00c403002000c2d0074000103400c40c840d22007100c600042c0440c4c42c3d0140700c03003540002a21007007600c42c100001d0701c905a403510343c601d20081c661010015411031040398026000f881e17110350001c00046c43e14413848465200350300108500c4c00040c5ca0b20001e0002c0282200307102170240380350509850301914580c0000da080c48020050f8220603031141c0030455a9008020005181070145280780c4c2101c692032514004052503c26650749280e410003084200400c0000c1001211481d9640320081e8204020301c00c1d04610071004581d001c1503241d10240007120b07446aa070055000d9010715503122031481c00141683c292051951003034004229038640c13603a40380203c850703a03c010381c0c407403107594234101d100c81c00c00c01c480c1d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 200889424 1250 200888174 200888257
    0x7020a090b0f040e031801030b1008040b010e10140d0204062408041109061c120e06122701090c06171005090a020c030c01050604061a 59
    0x28000400d00011640000c10070500903180301401d14010820442921142410410241c00c20044070020020743c00314140d0080040c10302041011441e404120789644a1910328000303035100d810f200c01c01603e81c81c4c0c1c074018098042010020305000180050440c05446003003842001c01c1950055070321030b9010034900d690002e008000302555018803110445d120303010100341c0080359182680450042054600603500003480ca8a05040c4000340144010040e248a500c03648044040e41c03e44404058010400c3c86400c810300c0a03070308003002a0010508071400b503c40d10043c8a01c05000c0103400c4a164498156036410040007007009000d0314480c0054000442c1d942880c0000c020f12065444003030407507905a41e2030003102e010801031170130341c081601c007003a5128a00004014a10b0903150751504817000600041c582010301c0d01c3c19145500040154405946a0007009a5494288240401411a1440c80001524848004050344030b848000c0100c010f6441c0040c1411844512003414440c91 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 200890674 1250 200889424 200889439
    0x1031b140d0f1b0816091511060a09050c0628090f0806010810110f0c010f060311280909060902060c0a0b1609030b0702011b0906030608011b050f0702 66
    0x107940f122075503100e02212100440c0c48a0301181c003000c855854090740401d20b95680d44804e0030106a07281548070036440a04100ea0b215611030b09000900610340200c101b800001a50351040c94218109035460143c1c40c8221400d0003c00c0c0990300804491000d001c030005880c025003844403040c0c030140f446030080d10001c0d030035074000315203030f032000500c14181d456000803121089824104041500d000044034000804240030f22581c0b410308102500c8088200000840c60200429502c01101c205500594a9840c140100d101504001e186c0520704681a024444402d440510806c4204210302c41d40c94002d40d20a461230030722150350300c424006030b402085e0f03c1e0384030039901c40d069550084101c02d681e043e01601c08140600000e2003240d1403000b05445210105146032614140c11000800c171000390354079050403c0e41000c258000541d42c1c0c034070b6220034081e2408c1030790040480303240e5041034110360b141103d020b841c840c0d2107008105000031464800d13a035421150a400e194041e42000a4001c0c12 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 200891924 1250 200890674 200890691
    0x20109080d050409050a02070c05090919061d0115050d11040c0807080c09010f080c1911100504020a1a120a0506040c05030f010306050a0e031801031b140d0f 69
    0x1d222008100300c0c0c908070400d005c1900e890310410300724440c003480188407111010003000300707083c0104100c1c0e010343c0c01c0e01960b03210303030304000c001c0c40624580701c0407202940d0760003211200380324515035000c5440d40100200030300702c4e031542c0403c041c1000d40140b51250000c44c0341d800821000c0d03002e0000c0100c000c0c009111b2010024805480b074241030701d00c10042508800019580c180000584c0c40c3c220050350b800340307810710310a0f050780c180c0c8019280b41400b0750b0400c03900f417801c440f403074100180d01005d907140d640151484132a642030081d03ca5012543ca0300f48070134070002d82c1d51035020310150b600c01180000080e00440c81c103000c6100d002e5030a410075108104002011a0a900c07140c4031300740a46041c0050030110380304682e144001c03640c0480701c428080042c0042102039000035484840b0603000283d0403102c0b01c85501c0c580015800502040c0c2008109100e5640750140060b01c0e00711801c3e0600220b01c070340c805400301c003114103914a024404248945000d40540264600c403600300010000203d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 200893174 1250 200891924 200891927
    0x30609050307020a170607050901030e03071a011710050619060206060f0103050919050118062004030206160203030d0e0a02011806020a020402091201150e060402120a0207020109080d 80
    0x401042c0207038425488500001048080520424518240c4030040e10341503603030740c80540700d5400c09802c460400d035032510040780c598410001081910f009082d540c481800300b40585511400c144c00c01e158a42d0200703d4500e905000091150030108103850101c4c2580d03030003004ca00c0205806d00c070812420b90350380b80041c00340e030041010350113600103035003207081c40e010f0034019070540d10283c4414030550b11004610440b90b003802054088203200c0d03000424070640171070011095080140003500c900e65604044025820f800040380c100001c04098582080d2654001883c5130190514000c58841510707032800840d5810710403940ca028001c10104460440c003042d40b0780d5501c0061040380402d98001c0070410707001d0115001c2c1c085804543c020448103105500703000103900f000c0c130016001458884030444c024000c0c003540c20544c0300140c2c1e117000249003e900da002c500000d49405e0140e0320401494080d204171981007503000c42007500c0540c0d9641140b0040f1407108080d03000b800c0502450165030300c00ca = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 200894424 1250 200893174 200893177
    0x718090b04080c0607030c0c120e03030301140306010518012108030a1b17061c0507120c17060c031f030809120105060906011103040f060201060e0702011a040e070306090503 76
    0x90362140f084960f10343c0d0ba000158103e031004105a00402c00514141000031111100c0d1000c800603440c00640a40300c0700f020a2644d00282c02165000360740e44803500c6a41030400035a4010030f000c4030545109501c0c0000c0008418041c040c10308000720341b40b4406c060314030174150035440380e50146420b540c80c600314a0300300041081c0000101c90b4540f504c003800c1c445100d0050984501028007889000e80c82e19030401049810782c0d925103414405881d005000f18105100b2940103040401c44107880075a00c3ca0103099001264010000c1d0902c10241403020000003d01e02d60b0064000048540e41e4030750345580c100f484013507491402d140702c10000c08030030070014101503e45075400703665480014102c1c4001c5401d80d201104c00d15005a007c00014509612415941d1950111001a13914040e1212000014000940c01a07000b42c3e440e400100007e2901450140d40201148001c124100324501d50f01540141c04a40038031980e01d440c40510645d00a01900c4c005662018042044101920300b9030703102e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 200895674 1250 200894424 200894437
    0x30105010305011d07050d0b031e1e03030f06010509030d0f030506030c030a150204120503070302071401080a0b04230405070608011a03070e13020309010c0906020718090b0408 77
    0x1904020000488103090303141d1086411007032081c1d0384e103503890070300c212101d801803052903401548481c000f141c80d48062007040903c414884038401c030344541803c601d10b030044030701f00e4035a0b4890345030187c0d14100b808401d0725000141000700c46050340341c0500403105805003001c0a0340c14011b82c4a50308110303410551040f8000c07590b403002c0c042aa1020304042c5c8442c254422190103800410304c480000d00f4401b4100501e00314070710014107040e02c802c1081c1c103a0750840700841e483d50000a440b0300f89501009010010503180c400d03034600e1101200002c01a00001d4211000070751a010a00303003d03a603d4000c0711100005441241c1c2c9103000100d544445e80e0b007a181035419005900c800314081e4031640804c0e042e904174914001c900090100d0440080d840201818200b041c4054480300980d140962246428101400076840c0d06100071942c0c00c4171110000001806164101005140c1d00840e00704112114000500c48000d964140c001c0640007090004086403041c500300420428100083d118 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 200896924 1250 200895674 200895677
    0x70807141c0809120f0d05060d05010c090305012405010503040f05030a030213051801120606180504050c010e03060a09060e060705040608070302090a03020d0614040c050418150b120a050303010501 86
    0x810070000d60104c511344500288485580010000041203201d02d030429904000042c15001083d0342c907440d92801c40b12148014000140700090801c1405024028046e600200407260305400c184200380d60030501c0148a002c0c140100840064140040300d04a190800d81002c184c0b5591600010010001e40c0044810085440c40c0c080100c0c03d4200401760340c200650490612046900f0702c92400f964000c800d000701e1b181c64a900c80440d00341c41c40300608100c80720f648004221814a894101d0400d141c0800050421101d004004078542d00055040c0d00440b00c40e500166204003130070403601504144c066030702e05200780402e20022070fa000c0c00a10448481e543e4680f1152101e9038114143d02c90030408a9010108000520161406035801598184207813800100c5810380c1403107048202c002ca400352840f040040c0200300c03034101405840c510304c030692801803440180b55604804d01200070202e110442d902c14140c0c60a48400350020040c0b00601e040f19001c000518001c1da8035842406600d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 200898174 1250 200896924 200896933
    0x323090120040f120c0312020709180209070f0e03060405030a0f05040807180b03061807120203060c0a02012c0d08040203100906020405060c10050903070807141c0809 73
    0xc251004040a0b00d003600d9922442490b0301c0e252000400032401c0e410816142c4281d140000000954241440500000603401520700b0502e04010130088541c0e04000d1264503609203681001a80c40c110400d520016070700345441515050b10044400036001240603402d0310403042800305028000020303004444503a0303283e0302103540b2110101c03081d020310b11465041d5840390005100e185040035008a200040350000910041403100192801c1001c1e95550304261502d1940001b06030180800d901174070b03001d811418101030300d5001ca6519500102501c65101010800b0740070103200f074021818602c41c0f090800c030075150040039694038104010f420401807003501e528800d101d00603d10580b0982c5c0050141100c80030b00002c03103000c3c005500c000c0fa4107a900300404540c0b5950640942040b0f20184010101c43c2c0044513810304071103018000000b564000d020007000a448602158191a8400351003070400000e010140e2034010081e2030051030800e894091118268003070096403190708100102e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 200899280 1106 200898174 200898221
    0x5040f12150f050702071a0a050c0102040b120f160f0c1a0a060314030906030103020d0807080711011e140a09030f12090603060b040603230901 63
    0x1102d800d5a00d00900110950412000700501a410214885852610604910b501500d00d65004001001a1400b0602d0080d019140140241c0215584030203000c15070010310403085500d40c98940741c40300000c011451800540c24640c81039200e61b040c96900326001c545c035801d40841070750f54902d60003100003031580507540d140c03282042c8280010300710300b54901000c980350242400c9165510a01c90354986550b0802201e0441c1e074103e8643e00b039046103161030200c50040d958082c048080102d00401440007800031340d000c803038090342d82c0072a1001149840c02da040c59a95100e0008141c194081c03044041d4038018065182181440030005503030350f8a18230460450101290b081a0360144a202e20350002111405080c141c20f05120b82401c0041c104460b00452107034804041e21088800c0d14842c600780c45800a010b160001c234194545400264040d088480e0320804982688024 = true := by decide +kernel

theorem cover : BRFrame.Cov 200719424 200899280 := by
  have h0 := BRFrame.cov_init 200719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 200719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 200719424 ≤ n) (h2 : n < 200899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
