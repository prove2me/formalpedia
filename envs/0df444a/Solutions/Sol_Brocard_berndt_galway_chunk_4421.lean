-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4421
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:34:02.182976+00:00
-- url     : https://prove2.me/submissions/cb814a8b-022a-48e0-94b1-9d12709da996

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 794964028 ≤ n < 795143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 794965278 1250 794964028 794964043
    0x90e010503030712050306030c0409061505032e1b081611060412050715020403051005060d03320304051908120c04030b010e090f0f0307020108190e0609 67
    0x1440399104000f0000010400e4215000f01c40300c5041c804c2d10b03542c800b030100b030900f408000019400340c0b91500306030811459070f011001d08003904c541010b40c1620f0388245a620415804501d8031011100f9409140541d01002601c5040240c000401da0041314120941d10201e442c0d940404507000504000443c00d054a0400d966903583c40c00900350354001041c3d83c1c4a1901600180c840c07251200c5002080c0c0c0500200c038091070348803d00c0e807003001c0750484101c000d4106020031100e0f8001c81000800c441c1042c01250700820000301030103110354940e641603502e4002c1607a4076000300d6152201848000070000c0b9a0f00d41d030052805103079280f8007490500d0034100325204a0b02e40c2c42c507400c800b0703004c124100140c0b01407010041d40d08032591174004090000d03009a61009101e11004000440c0001c01c0303080c114040d5140c4070484881c3c1b0002403407691600d25031401c141240d0b0003409810099031140d0000c0d500496413a180341c84521030303540c55038240c4007402c420400e070f54881c10920010010401181 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 794966528 1250 794965278 794965289
    0x30115030c08010f3503030405010b0603150112060509090102070201020708010516051803010218041a01050f0a0504180b10140a0f03020c07171504080d0903020f01020a090e01 77
    0x40c0c0a6050280f03c015000301030091505c140c18a081c070b450944280e10a125511051440000c0c124100201090380c0754000c80e000c6405500b005000203580c1400400d03280181c640a1900d034031500d51400444040303410344100d01e006505c4d9803000845444440c0c10074092016207002507540c21050001910301062640a8880c681c502800c200c2038602120f4002e000072640d140403940c0351102c10441000085038802658103510001d4020750304a0340c00c28096590006990511880715031040020351f03400d424503014041401008038140d00c80504005040d140784906000741071584401c0c07014000041202220109903445109103000d180055104401c10034925201103114010701c10500103001d000110018001d80414840d0740500a80641c1c0d40020400300b1603c40b42d6448140c4201c0c0050300300000c8840c0501250000c00d00301c840500ca00c11a001600c00386042ca0301c0c02008000d04a4400980c02c60007003138030f4000d00c00800c0c00107100c030040ca551a103e20904000c400280f03140180d210 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 794967778 1250 794966528 794966537
    0xf050702071d130605042d060c050a020d0e01090b0d1d030a05070f020a080604050a0b0709050a290328091a101d0f0702010c2a020402030115030c 64
    0x3c006070948200072020103180d2282c004251500e40b4584061603a00104c4040c61401903000481540c0d025518a01c1103a4050715051084201d120070a440314491400d40c0320050b042049050b080c140501d00392061181c040c5403c0400b1592071070081503607000b50700e035115001c0d200c049045000000000012440086030302039480c0110b640009001ca03c1403810007099095242140c600790750352404400300500c1490280e40c1d00e4582031a040c0e8462501d114211068142800860641c0d84255018000d4901c0a03105c0d540d02030030625064400c409907020f40540c001c070b154400364018102740286004202c2035051003001141060204138003c104410b81800314940f1107078502140421b102617841c8a000081000c0c1c43c0c40d00759004108802079003100700380c030407075401d503140e100c1c41c816455210342900d082584070354403064012800d03242d11002d2040088c94281c001484030758065031544001c1100410040703120070303582c0818140c8e002644803280200310141c10003180d40d00750080840348100c1c0d240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 794969028 1250 794967778 794967781
    0xa0501080106021902150301090f06080708370305040e0a020315130b040c0e040b030a030f050a090f0e06180f0121020a08070f06050408031b010f050702071d 69
    0x10b00a60b1444a00001110750a04188200941d265140d1000c0b140d07000580c0550f8942c1c4622000f40a0321100c0140040940380240024200034042411810f640031000944003180d00304403104041d880e400c50001c02e0080451444000b15011120103007414400d0301d60680399803809040d5000703d100106154982401042009190445115001c20241c0e040381c1120000c0001c040040081500055180d0800e107800c0d1401001d640100b08481e80745021030301481402ca41a0505403900c0c0900b80040206695807100c06170b8a00580151595100300d00c1d00305459a910003d04980084540c0703d0050f03448a0300a02150b824140c154586211030000c40d15150b0401040340d81c1c91900500c1100c034003851180b05102e40700454480d01502e20f40043c80c4801e036039102c401298880308039212f48502c20148000000d10a406481907070704840c21600a1410045000401d001c600301140c0c060425560340c140626100c0c02c140300c0d290058005034003c0c1a010705069030313103100c40d464803110303000960340342d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 794970278 1250 794969028 794969039
    0x11d010c060c02010f1505040e01091e0f3503070909150306140a0b180109090311010518010c0320070c0503061810090b0f0925050a05010801 62
    0x40310400e5a4460380002d10700707003001401c0340107011401403144a241010b114125054000d07184c032056403021501040b404417580442402ca4565060044c02071000d44c5021303007045003c00742007960714010402d40800800e01e50325110458044008134080703038042102e44580b10022070850300b0021840c0d000928600701198060000d004c01c4c864415410b8644084040c1c203c04100c03013000550b8407020074400c4d000e0078904107001003002c40384120300c0c51a007101841d8902d40488030407106000006415241c1c0d003424000030191001140c15800d00c240e038600900490350034403425226076030481c40101660845140c40e401d45070800c924200309400c0500c02c02c0c080040300e49902070fa841c03a00b950796075035805243c0a0040300c1254412a0702d8080c103002c2200c43d09a00307000005c0d00300441c4c151918101e0700c4000c00100c4420100241c03600f00400d001580280801d01d566401032008070458445454040484802c20300200d40011203410a540410450401c182702801510090820045960614 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 794971528 1250 794970278 794970287
    0xa03060510081801020408030d290a030803040f02060a0309020a0e090d030e0a050d080702190b22020a080c09091b0d110d0309060e0f01120e03090a14011d01 69
    0x2a00210402101d01034490b03e250095041300c000307110020a0340d032244030040004005143e0714500410001e0180c00381e01404d5243c640902c020000200013031049419525250240e400c014022070b2203002150001016a4440d800740001000c02d0350301186a890510511104004c280c0c401d00110110b2828400d0f6041c000c990b541204803145800100300307071a05109071412541104c09031560103103200240810745e00c1001c20f8400c82c925000c030b8480c511b0866101d0f415021410000d8195818240480c072035482c100c000f420600410803909009249540008518004c194014601a807142c9442c0c0303070500b000016954480e5081015110410b00c18010081c20030481c80128801c040398035038801080000d42c1c400e00c50f11005000c01c070715109a1314024040c00d07454040d003004184036026004903441c1c0015251100d00040e540d400904401c0981d0f10083c01c203c1c2d40728400c42c0014407010740c050f2a44903007007009141c050561000c0c0580f010024100102a45110360b41044000100200340d822 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 794972778 1250 794971528 794971531
    0x311010f0e060a140706020415080103050703030309050321180a050604020904082701080a020703090e190f0603061413081b060711010c110601090f021606020a0306051008 75
    0x151040d560380da00f200c1c022948101c40032540d90607400d000c00c502c0c0a00806070b000c0c10a9460101104102004128040d0b41c1c68609100003070803507000f03803c10f0001a201c1d411812079130740700300c00312414680104045402012014110214480ca400400c034404200d0032901800c402d06d000a8202c0f0342068841e603455203030051000c1c1c0200c0034000420100315402e011100a05035550044403c2e0502402503e442a81d10180d18002000c040108400d0703c403c0c804c0321340c11a03260b100c05c814103191004a0710108070003000e0664400300c803254003001c01038038052440444233400740014a14158a007550072610395110044840b40301000700052081c0480e411050a500901d003640c80b5000501c5c0c009105004240409003406405d007400542604080110590342c0244000d1054020a0504590241100c0c45403403440d0300175001000400b04581c40000b000c01100760140ca054140d040d40d1426801c50321088a06a41c0002c01044641d0b041c410f03000900421582035072521103641c2d004101000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 794974028 1250 794972778 794972807
    0x709020906091e030307080304200d1101020c03190605070302090307060e031f0903120203070509010309060902062b05011401271508010807060504061124010311010f 73
    0x1070074140c0050070f110003540d0001c1c8000c000c0860399924021b16003500386800a0341d00f100d1100c100d010036081e942a201a8810815000d0400d000e012a02e45030080f001803070401c164154052100d50b00303100d46050007810072280c0c1c00445604512701500e007800c102e8000602c034004140c810301594000e44c0d408240384044500614004901d4803141d00040e0a18502c2c0039590030a2010004140b601805034000701400c50007502c8540f24403c40708190001c0c1e1104030b44040c001081002409542e41c003e500229840d8003605000446180d20350201c0c030070794800d012840742000820590b421800040c0522204510680c1043c01294500340c4c000845114010030581405008488050307440c1002034401c0c0316090715506004a186c1e510030385544003220140c40400175040c00004200e1100000c0c4040460b403140d82c0d124a010302e002c1040300c400300081404081800782e9450301c94084c50b0220410412880f40c08400c02652640c1380010b2104a503865407130602c40000d03001200c0315040b500d034521460317 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 794975278 1250 794974028 794974039
    0x151002030406021045061406010c050607110708070825080304050d03050c07060306090b0f031b060409060e070306090c0206040308090c15070b1003050703080703110109060c02070902090609 83
    0x603148030807821040000b174020000c580152551418012640c0080081c0b42d80926075401c2a150400112600b01d01c00303001401590105c4003045070310740f2500d241004421002d050f181550b40307849400d82414850303400700016900103989070b82800c40d040d18001c072036101d0100c0241c402d40307807800003a202d00985c4103040c45040c8021458041c14054000c83d408a509141902c1d0003039100c94010b402441e090207a0300d034403417614504030000e003809100d0319903050004000705661400c142c403145e881c100008101c0d0b00b26100b07100002c1c01c0c185030701800c070103428002030200b99841c16080c01000c4039090780c80840490300382154841c0c2e4030340104809170095050b141c240041e55070712014500d040c3d107228002c0d0300300a080002d0b8800803240000b0340030303091250b80204200e0300c8180d0341055030661804040c00c280c100c803104000255001c070007800100d100742003421412100b60701a608403124000140da0ba40d840d0289242e1082d418007408014005008086082801d000d02003403c500a1070340701e90048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 794976528 1250 794975278 794975351
    0x20915041a03070e18150d1505071404120201080601080411240a05040f08030717030601021603051f051303050d0b060714120a0e091510020304060210 66
    0x603104089040300c5802c003405405c030708001500720b05200e4004580c02c0d900b1800c1500700c1422450a00d28801e5400d812024000c004e05451a030000104000f41841c010300c407135503030250b184840c4440903100400e01280c03140e00da80c0060001610f00380c0020400d03030401510900300400105240c8058800c3c6038192104192401d8074900d04111281002070049000404a445102c0c5c0340e200e4000c00941e039015040302d40040c0e9031004582d4074010b0308402040c2036680ba20b01400d4400d8140510740c480c00502c102e81c0c2400042000d003c4540c01500140c07100d030003456115801e03441c40121220b248540038010070042c501491202490b1702125002010480000f41c1c0803070106c1140c00c030030030000b00204220303070303c030098946010141170341158032445000e501c0358400c5000c1518103a4250241688905522559060400c0190b0500602c00b0009103c01c01c0841840e4403050402107004405400866445080440c081d25100503d038406000e20b0420802c51410780903c031b41e6588500d44200740034100d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 794977778 1250 794976528 794976541
    0x90a08030f060a03060e010c030e010902030d120212010608060405070c032f030c060712051006031d010606020115120210082a040302090603030909041e0503030a020915041a03 77
    0xd00f0255072014082c2d6040011b258800881980440444591034030100456031000c80c14900ba20520200030358545c1041451400d698002c20465000a907140001441d0001207408064030903401c0c0c12100014044e00104103640c01c0c207101c0c07540c204e201030800041c060190342e4000e01c03800110380001b040b00300304a085500010144e14168860801c13405603a00c03040c46007406035903080d00300c40400001304400b1030311002248074425680101191004c017601c0d9070625405602a00369402241d14481c2d03510900030b8076a5080c450a40540707074543c004100c00024049004144040303030003181e5024000c000c000016550f03003440c078075826010305080020384e8030800301f038010000c1107100c00070f00707008174030f21f09050446440100706481c402c54840d08941c90300001d0507540d004540d1619040800500820045107400c01d040d140340f0405101801a01d2441e03032103e0854006036118070806401040905851030441c00c001c0340c02e8030b50b004c80da090a107016030b0b08001c03401c80e400005074500c000001c00c14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 794979028 1250 794977778 794977789
    0xf100b0f1801141306080a0320060609060a030609150e0c1e0111070308070b010e0921090402161106070b04082d0a080901051005060d140c0304030206090a08030f06 72
    0x5001444c49010021581d4800506407a000d1a2008400040d04407012211201c0044030780d204c1000c450000700600d07502c82c0c0034082401805032401d6841500c0c8600000040c48030f0280402191092220502c00c6c800c000c0e100c010b5641617062855260440b5074151104d817940c94041307200700e02406411400410640041e00c801407040c21100c840c1c082c044000c001c0c0041c450040450398403801d00e04c0c0c0d1507030362001054140d2000380c800c010560012201c042d60048481c2404160101010720b40b0b2420b080346000400701d0f80980342d109c0c042c1c041d00e402a0144800d4031003840c4092819a8134624028032591005000b15004200500201c00450803041c0000d070054010181300c2d884406007809480f00c02c3c2d03422140c100006160004080c1c800140c003e01c4180200d40c01012921461823000b0300f0141084210341005000081a90f0307034181d4000400322620a86000c0d60240542960724203081c10000d050940040c01c840e89030744035130500c900260305402266800381e1544000421902c62000055 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 794980278 1250 794979028 794979049
    0x1b0d0204050402060405060f07110319030e01110601170c0907020d121506030911030d020d0f11060a06060207060804150504030c0203010915060812030a0e0f100b0f180114 75
    0x940010010a8081d5494003c800800c0d074603000c1c80ad00c07a01000418100b503903498849004111170b868100c40380c17002a01031051030341044014100410300c445100502854154242c0c440c0c40025803a1005402d02d00341480404201e00c1c080d00c1c2c0d49040e14043c03002954030010b49005c6000c000000010452a40840d400442d09600840c9450321440c4d82c0c80c002000381952503001d407a0306d403901d40e21003180e20b0b0005080782208002d030044c0c07a150307032103079000c2c2c403000c0c030011041080c4a42141d10401c0f0402c02d21603070b4400c2c4010751000447d0360a20340d00a241c00c2c0c0c103030081d03007c0c4400c04c018040070540d2114001003078050100d003c2103954481c82c045500860030030009415600f82104001000310b4411424901d0038411820000740e55113210f6940e03140d44035461049241001c10104480c00b01c250040e07114007c000341101c0d0454140c0d406145412501e48080e00c80c0c542d80c8113400ba4500c2c00e41410814500300700c50602c600450b15038107a02820f01132003003a4000c0c01010007135045842d02c0307051f603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 794981528 1250 794980278 794980289
    0x15020109120c02032e230615040806010f0312020d020c0d0f0f11030d090e060d1109090d0806120c0d060b0a0f08070905040f06050c0d020a0e031b0d02040504020604 72
    0x204026460500b0711a920100305c0000344001d42012040ca91600161860301c6003101103141c42d280a4480c0c81c02d0224840d09018095407801c820000400d10300404c1001030b008140c5070300c2c0441c02501d9410300c9450041c250304814110b400400907000040d50005120b001c2100c100c80c0c1d190045030f1303031a18201c0c9001c112401041201c440708410140803010580b020403500130f400342c800110008804586c200400e000f84464410180701042c10b9081001c00004500d2280088d00b06402001c0001030b03c101c42210864039a5010504c1455125071000b92035030004400d80d01d1310001c1d054010450f884468860b4420b000744140d0106001784031440d005162201000380800843e21348884c01e51095a0311400750005d240725100d80026103032110720a0720300c07903034001c1d0943d54001c1d040c2d40c0d500081c5c0700c0500480d180007024829081108030a2009000758000b689680c0010b152481c14135080c20b00c1400310f44080407004044040d039440b20384000da402541124001400d0742c03140f0000b0690702a40d0001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 794982778 1250 794981528 794981563
    0x310090e030306041410030807020303040e131407031a100e010603060801180b011a0408030a0309020f090601082a070b0f0c04050d110103020c0a0c15020109120c0203 73
    0x5040040c0008401540903607002d4909010001c6403010b030101d06441510240300c1803c00c10000c0011590a00180881503c004c080e40d20b8190b84804514801c0c4090f42c42c0c0704a04050500401042000560500b582840b08094011301d40355441d0a0088081841012903c807241c000051030b02502c0d00f105d03805090260341d80412561241002002480c150158850541ca00121042c0d00340b60841d180807196131200350311106a0074000c507407210555654a6000424040c080401d44401c140301900d044682e03a900062211b0305c03401008004010301900602405d003220511100e070364001040c5510801c107040314240c0e241c01004a24007251040303050210010041240c82c1080404200c481c018040183c56404545921198004e1440744c0d1017466485039900c0b40c400002058801d510b155940c050400500748145444900e082442d02e031000c440c4000c01200c1441411280901d1054a80c07080c402040030314682e51340c05003002584c0050000740b00500381c41c102159420000c118880850700c20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 794984028 1250 794982778 794982791
    0x1090609140f120405040b0d050604112e0302030717091c08150f04090206120a110a0e0d022e2606100302210f130b010b031009 56
    0x70404410807224440740c00e280600502d180d02a000010f4a1070032030508200301386414588030401c8002c2c0b044e4a45290000424030588020410612072680f0a5018a07018050103085508209103140705426400c81801480155840000354207000c180c92072040c100141eaa131500c00003502c0f44501013528000a81c40002041480034010405040d40c20b400d410355001151180003e40b80850101e9148544254640c03848042d883e116048046640b80135200081e0a4041c1e0042840e030360100c1003e10400401c041807040380700c4036100d048030341246035111500307004000300010080e0002600e400d200f462808040760030f55070391301c4840441c0118140030f0150700b1010701a41d40c5406c25412240c02040301240038200d004000ca014114800c2c2c00303801c07420760b6a100f201304103a03062481c41c071000f01a42800000784040e0200030743d83e5210403070303d0224010301d040c4624800b400d000a0006841e40050384440000440e178802e040e05480980700c1e00781e01ca50311915210720000d10740c0e000e0b0014508114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 794985278 1250 794984028 794984033
    0x2070f02010e06270a060806090708041104020406020a030f030204140d02040f2a020a0822030212030d050606071a0a02131401170403020607051c05090d1107080613030201090609 78
    0x501d04500130083d1450007025680b600f05561400e42168895000600070000401c00351040a025500501c604014403030144846c01040490704076800c20009a4041d0350a03030140764000070150590307002d601d0103503c2c1a08019842c0442001c14010b40c2c000d41100c2544401c56640740c000320781c41000700c8410000380448100340d0300e4030343d4428a44000500461209144035201003194290160072000e240e1601080400b0b0a030081c0d4102042400c04d00f124102000595885480c0d808100442c00215242d01c05071104600b01c0f00c0140c903140c0300e0802000000d00080c0f10324100d0720340ca07600594100c2c140d6118814a00a841003085d034441842440c132000c0381049200c1e201e4042d4202c01c0c0d030f4000600c15000501c103180e0506460190251380050002102107208200405070310401e08082c041c50380400c1600000e0710019117182c550384e04804000106075500003004010510781000800d4840c0c5030001840e00ca4001030400d40b901c2c00040003450a03d07000350080d202c1c2c168040010032902c107150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 794986528 1250 794985278 794985337
    0x91415010e0d2a0e1e090f070902030106120213060e0307090e0303180606010e091302060705010b120a0c05040c050f120603060a061a0306010c0b2802070f02010e06 72
    0xc2d0701c0d091141500807400f040342d1380c1c04000c40d8807500c541e41c210b00001d9004080e96412020082500c0d025202d0b1040c0c40043c1a0140442e600404c5803100140c0c50794105200a0580361111400c04900307441408496a03844040440c1030449016003000102c80312103501107420800690003144442c6e0400c1d44205140b600000118481e094131000300300440d0b0703c50030480d11502c0568082d8001703500e1031656001803601c810341a40003240701c064400f000c00c0d65400704400344c10191042d940c69565490428150a040c05440f5401001c00081d1401e09155680e10348285003d015185c002d583c3c0b10f010004e0301f401503086440c070745180c48a00b512000c0b035100c1c2d10203868080300d4a030700a00428000c1a140180350207440c080d280f500407404206036680b0788065181e04024205410400440a0800402c0007007620901034000d1501c10300120601c450351040ca0b0325640c0090070301c5841001000c003c44c9210480d00082682468800c43c1000c2c18000180d050240d04c0c0200501007201812804d00c0b90780 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 794987778 1250 794986528 794986583
    0x1e040e011712040605120c0c0d090905070206010e011a0f18010e0105130308091f02060103030806010819051308030c070303060b0f090d080408070609091415010e0d 72
    0x1107404a882844250701c0d98012802184a5a070100d107051042c8051180309258941e8050041002c0701d0410041e01c1b0b0711440e20714002c4040002c0341c00d5001c140a42d05a90045035400b59150004103081d52410004180508052044d82c1c40540322800c80800e0104900850303a0358980006c425488448505940c1d02d00071600d419070f40070507109804491554003510586071a0011803503100310491540c0c981406e25800102043d80c001c43c00c96140920000042d0070400a81c0554000c001660441c07501601112001d44010b05020440702040303003082242c0700b501d0200020503000f1a20351a0012a40c0c61803c07103030002002c01001104220f180000c0030702900c4d0541c041d5505000099680301049030318482c0824285000b1000c0080c1400d034104440e0360040d00d0b1154221502d010f42c0c48290600b040700640021002405e40d40c010040c40300c4900030202c000c3c01107600c1007031906058001d1541c040000740502d050040c2008099010307601c3c05a010074403504407d801121020301c02008004015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 794989028 1250 794987778 794987819
    0x606180608060a05040c0501110114040503042d12050a0212100c030b030303060925030c0e0301231e100302040c08040f080702060c0f011a03121e040e01 67
    0x142c2000030b85001c41070103003901460304240080c41050412004490f829a016000310f22507403503501c400e201c200d0070001140309a00500207940c0707980c1024a000d9401604a04291440c4605219102a501e034040e00d1012a40f5401c501d20144009181c19410181c1e5054080d501c4443c1c2c0800204250700820003502c0c400d0000350401450802c010240c0486801c0c4c2d055540541c42400010a942484400765401801402400401d1002e0b0861120b007103000024440000340c50750140b10704560003a000054444044000b80250354850405480d038460800503100c04031800400308494101e400c0341b05140503405100b1980619101c43c0c00180650144000c0b4052031400844601d031701d1140c03414a0280358009018500302c0030070f031a40c1c041070304941000d036446007007008043d10a600400842c3c458114480c004200034030042e50b102c8849520f000d150307009401c00200896600c00403400c58000b0394010010300220889100d02d9403003805503400c00311412200400118074091500b42c048101c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 794990278 1250 794989028 794989033
    0x3219020f0a050703060f150b04090b0607080a120e030c07030209010803030702060a15120b06010315050102030901031a09040803041203020a050702040c0c080a0914030a0b0408070606180608 83
    0x191035040c1da107070600030018280e030f00285420b000007074060f0440c6032250101ea0b0041800117081e480318003d43c2c01039103d01c00031003001804006040450086401da010101c0d10305052600310744614450f440703201e400c6030401030032070003000580166520020b5401058000c80752108a1a4481c960700c1034980426886458604000100440000116440b4020700c0e4090b25035500c82c200c118014001810b80f188031800503950210304e22040e040303058401c070b000d040400ea070b6042c8000050115501c910100141c070311400c00601582e40c002040703964280003884c0004005600c4683c43c90a44040008070703502150460911060208810203036005600800e0650f0302290f80000603001c070710a04020740081901407000350b000d49402d5000000e480054104410001010340d14100b070f40d840f145600000c00d00900051141c2e815a1070f00d00440c04040e070080504070038503100d040300e00070018030090141c100010b09100700801c1e508107800034200c03a08551501d11071005450003a0189010314074451 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 794991528 1250 794990278 794990293
    0x40906081612170d0f0e0c1c0f060c02010203040b1302030c0d030309210e030609190c03140114070807090e070212030117150106321902 60
    0x2600003140009401804601240d0802c1c5407410180c80c5903400710003507929050b40201221502900002031802000b004d000042211000d01c181088810000d422161030b030040c4140d100c41d8840c1008001e5000c00212907aa42c40000d250215007608107410080c00903081001202911f84c0540280d4041c0e4410f50300741403907035110801c60541e030b681004007035455445200d4200042c201010724480440c02403a02080703040060300c1d00c2d0320340c802c00e840541c8450b0000a80b0500a82c5c0a010510282e0049020784050b0515410071980d80d4504030f10880740b05045c405003410005800b00600046500c0014000b02d0360120f401e4500038095030f20626840240b0b1400505c030584a846c41c00d1085220b81c0340d84e50742c0c5007000030f0001014801803000055201d50062140503607020740145008000d002054510006451300440c240100d00904241c910000801031042c0341d0400f1004001204201d00c01d503105002c0c0702192105041c02d511404c001c00000f82c00598038034100104006103813590200d9040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 794992778 1250 794991528 794991539
    0x1e050304030f0b1e271e0607050f030a11090a0b0d05010e09030a0e01031514040f0e060c0706140f04020a06021f05090708032107020703031713080f040906 68
    0x14240c00b08409407211303402c2000601d01110320790b5161000c0c00860001098a5503001d20781e01e001d401c404503e0070482c9128120204500400620358414010f1400c1c42c104034030806584440e000141a00e120142c1740c4605406110404040e242401d900402029540b039456004240c031b42d0140900d481d00d14104000403403042e0150742070b540144181c0008601c1e02c0d401103030403244903e020b101e5904040d11741c2c0341140c1e84544400618080d010407a006c1d507180c2054000c203c12120160226032050f42880c551602c0100d0220b420b80d0300c480c102607880d41c1c4280500d00f1100606141c43c1d10722000e1a80414801c074620030076420303442644291491841c0319211003080c0c0e0b4604211000c3c24ad0715420080c07620f51402240c2005401000540449125603106d072403490840d08451a1011841004a4140c6d0500390507000346402c8034440c0003a0060078115140202000040701c041100d4050b800d0109018080444044140c0b5801103c4241c46820386461030715203612520664901901f0540003196 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 794994028 1250 794992778 794992801
    0x171e0c010c031b0807120203010f08060907050f1002122a0705130b0604050a0605070b010905040305040b180d06061406030105090f0c04030818011b0f1e050304030f0b 73
    0x1c0380f443c0602c07900c14003000c6500310350381e4100a003164108a1411014051503485001850290111420380e444481c24604070500d80240148909207a07402588200b01548444800980d142c40c1500c4029030540d90080c1030f0300c3c1203000e12421101c4040012101c1c800d82e02c0f82c082d10040000b2040c7c10313591111310105103644110314028594000501480b00b008180980d100e11407040e0094a060300b400d540303000103a10714540381d102402054001484104010f006600c0c0c602515204030100000c1c00c254800501c0f0340641c1c010503040340c03000961208005030110114594550040404005142c10314088010301481d20600010003403850300007030685000030a59050b16005015010303582e82d0075411004082001c0c0242070008405c00002c808580c54400070034960380894000007440c0034031800101404034102c45102142c004010f4040055031010020f141a41c010308072032031081e070048140d00f8004d01c14030000c002e480001000001c01044c4480071880724001d204415003503564044611 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 794995278 1250 794994028 794994041
    0x30905120a26070f05030915090c040501050a0803041a19020a210819020c031b07050418020409210908011a03030d0903020304030807140f0c010507171e0c010c03 71
    0xc004c541d99544581c5030a00c14005968041668412940c1000e070401a4115070801030780e840c880ca4000301107031885420a40503640c01001c0036541c003c1c03007918240c0f801c1d489000e24024480c40e10450301c9089550255103060380c0c2080c3c0707625400021007012407000ba640313a6292000311032141c0009039882900c4d02c054040c00201603903482d003010303036900d1012a4246800307400b4825400369007408035111013241040034004d000617520301d8005460700c810b00c03545047c1c0c040d400749219504004410816503485540611050350507103010602c103079103143c580c02c42c801d0181c050006c001342011503100c2c2d5512400f2402103c0c50000208003513048447e00b00400196a50072503015401003014007080b8489601c440ea07564042c3c81640e0405440340e807200318a1340240781c1910f128922840100540c40e05010342c662682c281d0b00144221100e800000e8120f000d00f01010317104100b0b102005000745000340464100444920002c05000502c119045540e0010006000a50b1070300c2d1940ad000381c064800e15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 794996528 1250 794995278 794995291
    0x804050c1f050313060501150e15120a060302040509010b210c0d06021201030602040839011e020f12030c04031509153207030905120a26 60
    0x800008401400540c0c083d40050140c03c2c2d40044c248546001c20340911806018241000d800c0710241555040103140194103c031840c03083c400c180903410461421750844481040c050600d0803940d8405002c0b00050003240e0000e90041d00344010070032182410341c454051580211481101c1a822240c289040040b1a4540c0303140d0784481c030b07414220301e02580e10070b0000d4070401d009490440d180303003c2c24a9000a900c100c41d00742d004142030100817000d00107000330a9204e581c04e2284840c40850500c0c1821101507103403840c40172059010780d41d10983c482407003c000c2980300d81030300d010030b40000e5032510003c2108480d07000d519252000307410301100712400f8110707803042035052506507110b84070058000341c2100d0305540e680b80001c2c00104201c005620940c1040710008840c0323544054507040d005006654500c1580c259454424180180d400315040300161034002a0307240039207055403825806107030101038001c000c22034001007a0b104070074983c0e8444164031807400925801a59641800c19100c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 794997778 1250 794996528 794996569
    0x140f0703030902032a010306060509010e041a0312030411010903030e0907030e1005100b09011205060301060b0c011a0916030c0224160c0312050c040b04060804050c 72
    0x10002003440780c0c11140d4402c0c0001d0503680c8a01e03028007115212074001141000962110680149560301440344000030b01460800e545071841740d000090221101c05c1110784103e6540700c8412034602c915200c02e40801d0050100c50314a0840d841030380403504110380450f01a407070700301ca0b995154810b25042d0102ca80c5a03c4035007001409004001d0050001407600e030406590780c0d0392542c0e001d001c00a03072503da6451503000489041c2001c005900c0d01003500580203001081096848990b444040700d40d586035500030002d45510340c0c0000a02401c903070f03403042c0941c80010402904d820390640c00850010b5064207406010328404042c00f002c104202c0d0b80c440c046c148229181580744c0a50810071440c100380c41500e8140110102c60032140301c3e291151030400462000b080310005904a2007410740b4050308110748001c51a5400902d420089001b040c0510313164004504409100b4042e60083d2070345e90b24aa85464440c0c0c1c00030308120040f20207131070901c00c00d00941301d81e0400d44000c0c91000c122182 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 794999028 1250 794997778 794997787
    0x503040605070f0606030f030206070f1211040b040803190c1104020711090a020d060f260a0222150e1612051608012709061407030c140f 60
    0x266000d8102c03940c00d84a403040c03501e034100003e80610411002d148500c1000d0480081420001d240400090080307050105030501e4010050304191380c3c00b0030390286e082c085544440c43e6240425030186601201020401240200da032800100180c40425481d140342981740d202c0107801c41d620024008054084900d542c2c0803456410f0680044c40c1c800d001d41c03841c0c8000c00708840452182d240460b01c040b0900d80c0815034078052605c2d80501d000911402c0e880700030050030b06045041d184182003090001241103080c50f04168801d00c04010000c0e001010400c0e1042e288203094240704000301c1e012900362510381e1000448007440350010640e90814a80c0506e070b980d0813160346a14142d03140d40c2c0140031041d0740740300c0807110714043c262190903020403401e0200c109003400f40c071410062300320555200b17664207105141c0780308042c6850081040303000400d00018504011001340381104090301c440102d5410480f00c1c41d01a0840900181542e9034680040300c058140f82080c0107248081d03800020820 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 795000278 1250 794999028 794999039
    0xa1503050d0e090f0601052512031d01061518030c0b120702060709050f0f1c0b06150720090901060e0903090a05280311040c030b0108190f02270d050304 67
    0x1d00c201c92194030b03ca0350400b08d9807541851078140325003ca001907102d807070300f400d034074402840d81d410b540d40c9200a10005043c078441440310215580520308004446a0014040441190000086401890a000d220f4444403510300c503070f21071500458001e8010012400551001070103074440e03212980d80824142c00e0108002d1000705440d06540d22410f00e000c0b0036926500c01d010a018503c48844051041d5101c3c41c002c00d923100300520180c030494110442c180d0441030502140c03071050b03012184000750b2207200018051000b0300d1f00e1594000024408101c0d007283c1c154001004d403003c12aa4040c641d850f0809a581d83c07141c240501e400c44d03590384082182341090f1015403c9025030000380b130b001111054100180d42066031013030315070703031495154621503041c903125210791082c0b81c0c0b038144030810200c0300217401d00c24080c11100a0103540d0140302c800c001c1030b5220340c20820100100b0740da503482220302d258042c50f0b00c008881005600450348609803503c034201c20f941c1580000036609082c6001e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 795001528 1250 795000278 795000307
    0x180d0e061603020102190201271a060301060b0d020c0c0f030304090e07090c020a110a030209070f020a0605270d080c07060207020d081206040e03030a1503050d0e090f060105 76
    0x1e0324201c0543d9002e125440381c800c031200540004500c103600028070301d240d50201820105140288001c10000b00240c0004600403d00340e8a000249510703188450729000e010a00500303055218a06005011035140300440c1950020008903040b1412220035801aa04111f42e005540751900c0e41540100020409545183c00c0300c00d18509601c02c0e52852591400030f00250f4100080a80050b00416542c90810a1540e20000c00c0c41c000d8488441d000c0c01d640c0420f86c1458054602814070840c500c0e4201c640d4070030007100b100c5aa1100342840a8140381142c1c0c110f4010312000010180d424101c188100d050000340802c0e07400e42c0f591440c0e810b440703440529046502201c000c1c3c0d030f455000c11030315001d40c5070710f0408040d05c0c0c455603129a031384480382803018822002030300842c403071030614040440ba031400000b626005032200d6400a6038000069030b850416000d640020100d010b00e1403060a01c41d0000564182c00c242690b120601340d0300c007801000418000c0380c510740450307014003336076503000d016 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 795002778 1250 795001528 795001567
    0xb0916060503150d02060d061703030915091015050102100b18070c0b0c0a0306091802040f0b041401080c0904050a120908060a0606020d0302040f0b03040203030f03180d0e06 76
    0x41c0c00300111134000e40214030660b02c402010042661505c41c100f09482d000b84852210b0300c03000d4091800c40c2401c4801d60f0b1500c3c120044150380a6500c804a01145003c0c4506203403c00308400c200314550b190107203040700140602c12580076000f1110008110320481c00f030500d8200f0024840e05020312011500a0700d0030000c3e05031010451882a200000351601450b00d00600c1004180c6071600c404a10050a036240e43c2c01c186030103400c145601d90b1081441c40b0388051242e0403a40844d01c0d40c24014881d00030001060310680c014201444c154545040c4100303a4103036200c240036502034444500c00d00060450540b03000740710747d00095040d00401c0400322000780d80c0e0340602d004042a0360b11707180d042c03a021090f50303980c401c42e56921081001c585c0401151240b28514241076052900d8040c080f03140403c42d10807108204070000010301195028421142541c005070146d5480341007a045240014001440c403441c2c0b031003228a504450b0303005a600141030340700201340b5031500f1040c16034411070000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 795004028 1250 795002778 795002821
    0xb0d050708010f060b0405310e1902011d0411040e0405190506190f091a09060c0f0c031303350406050702010242090a1b0807030b0916060503 62
    0x30a204804154400492384811150342c40c00e01240708000c603034800d0b081c0a21700c1c084084100500d044400140d810103668044160420b100d072081030802c0e400325026145c245000100441c001a02180580301120204e000318001c0701101c3e6613048440e41c20302c1d241d0888402500540c801800110031046107040c1d140d80c80091203001c6200c00110804c10183c0c2c00c000c4040301d040d100b4080d100346500011401c5030b032120031440104001c1c1490280840c443c400c88101140c0200002090b20086a04108442c4841d107180c0451402c240d40b403c0100b620359500309480207050004040c03031009000680e50880042140c1e0a083c41d2900d010000c0d6065071000e0b4049055016910400040750414544a05440760080c4225030422407c160b801c400d803100780d10400c0d44140d20051100420b000210102459408012118142c0d610300d00b01d4405841e1307034046003040c810030304007004111106502e580620401c030708403190740c0960f01e00c0070562046802100000341c1c0c1400021641802400c40c10714190 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 795005278 1250 795004028 795004069
    0x628060f0e0705090a090b0111010c120b061201080f07090207020f0405060f031b180412050a090f1e1d19020708220e040f060c030b0d050708010f060b0405 68
    0x40113808965061516802060360300e070307078403079508840d600441c1c0c001c030440480e07008000300b0540d8a80501895501d0220110640ea46c0c80d035031205480b0003085401c0001050311010107076079a46903180c0da659200c01c07203401a00070a0f0b4001100130031402610b1006500400c0d6004000441050100500e0001c0042d60b01082005d039100b09030701e0502c0081c01504c02911951070b40904082440812001284003038004009482000081120240130307840810311450f015944040d410801c80300140d481e00801c43c022500f4000084000c814611140a8030034044844030107651182800b40e005541601009184000e10008499182c04c0300b0725018183d26a50040c2003882680340c180603908840907110f5a84004400c46020030072407240301e8001c081c0c1402d0001c60745081e5454825040c51035200070161901d0f11000a48203011b0b411200e5840c0000e0541030301e41001e030034025500c40712071103072000315480d2210604085500d40106419180100040b91030f02c1e14007402d01468880c0d020944e041319 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 795006528 1250 795005278 795005287
    0x2070608150d03030f15180b212407050306010c080d1a240f0708090d12030507021c0c05070305070e010f090221040c0302030628060f0e0705 62
    0x1d540c2c005140150078080d0740c0002e0b254404542d0f2100300d5148110b5000c0e8400501c034100000428400b2440080c03803c81004200e0025410101d030a11526070500080c6440c03100111a0b282c900144102d02014450b180500f0354002e485d1407071110405841d0100080c40800c0015101c1d4020049140c43c0e6120300d000b1440c0c000c0041d8450708480134401d80011500c51903800c0950f9140640704c02d000004041e4426800d00451001109a44075582181140c400b000c40c1d680103006460b13081c3c406100010380050000e0220346408501d1030750211107980440c0c07034400494076482c40000c0090031040702a10007001c1103c0c024050791000c514581c00c0300c0c217115040c0301000040b414040000100221000e05903a54108206003c10140d590004503100c0e01c1402264038400090070904000000002138030210b46841c14941e409500700c1d000a50148103900034091540c00300e01418500d107040d02000900c0a108401450035a001442400420390300f04800384440c5000440c42a001030302c03400c0580c40c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 795007778 1250 795006528 795006571
    0x60e0f030a030c2705010c1e0b07110a020307140301061d04020a0b0903030703050d0f0903210510030605070203040e0103050309330a030e10060f060503040302070608 73
    0xc56000100080001c0d403180300c44107009400c0041541c02001000307403404054210410340031010101d1190604220340481c00313005001c0006822400c0303e60000c03009940d01d01c241050640c1004c245d41e01400030340700482481d40010040b0702510810381c0100500005890f041c00881d6031700002e1001070303240d546e8040005012007a05104c04040a400800110700c0c038040c01000405000d640c4100c1c200c035810803501041e5940441102e419603850300b08a0303240d07101c881d042c40c000c2c1840140b11446629202c0c10400b490380004030b40002c3c0c805114456180e2001401c0202910300a5070f071541c04c1141c00f80d0900003d030141e00200e81c00800340c4100c0303040c150f03280300c07101c500c01081c2d109440036040010980c0c0039040a01c00c111004003509401c0100b000c58400d1011000c844500c031801d889004513109210b80c0c840d800001842c2010011607075010610514a0b008158034441c0000c3c1c06407070f50000400a0081c0107880c41990103030098601e1510304072007907a9000340201103101c07400782075144119 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 795009028 1250 795007778 795007783
    0x60305090102220f05030f03030a0911091003060e070609120609051605010306091107020d081911070e09030a0302030a110c060403020c09130312020f03010816090b010c060e0f 77
    0x2000b43c004807140032000d103081808072810f5103580200740690082c41c0b06420502000003160b800c07804100c000101440320741006c0c4040c45540c1030295024446c0803d00c071901c0300b401d15180540380240300400520041211895aa270407a101e4040822982901000039280d0700000c4030501d8000c001c089284036065036030500340301510700004245083d032742052150703580c18480c64000d8031603407800700b161071004c00b15038035203025280000703105507102103800c1c040090800507520814407810010700803c0f2215030150114500740ca100d8018440d0703160024850304100d50039801506520051494a50440822806540003c020100654039081c00e0719881040600500707200715807802804031030916180003030501207481d51507441440c0c0a414400c020768010b084506143d49801d0050035010b40c4030f8004041c0c02150b0301025814004000022180004141d8403481c00741c0444280019454a909a04403180407410f18009410000980f000900542c0010240e22480d0101c941c444003883d107003131 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 795010278 1250 795009028 795009067
    0xd0c0f05011e18330507030915090b01050d0c0803160302010c0206090706032f0a090614030a09030c050a05010209010e03070e040809360f060a060305090102 69
    0x2600c442c068000c1c816020039849007a403500c0980e20b001c0d181000540b1240302107020480d44000c018001030303060440628103400b0041c1d54005000a10072441d210401074014260054284c80ea521184540f6048810a2040300031031907020f10001c1c043e900300300500c4401d04200c00c04403030f401d43c1800085003600040001e0b00c00b5101812040c038901441d03280013406d403880315034404c0a40d401901881031071030000c076030041031799940d21700003e4400c01d01c1043c00030440d1140207640450110b03448580004a040f009009280c1345840e5280c16950310300d802c0710b0f070703450f460012090020240041081e90001c1e401452502e40a49006050140315858a900b800a990004c8441ea07500007101d828030358002c41800120903080300904100c910b0034071181c03108a001803000b040c0301070000e21840d0790ba480b1b00c040c0c1900d03074216603c42c400da04420b410107000003410807030b0344079031040000151926181a00d01ca114030805088961300f2454a0b4041c0c019040c060580b00840d50280101c0c1071035001e01c0380c5034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 795011528 1250 795010278 795010301
    0xc060c0f121003170702150306030a0c08060403111b040b1201050a1406010e0d020405041b12030e060405011e050d2301080d0c1115070b0a0614030d0c0f0501 69
    0x55400c0d1031841d00c4160880500b505507504c540038462100565117020881c10079100010300b140c0e41f95102000030f8101040311800500c6007a9140300031030700000024035207214a21030340313a40000c402d8808405960340403215220910350006680f00429080c203030402c0f40b441d0f074064000000c0582611440c0d081d80c03801c96030521001c1c0c2d18951038101c01c00d4410041d03000302c2c0a080c00c07148000060040745500f040c949010b1302580d100d0010804008104080c0740079241040038203200540c5458400b42c00100c4100203500050624030b03d009a454074100315802c0b180140c48244031010383c10340d85807000460f00b02180138040244146001303400030b4000d400440d0079075080034510954020311200030300c03010381003450107a01c541e60400195030841c2c210100755400c030309034905d01e001d01c00018100c1d40c210481c440c82c0c5d00e4003049820801c140c2070541406011642d005125243c0c551980d1200005191580c540c5607112014010010340250314000c02035000301c00341188018552605400e4405401d40d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 795012778 1250 795011528 795011551
    0x92118061d010e060d09050a0f0b040b070e0f13110409020c100507080f0a090219051c080f0c010e030f030105030d08040507060323010303030615050c060c0f12 70
    0x500d88406052a1828501e580900349034401c0d04890b4085a414003403080441034241c3d951010300d052000800641c0001a0312007606490000356240c001d500d60720685003201c480d070f101d0740840e140380c1c041c1a81d8030781c5820182c450520380610004008110b81c80640052446655112412030488454010b00c094400e0340400360b907503006a0b003440d10303200b00342d80350107880741c80c10050280d40323540b041c9560380220840c0050340b00358503070050000050060900083d8403103000c80c00c1c2d0010f00b1a40640e039048400840c0c01c08000b17646800d400c50010dc2c130001c028400d05040080050b54501d150213811050a91400001c88130084200d0600e10784c000302600c0141c90b004001006940740420041e000c09005261003000ca0030156190b070b54841b4103000345424551600303185004051143c0c28080500e20f15011340032a5652800c0c0500107019a00552917103189907540511014002c01c121078240b160680109101c0d038402da1815001d030000c40c24403035148010080710a580b05080c1d00e00b07000760b680055 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 795014028 1250 795012778 795012797
    0x11b2004150e010f06030209240d02030406050105040f1a1c020909160b0708040e130b1305010c02011e050c0702090f060a0f1508100b07150c0309211806 67
    0x2e082c403041303030703140d100d00100f42c01041000c1c00c50311444c3d01c42a5107004e04040100a081880f21b0f007895000ba044000f003000e20120400050003030030740207981222025142001101c40d0014540c0650307a00c0030840303255021415000c041d60409540e040c080042c1040f42c40c40091441e40040c8805209444a50181d40034031110120740c44584e2425004083c0840301d0b81c6441c4946c1e030303690344c0d9002d11711030900b560498500040f51843c2417103644140308d178494010a8249800c0c10344031882130b0240000d0703415600e0311b61248444d40c0144034803030983c21390034040407041c1004441c041c0038050050180600c004184103400058440031030007400303600c000e107601c055842c3c51024000b601d41c0544c828910b6140c00f4108100480c18800d22401448030b0340f61006e059903a420109451003031550102804060004a040c2030020010b034840c0e0030000c800e014415141c62081c110295124581c026042e00c003400440c03212500040d040c24412149410138a954111103559111070305410b038094004240c0307045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 795015278 1250 795014028 795014039
    0x1c20040f021b0706020d030e0c0405070201140606031b0906041d0109110f0304081b2e02030f071d1903050c0d08040b0a0908030403050c011b2004150e01 67
    0x2900e06003103450030340c0100b070140c1c44c0c510000c0d521b9000b00140c0342816510a50034001e031401b40b0080c8003840380500301b4040d60800102c001c2c000c010806070000c04003401c00110b25603182902c22240903d010300b1002c1360714200c0e94400040e1758005500b0603804201008005441d00c0c22980f8030b1000802c1101041882d0714020540081d40e140c3d414506180d4000c000c21a0441040740c1903075000358000e528181c031156109022003001420b0f00140131184a82440d2448280d24011711294860540c08081caa80c212182d5140c16400280d0b02405620488e10005406a1040000064881080c1d50750301210a45101107402c100540c4403501c090b0b4403c2e003041c4107110003045800c036034500503900d03044a030a454a0704255801540101d2048440c0014201032682c890340e084009030444c00c00340c980c3e45503645040c0766615607102000e804584c3c05000c0c1240000081c02881c4a10381100500705000c0c041745c0410404403251481030383c019950700000e5011403400c1d201c20050144007400316810350414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 795016528 1250 795015278 795015307
    0x61505150c03310f030b07031815020d0c0306050d0b06030a0807120f0203160b0601050f0c010e070b040807060305060105040b0c01050103060e0d090e07031b1d1c20040f02 75
    0x2034010b01c5500345903460400015015040b910f034040c600b8a0006404d4444504d01c0d80c0b00307684500d02908448085020146410480c0d0007030cc2d0262085400300280010032106a080d90b03500e12603107900624961081010a80740440c180e13011400500b41d640320701303d940d02e015940d084050181c07600e40c0030003800701070b041e00419800c0230012680010b6052407928103010246c06d02400c03008050840d06404501305034099000d892800100c299201c1e15089030350b922030b00070618039180307003d86d201d41c050004100310084121020380b02d28030013629129007001d105802412003c1e0583d41006800c0000281040038100603007080f20340070300041807a5145044c01c0c4140e418040d0f8a018540011900f07040f05a085414001107d016018002c07466903442825401400d1501420b4290f611288084000756408440300e0540803102c814001d032060140d06003d0744101d210380508000e540c010034040400d400c4103003030b602d030392003001c09020308200400490700b6540000d91442460303402080058620741c06 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 795017778 1250 795016528 795016627
    0x106020d080f061e030102090d060f06270b030c15030a05070e0f0f18010e0f010806010f090b040b060c0a0c0b0702030d0c030c02030d050403061505150c03 68
    0x1805516071403401d010001400c1411050300e0808a444d524a52002c6034070290165500030200a03c0540b641e1401d05044016002e41358075011441d1a008000c02c131040c02c030400d43c03900e400c810000a540b035080f40808000b070a00400c1640c1c0340c860107080100d955650b8040403400c400c0301c00081e8517401c02040741403d4800242080c0d05020407041ca881050702c03290359924140c081200c20741c030580384407004140789401c03103036543c0c240741c0d001000030406111071800d0a0103071303441580e1200240c0e0303075407080380d20b410003809a001d001804000c20010503450340c10141c59150001c00c00a011003074440003403d80c1d848803019003c0ba41102001d2000c0c0718400318040b008007000382d40145401c0c0b03160300181d21051105e44100030b00c0039180800007814403c40320f880c4c4035980030741142c0d442c102d5600041d01c41d805c68030040360f680303091813542e0302c1040c4011005000c0fa40040d002170103007486503d42032240c1d00004222083c900c0b09001066459036200c032442c48910b0200c82d6010040e0031014040b020121 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 795019028 1250 795017778 795017791
    0xb0306090a0b09120a032c0d05070c0f03050303040b161d0303160b060112020915070f060218040506031903110f070909031103160206090f04050f1008011119030608060106020d08 78
    0x5644420071040c00c000c101400146c6551034141cae0766080628103400540d0301500142c1c03202c00400f00c0881000301c000300540c05980107510081095417038000c1100000788049050340050032401440186e000d80031080d403a10003000381943d0515020346462200c80d10088801d4860b044001c050090f10750300000c1d0010034079030100b415841d21506c080428901c0e140c80207a20300181000a500052203e200c4c628103032213500110079503850984c0d5100089007402c50b081544180d1909001c03a4041c0b40c0028881800138000101401240650700c069036840860f82152945006403094090001c2c4240000320180008400c0059503009030700300103080b926010310785042c0381c0c001c00045030940e0081703070f22005556045440554501702d002c0421142d039806066035400034242014428103200d800c441340e00c50304901e642c4114469a9908050a881001005c1e00d09614108001c109801c0e04044a0001030142c2c10f003c0b8442c0e0380c500350549810700903800840160041480147e0700d0384e004c40340340e40144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 795020278 1250 795019028 795019091
    0x405011403031905070f05070603060f0e0610140c0703050c0d0804090515040e010c030f1b080603010603021906020f070b030a09030306030c14040b0306090a0b09120a03 74
    0x59025020954900c582120b030007a5040001c2030030b83c40c0c2d00c120215101558003a960090044140c030b0120340d9805a4064680441d08010011600c0d40100070b008044540d081810300c250348030401400313521485070480b0001c100013030012140c900f00000080014404040007080c1d205e1031810701504050034221a14404d4004100744d0001c10f0540d03080d01c00781e5007102e10000e03540d1036110416441140350b804441d080ba04040e040302d002c46040d404044840f03e00d44041c055081c20b4166002111540c1004c01030108080200404044c0305000095100c40702400008a59840e5000151038020300c0600076904212400c090002682c18840400c0901c04040105111420000386100c203010042101c0380659032407004005051203034101070011034100290f1500d4903210040c500800340d021420500450030440d20407007a00f40010341034400c0b80c012014103401c1d20b082c0c1c2c0b2208040c1c0050451801417081c00d018031a122840f2000f00380d9202503031400038240c07510307019081030340f60461303042800341 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 795021528 1250 795020278 795020309
    0x8090a0314030a030f0c20192001020d091e050301050108030424020c01111006080705040e06093409090209150a18140406090204060b03041703100305030c0c040501 72
    0x150020f00000320000d81071810007e48810f2600f1034a4440e0840102d20395010032948002808844c0003041501060303503060044980e8002c00587e9901d90b011000c0000594405081103400d0001c130f0b80d03503003140390341200c003400958990020307003034407400e811018154000050400100d001220040348003845040440418000b00310084e464030f050086060501214409600d0210700c144500c40450790000310801080d5203032082160348900500445004502d06092680328000010781a4482d5146100501448440090b41c07080d91080fa402e441c1c1c078a41c200c03920584004259800d0000d8014844002210401c81c01041440f0002a01c241110080d0804500c01601d503070030030750143c0d040d82031401d000701c0d0b07881c91080041c00210f264200300300d210014003081144940043d51041d008640034424140c0351100d9462610060368010704094084050001c010005c02c05164000100c124103a6040e0340c0382c94031821940000e52007240fa410103580400249050301c5001e014011300880c01c1c4c1032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 795022778 1250 795021528 795021551
    0x212120106081f140d05150105010927090303020c060a0207290a0b1906091d0c04141c0f140607050a081005030d0504090c0c030c08090a0314030a030f 66
    0x8a0007030040d465404e4503d10265503a440d80c2c4d00010303a00341d100782201c0e42d05217183e144595040d000c1c05082c1c0002d000140008040d40a40e54140c0c035024014528100108484c3c5140c0050000240407800e040d024805a4031502e800d00980c0c0c4140311381a009a42c0d51000c0c6020341d0300d0a500f1010b00301c00205040c500c07080700440c980c00c6070301100c1c611001403c8051f4000040b10094580c01c1314a5041d40300001050044d8001c0c888811101140c41684a03000c2c2c216085003000401c86100705001d03810711007000b0725803030342e042d107881c0c41c4002d06007010303205100d0300f00ea07180d0b0360400c0107940484011858108100740d14144401132007034800031f03265a0034490402003491185c08080b0b0100101d2001042d540a0001140e00040c680241250012064600050007a1704203100d5030100b03904d400c004900707403401080100f03000da40c982d41d00c0c880c3e81550b507208a070913001100495081507000304080006102e1b42000074406810300000c50b111030802d10004d00b90307200c8030220382c6d4030303410103001018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 795024028 1250 795022778 795022831
    0xc050310120c0509070c021012051302010c1b180c20030f18030304080a0507060f080103021519030b10020114040f1a04080d050f06090403050901021212010608 70
    0xa460013116140303003d840f202c3d811680440a048043c0d44401242446004160001001c062081c1000e0f0244070980d0f600c60519205014403802a010999110701a40000c580c15400d00c20815164400010292140d08140ca00f503410066118100d03990a0704211a54101041d4903021041e079112298603500301c0107045d100c0c05501400340c0c0420380881c0c030300c80c101d0440da88183d00760400780407a038aa135600c03200c030356480392041c5065510380241c1202244c51842000290100c2c00315460b0011181d1869003848400c80c181103a1b00000d0314140404c4004407540c11200007101425070340031820700000307010003814215030b48d01c503825680f508801c4d6150000c0403440980c4590419903042e00d1170f60754203015200141d245141b00c080c28190080008201025014011621400070200442d60b0b80c04420303042d500e0140da1040c0e00985050000740024415401007500b600180705450000045440b400413070740215103c4201005448014011250b002e030700d4507446411641e01110b140150440c141c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 795025278 1250 795024028 795024053
    0x2102060601111b19170c01110a0c03080f1215090702070f090c11060c0706060b04030f020d140d031407050f040608040203010b0909010906050702010e03090d0f060c05031012 76
    0x740501d02c0d21329081104012110058001e000d01c3c195080ba9a0440e001c280c2c9654a10f00440d0125400151807001040c000515014060f8800c080c55589030960b16a0101a042089004e840120402c005080c4040d07504200340610803101028038081c00d281e0400603002070082959045501a25042215141f04e9a510b4129400c0c900d0014900503008002c6a282070071240707959881c42480c0034010228080d43c020000640140400c015a41d2110180d00041c46544000350250030000d0720307000985400030703017000d4082c402d08614241c060210309040c00c0180300080140402d9440c02c0b0211518400402154440721501c0e25900d00107507041c2082070380c0254002c0104010700900003c0c11920700b548580240d4400803d00c10b9030f4a8003011481c041c16600f41c007200c075141400c003c80c0509005000307000c440e42c06140030303505191a1000f48031003040c03400e0040e1505541d03500c0b5480411600e105d446042c81c00c59485a550740742029104a040f040755101602541d0120403205c04143c000000300c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 795026528 1250 795025278 795025333
    0x160f051b01030c09030f0602130e04060b1504030803060d2a0509041713090f020933090112091101170c07080904020921070f08070501030504210206060111 68
    0x9040900c860031f10034028020b03d17810540300d07400e060300400c9800340102100d1080384105402d0100314500c0b400d00c5040304660400315100c0905200c10300c005a0300001a5906c0381c0701a044102d450056100c800d000105010911405000361100c070490284005150300a80300a03030750140581003540d14003080a000243d604110b01c00030843c40f030302e00454603605c001851040300900c0502500c0400c031009503c020a00341c070908020300300140b4400d682c04003440c403c0c80106c48140c1900c06031030000c00e90703100d101c105041048602c0311508003026881001c080f6070040b84c0102070044c1110024000d040d039000c00b0b01018101d40d040003101e810b9102243c40403a84108000d032a861900003090280c000c1105603a4400b8900454003420303149409180324410058045440e6965503040c09072180485008150407500400d10601055009800c20746e08180300d001d00b01c0c0200150401401c18862800740c800068000d2001d0003000d60344078a881d040604864003501419601000051203030b400d031120b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 795027778 1250 795026528 795026543
    0x31511031302060f22060f080609070f020709062c040f020609012001091502130302040209030a02060c01050f06010807020a0f03111b03070902070203030d02160f051b01030c0903 78
    0x20007040740c601003d807400200d1000c00c005d904004088402c2c2142024020030000907180b00041110b94464a1254040c1002a241c201941ca80034011150036030640050ba056110741840007404040758851030008200c6d840d02c01c00444200d4881040b10801c4a01e40c040503a520b0701881301240700c891007076594507411940565244081001a188066552490701c1f000d4001042800350440c1034010745030381489940e40d42070600c03071302e07810408034043d540d450284080c1d02d920901c0141041c0e8002d000c100001030880e0a031152990000e251980101c20001c4140d441c0c2c004d00c8641000210003d42004007401c00f41401d103041c100080da40e0990785070280c5100302801e03210041c113024924447e14001808140d5514480d03000c20780501941e61116140244588040050b14880038802d58899503030043c05149000c2c40004540f010b0f4200c000b404d102c85291142c14400514990310840030300d032042c4003818041c2410403459002e03e51440310709040c14109200000459072000140341035a030b01192 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 795029028 1250 795027778 795027787
    0x31e07050316030515150a17010c1404060305270d0329100306170c0108060306040206120a060b04090605030606150a03020c03070204020c011413081b010e010603151103130206 77
    0x5145480080b4202240c001d034540d00d02050b0b1008c05071020751000303440b00003404124000207048805420100420715501c02c180011b001c81442070308100d8024400201d40e00f00300a50f100c29141e100c00311030281c1c03801c0c0c2c40350300e07003611494044c001c5181590700c0c00006000240500e40184001c5546540c2602c503250b130b1030440181034001d510035000750403451a01e415401e2071051856990446200c0c20b40441c0004001807494034000032260311aa501501903410b000c50310b02d00401044026140c99510b40d2a000003082211030103000d00010048580d011800500e00002d060825038013030034450003018006c29284030210240b04070f40030b51106113401660b4940036407510742103002e5040029481350000816031405c032415000010791070f80180c2001d95649601c010b07591101003811008001c0c0e4024404060440401307248800340480a20002c01c284020904160840d4020781003203508021014200c800d0300c0f05403044001c90701144c2442c500c2c43c24040314103101000c0400d40284151000503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 795030278 1250 795029028 795029041
    0x1203062121090a050a1206090309171506030c0d08091315081e19170c070602010612020a1401180e0f0a050708060f031e07050316030515 60
    0x640500c440304114040040034458400c0710859010445440c410b2100c00d001080700d140540440b4122884200d40403101c4200b0f0751644060110f4900650505c84c0c0300c04000760b0068650414008441800003900d4203204030842c0b90740840000c0c2100d070180c2c0c40b40030103a402c0e03200d141e20505015080712003680c84980d90b80014039200e05c1d40311403041d200d05001c084810350309100c01510079104440c007661039440c0341b41030a48160034038400c054a81d901148444883d90b040681900b09640110800010307011019050f02440e4011003c6014580c85682c007001034640c284286409401d10341d9000f244407180c4d400003903500c1494000d26a03410f8140780d4840d02030b80102182288810b50300081c126160752003d149880328011034691019800300310000d0658025845000d225407080d40310840c15440d02400c6c0711140da501c00302e07140c1600c211140103020541802c0f01c44000c0788802c00400e1040e040c6820315080200c0c980120340340700d040a00034400940d0100d0001e6881c0e4034160b20b45c3d10759607881c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 795031528 1250 795030278 795030283
    0x20303070b1009090602120c0304030507080306010905090403080a0e073005121903110316120612150c020c130207121d300a05011d12030621 62
    0x5621005501d03113064220700411089801800c80700f00c7d214241240b6a460103542200e5100c00c1b100140041d004104000019100202464000006241c0b21981c181c4520100700784040580d000e80204401c0d81c20090070740b41038050500d0f20360048001c2c01c2014641021a444d07189401303645220800103104404c1c591307480d02141003003960071100f1a5014150b10006048035403129003010b07184403840003a401224024011072042c0411801c0061a550301c90700340b200c050351002200c404104003e4019142e101580c041c80c1c0262680403064645812075160020319152250034405050b8142074080015540118403020b040000b5141003018005a1400a000b403044100c01456100001d102d0401c580c1d00140026100000005915881d00780070208006011005071b081c034803c071058218032440403111940c0411b0b0303508804a450902c0141d60307640c25034001e9980940e8426654403400904d540c1001511941f8280d004020318508180d40494200000700c0c0b035410700c0e100c00710490741088a04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 795032778 1250 795031528 795031561
    0xe030c0a03081e030c0a1412040b071b02030a06110d060e0601031a13021e0309010c02160f050108040822230109030b0a06051206160c020303070b 64
    0x208095901912440d084415803c81e00e1200c20214241e070510510003149401c50b8000c041e40d420603410720005600844401c40011401c0303401c8041804188000800716001ca40941d06c55403024680c2e20340480700030800c4030310520164841880310319150150300c0100c3d1f04101940c01940120f03809000048450301d0703224214111010a01d40740e0005144645402e42d64003510007641d05100e20240103400c078005054a413059a0f03c050450b42589503901250b0042800d4480c40c1c902640c9186010107904160b08100c1d00100705035101d103490211242d0601403a4650220145400c48290030310b00c40c511042924024241440184808207051042503802c2c0c0304e14020b169581d07000c4190500301c004103001c440c458160303070004003990b140402c03a140710054071040c41a074800003018a5900d58180012001d0101c400807592002d01199980f12940c00f103107860260310040c0058101050b50460880181d0300840030000344482c4000107035001300480c6c020380c0c1c03c10318440c0e0ba901d03100c5008098185 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 795034028 1250 795032778 795032803
    0x130311061902030703080601111c03060801020a050403021003110f0702191410020d2f0114040c0909080702010c02120d0e09010f08061b0706091109060f100e03 70
    0x501e007222018664000b000f890f080c0c1c440e035074500341070f1114030040d5140449101105400c0c1c014003a140b800010056200e0110b0b0303030b640307004121680c2d40c105036800c81c5d00c0040c107000041d0300087c1c140207504101104107002c04052404000c080f0715103100720514015149144c0820800041d6181075682c0c02110080c450b941c1c2841101003176a6071982107403c000d02008034001c0c0306114070b140715280041040c0349414220340300c20b0364291019103850b40c00152000c1143d44040f2540d80f221400109106144030310401861280d5181820b0030041040400d41d844040114100131041e40010030704000d84014940c2803d091203501928030000310906c41c4400c03098480c0c40789000340d03100140c0c041c5003840c6044051741c1e000081d90f00c3e0020040c24403103034080c04106600440110381c0c4100c081d040750143d043c40c50117140c2800380a80d216006e58007520820b5501d10102400d41c4042d280c000015a04450b00700c60707003208450080003041c0d04414034071446013404045590402c40d0f4170140110344100c031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 795035278 1250 795034028 795034057
    0x3090a060203010e1e0609070e13020307050a080c0703020a0b06041d03041d01050306280c0503101205150604020c060a1529070c05270a0213031106 65
    0x68440f0800e004e104012500514414000440c24561a1810100e58000c0c14050603540d0103681c0c5e0603007170301e2140c20913451940100e500b44160900301c00740e00c00345019056036036506580d260070309801403082c4009000003658510800c0208002600002c02e10318040d8018544081540c8150009005040c0641101010b0b41a06102220700701c010004005440c0c81411b449442e0002a008005051f8240103243d0907510a0011400850410340d0a541039206070f0980400a802036044400380e80c4580c60010201d00b0101c2130120041614403401c4c0a4103001b40d09440015503078517280e030f540348000122220b84100102091a0b901c5940440300d5604085084685070f0500808040041480030400f180440381c24401107000c03003d0101c11403940082c00110600c071401d1246d880380303e0f48034031421200d207440c030b03c4001410380300c120300080110540c1d08140c21001e000e035402c052004000f003c403124540704011041040350100400f02c00d84c0d4002d6562884035400300c0208869100700c141c40c0c2d4104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 795036528 1250 795035278 795035281
    0x30705010c030f060f0b0c030c191e03050d0504020a0512030715020301031703090c040e0a060606030c090b0903030c1504050c0f100c030201060b03100e01050603100b03090a060203 79
    0x2a054000e1041a140d964080000d41001000e034011901c20b80601d554170b0140300001c001c40b40c4044081d00c00d005428080d20f1409581d04003030780c034180d95005500c03924807880d5400018042d407a6840e0342010883c44800301c0c5030029581c000c05510030224411146980c0d40042003d42d240d07401d07040050b18000e0940c2ca01c4805241000e95a90405070b0100c030b4083e48010f60f80c0680b030203402507038122540034626411300183d80040c0e01c05134000408280c03044c4645640d1440303599650003006084a0318502911040c029410200709031580b54008900381400d082c1e804015550109001d42100d4180103510b484801610001c0d013144203141d0340e541035108030410205a04d5809400c2402103100700202c0e1800d4240c3d03028048160a880c0b0b010303501220301c0303045d0041c2a0003141d5108205200340300008840340c03507000b80c1c00e580d00301b074468103105050490140003c0e8050000240074003401c450450031441d00d070b03161000301801ea000c0c1c080000e8022011500080701040107540644e031054007076489 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 795037778 1250 795036528 795036533
    0xb240a0605040e0901090b0402010f1418011d0319020406081e07080c18040206071a070e09041e21050703570605010e010608010612050a020702030307 66
    0xd800a000c3d0150881d24000811000ca8051044600555102e40d54644a40da1600195800c2c0e44408122051040c440503801302e04815400038469403110201c20000d20600c04001010011103801e6504490342d201c130561065030f80000e049002e15188911403940e81c1c0c452020030b002e401e15900c261100d1103034034140607402000300401e0402d001c0260803600d60f543c6e64034155650319484104035401c8120704060041c5000f1800c103040c2e0140c005080103250100c681d41e00400030125202c00134520040f64184031200703030b02c02c414500a00341240c0340c000c241020b448a504005410742408906901e15844000300f0181d00c0c80c0e900c40350b0b2407400c2c0104048201c40080d145910502c42100090240341e60041c050181c81641462401c031083d20b0011007070810184056800001140300d15603a40151071540c0f445030b41c008100d018480c0401040551401900141400040c0c0054050092080c01401640d40c420501801c0100d0307404080b41c56100c0b090841c00a1140400c080e403d0702001655900307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 795039028 1250 795037778 795037787
    0x606180d1109070801060503060d0201031d0c010311070b060f010c0f0b07020709052503061802090411090603070309030c08191e0e040905030d0204031a060d0b240a06 73
    0x108415100302602e980d8070441111140030034082c03d00851010300115001d1700b080b03144447c6661060400180c100800c14002e0000d0140902884286d403209107480c0c101d580c94010545d2420110760120b051032038135920380d007131001c0041a00d0300480d000c01d1004110782c81502030307214464003e102c4076502c1006092080d80040101d850001610900400040c010a5071050b02d101c3c01121070381c992400c480d0481604164440c07041c95041603103030340000c6690000c0b0039101d0140c10b03000d00c005903501659410700054502d1080e01e10445103090150b203059883d12801c80307034810000d00c2c00258811703003071800780d840000424005d0244a40450480e0309103041308640b8042e48415124801c048000041c20b05060780c0c502c0f503001c0007520768826543c06082c9500b010421600c14010380342013144901c0c0540890f00302c0e40c01519005104a00c01301c41841e8003100582240b01a61b024803540107586481500c094040d1034807181e4074003246000b40403410ba880c01008140014407800f101717039407008000c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 795040278 1250 795039028 795039053
    0xc07030302060906160e1807020106050310020f0406180f0b0306090a05072f0f15240d020402090409080415050403210c1718040e060606180d 62
    0x34090b100d07141c0440d40b5101c3c00503400c0c0c8584401020300ca0032008010089900c12065640280c1201c00c10102c030558400c28100b0ba403195080c3e9000142c2a460714003014607004075140f0b120384962041161000c000203140490341602c420342032400350380c01030300c807015400d40e040c0d440a1000f07000108045001c43c0c0d8400250700490040f103070340300d0589403052120111801550400082807091000020400d503501420074440343c2032002d0f440d02c8000c0142c2600340400500f40442ea50010f41e4140e00403404514600d80000c1c0d044013070701da0360591601c03800302080389006083c481c04d44244038000315501c0b034044940c17090024005005000b89407526000b40e802601440c20462491229501c070b09101c2c0c07041e074044907086031130584440c0e031010941d42c0718030580701346900708840800400c0104649403181d1444d00c41604076940c0c0c4070725860400000d890500ea81c20322490801011003015000010400e400800460303040342d4820980030a5800c42e8000a00705400046200c241d5060110f404141d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 795041528 1250 795040278 795040283
    0x902011202070c170f1f0608011103100e010b03191107060510060203070503300106120b0a0b0703030e03090a030515010501030b01091703120c091201150e0604110c0703 74
    0xc02c2d404038001d040c2c68104a501c0c80e0051741c418003403c805a00e007402d00b906e0001342e080b00090403c1d1141009803e4071080d0140d8800b034007000080c0301d5032209544107280184401c4404441550401d004404944406480c00071007203804c0c056200303280300c00d9100d1140e001c01803000d42e6440d96545042400740c01c0403039010040d011207a1000921500200c1250212940840511300d0315400f0404280c41c0100740a03078810110000a400d035218400e1702441e8080c160588401180d012904000c605903140d101101c0e0180e030b405081081007035036410032740301c0055041c03c000c00c0c4403c0911b402d40c0341d40201954103038400e045541c00024084046840f9880318510541034610382c0c0c036100150151410482c4082c0040c60300601000003007106008520412440000c0c5d03480d0a100082408084100351400700c6000c00c001400f052903c3c010300140c0600804000034801482c4c02194120001d50030300c00c0c855000402000680580d0f5207a01022110045200007910b620b402c030030301a81c424060004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 795042778 1250 795041528 795041549
    0x6090203090f1c1202030a091a190606090303050a14042d060c081608030415140108120d02090a06030b0a1a04050409030519022d0d030902011202070c 66
    0x800b0f484920b8521004800079548581881c48031904080009500c020f260504c00f80ea00c20031036002603e2841194030b40410404010074904107800c1307030f4130011408184446420f2400c43c0410500d0380203000c0c0000ca1b0b4040c00c06035200d4201d0320082d1480400460104121000004c1c00b00340b440c2c2400030040c800440c004200d0040d0300d1941603072044915070045001298150b441034001a940c00010111040b4100e00d0580c40a83c1340c3d00c2d40180c0e0002c0e18200c031241965000d1103880c403024031803495221003101001c222540b500d81c48a4894440940038505044005081006168176404507044848054848481c1540c3d81c04011300504845240c188a00c45203400001d03030030707201800600c0c40a51039001520341850300c02004002c01c1e8410089007801002d00010240740e403100ca0006d9880016006048405040b0340b0b0032038a60710300c1c0700012030440111405480350400250465040d800d908000940788020700069440031000c400038548940005815810403041c44181000c86908460b03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 795044028 1250 795042778 795042793
    0x603150c11072c010303050301140d020f0915030a0c090b030601030c05060703090504091a01150206040f030e0907020714010306080c01350912092206090203090f 71
    0x60840381c11010a06400c032962080c0c4060000d0b902a500d10005510703000407200030308400c0700101142e18805d900030b40104001100420102c548000350758105d5400711140c0c110002d46034009480c503008540c1e820b004001c00000038810144d0064840340411000b41102e550007503920344404858501e000d6580032905200b0303e540c56060000c0c40c0e03410b032903020b130311200d8a03800c1038140004d50b04898130540030072906a20001d1035444910441034418041c0080d2081e4151110380402c50b0101a03100034034030030b181d0340e1050790540c0c041511034000743c0c82402c443c0e04800703034202115114080341520703501607000014011140e800054002c21609902441d116903005000194100c482c0b0b031091412907080f5401300406e56102d099001e15003001c0441220b940a0700038824070340c00000c00e621102d117050030300c14002d4011003007008000c13103001000e40f189044410400b09803480006405020403110104000051200d641c103c1006000d0f4280f0846d01c0b442c110709071030b41d036586050580100780144c3c0c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 795045278 1250 795044028 795044051
    0x7020f03010b060d0f0b090411010905030712170c010c09080c0109030804060f031b03061e0821070b04120f091a070f051504030908060403081306020d060315 69
    0x160781e01c2c070b1001041c0031304210920140c1400790070f6030381741e40111039522084450142c0d01ca90050f8025405040165018803582d0001b44c03480429802c0f40d846a4800c00c004c004001e951600000200c1d40480c04a6180403031120b030010a0141ca4601081035003410400e40740d0b258085441c4048606405c12201140c42c0750b0b005440700017217400040c0403580100000c0c03100c41c1c060003c41140b050f151400046d1007000c08a8080c1421818041e0350000380c6035a4104600c17142d290b07440d006601c3d07100c1403040c0903180144490b5283c1d1140300030b01c41d0401e1384400b105200d400340d05071011590846040500f9203042d29001c500c18044180c81000306e204007450580d0144140e0f038060650b542d207001285004843c0b001e1b0344654001e041c080300c94905942109001900611980001d0081c03c42c1240e0103040a14000c0c020400710b8100722410761142c001c110210741d120740d800e84c11100348500c081100f90a42840006482207950181140f03080640020402040c0000b40c5a04070b014541000081da420 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 795046528 1250 795045278 795045281
    0x420090f150a110d0e210f07171006080312060126010509130c030212030906071104110a090612090221010507050711100302130e09070603141305010b120307020f0301 73
    0x1104580d411480c404005444030710424403c3c6d2960781038204030362503240d80e0418a0b141400c550058007c0400780c071601100e0701e00c08c1040304051405402c09000c5070b4101050542e036801850b0303c5a611038802004540907900480d15404400f403160384514240c880781c0002d500c10340017885814002e030b01c4500000c0c50b03158902c1418114540c000c4000301c0307072491a002c01c0140e0418030850761683c001003140088a607182402000303201d1091042e4a012125141080119401e40c086014603070010091154443c0c0d001070303400103840090070004e080d8200d4412140080401c0100290000c0030403c40e010075543e02c00500e54084d015000a0200e070703035049411a0380d40101400107011116094170290b8510b084641440c0c080c1907483d0050800c194034581411b41c05a0781d000e00080e004101c14800821000c1c4101c00c06000c1d64203051221a0440008405500c0700410401e040856180b0701020017100b074200002001005001802a00311001a46d0312507002c03010880c0718040202c40e00c040790806 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 795047778 1250 795046528 795046547
    0xc0e01050105030621010209040207030306170a020a060305101508040b01171207050102070501020328140f1b0c011a0904120c05160b090420090f150a110d 68
    0x50000c46490f1040034405400c415117070803050071075400744600c14481d201d41c405030689500942d004a4061f00d02950034800079000000800710790003444240b00982c5a2510b1141200c40c2c601e8002043d81d108110318624007069000045944c443c0003071188010b90201a55025500031000503145980e40e035940410500f03048400f10094214406895804980c480505102406a030000d0300d01b41c001e80c0c46070308990007224803014400d21809881403a035286003003a0070171202010b0810004808406000c54100c00614183d103841000d0f0000b05200c1c0c11080a11a1302d4912452640300d40b02061164040d11812299425030403458103018018a4000b0a807400f5903004041700060020082e0f0855142c50541810b0300c16100340b903803503405400e503c1e460000402c100c10189456402500c00c010a0301e00400c288403140f000714840001030440581110700c000c004888500c1081181800310310340076103000110f11514004100f010703a041c0c0003100c0340c65a50b02181524496051050142e0301d0088 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 795049028 1250 795047778 795047791
    0x203160c030e15040b030c04030c0819020405041b090203160309020d030516050709020418050f0708072601050406050a030f0303051509090a030f022e060b04030c0e0105010503 77
    0x96503101c91599007403424400f1200c00e00c41100703520f0a078954103540b1303a991090392a4a500d83c00050708105000901c400c0c1005007108102500c80340e220344600011206441d140079108960f40d030b0101e400c11004107910b1426a100b08d02c2c0c265419583c00000c0300035081124070046c1c9442c0f502d9600c00c131510920032545030590080900c07072145042d46045659400081c18020500e24461451020400401440c802001e00300c3e00075944d1400e08044101c503913503451514681c1403c080a00480e1129410019800f103401c2c54003000940c0d13251000c40712001640011090803022a2400b1103901d28000c4207816244243c0b8140312a5035036405000d0704c2034551201400d824540d004d80c0d40040d12a4101940004a45100d081e14082c68000100d85e14404d8449200c581c0c041c0c8440740815401102c4120000040c2c000703070010b03000c400c442c04180d41c4151710400c00800c01004003081460070b5403000b4060200344480b07035100c075143d20301448c000c9a180208651a40301100005984d03208208882c45500c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 795050278 1250 795049028 795049037
    0x50705071a041202071a090f06040905101a03150312070c031e08030a0f0603060f1401090b010e0603060a0e0f0703050114010905010e0f040f0b04050f1e100b0301090203160c03 77
    0x842d0540b00c082d0980041c004103500c8002300620034841c0d41c0782c0002e400035044111000134541465010303101494403030b03440317403505c95044020030030250742c840c2c1529401a800c0d0424001001c15078002410101100c10107140860081110014004903180c0142a030744161151010310802c01400c044c44019500010410305c02080050303a44041a00010800d5441c3c20011580b41d40b2a900c1605941c039065001c546655510341d5240e40d07100750741801e0300612040e0802c1121412120000700080f44428549005003800004140d031601d44151750402801080d5000403103041007182c0350310440007500d00340b00082c00c1200105000c3c070f2041e400d01310b0031416101c41d0740c01850113006662362880c65507034607404100b840c41c080b0280c5a81c05002c8800032642800541200c4003400c00044850240c005131580e0110010442441049404500c0c11060f83e43d480c4a1030792007295035002c20040e80c00030117107080040700026505c4800e070042d40c014042034052609180c0c9980080b0342202c0c1c4040c01078000b4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 795051528 1250 795050278 795050309
    0x5131b0c050307021003050a18030807030207080705071401140c071710150528210c06050315040b13020a03020903120c1c080406050705071a04120207 66
    0x8501440c03542040520441c1a0b07414040b03140c0000316001c44071300c1e114001c01e40765001c105000040f4410074141c8002042c82c000f4000664400034a40c0b07000074040024503500145000a005110043e1050079600074110341c01c2648803503080000e0030200301160b0118880341c040ba14000000c4c42a00d0f07008190200a10403d407424031144906030001080c20b00601512110f4102e0034050700440d000201c20590140c102d41ca400180422035811004803c0000911407400b408400010407410481c0d2449015142400c5084401da4420009038401030042d10512000140c043d08000a144110300900c01c1c01e104d004007070184801c0c0d5901e01000d41c0d010818400103902c1001e80c1d8050940100349150050400c01010046498140d000ba50380b902c1400c0802d204509140400856580e4412030310160b0842e541850007800b101006807005241544950004680d24440c5050b41d031510340004051050a081451450b112001580d0907a4100320310300050f2079450000601138204d440308034101491 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 795052778 1250 795051528 795051581
    0x705060709030816060207020301020a0801030210030212061003140f040201080109060503030a110c041404210f1121071403030919060b03061009060503070308040611120409060513 79
    0x50303130040b6412107046500b44602c501681742403015182511060311850070235411030042294a4035001511020180100020144183c507088800d800001c00d0b115501c100c154580706401404903200740c00e041d01305010400240620700c4c082d1a002d10300070b8845024698841c4029000e030f510600a040e01039004105a0180034400c1240301140529901600d44000054001406440141c00441d1006c515007007031000f8005c000701c0b0189482c0c250350800c07402684501c030282c01c411698090301d0034006e42c82007601c00c4401c14480b031104080748001520b04144941c0329030360030307400c44d90303054030780441003181e44507a004000100ca0150700c00303400501c1e80410b80c1100c1c59064144030f40844225440341d40c80c07841c3c0e44041101b5800f5903040b980e044412410403500c201160600e0b17005038400d5200786010000b03d4070703e030101c1e416a5000c1c80d001e80384510703075171840d45040b0011841c0032800c140000d001903c0c110581c030110a40324201c03050b403002e0f08081940f400340d80e0f045110100ca80ca408149844 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 795054028 1250 795052778 795052807
    0x60806061c050a0207111207031502070b07030c031a0901050f060403050a050d230f0f12010602031e09090115120c050909010608040b0f0604060b0f07050607090308 72
    0x100000c0ca1041c4a05460340c0c0c01803106403042550b5141d00e454001c1490810020402c00041d1590401d0700c404421a04d06298a903680007184405400002c0c1d05407402d01c144540e0301107840740741c0c02c06c1c2854564140b0200050040c52552100c4000030b1402c000c1d01c2182420520f00100180d0052a041013070342071004100952910000759903104504200002c0041d109000c1a440d29004101034072030f42c00641005080c4103980c1010740d1a00c04a0b08003214664584000d1394100002015401d84070b8000c8160403410384104900f00e5006001c00c0000521160700100401c0e000140c40203c44040e4440c4120045902681110b268000e215000610100c201ea4000b141000114039100e100c820851240c002201d000c002c0c460b002400002c0c002005050031091140144501c0c90142c1e4241703001d071502040c101025280448084407040807510640c0d4580282c00580383e4590050b81c0e50a1041c0c00899a6000900880710f40c014800011400c80c054043e2508503034001d04a640303024100c12600c031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 795055278 1250 795054028 795054037
    0x314150708190609060f0509010602030313020418050a020a14010c080906040e191103010518250503100f0f1202030a0f0602120901020901050403060905030702031203070305090706080606 82
    0x80b010818100707800e00076115024900041c5150800042d415003010b015030004001d130340055005480e100010842c1550000489600511404006151030304c4c81c40020050551a0451f50401c154001d01d407041c04804100045a50702c22031b14040d01c1562039544a0159810b031204602082c50f03400c1c1c08000c90500380080c21201b10081c500391074181c84801c10041d000c015984225a28050300141840348480c1c841c120107562a201c0302c50456240c10002a041200d02601c248001e89100110300700c2d402812828084500f80f043d501103502203c00c000f0080d4008480d02e00210f07141c0f58002503c1407600802c0c4041d1104441a4060f80f810722085521f00c0001c190103e81621801400e803020850390112282c200740b145001513501e031340c01c802068028101403c0020385910402001c0803980c0c01c64101ea00300c0740d2004020034a501d49080c118258004c1c00c002070341501034015030090706584c0d040154400c24083d1070030050768456800b15584c40d0311600850300461040c40104466107000d40141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 795056528 1250 795055278 795055291
    0x80705060c01110f0706060f050d061a0907020a020f0a0501020c011103040f030305071103013b010e030405121911220e1b0d120c05160314150708 64
    0xf10310707180d1403120a0243e510042c00c02e000508082885d60030001c10b4000c40c4000c1c6060030b031100c0031900b0714000400610100c1d000a09130307580c40703510556101c04015501d60120005000b04814940204040c2d26401031080803449075100c9030a080700b62511112904c26250107070700514110244000548120030000100340151005000c0003e4044c100038880d070103544030792703070391525140c081c030f4031a0811200200c1d01e4441c2e4103008011020014800e40c1140311046902c68080e004c01407444065001d41e90405d501c680d5081c05040d03400c0400000092049038016600c08210a01c001d40b40d03031701c0300a810380340003909030780401d000045030342e4000d43c441080f8001e20101c010580000e481c900c0300050030403881c0050325207107420320382502404030a03000d5110707419214140351078100103150230016280081c007001c494040442201c0c0300b140d601e814103034407500300da8100c05020545101007201e840220307000003c0b00507001d0138800200b140e01c021245a1104015501c8101d001d5401b454000e12070b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 795057778 1250 795056528 795056531
    0x7060c1107031b0e070206060120060a140c0406020606010509040b0d030f0906020a1a10180203060a05010c0203030702010c020f030703080c07300614040305031e01080705060c01 78
    0xa50a000c14040500154814004441c42d504944084074482c02a640010500807400d01040340c099008281e196000b0b1091a100b00c1c0e010300084014144020b2030448009842044200b0110341c98642c82244030480302d078101340d503d540380c804011081c07185001d54030043c0c00001c0850b540c0d5001e04050f0203030300f00080020130762618910126040401441040d40000c0040c45076100d050307041402100500518409440d44030003d8551008030a0b059000d40e109032008800603d1f403c0012045501501100404d0b4503006003018075200690001e6401c60704c12030595200082e25030090404d200d081c0e84c0900558140012030700199500a0084400e9070040c84e0060030f140b040d9801e1103018069885020b52940b44c2c031000d0710440c54042103421403000b9040c62444012521444008120458400174103e07110006a2800c1d00c003030100040c11308a00110b2200707210400d078101004d0352182c2c10401501044100802482a400c00700b0312403a0119000b0032014041790600000400d41410720900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 795059028 1250 795057778 795057797
    0x3061c020a03140606040b0103111204081204030c0b07050310090c020708031b0708061e0702070902040603090b150a12082205031507080a0b011206180b1507060c 71
    0x43c1c041507500300341c00007034a641010040040ca40b81c0f030300c281040c0300000e180401c84642c0c40c00812005224800402100300070302800103041094080442d0a00c0382450100c400714141841d019141c020510011110102900b0000c1c130991301c0703003007600d100740141c9000d400c1480c6010003160040000d03040e04800c40c040c09070003044e0141c0c200004c1801900701c0c0c188040840b0310498071800e06040790001d0f400354104901b4025007005484800c2d0b04088800b00d07003203c3d07869800c82607140508a52207011051f001040005d0140d815510010741140034100070780a0342c0d1012a040020318001e0302c880e6006400c1d803014420941160144003040c0e105940b400c2c6000c42e04c80519410040283d030720913032801000d205012904083c0100a80c8481000704203a031802d041d1806840c1c1c140041184050b16610800c0c219140c0c1301e907400b10707910000040d0030840345403a440d846140c0050a5250b043e01804c040e000c3c0c1d40303418180c0c109c1071407000080307100703003080c41c070341d42d0000030b0110100014108103440c007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 795060278 1250 795059028 795059033
    0x1e070c15060b030a0f0608030a1119050a06050f0403091404060e0c0c150403020705040507050d050f0f10050f0d03030608030310150e0306070e04110f13050603061c020a03 75
    0x22070107000c1d00426803034903181d2a09454250a40e96a201c1c80b222050908804004001001099a4a6566504111000c0d9128070304c510b140096805a40d031142500507507040c20300c4000304491612a004001c140015070381da124144140c0382c180c0d4002c1c000358115100b04007019200c1d8540040a40041012840320b98401002c01c0e04a400d54440212410010310524420010003110801c00c0700c1e00000d46861405480181d210b684a20030f03c2e018503110000140140d02c1038045400380441c1c040c0070002401d000104444900307084608100b840f96a40210b02c40d80c43d115003070002c40b9401012510740f8640201406500403001400b00c080c151110340102e0000424400740d0b2040d800e0000d00c440423840d010a60160b2455404034400348001c948208056860100e6200d80c0311039a42801c02001c40210f0128000344030100385110031000101d100f0307040c036074040300400d226074410307071900312043e03d413020400c40c0d2005031070071584003080e081d41004042041c04d13000c8100b40020403001d08150f80780c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 795061528 1250 795060278 795060281
    0x807020c03120405030f1f020c0a020409060c081f1424070b070509060702060306030a081602010e04020a09170a0501020304082709060d051c0c02091e070c15 69
    0x1c040100c80390109050004c0c1c201044003e03100400600200148103c841c200c02d2005060700c2104441c0ba000100040408800c001031801ca550103041080240c04605022000380250184200083e01301d0300401c1e000c46040d0f03800e20141d0103c54280c0140341c54441283c6e440c6d8002e854489c1c200301e000c11070b03024403e8429041c242020403105826550740a600d4219901c040040c4824184107040c801e03440b160b280c5900b9210000e80c1a20403d589485d1400040d1a20b010818024691800051990860b044041e20100340f94403c0c1c898100c0c40c01d080040206074050303404101d00150103440b04110764084081c10728140e004070030a80e40c4042c100e03198982682e2040358142c0d44020002880c0300c0c43c03074014148982034180d2007031920b047c00c8078000280c14400b000c0c01781c0b40f19200c180000003c0c403000344140c2c6114100c4488040980c40c21001c084d018090680781a172068015900055030140740c841920f048031200010313150f06507680c55098401c0c1e003142c0760036522102004603183c401403c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 795062778 1250 795061528 795061543
    0x3080310030b282c1e0d120b010c020d050c030106060c021305130506010f0f1d010e06010512010801061d0f040201050a090810060302030d0309020102070e06040b060d0203040501060609150807020c03 87
    0x408018007028180c2c11880175070014001d800c810703554001c1880f00c0c84154042800c644000c141310300401d460b041d50004907800440510003039445a240440b00c020464001059000040181c009000350f0382d5401060303804074034060b4007079040040e0400d460031440095126940c0041d510650b160640450303282d091825600360840212200940014040d40c00c0c03490b5070400500260001e402894940788414182203010303c02d40e80f001c0e03034141c04242181e0081058032010609403424440d19a520007000c0d018102c54810603c0e80350301560324441c160700940300c1620031880c0381c03483c216948a039801180e01d070b0322066500e0b0420061100c080b1781204141701014484052034000300c1c00a056004050901411020b1002410719104642c40140d030007042c060100c0c2c1c480d4410031a140c3e14400840c001e0f00c0c4000c20039500010001c3d60324215040e03940510b000e14010070003081680d0301c40700140c4001d551070003940341e041800203102035418881e001c06948100284141c070a00c28030500441c4c60079a1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 795064028 1250 795062778 795062861
    0xb09061201090f0f0501060e07020d0f0203091002060a05010b040312050c010b0a14010e040e0c060306060708040f090e0c1c14060129121f03080310030b28 68
    0x18130a2800342032003800d009400103403007111041011410b10b0f003006550f07881d950008800748041c07a500d506040c0c0c02402903c90b0518060104055840c4a1a00a40b200411920900307600d24020002c01d01d520001e0584003940d40c4002c21002d031810300a410b6415420000c9061080e6407541c2000c200c0e51280c00164000300700d4031142c552100075000c005031aa801010426000b40e03d04039800d4610000000c0c040c00d00c0e107064401c0740d07032034403808081050381c03080c00000780c4120400100040c01c082015007c44c11507400d1501000b20400307010340943c03a02a0310b40c01a500180c0b0203010481034100826807050702c0e00c6580313495003010013004107a04108003607010301d0381504142e007103a01c0880d8002c9208110f4a0040c00c007803038021000703402e00800e000509113141d0b1032400c6259555090401c0c0b08040a150401030300d07070312490191012001403025020403136002e22518080b595400c0826402020000c802c4c44045001801001e100010620800c0020380c15a200400b114001c021107a503009241 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 795065278 1250 795064028 795064043
    0x120309010f1404030305151e01140301080d090801060605180d060c02030415170f06060c010e100f02120f280504140a0b0402060a050c100b0a06030b09061201090f 71
    0x1416060145c1110300007094141c10780750109600b0b415a0380d094012018100801c0300162411108004031071004801240c1455804c000002044000c40002c000ca400085651400180707500e0700680ca0983d00103110754004104140030840203400c030034640003004200a04105210a044c2d1203102c25a0b41101d07900c0c000d80c00c00101030140303008058101d42c0c200d441d800d003014558076182c00340d440214000c007102440303040d40d404038400366510803c43e0038149882c4024014850066070042c1c8401c988010902d52900d00070500c840c00c0114020740744500c40d52003942c2030741d50b58600030040601d4010200c00d80400d00b00d015082b4280010901420b031083c0040001719842c140c80d00c020450301c00007001c4041e9005050310b000250004c024168040d9060316a42c1d1151102001683c060140b202c60900c0c070b010745150a1500f590301d0340301d0600c10780c2c101c901e01c400d103035500070035000c503488204815088061040052054140b0501c0e200c0b40700c2c544800001c001185464806179841200740448010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 795066528 1250 795065278 795065281
    0x5121b070b0703051003051e15070f021c050a030b121203060a09050c03070c0503040906030302030702100519030b06070f0b040b0c120609071815020105010f08120309010f14 76
    0x1c0e81032080c2680811201170102e40d1714103507101e696640e040410050503004d81285140103a00c01807080c102c2500c807070240c01031941000384015066002201607000103200714186a200c1c2141d101103510300d603c498603000d00d4518404421000b4284ca4902c4681000310400c03d5000d0200810464207040814072196860b0304100003000b02d040c0c0190702c8141d0759407c0800788400d00d2032110481760000141c0c1402e04281c81c0c0c9140040c1140125817207818128902000041496000710080024030701c203c41d05070070514403000a54503805852100402901503200d021141c60181d44202168000141004d0078500159212584485c1306002102e8485001d814007003001041406c05030011061240507040c105071800703c0c0c960341c400400c403510031403806010503c002d015804100101110741c10030f4120f80c5e281c0c3c00350300c0340594000707500c00150302e0300c0000a015080d080640c026101844091700b10480307090b0100040d0307000035105d19200e5503507904001301314015200351000d1341d80c0d504805845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 795067778 1250 795066528 795066541
    0x132606090f0c0307030c06180302091302030d09030c0506210a061a03011a090d05120a020f070503060105061b01151410090504150914042105121b070b 66
    0x4003440041070303e00a500c660030034000034003401e90000680711146001c00b801141d040c81c107255540160f1010350098000d806007c0426001c5643c40c04a034029403c8800c49015608200c075010400d00c000b07081d00d00d20030800d00080c608000140168143c402030b940080d91498000c0382d100b801605e065100310740e50001040302d90020300d1000c01d0034402010301401c2d58507242241500d503100c80f1a0360703042d01c4005020595941c80c08080c0420039003003011940d0b003514104104a0343d03407107207040320090f205103103d0101880001540303400341c3e0740203406081c440c2d10307220078810690000200c641d09007072884941c100d103203400d1003003507108103541e21045c0382545058090940d05400518143c05601074002014609400603800d800700c0f241541d0020300c1010310882901d00040310340001c5882410803c08106040540c60070601450003070b45211800528000c8a220b03544041a4080200304180302d070ba4803601580030502d034040c11440d03003179240c006402c0c0020015807004004449503580e50060044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 795069028 1250 795067778 795067783
    0x91e01090e0c16060609020d0f060503160e040812090d09140f0d03020705030d09080c0406030f110a181a040506060904020d090f14060903132606090f 66
    0x41400141c04001820480c40721035052140440f5010b0402c2d441c3c445004220b1107500100c01880c00180841d00d902d80000c1e81009090954048580d041c01d014001c40c0c149000308181001e10a160882540c9a160100c1c50b02140c40060054030810010700c465102c4a0403038901a200d20704a0014264000305404060442030884e00305450450200c54103030800c0d10354866695036a0801c40390500c0c2c01c0ea41c1e1070f00701e2410f0306a800241e0035010740d00510013607a4009000b041a294620103803402010702d10140011504d407031101034030010111704014081070781070380500c0b03c40e400a040d8203400358442c820ba48203a0502003110400702d603a0041003001a810024040040c82c0459050042c0d050200000760720b0b0144070342280c403890b40007540103506a41503000203405944800070418400c2c0d00d06001701c11034041a05d40307066014500005940d507001008446116400214080303915050155030082c0c40c2d04075681c00b807966200554020301400400419105054070390040500322100620b40b070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 795070278 1250 795069028 795069047
    0x100f0617070203040608040b10030c090209040e0d20010e06180118080a140409050903040807060305010308030408030403030b15040609050307050901090b0105040f060c0b01060804020a0308030c091e01 88
    0x50443d0424041030111580c08001c140c2c0040c1c022014020f5501e410040d040341d074074654001044181410000030780007a00d90054404500b0444040152a0b035a51840391100340c1104000d0002e0a60041d0b01c0078207804440900d034480c100d400000301c0d5814665818500700e41510310300400b510822034a4560301d000d01810291407030003084005c40010a0355400e5441c000c4803041400d102c2e40d0804101b110300340c5070640d002012002c205005030b06010317407500d0302d1741d0003805111104e0084940128440d0b010740542d40c1266808442985540d545889100303681d00003070400c80415032207a0040001d030b90351161418000c0408080c96580e40c3c545107000c0c189070780980c090b030301942284408100d01c1d07486107200e6045454968020904000910049403e40314941020314451041c280201c0c0c890740c0b01c8000192507118040303600719662550341c165010314040750000e40c04292220188001205800030356000101d0a0405040041c204001a80e201c0600d03901d540b4440e0758040c0108a690003406003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 795071528 1250 795070278 795070291
    0x9120426010209090415091a160906140f040306090309300b04170c0619050c2b11033705152107090204080c0108100f0617 54
    0x21031401d070040c40450100400203001418800f55811b8520424803e03820078008507030311210501c98029011180f980c0500c0c185c6020500c140903100c4022101d000300310b0349080c8d4886403141c0001016066400b030266002003080e072070901c01400000002040c3d401030b002d41034801c0e282c095906040019010a01c3c1c05141030440503500106070f2506006541d41040d40d036504118400001e0381d4905064112034001880b4108000b40002c08414400c0c010801034010065036026281340c040d080d070140140c82c0141d9846800394001c020316518070020541103034400b031203443c14500300340c03841c625001261001d05650141ca00c00204215818940c04030484000d840c0a02e00c0035900e030300c1c1850555110280c54403020450f5500d000c12003111642a02d1021804010400003502081c5c0016401d40651010021340c0f40c80740240201e0500c0c41c030300903207040c1c8094100030000705081000440c0c0840001e041440c2c90300001001107180300741e80740c00700d026007030b42c0c0c88401d0b0720b074658030b0300202050008004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 795072778 1250 795071528 795071531
    0xa1103122a0d05040512010b090412030501090603021c0c0812130503150105090c0d050705210f1f030c06020303040506010906030c0b0c1006060801050f22050912042601 74
    0x1074120740c507002010348060f905c0544290360718040c14007a0b940109141d241e01684001608200010003400104280400146507024030540e42c0e1940781400740e0385d690000a620000518640f41c3c0300c071100c211164030798011004540240d5494001e28100f03d81c02210b0400b01c01e00182841c400c592482c55900184015402054101c103240d886580010b4113000308c81c4100e400e0341c0402c000a07900c0007540c20b2000000810010b908200740301410551200d180703440f10b03050301c40030440ea440c1f02d0003009104d0f07034a1801003a074980d100d0200306080d450f140541c0105040030075011010400304400741d0003508164000316502c0c2030505001d0303d0040c050740b0401119080c408180300040078140d10f841116160b400341c0c1d8a07186070700091418480080d46c6030b11b42c60300d8100002101035200c840356049940c140d40202c8500d1100f410320441c03040d04102892481410190105034242550203941d22090340b04c280c40d003440051111140d240e103d80e01200406002400315045c40070300c0110016000c0c101c600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 795074028 1250 795072778 795072793
    0x31e0f071419030905151e0106030227041404050a170a021207170d0c110109051e03041d07020601091802010e01110a0c030b0a020a020a1103122a 64
    0x6240e0b0b4407041a41c0e00700b00768840360140104201080300307068600060030344150380c0c0b60940b009103001c1e4130340c0145056602c5403000010014003034801c49003511210051403000e0041d034500c0d06210803c29040c5508a580c500f108005400c052003031030301513840781c1c010f0485e10000b800c1c0311031881000d1402c1e884040d400c000544140783c0004841c0c440030038101900741c544251703090400341925001c411110342400000c55441c10740c2c550744040b5804600391074599101182c0002182200c6100000402550045002c9100030303481080c4c28003001450b404807450261111b02d0250003203010001301c1d80d0656403200388402e69405200f1a0301404804204000c0010710080020360744418980180c14000c103040000b1650344101c4e2840c00045071202103800c8800c103854255103080c3c5510043d5603180340240841c018041c50f008071005466079034010b003003070001a00c4440c600c201c8080c425905124400c05000c2d4980c0c100c02401111101e90181000440419070251000ca640c411400c1260404035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 795075278 1250 795074028 795074047
    0x120a1208010f0306051b0a0e0312040b041e1d090d0e0d0b0702010f020c0f010b0a03050c0616051605130606021f14040b040311060417031e0f0714 64
    0x103056a08982d04200c4c0070941e038981010900b01921b80902804082d4400984200890303046410100009016002c540503903141d5160003800780258020103000781001c0004100b19050700140381d50810040004911a643c0c1ea40310300070201d11050002d1504501d401040b00c2e0341028001d40d8081c82842c1400e0143d004040001042c510f0001030003014442000c2c0400d2040b0310035800b1036122641d180c42150b070303200020381d40e40e5241408203444410350b0925901d00000c2c14a40101002c81e40c0c80340041c200d4201c158100651500200c444000450007a11040d0206500704070310107880d012034010b81c01c424100303414080c0d40d01c030f4901d10349030f098200b940800200fa03001640d4140301400780e05103481030b50320302c410f200907142658030400031160030b03800e00c070030301c1022001c442c0501c0c42070f103500782c85120b09800715464150481c1c02a10301e40210f424180e407001d1080003560320040e404042400410040c440986c03040c03080c0c4071b022003280c100c2c0c200841103402a01844e514900000000c0c00c1c00e1080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 795076528 1250 795075278 795075299
    0x40603140c0405060703030f0b030f0709110c0c060304021302040e0a061205150c040513050a0507090e06090a1d070812090d1719030c0e060f031311120a120801 70
    0x5d03001002c040c0d545500589215950f8404401d040300201030300c11520000a860740c0c1c0350800d02070400044d01d8641c080700701100401c2202c40c1c3c1c1081707401034140c28401d0070030000b041d0402003081ea044200c601204045004510090019007144c81c0303040d04505011801c50100c85ea0b03a040074048403507050001002c20740008042c4100002040c13503c40c507a80f150201da0b2a170003107030b014940085104880075a0513000307400c000e1080502280410182e595034200f22080750071840740360410044540481d001d070410600281e0722241280001c02c0130108a035151a516000701d0001140c1c0e00817880c18000f840d130902030781d000000780009003802c001070350000424404005200510800d44600044150a842c41c1581c030500d40c0d20005180d14458894098003905403c2d00800c001078800000214a2525800341c0c0c02c24005504154115907640740741d44168040c0010076521003c007044892429030b100b11074510444040710181416103054a050700440303c41501c0710050003001401482500c002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 795077778 1250 795076528 795076537
    0x3131208030a0b01050f07060504120c0804090e07050d050606040f0615050c010b030f1b0604060503060d0311070f0e09010209010e09130f0f15050f0a0903020f03040603140c040506 79
    0x4080051a8401d4500584061241025158111b80013190b103006116541e404284200d000d081d81009175018201c003216400c41c076000041242000340800c5c080400c4035404003425202d01e100300c4d1a07040c0c648000411070300d01e20801b240c503513012104004030746c103041c0142c1c10316102810003070000c5030400300543c00340e000740301d401010007102140c0c03460301200075081014842005401e84800400c0c250b030050b1654040542c000101d20006030b402c40d1410540200c8003141c1786a038509056403550400c002c4030326002c0c03209a0820501a00d141403610045c40001c3c02004c506600001061520f03000780407402e4000e00c449516403050040f184142d0b003000c1d02e803000c05411034a074401c5985d080500110800841c0024100a803406945000c0121803000000d406000b035011080c5407840303000340016203600b01c928021908802c3d0128820f03900941041c0d050a200c3c3c015a140071403481c5c00c0d00e1450304580e10a0000039240c0b40034850100f07406602c240c100485d00c1000d8901404d01001c00c0c1a4401c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 795079028 1250 795077778 795077791
    0x501140d02010c061d150601080a1119120b06180f2124060a0b03060d080f09100507030c03051605010c020624092409090313120803 58
    0x22144400d008582c03042d03c1a4014070340c444410400c58035944203110011170101200380c4a44624031084140055842003580701d400165142c003140d6640e403034100060a020711242102940a1014221402100d020107103108040e542e01443d40030303480945419500342025003405007008100e542d84002d0400300e030302403801041d0b8103491413041140c0032816180c00001c046030398040e210301260b546140402c0158101d85039410500c2d03407031400141108144415550664070440101c01001840d80c0c01000e15484000105000320791245a200c07415194401d03c101c02c911240015403146138503140240d0503809505d86045810168107a401a015007022070014051107000b00c1d200b99105034ad40440003003154060000d100c0781c11041d001075911001590040d44491040189020000c90880003000c10040282000c00a44440f0076800b42840c0380d00e1003010307407000035107035184030b0301ca01e01c655005248146c01940c2d11030195020b0008114241c00071b041a0341c900038404c004c40c102c00140da40085 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 795080278 1250 795079028 795079039
    0xe0a030b0c0c0c1005070203100506210c060c1615080c090303040f03030e0f0f01090e090f010507090911030114040e0a0512040806010e0601050304080d09081318050114 74
    0xc0c400301c0070501e09400068074581c404c090100f048086540580034009047c825800c03030700900c01010905081d01d80c100e8156411050f0300350442c0076038040a040e40b0346c00154600707480c0c0c08181880403030955031200b4840c4070b5641c0b08010081040480044d03420080940b400240c43c80083c002c40141941c0016003241c280c0d98001c5000e40d02c9640c240304460042552402d2040170725074038030340548507020940b0b001c0d124644011803100700d418000c0704c403281e04030140e448618072030a02d40b036800b0001f80901242c40c584075450399005842000d21485010301015110b00b40710300d2800d2000c81c16169164010240448280010410203498a42640504408440220b1485460208689090813009014151788252034100320040c041d030f8010016a03a2440580e101a80c071441c0b54569140c2c03d58113030307002500400003e000300c1c882d00c01a29010258080101d03541c880c2e516030b81100d0304900844200c0c0040407900f0000102c035110b94501100b4098803d0240d90701d070020281e10401559a054000d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 795081528 1250 795080278 795080287
    0x90102030f010e041e110f040c02030313030c0f03051b0a02012001020c01061419080c04021b0604112b060c02150112142b140c0c010e0a030b0c 63
    0xa0440341700981c0c080c890b000030011038941040b03840c01d4241c205590086020b40c12000741801c06000d0b614071070315150019450b648401081c880b04911858040d0b0800141c40304d00307000501c8903900d80840394020b503952a110480c0f201807100350000c801c8843d0656004507003000040c0d03048588052a14540d0034080bc0b5000d00c08016800380c41240d00a8200b54a82030000c14083c02d2001c103006008415507080a24940f40e0304007600ca02080e00488440360b2010a1102c42c038502a001080001629078021010749001d40d00e9901e00407003624215410020140c0d0380680e8144034007940c02c5001c0f01d80d00100c11141000107000060380341000540000e482c0c400380c4242c03500030050001600051004441e45603900d16200708004080c48048030590750a04042060300400107181810f40302140b0007035104d69609004241d2004840e4000c2c1c180440341e114500381300c200602501889030f6400c040c103405014039000500c0f00c10306c516414070900c0600000e02c080b8240d40c10b030a601000c80348445540c1e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 795082778 1250 795081528 795081533
    0x31d030f150f0f0106030903050c0312090f0106080606120a15061a07021e19140405010602070503070902160602030109020304050715200705101e0305040807080a0c0209010b040e090102030f010e04 86
    0x70b1060421840a07844006011241c100030060cc003881105500e064032031800340070341c845003070305c4071071250006950000020407101d00d448141800301d180e16008442e0401c809030748840340c001d59940304402880d40d03504204508413011090000d00c8003640360007807502049600184599600c0b0500c044102100b0007210440e880b880200ca8511010420039000d041d40d61034820302d6041882401030140e4200000001e0403030000640e0015980c1c010060f0807a6070510070700c10700940001100d00c04106000c28104049113191000318081c0c00498000760381c038641030500c54074000441e40240542c1b442000d01c02c201941c003411650303524150052030005041d103100c12601d007c60941285a22080c12819110000e0b0401c08170392690020003148203008500305001d808551003110023070480c580070402f210001e8198402400420424149101c490000d070300032505041d1700342c0203814062000102441017012a4520507404100754001b98607500c0c240707031084041c11041c41001101c480c10b1010908 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 795084028 1250 795082778 795082787
    0x11b0f0c060e2103010f0e040f0804090f0b1f050c011e0504140109021309060e1e070f030f02040e0f030c0102030709080d0903031d030f150f0f0106030903 68
    0x30481c0d04190280900942c02c2155030320340c00400101c154801c502030389540c1c1d05800d142528100d89001804002107450050202203100340103008850b451390365805035001404107800351014195800c0300103290076080c50240111403500c51031520440c20030001d41c2c0f80301e891340b0134054000240d02d00f040e22044a614018013406c00003100c1800340e091a891190700b1051035000d41d1203980a0700c4540c044e081140d004508889500d04040d400c03100d502042221422540c01250501e4072884002440b401b000f06100c3c2403610f0071154004095049034282c1c034202081003070b00081c0c51703101c510324140d0f40f86650f02c2c4400070070050001d01071920f90300080304000040c0301c08003229a484040c0c1b5540d00c80e00d004103000b58421140c4101144014074041141c0c44001401000d1400e02c0e11004034a0b405e588050b03402c002d00c03026100c01d002c40c1844203402524280b004500358480d01300181680310310411640522039004000d80c0d07000c24810200026001c0101c1840c0c110396040c140040c0d10301c0a41001c64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 795085278 1250 795084028 795084047
    0xe0123130e060c0d051609060e010e040c0206040c171902060702151c0c0203092803030203071208060303120709030b010803130503030c101505090108070602070602011b0f 75
    0x5007035010b41410818680d19000041c10b0395120001c04012554440c009612a0981081c0070000142518400d1005601400e07400e203081805040040150329444005000e59080641d107100580000d414030080055441000014214008080d204255107101d0285d5410080c0024201d42009001c0c00c001d43d180d81003140c0741141c0180580419240c448032407101c2e548400b5645140d5000b10f507000d150242144952030b440d2009501a61a002035003040003528198801c1104c820304014505a01181490724420000d520940141d43c90b011a4100301c951350511400900c00d024a42c1c04000301d683d03012085a800e5002018580344a8a50300002c07102500703030750070040801125100208941a000010707008556450316082d04184c2c881c01851707260301940c28411840e81c000080c02c0d0381d00449400caa0041005074003a014000d6071000011020710080c0d00c50107590b00081e509101c80c590500c0010041d00c4180002c0c0283c00704034a810301c0d0500d001c0b03010b004000d10034080e40c0e81284905940c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 795086528 1250 795085278 795085301
    0x90912200a11060d020c0303011404020418050406290108010f1d04030504090515040e0c130f0b211b01050304030e010c0609142e020c03070506040c0e012313 69
    0x171074032072910314600c5649030b10038003c203050f1244100d4820801d203018000c80d070903070350351206840c4c1300c00c01d0000b44000750002038811241c031038482644121801003d002c002815108040c144503511550001500740981070700528405068104184aa07403540c19801559115008281d14150b8079401c0440300703405190031000a1a081000744909034040b6908880c908808a07800c200d0038100054450b82e4610040d18190011507801100100c0c6407107501c014802c1641450218030740304001c0001d01c0c40a807240505016421079100c100035103404006803e0408032101a250b280c04948002a005001c020070003800c00c03401105014050344a51054600c9680c000c00a020b02c092a103000da04800401e8a220000c0c03003a85080340b40c8601200102d1390b021025460080c01c42c81c103d6962000e944140c41510341031004121500000d4410081a8443c50040d000341c48424100380c0307031011400d01070340440087e60900b40b40100e5504400e902000c0c80754200c0741900141030918801c1d000d0701900190 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 795087778 1250 795086528 795086531
    0x210124050d06080a060621021e090a1407021506060306120f011a030705010c080c0c09010306051e1905070221041e060f18090912200a11060d 62
    0xf036004000404034800e9104807800d100305e60311070504411640c04000b00010b100d100c20f00820244c2090701899062500c3e11040c202e8180c886004100040c0d000e540c0500200d80d512107074850f1012804081e07412080300d1001e00091850038251113a621005440d040c8240301c0000030440b9550b85881d00f40030746880d402554405051165079138001e101280340d8020032b103600e00c5001c800c1d103004600303042515030507100d0003008062500c40700c819400a410503550340c032039100501e600b03641e1000451300030752280502180a00d400c1e09004180c2e00d1100c45926450b91920074403614641300001040fa180090b040000d9071b58a01e0002c07031828407100340c44040f01d22910320440039035444100810035184606c03c198080c00c0c02d401041ca0007000d5100e4000000c6003010f50740c001521403054038620701c0c0c1c0134845071140c94175030103034800300c0e040300000f00c0311001c007192000394060b00441401000105801381d4001c441da5030f518161275240e190030003812003000740707100c08055840100f07030b0f610104d1300c200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 795089028 1250 795087778 795087791
    0x380406032d050405060115090314010b040509030d0e1203060904031e020a03030605100207030b181b0117090304091806140402090f010b09040506010c1502210124050d 73
    0x50705401020180c43c1614140902400841c54482d001203c51024419903541110300b0f00e161a003020814081e10440d040d5501c505116141e0750301c0b8080c550180c61110040e503034039214608203004461000d000d880c084d40115034000c0302680c1e44025a94841800d6800a000c2e40d40d503d001c031000ca01a07411750b8465454000c81c0c404669001607003640e40c0d272090304d0420816446904102800c114030502e1030041c0d02440b014000998011112034000188030105a0000d40c500101400d1a002d6005030020304502c2194014960b40b04103004641032145040e03100900300315440517180d01c182c0c014500c0d00343d00c0301c02034000c24020300481950302d60888020050004861044c00c4440c0701580d017640f285404101103051481c2e01d150041c1291208101140380c6a24002484003a020007030078241404400c00c803520114403c0d0b044203110794040c4200598992110005900b103503181145800010440001401180e042203440d41c4d0110700c0c0c0d04002410101040300722250320a041c0c0c080646802c4c0b04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 795090278 1250 795089028 795089111
    0xf0f0c0d081608030a0605030a150c140313060f0207030c1412070b0703050106050c060105011b02040905070501030507050903061302061c060e0c070b070e0a0f38040603 74
    0x24051405201d10b05e8091101d951760380300b0180d82d044080d9000d425601016000c840749aa40d501c906420f480354249802c103941d03070b0607035407407150000c640704414016030360a91020801a07210310081000442d10840c20560300741c500601804800c84002d00c0c00d5456081005501401c1007880c03c1600901501555030110349005545000e040c0c1d40c00300406c0c18040003040280c0242e0903030300ca580c241c0e0000c190300d038a4680111500003091509281080118040d64056100d034020452031a01a00081071990310304400107045460080c00c2c40c3c00c1001c1400650b80036130740811425003100500043e10015145400005d0007840303010617022400b00e9046000400c05030076003084049441001440c641e03640c5d02100890301d0712503001c00401d19a80c401c0041c0c1042c1c0a181009601c40d001780103203050369181c85072031341940c032541c00540e00181002200444030407480710b0304a2850301c040c00404400d0a04048034540d000328028001417503219414503413801114144405c1040601103c141d0405181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 795091528 1250 795090278 795090293
    0x30c120201060810060302240f0703050702100f2307032a0b0103060609062612030a091104020c190503190f08090c01051b0c0a060906020f0f0c0d0816 66
    0x188007c178001d01040300f02c152440049200314440d20310705a4450318103810424107210750350110381d0071000e00c0780a00c041c40260301c03612400c070405d1016840e4000d8100311f038003003d40000d600c0410240c0d02c030390b020401c8424802140c2030701d11a0b03506040180800c9001204e005520306183d0005605010708071010f0700340700004100038102e9014140c10050140c461450300255074071401030030600705480000a405e90300c600041c48130b18042074240d0b1040082203e02d1141c036402030b0303601c032503581d2640e180d101408000b1000400ca818120b90841c0350010351440340e515100b2907042a04074142003600d42c0203001081c01242d8008145841c126680034080c18080c2c040032600c95807800299149000031002040040c9200c40d031203050315082e040101280c40a6a003a016440c1840c044c05a200404819115200d018010344480e8a5440c40f071404c01500038904001c801540c8525032141d000d0400525001c214070381c001c501a92030103903040715810050300600c112601c0ea0010310400c5108424800c0c01c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 795092778 1250 795091528 795091541
    0x1b1203072a03050a0e010309020a0b090a05040902090f10030803010602150106022b0e03060108010e010b0321030703090b1005040b040c440405070f03030c120201060810 74
    0x14018207040e951a0600c070824000c0300c20300d0060120b00c040040e10101c600501d00c00755000070500d0003040d050903903404036001360200c1d44402c11481021a900d521494000f49460140c40c0a44003000b10703220980014002400c06082040340300f180344d0108480c4207542040001840d00b00411a6680d603650000a554520800400d881d018440c03001161052020941240014120916201111100e0b41c1e00e9000d03000300021000707103c250040d540c090b072014840c15008002030400010f00306185550f09003901c14041d00d01d44682c009030030940400c044008500b070301d114100482074582d41c50101c140d0040001c0c3c038014000c1840401081807000c01c0a00da041500c105407428448445880203010070340303808004c048007003a040500012184003043d078030b102e0b0751815603200e24a09250001a00480108400f6910303030b01c00341007000b06100003089014000c00c1071a004c021614590384004045500b0494001d192030000001c07010424803d4002c0000b81440c0029141e00070111000c40b0b005121 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 795094028 1250 795092778 795092807
    0x40506010509062202130f080705120a030503060103021303050f21040b070c050402040b04030624140a1a0d151a0705100903050c19081b120307 63
    0x190000101d003a0400b402041c0c010b01c8080c043c0d100c1d090b0300c0d82c188105241e0000d18104815400c0c00844951618a6980c000030290381e140e00c043c460404005a017000b500d40c01a601070041050f028a50b104009844954950989029500c030348030080124040d01c20000404c8440c2c41b8008040203101011070711101c2d0003195011101707500c1c2c14107100c03489544800115040807074207100c20090001c4101c020011540301e02422002a626600017400720380203034219890841010900780104400703881058181c100c040003501e40080303400142907042a15018030300650440c40d40301e9225494804000001d0f16461a05540200c844376a06003550080d000e445801420240507031401c5460341c01a50a48508006200c0c41a5028400f00d00581c0f081908031480e11030070311200028080c034330400215074800c0d580c47d50b81c1d60700a840c80740b8110010501c0c0c06080f480b0454240010080b200b100c040c440388180d000068001c0b01c0006080c1100c03203c001d0a100c3c1c1c00030810030819401522821100d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 795095278 1250 795094028 795094033
    0x2334080a02060f0402010509010e01020f0f0102030615040b07020f12060a0f0c030504120c080706020a02030a090b1317120c010b1915030906021c060f0812070f020a0b0a080405 77
    0x252000a07165103e0030545010b4081307070701089084510751150b52900e1a110040c0100c0c1d10300c0200f90384007480c12103079903007000305650701100344500f41c68140d020980c81c0094008582c285410300c0820000c030b00c0b54500091260405246216aa403a10141d6441050b00d141c02e550a5207003619540c0c001e040234078041c2881034909004400264004d114070781c015500305030b55103220b405042c41a103260609150569401c5d10501210340000c04500082c11400c0c965800f658444191000c007500109894101111000061210000001c40c41402c10f08942d041d5680701070480314a0f00c0d807800c1180070090000c0c81c0c1c00015003036141d4141500305125841c03040d50132500140900c60242081c807503a001e0001c2d0b00070b01040107484148250486001d15000d07490040c0782c415080d074840440750404002c4a4500d89500c000c01600d024585290003d21002000d800018100510002c10380706151b001410f00e100d40300305106540f00c11301c03114054000c13540b4003541e8151421020f0f201010448049500d071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 795096528 1250 795095278 795095281
    0xe1f05132f041509021b0a03030c020d030608060a050a06080f03180d020907030c02010605090924070e1c0f1b050102030f090906121c2334080a0206 65
    0xe003040c2c0302c2d4803070703041c1c5100f10b4070050b60508000360f002e0f6000040706074000152418028000c0e000340079030b4426510075100051650700c5c01c0c0000c1c6c103007a0b248940c90285490030b03000304000c55010540316400315a04a000a07103a403081e8a400041c1605e41220010740710322013182203c0324000005101d150120856030488501c24001c1003091450340b04000d41094000780407039880b078000d03080000303031906500010078190713204c1c40032a810382c001320398000c2203501600e0240320303600e0000c2500b08900c2c4a0344260246c1d20701884003400000603060040d0240c84107070031141d15120f82c404440303d07499202c40441c03480d9001d41880c03200c0811003018003d54020606000075158000000c441c8106075a0b203842d41000002010007060b1a03000f07010326008107001c130f09045100002c1c00300e0220281c09001c1411050781003140206170101850112040c181449200003d030094001a11400243e00c00500c44841800d8903110080c5074807c444a04072100d00044010414824040c0c8012480c030f40c22901507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 795097778 1250 795096528 795096623
    0xf0609080c01090e0c1e0415092402010f050f071815030b0f0907020f21040e100b16030e03011e330501030e1f0513 51
    0x203030340502100d81c0c00f182480408000c0307519107a0406a000c00c43c6000c0f81d041805080c03901c284c1041c000d200801d4440009400d00c020312141c442504183c9407071511051080c2000860002000910444261016100e80512071076100750410a81c81c8034011050146003000070310048081c1d01960f000c000f14505080c0200c0c00c0708a44c0c064411a0404080407509440c103180540c000c0c03030b0001146410000f0034a10303d04035100c0388031180c0103920781da000b8004800810f201c141040301500d0000d00286c41801090065003413841542c00303442001188100c40d0f1199920300b1480d840ca5408003407100d10218102c000180c0c00c00201c0007407800703522505480c0510318101401c0b104904407000010320100b0b41200c0c90750f040c0d0f20604440000e1503810501405505141f940249a103000c00c50900c0280b6082c801c5580c107000b6000c0b81d040220040c0145109a650b01500682e1088140503941d9140009160f0080d1501c505131416004900e01200183c040140482040713500424246d1028802002c4074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 795099028 1250 795097778 795097783
    0x1e13200a05120c0105071406132d0b1e040c03060c210c02120d020c010e0607080a09020a050d0f12110307030318020603090d030f0203071b1b0f060908 66
    0x52542e00c401900f48503c1100066426070401c100030758400742045000d00d010f5000b000000d02410301003030551680c640c02c2ca40220300304519076a000c400009002020500c81d048504001c02540c041044441d41c0c0e035981050b903403640c0282c0c0c01101c10658400b80428054105410303c241c0e8007520007481312198030201030b211110000c441c000200080c01050f54241100d500c0404991101c2c8155510030984072007a0040d9000010803030851603001400c1b90320114244940c0b5840200ca1010f403080c0d1501642c05000e0f104000c007090200390310717030f0364032000c66072040f40c0341000e080c004018990a800c0c904108084c5d03440b0345403c41e00c2502014024507000c0c05503a5031075040045000861800d031070303541c00314040c09030040c030781e01c2a0607858203100041c1c1e0f440010714403c0c0c1b4084001c19a20562050040607942c22281c3d01f101d41d4810424000c90581c001c81c190142008c0e030740b001c0403080300e0380303000d91001c0d50751192000c01303030b54401022452241c115101c070100c9840340d840c11102511280030a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 795100278 1250 795099028 795099049
    0x180a030c0810140c090a170706020c03014203061a0d210207080f01140c0a230c0a06060501110303010b03180a050109080a0807081e13200a05 62
    0x5816190080000c44c00100c0d9001098100310207001c0c118420b40e00c041310000504280403008950b00304103024454603604100c103600b0500d044000380150f000c82040054030480421110511919202042c50b80c0c020f5882032034500d06020f019150307020754a0400c14010800409101c416144800400f02189441e031941410726401540c4414903003010a211451074080c41800001e502409400040c0024148448028025803071f001044610700944520502c01c0f004000c5490a0020300806800c281c0c000d400007151820051680c1518500d0001d84126000301507904045100d450703045410000389400c00000c40e5400c0e2510b0741d0740300110306103940300e0209029070001d1400c280000b8400704030380755003034050fa6521010780b410281c440d160242501c6e484201503079041c1c000100303a200507a003c0d2046602040510b450892801e10700d540c40c3d00c0d07001d418845220b191500010517030350071609101200d042e5120101c12802c50550030b0406080400e008254851540174000142a0030440c0021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 795101528 1250 795100278 795100301
    0x2404060c0b010806090d0f0c0b010e161701090b060409090f0203060109060506070f02180709060f080919020402090a0801060504180209040f051614090711070b180a030c0810 76
    0x102086c25155800b251580007482c000000c002c82000103201058084000c64007074140c0041101c44c9203069001c1c51007108064025400b0000080104240e08440709000c5040d076507140d90108103c0c032081d000424071700507500003a18052034103030031008020041d03c41b0307800766100343c0070b03240d4a80c0d0300c40540c03003241e49602c80e140e000b91080001c031001642c0e90341d040c082a07100130300d4130380710034011070940a0402040f1070440210b51458001d005a41d00003900c8140c140840c90312100c2842c01400c0741742c403880340d40c01c030748200500c8208100031556140c041d0b030f0070a01c01074088a8840d42e2141e0a0f406020b0350302c207560060346800caa00c02d500c100075494150f04c80d0054500403698a8581d0b5101d00c480403036a044d40c2c18043c03940511454007800b00400c0c014850105285600844001040070300c1c0c03000b90041040c0706030511080715004010840904840c0000811a00d1301c607403141107040d0402180f90154066110740c4003004104000240000351a0301d14110381d04140f0100030341d0100d68980628 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 795102778 1250 795101528 795101533
    0x30f080615031909080a110c0609060705010e011a09060603040330051e0f01080d0f21020a080c070c1502010b100801050f0414062404060c0b01080609 66
    0x1d81c0340c0084000e0065400040c0e1081e83c1c0d41c20303e00103200008403011202c1c101d40c041400592081d4075680024012003c0c1880b802030060340b031700c0d44d00042e054403500c42224002d14010070180203001d1300794841840310314860003c0c40240702540ea8502ca400d00c51101ea44034486400114055090050580303100319032544881441b0000580d80a5130307540102584044160301682c0040500e01c02d0050702c1c000c80d808409107030005107403c0a00c158003002008108410340d4800100a00c0310300080300c0051820310f0921008051900303000f120585c2d1081e80c440c0b01450b6000c000890002640d00900c0c812030305540707e80694880050514080c40b0355030014204464a1006000c612103101c00e40600d401c0a0000107030003480c1c440415002c000300d206200104070754200400403403c04451801100d401100c0822040b40a0f8111070074071200036011a0280704950354006006114484900d041030031104501d440326901e00c0d004040c214004002c42c1d030082200000680309800040460080000b40003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 795104028 1250 795102778 795102799
    0xa05010e07060f02191b0f0f0518090a020f0414040b04060c050408030f0a050d0e0c011b02010207090903020304050a30030c02090a0b1206061e10051303080f07030f0806 74
    0x11415200c1c99030712800e00a00a6011002450031f1803581600028101102d010308154541400c000303079504448001c0f000e00f0400340820641d5240800c0c1c0d0302d0007944c1164140d091084180c0450000d1100010010340c031110741c01030000b4801c00c0000c00384164820b62061000c0907420ba0211214040ea00c5960341c250b00c00e024108210612002806954885103400c40c00c0c48401d10030401500c48540da40d000355040460345482c196406030045418110310300801c1180c11046d80000d590781c02c5480b960395600d0380c030070015082500c240121070050500030601c076801c540b01e0540138a01c1d66000c603488850168140003400800c5450000b010700c5030592100d1850b801d4503028441ea20000600c0611001e5844c80d202d001540c4080e40b542d20400c18500510251900303005221100c0c1c0182e45a524070b900d40031315003107a60b55011103111110420324085495602c1a410301a18000e43e8100030000400400c00076842c90751030f0041c1c481e00d80256120000c0d0400c050054802940a88000b03400062039030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 795105278 1250 795104028 795104033
    0x20c010b010c212d0201060501080714030a02040b0c060f150114130b1801080a090c0312050f0a171f06050705030f03090307031101060b0910020a05010e07060f0219 72
    0xd00940c0d003504505080f13041122200e40ca82c1805811220180841000107407200ea6950900c200c0000d85001c2c01e1013003050030061001703020408000050340d8454400000140d6594840c0c06032002850681503040c2c40d0703451080581d03103c01044402c0401514001c0000b4200301a5000c6501003206c1038440d02c04081c101c1c5105c03115503004a44c2d05503110710f29a00000c0001e20340d00207060f404610011160802c05400005040c02d40251403c481d842c01d0601e0000820600e612481c1243c2d0300a05113544000c4100b02681c4900842c42031000c41c403808150b214040d60080fa000c05003006694080a16503140c401d404a06601166980340204203d1424844507001e1001001c0c46401402100c0c00c0441803000c9003504c0d4004c48212120340c0000c03550008140d0800708e1700103030044803030090000e035003440300e4070760703280030300d03c05244a000c6260300c04410500a1007542a802d80080003448035600340c0381800e40d41c00c154800d07000001c0c0b84001002c24503202181c092030150380409900159070254 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 795106528 1250 795105278 795105323
    0x1513080307031503051c0507050712020a0b0d02040303090801051006030e150108032203050c040f020904140114040218060a11030309010c0201060b0307120e010e0a06020c010b010c 79
    0x14803100505035265001c44021602110000045100b94001c6c03804901040881032400d850000c00c80603c141805048000381b40400c80c907040e1003480c8071000d4600c40ba40001880008640d0020f4026600052028901074164000700140c9000382c0b40c11040c16130b100c200c2400c0351802c031242c1d090417401e01414001c15205c3d80100c8072048240c011118a034000b5600034030381e50750a900c98459030b4400540786251505071051482d101c0c580240002c2c41d103295440b29038903921002c4020b8420381c1d480d0403008c4800071641c1036032041503018204010509442980201d110420f0154202c40314500d02c0004140c5458000c0714001102c50034100b101d04143c00900640382c20510050003844100701c4042c2d00c030356040000c0c6200320501400401d20300c00b40d02000c0e0031a42c2c0c89e0048001c1c40410420028101d42248038142c20b049034802c00204007429a00141c0180110f00080440340100030b0004144131031034014212444080e8000c106001c0000c0c01902d943c0c0f440d020003000883c0c0d01d4131401042818 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 795107778 1250 795106528 795106531
    0x10e040b040c090c080906010f03030c060b0105040f0e2410051804090f030f0c08031f090e030a090e010807061b0210050408010f06081221040c0815130803 68
    0x1403400401500d858070441c1041c2c1300c420200f20700160792903081010b850000c010907401404241200b842c0641940c070000d101048400c4054210b82c2c40360480d030f80907481401160020009410b0340851951185a95540e20308240c814100d11603944184141490b2440240c007806100103001c40f09242c800303441503070302c2c3e040388007000300382a44182081c00e00e031214080e0b0210188540030100885000e0700d40508050360704000c40041000d50350039500081c4a000c00c60342c00c4500d4a103038085448030540c0c0e0540d80860380c2c12518489007080006200050008003400b103018140d1681c4003240d4039550115000902407280d08140c0e07000c43d104203d041d0140c90f080da9108958860394094000c19008504001b001160840005800040410111801703100b00d5500a0009500b846958581007900303560f4a801006d0709005080001c0180c0720201898840c2e10000e154180b000c0c403441d01d0305041610081030f218101c203034082c40020860b241d0b2810000c510924190000302d246150f280c1b16900140c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 795109028 1250 795107778 795107783
    0x506030705130906110309010506090a0e0706081906080706030c050c070603110c1b12030c0a0305030a150b030103060c081311060903061602010605010c031707021c050405030105060603010e040b04 86
    0x1921070091064200c178000a41c440c13201c080010845040807401e100001c000104600c0341d45281403103640316010089a000103e860070303e4450026110140d81444c5034400c8201482c8407841c1181c0001e0001d0f0104110301214000c1c2c600b0402c0303900800e0b05a400f4416013180c10040d4010240c20311029000303500c4411a0740159541c5410712030031702071f401d2418003000982072280c0e20b01c840480c00d9190014604036407101000103181814944503080b40d80d07407000c0c100202070007070120004500c001130354050451440850760710120542d031440764a6184c2c1c000c1c001661218200300801c10058026a030040c080d40e040070080c09003001036160000c040240c90b46882c2e11500030051f199032540e0030004d59000c0c069000318401e04c03280d12500039084614940c4464140010b0100140c082a00010f804c0030441400c4042c03603180c0ea60f942c0807400c00c0e184407401d94000500d40fa0f404800d9a1200140c419500c0940007040340ba1070345c80c204050780c04244924076100c0c3c041000140000c045a42154000e032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 795110278 1250 795109028 795109031
    0xc1c170f0c090303070303050609180a2612060918190c090e01050a06090b0a09050a0902190602060a0b100c020315190f0903020c01051602031507030506030705130906 73
    0x202c221000909540c0005420341c000381c0c8030340034092545810707607071190402c1301c2c0001c40e074848420f003041e0364448100010242c4241958285014208000b665920300946442d5038a80e41d881002d5110750800c00a81d26913020b40c81210014114680042c40c03005080100d800501108010309801e00c0c2c044000030b03040b242182c0300000040c0d012064080d403011942d0310b1f0300210f81403a00021000450f502a4405d40b841420814081030030b8031801d94101c00c0e24000b0f030300841d403584c40d144044040c01004400079000110810350201800c044141c60098440300e5090710306d240c81e6007050000380e407040503010b5440500c0700740c2d41c00501c1c050360f80300400c1031014040d10422400f070004865090030460b00c407040104030b000b03c03032400d4085204001c51060026420029007040c0d4900a40d603a803a41122030520900180d1113201c0340904c030340c848241354010304407620b00454002d90110141c088c1c8008021908000209810746800b081030025564064a0452048030a8500d080a1f01c5054001e46070309 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 795111528 1250 795110278 795110287
    0x90b01050d0507261b0f030a0b0a02090103110c070303020d020d0e1c0501140a140c0f0c120c0c01030b040e0606091b0f0403050d090303050d020711060c1c170f0c 71
    0x1c1408814841c0c140038031030328052082c40050101b4070b07491842040c4240c00880c6844005500c110411343c020030301300801038880030f0120047e00200b5801c1003c012810021a0003c0032101c006000c80549210754240c40d0000c110b000140d0350345469034603d1010840b08030007003000c0e08004402c80802c178202c5000c41c4c1a0fa4480c2c58050842d084910480400d0312184100501600d0034054031070030031068112040c00c0e107005140d45509024a0915041e2240001840184000100400d803030b0413064401140d620707803008070001d584504548400f8042070400d1090b015601d0140300b0315921010100c0a00b9aa9807091300700102c41e035005020200303501d00d446c80c404291240402611039601680140b0ba90b0300c1c00c6080561408030b40610f05030810130603078814400039501c81c0c1924017145494001603103585d100d1804c20915003039140c010780c01000100e0b2070f2010040004400070900c580608051030041c00c20001ca40011059034038410a21518000c84c9003070181d50101d40d4040c42070388029040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 795112778 1250 795111528 795111599
    0x5030123040f1b091505041712161703010b07030305041b0602162112050906030a14070e01020a140a0f1a0604051003080706060f09090b01050d0507 65
    0x1283c003d6074035400004452100310384542e4000b003102c1d000d01081842c8108020041c40010420307c128061600c0454030b81000c5c3e09080410050810980d034980d42d001e48520108000c52540d1410000648800030100501c0074210007040c00c5a040e80c0d1901c040c0391400300785440030b41c060000580704940d03402202142e450048a806600c1010703182941c003508140782000140d1000034041d03002202c64070045a98170310090b9054802c0d010170703030b840400c01e140c46081d21429105800341980094000700001700f000703001203807039000441504100264004984a0000c112038130380c410003405015910140e5200c010820031504807040010000c00c540000790749540c0d840650102000499840c0088580401e10440344000280d03c03510030b850030002e0b490a8155605440490f1001504051001500720140440c0e6040b060242c4024101401c1c0c003540d40c00c0c843c0c010b2210b07039820741da02400d003000440d403032030907201c4441d5564000303009150031800c00351186554804181a920722101c9165850803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 795114028 1250 795112778 795112781
    0xd020a03061a04110d0f06050102250b0f0408010c020c1c02120d0e010816050301031212050108030c0111070b0f071e02060609090a0f060b010210020705061605030123040f 75
    0x130b9025016884584444c44d0913100020f4800c13515450035458207000342440355076400601c6071483c500b55000302071031a0320800032428007003040c2c0210349450300c002522042e50030f14900410448510b00020400314100340c2040345c541c0d042c401c0080e400203501c40f4164803c01110102e050180c0002d108008160009620074076005481e050000402c0201d49c0d00c804968110346042c0e030200410042d21261104403100900ca0300c8140401001c00541c0304884003d24450b0904058001304020104684c2d40c407115196034a4005213800340080d0b00303080f0300e1800382c41c0420503141d61607030013200c80100747c4440f503410912440040019041080910014207405601042101d0b11032294003e0f1040c1d05041060141c040e43c0140240e540e0351200d4040300c001407401c0c0800f95048e4008000241003061480101c1c00c189032907644079030031030000c5403180502c0004103820b070244c0440020361803140712101044d2000d0100b44107020452000c3c5200031b981c403c0500b00d1455030038006100190100c414540c000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 795115278 1250 795114028 795114041
    0xb030304080a120306050a181119110f0d08010b0702041811030d03020313060903090f0303051803010b2d0618010801060513090b030a0c03030f09050d020a03061a04 72
    0x114280c1410010443d19501131080b04080d0409448010145081c00187d148a0b140f0b00c85c0c000e5129a107890000c950301094058a002c2181c10034980041581120000c1c030042e90b000c04910b943c00740c8256041545400035141c0080d10315619280010b07072814561035040d42043c2816a04103880d03030108203508000d1982e04c10050b2050013030890307213408031040c1071a0184e0850004140343c41041481140e04050a582602950180b0042444002443d0032903014042d039101526000062502004240e04000070b0060070b0b202007060030170f20780d01c0e0080600344d034130f0051040d070040d0220324a40e8144180c3c030074140805084c1050800005a80070108291f07900c40b41c1748241c4a0340300788000c050340d80e01c04065801009685802c84c03c180703c600c407a03500489180320301c4515660703c80c2d0310201c6032000d10108240c00d8008a1400f02c5960b00c0c00c019240586200003180044d4000001044611b0a500c0c8a102c05401400d500e020508540d211401480c40c0c06074051454440b034000d8144c0d90b11801002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 795116528 1250 795115278 795115283
    0xd0b0408070c080a061104030c030204020d090210050a020f12030609091f0204080c01090e0c0903071806030209010e07140903010b100905040c050708091c081303030f020105090705040b030304080a 86
    0x700030005042c05c1c1340c41200c042c000e000d104440200030800124000300d0304c00c001c2c0c036011200143d0340c18840100700f00800300703498000c0d08903290610300d0505a81100203889540ca42e90241d8000ea40c50550598441541c001002c0340c0d4401800462910308001e5022507102e0500001c8881040c07000c4080c140b40d0180624003805c46400113807e05c0219014806004141405e08003543c000c2c0c180107450010300001048c0100504001c540d00d41d0701e0b03504010050060069049a811030542c08074020003814403404240d0080e0b20050000688690011303c861040c0c90558840e03105681181d09981c06900050b4441c1d490364940068076a0396550b03140c640007030b050684070351035a58501020300040e220b0081c004c1050003024030068004c249100c08132130b00d41c04120b440c4841400300030340c40100e0204926016080071130200d52800700e030480c3c0d201241501e000c1e07103840c20f809201c130800324241e4200711101d140c103812520042041d420503800c95030075240002c050f04d0a00791140306051501d0b104102c01e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 795117778 1250 795116528 795116533
    0x3032604050309011706010206041209050a030821071e031d0616030207030e0f0d0f0b060306010e1e0c1b010203150a0e0106080a020f1605060a0b0d0b0408070c08 71
    0xf90240c0d682107400c03444441d00a01c581045444c007940040d444d403000800241c448000c9412a0000a20440502000d0034006084a20807512030500b001c2c1600030646044101606801c140200d00c0890081482a2001d07a200b0801a80c000011200096160701110a2580720074100384811301c44511502c501d0303601c0005200e2460060340015080c1030041d1500141841081080b003c65404041109030038003e403240c805034110603000c516444075440c000f804107440d089850b810400c1c0e95100c14000c3c1303030840c00c5a19030390300d4000407495008141c0310818400c54551000c074001d0900d50710b96a0005d03010340c401c0d040c011644480304001c2c440310580340c4640d50001c108410b2a40708110440d95940c150386650f11b00e41881110901254107018840c05d2000c00d074000350b41c04401d0b404031541a50700502c0c80fa200c14040340c501c10311200e012412035090240c8000204101d145102c0c040d4412030081504a1107900342c0c81c0d85580340009441504c850070f08002d82408a6000341d40e0301c0050507031500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 795119028 1250 795117778 795117787
    0x203011e020d0b0a121b0801020705030a170f27030a0504050a0f0e0f13061112070c0b0a020a020a02100c02030f010203010f090509190309170a020604030326040503 72
    0xc002c0450700c0c0f112200e48951a40681849005079407911450025800001074108406d0343c1140f64030130650750b01030f42031503000041002c20044040050281280300b9101c0300c04420780c00c01c116451100850b20020140d0401c80020750303481400c4c980b409800194280c1400b084144100a81554814068200803490000381080306040c2042c3d20350040c0300c081001c484050414401c00c60701000540070481c895894404a1424100810740402180d0b124804024120300e01600c075869410a008404070390360010000741c9201e0048800c9030750b00d176002051541c16500c80710343d08000d401240c00c51086100d0410ba020040e11400503400d0290000d4513140040d0310640b041600d402040382d024401a40103000410056004001d100250b038035501020485640d035402840c90800d415100f02c81070012010301d0028590000d00000070b442409088001010840504c19980c040802d40250451002c110400102c0d100340c10006194040d48505248800070381200c001c82c501c2030741c0903a1079420004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 795120278 1250 795119028 795119047
    0x908122e08030306240d09030815010c060e030f0409150510020601030b250905030c010914040c0309021f0f030501060c1101050408031314010c0b0a090203011e02 71
    0x60210020080c00d1005504440c108009036860b400082c0100e0b000e80da0031115070390381744060340f20080041034003540c40392101c40c1e01301d00c080580030b03c640035000f1848040100c1d8103146001103c6080c0a01078465400c2844c460740c440000f040b003240e948541b80824000c1d43d000b054400300074030040c030000e4000309420078a80354180c085140d03580010b20400c0900501c1d10101d1300400e0090440c3c0d0006c1003110140e4496034121824a8603000000d042c444400c1d00c4854540c000030201e05540c81901101d489103511001552481c506002e03000c400100840c00451610f001e0700154142c3c1aa0300c0d0100d80081140d0105000210b11034600e80f12101070340d403c81071598000181490100645001e200c9075250040181c0720700c5c0201d03005001c1c00b00394900e0241590040701120300900c5014216590b030590340c80c847d03802140354012011200c1007540071034140c0d07200f040250004c0d504008015030903110740d805500141040d18080780c065495101e1283c40303e141c0400000b07a01c085600c0540e0301c5a010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 795121528 1250 795120278 795120331
    0x702030105100f03060b010302040e040803041101020d050f160f0f0510090b010506071109070e01140304051207050a052a0301090308150609030604030207061719090812 74
    0x1490b41041c0e8a03956000c0010802c07268008048035040b500014651402c2c1004070041d108a81010003c0e0507408140001c011010004600c0307030b4000c045542c041c51000004a8a41c150b40c17596100040d028030101c0386001c021001030010006181d00c9149a10b50340e51f541003904030394102542c4041c2c10519020900c1414050703c0c1e40c079120f100c0100100301c2c40b640c0342c1820801c1801960301072034010442c0c83c104078903890070156440000740100c403a4600301500070040c1c100e81014a0020340c4e80c3c441700e0b500b010ac1c001a6070113aa8810302801d01d0307019540040c0d45541040b00113652500c21011f41c0c2020401c01d000c0c0d001034900420301001a0204464040c047c0c0600343d02c40c500a130b00d44040a8040b0703510420a43c1c104800c0000840308102020000d2028040c0010f00c5038140a00803e000c2019000100c0704c0488100740c85450080d02c042102405902044407449000300900008451548a03644040042c40c4107001c0703981008000000c5c03110340402200e50001c810a000d0140f491103004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 795122778 1250 795121528 795121531
    0x60e072109030504030f151d010f09050c04110f071208011d01030809060f0301142812030c080a0e010908012009031e0105190e0c19050a06050702030105 67
    0x36500140008a01994000c1c910701c25440301501c60420103140c0402c0002d01115240c0790342440e07209110304095405c0301108400d100400080540c603194100007140750500a12191035006400340007010f4001e410701c005010340c0c0000c2d44c52920100700d42c031500c800e210094482203000d030034400c0040c030030074902400020043e00310701100d44420203007085050301c8000181c152540514070984a84030040420b03a9401850583d07150408048000f14050800b40b40300200f2003011102610b540189525200403521884a00780c1c9a4180403010702c0f81400c1946000085403082c51f000b04118031548442032990080b11020000450b08803d4401b290b83c04006c1278058016603000304924142c00c01c140101c004011400e90b2000300106d8956a696818000d080a07502d20a110388052808075028030f00070907084035030324005ca8000158008880841c45004070350042c0314000c18884e401c1d8020403070000c401b6940c51504680682010800340c0b91103280c08001c0069841e0340d5110100c501c105401c2d04e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 795124028 1250 795122778 795122837
    0x27091802100e011d03030a12021308030d061a310323030c1f0e0607020a061802060d18023003030903071e020a180b010e090c0d060e07 59
    0x12182025681c5e50040101d035401e980c5420720000740749100b8001d102030b0081400890b100c010a2000284500000c0003e00305170701111810888a5200c2c4c040ca8a00704240b2007000128105000d183c004418040042e4840f8007940d12014403040d04083d4000b582095401c1282c03000180c40c00701140c0405c0200b01c085802e2a03601650401c009000c006980c3c040c0c0f8041d0700c441c4070a03074041582820166001940c1080e580094400c03600c2e00c100049c2d41c905c810b2900f142c8003403421403410110320301c0082c19407034194003d0a01d0b1810708415801d00c082c107282c3c513403104003000031880e03100107175100040040e07160420200400110b0b404141803140c818103104211558000f00308009c40345001004a500950f4010500901e000d140c012031020340002c5c0300c00940101c4441804140e035170302c00c05c82d038040d1908100c060000d1b8040d6801150b031021800105500f00301e400000c1001c02241e0f002914860104070400500b4594601041c0b4400d007059458001042d507241041a00f0045d500b0b12044040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 795125278 1250 795124028 795124067
    0x11205011a03061b0403060c080f0a06120b190c020f190c05011b05010f1e0e0c010e041103010b03062404060f140a020d27091802100e01 60
    0x5070004082500c030320f802441d07a4aa040c5560004c110507041da03003030f5005190850402c200703012842c080600f030390505a61300700c403206200c0c0010300850030030b004003400c0e40c60000310710380701402950b14503e602d50b001e04030041d50303104402040d005c3d04440c0301c0c01c03c800c5020b82c014110b14402d40c4c2200d007442a01c0d151001c41407203542c500310206400002070001c8410a01e800c0a05c2810a20946120610580c004045500f8030038540c142c0c03180c9821210104020305103240b140c1907450305031005c0302c03800300e403e840a030413800051240d50b001d0000c2074445840070f0004651100001a01c102590098010075606000031041c0000750a0149940300c1854202c421a00300740041c910040388c6020300e00c04c640400c80030407103004179180300e01c5600c41e502c0b170303980380007038407000c0c0d142d4040c0d11056050701c03600002d0915810b0404c142002040c01d580f071800090001001e5042002c000003a0440041409070021640d5082005071600c41051090500710340d075241a40b9001c400040007070607a01401000300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 795126528 1250 795125278 795125321
    0xe0f01020d050703060b311e380c0f030c06100509040b161209030503010e1b1b10060602060402010201151202010309111005030411150d02070201111006030c080102030103080406080907050901120501 87
    0x201603218404101801500c2e845446021044ac0a443d0070000d410301c04843c000480d110100500014903280548801c0104031030458558050129400d0300304c8020b007c0000103c08151203118401031050851a54070784100281030480046064844900045000500008c01080310b00e502041c0550009815a46103000c0e100040c00302480d400f0f80d078500d554400e081000400000401c01c00c1507901007e4a00601401e503650501945a8608a80a81c090750912140d481c81411102d0f043e0191001070311042070003031154004400a003d80030003190000071003400942580e840350314600345400199249507032440c140c1b40c000300074a190b0b00e509004500500c140480c480030710041c0e03101003081880040c1c0307803400c9000403907180200a82da91014000c50421040303078100c9400050640340240801202c0f035944905003400c07480248005008a4010f0100703100c458810aa100d03000003201c1c003207803c2e498440c800181c402c4030a078400307604814072203515810080d00f07004a04046408002d81181d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 795127778 1250 795126528 795126599
    0xd05160c0210090e07031a03340b04080a1403090303030f09031b01050a061d07050705120307020715080f06040e0f01020d050703060b311e 61
    0x3804002a0000d10542000c040100094481ca54100044c0401d02203205a410800340240c002c1440c0d00c80b2034041c4e091902410454100010858100d0301810a5440881003c40501c861b0418107544008121740200e40002c1703500d004000ba0000d491418050030340c4948901d000302074000300003100c0126400501007590741d0f9030007200ba40e6001c000400d181d041c9942c0c100b582415841031240c616030200d1002600701000ea0305610083c0300e0b007820380040207219290507916070341010810042800381da00600140030b2611036800380032001d02c10f0f41240c1441c4855106d51585400840301500142e00210b010001c80401415414101c5014240704280d420050303002e001c00d460040c405070042707441d41072040344508200490501000104001c6440e41c0c04066108041c01050b03c4d1480020309041d400310324800841c1c01c5543e00081c03181808613141002c0b02c42c402440c0807001d00501508005000180b402000c0c43c0080080c400c0f90180390010b0410420540002100070440135462031412a03041c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 795129028 1250 795127778 795127787
    0x141b07210908070f12032a03182106021303050a0c0b0a0c023105010510080705121315140a05060d06050604091a010e220b0403120e030d0516 62
    0x295003513105c21103203241c0a410103540c4190343e06106006000001903031b0094500d404488000540310751b030b90000d582588024610313003c005000f04038451040e0100e403c5204102c8865200d2140b05840c05401c10318480041c0d045507150b58410744140d001a81200204006800c911000d040d444520500b408100c04000300a44000c41c0c1c02401600c1040551a4028034078444440f5007001041d03150b100c10001c0314a0000e4042845018001c0c521544e865107003a02414915100c1c51080c1e441c3c0e42001c0407810704020708100a0030003104100e00c901c0801c0401c000c1c11005c0142640201d0110b002c01034984020300c4c195004100500d154941024410550b40c0e42c03442c0c240711500540c01013001e46a22000400400f00c0800040c0b00c10001c00300c201030180c4501a40d4108c5082c80c10a10641e90352000d60801082c2501e400d00080c41140c1aa030700040078201003681250092400041560096840000700d50072840f550606520218070320032811500e02645a01403229035411242072840d4a001c1c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 795130278 1250 795129028 795129059
    0xa2106030f1101030f05010b04080709020c060f1003120e09090a03020601060c141006050108090102161212090501061a0c0d03050702031c060501030f141b0721090807 73
    0x30718030552011000d02c66803180d00b20645103500e640080040307507035911088585900a2050348094062120000380402091007501d11841c2d078a00604003954a1120913001001c00400d42c05849401600210110700301a240d54001c60003a201c8a840000010400c040c2243c01043d40030141e010f8246178000070340c013103440c0f4111803050030301c4500f0078014134207407801d180c1c15083c04ca0703a1b214651100b640001d1680144040315020707254407800c1d403204480c1c10300741c3c0700d90007496821003d41c00310103002441903514030100300903c0c640a01c0ca40030401400e0b089e02c0341e45000f0740e950780d1960014480304407180011114459000641c0e490200695812500e5051144d4000f003030680d10750003c0c1c101c900034400c990b901d9404c0e110310049141d40c00d001c0c0009140c0790042d640084c0c60b02140d40c814002d03620802a00e4418011550700603a901e05d45c15041d814100110102803006201540c0000e41440b400841f8500a520920b034170007400400a009455641c0b01580650002d2410080c102c910308040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 795131528 1250 795130278 795130283
    0x150c02010809010f0504111f2c2e090321020a0c031b050906010203091027151707031104031a0f06030106050a14040b04020a2106030f 59
    0x1403180c2e641c45056030041c070072503080104103410201000200f2520079840c011180044540700d0308a807004074004003500300f030f2480101040352804056101042e005403901c60566904200072010266408070700307200200c4002d502c911b03520610388081e03100e40034030060700b00102c0c0c5000c400151542d00d44070041d40845490701d01e904587c2d103a41c40b082e8400c2c02441009500401c203000c00c6952440c00d0160184da00165122800c00f0140c08611840d01d9100303c0d000e42d40590056003070840210400040c61945512441030242020107400c00550603691400720f00110742090448914000d925a917107080300d240c940410440f40420071035240c8032031019810146c1858000b58400d89021009014815a00003402d02030b41500071000d8a050780220a2245861a820f4205a201c0f403040c5400c1c1d6115024460b4000341420040c050150901ca5524a41c60004c0c404aa44070108001c2000c0f41c0c08000c0c2100001d0301200c0c00f80c01d4018140c0000e0766801088801c000711450364035002004070409000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 795132778 1250 795131528 795131537
    0x31203060f040b04020d060303052d040302041e18060e01051017071a0301031b08030a0e0402040b040e010e0709031101081512010e12180f011103040902040906150c0201 74
    0x100c0b103940c1c549174180c42138203216520400580d85c890501a20701c0e003004642d80e2010f0260604090a5000b0441d1800229031485c1390b10f080c5403c65081001520110341c4192844980e8030080805903018002c00f899070031050441340202516080c03000c10781d524812101c14581c10641070110107140d14a1503403c440c4074a4a840840060001180c00d1090a81c440c00703c040003041301c401004456401107040305e100300724004c0c2c0b488002241400c405400c0c495100250814040c0c204070500449040c070701b65800410042c940350b00c0c0c03600c114039074010384c000c41a070310303041e50043c046401070b01c20b500e4118226041446602e85590785064031050341000c00760401034140c0108140d115100b000b420800401420401d203107468000e000e00908450101c11882d104008005070348041170000c443e80c1c50310141c42002111031200a02c415000300c0034583e410070400802d0207400b0300d0140082c10180c40b16440159070340f072810b100301c4203880c55500f200b69604441d01e48404169017209051965036030a007017 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 795134028 1250 795132778 795132791
    0x1416030519150305030a1d0306091b01022b030c02061308210f070f0c0309030f020307030b01031b09020c100c0e040608010e1b09130204090611030402031203060f04 72
    0x1005807880b0711503400140540300100e203107a4030790b400900d406d120614400c0b9034414500c61104141d5200d200340d559070841d80024030f00390b40e506e24865031925400d81c1801103804c0d14000c00f000000540844504c0040c03110512200e098031507060143c020044000d00c000e004509220361700b410001c1d440c09000b080341600182c00c45800c901c4045040da40c0d0300300b410f000c0380c601d080c096003403029804441c0d0070f000412011404042c5805501c0703040d81241c050355605900c5045650b4a03c140000c04001e130707818401c108001000400344194107000c0d600c602e1000410100c1507901ca16401c000740c000000840c0184050000e080c00040d4a450401da4540049424080b0103070542c0c44294000d892900603050050110f0910b40540045801c0c1d50003a0032903503ca4182032158925090120f00036a1018200010814807440c03103109c4602c1d240000c01c005115981036442e54103c0700201140c0388070719408020442940b805100107640c80c10aa102c1a1451410340300040c8820b108807a62403180b0f031b9400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 795135278 1250 795134028 795134051
    0x503070e04051005010312031118131409030706061d0a150510020d090b07080f03041514060f030a082a0a08040e0a0603050c120109061416030519 64
    0xb10703060f02c159590504100c5540c5a04011a44030889800303100441d0030000d51101c48031f00b8404a517080b001000e1740f03803003604800003000511481c1158be80d0440f41c641c048009030f000a000f035035001300000e4004503518006071810314161500e030f43c40b150803855000020302c41c0d5040e0071013541e4008454007000400d02c1c82d5103d24000829503030081a0081801d4100496441d000154043d411881c0d440384076841d541c0d155408200c0c401c0c800010407201d0140600300c034084000c2e001d10740040c89080e03005480010700114104403481d124030f00551041385018402301e420f00c0058001c440c4003e0f0007902c081925926850078a11640c03107070420018450780800c0c84045408240c1c442e62003c0300c00e0b102c44000b141807051080d00680203001c440c850110110351046003622545c0c0c100c4e80d06c01c010780404070403038042001480640032403010303d54840802400282c0349100d00700d180103048081c0c03c01d500300810000242c40f082401d1406251a1100b40001803841d43c011074404102880c003c0784126490 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 795136528 1250 795135278 795135283
    0x30a0b07020109140106061220250c0e01080609071401050403051614100f120204120303050a0c03060f170a080c0606130920030f030a02061501090503070e0405 70
    0x20300940700d150201d1000c3e0304c00d001900901c0860b9450341d07403010b500c28082404000c40311f1000b030540c42d90400f00000d90f0b10b044280f0240441c0707410480d10903400d901c3c4000c00304c21015002c80403100300303a600009008174040050407a003d4030329040140400d01c0c003500c99980c0e8813401d000d103407142d05011a121281d40c0c8514105c40141d0b50000607114152040202039144203194098072980b422000c42c042907a0800d25840240202c2c207a03281403500011a10580710b198000c01450040394003004003080c8071002c070210580180c881c1d9400152450806c3c1441c0c110f40703007a4281e40805003044410020607c4070079900080e80d03144c01d6034052411540c0400ca1038a210b447c4000e0241401003818015650049030303540c41084e0036904c1103007510040c04c999040702c200e85001846894ac11807003400001c40300e200003900d950054102c603000d296044a480c070f1500002503500040e44010100103440080c1c020142e40d415003800e098845905050000341c98a00b1401804e843d43d550f00006000c2c41000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 795137778 1250 795136528 795136541
    0x1230d080903010f02030901140702100c09091103060a091b14131d010f0f090b04470105070b09010209040504082208030405010e0303090402130305060114030a0b070201 74
    0x34020800e80b480004c02c2c0307000c1d410446440b4081c0d46400036810300c420844840510030741c80b40e40a00080a01841c50400034040340c1640d00400c0713405c11010070704490034400c44444036061008a5100c1c58880100010a403080d042081c0950900011442080010094010800941c20280f003c803a003000414030300c2c0100101c1078038007007030b0490001d035220840c00011046c1c2d8081c000c0308180d0b030301d401c0c440b04900c0041c4607012452141103404c00c80e20046c1d07170040c6401c0c88000c1010602c8540c2000b0f400089100c2a95500c0307908410084d042240d490100c4602c0d00341d5880c0102803403106000000e02039020b8544044c1980e40d1104c00a99248030030350440341c0340c94005104001506060805408a40111400c01c1103100301114400b062022041ca034012506035038003c40c5054105001100c280d10840300c2c503078040c4001d004049466031180094040005030492211501e45181003886c07502030107a00031030241c4801d0351405040c2c4c034003013008408213030000b41c40801e0361102d1504900400c01e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 795139028 1250 795137778 795137797
    0xd030905010c1a040606050a1d04060902010c050a080a120605060a050717030424090b060f060c011a040b01090e061c08190807090602030d050405031c0603030801230d08 74
    0x80c3d5000c0000b0880258403c01c00c0da44250b40089506485034660501c00c07010100035012228801c00080000d032458003c501070f0751040c5072049212400390b075003524001032200116218403010502825040d07000e000111010301c01c207014041a0700c0c1801080451003000041000c01c400094481d080c060010135078405540003009144d83c0340307401e092078000d02c691000d290030f141e407a05490204143c503d0144105040c1c01203282078441c0c4a20040080290300003070020703000481130041d40030445081c810082d030f0b007114122071514403100b0010041192100380201d410701680d1382c0180b004800038202e1640c413460589030b180b0054010f03840500070f01c2c0e68006c006c100f46400543c0c01c00111400030043c00c4120191100d10558880d2002540d030105140101001030388203104205e1003450702e070055500507000300d042d285042441e5421155100103808a001020f442e5402041019405109540100880c1203240440d03040c66078000b0b207034441024600c0c4680545440481404000d00c2250002d51 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 795140278 1250 795139028 795139073
    0x16090f0e0a150e07020c0604140409050c0a060305060906100512070216060f030e120f1614030318010606051803070b030a0f050c0711280905040b060d030905010c 71
    0x41c3d4030480310382c2c8820102d500b00014011010054540d04125069070203440b00034501c2501c0644410600c0002c120300e50055a06110b0a510300ca55521400c0c0400041d0029583c00708040c0350030414040c82000190103d070040403113100040c0429444000c0d164036411500b10200c05880d07080080f4901403881031038116003510824005030580d00800b01c2c111040464605000600394a201181c480c3d1001100c003078541801c0004081e01c802c030200620300012480c024003080d504076194000001501407458140b58400824031404021a00200300003002c00310081c030046060400041ca603000e90000c0518450030911300c0401640c041c4000000b07445074800f0380740c40780350240012000e005600049860945000b0104246030300000859a03243c1d000210710051100c25014040310035109144c0800360240701f90104044070b0010202c01c001e210011000c5500d040c642840d040001e0050180e81c07103440301d204014000383e0400c1900307085039001d00b08804c82d5109814854250104600e41d0311020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 795141528 1250 795140278 795140321
    0x18260129010810092c0c06090d020112060b071e0c05270c0a031808030705091c08090108160909050a020c030c010e0712080d0b010e090f16090f0e0a 65
    0x21407040180380170b01501008080d1104084000068403501e46c1014140c01940401140c080d601b80f4125403a0381600c180352034645c07443d8400300350088642d035030000c18905a000a0540900a80d00801703441c1001d06079145500340025540c43c1d001101e035100e51800351810005100680800601e00c82200402440d0b81c2404d24002d1800c40f159070041e046080030a280c400c601c0ea10003150001424019448000c00c1d00c0c546078400b003550150000b490740d952010340104c202c4140c00268a02002c802e00c508182a2940d00e1080050070380f440041a1a04020a004000084940c40394800048980c0e895001805032107418851010744140d0850050360700c400a0004a0a2b1056000e5407107410008240c0d400203884a03880b4991140c408800780140b18103001e204c0d002e00700d03584981c1025905042c580c00318940a000f00d009901c044601c04203901c469000c1100003100034421030604c410b540340c5841d80b103007450710032051403601c0d0003001c0000c1c0708440020444152a4803440341360440c40b41c1c14040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 795142778 1250 795141528 795141551
    0xa051e040c110f070305240609090f070303171509060f040f0c090503070b03400b06190b0f090a03020603041209050915011826012901081009 62
    0xf205011703c001c80701c0b44265200003689001305080c0c2140002c401c3c01c0c101040d1aa04100484028003a0004078640603203007800138441020042540250f01c03d8645101e840c01480200b1222a03009000b4a00d00e1710083c841c86055941d0410260721040c01c80e02c1d001c0d08504031010038020f03d0752914040600d4640b8240d2214140c000c1e10210442e0412400c0b038001c21380350000416107000c15160144100c40c40310b4114403010400c6070424803511035100170f102120b06021982408034500c40180d685020b48420b0241d9801d1a50321a8948080c6844043c100d510b03214110209208040d038001c070106021034844d4031680c5011000004640083c503885d2a8103050504150300c2c206c1110306004501c00c6c41c1e000440d4201445035601c2548102d401010316032591006481d15a2490f01c0250721041204000c90244003ca0002e101003080c90104000c1d050036180f0035085030034a0180d8001d480100c09844500f42c9856907a007640741c0d086c81c240099032180304600c140044540c000d4401681803042c00402d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 795143884 1106 795142778 795142783
    0xa060c0f15050c031f060801060e04020d0504080c06090109030507030809100f0c020c0604030c03110a0e0c07120f080c16060e0604020a051e040c110f 66
    0x1151000c0680d8080b902c0c225200d188906002c800c0c410381040c4540e1217000c8034031424104400906010f0f000e401c203e070500c604400c10000080c02031050304d5540541d224844089400e0100781400e2a121403260406c001d10400c038445d100c0014a042814001c1091203600b40d1911392a240c0207403802c4a4280e002040c540c2c403445085e1900c001003869114810103410007003400204000c80100007410480c004008500c280e9080c00140041641480b0010444c3d0748100d03c1d002c0031300800c012541107030300c82e4020616000c4800801118007101c000403c0f1507849414091586800800180c46e4009a0050080000e003d240021000b402400007403944410f504000744c48000c403980c070380782074860340c0d0140d0f000c54001c441840210b051060a10000d8a000c032242480603001c608280c501c5508100e165200b41d440340340d0312080a0140b140c450b03110210100342d501400d8080e0b05141d = true := by decide +kernel

theorem cover : BRFrame.Cov 794964028 795143884 := by
  have h0 := BRFrame.cov_init 794964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 794964028 ≤ n) (h2 : n < 795143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
