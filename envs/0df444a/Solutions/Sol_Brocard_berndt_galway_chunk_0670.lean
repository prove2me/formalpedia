-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0670
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:02:45.917931+00:00
-- url     : https://prove2.me/submissions/1f042062-bb92-4624-add5-7368a21c17f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 120323741 ≤ n < 120503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 120324991 1250 120323741 120323743
    0x105180103120311130609050102061b03180d080601030f02070c0b1b0a050303070f050c190201020f011d120a1b0c030c1d0703020a050901031e0e100b040c0905010e0f060c 75
    0x5c196001035660035526a52a001265950015200600d20401c1c441882c00062051030007140e102d480d00342142c903000d01092007030380341860312030820000a111009008e070075a45400342c41c0000042c0b8405508040041d115418107103182d03c03800ca003100c1c0001700300c515400d403070310f12a0102c41584250303041d01246080064a075401100d40000182c191044c6404540c054005d884034010100700030100f81320303c40e5a045404088003006c0e819440b4440c2c014402900900441d4511031440c403564160554120159151420f03001011002203011301945d24107984c040b0881c1000e1040612161a004c464200240c0080943e0009000d0007100d1202041d03000c20580d00f02542074140c998180190b4400300b01320100d0080345107410001d103040003005950f40c8039401414092000c40d66030503c3c400c42d02080012611130040d1141a50850643c909104845204030703040d1070302c1a54141301e00411840020518412030141c0e6050000461551505448140041e41c08920103000c160b07075000156001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 120326241 1250 120324991 120325027
    0x60e060d0e030403050f0c0103060e070c17130302150a0206041b0807030b041412091306090608011d0607201f02091203070f060216080f0703080105180103120311 71
    0x801c2948110402c40746ca5500c03d02c4ae0008440f02500340340c074551203408080303503440800001a0b41f022100c100354448d00344590000c00fa5001d5154081d03180502d03600c14010462015400094001024801d03c12500d802041e81984240d01040d8004070b200e009020004107132642e00300c444c06100740036010040103041017080b80500d0281c002d501e64000b421200554480c0020780ad030f05030300400e2103c030b0720300d0500c0c42d0341410070b03801008040f8281391107160301c07000c4506076031000c400d60303442e0601388044615425860041a0021026200e0351608000c003030080030b008068404246454006003101003c18000480401c402c000e050020380084c1d892a0040c0d000720000d14400e040000c810091214000100d4400716800a00c04900342c04549902000790841f21100c0841180140900c002031400c0008058507001031941d45c0d201d0f09142002000040143c0200740608241c000c1500d03030f24a44296070381100d43c0b2401d0704800c14501e1104030054820b6076500c61080b43d01103041120401c0c00414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 120327491 1250 120326241 120326263
    0x60709031a0402101803240507020f120a1b0f02030c010f080c09040b090a091a010308190513030501050a0e03130608071701060302030a0c0207060e060d0e03040305 72
    0x2140c14101d14038a0111045000c1d5402513104030381c110000e030410b003e035480c1ca15400600010202c540c0d41e94403040e03e0015091503440501c900700203e0705880000d44100c0b0340100d0b0520091480c000030384401c80e941c24840243c0e24400780d000c00c44414161140303201002805800e910515821140d1510702c0b207510500200301d1290180003060000ea503c52401031a00000c02d0b91000c2d00e0b0f0300c03400310000581d80701191080d0841d1b21150180e8042e294141031900400c40f5903000160020309080c0485000b1000600c4c0e403021401c81d004001003108201070b55289003d104401c2c05180034000d0a840c0c1d4851000248840010740c50000300740041940000d1047e01001400d00c90030692040042e2a4030500f606040c034407045134000d0104e5441070340c00507444109401d0500c02c0140004c00c00c804c04109910810000b0f40002c204400c001a5000b00c02101b0950b00082201504028024081008100f1218058100841d811484030004e400103100d01408000b039a07520354803410071903117400088003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 120328741 1250 120327491 120327503
    0xf0901030608060c12041a010806161805190e0c0909090613080307020f030d090201020f0f07170a02040903030b1507020906130207050106090c0e0105040308090108040c0806070903 79
    0x1000207501d910100358203100e0070940d54410320b0a00c0032480c917045864080c000744c0b40181d00d20f100070b82101d0f50300c03041da028007040002441c40c3e242805070501407a508040c200304109044000740e00c500c581c0c200e000c050380c100b21000501e5501080301810f0480300c50740080c8500c0b004405021400000350300428071120700b9642103455945842c62941d54080542c0c901d001500c0c030381028004260210055504841d00b441a41c80030342e81000170f01d2458000b002c8104200c0d50303e2601c40219a010010a420321007484050200402040d1038180c0302c0d1700c28422184412018140441c0c02074060003c100c034164010000c120186960400400a1010158580c06405642150000003152800741c80c4070750f030300424004850340d8800034007004403980c0440d507050035001c2c40301d000040c0c000c0c020707080500300c240301c0007403240703400394000b4a062400082181808005c000034800715810b64100c401c444400e007080962600e0318641140324960b154000400e9006040c01e108409030b100701d0600450b0301541b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 120329991 1250 120328741 120328751
    0x31009081314060d0b010c0c0609090b03010e060f0703061208030a0e2a06040302090a1b050f1806040e10060201150602030d0c03020c010903120e010902031207020a0b0f090103 77
    0x41400d03a0107102d2160103584154140044107101d545600070040d1700074107140410303030644247d0350030a89a200350407d0002c80c04a00040c85002c0b05440f5100c0e0144044009101000b148182c07680c540e24041c00250f000c103e12000901501c1c0a50043c0004007070485101090805600b0302e509070343c000750742040040d81001400c0041741340c001941120307556600383c2e45d044502004024151002030301056600042c0501001001d41d48111b41188075182d5404003045240c0034030722510360b88007074890380c0080c408103004120011384a6025a400c000f4461844901c01100c480041d04600031a170080c541c0d07403000020800400700c2c6200860860300f00e030f0000d02c49501c200368161041903190080ca0f006a005016022a401460304000064492410014070341036440d4003890a407031140c1c00550111741540003514556080b48109445851040700800002410741d0019484003401d080149203000c0c003244401c15076607908041c0c4e00400303000d03d060384d0b992040719a1005a130030941a06010130300e00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 120331241 1250 120329991 120329999
    0x5010501030e060f1f091a15040e0405100203040309030b01080307031e09030507090c120b0d08070302030f040306050f0601090e011503020c0114060a140609010c020310090813 77
    0x7034080c8030503503090400507003415907900c0c50007003150b40e00800030102e48141e0040138803508841c0c180700c4050446c4203004940840c03d000802d64040b5a22800c0340168100c12103001160201c2c0150341c1990703040d0b10300300c90b140c40f141446440d099450348103402061000081c4410107401404c05800c8078407414003102a0380e41c46070800c1c1c032402582e8026000c074800c00c80395601070540d41980c04001e1298145500c040d62240c44007441c000094012104a07641d40083d0000e040d08103031603214040246038203000114407080481d00003c07102d20b00409a54000c60341004250086c4190785503c409034030f10f207486940e41d0902d4800f5101c29100941540d00c140701084541d48940c501c1d80035101450741038891342c0d28120780d5981c1d03241101e1500080580c203201e51070b001c041c20700070901a00079803a80e501542c10b00d07104125200380c5603840710009040180c0050869154902540c00d081800d0825145014090001c01d0610300d04c0b030a14060f65213811144010011381002820740d0507280f810001d40706881d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 120332491 1250 120331241 120331247
    0x51006050f0313050f06011716050d0b1b130303090602011404140a080f040503010e03070c05040b04020d0203190b0f0102190302030c03040609030323070b15120a050105010501 77
    0x7841804a2507140208001540d002c100c42c00000103a12450440f14a50030b240212400d01000ba042802c1c2041081c15407100c0c0d840801a4640300320b426556030303104600e80400150408500040141007050f1040001d6400260340001d42c645200304914540e00d654210031380c010070030761b8081103010880c50075001c18518414840c40e10425218007521906884071b880d0808c10903180e01c0c800c2280c0c480c0f005d8040024440202428610700032403034598650341488101404e42d240310300c01c4030719980b0610104000c10340e03c00802089407000c2d030b80081d0b03210003200850040d2143e48514641d01d4000010303c903140c0740541c2e802d04020850b04c410803006138018100301500124081d040c4c01030b4017007a000c501e079041512030248924400c0c01100e00e0000c59000d9141944c000c0e900500102d04462020024150800c030000103604d1008011940b0b4496042900c2480c02904800f4201c0460003001440e080800403601e00c0700d0f01d00030300d00a82503814100981c4d903451a0f000c2290b407035080000000d5a940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 120333741 1250 120332491 120332497
    0x105010b070803041104061203031a03030901020a060c030f1109040f020418180b070903140706050a0324080717010902010e01270609030302150c09010309050c060d05100605 76
    0x391184000f407850300c1c1d0b600c900c0750940c2140c0c1000c0d406943d0f804006081c48007104016006c40c4240c0700415044c11400c80c0f285000044c071400c90080c0c00c200401c038000d0b03034045529200c1551201c00023402c41000002140182641400c00c0c20442c5408603020003d841c40002c0c0c04e068004950074000c00c0f0020032081d00741e0050788241d8802d01c0d000d0703200001000464101d40d000c8031f800024082d0307209154a40e1005864151901c001180c001074040c024401c240c0307d0440850050402401100d2030120024000d103d0aa0448d00301aa215941000d4000700a8030081031400590f9058001c1c0d15851006e4455515105000c45000440c2150080007c18051b04407095016101e0f215800072038401900e4140840e4a00c80c2d40441005141c46507181c90305024028018944c0d030011440d0443c540070346001d01144504041540c85d500700140b0340a001c0407244260000c1c6004506103016281280c988185540019030001000c030b1038408110883d40300b9480b91950040b51000795582ea070040d14584 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 120334991 1250 120333741 120333743
    0xf030b0a170c04060b040b090103021c020c06010819020108070e0901030b07020c010207080303010306020906070807030306142d0d080c030c0c1c08070f060c03090606050f010c02040f02120411030105010b07 90
    0x6200340000c0106001f510050241140e040c1400f6246ca10181e000341d8105142e00d0440e4441a8040f4028403c110b00300401b502622194000707280b941d42880032440c2c07017581400c000b410810711200185c42c491041001a60400700900140c54950710b92811304100c1c0310442d8403400501c81c600b605101036100043d8101243c5c0c81e8400f4614507401c50f02d40d000650f010981554000008000c80300005403000c000b00589402076030300040d520f042c98001c814500e244150188503080c01c0440c1d5822411b074881240c0e003800f101402c480100d81400c0450303039614940100ac0c141100200c2c110030402d1010004000750f001c000700340c8040342000c0c0c04104080004081030506c0d81c45480c1030000181900b0002c00c1c0503401480c8401600d0720b19030381c010507075521041d80400280c640602c6804c02595020391805040201c0c1c038641c0c03428606000070a03c11740d5004c0a40701d90b84901101010a04503411501d20622810354a5960b140900300202c0c00200d0352142c80c0298641000010f0480a000c240c2e581c003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 120336241 1250 120334991 120335009
    0xf290109060c11061603030212010e06060315190602071508010608160201020910020d03050c0a0507030309062307110105010f0512010b0405190513120f030b0a170c0406 74
    0x410400c0d16210280e02c0c8100441d82c0050080100040680c0305c8601c1c03a1082d07100e903802594907084001c00540170780701a800003405000d030030103000c03181e034403c01980c0e0300004c003a4a18800440c41c0b4005401003c01c0e10801c0e8040c0c11100d00410b03000e0380840e203d82510050b21780317143c42c0c40103200126402c010910a180025400d040800e5400e007502030b40d4191030516100150230b02681d0000280074940c0400381070f0141e03104220100c10581c15000765580901010724041c1000207060000d882d500c2000002820141d403101d643e002c02c43d85a1110a0f0032204004034200c000c803024403164404c00c20340f00000030031446046070321550b10501840381a1a000c20001c08414980300c01d106116044180c8241603540ba03070000d881d65143c43c840c0038440d1100d004552603010b0721015800845001400341c020460b42541d40074040b840003207411058160a01e044035021250090840040400340810307940640c460f40f00141c01100302c154404070980080aa4211890319000c00046440600c42c050340b03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 120337491 1250 120336241 120336257
    0xe010b06131a070b0109140901090803161b0302150903040303140702040e0f0616030504080f030c040803160c0602010903020a0311010b1c03081f090903030f29010906 73
    0x80648841c0ca80c0303210201e201c0b5242c108040e554921025903426000b40004541d26004041c0d181c0d0419849034100400400030884440c1c0c9443d4405075101c010148102458180d41400103148901c0401d0702902060184103610100c61030000d4a0b120810904458001c000010030007491001c81102c04680e81521000002110405103a15641012000340d0f40596508100070327200a05103c1ca95404822001410647c909030000320349003400742d2003290826140c41e04110004140303800b121030b01c4c00240c0b18151265207a102400171071280f90041c5116000c0456900f00018007400e000791014410040c0752002d42d01c62800301d080380c24000003e401030b07110400c54004240201c42c00c459101c03014002042c1400d03000701244004411440801410030346080c190f041c141e201e01d5071a08029014100780c2d01003198205006411802c1c00340c5101d043d5200e0009040501070b0340010b1000c054a50180070344040401210744d600500019401d041d984840c4082c529882000c1d00f0054807502c2d1101c801d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 120338741 1250 120337491 120337499
    0x11d0114011407080304140f030708040b1305120102030a0506120d140405033306060a0e0a12030c0605011a0d05093909010f051002010f0e010e010b0613 67
    0x90460b034120a00c14800c20030003800340818051001103100b5070060b810070307042c0c000c012040d926240d181c00680e1190341050107404d0015201c1c008940072180f40c07070003d9441d00f18003414040004074075800300b035010205050304c0d0074485042d00914401c0e03c0680f020001a0f44d44400e200003003980810901d010f801030351100c49842e0244201d8064848440e1050341015140c201007403810328100c1f003440c2c11580fa5441489603203050754403500e1403207818071944002c2c00c048000c100a409000381d10818010311609090982d200c02c20b0003401001040d001c0700c1072401c24200a03014508180d026a070071400d210001c40c3d2042c1c112034034044403001c58000e61425042ca000c1c000244000313407181c1494000c120400c40140501707a80e450307007a1221000170002030050f480e00e40194a0220240d4001e141c1d000040004075801010501240c10030b1311000b503070040340c5104030b00403c0d00d003411061891406031055103c01055210542c8044000c1c0204071080100701040301ea8000c0202c2110000c0c0c0303550f0700f44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 120339991 1250 120338741 120338747
    0x20f1606090209070c1104090507120303090803070c0212070302100c0c08060108031308010516050a0201141f060320071505070c03090e070903030e030c040207060203011d011401 78
    0x1550195a0004480e00700303500180d19140d00b40c035040b000030340030f0054005019a640f9902c8100204a400304040d4186a0b15691a81107903c541400145036480503014180a0f8108942c0c0765401b000c03160342d03403030407403400341002e011014203a014180c2d0840a02007280300141e241d081e00d800600d4100c8020002008860106a020b003c880c1c0b14400800040d000c2003c01105010700501d4001c2d589680c4500aa4244c21035154018900c6170304141c188407003c03500d0b400d201d6400d4940c1c613000b940c4000760030050f07016001c0303812120803507100c1104002c2c0c4003904500803c0c0351080d2104103090242e4408048065506031602101b51406a802c41c41984803040c00602c00c4911032910709884d800c01500d81c0c804c842084581e00c002c43c01e036030310300c00030554011391440280000039000051403c020030004c1c070300501c500005087c0103003c6002e40c400c0d48c1c02c000308150014020425503544070780f490180e000e50001c3c41480d1200001101c1010580480c5007054147c80410580690204000c0011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 120341241 1250 120339991 120340027
    0x5091203090f011404061803090504090816030801080105010602010b0a0b1b0d03020c150114040f0b0604030f110102030a120c120e060601020d1d0405090c04062403020f 74
    0x3420354442d110004031106001c0c040c0300c4a00340400642c0405141a007000e10036985d500b100301c0344561000c500540000d4000311481c041d00d80a41d000109280a03241000c1588100e441000900110180803070401d0340c8482000d045c2d0b18954003d01c0b059a0f00c080503400e03a04a242c800b58018400780007070115003009030260028284207035031031000000d886d01950900b00442031000c002500040d010940c0c6004000940c042c10040030031503d01d42c50803808a16109034014800d114030b0b21074030b131614028101d400801504100400181d0340f00d0740c9103806041c2075000681211404002c0b542030003258008804c0c0c40b101d95898456154007914464000000d0402131f000009004507055202a810950710540c0018100c42000b070285080103030000e858854a40030980401c450103030001e04040400c0740034002500241c2c0c0100d066241c1400791130500542920040d0424588000003c079010070070601401407540007042c031023080302c03102c00710180c0c0318408070400c1d854810000303207030340300000c01407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 120342491 1250 120341241 120341251
    0x121202030a091e0b041211010c02010804030804050a020307080d02010e010b09010303050c07091a19031e0f050d0818070503030304140a020a090c090506070b0f091f0c0f0305091203 79
    0x48109540c4a039081070191704107810506901020480c09410020702d0420110342d0082424554401001d81c0e000031b0030f0700f40c001c0c001010000810081001c1040c1045402e1100703600a069482c201d4031420b8159035807000e504404019800d0000c2039641d100103200302580003101a0038a8000c1c3e00390f0318151280e0b4000011491144140b5400155020f50342c40b40e42d0064039041c8031442000f2200b001c00c40d00d503011400700190070010280800c002080050603803210004c1764213680303550b6194200003546da002d420f8003800310700401c103e180001e80c0c44800d0070b1003020145580410981d44c8400b0342c2d42c50165000b410341550081011034041000080c4a54000c1150001ca8641a12540c041440549642e1102da03000742c9400007202c0340354016401c070016000c181e80e6030b0b0801c1800e0301c0328a400c0c80054981d0208288400104c0c034902c8081c40616003d0a18946c0409101203109800d001068204010b10001e01d0105102d011540310f8025140192896402468040e849401c40360441d400600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 120343741 1250 120342491 120342539
    0x20c040b090c1e1e0712030c020a0303110408030f070605010e0f1302150c06101205030d09051203040c03050c060a0f0e012105010504050121060b0109050406121202030a09 75
    0x403400041800c6040704040190304c050b03416803524098503004002c808120b240c0424103040c00c0080a045038000f0b80201c02603014540030580c000c5120300070a007840780e40c21003482800005032400c40720031303a43d00510b486881207004010f40da907985000d4036041001e03541c520f4040084c3c40880c08010040c07140c030b1b40b240d00092440c591107002e8107000312990300101c2c803004c030b5400040400040240720751008005240225010442c42126950592a440350500d40008150f40f03070104024844200300304003408000c001826504d041908101c0b42c0b442c004e00c001c55440c840c41c6424045424801c081e11040c16442d181c21113031503410102514400c0064182e18108600e002a0041280c9404a6461807600101000071a0350401040c04159a8160007403465035040410060a152447c444800c400750802400a062580d140040320752041651009901a043c80e402107841004182540c00841c8141e5441c0e0341e800c0b51000c01e81e100c6c09464581408114071000c01c0042e00c0c0000040c119004201c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 120344991 1250 120343741 120343747
    0x50d03081801140f0f06150702061810050717040b030408091201050c0a11030a02030a120902030a060c0206060d26070218040201020f030c1f140106020c040b090c1e 72
    0x802164140f010449524030503640c1941801300520021075510f4205038151105603507020703590280d4880780300380c0e03100038040d880005d41c001c90380001001001c400c82d00281078070904403901a004105400c060002d4415240004260000303940c520200e900312110084010f04650b91902d0700320b581c0e0000001c154210b000881e5a0400c0442032188070710034600f09008076281d008401c0020728030140010390215681c803c0120110180d000025100e2041091030040a03100205030000c001e0561410300030340500c01e80c00135a04010303c940001000003e15070032580d450b0785180411910006652015104a07080d002088000c6c90700701e96040c5c22a03080840520f8900541d000c200821500300d4100308001c4880b0900045680c10311041c40c074822401c3c019400c09103442d01c5141c4035405420344c42c2e01c101c071681c1031150f01030058110303030007508200c83c1d10003ca40c2e603828065110002d24102602c04d80c0f03880600c60840c030b060b01000d80a2030080c0c0710300d800c201ea2000240d07454214942d403520600424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 120346241 1250 120344991 120345011
    0x240c0f03210f0b010516060504021807090914070f0e04140c040302030111250c03050307050c01020f031612110a0606091503020d030e0613080105010f050d03081801 72
    0x4007021a9880c405404006403542404441d101103c0740ca2140e141041010407885040b81c0c04200003009840d0003140c0010f003502d4070710000b409062580d004030108442e60007040083d40d0820b10410071500015014822019030307014481014201301d0b40b54020698454503000d00d0f51040c1d41e070f1001c0c07500107031000030800b000790503013083c041d8100c503c111030107800241441182000c0c080c11078a445200708003170500d020000c034006602d2410f11080418039031845035400b40700d000340b0042c00950300310b0162503403041d55060541d11000c05031000e40c054030030000650300c1c540000088580c44d0307c8079100c007040700c6580d075907088003c1d031403402e840700b007100700d601002c0c0390740080c041042d0b000e00c1040005461450940000151410f141d0040d0004915400400268990103100004203a01d842c2c500098000c100c000342d0140140c1c030391145c18104881010551440551007503040e50003540e04907250b190380e00c0402940c00301c001001000210414045801d100f214105003130b24424290000c40c1e02c02013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 120347491 1250 120346241 120346277
    0x20408071806060504031515090e0d110606150f0702190e0c071e020103090b0a0e06010509010807170f01021602090a0509030f0a03020705060709240c0f03 68
    0x2a078001c080000344400a40300c198032144200350080c0b4036403c1c024182850350f01c441c1d4442d800350510000e010780f1045409207808003100d080000d40211107007041705d5640b1410542d6980c0740c2c0342d010342c0405e1540e01030f00111803000401038800c0c83e001304000c00295400c0038400b65508204060f04034604284250001030b0b86c0c50346240e154002161180810700d03e0040c040003018005000b001e14144208401004500b0301e109075660302c00b903c90140102d005610040b001890803e00180a4904440902099091030780005401070300341f800316510360b40c13540100101c000c1c0030701c50007116500c9480d00b0480c104401d0102591721320504142c0312402e40841503d402c0e07074000012044402410042c0303d04620303150340c3c050307040300005104014034a00161503540c0d9208030300c4900da403c1000300791080090f100380c04845c200395200b020395100341001030001e000414a0301440c0c14503481420900d1807800c02e141c4548002c10705a4a48607216500c0c1c8a03040c0351266068103904100382c00c0c001d2858080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 120348741 1250 120347491 120347503
    0x90f0a2103080c1804050c130b03010501021b0307090b0d0b0906101203090614040801020c01060812160213090503180406090207030c020f060c100203071209121101020408 75
    0x648522100c0d400c03100340c6001080303418001c1c041402c6050500c1100c840c0901c0b0541c403c4103400c01d880c001207949441000c0d085074000c8504034240843c4100c0f0201300000c40c031300614102c90080e000c4132041031021010140102ca582415501039010301401c00031040603804c0b140c1c03c52006029410305a00b02d4642800c280002c0310000043c2e8403c00520120600e8120365400401e101d02c0300000b086c10503a8010013500492050504200300f00c0c0c445007000c40f00408860060080c100215924240041624040c0c075851003180036a0044800748401903803074804441e4000100c69a2042c0031003182d0801c1180644220b60001e840e0f40c42625500182003000208000e01c0150050900c8091800c1084160342891b04094101d50041c890100000d41142210216a9048980c0d28440e07200d030300841c004e8052180e0090780d0703200d618021601d194103580254020b80704d50340e542091140468038441074407a504c00081c841c2080d0843e0440440c812840300e140c40340c449002515060f900e10b5031031300d020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 120349991 1250 120348741 120348779
    0x30615020f061605030a0f060b1308060705040b040e0411120114010503071802030c090d08031b12010603180516061701061407050f0604030509100e0303090f0a 70
    0x1901c1a8003041c489801041156441101d200401c00981207100c40100b0f6404050300804084e6224032202481e026103411850161101c1e9003a2500c60715100005400c4a02a00c03070340040e8041c00e40030882903440f032801c503401d683d907101d0f4a500d02841c000c0a07548441f0002c1082d40d0001040c600e08100380e8a11441580f2510140c0000c030f900107094a2a843c4940181d00c017074440e6105c8071003009420f0850f1082802541d0240c0c0060303c0e84e0b2401091512841003c1045921500c20154401002110000385010b601c14000703074150640c290805020621903103001902102000c0010080ca501c80d4101c0e040840b500c80b901442409565911840d04046006ca0700d03150030141e005204840d44142d004000d144140d481c144294500000030300481280b01046860120010380e034014484200004443c102400088440a1410b420020000c1e00803a108922441c1309010034402244124102c9200701001009546001390b070400300300788002205d001940160080400207041c41c0c0c48028a02c2c06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 120351241 1250 120349991 120349993
    0x506091b122a21010b010c050d180f03140601080102070b0f270c1309020d02060a09030c0e0a0b0303071a1005030105040515060306090703020915191403030901120b0103061502 77
    0xc0000d0320b0305402d464017001000e0412030000e408502261000441d4003480a444c10304261380740940300b80200e0141290400404007464407400010843c1e400c003211640400c4000741c0c3e10903600c40401d03600740e108154000d05902c2800740411500001480c00b690095500c4594140316400c94112032008244884040d9003504110440b60060401002d2150404004142007113600b0003a4001482e0385100d0001030300600700400c2c4207980c580210b4145002c0d5070000304001c030080d500c41c1c0619060208a0760740c6019809d00000400f41c0c03d0000c259001c0a0b442414080c41c10050a1483c03410710f40100400f4408003903440014990f02d007031090303c2c0614020301c040d0480c18007450354140142805407545010303500c142c0c10480741a101040d181c3c140c903412110003545849250900f1003c82d0301031440ba40c80150103180e2400ca80da442c0b403940c00c070350119640c80141c030100300401d6203e01954ac2e0790780c081150340d214005008026030004810302014100001c20548801c0c59200030110182e0301c0c009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 120352491 1250 120351241 120351289
    0xa080c0903191e020a0e060303090a15020c01090e07030b0a0f090203040b0105180112020a091a180907064d060103110d030c0506091b122a 61
    0x140207441d03c0f281d041c1c158030203041008450710b0340442e1520340148035054001d0600d1001c10311543d07003482162140c50004185201e9180c9550000b41c04212803101d00c4094803600b0303105621540100d9540c012524234100220003680c40f600207401130310007021099400403c141e00810307180000c0c21404040d2050340c50040e12890a07140c651042d050680043e4480c160710342c1c1508001c0d100c0c10f092419107991400d80c0c51990b484d0700c04504081102c1d003240210b1418600c414000400301c1c1081d55803030000701d031140c203542c03030081c0300c660380400a44041c4003980100c0c80038002c3c0750140c40c0741109040c040b174000c039110031100b411a01d016801c041c040c1c08211148440380c0100ea0030320004000303a104601400700c9502d5030f950f0352a400350000c01c40380a40c5908541905050152400580082d003000546140c1d10b06110b010b91540180540c01c0e0074045810303051680c0e03051103c1001643e101000c01008013031243d030010514111410071411660708503440011103030300c3d02a51100607440850748085c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 120353741 1250 120352491 120352493
    0x105010c03020a050f07080c19030f06020c100e061303020d0c1410150602010b0d0b060f30070f05060714010608010209090c1c110f0c03040f06090b0a080c090319 71
    0x1040c0023041003c648201280a80c1c5199400c0d8400d0000c00c5a070b00c980801c08034143d030310f0714001038060302090390400d005000c802d101108158100d00c20801b0031406070b4145503965010078100020f00c88000d00180c3c007500b001d940d10360140c00c0c03441c00319016011078800007000c0d10310b16241110481503002340d1303502d0704200d10b504241030701c4800142c00c50b400203010700d1303503910b0102e1050380200201030005800140030900c84e4507a10307107004403184042c0410903c2c0070741001d0f000d902d8105c0041d01111603030842c48800762200214a1000765440a0310000600f440c040400c107030f94018240c140d130140c0700441c03082e0b2400340911408004101d09400541c5440c1001c040000403003004003460345070541000311250410340c00780d103680149041e2000080389405241e8246a074040c3c4090000800c0002885001c40b180000c0608200d030035414640c4901ca803500d0040303d01d4000b9200310a8a650180031040030f10340220b060743c2c0c0c48a0405030290030019500006803402c0028442da541d8818240182c40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 120354991 1250 120353741 120353743
    0x60108060429013c0e042c010b181005120d02161203030f150b04030c08030c1b04200307110309010c0219121b0509040b0105010c03020a050f0708 64
    0x151540d9070760182d00e01395089503000c864142c41ea611507152248044100146015521a00ca4424003500c20002950981509410300d500c0f00c5100c203100703040640642a00e2014003c940c09480d014180c41c04103485800702950800d005015003c24245101c030111315516074024199080020f04010030325481c000c00081d0901c200c1940381514441c0480e02403101e80c1c0c8111803d400c1a0703241c54001420701055094100501051070a80b0040d88800c0c00020401003075006031050360300a42412455960b80c40c4040d07540c5c0b007030300d440c120030b82c01c0345004000444110500c10f4500c84d000d000800c604007245a0320b42e506a40b0a40d11044075804410b03c00b155a0001c00d204003010081c004524204411001034a0794030b01c0e42c0001e201d68104140c4c0b01000e080300710b03000001c00925450b042c902950707241400f0744030b6000001500d14924424001241c1c80c14090b014010364001d001550b041e424280116010001c114080e13095100c2c41e10440c00054040146114000c0c1c403902400407581071090703071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 120356241 1250 120354991 120355007
    0xa03050d05060a060801140a0f0b07110303040602070605160b042030030d050a02040302011205010f12080909040503030105150705060a05060a0b0406080a0501060305040b06010806042901 82
    0x942c1c010f890310b000074001d82c1e4220700c501d415a03189190f040e000005000004030000c4e603075040408244401140042d0400901e00589a140e11a9503001d0901c07031140c06040c2e0301e0083e881140e0060344003e10400030b50b40600001c00140c250254124682122074a5120022805403821100d29075080180c0306c3c000150101d400c1503a1084901c08130003014070a01c00e080051211100c10b80c07140c4201024081401003084411306240200f0901051821150711070003500a0310059010580401d40004003170b206100f500e050710403c0300e032a50345030300b032046400020b4025001190250010005680c00b03603141d00f012489680700700b004568940c144014408443d61100d030440003a94180001c0000900114100742e114562034400a0169940000501203014540c44940d540f0b2000801003065907014a01d544503251010302400b059903149411812504102c90151141e030700c200c0440c41c00c1d8803030b02c030300c0c1d0300500000d00c08290215035611000c28160094040003a261030010300c5591560000c0030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 120357491 1250 120356241 120356251
    0x80a150e0102030f0105010806030c031b1f02030301120f08120a06140f13060e01030c0f05010807020a0f080d060905090111090108010905090a061a03060c090117040f050a03050d05 79
    0x95083d820009030384101d905040c0642414000d114001411036101000600da06032801001ca4400c0a86000c03030307641458204002d2409401c4100d0ba82d4418480d000304841d5050240d030045242d60300e04030f20543c00c2e444d015801c80381d800540032342001041142c00940102c00c07032280352841c1800d04071075810455605a1100303000240080100c540d035626403084541084d020b882d2092031002d0380f00d40c0340040090350040c1d58820075000010041c0b2640c07828000c107880301d41504403d16a207410044d541c2c0307041214007200690240c2064400035040c0c140301d40c1e030075204036001401e104000c2848025a40641c2100d0000759940041001000c0c0074001c4240e441001000d0343e25142c1400d000800443c0140604040c2540b18004540c50240421038244060342142c0b04000b007107120701c04401528040d00c1c025102e841800003181c1041c0c820320071100101016103514120126001401140740c20003803040d14003110a13504480851000e200d0b4020f01740c0309507500d075a0b60790740100030801c448021340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 120358741 1250 120357491 120357493
    0x1704080c1f0e07080f120c10061502100b0901050d0311010c0210110301030206030f0c07020d030c03020f060105060a030b010306051201020418020408060705090d0515180a200109080a150e 82
    0x961742c0c240c0c0802241c1c161508804011440d07681c4002c4101e180f07081b802c032100911161034190000303165130001400c1001d801c070a81c02c1d1030385580c10540017016a0300156499500c000c020b00100450700d0041004402540b10303007011240c41c00b080801c942180d41c43d0039003101507003043c40840f012074110304c030358280d44c03200d030350172504550554003c9070440c0001003400703402e00c000201043c0071905400a5803002640146540a69948e82c0340c020a01012007404401501c580f0b03500c1300d13004501040d028180c80000e0440c509100304444110301030481f41da80c2c20b051640e03a090104060b200d03c215080c0040302e0800140e43c2e1482d040c060850f260041090140c802d10610041c000c0741408280d05801201c28503005413141c418400181c90300d0350100c0c0040451154550000055003404007051040740d00021222400d07540800160321014082c100918a82c02c081e000c101880c1c0404928910140c189428844580c90f0703050585451000794050746c144501904189054804c0c0c0190710703c07151158 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 120359991 1250 120358741 120358753
    0x60603250807140f090d080d0606090e0a0203040b07030c0c0f080a110a050a02190e0a06090509010b03061b071b0807090c0509010309030e0d080403060c1704080c1f0e0708 75
    0x24240701c4045c01990160f902c201014807401c401d00480b44262030005101807010003190f50b90321800b801c540011f100342c80801e503440d40022105101c03803080d80d118640042c2e400c0070a940b0103074124010048010142c06008a848082020522002c0100040e51154800b180d1b109003618000d41161003030500401c45030301c019070700d034002480480e41d80d007c5030b41134585010060340000440d401d21900d402008030351814034100107010702d03150404000c483c81c848040000e034846030040c82c240c83c0c1c1ca140698155001c1d101050100010654810f2440ba440c15604d0510240b03039280e8029201504084e10501c0c03c044081c0300043d02400780c4d01c02130403910700400201c0040c2c1720141250144d41401814543d0720b011103c2030500402082e1500040107203200300754082ca2400708140e0308640825a0114034180010700c181d402180c428440480440e002c0400b5910355950401d0f5602030000a803041c00340d500d83d403450070801180810400000300c008a111100c2c41256850007e0380e40c82200164041d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 120361241 1250 120359991 120360007
    0x90f06080a0201050412051005091609020f090f0303120c0a020d1701030b0a0b0303040810060902070209010e04030c051006030b0702160b09010207050a030602270906060325080714 79
    0x440301124046d48035a0384400c010306006007072000c411945c1d0f1a044c00d14041100c800701c081400c111080505000109890300e03000c0030802c0b8000d01071000e122103800c1010324468030b001c003900b0a5582d00201100c1c94140342011101000f001074854a411040101b14180901e805200380c1441020a00d0842802c1c5850144041d04c04010712003c0c7c420b040300e9000c540e403402d4940003400e1402003d401c41c1e5499a9696220f90b648211040c1160b21a250100109480402c0c0c002c0b1518243c000341200742603400e040c48008210405801101400318a1518900054080c8900d10000101d03d100003461403941c10001c8055900a003140c0845d003000c21804440c8400840d0201030300e8030b1401040d140c050400041c1d01e0000b50f81c10550b0700c070482100000401115400504144041c2d4045411400f0b4440712048102d030400c8015034440c08020010b00300b8280440a96400042c41c4034150040001b11000650a5896014000010310341010400401d8200144060180c8080c0c591440e05c840f0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 120362491 1250 120361241 120361247
    0x504030507030302070212070b1312021e0102070f12061112011514030a0b2103090103090602190905040b0102070303020a080a02070b040e070e0906010804030309020402040f090f06080a0201 83
    0x741200003024590f010900509540750114800034100e404002c490030940c40b4100300001d50021544500c02012506011468000d01c403d2400d04680c05041d01b98200d070b0301e01450742e4038101500618110b204102c0e000450940266008000341110001e40700c4114040c1485015036028480303100810204003c0208202c08202d4268116070041104004c02d2090b264101d074101250040c0c003029000100c2441140f851700e13407110041c0d41c030444403250489a4245501c001003100c842c00c5a680e0014800c111040d40260407080c50203110b00f00040c545042e0078010030b0941132510b808400960700701c0c001c0c045030070280f0134101041000d0004210ba00d24654000f951928001001411070304007040080368a4000c001180c06410413440c80c0751641c0c2c0312002c280d948030341265800c0015141750354112060400412050160704c069544034556a40c0d5182507014100c0007408a801640c2004002800b108800042c0d004e49900840411042454000740040c0c8046400108840e00110b04210050b03170 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 120363741 1250 120362491 120362497
    0xd0f0e0d2a0201170402060d090b1509040807030f1b050c040507050c0c01050708071202150f040b0f0405120a090e100b0712030f0c080609092a0a0b07030801031505040305 75
    0x301341070444925580c03440400e449004e4060042d80340f80c104104002000003190b542c030700c140424000240000d0903201080b50070350342550301a248030420069039012900c1111409aa6205801c0564121001c0040b81100807c4101d06645940001030411803920b4140200350300440740d4908681800e2640403056150403400c040c00b8140880002c10404100000094615454101140c004610704801c80079484091034440122207a204000017403000811004150169800103a088255962808454462540508256001c1c0300e00500600f130420308030010a07020005a4425170291318141c0c040e6885000030700502000301e60304e04180001c00d44072080c4c4000303a400030b20120030325070708030021740043c11141041d100b610b00300700e030240300c154100b20b216010b845c1c1541c0c00e000c15540c41c6c05085d1107c10800c82c01c00d1140350840300b084a1803103d00c14011441c0700034480302441d07540d90818080c0d68401c4d04d00b107000c81c103c140100107000100440d0181c1c034012600c00c0c42a0700d02646e004000e48 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 120364991 1250 120363741 120363767
    0xa0f0504090302120d05040c09020703020d14221703070209160c050f010204051302120c0901050c06090c03070618061202041d0405060a0905030d0f0e0d2a0201 70
    0x15581d00e031030300103042c42040000c003030b4403036101c6440d43d0320045413602001e001c0448080d210060318840000b1982400c1c03003100c0c600c0350154003400401d13107401401c5450341011070400140c51003d01401e903521004509800306c07111000030300c00c0a60314002200c052014940513082182d0428444c500c01358444916803680b101d00d14258145c1c002c19400c040e1480c06550b28041c10500c40d174254214051030542c01842039800890b8608440801d4030902c00580c411030444003461103407800494185104034002d0844c200050502038101200d580e1101c1c5131690031184914103038006040d003c0305003414485d42014200500d4200100003804103210501d4500b4401c2004000c0c6200d903407151100070b42d050350b0140c10701001c82c04102146a0656041c00d0301075600359800d01507440416440030840c440ca00c0615813060145d4140065030030000300514039030b004500f40c180c0301e4102c024280d8042c0100b010401007515152031407032100886018242d40c010345031150703101203c0301801613a00455038202c91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 120366241 1250 120364991 120364999
    0x3021605011403070c0c0602010506130209060702010f031b080f0a020f0f0a09030803010b091201061409040c052101060e0f01151103040605040329070f090308071505060a0f05 77
    0x251104103081311000381c41003011b000c600046001044030350341900a18000d420445072100c0c11402c00c3e20640403841400c08641e8801c000708803540055004140f440100000340c2000215106042c5440203041798945100000900000401040145c038100ba80e41010304c0c0f64007182011f109005c1192180701b980b0000c0003044010402002c41d511503030f0507001542d84150826125607448030701c100560012a11148522844c1c2880c810101c8140f19040032a0084d05c15100410000c2007408210900600151400c030507156011803103440300d6207003860b20b80c1d112500c1030410801481d80707400c40d80950040d14010700344100b444148c0400d12001815685e00103100c00c580307240c03400f0555900180b901c0c0f00c80e143c0400715001032044d07044401b40088030b000d41d60808142100d84801c5038248101a131504200d00300c01d001c1050706228441c04010b83d00c05003082c0080503102e85410340b09070843d11045039501044200585c8003852800303402e8100300c09444140748a81068195205244280119409 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 120367491 1250 120366241 120366247
    0x40f0905070302150405060f0d1805070620070f081b011d01031d0309040e03030405060705031003050129010309020a061d091003030f0f050d18050d0804030216050114 73
    0x181d40d041c00c0486008103001031000382d0300e0b8080c0c07607943d6107904002c51520309d01380380040c45005152203a2060185650220151501900700074090b9103002d41301c00b03907d40d201040500920035a104011020280982a00402d03605103040b41003854040c80c101000c02a08801c4241081c0b039030406407a071640c110250f2010003024200004030010000007412a94001d040c1212020404011009003420703101510240702a0f800300e8011941c920040e9001040c03903014a0019061912074000b458103c0f14840b001029aa0fa03a01c030f0303500752811000d00040010060100400003090200401c8c661030003800e0038004041c0c5900010312581d007910400060150301c01415202c030703000e01800e0071032400040c845196824003030340041250004e8007003203022807601074000c422140506840c0c2188022907461a10340003c203000c0c2030140010305507040c4506640c1040c03000056060200c10070144003640c9110a40c9424200240f0300055071120080d1103844d15000d02040c0d900003000188489100c1000382c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 120368741 1250 120367491 120367519
    0x60c0309060a0507020409060c080703270219090c08100b0d050901180f0203010c020309100c020a15051c05130605040c0b0c07060206070315060318020915040f0905070302 75
    0x2031904c070b040710080d4042e04d400540c408210f440e90042d00c0720b02507503440503802d548006040d421511340c507040c4410412107403c900e80003101c08400151062000d01240740c43c1c0070700c074000100c0c00c0e40c61f0044c850043e12940d00904099020891540c860041e0307109102d110314104080f4000d00c14080d680d80043e440b217000a84142094214209204503424074850310403071070500e00b6011a48580403032103942048818410103100105a42011000030102e0031945100c00c004d4a41400c0641c08a8210420a00008942c3d04210031440300e0003641d103a071550783d10400c0c9426416641400a190310615000070b03c042d4003d40707420340c41002c0d40044006140d40b00c0f41844c5016107495030220b10440303030004007003450500100300c10040790016000c582072a00c860002707400352043c2c81201444001c000f4410000e0710300c00d0b0895404180c8203c2c42d03a01c034201d580c0206032140308c00c407000e2004240301200b0040a080034418a0610a000c3e002001811610307902c00343c507121113200180c402e0410002400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 120369991 1250 120368741 120368747
    0x403030c0309150204140d0b010510020f160302190602061503010f0903021c0e100c11281a0d050c0408010c030605010e0906030d050c030c0f0a050c060c0309060a 71
    0x2060083d00b006018076501c5541c6aa04065807083c011078030306c3c0240c01044045030410f140d00881c082d60201950545030b0a10040c060911203410700d8104600c2a152502e0003c9402d110b00d100700c680301e040641030319003140140300881c1112036421f50400c44141e000c1003015070110300b40d41c00a940c0c6139404082d80d00900080e01400c110810880c03400d1070448200c1c101600080c0700e50901e031460048802d0011181da064441c42200007110307030002c402c2c0300000025442889960f126900c0b800070719121042600116402c2d046514001182d103c1300c0780c440d0b09820003d45880c00410b62049018000c0031180c0100f20030303004000745d41d100b80751078001183d101c00340c220a4902500c1100c00070000c940b22180006c0241c402885010302103880e04043c07803041d0a1171201d691040c84094000c1440500d225812103855001b2940d103681800140010310140300b041c0034040d00b0007010401050006020300f00107041c09920400280720795010000e01c042c088022080c0c8960311401c4618940b1000c04803c16 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 120371241 1250 120369991 120370001
    0x603020a120c0b1c1103010e06090405031206040f150906080d1d0d150204140409021e01021c0207080f01061d0907030c0e09010b12070e040f060504051b0f0105030403030c03 76
    0xb07a1007041c10003036122850f28048006c0c5040b00e44512001d001754407030409010300c8070b10585020384140c00811031180b070000211240354010f00081d20010b04600c1e5020b034001101e6601c2e06180d88269881402c120004c40c0d4050702010740300c200080d010060000d41c01078030b80f1144030b04400c1c40464a107401e900c1641d030131749502d60f02d41d0094044000e261210682400950180c065000107e0320078200c242941458400c0265056001d071000035220342020b5107a4184690603400ca0440c8100c08001001440340c050b183c92440a540044c05203905044489051076014003602c480c50b17151940403c00c403217005411131103907103d4003008401921000000340c2044900d03000500b110150030000100c5000c031004041c4070701d40c0c6030000c0090b03490180405c0310400003002001100d60000c481402118581c6640903082031081d0705260283c2c4480d503070b00742560000c450551781500400d0004544088041807101e06000c02c581a100c210f00038000039006020181000d4101661040f080112074060307849 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 120372491 1250 120371241 120371287
    0x905090a020706111905070305160c032f090c030103021908030f0a082413020702031002090316030f060c050d0f1505090c040303030e1207060603020a120c0b 69
    0x8103120710050b13000543e00c2a403216103c103e02240e10107071400403610074400e8402c9641d15545452031f0001c080c0c000c42e00900340c80b900781c03841d2445d2000000004c0030b40985103610702410744d80c011829498051064a456525007250107210302e84100108441d00340110381c19070b6811110008080710399820b841d101e140703030380200f000362100040300380328007080724041c000610083d552002c0d0395450a0f181c9a50100d00e948119802502003018601880c0070f030141d41c0c5401e283c0d01b00500b042080c2c0c0010f882c040c5030f03494060b541d503400100090b15007010710114240c4214600d10702482413856030356003400c175100d240c06400395a842c07002c0c801b0306114508684010024000500c24054100d5400d401812907031201d41e002052103000140300c1c100b035171a90348100f030304000f15400c041c50364400b98081d210078402d82070b442c05012110150f02e407154014007206401190001192411071040c401201d81c2ea4000e010b1809840715440d00245403011600e00b69903610000176100e80d621071b0ba8020340703004010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 120373741 1250 120372491 120372503
    0x30f050303160e01090b0d15241d0409020a15080f060f030307080c03070804090204091a030c011d030703050616050c031204021906020109050d020106060905090a0207 73
    0x4110024000008003460065100100000458008840668a0405007071010740807801e044070070801041e50320003a041103140e140000c10004005010328060f03407010340100c0b000000004151181d0b2140001c0d100c40e2540a040016400604005000c0c01090340c0364150701c255150852001192903980e5240c0040c04c5084002518019040c00a0310411013110001c030003200c1c00d00000d581b4034025804007544000a07020b1450710301d00e511030024507804040d06c001c0c5844104940000100341c800200000c0206100060f00c03541010340701ca054030f90041074440d042c4204d401c0054140d5003c903030036043c0f060900b810701c12040e40c40d07210f6188681009031194103000300c00c0c0000c24050080340e000c0c82800a0b8495117003c11241406651901030005a44242d80c4180544020f010201107026045800107044c00400d50b1081ca5000c19850300b0741241005075120348031481002410000382c258240d440c0000e001c65428101d0007003071801184a0b080c41011000049055100154111402d4940200b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 120374991 1250 120373741 120373763
    0x140103060b040e0d0e090405030c0316060c030203060a050906010905131406091b0c1f0c17011a0a030b04060906080d02010c02030d0b120a05100f0e060606070c03 71
    0x41000e400611021420714062418418901001c40c004038840846860b152941c05904c0d2125044c0a00880e0003002110036100c00c119400d0315000800244c40711400c080d81c0d800036441c030f170300d800819654403080000625005009005003035554100401c01d48009036100b00d80303139440d000104e03806402c5130b1116801469501d1000c80d100c072aa04000416800c103007034100702d52510300501c0343d81f8200325500022064828039001030740d6501001401c01c82d0b028021503111140c2400704503400e000d9040c440001e00e54603868103100c6900048001c0362401c00030b68003550b40d80740581d0941548207030483e040c903403400081c2c44160349000354041c410918018204110040d00ca0607810010100350240c1e018912070b0300301100310944140221180183c0355405542000d6600035000e02070800c0450956010943c0480003080402c1000300f50180f45c00b80000300608003024100900b00c0700c20341c102c002c110342807035148400101d000072001e03009402520401c1e5203035036a007031103d2001c50581000b04204004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 120376241 1250 120374991 120374993
    0xd05040b06040605030a02090a020721230702030a0305030a09060e030429040603090312020d0c030b01050a0e1c0209070309031701030b041202120409060914010e0a090501140103 78
    0x18600e40c46410305440c200405502c92042695075030742500b0003903101d030f400d90005140400300c2c3c0181240c14070544220120540701c0e03046034842002c81403240001017803000280d0150f07242c0d07000c0741e4155031031482e001d1802d101030700407a803070f00b48081e800b509112002000c240030210551211034040c2d005401007040359030501860703450381d0107481a0900c040c101824941020203020451070013341c803400d0704d850f0503d010002e6010b132030712040503001e00400002a0810030002d0009107049060840001000030450101400b12942e015909040040510501914541000c8410340841d0b04a030a0051030780d040d0078100180e40741000003508a4002410302c44200d41640200c4c00942c0700c1d840b612100300c0c80410340810b001d000d10001d030541c09d2400110303021400d10810400400c549105495018072030301085c1d00240d2050307000007000c03692400100702581ca03034440e4072104004204541502e51508115502058020709801921a900c0040c4400c1040035880000002200c000001c095a07503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 120377491 1250 120376241 120376253
    0x503030f090f0708030d1b2a0f030c020108070509012007080f300306130f02040f030c0e04081e07020901090b01030f0908040b090a090603120212120105040902060d0504 74
    0x10031070b001c1b280e5040132041c2d038059000702c80074500c8510300d40d285114000300040070007041c0328810305000d45008c4101c5050100b2401c20000c20704c540a52205040c5050724030005042c1d03200107145204000c5c0a10201d00d00d030707a1060360001001c020f8060fa295031008400401e090809079402100940710b164140103c641c0041400d1141d481400360005000002124041c000148580d13900c612030010000141035180140c000390005145000010f10100d2082040049a1094000707000c0100c42c00300070020009010141c3c0302600c0400c1a105250400da511507010303000e0f0b003041000111400c848443d0030501da800341d07001e19400400381c4600e940c0d110074450090005030200350019041c226440300c00b15241c052442021307402612140307800e180c0000c1e0040e60704020807072940300034040400285024513000d0640510b000d01801306600e031954901030300c3e090001d10f99480252090264144040b444502c1c581169801d40300032a240c101840080c6da14855001c048031030b207107404184418014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 120378741 1250 120377491 120377497
    0x22050a09090b0106050a0f0f05070b04051e1b12030f030f011406191202040509090714030615060901030e0f010504020406090614061e0a08040b0604090503030f090f070803 75
    0x40030b41048030503640c0310807040300c2ca03100340e007028404170380702c00503a541c0c161103404050380c803488034904141844070035611031030451416601515541d01966100302d101d0b0b510206403040384c0c0960010814601210310000b0401c0140d8480c88c0304440c180983d600d561014400c440c400c1c01400300456480ca015030850031080803e01031181502e001c802000c1880c20b04908580c0e46c85008a195400d820000800301c905451204c400d00c02d10382c09103c00251600ca0003200c0f4001d00102d405040c000b41000e10451741c910030b90000d244039a003d1000d0290300c00d100300d041c00d0381d0b480c1622210b0751780ba203423001600a4501b0600c0c02045d1b02c65007140b010420410351009010f580300300d400b804a95581e003d440246c1d031702030051408680c20084144050b20f494030051201e4503040352000d100b1a01d0800d00c2c43d10360014821440820b020b101000104a0250070b0180e22040446040100741285e48900341d0b07030b000081c401c408462075000440d010141c1000045440c01c18141107500f0503407140440303a1aa0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 120379991 1250 120378741 120378743
    0x120307090e0105180c0c0304030303020d0f06030206032409040b0f090d02100e010605031504030e06130303110705030706020f0609010b0f010c0602190e0306070801030822050a0909 79
    0x2030650900429090100c0c100c09048840080c20783c1136000c4003821000941502034007100d198075042003a022800810f101030002035010303450050b00c50f810003840400340c590b00c610300186035103000014801a5031b09825030fa0844014914840c41380f20981c85d000c1405280b0313941c80d9205030404100410440d400009912944610240d244543c8aa110140d5903a40c0002d51a0141c0c101008080d481c914907071042c03403800c440c00000301c3c40b541d0314004a400c088400300305e8072003c1d00b14400c2105242d0001e0015090103c191483c07032806048071445289444180001400c0000301c4403010308a00b0300700301c14000b8103c0241651801e650310140650340f81b0901081c00c04500030240060000d201c1803242d46c20720940a0301500c3c5034031a81c00112008084d42c10201c1c3d550b6404d1140440c1e80302d8402c000c0c0c29401c0c4a45600d1391030012401090714080c070080c40070702040302960060001800400c10344601010300348214660310b1603600b12003402d41b00380e040190012503078900040d06101d6508840481 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 120381241 1250 120379991 120379997
    0x204051f020114160c0305160605060909030702030601030f0602090405070503090c0111060c03072c1e010207050f040216050c0a150801150e1e090a0204270e120307 72
    0x300403200c220f20b0020200d400b0109a00314181c1501450b02603d140348445100e4500140b4140c00c001e56651600d01c941020346c5c51a03514800c0050505022031019003000c40d03000114200b4005a00199840d20b05000040055051035480810801950180c90644d90020028803040c640000d00504580080742d10303404030b214640c003101403075003d00c0100502080e11800317441903070f03580d07020646140c0c005402d01003080340c4401c00c2d5003482c4000c10040d011244d66506202030551040402030809540350307650109800441034451540e0700004d8001c100c85054a44282001420300060001c2c0180e101c0e000b20f00002d2445941040f0780030a10003004002111030210701626183e4040e11241040b8100012411b0000140001651041007460081951170312503030002255021620a900100f40014480d40d8545030300c4003468240b14090b844412907408600302441e1091801a00141d00d1280030300103001540418030300c035943c0058000458031000c4032030002c0c402c19010600d90080b5244400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 120382491 1250 120381241 120381251
    0xb0d150e010f060f030210050c0307030f0905060a1209020f030304080c040617120c1c0f120507020d05091203070c0f0803030f04020907031508010614030102070f030f02010204051f0201 81
    0xb0607140b0b1241005460080303000c0032540b8190307401c0c03013648009001d2000034000d0910500d400c0840c1000100459803081c0d03100080c100c21464050700c001c01ca500002d00ca0743e402d0010b0808558080b170210b20700c00000354007143d000c02c180003040c1c4088484503d0394040c00005000b2514900001e4020300111060310100951580d0304842c0c203114504181c40502074112150b0030a0f60600040500900c040080075111961180d80503500740311030b0f500708500450401c459008503250000030030301d00c00350b0304002400b4510745107030b009440d03650b08401c40040c48000702d4542c0c0720342c0703d5a4a11408003140b20480e80c0c2c411250501200740f061a20406030030390440031000c100c031040803003030701d00030300218001c0801034039550f01300007405100400003000c25541341000c4541449410b56400180030b200f000003407242c1051320300354070b0500c1d007508140a0303070040212a0000f003d10104100c5550981352000c401000390f0402c0340603206032303400964040302640d4294107101c2024800d50034400180c0003081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 120383741 1250 120382491 120382511
    0x30e0609030903060112141504020f0108040c0506130e010801050405211c2c01060807080a03030905031b010b010305060301050732030a0212070206040f03030b0d150e01 74
    0x7903070303116080100342c05030002d500401613245030424448426200b810400c1d4090145545940f078885090603040d55265801c1c00d000039801c206810103404c1000307181007180d0f4500b640b00e442c00707103200d445094001c21002418401580d200802c9030003500400151b07a100b940e55565041c040c060584082d01c075030054003906c010300e1101944589160303070180d45050030845041308042840c100050191b2419456092106034001c0c200801b4294000309402d0700410800d40e1000ba0031510250850030a5500004050000d99000110201ca0a616140200788125030b860041c0c2140100714008100000c1000320300c45941c019041030100103408e980400660340e50400705030a13078030f09448103004a0301c02c4a101b0040c07003020350054080020712991034440d1100780142c410b154402c42e48560f91a0b404551014500c0741c0c1740030309800a050340b0090419007041d803030b84060b07081c4c84400103081c96900c0200031800d44503600b82001440e080014404a004410340d0340024010100681c0b00d0744d468070007001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 120384991 1250 120383741 120383743
    0x90c0306060d0c05010507060e010212071e0815120a0309030210050a270b0409020403051b090f0a182a0b040501081b0f040e070305040206032a0307030e0609 69
    0x100c0ca2600070f4019801945408019512036000200540c1d01640758040c580c98200c2c03d000030720003c80103843d1031038140303403209005180c4540241c05800c545000303001d6641d501e6008018a401c01c03000c89440806080400000d810103000d60419071990240c828a4400d058228102c9000c503130081c6d4010401d100f030507104541c14401e10701031a0110ba002c0044008082c290724004000503c00b60010140e2502e6041000d61a0001d0348000d801a030005028401c10009014a034489429050011881c20000700002da2401008102d80b0200703450100055850107203810501220b6000d20088580e030703010b800c01600c81d034854410901c5050811100d5440f150641310b80804941003100d486040605000045440c07080180c80340d08600d00c10b40c036020001410000601080901c1e8405541c4c42d8a0105540600c502c000c0502d024580303024204005610f9900c1120b5100c12540b2041c103400001a012040c56902d0213528008107501004005109806074041c0c902d21500e60101d401d9503490016003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 120386241 1250 120384991 120385009
    0x61205060606091804020a08010510060216080303010303080a090b0c2101060f0c1406070c05070e060609090603101125120e030708030d0504060b18070e010e09090c030606 75
    0x52034100b20440c0b1940562a06590f026800c54401070107c0c0000f42d50700705c0b43e801c2d2032061300d204800d00c1e034812017001301940400210b400244000e04202071185012a840c3d12400140300c080c0501860600103100b0b80015448480d200da07011041020505012012180b40d070800b4003881d80c0d624000b031032a452218031150301c604035242503481110074010964222a51444044112414041c00c690310901714803d0090621688003561130401c8101c0d41c1c100303030349840320ba0303801040021a088140106c0e03844042c201c2d0a020300c00d54440700103880e0700c80800e24081603001042012450100044941d120702c40003811840c5580100380940b80c90f039100143c401c92144001000300c0500a125078009018901040503820700405030b400090351000c42d04e055620003031004030f51658030020042017105a22a0741c0c4c90303c806548030f4000e4030415803403c809200180103607080c0061085120307540e81c0310b4200c1c4202444040e105165605200d29200d40d100d8441c8c004512134050b4800080d001d003060207603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 120387491 1250 120386241 120386257
    0x614040c05060a03020c0604050d1808032209050a05100f0608060d020d150504060f0c0f08040510060b090a06030b030a140307061406011e090b090409020301061205060606 75
    0x241044245030504000190f48000c040e8001e043e028031102050190500c641c522807800340010b404061000c00009108440d40404461301200e84507090010040010a850460740b8440d42c410b40c1040c01d8000b182e003e0800d9118510076414102007100001a41d0000740c09041e504044c00390240e01d90062003c14685400b40000150410001400615200104c1e01e0064009041030700d008449482d40440c442a1031080c004c1d043d1500140f10401c0038511541c21a0081120b082201c0b6060b420300400c0035002d02e03554030420403c9000300b000d2007020300110000070300d242010070245544d10546920344c1c00803a600c48c07141c0c550200014416001e4015110f520b2002000f8104d1442680e484112503400d01c10b80b004c846c4400d101071270001d10a4030074101c41b02d003216201d03071070b40c549000010550b0081848018200a80290505600d0713001003214040c0e030505103032a5203680400c0d0202e4020004284040d51540c2002400039160201d0210010007900071006c2d40e02550311181442958403411035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 120388741 1250 120387491 120387503
    0x80c0a0806070e04110706050405030c150103032c03030414040b15030c2808090d090612020c0a060f0204031b080a0201030e01020c0d091508040b010e0402030a080c010207061404 78
    0x203c03581c081c0c50281c2c4042c2d4010904a90325082070b100340c0b10942250000c4800b1a02c03a48002030700c40c400712042029021061981e450404950b0441e6001803042c122460408820078500a9200c520310032001e100c400d0100107404c80303841e266210f41c000003201c4c0d104a01d9010701e00c0d00c0c0c803030006414104203d00140040ea0308462554403502c4040c0003a501543d0f0500ca80c030b0800c0c50100c0480300000b682c918950007651440c005041c643c00391030602c00340742046820301c4200c150401100b900800c044040f4007055900588403014031202d0340c03c282c99410b00a1030385191081c44030150041340e000d001900e010740030802503171242c0314590b00348002c2400341c81081c0e403058242000640c82034100001c080e0a00001504284240415501e4034038030710395210224156000501030b800d2440100c03805040f40f03141c108100d00303060310f80c0c0d14454418051410340e40d001c1d43c00102552001c0101c002080d901c00f08072561003502900c068000e4004080407629141000110806441e5180c0310300e002e01d41140c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 120389991 1250 120388741 120388757
    0xd0c05040e01060c1a0f15010507050c13180507031b030809060a0e04020c01320109090206070209010e0118020f0a0f1e05030a050604020301030f0f030315080c0a080607 74
    0x103000c0e42c6800054408481c1480340c0f0302001000380d502d00702c0c140904d011044440041c00e21000080e01f000300f6881c20b90411800340956008214000303003910084000741d6000e40c0c2e10b5070584620b405040c60252480c4180010309003401000000640c1204130f0f401260001c2e00d216005141490320003040c80301500c81c59041c8640d031220310b0b005d0014030044c0e80b182040390001007604045400e9030040301c15000242d540b980e11383d80c410006c02800c480d420700c2d00079020400e05055074810160b081805180a240c2d41d42c00710000310340300c01c8121060150000d02c41d441940e036230201c48400321402d0007220242c0301c1c4400821000b450a00039a0b40010800c15101d05203011020110766006a83c18054104901940e0044d800c0364403e194034070000c0541c0d22a0380c2d9141c40480f00068a802030900380c0a0381c030400040020500d0011410181c0354841c0310020005000c1c00d00f00c010b410318a49014041161180000e065040010b04160142c03050f51109811030f03070b8180700794841004464240105440d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 120391241 1250 120389991 120389999
    0x3030c0c0e090624090910061512050a0209061c181a13020402040603090c0b031e0a0f1d0c030105010807051201021207050a110303060d0201030b0102010b12030d0c05040e01 76
    0x400c1c413441c02c10003401300e00b12198002000280316100b0688582c8016040034090840c061002e010304000f5151a217040070160402000c02010441d00035040185186d82d0030108a0030009601150003c140003018103458440c406080e003078160044044120b000d2400000311500e10880048000064214010050354400c90862500f13000d4010422003600040b02d004400607915032001c1c001403c503d0b640002c0802d01860030700060b01c8907411901010703d003441002030904000c22411000c2494401104954a42c01044000f41061410700c5985504102c00d8010404101030784500000c1480c0480d000780401030141341c01c030380302800791a4054012860a00c481d0808600305070b54213014500062600802ca42000583e601c10344844d0009640022411003a680c44444002c45401d0310001d1403550a0140015692411240d0f000303050684450804561743e00030740c0034449503c40900b100514440d00c891641d1a54028085516100e04c0c2c4014910440c0c0f04000b950143c4070401046000d40e424 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 120392491 1250 120391241 120391261
    0x6030d0503090f1f1d0c040b0315010306020a1209020f09100503030c030a0807020f07030605040f060e1509012702031c0801060e04111c060f03030c0c0e0906 69
    0x140b010200c3d100c0c1e034800c0e4035a41400c00a011020540c250701120100442c0040001e0350100e030fa100d8044008940d40d402d51150100c0c5400f0150b404071000174001446a002c00d040c956003034207881560b07000c0d1000009001d40d41e00140141ca031a84e0b50700d419050300003101d8003140ca00104c080d4101da2400b20b40452070812450180e00014054607000b1403980e1003002070310713540c018a1524095003000c181f86002681003864141c0080745400600008000d50100543c0c03250180310180c04a42c8540104050048450b00802e0b065000803090240303c06903411240d403845210540c0c0c90180d0410006400c1102c10b01c160103040171a100760300352489100c080342c4000c141404040c0e82c1401101c032000320203075508070482e40c4004141c813804410343c500303440680340614621840740190300380440b900041c4146c81c1151209404440301004d500c0d00440090300419841d0045404003903185000300a250300104400e800d03503c12a0304907003851306c81d964000b1120341a9608140d42c1e101902040800d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 120393741 1250 120392491 120392497
    0x705120703020d24050913080d0207080f0a090f080c01080a02091c05060901140106030c09090c0e0a050604050a1a161a0a0b0604050f0a0305010f0501050306070806030d05 75
    0x914016040081003d100c000702c2d00c0800469407602003600d09035041c01100b1901400800c0c040722801a14540744400c6070000700743d103800805442e0300203880c1d0120f0845030b05441d091500303c002651141d240e00e000c2c0f030541d807262142c40c020450102c0e0008995005c100d08005542c2400090203144420400550300003001500c5502101c1d02402244040d8035061030b0050040482c000e820804000390a20724208500902103407500d90400c040e581c0c1c2c0007203500c00380d41110010f14001851807035001c402c80304502c070394006070380c0c082c204a4003000e0181c1c0000328610220003125175001103a554420004c65102c1d61180c05c0e00001214030810a0303d50301c2c0c420214101202410900d4062880320314640c41c003602c2c0c402c0703c003441694421031050b10382c291146e41c045581c03078040055194000001705180203920426114480728161540b45840d200903401c020741d48400207000c0c440c0c43c0d80c41031001d0502406079074028071482c00000c81052180d40254000e090103809408080540181112542c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 120394991 1250 120393741 120393751
    0x120b011407060204051002060907140d050f010b030d0903020d02091e010305060a050f07021b04230a0b060f120a06030f12110106060210090302010e0d020705030c040203070512 77
    0x240e080400d081001120080c8040d80c4140c40069450b4201010001754400d000485070855010004104600000280f202d064a110180d8000104480ca00040c880114203400a002d0f00507442c008210742c0c415001507003051030450a0b01c6249400a03011903602c4160b220181d8445414001440982481100c254100202000903844d9085a18003410201d000f071380200c0d0b881d0302071800c01c41c0b05d903c0e9200303454000c01c44e02503948032403d003131030000d40c0d42030b81c11141c02c00c000c2d11240c5445c8607610341c0d000302c0d10a8800700341d030000c40000c140040706100d02101d0300e10b500e50603d0795640c82440c08104988a1011903514203041841c01c3d10662001c46c00241480350b0700d80c0c0d41c0004008980102c0c0c4e118442c5108105440b6030445004004010030402041c0f1815a8186001844032a4005c209011109182400080d258000d41002c82c0500f400380040420b5001e2001e6058201c0d5012440b2801d42d1810740451b040e0071220000e11007284070440301103001400502c10301f600e250002c0b540d15045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 120396241 1250 120394991 120394997
    0x9011503020918090607080c0a030e030c0d0306080606010206040506070507050c04020706020702011101060501050909040204090609050a0606060203160609030e0a060e041103090303040323041d09010c120b01 91
    0x40711080010401e0003e80c1c2514084101c940b10411985042c00c10500b079008401d4942407607a800d20180038541c9002e0108440b0515803281c248c03e542040070000d441c005100a41110071280d0384a10240c020f18260013a01d0990081200044465000084041c01250310000820745603039590700c1290103402940e0100d5513401540134140482c0d0361030001d000c00c14002c200041e0388501910024102c4040b00301158880c1e410305a08001517078004041c0c0340151001d8a40d010190307510310001d0020480074a00a0580c2d01c4d100c03844d42030200015100c00c035a031044070108005600e607081070341d690240d90100c04104000966010016038070740c00580b2203e03c6070400408c41030f000800500607041c203402c003900040740414840381e04c2c0b501d4041c0c00c0e0600c14030045203103542030a05c500364076880010700c00b40a024070030381310004840c1e4407071811301f20300c04200445440f01e803500d080c800780c107000750b111001c50001d110100e01141d006105001d866080d41c0c0300d64803400c51103106e58000e002c03410b4085040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 120397491 1250 120396241 120396247
    0x61d031c0905030d0e27070f03062c0a06031709010c0b16090f0323100e03090906010e031c0e1203090312040e01030b040602040b0706090c050d020901150302 69
    0x1e4400f0800404a160b5989410060003050300074400c41c03485001507005070706150302180700c1c1d900c0c40351011b5070451001e1a00c04a900040142500940340b968070102d81c04e209554003185a000d00444851000240b8694504a40ba408a44d50640d06540009406c0003261641400900f202c2c00082441c4907042c101143d070000301d0b80340c955000c2c00444407504281da0810010203165848110000a01040e001130400641035840340812000c0d0b502c45014100480b00b40110304007800c11922603040c03110314007840b9101c401103286843e03812203152203000720b18000200300f09601403070b5400300b0030401400409003904641e41d403040d0415024040010301c00d0728404480c440c1c455510010170101940000c43d44c92508206251801001c0e01c003d0041d60b00501060042c460125551030440c1c3d040340d0030204039107482c2041d10081c0b14036440698100b00000d02d06042000c55002184034034024400401d0196580d014401c029007981c0d402540092600e0050004141060001150321428079005003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 120398741 1250 120397491 120397499
    0x8060c030402041107050105090c030708030405130603050601090605090a0b011205060613060203121506030406020a1704061b080114010c0c050303070302030d150513180c0b04061d031c09 82
    0x40c25400305e001942d060351114200142c410040010001d6600b0a600610a4070f00d0046660380b00d01460090310711070901c000e00299000c1c5030b604008095500306003603507460359481d25410020031031407140318000c202e0710300041d1109003280700c0c455200340180c54009040121000d41001000018001544050140400d20300b40c0104000b410180c14180c00450340c9404603804800d001000030074078440e042a043d0000450344681098a400a0340701030702584a2040c2d807020b445480d1062058205c401d210310420090144641050f101c06c6841c044284180000380400c50703180300b09002e40c0c008001e20030b00803803141d4814440390000303a0048020108140d126400a42580e128600940060340042500742440e5500e10410200c0343c10300151181c5203281c003001c64034240700406440b2101d9501c0680d410099100e4503141c003615031100707154845a80b40c412018882c0c12a005040002d0010380c0c0f511003014001d1b89481410500070002c0c21000c0000400741414404002d0301401c000c3d00d60301c005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 120399991 1250 120398741 120398771
    0x1030b100b0a0e0f0301021602010810150302180f0a0501210e1510030b18010b150a02010e01090209060d080c03160308071b110607020a0b03070e010908060c03040204 73
    0x2001d802c0c0030350f50b08284401d8810030003000c0f42c0306130000d52190740b0401c1080c1d29450f8110a5600107942820b208405655100345c2c62054409035000200180081d0700300d45d01c041e4194000c19403c1c4203072100304641c4074210f013445060f0301445d001a40110407103805101d03542c01008482440c203455106182c0c4841161050800d40e14076001c054850391210042c1c0032181411002c00740e22048102d0250001e07442d6466107440801d0140840201b00300203d8101d0840d81d081d0040d14682d00d0140601c220001d96580e88a100d50004420310015403810800480000381030003050303034640c2c00a100c7c0505407180410440000521081260f004c40100304007048008107001030400c0b4910f0386201c016120301407c000d40880002045030301001810110030b0381d0110800030764040580c004000540718a1840c0c003007a400e10401402079405074a070400010003d83c202c00852242034699a406c6c4800c00400c010b650784ca0032801421072540100700020a11901076001d10382c090300040000c200c5c40f0310001a8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 120401241 1250 120399991 120399997
    0x5130c0902030a0615080a090f020306040c0504110c0c04020c030c06040605011505030402010c06090c050a080307170c0304090c0509040509010e01060602160501080903090301111902031201030b100b 87
    0x100203915004410011266068401c0100a00c040d035940504e158151034000d260b03503401840c10340d80c507a50707017000e406100c010703c05016041e0780901102c005050a0411505020300da00c6951710403414104400704040c982030070b4508440c3c942e0000d00c1503500e000d04120280d04000d04080c614801449011340c000e40800000d40110301503540011035506000092254034020012802840810000d120050364007803580713020142c12580000f000d00345403078040f100c034226a2000b40e10080700a0003185494002c002005a144203030700814040b100f0190383ea0309401030b6204481d480d08144400c011440c5290403183c005580d41c5010b40c507203905040000c1c01c4a6099640524680d580c044407100780c036007440344a0142600e400103141d02002c4000c11008046903001e1181044030720004540025030402c15034110340d000400078405030050100e000001d8010308050002d40000c99185640c0b54008800c50b030705441001000c0074160308585070401201c0000d0103000101406101c0042c0e0503d0403006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 120402491 1250 120401241 120401249
    0xc0f0310060f0305121c02030406090605160315120209090709020a0c0203150c030a090c03020d030206040b1f030b070c1403090103150506040509070c06020a170f040507050405130c 79
    0x74188030b80e0441c00e0642c40c00380840a02240c041e8204288015101d00b1442680c82c0d0948100260343c0e81d50710b15002e07000c0d02404a00514450400701409035090a0081c15084903156560400000f800c1e170414810701080c510912803201d01d25080000075080c20601503070f1280c107071000c50b03004075590135458040b81e01500744100080c02c00c41c1c0b0301086280038004940a100494220592130a00750141941444041d0001603050303a45c8080100700108401000015038000340034501c40051410040d40b0f40c1001c0303804640303071189031000032041041f002155028206094500110038150faa54800303042c0080c180e0424490302d404000c2c0050030347c00c01020035041a802860310783d100701001400744c4248540054010200000a10144c1c031400266012924121200021030b11071050a0341c14008202e00505180e0000414500040d040605c1084801000400034403e949201c00d01040860a4030000e241750003503401040076191542046400151442102e10414259554280e0b142d03010b40c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 120403741 1250 120402491 120402509
    0xc0f03050a03090b0a1d0d0516030b0c0712180b130602100204050d0210140f073305061309030206091603030f08100b0a0c02120106080c0f031006 64
    0x70003904140d4000c0b5904000c084442056003400c0303510300f003c1c0c44110743c1c403003244041d0589010b0000547e640380711060016040415a042070700342c49040c00c04204203000a0300c0308c0e1001400300c2c5600319031034101c0d140280c001d00c82d10900084021300329a0003a46104818903412601c10125000046600401044114440900c8418a080806420641c80589940285105000c20812500c54000600317016a046800d07685041c0007070f00568a18000c3d440060185201103414035082490000814410307000b100840c0002e0000d41c100078042d00002140c152120241501c4126103025400a6400c00001404000000140c0b10070108440300001c041d0011791107082400b14140080c480d4568141c2d00b0390303080581d00d0070b40e100640089442071942d42085851000207141c2810300e007000c40685003060405d130351a034101c2d10007446408034039030a0340704400c4440602080203051180b030088540b828040c0010390b500208000c4290a0a42d9040c0c05000d29514108100301c5441a4405001290 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 120404991 1250 120403741 120403753
    0xe04050c04020d0e01201608120c071109070e0907140f070311070b070311210403030e0d0b0601030b0d140a0309060203031512030d05070801050f030c090f040c0f0305 73
    0x52044c9003540c20000d0300c1140c003c0c40c880400c3c460b07107900c0115800d6510130114072068030001d140c0300d020340c0314100d881203948402c1818400b00c3c1100c00010420540500341400d502444d480070810b400341c043e550761001c9160001c000c0c40604110001c0c0340c2c814a50b0911a081402924284145034400c1f1503543c08910006880b0003095040042c6030b402c101442c0007046e10300d00300880800c1c14451840c0141c06e000e110740d01007143c14010040030502c1e024007034241c28070a480b1000100141c010740000c40205070700b03105000d543d0809500d1244543c2c1c00003619400c503182d83d801900182415840c403030300a060f8032041d50109059054047c1070010041c0102010000707810000c0800c0002e41010045400420502c00500e504003460080c6940850303000300015543d41400c0d00d07510440c40d007031031030301d0078282046882c6400c001414102e507000c0e645805200d8441d420940ca90b10045003a80c0d200d12200301140007a072440400740d901521644c46074091688407080782180444543c0300b00c41c0b540c081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 120406241 1250 120404991 120405011
    0x100302151e0c0f03120402010e030f1504060c03020315010503090a140a0501050705130918061401050102070f0608010308070807020a0b0c0d05040806070804052109030106060c0c0e04050c04020d 85
    0x400022040403c40000340d4140311058009240c1c5080280000e4100100d10358101c9035a64280f04245c1070344052000c071003501d000c608aa007640b800403581500c2452610b51b034040f01e1402402101d00c5032941c00d401c0c000505400006544980025140b03407003500c243d6081800154204012484461245001b02001803031890711900b540c0d0001c084104102c018031042d14800040030003074040d180850307000325186485049074036490003600d10140a8605013002904800860055a07050782c0081e400c1c1ca01194665100543c1c00740c05114540009600100400124400401400e5000c0c45010760303e250481c2a00020044500c640020704440f01c0007482c0300c070404d010070050501624a00b855414985000c41450704c442d4002d10140a11035290b00080c01c100061280350b100c40c50141c62010902c2c44407080941f00d8000c050418000d42c41c0000106840b4040e00b01f1750411680100b0010401e0305081c0182113400010b4021a41c0c1d202c0c00d002c85445990b9400600900306810760005001201 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 120407491 1250 120406241 120406243
    0x60c110a05010218151207032c0111090307140d0503041502010f0504020f06090102010f0c031401050a0b0415091d040605060d0302070605180907080105090c03100302151e0c 76
    0x7004a11520903503030f80e404514140707901d400f80c0e05915050a0002141c0e610203c066018101c084001079009c4940d8a04c00b86914802c007800d601b01031000020000000c03030110a000301d12450b4220f6038560f0003007200b080340c0c030400303010804101030281c0a4030459006a60711851134002e500600b840d003503400030a00c4042c1e82440760008846080505006604294021442850302280c0c01409800001045001d0b0b9000750024040b5078800c2c44100032094003200004c000700341124080c4414504030000007200d1401c0c1b41da84d8191956a40320900c1d141c40c1100850003800c00843c2c860921204120001d8080146420b0703400440034a03221369220326007458800304541e00100740310f2145114665440120f0340c0004c106042c1c40c071500f40280c2e111404184007005c03c81312500750b503002407510b0821076541e81c402c5d8424101c8800340c441020544a00781102400e0004858040e12a0310b0a141000985860502c05034004180d00d8043d00d001e550700340301117034501c0d070301400c03180c0c450005014062440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 120408741 1250 120407491 120407527
    0x10303030219020307020105180d0c030503090310020310050904030903060912140a0801090f020c011802090f011a160510090c05060c1b04110406170708010503030304060c110a050102 80
    0x102da8400342d464107209030f00190040c020040000d0700c03c07040c080314601c1c948070070008640780d0307070008503c0300855039a140c0380b0b969074480e0040d240a40100c9900c5403504619000381da00030f100d1813246002a6003800148450901c00400550800c820300c10000b002c52420700c180b880060040000134071044038000c025040d600340c0081c42d20844810402c0440385580240c8440c1506d00c2c0300c2c008071f0038850114583c4e01a000b1000b82c019103520300300c0c03600c0040141d030001001a610940d620b0038943e40302044100d07840c0091141d1240d1070090809251846013810003041d103a000340001c0e0482c0301c01c907280e162500e4002c40814101d03907980ca030b400301480810380948e80100710455400d8a04052000781c03d0b00c407041d800002e00548040e20b481140c50780c81f500a0a40315900080380b58907583c1c1c3d00002456075100c2462586020803010128030194810102c00c2d050b030f04040c006500c1d6844070354628000b000d600e1a100208171032451001000c9400b40400e0003041c0c00342002503244d40040c202c0890f805 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 120409991 1250 120408741 120408787
    0x14030406020c0a0b0a030f061d060315090303070302090105120702060f09010e1902030307060c08010f0f0e060108070215161101050708071d09010603021c050c0d0c170103030302 78
    0x45041c0d00400c09901060100c030a500c45a190102d1007c0003000000c0c050000e40c0c01c80100c146203031951100800310090302c04e1060800700d041701c0c090304250802c0204e44806883c4034200e90010000500560300a40040449540625041d89070030745800c1107a01607001940c054005030484c9040c010045803007405a41c220702210000c1100c1c558080c00c00d5914001c004100c2404280e0390010b005558050041c0c1c0c0c21146c01503014046e2190090004045540900601d000074021507070103c0c400c0040d810703400580c1c03021000700c01245c03a52001500e041d2001007040c421441030702090011000303603030b25035409a10f000f111140304116185004e0086214002e18401981c034000c10024081e600c1015141c0012a508206055001101201e0440ea0780701c10404d4104095170000903007154568000c05911144418841b0f004d4075040d080c2d015a2000c0d87c6080040c40b003804403005402e1103510041c00c1007060308004140041c1da40026a00d0002684143d000c250b01240d4610590104c0c1455404a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 120411241 1250 120409991 120409999
    0x909060b0102011e0e030415050c0f0109080306090c0d0e0c0102010c1b0308090f070f090b01020609070e060a03020901180b030d02070b1321120c030e0d0203010914030406020c 77
    0x20701402510f218200302c0ca00500b030456114010645910301c18001c03140038003207081082262300808c40010b071441e0f004e91681c00d1a44625a06000100018807500c461103912801603072458440208204a0ba500944140c0c8115010062860000d0135481454100307041c4102520680340c51030006400c55080e44500024802224035004482c2e81000007085082c1c1d050404070525101c02c07148901c2c18040d0150403016124086010a070703884100c40c808111151242c041c0b0071a000003004a07241e4070143c94201e61580244800e110300111824040c2d8403400c06031405281c5542c3c1d0700051840c60302a40800c4201d180c1144000c04c00505004824076054160010300407003040100c001d641700418401e40303815140100b07100880012030000000144409000150120440c00c808245c0f65504603045030003110001001ca081c9005240c1c4100e45a0141c803002d01d1031a680d424084004500030040382c0c155a40d03105000007030702a03100c6000a4009100443d266401c242d0003a04e80b01408099500c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 120412491 1250 120411241 120411251
    0x3050123060f07050102070b04050120040b18130c0314150105030f04030909050c0a020f010e07210203010203240102120a0309110916030609020a020d05130f0909060b010201 76
    0xe80d19464119400070390754041c1240d4030880e900b003103030090080500007810703030207480d092000b400015001844031014100762091f81484810800c1b603140308900c0381d05d40c03083c414840007000c00308140d41c0403598080941041d014865114005088500700c121460120b0740c0e4044102c0788a000c4a1041d501c4030102041c000f1020850002a101e4040146200040b42c1200005001c051040a043c0010404000b0512860500c92041c2501c1d800400000c401880340c44036401c04a181400380c0c24820407c00b000e81150341c1441c60000d003882c450b040c0303600309001000c1040700589007440114071849842c10440c403404c040c038410350b440c0447d50145604550064501800c0d8214810880e84025220305000850200c0c40c581804240700880307000b07910441480800000083c101c2d101c0c0c102c81e6040d07404002858889160300c2c200c1c00346d1100c450059108881c80200b42d030041c070061582d1202040880300441c3e50304d08400f00f60303d40b0303000540c2d041c0c0c640c441c1204001c8a8050000001024002405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 120413741 1250 120412491 120412559
    0x607030207030f0f0f0b010302090907030b191b030e070803040f051c0506040818010305040f1403040e09010c0806040209151b0319020f0f07030b0a060510030501 71
    0x541c0301c1440c080038014401e0b01540074208200710041d0092560711100d4008804014104218550b10900c800d900600d0000700080214601040c072105481d07001000d450b1507107410a001424403c00035564107500d076150b50b44001040d03081c040c46034800352664041402610a20040d0905607580c0c002840d6901c10300c0140400c1001003c606d09a400c10f6600400c41003021060069181030a100503003d405500103020030700030600c0041c0309034035881102c05a8032131703044011800c58004640c06402c421004103090001580c0c0307012a00d1042504003102d04140c0c0396000d01c0c05582041c3c88201c1640c1d565003c0c92070817900000150340c029001c5a00318102503028000c50300f02c200101c0c0c00182ca060001c0c00104e060800c28071024000340fa10704598448141c3d00100c800161035500141c0940703d1090399404800000488002c0c081d60300010701003803441c5544000d040800600051407580e11a440464503841c0c008032020030030702c9550041090351401d045180e585449801d036100301501c1d201455 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 120414991 1250 120413741 120413743
    0x52d03222301030f0b0603090703030e0a030804030b060a05090903030105090106081311041e0902120309180a0605060304031e1803080904020904020f0711030102090f01030b0a05030102030a1a06070302 88
    0x1c03001c44420300300407501800c024000d00080c00304004031079102c40007109001007600001041000d0f00e204c1c0c0c48452514404c101002400002403000820902c4100414400240b001c04002e402903000b0b00f00b400265140d500051000c003040721030840355070010004121a142c41c112030f0b030052141741440c00300360030920b091043c800c81000c806041784d06c160000c582d1a40b5941e01402960320402d2200c6620030420142c14042c14070307654107a1040c0300d0800240c0040501004507014010001c205121054031800c3d02d40b03400000820b80e070240b030b694150003d1140c8810005500c241e1190340c50381c0500300c490301012144a40c4280246c2000100544200e0000b0070421141c25650044d5003992942c205800040203031140503860764025001140c58200c03460078001600b405031184104120320303180401858202e001e0b501c1c40c50351041e03080c0c0304040f895000e0781c01010f0225018004010040d161000311382660301c1603d200a0456450303011940e00c1144001424000400b00d562a2408200b41c40017 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 120416241 1250 120414991 120415049
    0x406030201081f090509030c010609060b120907030c091b0c02060f0705100c03020a020609010b180c0c01111806030405060a151d0a06090504052d0322 66
    0x20880f8040401040405640780c859284018543e090003030040d440c10400454a0350002100d010a540c2002070102e291951400b4080030b42300014105400c2c440515010b0358004005001c0d141c2e280200100800810710b0291110082c00340c2010120740700c1140d1552a54824602000000300203041c0c9014005940e000229010b0040f4864903c1d11031040b8100380d07080840318072500c40914074014010380c0240c2c0640107040703508071a03003e5034540c0e03607581c002e2800d03101103848042d80b00103002104c3d88031141400c0c065400c904c0c0a100c8906040710303611000d08442e42d21a00d07115200b000b2608503442c0c000c0c60039080f5420401d907201c80c20341c10113540b60755031054040c10048401c1e03110503000402001d0711408900910341001c44010489180440302c150703e0040c0e8041d51110304005c8041440d104500905d40500c0e1b008006082c0d005528401504807054058903441e0560783c40800f2003080000c0018000b0008483c2c081624009080e0b50400c1000c00380d408000100304a162003d00c540c01d40c01c503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 120417491 1250 120416241 120416251
    0xc02070e070302090a0f05010f0f0804060c120f0f0509070b0711120a0c0f0906060c020d020a050a0905090c100210091104020703050c06180c04021332040603020108 72
    0x500010752650201500a8000e00e0500c54104034158800285018000300010072101c082c1c0742d556810200c00f808855900b100784080c0e0202c1e02c10400f050016559500081d100c58291030300211308074451200c407080c0c5011461803000c140d26018114131a65492055981001c440802044e0b51403400ca1040c000c2c2c018424041d12840b0036045903030054070340b103107080c06005007002601c8480116142080004005005560b0443c00305840801d14200c40c0c4105410343e40c0359181e50288401c550300b08054420914002c98101c102441c3c0001c00d03445101c4000090b0421280210301c5240541c0070a1501002c00086072041d4000d0000d45c8a440d00441c0c3d40d09201502c040200c0d61b1f9215050900302c1c0c40b0444202c0c3d410920000d084014194441c1c00750000c2d500140603912036483c0c01400c1115032604d01c86842e1030f504282ca0081c1c441c5401d90007032940c1c440100d00d2400b0150340e2003c980050305100d20303402100010740288110f180c49400c0c9a0740c0e070344088a0030442e00f410368000800244000301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 120418741 1250 120417491 120417509
    0x6011d0603030408150f0702070303050d0f0b10120b03071d070915080403030c080f180c0402040b1e0f040312110f0c010e090c0904090f080307170a0c0207 68
    0x800e0440d00c0c240115409000c082003110400c00380301c801c15100990031100c1150018265000c601541c1c0301003600001c41b501981c6250500c02c001c84110000c0106800079000b265440d01c00344000d8440c5060740c524010281c07625800748040c81007241c04e40718141c2805100750084e250500200c0049034049000030380c40b114081d01d5544445050740c2c40c04407034100c42400500c40c05800c0d160380d800300c00ca0b84100c2c441c0e80d041c0141070000605883d0b0070f0727059503400c004140c4007001602190828100be00d00400c45000c503490300000c6804038040b41c2c8241c00c00c43c0c403080c00064501607202c031009080c2d83c1400d0b50782ca280c5480e00c50b285850242c055400000c1c0150081c6103440c0c0680d00c82c51540c050101c16105490b0a1a420603000d0fa6884000c009240031078040030501302750346051001148101420075800340307855104e808020090548020803200005270140d64404101c946002c0c521031006512410303e4900340612a001c40800184450b0030907081040b40002558046041400c60304100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 120419991 1250 120418741 120418799
    0x311030114030f07320f010302030a090f0c090b0a0602030406120b120715031512050a0f080c0c0d02030a06111903271703040303060314031b0601 64
    0x1000003030030024005240c0202d4852070101280c5d036804004044009803180f5001d0503d50581107411a911070303e40c1c21650f004505142c5002e095010703030000d40d4481840c140020340d154030740c0d8682c0d0300988907a0040c2c81d5450380c2407051104407450304c105551403500304c0e00301c81c0540c0382210003544d17031080340180010014a0300c2c020b00d610886810028601d14000c204500381d65510784070b05e6940c41107200e9159000c2c01c600102e08890f009104101143d0726080c4807102e41e5040000c60a4050701540080300e0a104a0703400c04007143c2054a1140d030b840c8030b020220703954040c98610b9840c241503000c002e40b050f516107104400580e40003610746c0c1c01960141c0c000c01c0c200c3d29418108124000e2016111714628100107a00c5010380c507a1011480c8150a01d66840f0700d10401070300c1280c1060140e00070924000e00300c80740d01e030644802c06164064803070f2070080350443c0c484d510301450f6020640003201300ea00c0850460700c0356049542c0e143d203001d0b08000620301503241c51085c2c030301c2207080d0540740c154175111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 120421241 1250 120419991 120420029
    0x6220b04081e2d010f0f0b0301150521100504050303040b06030309010c03120f0c02010605010212130b030411060d0605100305090d261003290a020306192403110301 72
    0x2900f00d0318580e40141002c00c006e2804d201c43c000540300d030a85451003540307051200d45021803008036600941e50050a810200c0990b4224801d02080078901d2262510136203c1000359032142d805041e204e50301c04d4014640700c1c102480c020314041c01c040d090a2013a0401c1c03001c01002d99212403041038954251402d83c1c0d0301d1341e0810140d0000c048160100c4402e500304000e405a00d90150400307030481e202a82140e2050384404880710f60707070040844009281c900300030200118442440610b40040c011690100440400000541c00e81d02040010701190303110b542c100f0640c903003070042000c2903416080c18000c40c40c007040c2031902e41450b007032441e00f8025900d541c50055030410307001141e900d00b07001c2100701c02c1c18000c81c01c81d0b004580d44030488148056030200101070f401010752009442c139841c060181e0780c4541820030042d401c01060395800c60920b0031140c03048038800c00307614010560301039000c07041c200f02658110040882c1c1c040c40f00f0b1500742908404a01409401c503030445106022b442c0d210381d0a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 120422491 1250 120421241 120421243
    0x3020309011209050d08150a080d080c0f070f0c150905040e0717030c070510080103061e0f09021009120b0405070b03070504090b01080606220b04081e2d 67
    0x40128013601c140304104005450f903400c290b401d0302518207641c03171444080b02d1008011903c10f860050008a0304682c042c011214001c400480d00014031a051604010074030100c10401e4200f0001602c14946c809020001d020996410700c02818000c40403110f00c0c50700b40300180c0104400d10445010740c0d030780c13540b14070381d501d090010302c1c0035002000c58038145803101c0c42c0345076032900880724110b824051032800182e01d1400000044d401c15454031a80300d2030f8070750b4036a1402400702040582c0c644080c0140070504171101e00c03a1000d00348a001c80029017030b419006105811103501d00100601241300010b0080c0d14030100140000d0b5030207070103941c0c980d543c1d1a042d030422010354030010141c94040305114482d600907002d4010317200440010031692261030011144101c003a00c2d010f4100904000c2800060160300602e910501c3c0c0da000741c50000d0f6100e040c010180c2c42984509280e80000003d0404c40d51000c42d4003d00c5908031000742140941648049441c1c2044003100241049945980c030034000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 120423741 1250 120422491 120422501
    0x40305090f03030d0e03090307050307060903060f021c0507120b030a0204180b01061106130b0604020702030a1202100509070501140a030603060c2d05090609040e0601030f02180103030203090112 85
    0x203c0918180901c5c003810f044156243c20890300d1502c02e0051501c00308090078000b80d1003007200c0c0184e850000d0f80e86581c0391a402400d50024440c17107940c00b00040c10481480c81203003543c490024100040b54602604001c0100c0c0801d03a00059590500c941e20078135550014007001e00b20f070100c500180001c40b040ca0008241400c16004000003c29000083d490360001c8c0301600d601d2104080d2801a91002c0b24102040c21540e8020f01c02d484e01c1c40480e401b800d055020b01160b6102504507802082552a0a80c2d109264084d14005910009d0034600740e401d80d00805400c000341c2e0006003c0c0340c0c10030b800038149400d4071007400243d40780801c20030007551094001c20011034020f0420012000a02c0740180242c00e03028034201c0c40750014000e1885000c000c0c045030000850381c5c1d2880d040c004464200b006940c481810f040d4403a0301c403040145504001d201c20b9008620900a031144c240c4a4810310040310480e0380c1c140d012618403401000440e4000c021a5001c00c82440c140c11403002503c8900001c00f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 120424991 1250 120423741 120423757
    0x101d0a030b090d021902010f0f180b090109050303070804031b090c02030318030c1c0c0803010f17030a09060507022205060109080115030807050c1224040305090f0303 73
    0x30030801c080c810224808038059035110410b070700707540100c0008418a03c0c4030b803018500900140104458440c81449001502104403079484c104485041394003810312008015004000354800010700c0c01d0312580c001c0740c90700052505401540c140a559168402d560169110181c050030a00d0500d0600c05020041c80c030103005440410840445402c0b0020340d2038204590f41058941d003880c03070740c101c0c801c0001903c01c541d00710001001d89a006890754210300d0f4120049105015180c41c840300003c030781e5406980a05211036410103401e28100d1002899540c6a1280409400400407518040d41c40940c40007a200e150501c19910749143c4003240c02003d4282c0f811280750000400c500041e055604140d028000c26610509069203400d80c1c54200c0d860030601c58034014481000b0000942020080c04000d8090070582d5100100000070400300f40740042c4500c2c4642026904071090b14071000c81d00000907035640e020304035217081c0e503024005204519000b0b00c03c80c00d00c943c58015540420440b0300c1c80b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 120426241 1250 120424991 120425003
    0x90a0c030b0d0605071808031c0b0319231203042315010504020a0c0609151103010303180b27040c050c07090b1008040c03120f0806101d0a03 62
    0xb48500d040c244000c0c8001c2c2c400f44001001840d9103910603000007002d60907a07010b1000385240c00517240300c5450000220125284050712200e59091599092244020740c0c8040250011540800c0c5403003d403a05507424100c141c501c926540705186500080d4540a08245184295503922541030001c44007650541c500800d500300c117020000c2c0c110100701c102e980d84480300407014503620342040005900079428444000380034040010080703600c540150710b03014000e00601c201800c44400c0710003a035001d42080c8603103480c008010402c042d4070150017000083d0a2110f0088241003a080500a1046184041000342d84500e00c0b01010395200614204901c0140100300c00364040d480a017460304940601c0303240d0b020b2003500040e048107900503c000c041008100c814090820031040c0d4562070040e105542c0c41031880030100c00101c401c0e414400134206170b1150034420b07020100007001c84100070a614007581100d0205582c0a8201912100c06050800050300026000003c100d440045174406840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 120427491 1250 120426241 120426259
    0x30e030a0c060e01020106060503070327030305040b07030b210f011401061205040809010c08040b04080105043f1814100804030e0f040605040e010f1a090a0c030b 71
    0x400691090302021038201d03032a600418240700006901f294190b208002c00b10340d040002801c218400d03841850100f0f41c10789104200c1c05400c4144490001054085002c240d580e81030105106034070040e1a84503509150502c60060079000ac61003583c0c1d040c4105840290a041301003410105108641406c40e01c08000c0140c4080144240c11585086c0f0070303134010482411321040d41440c84c0c0602403003550002421450074608000440700c1d43d0550741e042c2e44c4c641044c00003003885441a4000e1005080d0040042001d05050038407401200800b0442408001c03061984d010300c20780c081c0102c2d0740030b0702d490f01004160141c190650725400d640c40812142540c2600c041190a45103603072990100c0142c5021350f0bd2903403480260b500e070f001a035020300450030000a100252900c00801c2c40300300070150000c92180c0e615000308040c2d42902c0854072542e516205071381c0c054071191245245100d041d07540d82c0c221451020101d14800c40280101c90101c0c1c44d45000020769000f90807000001c6800f910303c0790 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 120428741 1250 120427491 120427493
    0x20112090c060905010215160c020303030702070306051501020c0103151a0408010f0606050d020a1e0e0f1c1e0206070b0f06030105070e04090203070302040e030a0201050f0411010c030e030a 83
    0x60501c000c0c094140800c203090710100d07855100040d2000a0451240c030803403191a030b24580c0c0c1451284001820030060702c01c540d8001070301c0610155001c1d10040d0010f0085c0c9045242c00340036904002c040c3c50720003030582c1400c0382c9607030700140500c4000420b00f40001d0f54a20b5602d07881c000490758201d5030354210003a881903840c0d44050003c0c0200c40c4030300300030040d00c0c480700c4120b070650307515110b14000031ba400e01071072040340342ca0381c02811703011858107088408900000f100552405114810700105003036103481d244600742980340000d100001c490204034104002511904000300b0f90014250a1140c2943c2a0780001420542a00b070b40040085444200e00d00e889142107504a80c01e00d00c010304840410020305050249a0042400e500c4456403060000d003400000c0403560b205a0303152190300000809078840d8810707400038900c0c04014503a1842a842d001e82901e001500d00c900e800c2c140300802012894420704441c10314000d192400c90302c0c03824141107450f102c9400419074103014a940c164 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 120429991 1250 120428741 120428753
    0x9241e0605280f02120a080f19050a0207030f09260a0501060305030304020a09090b310c140105090916090b0a0801060305011502070306050c1606020904050c03090309060702011209 79
    0x400c0f200c2c2c0d907800c903480d00c910010207120f00d001e00f0051030041962100451382403070007001001e40c410280c0c601806a001c5005501c1300b03407a01a22645511a400500203082c180e000b80031481c950300c0c3d820100302051a05e003204054410303100c0301003900301010000c2060340301c05000a551494000002b4800242c60381030070303520f076401a1130403440b401413034100040150590003a4000e10b81c0016410b07295a6072002c0d02d0401c409102c0f58100c1602c6035010b00c6c3d140c0741e042c40261307080c1801016100d1450b4100340c0307102007201085007064180042030003d04060b56039618100d0b400b904841042e0349450403400180c1b00e1803480d4000e100b00c0f10700410f001001039400b40c491812540c03d40c1d010300a990380c074487e5a20002d0f44030741420041e00984030a101085440d001690084a0b4551080c60201e07046440841d00d03992440403921b0940000e84040c0c0c03440c1c2400340c0c1c0d4001a24102252071820000b80080e601d00c9000403203401014081200300c01d5a009000d00c448610900400303000701d460900c2c00c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 120431241 1250 120429991 120430007
    0x30905070312030506030f06060603071707020d0216050303030a09170a03020c070902041202010809071502030403050705010e0a0905090a0f06050a0f020901050a081009241e060528 79
    0x4240004c1c5080c0004149150005096050710000c0d400b80001d91200c10610415600091854092144807801030303c0c00c80703980d1201d41c1708920542c085e0007510f10200d002403c210307515807060307a9140c0c7c0c99002d200070380e0080b08580c0c2001348040300081f0011146442e0801402149822585140105045003090b81540040c0060340482003683c248507291190402240102e008519000d40c2e80340141005501410005c0d411440c418122a00300d5030710848402d8104903030808200503000401d0070410010f003040f40601800017400c20041c001070080126260407607074807079140c1c0c1c541c40380d0200354011011b100d25114260403c0901701c081d8294206080544016a501b80c54589002106000c800c07141c400d4406020b01699403e280480e805000c0700ea8002c00340c00c0c60300100c42c3c201d002407101010311800f00180c042515244000c0581c035010041360074640c1c0a568051040c84240c0201410740387c0090945299041064880d07064800012114081102540749021a03a5211000c1d40d0000c0807 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 120432491 1250 120431241 120431273
    0x30c040305010c021902090a0e030c01020901030f0c020d08040c0807170c150f090604080303040605100b1c053303010c09050a0306050702030c0703031701081b040c0309050703 77
    0x280311403000418200e948031755a00038003403100402c485040061410340e0f60341c0e402250b40480411201d055170700c5282903511290a5020b144c0d8000703a0311104c0e5800d4060000794501c000c40401c0307000b040803c007944a5000407214010004c0100015080207144000b99014260070411543ca1580728505e40e00081c88001b07040c80075200d070603803401581c50410202c0072040d000543c0305043c21104010021642c000c0b10013140d1101c01440080340e0300f60200050742c8183d000d001c002c0f42c42d003881607171541c44603c1500880f4802e04100005d412503410501164203804c01030500180a13501c0c00d00388648a9036540c2116216a401c209050052211031810784d10000c040f40200b2103000d80000940e041010342c07251710b410050442c4100085400b41c0d200d00d50100c04c60043c1d03440d01a500b0405814114241c204801040c0304808420540c04045a414094100d640c0101051444101c01c140700c1c40b011028107118907114200340d00041c0c8260482d04419501c48200d451641e100d241070200c032120456 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 120433741 1250 120432491 120432493
    0x9050f0703050c0a14210c120609040807080a03240f06031e0c050403021903031202090d0b0c040506040308041403010207020108010909060b0a08060f0f06030c190b030c040305 77
    0x40b0309a0818401104c80c22602a02ea000000143c5060b07818590030494400301e0495410090651585102c0b040d14810110b00e0132140d503502100b18034941e45400900a140108590303020040020880e0089698903904182c00c1601c502d66904214050441c030f054000c980e0400c1020170030313802d4800160405940c0b0051040424036203e44040b0101c841d0010f9584203281c0e41d840c201080304260740040392580032868685e280540b6600400c4501c0030790101654000c91508041040c19442002c0c903103a100221001c0d07282c0801d500c001240403205180251100701d52001140001c007503c1f0031070f001800003901f800c0c1c0b10b507580e04000c0c0080d00188120318042202d00d220048515040c401c80b00103a5050315403801c2e503400c081301e01005041d4040112003159035010342410340d58030038681e070005141c0040140520710701070681b030310111000341410090803420424018a0356020401c05821441550f80311180450f03468540c00da940d00b0341c04001e100c680001800f02040f080001802035030302a40c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 120434991 1250 120433741 120433751
    0xe1f080109030305091902010c0804050d050304080c030106061e021c03021b1207150204030218070e0a0311040b0112060306060e0708090316020409060608030405190e0601030b010909050f0703 84
    0x702020303032a1114882c40c0315420001105a86c01907010300e200740c1485008001441c2081d40b2040800c1743e0010001080d900c580c8003041c10060f24004010040704060b0980007413245600e801c5006c0d0010b440001c1900a4004040e4060107da108100e6076400c49144003021a00301c06c0d40c1b0014000f50300c080361f086c1c4113007800402415174540010301c00403501040980145001ea40382c0792100180c503090041e542103a02048000096511590708080040d180c06d00c0030301c0360030101000b800161810005601400b1210300030004901b103d241c41a07143c10580b030200c1d0906240c0c0c0122801d44000081c0000b4a18160002c0184106a403040e0b090b2401180d61071030603201c42400b030b94070074070456002c80298010400d18401c601c504038076078040351010b000801e0740111982c0d001e060760226000281c50ba0f1005c0b6081107070389440d45040c003c0c128040280c1d000c01c1d04060214048000c007c01041c180340d00c9140c200781d07a92045081c80000e0060301c1080009040280312000d05d0328043d604d11001034140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 120436241 1250 120434991 120435001
    0x906050c0c1b03030306040c2105070e011805040c0302040b070609020a08030f03131a0702010e010f02070506060405130816061415090405010e030409090204110909010e1f080109030305 81
    0xb00782511112001001107040d60384a03001c00003d004c0ba00e108104000b05070201303000d07202803082100f081c80c0403980c001c0703020f00d04458000c100283c0c8055241c108042405441511422526040180d071410385c4d0100e120404807009801030301c02e56028001c840c07030014403001400810343c0075184580c801c030b44a101680c0d0b03651041c2c1d0341c0c4c026803100c0d5201c448204046400090140e0000c440c01b485000e0800400c003082d2040c10710540100c80400c0503075114064650485420b100700600b00d00030300c07070441c1000c540751200d503501d990003094640180c1d600d2010400070100c18034072001d000d80c0007002e00e9503040051a8124001301c1050211402814811034920344602405064810414402041001c01c1d2000c20011070240142c4150317407556a0302200062580140000c10240011040125842d6100d2040c001210521141003140d8607050000e844603a964a141c541102c0302000c0a0506440e0305c0030703820840511001c2c007500108182c400261a80b0f040d08a020701c54080c2e101000a503840c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 120437491 1250 120436241 120436273
    0x501050105120c07020102010902130c090b040f140a080a200a030215031513060501020f03070b07050c03190f110607050904020f12012702180d05010906050c0c 70
    0x5400b8000385002c859800040002440030302a054440c0144000324111400d5000308107080c0e11450500c0350a074a90b04420543c640200320b081c02011515080c070b140c0780c6000d0300f000c100760103400b9002c0403147c000c49420300d0341d45000d50200170b40084010798207545039600d0020f000740c5040280941c0c00030850b449121520300b20314054112500a000070b040c03a69244203801243d80024130114905043d6050303114292543c070000100c404003242c00095281c2048006031810b0004402e05100c1d0340200400400212040c0807039422805604216440319100d190140c11406080580210103500d010b59940503a03011621154104041e01c4c0c0e408507150000c0c1c1143c40b42c2045a0345000315804006d0740c0d42e5420b00394000d0a200a40c09103541c18444441078050b01c1c0e501c00e0380704007205801c100181070540140000c017003502461b02000c614103141c0384070b2150f52107881c4410900c81d4035041506024800300303400000d585944140200114580401864041d41000d8003c803200d05c9241c4210300c20600e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 120438741 1250 120437491 120437497
    0x80106110703030809010f0603050120031510050c0d0906030f1a061303060f060305010b010801030c06051c0507031e02040b040306021b0d05180a030b072708100501050105 75
    0x58032802400e941c03810341e101668500e4010b4902002c543da82d244075505ca000034417070103002d588104004a0302211180c0304181d0359803285000310051130204280b00d41006048610424940255600b0311000300c0d0620035100307405000300c18201c41c01102c3c80c0c02c45c420381c401d45040030390301c854400308a10101c0c3c4850504484000b0340030204122022100c403070906d0320740d024144150300c40807180c1e030090316945c40b1001c0d102030600c450b105035160703003050040001c01e0095410f507000c203203013200c1c8562441e22812560029031040c90309100e40001c0a254801c02040c103001c0074101e0344420300c000c1c180500014014500b040300c00c1d0025640805420507070f40c107070003110222040009681c2c142400c1d40c179498000d60160114445028000c002070056800030300c8100c84410b95611481e1b1036100d114502070442101164062003503c021200307000040500c0d9456820000074600002c00e000c500440c0640000d10401c5030400b01802d200000c0d05131400130380f803025400b2414041c0311903641e8400548183c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 120439991 1250 120438741 120438767
    0x20a0807050a08190f1d1005060303030a05040f140d02060c18040e0307060504050304090e030307050a05030a09050f07231c030e061321030e010e0a05060409060303080106 75
    0x81d4006010034541a591044d010031503c40102c001283c80482c0b005200b140e10905840380f41d86005908070074030303c1c0c050104c0d14800d0000002070040345402d10000b5103a1000401182c0550b98074000b040521011004008910354070614002c0c1400000000c00d5442054240501c014814600080c0880305c3d00820364141400d03040c08000d00c4400402003001410032303c561000d0302d120601503040425102d0040d2402113006030041c50780c0b02d042441103402d44d035200c2504040e0b075004106005000e60f0040442d4907201c1d091400e41c0d203d89880140c2000307003484a601500c5c0340b0032a51001c0400b00d02041c801d00300c5146c0c01425407400b04283d442040040082007450344003228680320310f62054020b10000d0340601c00d2828082c0c0d005440000b030107682102c0104c1d055013070462400d0052098850038200512038807030108001000c640e900403d0070b84090406810440c1c5c00503032040303e82f40c8128120151000604241e121900c030030002300102070a1006070000748020000190540c0508045030702c803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 120441241 1250 120439991 120439997
    0x1020c0109050d02030a06020f0c06070905010906030b01180e010501031401030507031202070e090a021503151c0503030109050a0c0918110d0510060f14030a1518020a0807050a 77
    0x20700e00d041c0400402c9000110140c4e058001c12961500003400c030f1000b0424092500d807041c2c4c491895005c21450210018448401c0c00300406041c00541c0e0000181c4045031800d16021a500141000494004410300c003441450016a58080f036904022810346040e90001e0b40c040209042c40c69916501c03020078800a482d9822055040c4040358203006d0300c0e00001803500480703410702d82d24250441da00360106d1324001650440c220400441ca07058845003003d0312030140702c504606000140c5620203031400b2407180700e1b5030641c00074900ea000a00c0305164207500181a02d071a50780d40c0c109000074100803618800c01510300100808a05c0c02484118242d41544445007022000000f10900419000d01c212400040a00034803d00c161140513052250340e5400c0c201034114584180940f042d01c880d500c0c20140104050f1040c81c004244007620703400015003c010a4140203060701c540c0b0440c280e0004403080180041c0c0b0f4025980a8000384070000f4507944200113595409401c448a02400707040d5000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 120442491 1250 120441241 120441257
    0xb070c02030d091a1810020c0916080601260a0f020d051e190b03071205030702032a0f2407050606011d010509031203070c05070506070201090b0f0d0609051501020c01 73
    0xc0d40c1499010303504104154011a000340e041c42300005d8a10300c0403906180045d003892100400301c0d0317110110b03d4011400f0f01b001146004020b415a1104400e07104180010302080001004101c10760001111a950b074403085542e0361040c1c0d001d0b4041c0c40d04403426204070800c05000a8aa411040c02a11445181418100076207088162340090702c1e03410700c00c507414401c0781008540300ea103400400111034401c100450740d0740090300c103060505c50034660520710000001100020703030294613101c1d22040c9003203c0b0603902e0100c880000300b00ca610050440c3c441c404d0303180004a02d800200083c040c02d4000c1c01200c900d50340349401101d101c1101907030406c4100c020f00f00303000554006c40287c029110010140c2e04800d100036040d20f0160801c807aa0400170744800100c2d01400418001e21001d0803003542e00c24602003554001a1850f10700744602c08034540001540b00d0340809200554050070b014420a001c0b10360f40c2c0c04003070007802c815140584d214600c0881c0c0c1f50710f0346c00095280c40000040c4c41d6101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 120443741 1250 120442491 120442537
    0x2010e0105070f05010203010b090f030d0e010c0602070b010603060614181c020d051e010b0612180f030406110105070c0803060a0b03040b0907061b0b070c02030d091a 73
    0x1007540220208885245142034040005402070000d1400f03480c0310205075803920a01001c00481416651200d4080e42006001116069001074154900c41b02820055001748071441d1480c000e118100001e04040c42c80d000109159515810800c00c954080e5030360f00d4400c07422608280f19215241e055007140c070030640181d1450400404415072035801003801d03280894a034000c1500103041c07420403100c64209040d44000d0754042c03100c407880740010700d0080102c42410313004a2854842c58500d41c600030780450002c0c0d801c0c8480721401c2c11ba941500b06a94803a0601ca03030b0103540c0d40083c0070300b00128076051361030580030750148143d521440140da9102040d66003500e88100a0f0f00240a1030341000e0003a50109100451600550149125904002007460802400b501b07006a40d08040d04002d084846500b083d4005400404015007000000509844802c8140c030303841c0060000075054062482c8240c40a50052950000c40b01b0881e102121252480a0718180340301d2104800a045c250620100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 120444991 1250 120443741 120443747
    0x2030103060905060132010908010f09140109020a0b180a030c0e0f070e010e011112090306090f030a0e03010b09090109050106060905010918150b031006020a031b03020c06030702161202010e01 84
    0x3400681b042c142452825110780e540c42c01d48045042085c85103440d20300c031400304410700350006400c29400008000d50a050790000b18280c0d9640708050b2412808a49030301d595590b11042e451b6080d0040076088000d035070b4980f0300c1c000f0395988641030f0240100c0340011908d070b00d0040c40c507100301429503c4443c3e840c032010042d40e041c8891030946041201070361914141100800164561341082060309484001a80400d03242080c01007030300106420070707203040d8000800002503504001032402c001b81c0c880500400300740100080c1c046158004d00d4481800103854040d0710138040103002d0700c002d210f19501c0c0c40090319030300c0582c8203175070002d0707014601006428400044071084425404012441c45010004402c0c052029000040f00003800405d00004500281a000c0144070170f0014000e015001d0710040d100581c0e4800e15000115580084010184240116011600300600040d2241810b00b80256a181d580d981c00c98210b548036004504d1841c154141c003450380c0e0581d40c1c020071050000c011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 120446241 1250 120444991 120445079
    0x9010b19260706031a0303040305120c03090301110306190f0b0c010e0321160c0b13050a05070609050109180b0303040909210302070c03061e020301030609050601 71
    0x200c1940c0401c00350008101028070886000344035942e00400c44202d81600000344541d0441c5680c4698410001040000d802040c41b000d1120340040d40390b1900515000c090541c4035000110703526504e00007500c3d241d640303c034002d14003a030300a0f41c00070f00e01c086842e1860328070b2016010301d62218251040070030228400720020b1110051000004c5082e4000140007031454100c40c0210a06241c20300001d5000c0b01c010480c035034484844404955402d00b041d00140c0341c000720b85809005081e103800000e51a100114440c62020f40c0082280d845121504100342c8448840c05044001110890009443d6102c0e0b5188801d5480c0400280cbc40c98070340008060080058511450701404107200000d4680e246105200f4082e0286241d000ca1050302c821460740c20503181d03420014180305009203030115454409000599900c200001000e291031005a0030a0110704208540340340000000f004101481d00055980b034402c004031421640c0380c1d190202d07000f8081601c0050100c00314000307a6912280080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 120447491 1250 120446241 120446279
    0x60105041107170306090906161202070b13060f0e030910020f250501110a060c09051c0210050f070f11090109140603071a03100b0304030809010b19 65
    0x64924020140d0b6454043d03480c3c0e01018011440044104800390600710451b03a4807041210281c9143d03c1e0540c0c11100401c20080368004010004071844070541c110381c11110310a4012540d001c1521b404828800c031650b454800720760403810100d0907022016079000e55080010100c0c091410072000030207000f4100c0b002019041113115000031400300c03240500c4000001c4c042c3d01000000501c1101088a0344030566000904203c03842c04200e10700d40c07010982121440c5d010344045001001c8a60449a400068015903030183c00d41d04010722106650041c181d02910030788001d1070f68022150280d0303950040144c4804180d00c10413503080052540a401c0d42454814811204241c3c10900480c032088801d070440340c0300f43d541d1002511122540c0c02000d0307004004400804030b2500707140d118001c80d0703003d030042424a01c0c08000301d103514080e4080c80d0041c04200c0d01c40c54491921707007002416143e043c0c90a041c00d510307120b00350800b400d103800080c40340c0d0010110685814500545142c00b0742c40e0241e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 120448741 1250 120447491 120447521
    0x40b0102120708092107150f081b030a090c0f050f09090102040306020f030103061820010908010e0c100302090d03080a090b040b06010215010e01051c0503040f03110306040506010504 80
    0x31140c4240d0780d078603007410407881caa00c0030702a02c404513006906d0900d458201080f65886619040c050300c1e4440c2c0b00c0301c1207001c42c0c5080001925800002c0d401a02d84221510000c0d2002c42041980c1100c0d82c45aa44103002c2e2a0b030071423150303841c8202204003029000c2c04e82c01024000240400d0b08180241d00d030131014000005182c07642d240c5aa40481e04004662100c1c1100040104148019400f0310500714204000d1001e484000796a900409603201c84041c6030301c0381172142c4078507076070089108800400d5013800a2042003120240243c9808060901c54495103c41840ea100c0030720a00c00c2d03038840a0007501e1769030100e04a4405a803814001041c030038a00b034442510100040341c017074807507024600c140214880360500034006420300c034901c0e400050407405a0010084c030408000e0301d40c119542038480e11544100c039600c103840400061000b034014400028001540c007410350603581142c0c091910510882032880405848100075603000d0403030b500032001484680b03041e03400740c029040140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 120449991 1250 120448741 120448747
    0xb0a0c030207030b010e04060c03050609040b090109021302040305061f06050706022205010e0d02010c020906010e1801080606060a08150a08010906050603010b0105030f1503030717090f040b0102120708 88
    0x20742d482e40356000980106da807102e070100606c8100003080c000c41d110742481d42810300181c036201002c5821080000e1010344140d0300030002ca00c11000039441588041d80250000c00014031001e080c5000c0d6000b403000b1a403902c14000050303103031340a6407001c004014120b40c0c400321052500c2001c90342500001d5059503055420000001280043d021801005040c0d1a00d85081490140090000301844803c10b000d00f804c4000c10005030f0303014215848050b41221030407aa83c40c1c035030040b600800c0b0b00c401c154205080028000c034890051014504882c035500445450f41e0340c2e8000e00c0824040c400d02040420000310104219400201c0c5070b051000001c0e200f40c002980d240b502e2800d41d038403008107444c000d941390706100d01801e0a0054040708c1c1c80070700304640795062480d801c0d250601c00a250b035100071821a2001e01c90344c4d09000300c1d0030b0280c1002044c00d5000ca1410400c5940e0b220840c3c461044040c0e5a00c00102c0c1494000e6102da007070160080d04801c01d4210800e4055480a982201d0f2041c0c20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 120451241 1250 120449991 120449993
    0x12080f0403030e0f0105030606040e040602040933030308040311210901080117070b071106281e031515020717070e0705070302030904060602250b0a0c03020703 70
    0xa4040d10095001e40d40d400241c103a031505008000700312081041c10444c0420401c1480e88820b0304803070844d6207035840840035648600b4080000e019a4000c08012810301c1d6029420040903c850800c0802c1c6404c006a102110025190211400e210050100c0d20030341c00200800e0140c1c00c1e010078086c03084191110011514400c3c01c0e6050301c0030312180140e0012400200c95603000123400d02501c600d80d41100b46200c100b0945946045622803001c2d48100043c1d03500802c45040300b400074100018014603100c001d52080c01c200c0f2890300c4ca1442d440d206d08250403100c1c074031a0070704030b107070440b107814207034101d210210700310041c04100c1c0051030104210720700041c01880340d80000503448c080da40500320380c9007071224500420090a0100030313141e10019040c0070440c58440319603000f080070308186e0f944d004a40f9050b421030044210041e801441c040340040c0494000c103845001c1400310200c2c80000441da554440151841d01540f0f02000301032000842080c01990a80e40050080c01210840303552 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 120452491 1250 120451241 120451267
    0x209010e0a0306020406021203060607080c032203020f060a12110c06010320180109021b0607020a0b0c070f080c0a05061005031203090c01200a1a06010e0a1208 70
    0x9298411143d00d507002800b004002e41c107002a40e20aa0801c0616203142800b000050180c0164040079210100002c0d540700c500804000700c0e4401d09a03084101808c200e9510210100c0c0450711007640142700049011840780350082c00c0341c600c007140c3d441e43c0c02e0b40070f112140d0100420082000340710844c1c0400503070004030300400465009602c9a02260388181a90700380e51490990203204a006c2d801d5405030064000c0c07880003403810364a043c1c20051706d0f941001c3c2c80c3c4000000d88503400304a40a41014005025404141030008900a82c0c2403030b0240c440050081c101e100740311024010301a010a01800a441200140403814200007201c140c11078585a02d410034405441401c0c00044082d0300f0845c0d41401e00101c0c07488401d240e0380302e056240c40b014054440902034140c9040100740246c803003c1148030289400c1c521207481c100c42c81102d4602c0d0042c80c82c001e0360300100c19001c901c80060081d41c802d8158402440c005050401c00914121042c04040c0d000b42088400000900100701e49000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 120453741 1250 120452491 120452509
    0x30a050601091e08070e0603070e130c1203020105010509060a030222061d07180b0309070b0a05091809120c030903150414010b0f010e040219050403120c030806040209010e 75
    0xb030103d0750311010b289443e450604e0285540e201d40c0304048000104400d44d94042090401c441d1b009610400c103560b82c4010038442000e044c002020201070400100d14048a61524244148290000c020590701c41e0208a03011904072901548803000c4081840142070105a0303031260952802055216200d00c45182c0948030365420403a080090b004813141d8429207189813a4200702c5c0c0d1b0810781d21540b0445205191040c0d00e0184003802d010001c00f01d10020030400c00c200050900801c070700d40303c100c0d4680080156000307080880c4149040701c04003132510250005d46020310514002482c039411251444040c2c1c0c0c110b910010050b0000340700200c0ca40e02c0501240c40780d0300440402481d07178030380752400241845242070301c20030301e0303250103103038001c0707860b0b412080b0389440003400c01c1c6a19542c0100050302074410b51000c1040810441c403815441600400500250781c07180909440b105d03c0c4501c1111140030001c00500060340c4000460f4440c1001c2c0d0060060300410700d0420041c0780700d42d000c545144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 120454991 1250 120453741 120453779
    0x5040f020304021e03031204030e0a030303050108010c110606010c08040e01030c1a090d0803090f070f061407080d0b04020f0a020f0610080304030605100503060705090103061a030a05060109 83
    0x19400004220840c84d1111945040b420680c1501d45200c1102d0f011076924010349440d0003400c1905000329041c1400703400b06082c1d0f001c0c000c003103806103a02c80c034008014050030720511409600709450520309138010340200f400e010710800207004603a14100111072241080e00305039280c030420000802c001040650081c041c5005820780340015240a00400010060000b04540800d05101d01e030034a6468458003904076400026036503d0351103505a0b50304204919141d610a88106840002c2c544030401c0000220b80d225143c90810030079107489030100c1d20544c0002002c1ca20200525001c21000340e0242891150103000181400f600c07000084c807590000ea0080003580c0007010442c034800003004042d42c420b082120002180e490801e4060b0b80b40a54000200400d0300d840c002060b03007240c4501c24008000003030449840e401d01c03110150581d40144841400242061400304080300c080141c640500300d5040300619507a036100201000f02030150a2504100c0302d15000260054603120f514001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 120456241 1250 120454991 120455021
    0x30f0b0c2a0c0103061401110319080402090901060303050a0503130b0103110a080706090603020319111c0501140d03030e03030a0f060909050604080d1e0c020d03051006050d060504 79
    0x21000d2140700d40ca01070704030a90b81d041509184051044c0d010354808050001c0007030a100d00388a01000d20282140581660703401066a5094038075096903002d48150b014a0080d039100e520b68448075401750990f8010301010303011404c00c020700600144100700540d400401010540707900780c0359555005650301c0c2230340261041c4040d0880ca901d9441c01d003440c01c0c024011080241440f901e4850045c05841e0b1501c100028194040001996900c45140021200c045103030104400c10310001400385a07040b101d031000c404850034046001c0014240f0405040e00d001400580758616032000b0802c220051410440401da290028035180400030009180190240c08002c20405c0071500800c0895000d43d1101010031704001480300413441c041207442c4c015410030041d90341c1c0e682005508029011580860754640d484a00c4003802c1c40c507079407121016064a600340ca9a40c01130715000c03015140182c0e0300c9c503018404803000300103650141004184005d0342001c080346607942c450015049810245a038641 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 120457491 1250 120456241 120456307
    0x705030708070306050f041a0301020d0c0f02070608010b16150e0d0302070803131403030106080f06030c0a230a0b090f0108070912060905060405070915030f0b0c 71
    0x2590820302403039002d22940781c20410a860300000452064401d440c0c0c50003569540b400c1496000d5020f00002d1100f009802903544a1400300380400801075842e1000008a901701654900c0d0302c0402c51404655070f07030f40e61901c180d082440d0000d03182d100074000d11582d00c090244038001100b280c483c1403119298180020130011208820b418141c40e04070f8071040510400c0b00034005584601940c0e00102e2075400301c0e001400c18500800b079000b04a00f0140740b880040000140c0710b902910081c40307465009001022038440206040c3c0da414038481c101e600c40c024000522108440800c0c0f001840910704060078542408400f2440b418115005050306d00000243d0129905102811a02e04072080c40c0202c0c241c644074100500c1044180140014800da13841c4031001c0c480c090304690146600241aa8468105840e00d01c0d0b981c4028860780e100c1c181404500c5800780701d24000c1d842240e81000c400b00604d00c442d03894007040034004190b07041d960010721841c6101c45002407a20121140b20300c0900c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 120458741 1250 120457491 120457501
    0x50705010210090503041203020c030a08031b0a0e0f040b041406030d022d010906021c0b060309030d0203090109050a0c030309050924010918090c0b07030503040b040804030506070503 80
    0xc00c110b03019900c5240c19003070201c034a0004500000711421100c3d80380d9095030340440c900c4c0072030412920580f00e55240c410381c1480b2050040034401035005285580032440c000c9201c2c0b045c42030038011022048041103010102d0a820b003410070f2030440d250b1000b00001411240b035000541203d42d01005410722000ca0001c01c00c4c05d080c100041c03840401280001c0c00703445041c0443c01000380c801240480d0010311581d0081a0440075000414143d030301c0b81040d5110344031441c0c218854840807000004940c00d1100342000c03810010102c03030043d00140c003d503140c103081110040c081d51016051018a42d030301d10402c0040380341071207101e0300584245101d24005241d810000c0c4540220341200c0e1044a21806200d0240968001042c2c00310030248c3d0b1500c0b6464203401a9131400c1a43d00c403841d010541843e0807111451070340700661080c0b04440c44c03501d03541c840a213041d89015a820050202c0c02c1007000c60007180b144d01c24079a215215040c100d01c0c0644035075509042850548410700490001310602c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 120459991 1250 120458741 120458743
    0x2131e1b0210020301030b1f0308161209062a0f030302090907030501050109090509010b090108010605040e01061202041116080909070e090a0e0106051801051809060f220507050102 79
    0x11001d51001030040d400d55045072520151034802510450000030700d0304c0d00d48032044c4014400802181c022012b10789440782250740c03d00400181c001290907a6034941c020107400d010f6103498007079401503925035000f0107044624480502c2c24003111541e64444081010018a00c294800c504d02e201c0c0d5000740e140c0c46260700b44080e0480c05007449042c1400c14005120a90b40454000d08545d1071510101e29510381c082c1660041014444440c2c0117400782c8004a10200d054101c1001c0321401d990410135502c404402c282200d42602410904001d80072103e4050b00d815008110f03080c107003080c1c80b0b2a150503051030b8a0941c80c4403100701d59201005c03078010b81a2410340740007907000c03400f4142260901400c5001521070b0600074190084c0c2da564000342842c8620950265020b0000503000100104410b0b441e60070b89542445144c1c46800c07142c82002d041040e8110360f901401500340142078948035001094840180281400c014001d421246190b10700110011000b0b94005d41c043c11138641000002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 120461241 1250 120459991 120460003
    0xf040b120f0405060402010e010908190309060e130209030313030f020312160f03091805011403011518020904060b07020108070206100512070e010b03070906090302131e1b02 76
    0x5900141e03030360701000003050001c551158000e6092074141d64414402d40140c80c51110340c3c1001505115400d10b407119a1030365030105840314040d4540704440d03507481008030707460103c414500741c100184c2d00403546580030b00d80281010360001420b480c200300b0541a40d00c0100400e07441a18201d401400728401c1d41001d200c410114003080e01200d2400d110401400d102c0401040001c0c209070306440c0d10001d0500c40d03040034001e48448a0b0710340c403100b4121448005402c0a02801000054010b03465429240501c91448120100720104644610300007501002e441c0415082941d25000c2100706503a50302c0e031040344090550782c11120707181c96482c00018124440140341c1070a41d4450000d0000020300051414201c0310200c07144040c6015902c001070600600d5404640c010510b40c1c00418421700280c0034511840e41340c0e0340c140ca4035030340300b208032504003440c400a508401050302d400c03054103061300000084010442c410084503014a0440100c81c5451189240c40c0e060b4030303031818216414404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 120462491 1250 120461241 120461251
    0x705030103110616030e04061823070206010303050304050c040c03020c0d08240f10020703030f080105010503010b18030a03020c0307090608030d0209181005011e0207140301020f040b12 81
    0x20504100d01c4500c001399840e48681c02600b031103130440880c40c142e80c8581122000e01136284210381d00c02458202140540040f02d000315004c3c101d030080a00d0b040d14543d04502c54121035008106030b03440c43d00e0036a11a44042c02c26541d50049207200610b94485010f4040003a006650060b0f13903030701c030742c00281c14000b0743c1000e241002800e905010348464081801600e440e0140c03a640000e08040c170003d0809060134524603041460302515000264000c1446001c0301d0182e21600e250551400341220104400d00407180030540510041c030910321580042d05d8401ea203480401c01c0c0480b244000717441c000c1a12012001680a82075200301e41c2028024640100010301d0b00380542420413500b00e40b80c1c092554400102507003c01e00114980d5000c44070585100001aa51998140301101c0c0c0301400e407600640b800704030640341541445000d20568035408000b9401303414030600748100c07481d500c0300070186154559000d2080d401c3c50034180f00140000d020180c1d40c595612405c0c4420740e155a4018a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 120463741 1250 120462491 120462499
    0x2609030a171b1605070f08010b0307061b0609021c0312020403080f0307020312010308070218041115040b0c070503100c080727080105041401050106020c220203070503010311 76
    0x240b11074140c0b104210111860034250032074503100b401001d2040a810b0102c003506600c100200090340c0388040e900300c01078620b0b4000910120140e1018182c0d0342049114280006010b19403807000b1251101007041c1132441004e000c44d81c0742c02c0d0340003c0d0501200702d09050b808110224103008054012a2175015254100429401c140c40e5850f05500f40c0138410030035003101400000200c44c03d2003401182c2030158003104a02443d40c4038203006920f504000022801240e0034a4000c004c0e40640030034910403a03102c4011044004010207002c07120700b2180f560f0308628420301002c12001702c0d0501618448251070024070741235203082c040610b44014888100595803a0400c04002d10343c0c4410b42507071240481c1841e05c103154000544602c1080c0030403915101001a500101302e104043d0400d5014601642110500d002d000c038019080307610070b00c200d50143e807001b110182e00342002402004003030225a180c0708494404100340060340d100300c9411000441c000010f0040040e06440700f244204262 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 120464991 1250 120463741 120463787
    0x9010f09080d111509030c010e030909060409170309030d140c04060f0c02031e01051f090b0f09010f03170703090603091b030b0a06050f0a062609030a 66
    0x8401d054581d0a0300d02c804041000003800d252903c5010080c02518126084400c8101d1030325101240d103a401004807642c40303509113032000d04041400002c4e03542020b0001c140d00c505469100c2040300034401103104660318030119411040d5400d41501841c0704101185c051540c6034032050180088586903503503001c503c0258001c2c0013080c1c44100541d401d540b0326040160b40960417072816140c03c180500000d6062140c507080e00324010750600685440c0304008024400b035100c10081200e040d07524030b084044128541810040e15896400c4003040c2030000e04007250020250001c1100b4040c01d8110b50b18010780083c04004100d81040e0703210307114507900182d40c2071011a1394010032581c0e040c410f000406441d90003810034005c0d0b5103240e2500c01038160791150560750702d19148040d01c00455042c0c00c41d6152510000302800c00d032403c0c5401000082852040c076040c51020354144c1050740e42403030f019401c0702807401404041c0502501940340394005640707600202c08001e10702c0d4105111070094290070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 120466241 1250 120464991 120464999
    0xc01180b06030f1902040b01090312031a091501080c0d0203010f060906050c0601030f02130207030f030b061606090807050f0714012d050d060e0604060608011a030c09060304060209010f09 82
    0x4136401d104d503903045801003070458010004940342d62460300041c000440c50f0a01026847d01984084a010000c24100ca05d80300900c0c00c020200c8800c079030801c02040004a141744a40c0320b0f4106c154441001180c00782004036406c00032040780c0098000da0f580d07000c001d02c14009607801541000c000d11403441c100d85030500242c44503440d20700620000f0107031000d40d0000030441d07903140354000044c6030519007107407108032a0900400112290380d00380082494900300c4549401c1c00d000b110b1001030665a104844105035640e50028114001d05568000050001c2800190706101701001c070048200180409410140c003119090320b0a00f603a03040c0b011a460005452040b490458058446e082110310585c03078148068400f4400d04910844e6107191034400b01305072013840d61190062806513000c01c40d0b20b0702c0b81410780c2c2100083c082e40c0341c1c2046c002c03001f802810054008541c020780f2582c01d80d08240090020494a400684040b12003d4010070b9840007564071100000060849203000707103c403850 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 120467491 1250 120466241 120466273
    0xb03060a030f061b0519020304080d050d091403031e0412030216080c0d080a0603050613050c09070503061804170f070c0b04170309060a050c01180b06030f 68
    0xe480001c1154500040a01c18007201d603000100715080f0f6120900c201082c960001c0c080d42c0b1298036100846060020a8040d031310010607181928a1744000b04492494044c050710f094000c2048107052945658100c80090480041007450508400066850307041c607007900b40c9000540880210340304000401c00020640f4120746402748032207800c005035940040f10004035441c1d444200504031a200081c2421500400203241d40c8503403542c2d43c0c4181688584c9480401e80b076032848050f00c1c0364002c13404100c1340e041445440415078812001c403040b41c1014000314505805c1250103c010030804410030805040142e15950640321400c0c0214052419554102c0c5060000da01d00c45003100110b0280300f84424402254409908130301c0d180366007603941240f03403110383c0503010359140a101420b000c0100480001955000c11004000030304215101d00212801d4000d03040b185280d40d00c5124030400c001e2180e2489018501450010030585408000e15190690740500901a540300c81810621801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 120468741 1250 120467491 120467509
    0x507091802042c0303070e0105070b040210050d24090212010e07030623030d050403050619021b100b0f060711040902030d0e030c01110a020d1412070c0b0306 69
    0xe03044600050900708080d210403c520b21080e0045007810240d001c102c1d94000001841c0708001e299210100c0c01a098011551800f4542c03000380240c080e000841c0052400d130003403072209545450b115041c03811603c4598251028082129502c540301c1860500729000482c514000d00035200341549008650320802ca40320405105411030901041d001c100720303038400e4000d10300410f044100722150030343e41488544000e000750401403081c45030020048000c6c3c024030540e4201c0c0d81103000361071190380e041c00d0000303070b00202c0000c0785800340c1c200721648440c0c43c1d0050700240381802c1c100a02c070700e2420002e1041160302c614003940c442d04000c0c80e0130f0b074a076440c081220040d40d8041500c1c5078003000040401d015050883d0020740c14041d510714500510760050b50240c00d104204c0031211201310860040d60382403005160481580c00c49802c0c4005410000e0030342811900c0b031561503194040c0e80d0b0b10642050741040044641403c001050b20034001011101030242990303290380d61541c104840010507180b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 120469991 1250 120468741 120468743
    0x10c0c0201050a08090712030e03070603050c0d0e0a06180506010f0b090111010603060501080d1701030206030f0910230a05060913080903030706093c050c060f0705070918 75
    0x100d00c44c40051085803042c0314040083c41252110780030400e151030003818241c06e07415500e003e0b102e0000e0024406100e400741900490181c110070b403410100b002190013400e11500a644203110740c080420014015105030b8001c0754182c40307407145a10452030103504049c01a44990680340e0b805c0802d00100340079904447c0b0061003421701c03107a10600b540149001d41016440070b491140b50100015621001040000100c41d0683e01c80e0340e915400c81c190201f0020070b020180d04450140001500b025000034440d40000b8500c003150b5546030005160b17425251101030340803080e1202c1110000000e220704500e500400c1c04031040c0038504d4000301150072003100818001c01a4619002075091000410403610072201c09801d03280d548071641488805000300402c100c8225061480840034580c021440340440d031800d00045450f40b1000314000800200b810055070180a4144c44161640c0c9440c010204101902e0b9580e031942249d05000d4144100785d80014070990510780383c01c0414031044650a07183d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 120471241 1250 120469991 120469997
    0x5150306060d0f320f0706081503010606050c010b01020703050607050a050712050304020a050603040c17010f14090609072d23040b0a03110607060209100c05010c0c0201050a 76
    0x1c4012400d145154240d0f0728009401d4103100610112040203d01080c040b0a0580081c11900700c031000c5000d80d80d042e240c8034809250071120050116500c210400ba070840410440d01c06003d4030306002908503551a480320010070300004145101c0c0c0028024642c17a000240054071000b0b196803681a241c982c003c000d40b04124000401c1c00c01c1d18051000d503090140c02414100e1110102c3d08003074030660082c1c83c260701c10390003c44000742d0391400c1402c80784115448004210000e20302040b001098140c441041c2d82075495166810703401d00c09101d4492100440030706107409044c00c02d841070401d1005844030002e03400030b40e0b05125010a5a010760140c001055282c10411501510700b400d241c1701750071a0100b00e240f8031061001180d84034402d940c800c81203e04014280c0c9400c200210010783e444000c14402220300300006916110000d05100307800f841000d4540003000001071401c0c0c03010340189021030000807086052000c00d01c241c0c524036040d4105102c040070160006022400f50001c0c090070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 120472491 1250 120471241 120471259
    0xd05060c07031107030f020109091e0f0e0111030609090f030414010c060c05031602030a12090c09050f16020106050f040e0c0907022103070f1101090b040f02040515030606 75
    0x80501c104014250743c0514016075401c16168a86203918440300d0350f050b40082c18468000c228035a440c400e503080f1400410100384103c1d40085100d000c2d01c543c1c00c03164101641c68400800070791013070254070721406043c1c43e295568070307280d001c118070703400042c00c0201181c4c06030210414000c800800c4074241d400001c1074140c0e014440780121140324401000800030f5040c95801118160461301550248442c10b41c4042e11501a0701c04999a01810100d44000307580741d601804032112903032014a9040c0150040c21100d615180f50000380ca200350340041c1007140400401c0a403030041d104403402c03140c06e8030003030140a10f400e000039404812001c15a2140fa80d03040b0310350038403004210305221107001405c540100d02d00030f10003030b40303a8410825408903039280d140105200402d400c103c910514035900d4004280d00c2603070b002c40b00400340c3d0001ca44259602c2c41d1032004124641d0304148158410340e140800c000700d81c41070005588d40500380710101c00707038401c841101d035401140b03441c2d0004043d182060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 120473741 1250 120472491 120472493
    0x906081e07050306040219260c0d02150f040b0a0203041502120304020f031009050105100905010530160906090c080c0903190501020c1608030304080a0504091506030b0d05060c07 78
    0x41c4c00002c40e0b0101c7e00344071202061304c1c110708109024444601c01001541d003003180d10806e0041c1062b607550000e600514109440325959042c0c4041c04400c0600100903003003544500c21a070455021190000c003607840810108041c1b00603003035001c080c0207607201503c1010299240400316000241c40248a014501541d030416181000f80c1c030b06107149400244032480c05414214000c2200b681d911440c1071256101007a1aa8503000d4103040301d0340034007007000440e0005d141410060a00b0091685643d8202c080600d44404000d036442900443c8030012001d46450325000840e2441d510002c107090400345081500d641080c0a20f5000b0303090121255030b600210006810582030030f10001034181d80c800c0c01014440154040d09691003204100c0701d80c2c01c1240301e0201e0140b058407460060364000c1001400184c4403401401c0300e808e0508000d82030540300c045880c10346054603009412140c0301c580401c0384542c035000b0902c2a00701998184c00c444090b481d090b4a0f240c0c001c10b400501040024950 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 120474991 1250 120473741 120473779
    0x3070302090111030d050627041514040308060a0f2102040204050d0b1b04150e0301110c1510050a06030207080f160c081501060e0102070906081e070503060402 70
    0x281040320107405072a0f0b14060040d17000c00a040c2501c25a0240e650041036801c206010074101254507a0148841c0e965922583c80c5000150903200e9034501945661000d20340300c94449002e4001c0d4460341720b494891801209200f0500c16545c014003403010702850400111811a03408080d840001c151140e5034501400410068400c4d60f20450b0404140f0300c01d01b080c0404510206c0c0206900708801c0015094150808900c0c003503030040440ca82c070012030300d62004e802101700d10304081000e0000b042d172000050710003440350007080f130843c0c0300e4010080c0050130742c3d4005e01095128020300b14034040e484c00c00021031740300780080c0a0742d030a00d030340000c0c240288605841641e195070902e8511030b80e06c0c0301d03801145012415000b0120355095070040082201030001c07421700702040c9504000e40440c1c1c07900b402140c0ac0c20b0b03881081f41c10f60207005400702c1d08e10900e00403070b07003d0217500b001400e048003422025546070705a030190400980100720140016540460480d401c40c0e01101c3d01000040010700302c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 120476241 1250 120474991 120475007
    0x12040f050d1403130303020c030a02090105130b0406060509040b0a14041d070803071203021611040207060f02040f080a0c090e030f07060606080a0b030c130b090a0603020906060f030703020901 84
    0x205948400324054604864409065045e60700c40d40c203a483c07100d444824142c5d140700b8a00c000f580321020600610aa04060040305048002c020001c2855030490021804494040d0007481c009207000490002d541060f0103840f0800f2015510989080d03d0448000205203035100454491500d0340310344500e21898038058024101a01c081d40c00040e55000400e0762070b40101c2c1e080314694001558002414041d01c2503650310300c40d80c3d065070443c1d0a10380c0c7d01d031520440b100382940d20035402d009080100e46c070341c030809620704490f0b0307070050759142881c2d600e84040c0516400212694000000704001940c0c030f076258401c0b64105000440c4010764246080e0450040f07a2020314444408140f1105001310313900000115480c079101d11040d62904030440c4143c400d0095100d030581d105403200661801c204882c0b0f09241521000010b0321001200022401e801c16220061070607107504061056140c25802c0326003180c8100e9007107180c174490000700d4042e404000c1081040c144e02045451803a401007040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 120477491 1250 120476241 120476273
    0x30c1b11040507090305060117060f0c030a02091c060510050d2418060203010e130201051605030906040306020306031b01021b011718061522060308030403020f12040f050d 75
    0x1515421740e1242802c2c5a0f80d0071004100440380b04d2b400118440781580050b0f00e0241c10103c160510355507450890002079408400407640114281001302d50728131406882c0b0114511a000102c2d050901c442d407000400a6a00a54030078030f516006403001403101000703041c00e00000380c451290141c881d4050001010000b600426001c03000200d8000c11243c0d81c005c40c161401d4050440c9a43c9881001c0c0c091070003061002030100d501003140c034400c01c5070020102c06c810710a508603440c00c1c10900205100c1c2e0090b40c41145e04640110502100341f070700348022905006000035420700c2c8158070300000d50fa081e5a2603001c0d05540c0c046c640d140b60340d100b541450051a82060310750b650341010007210004841c1d0103083c0380395009110210700c290019100749030606500030400d001d40e07c90408185a40400d401c8900d10f01c558880740000054498000786100b0350113034020301701003406403030f80b00c0c00d014640b0181000b448080105218901d41b01c00168161207060795032100206592401110785261124 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 120478741 1250 120477491 120477493
    0xb1b030403060c050d23040305030406111c0f110702060c070504090f020315010321091a0a0807080103151d0a0b07020709021908040203120a030c1b11040507090305 72
    0xf0041031560410010f00140520060402494141e40c080a009180320035181012110000100d004030344075001450b00580210400911201d1082c2c00c160b40d54001100c1304401d02201c1f40f50419041148210418810211802d111406040c0ca003110140304152000344a00400700c0c0080c00b03501c0410015024120141c0108418502e905103070b0021801c1c40700c120b00c00d01c45c5041c1c060301130641900d0349040780c7e8043d00080809a05100740900074600030214000c0000300c202c009221100d14ac80344030b1011654060555610340ca1000502c0c0720f4000340b0141c14004604010000148004a0244048003102000809084080c0d0340094481620712921161081d00743e020305006102883c10f00a8040d038088462041e501c44903402030380161303002c1c0654850344000c800811070049022030380c0188002c0c00e54003c50411100307841103801c01c81030000042d030b070b80340003101d01c60300907003403000070302d2440c2c40e40541410070341e02d10320300044a0f4001070081d502c500105014030300502200000d194020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 120479991 1250 120478741 120478751
    0x20f091011012d0902011e030908190e03030c0709050a0207061b0207050d0201080f180f03030105010306060e030303160e0a27050f0f1003080c06090106060206010b1b03040306 77
    0x1070703c10504003000e06501c2d110048807075107194042c0d42486500d03100d56041e12014000d40d10386062000500702010380406250b00c6a40c668001050580100a641c0303104120302001304c0034103030060245510191950080e8400c1049c160f005400182000c02c84d03d010901007025582c00b4072034406401035050003000756003070400000d030450341c05814070110130155088070501ea503030b03104101c1d06283d040400381c0420300b10f40201d01e01c10038815412b6400009900002556180072007004e2604001400c007041d641c00203c014040d644e4180140402030400f8602080c0880c1082300081e10b03448003400b24107040d400610030400d518024041141c01c007000608a5611564a17260103030303144207114015120000d118082441c044062159a00030030300700c0b007901c1d0555502d052413921680041c0c2003600012120f0400400100790f11300808188111101616903401c1c1214014251601078214100395041800140100c6100500317841140d01c80c0d03240c0d036545e181d0024800d400c501c05e581024084500341 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 120481241 1250 120479991 120480011
    0x105120901060b04032004020a12111e04080c10140306150d020702090c040b0406050d0f0207060905060f0f070e040f0507030902090a0204150509010219050f010e01020f09101101 78
    0x2201c14030b404201b651255070b0411404d081004101d10403a00e07800c01080b907200003000005040d03031103c60105200e080d210f282110f0200b48244040d8400c82403100260300180900c0034480034080101c0c685419036a903203041d0360140002d071000a4000300f008183d400403000440380e9946941160366040c0b85d0400d91b5640d41c04039074946c046e5001000603802000207102251252458a007101c08456120721b1b038a01349400d0500072203803603000030301c01c00c14140c40d11642c9214842502c02401c00e2031081d00c0004c3ea9004500c0c0c090b00b0640300403c4420030010402c2040136542c0d090304d02a5102d07444d4030b028003c3c13621004c00a40182115000405110329140800940a41552180d0318280c001c6503035020650312140103009074031a501480c050984811003446d9498042c8018144a44050050380c10407001d4412100181c02203a800780c0e03041d4404c40340d00820743c0080c070510340801030200c002c4d4500b0351416030440041c0303d8030704054001c0d100001030448691190501d90103500b45000248041411 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 120482491 1250 120481241 120481253
    0x80f0a0b0d0b010f050f46030b150904031119050d08010b0a0c03030f02040308030f04140102040609030212150a0c090b0306010c030e0301021b0610080a020105120901060b0403 77
    0xd001d120f9040c070040002060038640040c0348180920001d00e0f10320100c008811000c0100e2800e50200c1d0700d018407c0146542c00c0100710100d1a2020302001c0c42c0c0d0440c5141043d015050014080810031406540e0380005601e0f00410b0315401509070511115141903c20614903243c2c5000b100c25500c040f80321603e041104c042200c80f56410182d0b0754001c83e91700e417501040248120202074010aaa103449540000e0084c0c001118806038070030010b00340380d640c1c0c40307450b06d0313500c112022030501b20107004000c10059032180106881c90200021801d05041c180080c000c044c043c04040d1007038803a01d10b030a50b9104208100405035503103074840015824038803080c0011f0180d0f0458500401c001c640081801c0c00c5181c250303449010144d40f849103129441e10706a135010308411110790555003c0024890b0040100d824054105c0c1c15802043c00740707860301c50940924510380001c1d666801045010001d40e81c04000da8083c04801c0011040782c1d150300e610180100031076804120b10b450007040000034050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 120483741 1250 120482491 120482513
    0x30d09030305180309061b0a0f03020a05070911040302040f02070812070909110301090f060302031f050c032703090913060507021f2f04150f080f0a0b0d 67
    0x103d480d80c0079402090b510f074544034010701ea21260011002c0c4100c0b4008489007445040d07043c45403007610101d40c0d943d191083c2c8082c040380300758096802604080d08205d0100688402007001010400c0b0900354041100da01d84102d00c0080e01c15900e809020116080c6507040302c0e01c6560180701c0c6030307880500c5200c890403110102c40d22404900002e00000e401c210502402c4103200407220003070700d10703800d00c03c02500504000145c540250354034800840140c42c02c100d4022031021400c500d1100303002100c172180540f50000c001d580b4031a0300340240681c1460b100c4c21510382c1500108103840c3c002d04020024514000c02d46902d81c4044154240310800180071f051402d1203004500c180041c1d901c144040e0380d100d03054140d035041d22600b1412688410035540c0400b0000c40020341d0013003910030002c1660420101100304501b000f00000e41000524000110701c02c40b07094604214070b14603031024020301454001041c442d0b000202034001101014940d2001d03074080c0d0010044100d040003410b0000301c60f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 120484991 1250 120483741 120483751
    0x4020d061d010803030c2505010e0105150604030b0c1b070e0402041b140d0906020c01020306010f090b0406081b0313020307050102120301180231050901140d0302030d09030305 77
    0xc009a000440e078410040105d074071482c0d00d00521480c04070700c102030410628070b984545100341d589a280c0c40c0025001c3c003611865411601c00030401d81007000c0400c211410794010103104041c08c000410004020118155010035801d08007911128503d01c9040d86200f9010446450701903000041030000c8070400d4140190b0003501c0801c031040c0818030014103081c00003043c802041000400452051018004241c50031401c880804c04102d5a41e9680990300507060183c45d5075008000c1002d01c1d40d02148500398182145440e0708040c1c58034006140a00c01c2e4003507801002200300c00142c035186540c0e00c00c24110b1138587d0443d62480d100500c0881907280340d004900c01d00805c14001810341c80020440304039045900c407549141d10380b07440740450050044149000f07540078000306049a09014040c11003203440d65211009050300d8bc0c0c10b43d5a000305400507842600c040005000a0fa00c40c2000320012505032015183c6030418103090340355010745032460310b41c2401c150855040503410740019009d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 120486241 1250 120484991 120485039
    0x70602060a020306031009060b03010e06160c080d02210103060c09080c061605010b09101503020a0906120e0d180e1513060f030c08150103020a05010c0204020d06 71
    0x5619a824101c090388810b0b51202d42c541c0c499148840d095400e035102c1046544900320019003180d02d0000710342900e052400014141c1c028100300a65070281c0e02030300c080740d40985001100c1050741d07a03404040380a882052054030b80c2c0440d108105042e81b50b06401180c12180b1000780c40c1d81c0d40e20309040948810030b0904006104c01100007000c43c1c0004800c0c2c42603100925890600110440b000005410020182c17a03542d04c1f0762941c1c05c02c1c0c03501d1000a004d0f0ba1410185070782c1c5420424900c2141e0142c2c90405c0406104200b1402d080b40c1c0320a10300709540f0507251000d151505a07100401500c40d00c211074005005000c8038243c403036008020301246180e8010a00c0501d03a0b2031911400c50a400c03150143c0901c00c1c0c400c50280d51805015080d1400d003030360f0b0b0014000d5182c000481a0720272a400440e00824408014080707030b07004102c2c0001d00360a8103040d02c078039130542d03000c41d02c0c114503841960b041c008a691200110760b00c90301034580648000c0d908003c095520340f0803060010041d0391242c11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 120487491 1250 120486241 120486253
    0x80a0c15092109030203030a14120708010e070914010f110d030c02070e060906041e02160201030b0306070e090a0204120f060c0206010605190504230406050f030715020a080408070602 80
    0x10850103650302500320780c5c0007006141044500d0b00c003981c04403d4548083c14a6004108000c01c070b144424001d400303030301c0580d9042c441c2c1d810555240e080142c050102d4081c4031056104102007400c104440351041e40c2031a08402513003801c80e06440c01180440005964000e440d076003c1a55450b62154084450319802c440740076590301c88250748032400b070340c1d0641c1100340000060301c1c0e030400d90402485055078940041a10f84100d0404080342c001c02034204c202c51060345c001041d503a05000344141d00e81d044000c1c1460b0b09040001808405001e00b059000b008803200081c90780302c0a505403801411844510300c1c1d0f41001d07107049203100c0403a501c11101c843c13a00c603c00c00c4035480001d1090589035079407103aa1034008140c5024403922800700203201041400c00c800f2900242e01c6041c1b603010503040360121844540102008142c1d521604190300550f4403503c0825035540020311a4101c032201d0f03200da500d54030494801c9043c010b00a002500c210800140060240b4001960b101110724950a48170 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 120488741 1250 120487491 120487553
    0x9010b030715090b21010803071518020f0402090d03020604150e03030c0c071d06030105090f030a05162a080102130612140c0901020c0904080a0c1509 66
    0x900b00c030307070b815400006003405024050500b4010051120000350b4128142c04410400502d124480176086281d20341c2012590300208001c010403440310303803030125040c0000400c442c07005c0b0381507002040181c0b207401043d45250480d03d83e5811600e0b10324010b80009060038050502135035500e81580c0407660454440d103401d000d04554401d008071840c1070400340d480c50b240d9030307005091a04a401a41c4440c01090030001d55140c05410034400441c0311100d01c50940f91140c1010300b101d00081c0313204140c0d00544a99088660301004840202e482c0e418039540301e1202c1c003181520034030f074280300034102e0f00025103000c001c8801400e0f108449040c1c0020340c078031940300c0c415607084c0d01900d00e00340110b1100c82802c0c40354900443c0301d0841402c600303030000b950039800400701102c440142c03501c14845000060600032540e042c0208074200ca02034440400f98109aa01c14059110b031017041000c205081024104201e1040ca80200041444006001c2c84071a4140b440c0d89203109041c25192003a4580c00c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 120489991 1250 120488741 120488759
    0x20403110a0e010510090918062004171005070305091905060103060c2c040f0203010f03080702120a050c011b0506070e01020f0a06020a0e06030405120a05090301020309010b0307 78
    0x3410b07200c400d60801070036440c0c803042c44040c4a07030116017802d215031001c0101d4002c1c80c42c80390382050285050b80c180c842c080c0d0700384942142d140b2507000107400c4e00c3d900401e1402c3e04140c100d80455403403207246800010381d0103009003080360200e034418070181090184841e440d4103800081c091071440084c1c603100034004a001c510305040d030360010000d800080c01080801c8540c3c0c000c0c140c00c0c0150400644442d05090010042d00440c50010642c41034070800440d00e0500c0d1154491306003191000314a1941000300404411950348070041008000164000c2103440750083d03550007100c403078126000d191443c5061038440d404044100e0010b014000d00420052803010110701803608080a40320a44988000700e0345a180b107101c007410362049500380d002010301040a4880140913041c010303100d0b8103030b00c4014a80500040395610a0b981401400041140814403040400110042030355178188844143c035103000da880095415407000c810044105019000350b002c84038100e007605c0c0c080e62280408 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 120491241 1250 120489991 120490009
    0x108011203020705130204031e0c1d04020d050304031a0906150f09070e0a030f050c0102070303052506050108010f0c02030f0a0810030501020a090e06010c110907200102040311 77
    0x15005900c43e210030091400c10001e0641c0825032200094949a104d4a40c00c1000048440300c520303501120f1400d400b03004030000c5e80c2c406002440804942030000007400c0d81f0825000d072010344205440000c00080180410480e0f000790b81c05070b040d940c0c0301c0000804084000341184c040f10f560107140c1c00920380b00184c00b60340d040454000c100411041c161014070030b14001c020a4034060000e43e081c08051980c94002280c02107105003019441030040745081030034842c86d20340381410b56000e039105100190f0404140c9401406003802c0e0b042c02d5005c00041080304005000c05009140703014000301d1008810b4103c40f444680a0b1024032031a90b400b50200d980c0e00c00c2030340c100304030700c030500c5402c5d1003c0c42400219009140420031003400c1d0740740c1d103c090881e80400060004204a0841044003550100c240d41c0d005400b42030a102090f0305803500310418400c1030400c0d126090000001d01d42c503001c0c0c032010000711301580340080390302039020324203000358001d0105403040c03400720481000b00d11f403035404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 120492491 1250 120491241 120491243
    0x8010b010c080915030c0a021c02060105090408090d080d0b030a1713031a070912080a0305090f0106170c19060302070812090c0a0501050c07151403090a0201080112 72
    0x3400c2000000d41c880e040d107900449903455114800a05007540d4420741310140d401880009115943c4071948440a454000085104800c0d9460680381210054010944504486059840c0710856a5614060045108000c90785074840c003c0342d5071505200c03020000e4007113090f120000300072403402c410070590344840005005011107094442442d05180c440041e0810b0800005000032041c0c0702d03a15210780c1c05800c403684035100440070030088150303400281200207001d50350800134112450748842c056440703070b007105000341030b1141c01180e9001401c001d44654242030b01c00811030140c039005c4544818031031400495651103102c018071a940b81002c00403030451400184071840c44e1405106a001c1e42005c0410303591031009004c0303054000350100311036106040a1002c2c01450710360b602001009803031604060b0400c8014410f0704629940000c1100607200c14000142101100701c030120341c2025040100248001c2c08021300001401c0000c0329880540300b6218140580e88404907041380202c4148 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 120493741 1250 120492491 120492497
    0x60302120406022d0d0501120b161e080702010501080f1b0409080708040f06171f0807031b1418060109050d0b04052514030102120c040602010608010b01 67
    0x807a00060140d4018915011403410040b80207080c8400e5203488403007100700400c1d0210028080c00e010310a8422107000d020011002584d444280d1588601c0e0b0600a2403101e46080c03911070b240c5243d0003030b5074034503c1900c14000380007a030414002c003c1c03000c3c406407003c402540c00c0c00004038241102050308219180e0084c002c2130050b00c000d128941c1111203460094100b0707600c1c0800c502141c9200010b04005d4020881c441d40e442c948000700880500d03561002c002c0249044180c5120f241c200c441c650401252244120f100d0031030f040c1b030740201e03c403580421030520581500100300036808024040790855069112542c41d911603140d81040750b040345140d807200c0d150442d11202d0750750803203ca0b04850103242c261a059210004588416490041914109640c80801c010001d0401c0b6800000d03003548611210602400d0412441040c1c50244100c00d4500c00111030040d1070950503135119803418400b4810074204044000c00d140d000303010b0302d40194205000400c00d20014000d9907001d88040e9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 120494991 1250 120493741 120493777
    0x1030608192901080f06060a18050403120e1501050603160f0e040903111006080705010e130606080405060a090506060f13050403030f2301060c0305120106020303060109060302 77
    0x399420a10032600c02c259402c901c0303007045480e800095902c140d0301070001100140502601241d0151520f000100501d02c80c0120002c1440301c042400701803d03601c410701c01c1c041480d4680307260a0341d562280c5c840780b000481c600102c102c04070300001401031301c1400c1d1030106c60040c3d0b06c400c14440684001c0700c0c40b1104410942c3c2c4858003d1007440c1c00315511199180034030190320102d00103000d0380da04c40780640c00610032004bc074540c1241400000b0400160240401c2550b1030148510b4039040d061180728140b10301c00c586241d07291210345801d0740d0400005c104002c01503c40344094802582554146c90314825000001c3d030b1000b0138071a9001450700440205103903aa800b040060a050b0207110a802560380030249842007440d0042901991103506c0c04038884090303502d10b40840d0380071600d51351103842550794041003000d034216080c15604d0703500d404821100c007820240c900d8861128410300d130b1485000002811680400510700400c3c01341e07540150166509400c4090380201c503580c03080d02000b2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 120496241 1250 120494991 120494993
    0xe0d1b0812031f030c0b0703080a0c0917010f0603060f0c1b02090711030304030809061302011202071e03030204140d123603020415060512090703080a0e0103060819 72
    0xe1008407480001c0b070b01a058404e0b220b0f59000a0030360990b101040d542c4000c5883e204041d001f4840b2640409114401c12202c862002e009162800f1445200c0d00403103800e440245450382034002d64481d0300c541c0014482182d0302c0c41c21303800a180d200840c5a20501d401801c2c50b000b8400c03810040e500ba2a5891b4850444054080284421024160303505001c2100170b0410804414005548601c0c0240c94020413450702c05003141c281740000b440c100307414018842c980c0050380c001248101c500680d03640140c540318607180801703040101010500d00200450501300405078141c0007002916481c98612640e807200307105105981012a200514040507260038010161164001d50301c002c3d0159402c8502d0248581040a0300050703030488458a00d85010074419404d05000b20080c0712500075080100c80c4c90040018182d01581c20614123140400020ad8540340007000710324080d5801c0242a42e5500303000c20007624207440c0d000b1b0740380400e041910004145030b003c01c0304e55861403100200d82c065841 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 120497491 1250 120496241 120496261
    0x50105150f040312020a020901080f0307080f091206070e01081009020c0a080a090303110303040c060c03050d0f0c110c031207230703030908010c020709020a0e0d1b081203 75
    0x12491402018000030720000010400102005501100a4001d000c1d0030486c0e005014031140705800609060344210341802d0304c008004200c03030074160460f5007103071211840c3c105289030b440342c0300e80154090202400160880b101040e03071801000e00d030f115204419034841c01510001d20441ba6010804007440c801c1080440b560000c0102c86c8509094921440003aa0b669585030042003d410005090100a004060b00444084100300b802c00040d821440c2594540a80251a005013400c00c401d817010102018011002d9900c1904150300900600d16018000d10091009502d06c01c00541c0c0d00460880c010808540100c9228010b000340c02190b80440403440d4a50017200f00b1141190440c01641c642003582600305900001800a4102140b43d403c0050403d503641c1c00010481c1d00d02216032541301d400040c4076045841d40e600168650780304050684240c0a9006100e800407500c40030310003041004203d1400b40042a0742c001e04007522006441e56440000c082600510b1080004c0f038070b4480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 120498741 1250 120497491 120497497
    0x4030518061b06010504180503071202030c1b0a06180b03060a0807090e15090a030804020a080f010c090803040803030c0d06050d050c1008062d1002030705010f05010515 74
    0x20000d003440e031412501400b044500380300005034416940026006108030310f8070703000b88203403050410703d0442100800d4845a840344141140242042c1c1491070034841c8034000e005454011503401c003070358081c1c0c004200c00325440712828107481c0b1803240c400000c1100c60080da104203841410401081e000c0e814038000c5015540702903c01540100c00f010f0000b0203a408210b040d000c0c1000400229511144a240c6441c0c15481c00252210040603000c21504500028100e0b101c0c50300b5103041c440580307030742c008907003901c0454110313148038002c0042a83d901101504001d44440f11950b803030361076075611045503899000340c0c050803549030010800300d0405a1540058a80600384a0340001c0e511356800008844007040c1b80d085516410160104100d482c02c108608020b14035820501c0391850000002000b40d004503c0082030040c241c44400600003106481030305000c006402d401c01e8402c03c0c400179559810000c0c5c121815030030312600240e24659070141c0380c12508054281e62a0085a469a0006030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 120499991 1250 120498741 120498787
    0x607030c0306150e030d050702130b04020d060306050402030f060c0d051005091603060b040f0303121b090512010b0a03020d1b0303050301090b011e0f0e090906011d040305 75
    0x6846a0b000325a00940050150404015898440380c444480050600b02403c1001840c10f01c0001c0c840640540c40d141c2c0040c942c80d078044400151300d00e003c000600240910804581c003285001000b00401100f0f9104030b001e54002c404480c0314182d074030801d0303540d05003c68800e08045024030013403181d061207070031454010100c4045140e03c01d80314808907629810456115580f1011003035202d54042e054400d100141801c6525140350a08040001c030b004600c5100c018100102d03070180c071a01c1041e81d408100c0100e9a09604030504075a0f000040640c1c8207802094030425008200350014407051090981111000e429a0b103564a99007c03c00201d030b500e1000d079407581c0740e0100c842c4900c0c9070709440320285d03203ea10b50a40b00d5060542c100110307013030030300041e0501400e030a02c1110b11101b84400400390805190040c005150401c1c121168406c0403503040c0c00c00c4c0d41c0e074188444843d0104856040c0c4059194011a2618ad54212108044240c0300540801c03410050b4180641000044882d06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 120501241 1250 120499991 120499997
    0x20c0409020f0409120f020309010207051c020910060e0901051005090112050c0301140405090c2202030c0705010b011403010501080c04080a030c0b0108070b03060603040f08070f0201080601110607030c 88
    0x30650003004141640c5018004403003851995042c0c490b13654110302d28401b1802c240c8002c0d82081500030011790742d44814002c0510865807000110401c0c010f14006030480daa020300545014144256000260307540c9004a80c0031508268030113115050441e000d9040743c40003405242c1741e91081005940650060036018100980d140400c600035096004280c041c01525080a0f5a90301d000c013610020540707001054403d904080600601c1c0100003818620301c082115040180b00701e074201341120030b00d000c41900e982800481005003d00071a4054a90310b8041e03802440b6041064004444103540c41c58a40500342c01400107010ba540f2442d28030360303c01101e600e85031038280c541c908a81b80550001d41103001030b0710b0740352100411541400550042844400614502c2d0504140b511360f40402401c03203020381d101000190506c4172040c0500c4c140ca8016107104c2e42e80c11141031225034100d2504042e03020902c444049078681d40715500860303241c103e0002410442c1c881d1031044000e00301c41241c1c0010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 120502491 1250 120501241 120501259
    0x30903070f0b0103050c0145231203070602091804080c0d0801060221040914090d0f0503040b06041b05042108070308100e0c03071707020c040902 64
    0x420700702540e2540da0096859120541c51803505078544003515894604100340c919507605441010260314103248065152000072980100324805401c0f000b0b03c01624071050002c000528800c0340038514400c103107860046000700440014004421004071014034103034800c001f21004100954098245004002d00d800005400c80220009103030f81547c05031454a00001c25020201080064205a101c030b810140b03070303940c90240003035101c01c0b02c3d0841c0c2040c01d050080c1254540034a43c101c3c1c0113000c00c08410031144503100f41241c0039100864410701c0300c0c8035030b40303030b4555a42c06419048848480c56a07054030350f071740301e580300784a0304c4010b0000d81d00192105092141003195465031584d403521651a161924500382c0360390000d90368817654983e00700e0a0005100030075204800c54482540505001c0c600b91500d40319200c0cad040b550b5000034241480d92090101c18075030b120045000f43da0340d5660202d0369841340081d041d41e9074280c90b0003015a114000f843c000d41800d4000300d106d0380c0000c1140d05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 120503597 1106 120502491 120502493
    0x70c060f060810050f430207060203030c040314011b0f09050d0f06020304031b1a01050102150f060d05010203160207150f03110714160617010b03090307 67
    0x400306c0c119140500880b103030003200c5800781a02051910100b8442d000d032181c641c2010b110300005016807200050011310002c2542e0107099561105440c29107140c0e5080403ca610006107091552103420840031903104c101c0703214036034030a51550990350206620080c40e0b490035401480c41810302e000c02002180d000340302c10b1142940282d005075292100e003011341d80300806055a00c1401c0c8030f03400242c204070105c9101c034958075034001511b101d40d89880c01681c030f0790100ca00c00201c00c091728000072621200c0c120b0003030300100050800701026585894103070990b4422140c0780364009000b2032402c22207904100ba03400900740c1080d401c001050107000200000e001c0c141d00d50405440c1c0d05440c40000c041c50460b000c1c2279000e210b4081122640503141c0d241d141405034018141c004880002d0f0081c0604040a403550004c84191140c0c1e081c0000b14031280c0000c3c001504520050040718 = true := by decide +kernel

theorem cover : BRFrame.Cov 120323741 120503597 := by
  have h0 := BRFrame.cov_init 120323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 120323741 ≤ n) (h2 : n < 120503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
