-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2475
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:27.488242+00:00
-- url     : https://prove2.me/submissions/7cdc20bc-629a-4d75-a043-63afc91ecb8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 444964028 ≤ n < 445143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 444965278 1250 444964028 444964031
    0x90109051e01300b1306050702160b0a090803041211040c0f030903032c010612030f03020a0912060b12030a020a0b10050301091202060c0901050313060f050705071401022812 76
    0xa490f05031044101185601202c1c683c1c2048042341c801c0d80000345061400c1d4028a0390f0760018146880c05085400c4890301c1e00800c40030040000d001e136000c0c0000d0000d41202982c50b5042009400c10310080b803854503401e030186240c250b1500e1860350251410102101070300d0003089602072410214084c021a08400c00d11140d901e640444402281400c641c0c007582c1d2030000c0c03100355a200c580900408030840050041110708650600d811710076401047e402d9440c0c00d15032071254840d15030004801b85080b040303411079501c070040c1d91285042c0400054104001000b5807030440c0d4490001d4841d02c0e41040207040c41000e401107185528601004000340038080d008104d80112400c04490312428070303980102601805c0041200712000c601100d44122040e15143c1c0741d40c45652111042025480095403030660b10018021040103a00415004100c1581d655407140321a0070b15000c1e1001e6401c40c0c92917a88100902c08442030721100d40ca4901d40c1c5644090341130220740f501a21842c41300500d4400b842e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 444966528 1250 444965278 444965281
    0x1213030f1e0305060f101107050f090103021201020d020315012c130b03030708070210020c10050a0509031507121b0503060114040e07080105030a03121505090109051e01300b 76
    0xa81d04c10b0b5103e2803071902a0442344c110383d039002840101c00760b103a09141c10038800c000501c094140803e0148403c101c007000140f40240d036401403012a00107540b9403040031601100d0540ca980d1041d141a0b100c41060116080312100c9028101c19072003205079540285020f12150031101c1c000d502170618000041e065030f80c0c1d03c402c0d2411400a6020180c100d200d901e066002c40e0841e440000c0c100c150280c003400a8259108210302a140b68004807600c10410908000074000c6403010700071400203134158101d050441c201810301801da0403015840a038854a401d0002c6040b10300301c40b0b40c08200d8440c4c1421030f525101c040c0100e445c1c4214403040d20034802d0000d800110f4007001d0180901c00c00f0241d90b0300966903254003c142c0c42e00c244181c0070700020340d2201141c800c0d0100358003140000500008560400381d542001c2090604264404810240c2c1c60701005803010606158219200109208080f950b04024a10f00144454003000021503009046045209602c0c1a040a0700b600000d00440b075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 444967778 1250 444966528 444966559
    0x207051e03070e04060c093210020a1e08070f0203160b041a0f1e0409060902031f08030706050402010516050c040b0f0f060904021213030f1e0305060f 66
    0x2103c044d20211030705031074490340c105024401c041907c15105003046e1100001280751843d0701070044001810340050700d0f000d00032071076620149400c0d480481500a80f09440c11414000c5100391030088098107110466481c00c0086c0ca0642201c00d0b1a80c404400740d0302d001c90b070000c0303480c01d0314901c4071402050800c4404034040b0101e00c042c1003110300c03190102819200a00c80054030b8000c500010070710103001d00000880f204a00004445262007031300180c20190f072358000ea411350f16164040906a07a0000c01d000c0300d03040058200217040c441010075000356145c40301055aa1150720700140c401c2e9590b00115046a12480848004090320031920706400e1103814940d4841c240004c050303100301e140250b0b414450516030b80d84407821038000c241000303082502d8184803507640000aa030350b102d80c0c20001001a00e040310b283c0b50140f00300b450b040d0340c0f0589031701e809041d0250350301d030820501030441d00d41040c240e80c1e00d07103140000b940740c600440e0588942c004242c0c40382c1c2240b9581e4bc8580c1c0107100b03241 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 444969028 1250 444967778 444967799
    0x304080604031d01020307020112090f02040510030302060c070302070308030a0f060303030c02150f0112050111130e070c050606040209011803032f03030c03070c050106060806040e0303070207051e0307 88
    0x40702c1c41483d88039501200440040e640e03032045c42c1000340030801e0942041e00f0305405038444070400307004101116490805a0001e812104125a030500d8201483d01c203105140d41048061f81c4084604c3c0c03224a408010744020399145068031004000300c0c00000060801609034200743e4600001c140d061090540304e18010f40640898000c910051280d02ea07103a41c0c075003102075140d00070403807018001450b03401c064200345e0004010405a40541d01c0b80200070400c0d54000003400340905400d80c0ca240ba90400c0740459990401802c1c0c07408018040d51a400414404514a50000300485005a0700c800140069901200c1ea02c40403000c80031044d000403e140c3c0080c0c80310008400c034504d41a0361a03440d41402c202c440d01c55101d0390b065006100042c2903120704402150040e44906000c50000c13a1980d400707003556240d800150020705410244003085c00c050041c100d0400c001e001840c15407a025500039030350344040c0300b500c0c0b00e411110740724a04000340c2e03005c044040d100601070319421907e0f2101c40c070303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 444970278 1250 444969028 444969047
    0x100b070501020415020102032802071a010906063905160503060106090305070506071407170606010804050c0907140c07050f100c030804171b010e010510030212030408060403 76
    0x108130080b07913441034103040c0c410310860384a280100c8007044101d9611400030b400504c030050941d08184d00700580c0d00031a444550445846030a00b45050441d8100803200c000d075907a5511460500440004201c2003614081b0810344500700b16901c0d09941015082e0003502c04003000d00a1324078021070380e00881446c4001d08040581c0c0080c0d0803191140d076982d000f01d494415038440540960840b16045c883c030718040c0d00802985002e4015080c0401710002c03903500b031500350340c40031030481e0210072540c1100d00c06100b40d991101c02428440d415280c16211203480f04114500e16100d2a0100c001032230850081d00110318000d54901001d80b04c21188010503030310038050281e148641464189d000305441e15601843c9007200c00c2e030b41c80e000083c0a960aa42c0148090030445000444111001880282c0700107040a840030340c04082155020384485401c603000b04401c60380a905281c00c0108802c403283c0702e0000c50381c0c15981c1c400c410382d403881c000e0305501842d04a526180102007d2006160f800503004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 444971528 1250 444970278 444970289
    0x2407060501150903170d060e09070515040509181b1302030103030e060304030e03011e0e010605010e1003020903060c031f12030c140a0b10050d1a100b0705010204 71
    0x300403a98988051041c4407001001d8080050b540d4081800041d0003000511081d01c85d20581034204807034041c2c04401d503130703480c1c215000310301600301040001c00080010344000c1500391020400c0514288000000d445207020f0035000d0180c80c40440e400041d01c110381702d40c46880205464140b03081d0f0042c042c007140190405403243c50b026009035001e02d410700c00ca904899054484030000700140301070084a41000700150140300384994881c00c940c03028049d44c2d1415041e030801c006155001341d0703200102c54141e408186284c0c07411201f404966040307000310500e481e04492a403820011484110042c1c480c0c072444c43d030035020300c8043c00410103002c00518001c1503032440301809268265000080c0c02c9080c4940801c0f00c20100031100842e004411081c20580540d20b01c100f4140182101841e204d80c2c00c0c4120f40d04001c903410002d08011b071000500c06400c0407902c541c02544a80c403104070800f1000c03040900050000003080454004020201c001c0c114076010f142c0740d805606109000350024403c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 444972778 1250 444971528 444971531
    0x40e06070905030f030301061b0f0303050a1a09071209060213060e1f1206150c030908010606050304020f12150a06050d120f050f0d0f0e0102040b0315240706 69
    0x42600c3c42e000c41c56580c560091802581103a180080440d1050001b030450504d110b801100d20010402c040b06109480d401b03620041950304040c2d14040881d82c5592200f000d804800303035404481e5903000c10160f00f002c41482c000740304014501001d4000e000c6c00d04010000341c070002d4941600d82c1d10310160b00403140039880d003400e120352000601000148088000414004100030740d840c240c0694a80380f06142150310005c1d005032594030340030101015110100115440106440c1090742c0b04000001500c0c60500900c409480c0c1500a412400040e00c024480c046001d0000002d403144120350b591350743d229003100ea902105410040b490042a91020201810000046890308100040d4042580d1002146541c505001c03012181c008440780c03d00104202040044040e1003c0302c0605050040c400f4001000c1caa0505035034102c0394013118110040e40180001c02c5090401800d980d4004070081e06520202e5448001400300306110070703000061040c0c903540a0744a00c41d10050010319110b80e80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 444974028 1250 444972778 444972797
    0x501050f1804060c03021c09050708210c0a08130f090c0e130b1f02210f070602040504050708060f092403160621020910030207020f040e0607 62
    0xa1140982005104500740503101c808200060490341c00482c3d100a81e00c0d0060811501c0c00d9080051000c01c205a00749903266a0780034148034081c4a2507005045d800010400c008103184909074040303c0700d0041e00b003e4008544054250070912603000c0d11540507000d665076a1400d4000a5204414069040040c50881c1c0226401620b8400c108030700015440307036030003140c01d001002a40b000e01400100790646a600202617070311a680480d440d0b402c0386001394414916000001c0c41c00365408400d01683c20036060140c04d8165040c01c48140d2040510040d0795800030381081d00c041d00c103d510440c2c200d0724110070009102e500891710b60045004991903500f40285d20200549500256400da081080148849035000d6000000741000c0768003a0a66021a00300701041c170040815034403140200e00030941c1441a503101102000419880050441c02c02184038041000c2032443e85103079003810f070300041c0b00c025035640045440512200800c24000081011039103504c0d039006464410100b41c451a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 444975278 1250 444974028 444974059
    0x10902090306040b0a3c14011a0c0f030327070605210f04120804030c0f140a12080c040b07021e030609011b0804020d0b0c1c050105 58
    0x8035001010010300605054550342c0350f000c4410409002c9011207940d8030744072055501e05141c0c0f42c01c4544040b0034012124034900300c81000041100e800110640703020380c2840d0501c2c00c92092030540e461000b40e00c28405d400318405550740b05141c070303212040c89802c184404450380080154401c00e00d89031036082280b4001640a084270503c01081003075000020f051203030522a1015002c01c01c1200c103100c42034000c071010a168a43c003641c1e440c0303114031840108424880c4044100388003d02c00c0c80d1026803403910b61030080442d080c516004000c0803180404106100c0b1107280005080035a50540d802080145010f1154100070003074170000ca80c1003800102d10b503668405550444e0080307000f0320315282c042d908000603510803500703214414125036009210742d10200001d910608440c000010420558000d29107090495500c034410042140e00b00001a1502c92103140c0899125000c0c3c41c440d2a030300c00700c1300c4a001e81d03983e5240303aa180c1d1030b01c0c284088085d08540d0480f41c007902e003c903000c0e8096 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 444976528 1250 444975278 444975281
    0x12070501020f04090b0126060f01030b06130f05061215010207090c020a121107030f080412030503010807050f10030c030e030316090f030201051e0f030a06140d020108070e030f070e0108060109 84
    0x480c061f000303001c5c60001910318284100022446c01c8149400142c42102000003609a00108039400003086036440a11007440034604940207803104841540c1420600c03040c0c3c00045c000249821480011500c1290060b4003c001001c060407500c00c0520000000e140004e59640804406135034140704408000041401900d214900700e620501038900700d4210740310724035140d900000454500d8000c2100080040160300112085c41c403d41d6295600d524248240d4136140194104a1040408142d54130f1240d94600b6800c4140641f0704001c1040b0440c0348c401e40080c503e00089695a000010030000101140a8181c018180ca5203c5603603d41c2c40b410010b121100c0c07408000c0c04030314200080782c00f003a5070030340c402c84c1d00300d861164602d44113a403c50320317440e40c06c00c1e500c8001d00d13511030368240280500004010f410074426280c2d030280340082e4000034090f000240040091214a032040002a01c082c005500c0d01d40c003107011140040d40c1d9101c020b80403142480342c03140c58080d500000c503111189 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 444977778 1250 444976528 444976577
    0x1030501030c050d0206070506070e12121608121906080127241d03030601140d02070b18010506031606051305030a1b061112070501020f04090b01 64
    0x801070b40861941010b09012441c802008141d07480715081c402e000010b403041203400d20904040c0c1d103401da15651082030040000c2c2010390000e95410186a00f5140403060040d9030002000c0d0b80b01c030071021983e0519400520540340f585000d545004100505001d5000d06004404c0e81d0303200401c04545e0701c030b180600720303400c0c6818003200842050301d07648040942c0071140d02031402515040c02d11050a9029150000d10020703440c091605c400550300341610000a240101d901364006c2c516514041000a1500c50040c42c40902d0010200300d085030600303a0780c152a04580d1012442c0310b41e0400d096003400e6090b21865030390043d170a00740040d049040100740409102c000b043e60754045400c01b4030559054000c0f011010032503801c20300014041e034082240c00741380303402031000542d00311110702c8032024040c168020700f061045100c1c00c41c2000364005080c1030054411034009895021074500759019205441503811103210108001c191120180d100462208090729081520700c951a45500e00012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 444979028 1250 444977778 444977783
    0xc0503181e091b0c160501090b0a0206060d051006060c020405010b0f180f090106110709050903040b070501150b04060305160f03051302120d0e0f0604050d111c030e0103050103 77
    0x200001c03d00b010804146829000d40c42065142800c140030500341c50a2210f200c040354030400d0034820803417943c0000100c1c0140c0044003041d4605000d1410181da1410301815240c01921201110300900c14144013407001000400c50500086a81c5c1704000d018000412059100320301e40000007450802210881d02d420005404080c204a041849000c00c1d406030081c039a0054001544d614455642403012030180030140c85803c143c0c00d44819180c80d003451500030714591480c25090190180c00002650115041c42412a55580c42e41c03a006000d840304584e0f101104603050030118182801d10040c10070b66819075401c1007160b8810ba821006c04401d03140d01d0002c500a000401e8601d031083c0c00c02a40448000c4001501080366030100701440055003903161190411480b48400c150702c028101c40946049130040c14006010300012124032403407140c503100342c2c01611034400f0030000c21001c0090b41310090400419405482452603c0d60140314120001017801e507074581150b001e8411581601d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 444980278 1250 444979028 444979039
    0xc0212040e0402150c01061706090d05030a0c02010f0c020c130c0c0b071727030c03030705160c0303030f060504021606020a0302160606360207030c0503181e 69
    0x44854007404104031400c1e021454880f030400410505d03030400d01a4000401243c4804940001480001341c281200600700401540240002080480e44a0300b901e0700300b000c0303071400220308806440c268010400070802040c460300341030003d20000d40224030b14000307080546066026208103502c5034215101c14030504003062200100a0100350340d12465030340031400307003001600100644035224842d4000c8a0b4181c070920103c0510340542c1030585002510b510a00042d410f21240d60885c640301d01000b0040c10410601007040c0300c0c00e09909140110050f08000004425501c80c10f000b000b50544c10704060055044c45800155410b09100321558040d01c01c00a80200c05d8680c0d81c44080d41c4495028004c05409008207460304603d10902e5103250f201d820005040d502c3d00d104003030240c02856a0400c1340743c2000c0203011900807070304219120030140744016a10005481e003510107440850300505a03110114000804004842d40208442011128400d01417842600d070221b0300300201c0501c1c0c001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 444981528 1250 444980278 444980281
    0x907091d06131104051305010c090b0306090405010902100512060f0f01081005040e070509090c0d030804020102070b0309060f0c0f04090b040e012c24190f0c0212040e 73
    0x502052610880744070340044100000d080b0001000e03a032040c0c50906d00e411301c03110000d003001000d120703182031107445082020f9158a0202072143d0b50100800c43e90040742c054000808212080d448440040d900a00100a1103030902d0014040d4015520442c0310035a010003040003840d2074960590348403402461040040000001120030500140c01d604156400e0440030070756a545008690084884e03030700804c40d03245882c0030030540c1200070b04458010f030010548a01c0546540040c2100310f501800e0584180d122480100d142c0703c403030b070700c4002d601c50b01005018032448040b8181d07010ba0307240c10100b240760310307809610718462160040045480100300810014545036030800c50394030500410000d03000810b0742140d801e554112002c0b03c21071030b04141c10318050b038201c0301c8102a201100c00400081e00e030a404040035260114441503800030410004d8014440c4052000309240f0300b040c04c0c401d01e442c0d168007201802003075a4110150050710068100b4070700c0c0d6429a070440300900700b0002c06 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 444982778 1250 444981528 444981541
    0x30804030b150f0f01210c0c0b0c0703050f1305030a03030b010f080f07180801021902100203040506010e041b0303091406030405120a0c050d0c0c0b120412030609050907091d06 77
    0x161614460421045110840710403100300c030602c20784003200c2c941e4603540000c2a44d4617103270500250041c039168100700300340034a5011a0b88607040d5482c1034184901180e851003561260107501601e40d00041d0705100d1041c83d00300301540b41d0001c50049000781c803074400e84240c03030500f80c0d80744004032401e41c456900e6100040c40140f00d016040c05c1c49030080003d05400d526040c3c001d09a1340f0000d50842c2508030348540c10410741e41088060450308d0034010460440c1001c3c0c1d10300d41c948030706102d500c2c142e481c0840403c043c82002c2880401000c030028078011110360300c0c50003811409540c82142343c0c0c3c110700c0f10300e8446410054112441580d00201030440e41e103580f1001809600003034410800c0280c0d6112140000340100009003480b03c064480481d0b404846c0340051036000e00d82c10003440d00d0402d1000030401c0744c840340a180c000d40d010300440400d80051a084000b0559030340306d400840d007001c0c1401402e240100c0c0302015100705041c00d0048504c82612509082c02d1400140340c45c0c1d001000140c039 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 444984028 1250 444982778 444982787
    0x1e010b090f061806070c06020f190b1504050406060f080c062505030c010b0312040b09011d03010606030e1c02070e13060204060f09091a0118030804030b150f0f01 71
    0x2640e1007100544405401d00c03c0200b902c5812800c0c0403226075450703142c14441503070100a591745400881d001407084d8411411108508005000c004011404080c086a101c040b0100e01400070039001d0f00800c0340b4942807c214010f00810701c101c0303441019419001c1a07081c0041071006014401810640c50405108014030711943d40c00780d1014510000c620003c0016001d00041030409401e800100310b40459808050600f4445c00058007041d800300410019000131005568024009082c01860141508a45154213202c546415495440c115021940c1601a40401c0031350540a08031074940d82545a00705041104108481c0581d0100c2e9080124000d4400025409085070f88180d01c548800ea942c10700345e030071681020020528504000e00215070184284004014044041c04001c4100e500c984030428810442070400c824045503002405100143d43c0c019540800031691703841d5241031480c50f8400607034414901c40000140300c10036240101100310581c100916440c4014003c5c0d00645 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 444985278 1250 444984028 444984037
    0xa060c0b19090503310b09030a150905010b0609030a02130906093f0f170c0a140909010b0a0c050a1b06050c060103020d0512031e010b090f06 62
    0x249610a291020000400c1e4082d401215224400468880081004421955045100c0b45800019582404800d01030443e07052085682c0c608034190780315010400f190a1042064001e8040c2d42d09061280c6003220a601510f10180248020001600e41004101692080383c00d40c03a490b900c6250b400340940390078071308801088000b08000656040e030b6591102654115102a110070b0b490000101c405010003001c1e04490011202c031a05031301107008141031245198411100300980075414000c000d01922548500300b0070390200380381034a0046207503038680c0e11050350b0f04d000650321000c0c400030580140075203c0c00c130f000824401e0300d81e003000503940c4103400a5038983d00b0044c403070bc0c10001260080c07280000d814001c07600c9403102e4043d41c034511180c2c003460303014504000041000f04039034000440e1890640b5070440390700038040b0050802c1480d2000d1001241c40022002040c0038000c4d0342e025540c000e103015400103200c03c0c0c1c2e881c426503516004203000d01d03400055502c82c03000c9a2401c24000e1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 444986528 1250 444985278 444985291
    0x3070f0b0c10140402010e0102060403120515030105040503040f050a0b18010507060e0618070e0112050a0c0902070302120304020603040b10080d0302031e01030201050d020a0306091a0a050a060c0b 86
    0x110008034840d040071059070b660400f110842d8400c807040c0015035a0088103000e0b001d000703000802d0141410340e001884524568006200360740e940e008907004c2d456501d80503000350001002840242050700b055502d96106102d078a07a408149000080c0074100208a842115454180d190074003542c400c0100b81c07120072819545c1048010081e4030001080c43c4a502d8407403456900402c19413804000c041c0c4009441801e003a5158042d00d410442408200c22082c103552007840704541448c020b26003185080c0555000030b00340220001c000c1400c0e003190380904040b078025400c070b81031416580041d600522082e40d0294100c3e904100140115086403040380c0c010f40280c030013000d1283d480e01524104030380342d8600400a6000405d2084400c5000540d14940010b41d47d80d2540e03505d1940060b14038400c0058400500340c012800520b13480c0254000d400400881d8800e105070350603100c114920000301000d152040459a0380841c5505015008009844a5451701400c07240c1d030fa16100782e42000245007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 444987778 1250 444986528 444986533
    0xb011508100306110d020409020304020301061403100b03030d061e1d060d0203120f07020f090c09090403032703080a060e18030409231303120203150a030b0a060503070f0b0c 76
    0x3802e1941040d80300600040c08d15510040c0c59060601c10107003503030016841140211911031080d00255004074107000c401c2200200015015100700c0440d040d80150400314407081c3c542071000030b640f000e00b6030360301c811004842134111751b9031a42c22aa29030181d100074588030307419090004410707081803680c0d000da050005049441e482c40c0c0e8012a0216880346001117100000491218214201200d444054242c11038a0342d110b880d140b1461304040c000c041503240300320fa03c5c002040515000e070f07000c0c01d00703c0360800340d4581000c1844149003001000c01400c50001c1d99090010b213604545101e84016144210f88030041a180c0c01c4003d82c1d208803040514071140010840065030700410311031081c00c0c16601c5a272074109440c0c0103c15044401c01008442203081c000031510020f0f0348420000c0f00401503400058983c1c44212075000540b005984a07500701e643c0c1d00d000710500c005402204c0c42141040c000303000454444040c540c0320100f80c801d503c0c100361061020b2007403100741405040074a00300000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 444989028 1250 444987778 444987787
    0xa0f0e0306150f06071505100f080307202101060b030901060602151005190315090b060f090103350a03060e1e040203030c03070b01150810030611 64
    0x60305051050b25503400d0a0300602c03074049542800a03244403044401c48480c1c0c2811056180c205c4808603a04800d0400d9507110009400070300900304a4003d8641d54590941654813171018179520303845205c065424003c41c05141080420494180c169401c1c06030900c2c603101c0400201c44649030f91041003000c0d0355200c2101160b108400c4002c1c51041c070010001244503460300700041c0c00d00071030180e0400b0380003101081011482083c00404e044440c1502c14031240e10742604411074007074417904010040d0ba00b0703141008107954690000403c5c580a82051310541d01c801303040002032180c885c0165006224000100701103403220000c6041242944c01072114840703110b0f841c0d5a1003a245243c040b0400010814001d100e5140c8100006881d8028080041d4108069a04501d07040c4013044441c3c2c80340e07403000500715101401030b520003001100849496000c985440485084240101c100b00707603c084d8162441407168021030f000781c04452031290803a0850301c0c0c82010301442031042c6080c160411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 444990278 1250 444989028 444989057
    0x2090c0403150902040b120a11191520010b01090509060102070902032d100f0f051225051e060306060d060308040e0412030504051c090b0d02030103051903050a0f 71
    0x1041c0c486401f560038007800003101e491500100032040000418040c414207440980d400103889500da064404101c81416031080c0c0d14011945d100c00030100f07014031108480d103100034040c15080071058075000d80740c5040340c2d030b106e1017405101c41c401c0b41c41d60700680c81000c003004404400c0d801140c1000320300e907030443d0501000c0409280c191200c0c8204404000c4041003200441d0100d29207805000d075031154200e801d1500c20044a120314500070144a81c54810019020240030410000903029945c024401902580303070101d0042d01d60b10030240103c07200c0c0101000d035221a6000004032030024041410368807000c0c00c0c080b443d00050071070f1445070b07551400031000c40d180c3c00c00342c002002460358010075803070946004107642900f25487c0050609200a101c0051000f00b00500c0035402c007045003581c100000b00459020041d0342c80342201c4000003d10300c5019500d80c00560580b40500110390024000840c1480c8046040c3d2000c6c0001c3d80c284001e0f41b46500c2514008e80703640961030084801c03c0b550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 444991528 1250 444990278 444990289
    0x1230f040e07020601082b05091f0807020d0201021e030c0f07060207210f0f051201080109020108010b0f04050d0305071a040b0603030708071e1a0402090c0403150902040b 75
    0x68400c000075030301038001000b00e1a41040000703802c1c00001d840304081e000003801d0014010031055a0008e0000202d201001c075184d00000030102c0000003110001e6004001002d80f1080d4142e0b0104014019030580e890001c1c014001c662460001e4a1448182000030301c1c0c4408a401c0608018458141041032403c99001840a8034400e400781c0001039a464a51400780c1002900c010071414915046810125083d004500100b08140e107050058000c0b103c4034044585100d0a001d803412500c0200020440d100305501c0300359058402c0c1c070341034016629082e12a800d40203030807440e44d001004201c00e0100d0708117121006040c1d4424140f0b141403a000781c1e11080800c10b0f0811062440c0c41c03500c01c010920074500c10702070300040c0a8028524118850320741b61003d2040c8003010f844503400304c0c60040740e000e00081c6000c00d55004180612021580d90704400c40c03c0c1d047d50282e1080c1c0311399001c2843c0c500e4920885040f25070050307207482e01195042e5560094268844160b80c05542c0d010741030265101c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 444992778 1250 444991528 444991531
    0xe0c0d02010c14250605030721240b0309060a0b18040609020a061b060e071706011401050f180d150605030f0c0a1e09060b0c0c01230f040e 61
    0x307051004501d2540002e00d44440b003c4e0b0100306203000d03003006050340040c00c03a5080926850200001008548680c1c01101000d10038441c5600e0b00b80c080b100b04985030311104c91803a0140854041c02d0307460002c40000c0c0000c2e1a4031586c1c3e0424808151541406d900c481d00414014050002c3c15420681e40e41102004640036110b03640c032a11000304614100c1a03540160400c1c3c00c0900003400e00c0c0d407400000c140e14440040009075640301040001804120040007080943e00085001c05141c08141d1681802e1040088480080800800710340c040c4003070b6260035100e05200c6080071481d04600c007100001301c1e962a0450b0b025040d500214604030b07191038400c190342201195151401c0185882e000e40c01c10120070300d400c2408060304a640e10034600c0204c03454503504c09084045120036040881e0740340c0c400c807209480d20900040038042d8401038103214030303880c1c00e9540d0301c5070382e60041d100d01c06562070340207000c040c03c040c3c00702c0140088044d02029600350f440c0713402d107030700c41d025030369034010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 444994028 1250 444992778 444992813
    0x111042114060f01060f080411060d02070c08030a08180616110f0c01020d020106420207150503040c03120e04090507050405011e03080307030f1b120e0c0d02010c 71
    0x819005001091b00030b01070742c1070201d951a0840c01454583c0f0340d850640d422501c5144034000005602c02d10001c55019500d649401800038010241c0c0d03030140310b81d26800f0030040d0022890140000c3c0d0140e02400719103840050a60280c2501da45a640c0807400f000351038000c038140a100002c08400160801500410601010050040303203003410000e454080e072110301a0442e0304081041c0541551040d2480031140a0800840078143c0d81c565506101490034110b4140b04400d4060b0035081d50024944088030032a54482d07024038451041250f9a00c022503014200c442904030800011341c00900c0152046c4403450200381510000c80002e0070b42d0702c16a01a04c1c07503400110300380101d1800e842164018044150401a980e221400e00e6000700c08510002d08218004400075900c14005c1d004140c00c1d00700198208078a08030407100c402008074000000c00050420480d12001d045948543c58504100c0350041c00007071051000c01c5602424510101e0401c00d013400c1c460f0004500c0f4003010080300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 444995278 1250 444994028 444994051
    0x7140f0a030801090b1c03030605030d03060302130506090f0a0e03070804090e030c0d03020c21030406052412030c0106080609100912081b0a050903011104211406 71
    0x200d032414018032001040e04080540c9141034080041c030fa03160000c42d120400c8802e10005814001c1c24180d009054a81c070054150080490480410354158041c00c11b0303034800c17680c102502081c0e2412200725142190407076006600800815036102c1955802c2e03510043c00b82c00841c42078590081d250840c1c0199408544040011509010340c140701e000d200000090703a8000c1d401c01d01400049507540c9400c100b03400038103500007071560035800244202c5082c202480b01c103120788520804a514036901c00c841c262900c80c50000841c07400c4545161024011a4400100408400e0641007000421168a00c42143e120420070705416030005e029903801031035400082c101501e00b000071203051078440382c1161100d901c0c3c00c040900081944080f24100c00e094580303a90302d0b42d204c4000300b100705071810110064140106001c010789500100400a90009034002d00511600d42450106400780b03010729010103000341c1c1001c23034203881c030071510401d24010741700205400d07050400241004e400707444081180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 444996528 1250 444995278 444995293
    0x301020a11100e06062407030c0201031a0906040c03020408250e01082a180a0b060405030a0f0206070c090501031101050a021c02030c12030105010e06160807140f 71
    0x401c040c02100c04500c4059020b10201c50300011043c0c4409005080500c00d03070003c00c0070644842003000c0b142c00700450031203c6d5a1004607080203000040001d004900003404c02e55a203c458204c3d421510172080040d01c1021540c44420400015003094007901081550030b01001484887c00c01c401400f85103800055015010081180250341d401600305c220394042c03400c010001c0100001e03246502000003100000103503044c610000b0a6603500d0142c0c0d51003200c01a06422179103058842e40d001c1c40c149001002a00747c40c0c8144402c6000c0d510550307500d904800790000200b036005072128101c6200401e486e01e0300003250384842640b0342030b8005044059841006004000400c00301001d07800090030703d2810028907480003036945e6407a8206410568170041030403541d5008000380d40074400d0b610181c0346501c0d00f140d51403659030424890b0074001080c901c914026420214206c17044840244038501410056480321840341d4049581101e00803505043c013401d8210900030241c1245a04014100c003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 444997778 1250 444996528 444996557
    0x10b0312070212060415020a0c0210030c02010e0d0c0b040c03020d06020a030606030e210d11090a050f0310200301140405060103020307020703030e030a06020406020f071a040e150301020a 82
    0x2400703501698148203500130401d00c804102d80721900d5956102c0041c004da503403041c02800b1101082503210007034008800429028000c0e8064101000c0343d020703039008000e041c0c1002516541c4981481c200c1021074010002800410820ba09181e440b602072a81001510381d0b03a404a40b07481c0b4140401c0d140da66000c0b0760030030010b03414020700c8001c188500e41842202800700c011034a90078400407486952080700c15001e40d019a002c1541c100c002800b60400c000c800424800e403e03580403c1c00144150f501d80b0000c00c0b40c5c03a180c0d20480724080050000c00e94200c040ca4503000074a1011020844d000c898000c004c06c0941d42c1c0019800f03001c01c0b036483c1030310214220030300003075581c01341c5a507044c1401072040199907580012030004482e050303d00140b4100d000b80100341055001c0501402c1c0da400010003003072071900007030040d402c460b40c602201c00c40e41e903a42c1411ba82824448500d50102010402044030020601145800c4000542105940c00d030b00000282241e202c10f0080021840c16801d070b40d00d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 444999028 1250 444997778 444997789
    0x304080a1103030103080409020d1e0c0809030a052505100b03060f0c03070507020f0d0b01030510060f05090c2206031103040c0e25020a170a0905060a02010b03120702 73
    0x204000081d00850a65066a44900c9903004c0c6019070b02e0102e0f800301c0c40c03050411442d00402c5441000d05440250390341c3c1500c201024089080802c004101c0340c41c040340060300c000044079840f243c20b07546c1600f4410045164440c191321121080b2201141000040210f0f6045c821400442d01c210400950000764409140c200303240181503410844ea200c1c10069028580c00807a50301103224a091640c0c0e40091001031402680151a2074020600010603c1001030602605060f00c0c003c10803190f480c0d4035801120309503407180c010820441e03448a01081107007010310f00c860300042141055810030350441c10104403481005880d80c0703032400c40e4108000c0940c05226090040c01c400e80b86514500c2e044e19911881c2503644940403484400400145c1901031070074042c9100d01d00c0c16000108020142c9009540d10103103c5e003600c03680506180c56814003810000c6541c205400d88407644440d2400c000c1140da6004010088255502d9075030b4101150742c28080060364040080b10644c880034203006201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 445000278 1250 444999028 444999047
    0xf0a060e0709050907090905090307050c12030d0b0d0f150c0e010e0907171005030c04090506040308040203070f121a040206160515091027061109060304080a 69
    0x110405804050103206903211040c0c005843c1c00b910102001c0d22040c40c2140d141d103c0b41e020154051a06c001e212481710040001c00403140103008451a070745100c2c040001080c09e80b16403203480d038020068a480c02d002604100100d003001405198074400c1c90f181c1c03400c07086604008803590300c00f0001c101e82034421413080328030b41a56442d00850140b4130100180a1030300e0100320500c103500220000340c44074400d8040701284414400c204141d420321900c411404000b47c01400d22a000311103044c0a00d042034801d0f0b40f81c003504070b4000c11040c0c5031070700c05071802140900103a8160103100b42c04100c00000c66060002406900c0c1007081e400d003030303082c0240344078010520b002185403c80b05010240c1d40d401c045c0e4851446484001581000030f1811a2500b440c3c134070740c0107400c0011010401a900f0102e81840034039221035081c448061103410880071507905103240500394031400101c0000c01c100e0b42c01024000300440d405850210074100251290300215800c8420041c0044c0d800e4441d42c0c8040100c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 445001528 1250 445000278 445000289
    0x1312060917030a0e061308090316060c050d2c012c090f01030302150a020409090f1416060509040603051e07080c030607030b13110301050a0f1d0702150f0a06 69
    0x8103014108841c1d28000446e4203000649000f60120b0259000e69042c800d2000c00740e1000b00300d805150b9a584050300801c44100180d5441c01026140d40b050350299002c4100f242c0000c407020b1b00c070a40c3c02038200341145526410380c10000c1c1034245c41c019500b038895005e0305071500150140460f002c40300700540301c40002d000303807803100090004100094000a443d100310001005450b007a69030401172000900403544444903007814511008180305803070150840d0790b40074640c040701400c2c080b00003641d200442060300400e02c4212000708100381c856806405107410041c0045a015a291111860186c03031040449d510b00305c5d065808680c2d00c1c200a803100504460b4058a80091002c002a032a503000038110002d00d0784680300d01c0b25640d50540c2c0c040300c040303614000300441e020752000c8101030b800034000e5a009501c07041b0b0111f40d05558070704040444500300c21407e55620500c110040e10a8090850300039440b40700500c1e00010300d80f00115102d8001094034001d40c2c506030005109070703074059011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 445002778 1250 445001528 445001533
    0x9030c0712020a0909030203071505060109080318150f030405250f0308030604060816050112090c051c0510050f06010c1a071814030c061312060917030a0e 68
    0x220700c01600d81046503c00c03241010000952115a4181039045119404004000819150407542c2958a50740002c4c0a4002a6a1001002e8543c0d4280760345e4070031442074500c0ca00c0003200207005071808040d074182070115050983e04255032880700d07039200e0f00180e8003294290060005a94428003008440d04490113003ea0200158074101e40c1c110b100540d2b000152901e0343c000009491a00c83d5001000184a85012210000f59126044800100038043c8500060741801c03c0c0518140c2030059150468025400b80941c900d4981005643d201645001042c01c0d14142d1005c0440c40500c4a6444074001801c00b03d01440c4c1028004010304004090506001c0d429444c140802c2480c1e51151506004145841e41c82c1c640040c20b480700c01c2d90301600d0401814080020445001040328105e40b103505a0484096030804020018540901800540e001040703410410040d42d410740d50a0142d40110760001c2c01d44260b803100c8800300c820552400380400e0000902100800d5403060404100c0242c01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 445004028 1250 445002778 445002809
    0x408060a02030f01031103011b021e030a02070605030a06092306180406091407140117061c080f0703050315100203090d14061e07050901020c10051209030c07 69
    0x1021600f404041c00301400040c206100c5035038503182544510035280001d04100b03007020b10b08000a5490580405402c1c01031808504250070072070020981e0007003101c0340c000d0401c1c503060103000c44864100900d80f0702620b495500009550801344900c51481442c18010113405452a10720041150043d0031107010344140d05550b40305440e0301d11441d800a9102001095164590600e0003500d10401c42c2d11246d405090300000e510701411110000c00f0754280c0325803440041a28480300c813080f0403201d2a411550315040e01c81d80442554011110510540c6c00c1c906091454036042d500760804a01240855000424441e22203082803000b41558000c0740c40c0404100c1c0300e0002502d030300514005a0144580d0082442000a800094041d020481c000c8490903c0c1c4864540702d80c0e40c1c1401801e00355011000072604581c030603c11119581c006070003d00303840e070084d800d010015002554410400205000001d401c020220503180030f520071000940d12001d2038040c842c2444107a900c10480c1805848 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 445005278 1250 445004028 445004041
    0x40602120c0a0b06041d010204090b0402132115050601030b0d0c0504022d0d0b0d03020309061e070501060801060f0e160c120206150f0102031801120903050408060a0203 74
    0x2402c0d400b141c3d004001003207a46070318000c9400b13007500e124a440e0101c0c0600f5100c01c00e80f0158098012140c04100c1031000c02c4a031011700c0200c0c891104454880c1c120008240710764011082d454040b0b6044482144004540d07407103442d115925400c400921b15262020b02800d50b915001e400d50b80f50044a401880520071350703801800065038490356004030740108950384224114a0000080c0c0559241104081c540401c400d0715684240710b1070034050300d04142d50099090020403018526490b030021440e101400d02000515002000d90020f4941a44a0b00700349a1181016143c00c48c0304800108100f0300700750041e803d68840384c21115440d044050200403103a00c610030701c0e8002401c0c0c01300440455541004440c424000c50028003203840110440040d240e001403184c0c0b045048400140e0740507035040130400611078080260b40113a1052128a04894211140d401d4880050400240105002440f001510b98207101076001c100086020444020300307002542c4c0c8125052f000318654940308 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 445006528 1250 445005278 445005283
    0xc04420603020a0f1d1002150a02090105070b060d060e0a140c03030403021c06090f060b0102070e07032c07030303050c0c2e050f01060e042705031201030503040602120c 74
    0x5503400d402c100c0e4440c3e0035686030b042205005c03151038014002c001c1c1400d0042019648103106400b00392a82031a10028407260110700c02d4075907513103059441500d011a03588400c41003080c0940110307800340c00c05031860b0016107544900809103e022000d0800308000307051140381c40300d02c3d01035003459811419408480340d401204890540c0d03411070f00140348103500e0b0056036135401c0703140d0300610b800d10f80344d44001440b500d1004c05021601c1140140041d20300b5400480e1111034500c1407003008900c01010610650103904643c00c03480c042c50405038080c4a2107007840e8141044120511941c009110900c03e16500d405030719440a0075003455440d2406468071550388404008254500c5155000c002c48a40c202c0350205a240603450030510030343c1081d04103110403100a1180a0126603141c4100e0f20900701401442400c540030746540d045440360407102c0700e54014030001159a40010000036000001c94032000d070185010b00d00454441c2e0400300c1c0079181281d0f0240382c0c014088103100c0c0781b02c0b07580300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 445007778 1250 445006528 445006547
    0x14010f08010510034502060a030e0a021011070801050606030c07140703150c2c06090411030406060b071214070519170c0c04420603020a 60
    0x80c0c3d0560450790010390304900a151903807a0050154159030001d01d02c0c1e9042c00703440e11548455079030300c46a07280350802510082c00d07008002d420410078032410340c02d40c0c02035101001d000341c008280d58850b215540080c003c0240199850045000e002c42c65251380c0040224801600c5540000c02060070b0031400211140001081d40080c1400021240c0412814035000f1070071103981c038100c0c0c2005484e883c0c02107600d15082c580340700300c614001079400202e10603030108203042440f01140d4010844210340740d09403012000750a420090400c90107419464a1240d00d02c0040381c44060741e200e003400d143c1042903c1e203d5103c241c441d40248041e001042e1200aa003076803440c40e080210001e80701421112030742c020040080c10700e009040c0c8000003802400e02c60010503100f000b081081110098600000e0302400f1401c182d40e6000d01c0406241d070a059009039207000c01c00c0d9049034510a4503403488042160380d1204941003c010f00d203018028010a5003001401540c1419828482c022070000d10804a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 445009028 1250 445007778 445007789
    0x11527140d020a140103021207020c1503010522151206050f040206030a0b04090210050a0909020406020309060c0c040e0a0b0a09030f0806241b0114010b0f19080114010f0801 76
    0x140c0e0360703803c4d0135a0300035411107050b070840c2e9419030313484e00e805c0502a44686146480702d0041b0b1a4880c01d01200065504480c180c540040c0110308201e4007050003140c0406a040b07115400d40d0790b440c00342400022614031402814074042d900405c040701c0c5010000d484000e031003c9082e11100f002e00c00165203c0702500e6001c40c209500040040d0201c000a02405010740d0107074102c00820b1100b40740aa11200802030704205440d100c1000f81e80b800d100049210741e204020058205200c161201d2070280d0041c00302d102c0800450354418005400582250041280305003941c0c4009415010021402c403c65403217403c501c020007140380140c501502013071001d184001002417060000b2442e42d50030070002c01450100580030342d0b00c62001e0102d0156841440d8001c42e0f440340070075020506005000b041a480602c3c2d000f400e40780d1030320320300e8902d03a00480000303030340201c00b40400751000b0406103011a20303c007640d8422886500d03000300c800550f20041301f61410070107400c01ea1045180c1180d1035904480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 445010278 1250 445009028 445009049
    0xc09060f07151d0a080405300313210609030516030e011b02100e01050c010c050406171311010c0b04050105040c060c030206011527140d020a 62
    0x103004a65162148610440205081103144640031400040e900c030501d00c8a80a114000d00d030702c85000c1c01d43d82d105140340100743c11000c1000b0b0206040801c4080c1c081092842c580020341030f6401e03507a5292656003401c4c0c54944c00454110344058262440d2801040e00d030480342c0081e580e000e0000899030f581c0030098101903d443e1b80f24100361040044038601d0f401c084c01d0700203c1c51246001480076405441403030008050520f15030207040c0603190303014a140c0c024401e84100c05007110a80e07542900d000c465060040900100c0c225440030b00641c40740c20829552a076445040c56000741c485500d51202038503040c07121040003000d008440e00c40c00c07465008400d031856142d21000480d16551030480c001c029900c64000c0c401040415001706010345c1c480c0d0f0320f1810958840034201d4000300b5070140a00140d1001e00100407154a400350b035903582d052450700b68920111400c1c044240c2d41009607a000764105007104108042c42d511542d49002c0c01200c0e1020600481c0c0c0004082c4201402440e0894 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 445011528 1250 445010278 445010287
    0x1060e0d061d061f1412010f0504020306090111030a0e1204241b0f081303060b03060f070903030c0c1d070305090304080c13060503061815041a0a0603050102030c04080f060c0906 78
    0x9a86e0000c901d10b0985c00d440c000d07c5400c1414651102918064400f2030092140328086850544180600c030a00384280071000d00f5903403104402005000702c0400b00c50070b40100c00043c2401c0000c04010700c013070040c01d000f41854401c0318810700b4003400d520b41c200342049950201c0741007a4103a0780502070301d29041403040911042e01d00300740c80940308406031400201050341300001044440d8000f4444481e08506480710740c1d139003002e180285001190940700142d0604000d100090150703280441d003500031a69003a00544905a040e03072068010090208085184100300702550b250083c258011907010185040078544145903648994102000b4410210340c41c100380107116a03030054000304401021140c00e81000140c4010084c1044000b80d500d00484c146514807260300340350a0b00566100c000311009800c0d4940c40a02100003070100c445a0342c44010000c046042400510b00608100a02a07500c5240251151500d07a0780f0401a0054102c601041900319101041d00c02101081d14680c1d540c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 445012778 1250 445011528 445011569
    0x30f070225120c0b03011203020c0d03140f0c0102070f1b180b1c290f0703020c0102070f050c0307080604050309040905070906091a0d0b01060e0d061d061f 68
    0x900144d004a800c04501000004403034910320303002c80d400c5000703809440090b05900107110080e55500c40240c081a50390040030480300110b0002c02c030003400c40d10203900700100305000d0b5003a0307171008005940c80d860108503282441980c0111100845185c01c940048510700003a01c0c0015058040d400030040d520482d4114549511101642c0c400c0d8000c00d100003010546808e0701104001034804070100c1c0175440440080600d8401c05024900c3d40102410300da40d102400c8000c0d40c4203d04405040d5002e200e02c00008000f980e02d1041984224058110400c080c001e0518014042c3e003c4038480d0302c60400c0c040801c40100850311658004d85012859951500780b0602d820000e40c451b1006501d0010f002071805955404400403503440c401ca0007070030401c0b00030001c04541d100300c0606866480c0d801000564065045851901d802826448080c5160b0312900100d404a2201914100103903820310300c030807010b01000e0b074082c0c0030b01200d40001104100310300c0408014090511900b1507030210180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 445014028 1250 445012778 445012793
    0xb06040507140c030a030b0111210f0706143102010c14011406011d0d060b060a1d040204120f02060f0c010902040609020910031808030f07022512 64
    0x54141049516980da4494801c210384d99520848080000900e01070f20740340d681d8400e514042c0c0342205400103110100359503941055032a001d09480c174201200b0031900c005107220782c0182c41c90360f004641c0011260300c800f1720081c40380c0004091440c400384840052200c4c0105000016558200c00700f20106a2500c1c40188c0d07003101d210070081c02034031008201600d071031015040200e0148440102d0845900c4480054444030b400e8946203904400f01d8003000e005041c001c6c01e010003180540c0012404407614bd011918940c401803c0c0700014044034400000400d9034400328059400a8404505d007501e0a0b454103a00c6940b214000c2c0b54106400c141e80565545030180c038020b14059006941e2801c2100c1e615000300340e4aa8101e001d10306012001400d9041071007074500d040300240141c49400d015180481c0102000141424400d5a1098980210b054800518800c031400b404503c0b40c2e04101001030301d08810700707070194108c4440c0d212180322030300324680400c00c0742c40c0f80c6507008982d15280340014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 445015278 1250 445014028 445014047
    0xc0a050a090b030c1807110309010815011e0302041e0e0606030702010209030114040b0a0e0304090f090c060503060a1509051c05010c200c030712080d02040609030c05040203040b06040507 82
    0x198000e100d10080072035221302082d8680a41c65a45500301f0354103c280c0d07010348901036070407003a01261260000651003101d102407034a1501052400140040e42140a10048041e000c0038100107a8017040a0008001070615960400402c140070600d007898040700c0449550010581c81c041c50011010402c114000d4050b03074640da00c02402402421000f0041c6c443c40b0004440c1500e080c1c00305400304008200d24440c00c003d5140b0744010714506400c1030015005008800600500a0350320141800840c00c0300380c1c004003030702c4076030f80e116502c0c181070382080460003007a00960780c210701e1a03c44c2011150044603100850f44151000841030565044402c07140e103848102400950802c414800420f5001542d03802104c0c480b0903d6202c1c040c41451f8581d80c00c00d64400f183c06a008130410701c18039002c0f40708070044502c10300c0e0043c81c011207410640e05a8205030301100204024040600800040703011400c040c0a0640e411425890a07844180d071000002c0c0c25140036503a100040740041e8880e81c00e20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 445016528 1250 445015278 445015303
    0x14070b0f040303060603020c0703110d050a2109060e0907050c01051302040c0c032a080a0809070b09090f220809040b0418030503090c0409030f020c0a050a090b03 71
    0x504145060540303508600030803501180080c1c07070050301040d482d01a100b03032221070107840021300401c0e04565410107891110b140d01a03204801c51a6100010020400701002c80d00c5400405540301045030054800c0310a096024144107240500703201155100315145000d20080703a4158964450070400c0e0f0302da105280e1000c0d0740d5424581001102d621003039060007800d1081d41d0401050f07c550000b280c03035802041000f400243e44070745e824000340501c0428076800d05006c04010300c0f5a402d6443c56800d900c80004070001c26000c500b009010501403040800511100000a01d82003200d800120304d6500185081903008401000c10380c0003a0124030b4055492080c200110180400d06003400f00da000078424502c40d509048200c2421300f0300740a03c4400c000c00996558048a16942c2038400d0b810040000010b40700f041c0916503556124000e04800c40e000b5100c0c00e00c4060101700003810103140f540362500032a03103040100300b9034490f481004100c901c001d200181e02c80d00c40300044e04200304032001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 445017778 1250 445016528 445016543
    0xd0302030d0f110705030913050121050312091c030507050910030b0909030403060b0a030f24110d0e010e0304180e010c271d040614190b0603090d1407 66
    0x21382003010010003407600300802c0340c0c880144c801c1ca445c0c002c00c0c1e07482400782c13212035421841c0c4141507500d086031044c88140700c1c40680b400c00165106210984004540046150740146040104c0c83ca0140c204201c014941c03500780036071310301a03001600c644582c00c0c2ea24011356010302d040c420b851080d84003a600c10001400c018060420b0480280e80b9009400160703045441c0c6600124140f6081d0540030840c2d52200d0000c0c8207100755203030745041d4407254108d200e95500b4402586060f44091181d0b00039401000e00241c1c840040902180440314045210400e0745e15050030301005e100e00009650484009106182c600050000d081c800303040342c046200300c15800c000c1908101500103c180755030301404441c91043c0c000e04a04041d4054945c495500d1016450004c0310920480301ca0081d880b50203624046409250104038401d11002104c2034940b030b0071241068510342e1154069140724607030442e00c00e4250300b09803d00b00c1e110403401520905019284000c801c40d41c2400c0141c850140c1c10a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 445019028 1250 445017778 445017787
    0x1518010501030309080d0e0f060f1c050711150114060d05010803031f0605030403050904090807051b010309030e041d03070501060510030504030c200d050114060d0302030d0f11 77
    0x8010b440a16a40207a00260164031908620244195082c7c084c00200808040c1c0396500d05040c000c40f6807040111180300741c1c0c1046030b45210104200b031500000c111040c002090300d44007000602120b01205414165009104c8075140e0224401c495410740d009203800d840c146100d8030002d40d052040c0c10082c41480e0810380002440140440074520a5448030300c1e00d2100301c1490070441c00c00c4201d00034200403a02c28000300300401c2c40b4001800030300001600000c2d1100158441c00c180390030460b000c83d11075124020380001185696031181001800b03003401d200211295401610a1681552680c09030707030b0301c0100300a2144914480c000840540742941d0b5180500e0130228080e16071406400e010b07400c0660b00d0030949100384901c511903030305030360745c00c1c401c203170980e44c55070300d203015090010080a40845040a90350b542c001c0010080c41000001448040c00980318041c5000602c024410320040b003100000c6038010045444120b803481c80040e2506104112000405001921403a00b040c08034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 445020278 1250 445019028 445019033
    0x30c021906090516061209031701030506180609120f040306060303110610050f0d1515031a01050d032007060f030e0703111e0d05160e0405151801050103 67
    0x42c044414640180d040e100c40d03c066400ea1102e031401c1748501000105400103800328461241d1121054030b120389007011064800c20442c054046080c1c00c10f0300c1c607070000380600010391000d143c0030480c102c20001a0444d403401c40100c0752544a5020210b194180c001100780d03001c1590021600038551050081210b103840382030007051115200c4000d0344030700c21800401c030400140300c1d07001c08503a401040c00301844035880511600f4000c080044070108904952030402c0315441c01101d03114090102c40e01186869420b22420301c003a81d0f03080308040d400c460011b0000761103c2d0300400a031905401d046660400e00650742121020b10b42d103600050007036038030210b8940d91000c0314000d60318642d40c0c14000b1003100c40800761121a6440001d00180321140110820b0505c5859030031a540b9900c0d501c03040c0c01d9107001007000c3c5046c04800701c0e855003195074107146003042103804202a19009085903210302d00b80e540c2c0c0741d80381c680d4003205129410070800a00d82480c0351401c0900c01c0340c108020700041d40d591 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 445021528 1250 445020278 445020281
    0xb0903030610080f1306140f060a1e05010c1b0803071424100b071203240909060207140f0d02030a050415020102160f170f0901030c021906 61
    0x96581920600384041020700b554481c1c0c802e58010450780c920701e4180e4849000184070003443c00740c1212445e86a59110580900400c030310761280b00f01c9150680f0070301d030803400c00c11180441d4000f000306c40002240441108030b1100468203403070081c205a41040440c0c20110480c403040015000107c081980104a01c040400a4000180301d100009801c60014009a44441c039251039404003040b0615a54100b4040d624000c1c2c1060383e000404540c1c079141d00c21000240d100030003e6850200070140d080507160300d8442c4c07040311a040080d80016052542e08141c2000192050514980e1503010314030500501e80d044483c1c880c0d01c15503c80c003298494100589512000c800103071305018600401c2c15250010080320080e60315551500d06d070030f091640600d014aa0100c09004540d82804506880c0d0140c8a04030803070760180c00c40340a128000d03e804120031204490891450009004990030080180184d450014007400c002c00c8a41404400b01d151020000c08908511031101d038039021320185 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 445022778 1250 445021528 445021531
    0x605060f070618050309010e0f100203071203110301090f0b04050411031e150a06080d05070b06010207152304090605211c020307020310021b07300b090303 68
    0x5000c041c403410789051000081c01c050f04102070b25581040000e60607541c81641d03da2107540c0014565440c5c2510040440d46042201d0443c2d4050f0380300280c9c142c02c2c4155002c00c0c104010442c50280f06412455031a604a40018440c0c441ca90b502d64145c3c0c140d4034195000100102c00140042049103481d040c00d0200c51043d2000c0390080c05195000c614080e0708a070405081d0340000c4c01401ca0300030214044513000401030200350308980d50318010400c0041171184101401c850368400d41c8a1110742441c041030840a0a80c0b415544005003c102e4501345000c800700400181c14040408d440c0d4001c4460605046211001c0d03100d800100031038034100e20380c4800203440c0c0544803603641004e035104141c00700c4400c560021140c0d00610780381c00b03041a032070703503c201c0001c861044e6410114658080780c40c00f402040310b1003205401092040f0303c0c140e81d00625100b41c18000044c420189082d0130010181d10500301003440c1c11900900101d81e100200040c0d5250b948000001800e181020340191250030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 445024028 1250 445022778 445022783
    0x5090a02270c0d1a032a0a26070608010303111501031214030606071b09050a02030103021e0a060e0102030f16051e1209180f0708011a0409050603010605060f07 70
    0x160001501045001c4411126a040b005e00102401c036102003140c0c012000340102140885208942c1865585400040e00300500754603807049855508541d020484050f440c0c000030b074550222000b00841d80d40b103402030381140d03014109105070700c5c48028000d040c40350b43c1001c5503001030b0740030002041056001540c4490036140d034400c411160072182c3d0f44c0091105883c00e5a010310113002400100398207a15040ca00032814201d094060398880008064030720845031210004c1c1c0c00300040055013007010001034604220016030040c1140c20000880030b40d51802209c00b0400c1e1103038050703c103900820444504018020003c0c0c0c40e407001c56480026919000c00881d441e0041c2081003140c00c680801d0390803500b01e40c0340500401c04203042c1218081d0804004c40d40e0121a01d030910444106910b001030250840e01d060012620f84000b028280f010b043c0d010509d507003070008440820000420a85040c0d81c04103502140326115103000a014003d42c1e003109510007800600400c3c0340b40002d000b03014035031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 445025278 1250 445024028 445024031
    0x11090f090f1219020c09071119150f06050607060615050702010909021606050103081809130f050a240c0509062a0d2105090a02270c0d 59
    0x1030340000c14680318000d40c0c20369603180c0003d101941c48051030b065501860b040d580b04654039a92400001242200306131002804500c07611008001518140052280c1e0f203101e6080541d01c100590314141210b00031400459002c1d60344102801401c0e00e900b02500901000388225142e1801d400d000008200900c5080180034000f41c021031030b82d0003101600ca01d40d40503116009084d20300060040690f02c00d034000000442807080b52070026025119442c0a0360282420391b40302c10302c06034820b140000e00c8450074450b0f07440408100076002a65084010a940311041d1402d00352a49081840c1901d21700c001444202040e00c0f0440c0f0b04500820b031008004261400d0042c0d00200c2d10076650b0f0300c64148465045082040b1581b40e20034041d54000c0101c2d0301c05c40030a51200140740013400c11080a0040001800103008864512080e019140412404903403c2001d800c08000c500c0c0d8034151000003d008640c1580440600c20102900e41c50015152820400b646050741c0b42001d00e9204040080303c49 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 445026528 1250 445025278 445025293
    0x10209120c010816050d0615080901110d0e07080d0f02160503061b1b0c04200703081305070801150e0f0601050906040f140406050d08031311090f09 65
    0x103000050150490001a100d510003601c0715a5284440c00d402c448040a0100c10002c84a4862882c81200000d04000f8000d64410441c81d400034221400504000e0701c5038144150200000005421550342c5d41015000080c4408407000d40d5042c1407581d4046502405002c0c1150085034010b401c0c855030700c4284e825105040744403508122010b9650107091b030107a100303000007110801010582642c81c07912003a200d041000209040380da0003084c8402101c940c2102d058941181458002d03001a042d510142c43d009501c058145135845c0034180000e402c01c286100881c804c40a1340503500d41d065040b000b0f85103000c2c0c035540854040c24003181c04004c41e42000c200080d40c00c460824081c00b400000d9540615600ca00300119002d801032240b0340d9001b4010000000e1011041e01c1c1030005090480543d8036010b5202c080100300d800c60f40c0500c0c0a1480c44030040001500c81d4100eaa200b07080c07440032003ea040342e04005100c8428992599006030104050000c60440780c03000f2481107004104444c0035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 445027778 1250 445026528 445026559
    0xf06090e010b1219060e06040f0c0f050d0f03050f0403050706140a1e0e060703030506040f090203030a1d09040308040b090f070b030912041203020c0a060905210708010209 75
    0x100c000d40c3c02d020f100b41c1c003c1e10b10551345200d0002c00b40b40d840d0260801044004c10f0f40500381c1000d070140c40403280e02581c030640c1c104002c003509440c40117000840300351b0003e42ca0304010507820285c190004118124200c03140b0105405071781521900820134092903207403038807840c00c190340d800d503070007100d004ca00130300c1111008810a0048482c0c041c1c03640d071082c59038000c540c80290f1907588040078005000d0607030603801240c0c80d800d01810465010f9034020070141003480a00044a580ca04201002c0c1c1c00e11460002684000045417403040b55403420b90760070728400056405061062900d168404409414081415401160340e030281c0e00172001c040847c8c5814400607a610000c4452041981166208000c0103c410300610707441103130a025030b0450340813003510fa4030aa200d42c1050105900b01803040081c55410002d0300b01e680b1090341c0904e80b682c18082c014103044014414240300303070000150b910f0407040c94000d24080c0400c4504441280e601c40600c14040e41040520300d020340c4c00b40c0e00200e003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 445029028 1250 445027778 445027789
    0x2032406040609050415090e01200c07030b090109080a080f070e03101109030610080f0d12021b010e1f180201080c130b0301050406081f020d0f06090e010b 68
    0x2160410303110380440b03030728144c180405440d2100c1000d0300c4154101000800d031500e80140340142080d4800007035240b060400484240c54024400b80d6244400d102e10640da120005440c0700f0360380c0140f041d8003550b90300c084d00c03070240c00c24502c010701d41c107070128100e40310315040b814050041080759100813040c3e4551208880e44014101281d9055203c01440541003600d5402552039980c4150303d1841c20104c0030200c0e1601c0e506450f400404200003104100c4141c081c0b03c041c0702c010b610300180c0481865000f005145211224599096a07400201c04a10703d141180b1075403100f081c40d000f440030030f03031030f0f503c0d036449055800542081ca40c034140f400d0b10750081441614030f0700048183d084000340303681c7c0044401d01c00c003c3c6450480745042140d03114244030310110000400c1c1100d0b41e15036030341c100424070041d01d250394420181079212050540325400006031462699085074001600e810806000c6e2000c8c241c40200d0040c49450410081000c0d2503a802c03100040b2000c1c0c00070300041000205010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 445030278 1250 445029028 445029037
    0x6080f0702190803060301090609051006080604030503010e060607121809111207090806010e0a0f06030b040b060a171605010c02010206040308060303040306020c16060207081f0e0102032406 83
    0x8a8400b0301040c1c0ca400038552502540d00044041e000052505d03841d640c00c02194014041980d8070f5008904c07a030b848400341d0003440042d06550f0050510741c101940d0140280c0418090380926030107600004401c1e88851058920107500050b00c59000c1c24400f00240c203090380c40700345120003034104c2000b00312514030307014226001048400f141e00d042c138100c10b145c805401c0900140100880510002214141000024003800802040d80c1d55810004240d600311035040308a20101410304004002003111a000d06500c590480340d0710000f6603c00001480202c41500150204680c1307500c100c0204000085508441030b6020b0110b9206071640010742d14042c0140c070007401039211703800082c00248108982a00a4000380407241071980382e40c0c034901030f81c12000c1100096809014101400059200f0242c010b02a60001c0c0c4031844c00c0c1003020f504d80540d03041e160a6025481c0400e9014002d560112414a00d0a030085407030342008140140341010000f11701c520021509100e8800745012011103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 445031528 1250 445030278 445030303
    0x60702030417070b041706011202090a090222090b0f160f0903060c030b2106010909050304050a030f0c06031401090905010b03060109021c05160e03070f06080f0702 72
    0x2181071074544030841055040045001c400350281d40400661003003920040c1c00a480640011060410000e8249183c40c505038400c420080729140418007584450b2103060b045030300c4440104021a260002c00d4500fa0420703003601e20340c1caa04481207407100d4964007000080d8814100699542c44422404da10044183c1d035240c0c0441c0d1303d04440c014140202c85000d48400d00d410320b5052940e03651a050112062415208027080d110b201c1032045280c59481607490280703030003a045004003203060540d91000140a144041640d408809062100c10010f0720000c5c1030060901d4050f03a10b910f4000c030107030040d04040f1105844a00d0200d0214001d00840d002400f441903201c44d260b1800305004e02a01c00380750141d07080e56854001c041c0c540ca044c0320031400f038001c140e009681c1d801c0c0700000c4007409840c103180c0008141b4100a00c140002c164104090940070762420900c0410030000003802c1005640c0711000903007403107000080070f81e000800e69119414901c0710750419904c41c03000340e8440c0420050b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 445032778 1250 445031528 445031533
    0x1020c031606030902030a08040f0e06010c03091e08030d061a041202220e0d0207052b0212070311030c0a03110d0c12080903240a020d092012060702 65
    0x184002c502c03d40c4a0b41e1498002000c585900d88180c44640013a80560000300f020701686105100c41d042400800790001c0003031800c082800b1580d14010908040d40c02403070003420b946c1c00c8094041c103606440c0c40c00303040c0d9482901c1d500c02040166100410181c40740d030305040c1114502e0b0659048040564040303580140005855000c02d6007008100700c443c049600c0c81c003510030a070003111480744c0f040a03422203e41d401010100e007010400791a0007180c0d401a8816080030b540d4118410034150180107410b40c00e10320740500e5041788000790010f0408070550040c0d2140e0a400401e02c4011060341400c40400c1d0240d401c126090002e1240148070350101401d613001402c0c0ca00003d0400c4e0388085405409460301009445c0c0b506051400301010b12415103000001080c52141c80c03505000c54944842440800800c21285580403042c1e41401055814415808582000c90441c0d642000002035404100e048002c2c094015084400070040320103801005540600c1400c240c0020720300e4001c0d09103400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 445034028 1250 445032778 445032823
    0x5090103120e0319050d14040f05120a2406120b07050901030e01150305010518061b0702091e06031b0d0507030b010602010203160309030e0f0105210601020c03 70
    0x20151541041a80b402d50107200701c02d400d41800400b4608000344030700c22000f40c03980c0403101c0300c0100083c0d5a61200b210b140b2081008009001e405540c2c0790441e282a58580300e859503604c0c4090070301030084c0004c1c181c48485160354011111603000305025143d0310004000315074840441c0000c003c3c4070000104070070a01130114413018050005030405510514000c1741d91800225590309440c1084e54030f82254840d15000d00800c0020b02803280d014050004881000304410300c010399a102c0900003a60000d8014614001d0b08000d004640e1b00701d0700035240316814140003982d00d400c80d000130080c040c049502000702c1c07858503001c12454403840041810b07806502d03a100c100041d80201c00c400b110248a03021000000801e02c9103070b0380c000e003c2a00010303282d00d071060b90010384800f40c1c581c80702018034189500700001e270800038502c0c42c40030589405103c07005842c0143c540740304220301e12400410728010142c0108050403107504c101420b80c01e48081400420506903aa088010f0f112120080b460 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 445035278 1250 445034028 445034063
    0x31c02030d2d1e020702190801050601030b241e04081f021603030f0209031b0103050702120301060f120f0b0102010b0604120605071b0f05070e0721150b040302040605090103 76
    0x402600d171031800140b0004200c1600b0310f910b801910294442e0519075103e00402c042d940c2c061152800b400d106030350180009500e406028a0b0700c590502c0011550b001044900f5004802c4c41d4000030007108154069a4503251116680e540c0c07141f01d4400c0d401c0002001c4a043c3c0c6949000f51240d1407440c0c0307000c3d10170080e0780d079058001e80010b0004c4209141e00340a51640750b0f030704118203c8160f01c103a0900110309035900005081d100002c03e0b01d819584894500070084801d401100c0c11103101d8500050401c243c0002100c86841074a41000e1250921804c20510083ca501500f1519002d030020403e10301e00e00144416070013540300307038194010001c00301c40c04140c05130040d95210409140418903c7c1c0b06c1703001e86012070700c82074050381c404035410340803020480100084809450000424591843c0401008042c0c0d26008134500290111a008a807c1e03201a00011a480403012402804580710400c07400d0503007280c481644201d0820400103118141075000c00c3c1030b40d80158038030031214002c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 445036528 1250 445035278 445035281
    0x1806052106040221060a05040501060c03030207150504051c090b0a031104030b10080708030322170d02120c030103031b1a010e07020d030b031c02030d2d1e 68
    0x1007405030426020415040d9116540000441c2249240295212402c203081400302044031a002071303018910382030040c461590000f6016001c0c40d410f25000d40d80f1000d41c07500c044401d941846982e44d80d81450140002c004000c207060051100e003211007407881c2841d85040311011907911440420060803c2481140c1c1d100703030003034121251440ca05a1500740d480c0e5407110000c404450341c0d0030b000c0030300e001840b4110061101a004150000095046082c9072148014110949042c540e82c440f03080d00d0340c0d040264001c40c103010b031002556250b4960804400640103548485a4015400c11107000100340400079001d0740c3c1030340d4156540c5410404985440c03500c04d03000c1c1c08103503060310b10408000e02c03034520900c4180c060014060140c403241000100649050007501c103000906040100c00e0030740d5180020000c0305a0074002c40710541c107407072007000c2c2e045101e259038a00b0000d08200340841d041003154014032201d800704801d029182d2102210034125445200e12610301003c410002900480300d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 445037778 1250 445036528 445036531
    0x1209180b150a020f070b0403140a050c010e0f100806012c150d0903050a1b030c02060904061a21101a0903011802090a02070f06020309010b090718060521 67
    0x82e401120700796154031111074500115135005030589000040d09104000d010b02064803030ba030782040181081d4100340c0c2c40503161003580c1b41e002c1c100040010114150b5a6400141d006608080c0c208141380482000c000d1907410100d0300313580491b03210058240c481d0100200c1c510f162a040d450450403415450801c020360702c458514101c030745000d104078262030300684500c3e000796202c1d88a095952244d680050681c564060f030342110003080b400320002298104082e0440c0035811201550340c5e00048000800909054008290654002e0317440800010603900504c2c0880d0090b46003892071100c403102030b48500b0122000600079140a008200404020712500c018030302d81e8155609200c03125000c2400c45048010300f0030120b840740e20881c158248410000d80010160b0001d520b401803070f45a495400c0450300c0c000b407040d54000006007240c0c2c0e00b0b620003a02d0742001020002c440c202054000d00140404c0d200c410b1400d603140e0001078041c024030490b58170f04642c01d6205070401d841d40c0e5000b1101d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 445039028 1250 445037778 445037797
    0x120c0a0309020a0e0f0c043f060b0a05030706020319091508041106031315021210060e0102030306180402030f0313141c0b0c071209180b15 61
    0x2101c1000303038016541c64000001400b030360340f0060241d00d400c0300041081800a851245643da042105210000d003107108219011040310b00d5041c0660901101840115640ba034000c44000c01c90fa8481000680d810005807410101c60210703910f922a400c054842045120b90f0015900811502000035440301c0114400c0e8614200503100700d0782e59502c031b102c000e204010340b000100e07101e0401c010011702c00c520990285050302d0722411443e00c0c2d00780c00c5802864030000360203e0003041d0b081404071842e4044130280341c0c20309850755490801905400e01c0c1c102c14000d200c0802e03880303240283d082d4400002e6a10442c0006c3c10001800170321071070718009802c0a4826a054041c0889006c2c454504000510782880300742e52402e1087e103402141c410007a0003200a601c00c001500c00c41007614180d40c0c6613a0fa154100040000c2e6131900d10f1542c2052144c01d0004011a8090502e1104250015103001c21200705017034a0389900602c5000100319124030303d0b4039a0000012107010152812403011703102d001c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 445040278 1250 445039028 445039031
    0xf01060602061f0902070605250918021b030a0f020606060405060903190b310602030601050d1b120b030a0b090a080403200a08121c0c0c06060803120c0a03 68
    0x20f4032982d5030700503070780410303030544847e51034100b4400c2c212208400c03d00c0c02100c1e1900004030391660380b0700404000c0d01d0710030303507954640c0341c0b030301c520101280c5c0d0440d4408a100c05188240901740440e0030340300e80200802e8000305900f40340c60403c135400405c00600c04d03c0028900752406042904001264204c2c841d07040d003601c2012440080999649800481e050041c0d200d41c400d031400b00d00a6441080da0343c00c46004c007030702402c8283d02c0c4590348070030359445038031540150710303075403100c0040f102e0380203e5005500d054241587c2c0482d090072100c152500540e2507840c0e1001114009818081d5803901041036056401034103881c5c00b050b403421009410200f854217541281c403031038447ca9080e411039001034a10246480300c2144800a480341c000405200703139400d5001a00c0c0c08011b0b61a450f505a91002d2404001600c81f000c244901c904000495502000c004032800550001c200000c02d0008903112840d050010074201e600205803181c49120741150710203542c1c5d40b096031507982c100240e01020706 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 445041528 1250 445040278 445040341
    0xc0302040b121602010b010e0d06180609030e0904032001021303080c010c0f0221070c090b010311040f05130e0f0334020d05070807170f0106060206 65
    0x74880403005244107400c40344845401c2c00c1c5120104000c5190369002819a07141c00000b42840c1d0700048205012007085070320b06220344a605200e0302600c9110383d459143e02c0a8035000d400c200b9542c2c0300c09400c1d4001da8074030710115080b0003840241c09080e2400f4012480901040130a000c020310000c8103000210000750618089414012180d126500111800700010600386030405c070901c1202134a0190b440c2030110b103907400d90041d403118405075016501960800504450502040485005036882282c048280c0c0d50365800c4401001010302950003e420304040030f10010314402078400750380c250580140d40324901000c200c241d4102c003006c400455111906008184814050710103854080005155508400701da880c401010b403800c1207640a004881c0b554001007032040001050b98143c81011030382c00700f410600d01c2d0100c583d014411602c00c1410104004200c8030209003000072000864034012060718041d802e82e070f19030044500503440240040c00c414801145a5485008016030700c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 445042778 1250 445041528 445041539
    0x60a03060b040b041806061434110a060f110703050a05060105150310030f02040b120f07050103050103080306041e02070503070c08060603100e010e3c0304090c030204 73
    0x40d4102c0d034080c1c41c00501c04a010080d001155401c0501105600c00800c21941080c00140c4002ca0740b40c418507001c000490340500c0c28503e600c6c21300344040707200e90070110621031520052400324001d40032501c16001d40c0c60605607051411068081e81c0c802d1302c52190030740b203041003107a84108010782c4640d14420500b001000c59014041e5000c00c501034005092558100010301c603c2d0020031106e035204807010000c002140d6041d00c40c0070309507540032119807010986400000d028006d8454081d40c442d101c5030a010400f100000c0d1402d040c040340c82501c60f00381d0b42e80c1c010360403128244009040f00c40c08000145c128540f5a0080611140950010b240030780b010551404030f03004600210340c0780d400060b040c0705110707481030424010103200000303040c40d10b000e00110f42c42d0543c0e2410109142d89680d1910208002174100320b070341552100403a07003130000c200c440100a0109442c3c44600f00403002c101e000d085c541d0300c1c00303c15600d2032000031840e1628080d4110f00400000015404143e42400b02280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 445044028 1250 445042778 445042799
    0x7050a06022a100b01090311061317100e01020703080612030403050714030c1516020a09150513051b0703050f0d02190806010c0308150a030f05010507031a060a0306 72
    0xa102c0c011100a02201502c0207a52040b01e20000ca0039041c80300c500400c000041d9001c1a171405154141c8030280c03100d0540c000071200501d540c10a44a101d00d0751031401c84124000351410404048082c14081e4400300380c4414204d1251b81c40c0a00081c04020014511b401e04803502034460034040c4c216032030b103940d07a20380b9802c0014a03004000d5100440031582490b1401b00440e21301c00d602102e00f20b200c0d440b0b80405824500c20408444000f04140c541d13402550784021122008081001d41031104c500c480c08041201d0317100d070044500c00c05110980f90075141e05441b6a612410304e040c012842107490070f0040e0b800f6000300404404110b0200150260079042a010b4011900d56500140e128880303c10b0000000d94120341c0d00d42080071030010001c81e41e170301c000807040170360f01802c0200b5240c07501d03489001c150b5540403005402c40c0c4645400010421410054881140500000c004603101d04104805031406c0c248040b03803410f111a40c0010516110b402041c10906030f040c0050500c0c1d50348000403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 445045278 1250 445044028 445044097
    0x30910020304060e0a0b0720030f010b0a140d0201050f0702040c0e0909120d090c0b0a0807090f0608040602092d0109080601120303020705240402041107050a0602 71
    0x10010780010404200c035a41090a0810f002012100750000c217050498041c083d0140f40b001a1074450381c071035007014611a2481e04030046002500382c0fa0398042035140341d800707011075040080c024101c0410001c1d01c850a10300e00100d0350780041c40b0f400103040310b800440d0183c2181c02051348105042110782d0040c0d4a51150300c1b0080000e458202074602448100702003040e0003002d044850300305a10203030404030f108003103c0c1c140b070800c240050141100e08104071081c1e2103401c000180000010031204603034010804610030002c039645c1900454075149103014018141c415400440c0b42080807900048103038010300f40141b005002e40310b0011701c003081c42c851345018440344254051000d01e106400e5902206400c060611400103007055494400807281d80801160041c04040d800f00b003010800005010981007140400c0300e00c03105841039407003003c030800203544c100d100368908282e00b458400074009440f40c1c03030b801001400c3e4078002d6071034850107544404401c07100390403000c4200e0400780d9010300e001c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 445046528 1250 445045278 445045309
    0xf0215010806070f05130e070c02040501090204080c191a07050a0317100e16171920070f0809210f0606090115030b04020a02030705010c08150607050309 67
    0x1480703142031048004d0409046124203e080000030480b11110520b01246242110398078803108405507510b840850700c2c0489130324001d41c0f260400340000360410745900900103840411003601d0b40940300608008000003401c1c1043c1082d80c00319000c105c1c800ca690a5000d002c01c21034400b0b80341142c00d07a201c60034804901c000301d0108010031040f00c441103d141c800c681c803900e8029040310090500c1d99081c5031550060a500343c1c0455219280f883c00d10403220b5035854070796107804009a040c940b1150400445851162010a10744040c1c107003d441840485038141c080b61651030301c4e00445407070350048110b0001c2c0a41c0e84034020401c06419441c0e01d584003440f0802c0c2c0354500741041c0390004040c20b080038222204440e50049060140d5907a904d2103140c1118032400c003c00b0407141c003e03c260003030402c1070103184e8458808070741d02c401550007000800f1228481d100800c4200040c640595840b201517884101c0c01d598802c840f5240d090120041010300d0080048a061900c000c0005034610040c0f601c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 445047778 1250 445046528 445046533
    0xa021e0a030b060c0703110f030106030308070206090a0b070810050a0b13120b010605130e01030f02130507080105060703180906051903030c02040504140f010c09060306050307060f02150108 83
    0x55420140d4580314100b4480c0003103d140745001c2504030304075580c0364280409000600544a8a115075030b9001641d014400050000d110b09540c9040c054490401214500c0160081c0300000390354a5010640c08881940052001160f80711624201c4e82c01d500106070700e1080c0410527001c103103982e0380d000d06e000030300c45840c545550b054440f40100c10011642d00503040140d02001c80c1000036085907060341504d002d440c1254a42000041560101702c0690014448030704200003c410311070b6807075240000e58004c1d85e400c15040c00d00c448070780407901c007146c0001c00142d40d0300041c4501c0c60900014038804e800391400d0f15250010540850b0000410781c0642c041d141d407154108010300340b041e1608503484002c640034036818515200a001d000702c64000911980d91a400141003080f000c2c5d46411640d1325604540342944514441c5e0b00a218102801022501d81d900c0090128030038003610040d42c0008d000340c2007152510070241e9450000742c40203000e5000e000386101c5611442d1114034000c0c59480c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 445049028 1250 445047778 445047787
    0x4020112110c10060803070605131203090308070f0c140a0c0e07090b0304080706020918070c03090807080c10021e01150f0e1302011202160b010b07020112050a021e 72
    0x1229840c19143c406640c0400b0b08010741003050603004400d031811140c2010021510380d80e07040c0c0600c3d13a104440001000c170000c240c540c41020313902d6807010894a109484001c41b68503841c10555144480007803200c00603462030840b40005000700080d1500a103107000301d0b050314100b9a901e01c47c105840d00507040900302c500030040c0560b849801d0b203005201031504985141004e0315100914850342d00007602c07041c2c000075007014a0f01c134030b00080704407070205032046224200890001c044454106003600000c643c01c101007094800803540f142102e5071000246001d180c0c032802d010042d43e15031200800c0d8050b10605082490700340ca804610a043d140c000036000320a1506c80c28080e282d42c2001010420403075007400300f81807446103903030845a07180041544a200d440102d80d5010752400700f200690000c02c0403101c8410391214041168402c40518800342e0721611503a889007d40a00640016040041c3e005c03150301580c0100d4110420030005450100200c5500034044514401018020390014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 445050278 1250 445049028 445049047
    0x703030e160609060804050c060415090504050106020304030b0606070506040506100b04060e0d050703120c020909011112041103061003110102010507142a011b02030c06010303080402011211 83
    0x11820803034103041d0440881500b00b0400030300051a40c01030506200d2004041343c14170004000d099044080205199643e5407a010401608080d0402e0500030500ea60700200c3c03503207001c2c01180e050704c580d07900450425141d900ea8040340300c006030040d90030030320403c440320105600b072200364800c90040000f0406030820b58003c0e0b50070607666000c070301810810320040c0202513210018003803669003104d00040045450401c241021300b1580010711440c11490754102a581140020130914000c4601d0b414980c0d41c0c110307050036940740c540c412420100820122000e004415056a00b150043e840c0308680652800447d1904c02c0c02e544081c08419540800c00c10004507400361500c0070000c1c402800305040c500c1002c1d00c6258840152a40441d02085c54000310f00a0308060f20420700440d110700c80f0340412500d031402417001d4458440a04149542061000d00000407101000e0900f4020705190b0300e1610308035000340014008034100f00340741d81c0c0d400346c1c284036000f420007003a00c401c1da09545d1100e0a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 445051528 1250 445050278 445050283
    0x50901180f05030f072913060e04110f030402061b07080105060405090c010903080d1401030c0e070903030507020907090b12090606030a170904020c0d0203070203060c0306060316020c060703030e 85
    0x105a4210f40d584611020300110307100320f041b01d5100054002c441e14002040311203c0f924042d4402420007500442000a105c517031050b55900300441c107880070061081e0b03403100149148203e4044842e070540820100300181402e0006281002c0c1e4029801003001844c4d0a65041c200e11f680058481da4461090001d2450704c0d00c82c254000421900504100807600d0000c2c08460aa100140007114046502c004061f0366800441480010034409840c9607100c2c9030404c4042e10781d008041109441d2030000e110603015000075010740b5050380b01d16003040d2aa0707080080c0500020a1503041244c00c1070f001548164010203841042401401d4103ca468450b2410785413540091140d81b090f44a11052404955074a0100c144001b001d202a540c1c0c3c0c207400089000f80c418117044088034810508410703003c1e07a02001402070148220706540d0240c031001c40202d11800252140c80e4010340c2000840c4510004110694012080d401940d074401221400140f094010030b9003580440d444806e14640010103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 445052778 1250 445051528 445051543
    0x212070f060504030c170f0d0c300c0503040909080409150b0f09010e060d0f1a010c0602070606050603071107050405070f030e07030b160915090e04111906110f0d050901180f0503 78
    0x92b2455182c00048031101c1621285030600c6070002d2124000809060046c00c0c821200034020b155018046800e00d0714000300319a02030b2080300d050900d810700101c0c41c107003a031a10108960000008900744007085e0444071240d03000d5081a0705002491031030b9044d40d225500601036000380c03048001000e0300146014015507201c2503040f00b0f070040c00e006d038400d40e80c0c00861045c0380d00d800c09001a1680d8691400c80c0003041d09821031a1f016001000300110f00364480f031020010206201603c042550300c0c01403100b950300c141c2d103c1d4081111000500745d0a4442e5118584100b182c0003101c10856a0352900e8000b01c0c410303960721107070720707034850019038a00e070080074540c0141002070054102101560008041141c51302911003420080800b14050101d036400c1c058942d14010114001c56403550b02028200fa5203120b03900c04140b80504000c0d442001181400d20a40c80402406420301211310440c1ca07a030006401c581884103903d00ca100444070f000e00c1d90042c1107022001410300e4104030406160207070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 445054028 1250 445052778 445052813
    0x90f05040b01090f0b09090124050307052b1407050901050f0613030818010e03150a0c090f030503040305070f03170708070212070f060504030c170f0d0c 67
    0x148014403000a002484960445804842c0081c450581d038688070301801e0a0b40c6a907500c05094018489030000650140c00007840c01784418130003c05404c2c030119042c3c81442825815005000d0421150502c0c40d5007001440b864014029018a01c19054000324101c9200340e44142c10f0304035080340311313608015180140400701c0e1100c50032361600001030201c1612035941da00565004c241a1450600d103800d04020f507511180c440e03114000180800705008401030514000350044040014a04012907006000c1ea000440041250b90f40854503020b410001d115100300180d404c1c00044843c101c95203280a14800e8000d1540e441c51030520350300c0c020141c0c110422428440104200140b01c205c0d03501c80d00005404a1740d242c0b455420300f2a4540250000a5045a81c0100c10041d695002c14000141c4503004241c400d501c0e1113035011290380c019800002c150100c60b1005003c88016001e00c01c0440145d0012107410032901020315083ca010350010304042a030307801e051420080c100d51201100310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 445055278 1250 445054028 445054031
    0x150f0305091902060904150e060a050f0d0b06010905191d0709090b0604030f050c121212060a1502100606050703050702040c09150504030201020f2e140c04090f 70
    0x1c811200420990030b40304000744680c80c0000e003075001340c03141e42280050780245109084200e50312a400d51440c07004a80061007108244004a414130341600c2400601c2c6000d441c2424000850342c40e0a1031210107008241030141103000000d241d92042c0617110000505102441b145c0e203040320b1480300140d102d1001d02440082000c01c2100307540025480200e50014401240c0d00081c4404a01c0b20300c04ea0304045e107000b8444828038184980001e04d0f0344c0561080e6102c40341420301c0748005031180f44090303400791800c1041006403081c2800c1143c0f5500000020440700700c240e40c80c010500031541c0501d03400050303003100030700f1a2120518400c030700c01040d2500703103585406400c1c2e80c02841417143d140000d128991703d41c20b4071000303441401e0b42d6000d08005000803a204001420203022a04180f00403801840b403a512290700f01004508100c200b1190040c0e0200201090992840d403540d40f0300d072024840d40d40640d402120195107080e40568107118405940d07900340102c1d20305403450014502c0d4440d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 445056528 1250 445055278 445055293
    0x8070b0a18080c011409041104080c09191d19051b0307210f03090513180b0c16111002032809030209011401110a0c140109150f030509 59
    0x2c0c000420503008111003481c0c140c14040e40003c05c048540181480107400034074128000150080000050041d60323829800c41f44492803400400c807805800b1140540700c803103624919550341e103075a0002c0e08499802426100855801c0100a292024501c064041e1001245e80d0a06000c4248104e606001c50000210540104c0e00c010a81e20107075171260000c070807501280310070344410350600414415440508560744540d40d04000345a49414066144a918450004500c030030302480764a031005840c030805020f5107050744600c503101000500d008091201008129150701003480102c1c1c0d0f05110f0450b9042c51202c440074032204c401da0420780c0003594000c00241846071443d2012360f4640d2122011158a9564200102c0d2066041e51000f50089000c0c0008100d0749280813515800b0582a07850a0b282008102220707070325a564134024140310b196907814051150314909410580744103042050300603130340300006a030a40e0032a4180300040e910486503103400b0303810b008194020030400d0081150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 445057778 1250 445056528 445056539
    0x9210f050307080411090405010504200a05090c04050909010c0f030b010203070b072f010e031201030f0305041a03041a1b0318070609140103061202060c0708070b0a18 73
    0x841c800505548203100381000041c4c1040b881c00074480440d10f02410800d0365080a10b4010301901003035404031505200c140724034035480b0126410000302d800c0100300c0340045143c401484201d2502030200d04040c2c17803c00000c5401d03152465801c0c09001c40e1000017a5211407144002c00c02600441410b04150600c3d1103003d41d82c0c0d0000558420039000a882c100a80700c0346030640750703c3e490340c0c40300d000c500485518802145524400b40c01402c103a100a01083c000301e6a050388a108040b143e0030044060401030010684d42e46810114620078100145450b49540d0400b88140c0c2c0405508034440c800000c01082003ca04054008669114003031911070800700440c5443c10703449c0003902c0200102000041003411012010000070100100340c800c2075032940c00041000110340202560001d05903291007141d48a80f10340021560741d034920048107070032a13007001259032004000814501c5000004920084123100c41002442a0b24841c0ea40e00c803603d6004c1d1080807030504151080203410001c00c00e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 445059028 1250 445057778 445057787
    0x90602190206070b190516030e0607022e142e271407080f16140c070e0105011805030d0305060604091b030e0309010f120f09210f 57
    0x5030316031113a15000266100718140000009802800c60032504140500c1038200b031135840e031040180d050f9002c1c0001c1040d00d201c03070356400c400d40f20000180e1103500d60728148542c00ca40b1000d030b01c810504c0c903400710031003842c41810b03507012034412603a001410080c0300007064440d004015a00c02e01d803640d0106100342124481440c076510900000324680d481140c040b0b07122840c00706d2400e4100c10204841441a07590341d6203144112074000110b5050400b043c035240b890400144a9141208824400440a00d0895038003990301440e01009505000903e0214401c1c000c50015001503d9040c0d010b6140400041080300e1680c041c00c106441c01030240302c6910003054142c10300da01d50a0104d6a61525000700c2d42c80d10455208524461a0034695805180d0000d81464071103140d64060064805001c041a264440d030203d0300c0c00304a00c00d84002d5494059204001d0f413102008000a40d280310f031000390195074402c2c0b030448000c1b072000c21000003034201520341c90040703105203003503c45002050009031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 445060278 1250 445059028 445059037
    0x91703240907120f140a0b010305071b110112051608060402040605070210140a080603010f02030609070c0201110111041a0c060103030c020a121a01080d050409020705010f0606090602190206 83
    0x32801902c0d5841a44c4c51525500041c402180c5907007281d4052400f0406080108403c810243c0042d06007008141540d01c80c1310b0346800007a0902003404450700c07c4c2d5032021461a02d10700203040c401880700c2c41c41688160b104440c481d0303180ba5030100300000c0000b070040013090000e241e1486244113010a01c845584101a140250782c107070780038120444d0b81101a1481080c00c511103041050020760081d241d9401a0b0440c029103054000f808a03890f01c404003026400101e071090f4000241c10001580300303100704006401c0d14010b0501c1518252001c03441800e444405000e140780f820002020010300d03100040c14111043c910040f9030400b908082c20795280c003010300c005403c1025600c01d000030340d65580c410310300501d080b0030125403501a030b02c0c1c0414403a40d41500300100800c800f00001c0c000501040038a1400429544d1924203400c0c0741c00b0200a4020480541c0d2640d603e420100829450780b06010140a1507114900b103140750001c0246880f40101c2c0042c080030041d401540142c80c0d079015035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 445061528 1250 445060278 445060307
    0x90b15040b01110a06020d0e190b01060813020d1109151305070e06070c080703150e060103080f0d0605100e09150306040807020105130303031505150904091703240907 73
    0x540c0c3c403054007440c60042c5c039082303807950240c0c0103645c060110500001c2569070928030406180c0d0081c0c0c1c3c0c1c0c1605440c9020102e941080003504801c5400c014030b080d00090a190344202418040500e9034000f05400000442c5d510030443d45103400e00c60a031078a90801143c80d95040c105120303d10304124028104141c40484d140610f1001c03580a04000c844400d039005003410364200d070543e69403070034405007140005200b0300c2083e15200c454852600c01017901810b99401c1070000d46840c200301210280c40d4030002d42e6640003540c0710b002041550300c1904a032a110700603561858140f41c600c08002c0e00705000741803a800c00800311318401c032907140420201d43c490b4100d00b205481c0d41c040e0005807228440c02441c121050300d0203d01008060b00740e407104080040c104540c80d000c5803903205000740281490031158032070105121040080c41d10741c01c040300c1c036440741e44004001405002e0381c150701e809c1500c1101c0c043c89500140a9171106802a20341140c00849216607141400b0340003034104401c00c1400e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 445062778 1250 445061528 445061531
    0x150c021b0d060c1407060f0608010209010e0f040e010608010c0f02072405070519351305030d053402040e1f020714062701090b15040b01110a06 63
    0x14007420344c02031420070b0510030001d90007556072a5600e40b6800914003140c0c2c081c40c080c5815008902800c051096441c010010b869050280200707900300b144691190201c50343c0643c49528081c10362000380607940041136403000228807a201008054215003802c032004d41103620011040118a41c000d0250102004103104c0840240f0036003c00c03180f61040c1400a071503489a058502ca1500034a04114602401111540b40f0030300d0408948840740000010301072010300da200081d055a101c0030051514045414114100c55501c001103070601c0c4401140702d000c62000300e0041100254a040c03050258400710252469030450300300708042291100000e0300a5540314122a008141000386a56180c4008813044c855403c207101d1070080d61010a04a481c2145045080014030b00082c806004a07051044062b125011000d20082e220385403031008a550340790200319002c03819078007055004c3e42400040901500900e018001500c01000a07a410800a000600406d5402007001900c490748a40c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 445064028 1250 445062778 445062791
    0x150712050a020a12081801051b0313020d0b10080606101b170403060e010212011a1c050f180c010e150c1606030b01050a05090607150c021b0d06 63
    0x41c202e150001c2840c0003020315a808168011554104000c54414a010480c0c13024129004034418280e940035142e01002005501c1aa12070054210240d0ba10282285862072003804603000200e50003440036098444407564824061088104c42071040904104801031030a41061408a8001d192549810040000c440c0081a44020006901405a0f004049000100c0440505041943c4284070842d49189002d40a0300040810300a4600745901510f0b0008a6840d10300c0d42c010203001c1c2d20a841c0c080a04024104624000aa294500d2807034880001402e18080240c200c210402901c1d41d001703191040c5034640007040004010000540030b1070181100c0903c900407035035012040c000c10324880740c0402c64031007111001404842c1c070b1100d80405503101c3e0b9a0a802e4044505010425001403c10046400350070b00680c02441d42c0c4101400080c98104642c4401052801c0d50214540d040e8456094003000c2e64100042c0a032034800072800f4041000304c000203082c500c07411100803c041d440c0c94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 445065278 1250 445064028 445064047
    0x14130c0203030606090d0204110d0c2c061207090f050d1104020c030d0504050f0d091421030304050f011b0c12110f01020309010c0906020a20041a15071205 68
    0x3030306d010881e0360140040c07052000031001300d42142c01104200007024600b0b00c44801b01380c4222071520a401d81d411076420743d0104810045000d4910100e80342d0010310810441482c0420f24000a101d00010b6803041c200c1414442c0c1c80c00c4141d0250312462003072100f000b0000109890800700f400c000fa0868005a4840040141c58118090714954076541450102080240b103c040b0780400400a40300941c0c0d007102c1440c805032420384042c0105881c142108210400074101542030f49140030030f603000c81c894070f070480140d82d00d035038802c807011509a00304218040c3c0f141c000340034500b0750018103e403a07c40d45502e40c0740181301640800001d043c0c24114941d0703180082c0184000c00c006220401944c510304000031469020b5402950005a10341c07074a28001d0616214003a0002552000ea0180c001d507006e64481100d860841c1d207603446062202c019118503a584c2d8071a0358800300c50f80340b40f00d50110445082003044488a821a55000010000030300002c0d9201d10048140d0f03440c0c01c08948a52548 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 445066528 1250 445065278 445065289
    0x10b090105011e0e0f032a04090b0106080a091e05060711030a030207080409180b0c0405130507031104120b15060a050703020a020a032001141e1314130c020303060609 73
    0x1605d11034041c000d43c0302c80d201307400c280c2000c0c40c1c070640005804400260310000740401c031a800c500250051204c00c1c010300c01d5912412065411060790940402c05c050151111840b030382c1c2d0b000d0356603940d0502820502c20480144a85070b880005420b00014052603140701645a00c262a03840b000c05500060720b008000f83c841c152009081c02c02d00800998507074042d00c510b00c89103000c0603030b00c42900c840010b040c00144000c035800c1d644041d11103450704498900705800340c54050146001d02d503c1c1d00071311401c1c0100001038001451450308010244001d81400042554082d185001c6000050b11180c138680381c041c01c864607000316140c403035560b161a0508905150412400940c4000300d138800109001c2c0c5078103901c03003010850040520a080f0b200056031151104c0310b9814181e98180003044000d031031309503200341620382885001e10300580210040314007403c503041424144540c451184480c1000e45455484040a41007003000351007142019569010044c5418400c00c1c1c0012499080d8850 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 445067778 1250 445066528 445066549
    0x120906060a15050f0c010519051506071e120e090603062a070818041811060c010e03030702010b0315012303031305090a1109040207050109050708010b090105011e0e 72
    0x189000729464001e00c1685c1406480140c988107414a45007040c0c0c80000494407030076004101d12074560f10130004480030300600d41c1281c001921040202071140d4103101d00b003520540f43c40d01c43c036564103221802e02000340c90014581071003170041341403400f00515602d0004105800c0b42108054004043d1003400d1015191a4049803400c2c400b004200751007005015000340000d800b051014038989103003c024842102c012145c0e40a074049241401303004200d161103012542d501c080c0156290110901c0c8071401e66040c11030141c1180e0000040049240d42032041c04a8a9011070240c007458000780e00b13100000106015200c01009030042c945070194180741841401031028060301e8a032407070101d910040305064440c45000d11048400145400903130f00c02c65001404c1c4051650401c2442003d110080d000160101c81030f65030f401300f01020440c100403090041c8194000840e1490390035080c01074280060b401706040c0a00850140307080b50249441600001f0b00d442d110400e009545c0008884180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 445069028 1250 445067778 445067797
    0x306090e030315280305010c03020a021e030d1a04050a0c020d080601091703220501090905131e051b0109092307020d180f031b0812120906060a1505 65
    0x38032400050113800720140318100e0b40910020042c1c100746044c190241e20440f41c4180058003e0081c04200c031050065000920f9408012641014030540000e0115104c4651701c90100301c01c1446540c20f4a010700803103030700a44000d0b060011044200c0060351311118005c0e0302c01407280a0000a511740d101d0031a00c001001040340300a40c1801340310209440303600c4000303109a0300754800b56064004200d0001c8004071075060b50f600360302600d04241c0c0c00c02000c3c060440350003d104502003201142030521300e02c00c40da04100800c810101503203020352800c4540300d0211086080c050701c0740781030307a0000c80c000100c44c1400400300300c019042c8208810310807000d000003c1c000360301d800d004409500003510741041d50180c4441c0e126940c8004d604010305824403a03056031041203001400098520405100440b4520a0101016481e81b42440c145902204142908400401e099010549000032180c201c40c45e0800b4102c241088000b08103031803c540030351042022000d1002d84003612035000c4500c00d44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 445070278 1250 445069028 445069069
    0x1a04050a1502090310020f1b0a0b07030902010e040501051327030306050307060f050909040305221406030907090e070803071a0f15120a0203010204080a0c05181501120c0f0306090e030315 82
    0x1908bc10701070000d01c8621400d03400220b0101140b1a182800d1148070b041c0c0c0e600928038198015101050300240484450915116a4040006824a8078000c000e0707070040c0300e80c0703001c0f0f82e0f02e00b00014949080001d0f40940c2c10403d200c81e2151404ac1c11a04580501200391203101c0076680c1c03800c3c10703500d80c40781c8131422140d0652031045014941c9803225500a840d80c042c01820310303400700b4040090500041c0e404005540240d50308008029035648aa0340c0e00080100392284a0369031081142950017022065881c401e41a99a00036846503c20300c0743e10540c0680f9507500d5007801d107070540350340343c160302c4003401100c050440d11600541000707803000095005000b90b40c0c441d00e51507180d0710b80070403800c1110304a1485402141c58a01440e020b01c620300c0c00304040d08a55070700e01c8a041800c03481d07103d1310305100c0c90746616a50810203003e80346080501e907e84e00c1c880d151404c0e00804454899211b480c02524002100100410100c2102d41241060705100c480c80d00d01d9002820404814144041d03a5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 445071528 1250 445070278 445070281
    0x1403070305100515031302010e090f070306050d050d0309110418050c01030b061603050409091109090102130504020f09041b08090a1a04050a1502090310020f1b0a0b 72
    0x859140c0c2005114a04803002d220300d8030303512014070002441d441a2800c405a0500c001000c0c1040146c0015101e80140f4007074440c03011020100d9103418041c0c0d0080c00c04c0d0019001c00095a8040c0144402070106035541c004840180c0c1301c0c96128484144c0d041c0400d500c908501c01401413a2014001189009004004401a80d4147e00d060b680c048000c442c00e00461448001a41c080e1041d80e4000ea0003402c400c0c0340a5200c000c601081c0c002010031014080d0511010035611854800c4980305441000312070070102c464010880c5035079004040e07990301da00420010a050380b8101c2c7c1c8100b121020340b000360701e84403e40744110040c018004900e800500d004842c42842c4641d800c9008030503a1600c40580c95250442c00c55100e070002c2c0700c06460113401808183e011034595002580c03043c0644140c90015000d50380b170b845501d040c1000d50300382c40e4000c918541e192400f44004ca09250403c0741c00c526065803000d4602084c020000081030140d010380b41405485001e0142d400b100c0c1d0310854a00c2c16 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 445072778 1250 445071528 445071541
    0x90a0f03030c0207181d06040308220b0f0414060412030f0b040f0b0118050307050609031c020106060207050a03050705060705030706230c03100b0a180b030615190f1403 74
    0x41c00440350748180e880c101d1040000140010850f54003549d010390354a0001ea540002e4072076000c280c41540c100d0320051100e031101165880f00c482d40221841c02015500d810503080240001002c080507e2068001400303001c0014403c40700d0144c282003504000c03e0103c80b428403540105076120b146600305090890000340703000f03107901c59480660240c90b0000701c50810350016102c92510b02800380c1650007407206201c03c2c41e100014080c2908003c044416600d94500b0f10714804488802560150791254014000c2c41d4041c841e08001e400140d4540780554515211107589001501c1101c0c0500c1d000511101071000500860b290b058000710140410700286c1020aaa0000400b500d8208030f4a40c0114810041c4035089074007842d8451140031010782018040c00349030b80203400210074000c080c8040c4038202c03252544e44004004160545489203047c0091141944140d45800b0084004025a0003c800d2041ca0205c0c0c0e221180b908540101284034155400da541c0040241e101901100300030341d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 445074028 1250 445072778 445072781
    0x306060f0301090b31080909042f1e0a09110f031509180a1506091503060b09090a08070c0f1e060504060f2102040617090a0f03030c020718 61
    0xd8650090309070004484229081d082030b180600c020701b0341004202c000680c2c90400303000c035081401a000c0c0e80c90000e038003e01c2c3c0500130314010690407105c0301e900c1c00c440c180340c00100c580b0301d04038130503034180100b80001c0041c3c0103c0b45405140c0d20103949103000b203000e003c468180c500b20741e800010280d0700c0c01d000c59100701c0720b44005000d500c81c0c1d5a11380001c40c40c00340a50712080e500030301001010044100d540390003513002c4a4075815180e5a8800b00002c121050303004903407076512039000c0e440c800340c194180001601c1c00d05255502840c1030710288140075a00255010000c2d0300b100d02162034601900d080c801c00c0b2000d5201c07008800312084040382240c007040c0340310914100d00ca0500c004940e64030701a5141d0040344564001308481c094030010303c0340510941c2042c003801d00300116200c048441a40100e0b08240c0100d00041d03000310b40038804105851445800084610042c0b4407017500d65640003600c0d6000c40d00504064032003c0442400780208500000b902d000d20342810f50041c089030020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 445075278 1250 445074028 445074061
    0xf07320f01050907030b1512031b100b0303032a0d05070f02070602030412050109020a0305070315020702150a020c041406040f06050d060b010203040f060305160302090306060f0301090b 81
    0xe015407810b008a014114002054801c4a038072014200950340da09603800c00d80940813101075004995085a8240076805000500000c041140c1209a02c111781224901d065a030043d4034040c00e00d0103210021a55000003a01c0d840000c1d583c1c8819401c03806135000c101b021001e002e0901e09000820402220202e640240c2d100352120750f10240f40c440702e881c01700e07541d0f1050f1140c000036820810042c054200440c038007084807401580042000c0d01c0650120380c0c04009a03100361200d4003c01002c1c810031407840c1c1c4842108a90110640c109001034000901e10f0007401140c0194540001d04d0781c42ca5402407101000c0d881005004000035010401c0c248200c000880c4e100e80301d641380483d50f4a460000d403064805664001d00301504600c00d950b02c00c001000f80c11042e50551200380800a06a5144044a00a011590740104803400c14003000d0750056100d500d04001d160052202040039140010aa82e008004075251400e4003800804a40101a5220050051400b8900700200d4a10721030508 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 445076528 1250 445075278 445075303
    0x60919150219080f04020a0e0606090d32060a05040f02031005090d1112030a021b0706020d031109041508031b060108010e0a0602070309050603041104110f0732 70
    0x72400e95130102d1103d441076080b00e00a40c8070302044010300400c0841e51549501a0002d00024600b07445400054403c0300030b00400c481c50401c0700000c59007400807145100c80100000714401184c40301803074071030b110314000b880040e03011703030350710015040c17025070802c00c1410368024090f19421440041c24a02521048a00d01d44a00c02c04451801c4c50b4810039180ca58114042d000d00311190300d80003c000668006084441d0858090107018a0a070854900301d041001e1000148103040c548030029041443c1c0200138801d15242940f242e05100c0000b048801c00304045500140d0340381418401d000b50401c9810040680c03002140c0214a100c0b00243c03c4041c0c413140c0c0031503060760303664204242a542d910300c1c46825a0049207800700081c10b40d4001d0140740f4440c1c14529046520782004c50340c0d941080702d0903102c88005010b402c0d4182001d10903244a041020251450100c545c03540342403500c22135900403c0e1008542c100402c44131180c918810940c99900200401c500402d50107950f8034004208 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 445077778 1250 445076528 445076537
    0xf0a080a031d060d0504080708032508011401030905010e011b09050319140307120c0b1806010b07020310050414060115121a0d0b010611060919150219 66
    0x4104500e012040b01c0342c4640300500391890101481903403005014050b208491f24a02071040800051002003c1c522400c41c0700d820030003050481c8403001d48010300001c0701042c006d03100c00600408401c0014081000403e00b40811041c42c02d103401401449070624440c2756500c2c242c4000031500b102c1f02c41000305041555488070007a100c208250310340f8508418a004007131220903100000e03991928102d04480c901c810f4901b0846a6100c000c9014034407241c072400245d8003502c5004200c180d110035900203c440301c1c040240040182c5155440c1418000d0b0b07100c3c0c01e0045004800c43d5001c00c841034404040c51810b22690070320745002129000c0c803c5c1d41140c140214000403d0070041c91019040d0010307540e903080791981d48140107000400104942142c0c848840404448644031001c1003103000b032003074031402419813500311f00a110301d0820700c00a04a42004090040b074680004041e2191400701c0c4000c510711050380762540050543e2410380751410300106e40581c41d440001c44409940388242c54 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 445079028 1250 445077778 445077797
    0x905072d141201091b03020f0d110d06060e0103110c150603010e071202030c01050f0906090a080a0b0a0c020a0201080a020a030b090c040f0b0301051e0310090c21030f030b0f0a080a03 80
    0x7800c1e807d0f4011880d184072401030902c0050003085172500041e8000c60f003205440e180140301020003080d00c055410160104c0d140070b03000d032055641440750580b81203207029502d0800040c25869500c501d050541c04050300230785000b041e04c0e503a0039441103018859040071103504566030036800210440340c100591290040c20746480840d4058012031ba0b8a03100c101100d45814404003c201207900405011a0004000345010035864402c10280c01c40e54012480d504140c80c3c81c18802041e00c00340c6100e04119002080d118005036044469181c202c6010100961142c100002c1100241045000c01c0c1d03100761440144a40c180490f0000c00a444130000312000d001d84032079040030139100038401e0310f070041110f4602080401d2a80d107040000301c0c008065410400d0114000c4042e10702104050307610000410080000c202030000710806102e0326040022007045d1502c000c0c081c0001e8082da4400d00da04c442c030500d81c554409115080b40800140020b100c940c817008082d41d280c441203403c8020540146 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 445080278 1250 445079028 445079081
    0x31d030408070e041104050f06040506041112131a0406060812040b0702010e1012050604090f080705150c030103060f0605101103040e010905072d14120109 68
    0x22141074614140041ca0301516021848241210042054800c2084444200d0559440c2d0049a006014100b080c00450500200b007004491014141c140702c0d030300c0c245007116012121300c1603c2054600300c01006e002d944074031904554100030800200303980d0000040041d43c01582c0c01c901e0040b0b024200130411300b501c0705016696605a440c2e031f01603118042c00100040e0a0b03041c01046085e10602d0000301180403c1d000c18240d1b1400c0103a9800302e00011307864030320180248140b5a01030300440d41030180d069240c6032080110307050172004e0505c040009458080c07190070031072030301c071510120100115032911040f0441c59030000c0c0800c4500d10304101d04050036583e140202c0d020740d18010549241480d5001d02594042c41401030014180018400020f000d0200102e2a00a2400700c01c080346600d0401e00040159141d100ba604484010710341c4880001c00508003901c81d1a003505180c8007002d0001315541d03050040440090506c1403084c000f00311b003a40c40d00101e65420784488400107401008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 445081528 1250 445080278 445080283
    0xd0c03111923072c0901050a0c210908071a070305070809120c070f0807090509030a0c060f020c0f010b0f0d05030f0a09030c030c0303090509040f06240303031d 70
    0x1c40821115501c000c4041c00140b101d0304071301c440003801c403801841501540d451112424800c841200e035595450b8208081820b4030300404050510903e401009214404864540003500004150005d5a03801203003017002030017404c0710403050304985450408450390a4008a41900301c803110002828140894100c43c01810444d02450140000d0300300300c3d0020f0904440364212880d103070203034410b4550024030312008014200240c001030000d098203e040107020001d0300d41c0500518000c2d4020065451101e500410101000d90301c26400301c1d909164010140190142c48a2405603010b100503100c58113205610450005da82610300f0724500c001d103020841c1503071020300c0151494004001d0304141c840c165008040300d038114141000311944a4071030b041030001941045469000b800030030300a0580201d41c0000520040b0b0b2603541034906030f0303200c010401400c10018a41e0351107200715081d1a1148146000c0c0c03080702c010f01c00d903141e560305006014150009030030748051041a085030346520701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 445082778 1250 445081528 445081583
    0xc030f220323031605031314031f09060f05061306060c02010503100b0301030311060606030606070206090a0512010603031202030f0106110a060204030305091c0201020d0c031119 78
    0x124146116140e0a616076180d0310440a654800e4042040000104450f0410003c10180a1740c011a1101e2501c1a5106807440c01e4202020248070301a1940f13441e44c000075180e07074001d151030246c441c17030071021504030190400c0c2c0c500800351410121841811403a0b40d100501c1418125040b400c0c800780084c0c4a001c40720a80998800100000c2c12100554001c200640e00318002d0084d414031b255440000d61144c2c0c000381c00450000d1b2480d000001c64074130070003481750894400c03550b41d03246041c0080054000d200c1d52000074091007012074244503683c4c0b5409084010a0302400c400750b01548001d00714001c10304c50000320041340ca00c51002c20012541c0c425a4400d40c0c650091404690a00c003066402000d10260341490b480341c03181c00b00c00207450380081d000940c400e84956455805601c00c02003189454016001220b034194118405130381d00050254074507215040400d0340d8150790408640e640d000c000c10005610a8080e41381e03241020101503030209018185940c0300304a0403007a0817000303c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 445084028 1250 445082778 445082783
    0x170304061802060d0b0a0f0308030402031b0f0405040503090a06050c100501030b1305030f120412050a020d0e0f03120903010b0d05030403060b04020918061201090309090209060c030f2203 82
    0x3424040c00303158540d95030050480c0e0170b009060601059a8442d08064000a50422505900c0200c01e0204505040108500315118048014003643c030000100d40c20300e0948108601c076070f4a410109082c060107000b11000b4100c040c00080c0d01a403a6072010342260304c10036001125104251030402009810b01c00c5034180c80c0c3c80310210303a0580b03a611120a8002c0c005205690300c1c0804c0260026500200c0300a105070b02c07018220010342c0c0340c41e0030300c0c0040300041c28054013804410041d81c05419804110800445103c0c1408070100c0581c00100da0302c01140301d0015010700c1024651520040000080d016a82c0103c1c000c0c001e1503001018010329030314180c4001e2a42e4801e10060001400c10b40004c0c1220358003a000501f091101e000050800f4030450b44194026240e074144843d50404084c581403498030b00c03000340200a1599401000e10549104003002e065022510250b03070b03a00c0304215124103007084122600c1c1c6901440d5040250301c035946001080c0340c807110303900000d800e40c0c80410840741c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 445085278 1250 445084028 445084039
    0x21203040204020901020c0d26160210020106081009060c030b060417100f050f07030b10110f030c101505060a080612060702011a03060f04030f0c170304061802 70
    0x21a03540c280006504980704080c15070054200b0b81c40c5c02d441d400d86000410f4001c0d00c003c08407541213901961070b00000c241c910b01ea10b804003c14213640e4030700c0920600c180c0d03058a0420704c1150401f000c82c014981c0f80c02296450250b440f142001c404a5089441d4440c0a00e0b03081144152102c800d134105d440d06034005030420380500c003c1102d20154501c5101241909065481c00f0101101d0301e01159032101c24906901d54500c284212045030060b601c2d071000113810701708501c07180b00d000150981602c2d802c85081041d000108403a07220700f03005296910320300904890311220469451034992a510200e548281c2c6400c0e400b40742e11080300041d00c101d507805042c0074a0000007140840b0507440c0100b0703c0e500003210003440e550004040000b0303441101702c1c1e80001070b04c845c14202501d0940308405003a200e83e11000501c031121403c464101e41065041c02c2207442003066000c2511a03038418100070b420089040c004109241c141401540300702d00c18101009240c0300382c8190203000c2c1d0340300780103034015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 445086528 1250 445085278 445085281
    0x503010c08010e09030c073809040b0607020607030509151e0313020d0c090c0507020a0527090109030e0102010c02060f0709120503130f03050c04050c040503010c110d021203 76
    0x2e40070440440d0444003013010b0341d14240c4103142c89071500320290300200060303040c801c6802d002c039100101200c212100e0746061112400000000015001d12050544907a03a51001c0e5aa240d543c501102c80c00340e4080e05c981c0d00c0702c0302d0b400c1c05845074011000301400340049004c0820803150000407070ba100180283c68405641112220101b2500014998134640c0c40000f480e0380503985507000640c4040c4500c800c1c034241800e06000e001581c004a54600610000b4400000103a881d0941002500c90030349410308668524010303100d0420490701c1c05039a1990b24010301c9803d0506401040d9614000d8880300b5900c1040c40049089428821288006810490208072880745209485401404918042da00251a11600590b100c0002400c8802d41c0c00001c103400480d2518416070018107007003000035801460764544944410111100b00c1c85583d0b01c900140341a100701080d5000790801a00030071814002c81c5020300392450340d6480040600c900700c0d0751100301d40b00142c400c04400d51808a00c2c20b6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 445087778 1250 445086528 445086539
    0x130314070f0b060f013b0d1b0b040513020307020c0d0b01060815010c2a090f060503030906190513060305070e09070f08040c03052b05090a1206060b0f12010503010c0801 74
    0x41c1c00d41c0e02040500c0d0a0a0030401034240d0b1f403040c02c2e0300c04074040d0409141d10101c00564040002880e070041c010803200b88420001c6640e03840d60302da080f1125000142e0349580b0503204908203039400c400b01340d11880c3c0c4241e4005000300386803900d05036041600c030320b000b83e100c0e0075810020102c804100b0313001521040c0000e0008165101045500e501c120600380482d8102c00c10142051071604030101203a0ba8202e4903d5865890044c01c0080505501652910382000086040751003a4946446d60300c0300c07104e480d0b0007240714204a0f40e40184a0394881c0b0002d13201e480080c0688001d803445400a060f0020100c0e0b40e190688185004040540324001082c41c085426524101c00610950322210b4104000002c00c0701404a08504552018440d00400c91a010a404102c482401c0401c101e000c0c860140fa40c1c5a5603425015110245440740212a5924045e40a080c40790008100e103100810100c002c2d00c0004090828400e8401d9901140da888a080c1822a00003112100000702c001004021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 445089028 1250 445087778 445087847
    0x1e04141516030314090c0a0b0a05070314040504020415030b120705010311070206030f100b0a020d11010914010b1203090f0d0201090e0c040e07030203130314070f0b060f01 75
    0x162482403d022071880e410514014140c08220f5a00402e50010090140e0501d003a13181580680304078041c840c00e00a02c003030020014000c281c4018240805034507507400050340b25007550004c25004205654a94841214a1030005c6141600b00442d0405101e410549450360b5904081a46140105280c3d1314180c01180900504031220071620420003030000503031200f00c01540f01d181504810880c6082820700068181c58540c4480500704091003480101c96012507603000c0c03640d883c03510707404007590307200301900500380c100c030040626161a204034046601074005444240d41109c465008400034000030383c89101e0b408510b85d11610340d5002c80110704d02400c0041c4050b0040c513013a08641e454480c2100c0ca00b20698600051101c04601000030b042440140c0394003540c036140950035030400d02d12a02400101f00002800d100c041c482c54940c600034542030b202c20680021423030403085603d04240c200716a0507107205001d06c2070248004200d5010701007030300c0700b0341c0c191040c040b00d40311210707a402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 445090278 1250 445089028 445089067
    0xa1a06101418150405091b03010905190903090e0108070e060d03030b0603040b04020f010314160527030f0f0a03050c1c0e040501080105071209081e041415 68
    0x21100e40c03041c1101c04540c0f40e0301030040e00b42604521240d13945060004002c108040100402030319075008519500351030540050b80d04442008030042825190f00c1740004005d41c054032011006444e12014405041e8001d41c11000c0f16640c1280080503602e07410605d407500e029000e40b010452038140402c00c0c508200000191150180c170307000680451440000b4583d900c2643c0039168490148284002e51074030b0b02002c00781c410242000c1120904403400b43c01448030042501914858640d164400d440c001c000722921070303900321032440038000c00025a9141c0804102018000e10542501c0a407610300003441d2940c5d22540c1c0001c01c0300300001c0c0c4e01100c465000c003100241500a00d08a248186d0445522001000940e1202519a50783c041804103e0308142d1107151242c0c102010710006507000102590351111a00c40400c6140b218101460584692108901000f050403524100c2580d4180500141d400702d08207107030305a124408001c040707400990803080114041101003142e1401c900c041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 445091528 1250 445090278 445090297
    0x90102071412030a0809070501180e070c02062b061a0f0c0a06090201080f040b0105010e0f0901030f03080a0605010503060105070f0f15150305061501110a1a061014 72
    0x21019040902c09041c10350700700300405004244d16100348002c030381703084c414803001e000c0078a030180000c5c803022910115040356100308034450900401054002e44100c414110341900036090310b03a24141c101d4180d50920309004250f5a420310b2440f41400c0c1030b154090401229694800c1d400b00c1074ac002d003a01a650304c203815403000031101300000ca60500e824403503404032038000c2c0b4001580004c54000545401c1d8000d20180c41104248100000a90b0f41c07030f11981500d50a285c00c1d80210588801b04805414080e00030342d0048000300008200191000b5101c4100d100b03685280880e00c03000104010303079009003d568049141070000540c1c55210700c000e8560540940f18580352030b0500d86a01c016000d00540940300407807001c03a10130320010b0300e0247d1804001e015403034105061444e1205510b0300c0002d000d200346c3c3c80c109402a081e80e032140100d0b4a8889084007907401554091405002800c0e10810311040110400001030441c60300c448200e0942c0141c0e2210b809030380c614007410060760700c00c8140303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 445092778 1250 445091528 445091539
    0x70819110607020706031d0d03050a021b07141815060f1216021209041a0310050a0b090903070f0507080a0305040914040f060c0207170d0305010b0901020714 69
    0x1006024804010300790155169401074032110742005001025607560044a101e2143c83c000401d03079072980084d040c00b090b01607140002e41602c80f070603400060312500302010850540106410314015020814a085940070403140c0603210044040c040c4010b000d2004107100804480059000b0306082030890351110028022440e180360008000ca1a80011086211205000d01040b401c0100d00061040646c0e10703000822500d8070a0840380203070301c00c81103200d024984442c20604546000c5200708540c0d61b000701501d110281e40b088070001010105c50320b030031007410b04060040608004520324050b503510406140b078039900d9168800d5450342d101d0101c465109207000054003500500c41840d0b028403d56940340c2c3c0700e01d058082c1041d2040070044101c2030a02105010010f0309a0008101c840d0f4406404107083c00140c0060b800c0140c00da00c44c5803501502100383c12040400705400013401d126480c2000182d8841d1004c0c03441e4041c03008201d0141c0e10648040c844440f07144201c18040c40001e05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 445094028 1250 445092778 445092797
    0x30218040507020a0201020d0212040911120103032d1403090a0c1511011a011b1b03120c03050d0921051908090309010809240a0e03070819 61
    0x428216a4115880d01c0140c20a6813010115a410300200d0346405441c0300030007100c203102061950a12030303803050f200f005595104c100c00d100e400f84282c4003a40e1803503e0603200c13980d481c107000d4054902c0362043c4495114a0718007001c200c0c00b40300403110240c12030f644d400120410540c03003412035002400d120424480c07059100005440e2081480c041c0c940580c61480070445003002612020031140302c4405079040031903010a0343c4030a00841003201c402d1909100c460341c0b43c40c0b6984040c62007000580000803c0c0ca10f000100400340000c01128400d07484201c001100140449502008440003000a002040080c41c0d040035a007200c008140643e0000c508201d44022140d44ca442c00f142140100304081040040001120800900320b140c0b81003000151801001040e10391140d01d0a0505000c0001c0c04105914401c1040c200c09201c11078075126000b0b80d2601d1810440c0e003c0300e40801150500403240034441001c015140220303417100034241840404601c100300402080460001c214a070071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 445095278 1250 445094028 445094077
    0x807120c060903031a0939030109090218190b043b0a0f0308270703020f01050405010e040b031c03090512091806010302091027080d0302 60
    0x100c1d4064491003910006000d0010b17040d13011000789511003a52091000c4010042071180d082002448040d050b00320f04110b21700003510306424103c03108102c114440101c00403400820783c1d4442c9081c01e000321004100f4261201c401b4404030412600f85800014040480c1c3d2840e40c0c40d0428402048000d00c08100070450f14041d07408070440c0b40c120030709047d4455100840c0d0100114032540d4940110150221040e1601d41404035100003000404001034800003070541c0045460801740d070101d1010070700503402e8001d1230300d5039a211800705a01c03c0c42c84803500b01c0658000e4003154111003040c2c40d03031420080340f041044002c0c403241002c0d540501074400200c41c5481c0301c603014007a0305029100050f6034206801c1c50341c41d01c4900030102840241c01c20210300607070389802c4040d112000020000d4440c0e0303110f0300120040e0082c14035803904030585159454080383c000941495500c1120101002c01e00c5003013000381411018403d560154011001d0324004512980080825031a202000d0b1000450311 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 445096528 1250 445095278 445095281
    0xc1f0c0f0e03280c08030304030503161e0519030b101d0414041704180e0f03160b0a02030103110d08130b0426062802030c040501020f03070807120c06 66
    0xc20516402d00e414840383d40c204100c02c20008040c081c2d4600450551900744c0e400750142c4001f800241c0600e40c2880050382862042d005a5410754a038040480e1882503614003030856041035121602d40040318644840e03680c4070748a41304005100614078103010711188070035903095440c8249480c83c1c08062154200d030f03494901568801501d6100e600c4020300c0c16003005081c60750000044c2c003601008200c100650340304501707080d4000d41302d110009520b10b683c0e07402603c1c00e03011212038100c6000209081d9010741140c400c01c074009001d08000d000c20b03901e2812b46000ca100900004100f500b0841041c03440307041c03104400f1301482c801c041c207901d0213081450b4052101095407003e04840b0001606012198246444d06402c4141580030354140718240d60792504c441c402010080d03140405010441e2010402d86428801d4886150840d52400c200d0142401980140282030162044c00c44032449907800204840340c407034101e201c2500300071081d034a0707102034540b41c404001040700105200300804d849 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 445097778 1250 445096528 445096573
    0x10b010912170a0905011704080f0f07300305060a06050c0304090501121e030c080d02070f06020403030e09010308070b270f0d05090a0b0c120c1f0c0f0e03 68
    0x1e07031141450719180170001440c00d2801c500e200c0c4c0b400d00c80c2061000041c10071064910648810a4241d162100c48030000e902d4003503050702901040305a11200c0750701c07240c02c2c407d08040250302e00704800c0c5080c0000c00d030291541600c04039000200d0200c07c1003528411030150140f418540140d80c94103540d0152441501c1d004e80100489980146860041000039482d055080003001d220304850f00d81600c0203404480c48030006410840e001070b0113201150b40c2d6040b5900241d000b50301501d00c01e141d00b000d00c001e4010740001c4000c102500304903102c901d040b8400714101c0b07510912062030541c440c0d449101c1688043c001000b1200102209100c4124407039512070070011706001005140291b030012840e01d0585030b002814018100803100480d290681d0800c15240300d0755420307a6442c012100c107881c010300c2e8001c000b0010800700b950294040c01007645c01a0005002900036002010749004007100e00c451076160206440403a408aa50700078240340884090007000d55111078504c14401c447c0c03500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 445099028 1250 445097778 445097797
    0x121101050405190e15100f030b031002090901082d01060308041d061905090402030304031a0412022803110f010605031c2f0a0609050f010b01091217 65
    0x1800001400103130911080694400f5900c035074020003820b40e1002c5a0300700c000c03610301400c0020010203110b0700d5010382c0101807104170182c00c03113510030002e03400c042c020b42080855500c2070032400e00000f0001e600140003508001064080d00040070000c4160200c03d00101d0300e84215500c0300c0001001c03400700c2028100034091040c04014040c64460709000790b18008000034407800180c03410f02d00088141940710250343c03054074218526256400060700d03501460f84010030a0140942d202c0b602d00b0f652410900031841841c007128030541c3c0c000203a840310b465803a800c418201d0b245801755800031506510075a40d00070308100a044105450540c10b08107610480d045a0f91100000c1106041c1001140a0014013000e5141480c2044a00812100e01383d0040c148a18001e40c1200d2007100102c103c8161045d41c03000c9a02055482c41c0040103408100c00694003400758411000582e003040c092000060416980c81155508104c000c1d40384400f139810542ea40000c58204180b40841540204440702 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 445100278 1250 445099028 445099069
    0x1a1e04061e0809060c0c07050d0303090b0a1a0907030f0c020606150c120a02070902040e070905040218120f03030f010e0106050406050d020f070510060f080106121101050405 76
    0x607082100c0010300c200c040321480070000403804000c040500460310a803c81c4c00411442d0380c8840c10309400b8541030079500190b41c001c449261890815400d603001c0b2604130301c29207801005a031068607102c115104042e8281005400c142406034030724069100b194010a20b0800050411f2094095002c40d84500030070000f42e0710203014030819280001441c803041140c41c401c180707459100312038107454500703044d02d10700c951401154110540c0e00070b0108002811a0303810441d19a503607082d0300f11103001c05680c08008503565100100340c5041500032140b11007400401e8540d41611082400154130340103003244000d0050790003c3d89018000c0c00114010000304d203841240d0750401f01100e44d0010180c1c4900b042c0a010031042201d203403c0b20907181c500c0110540140c40301024041100706114600c4001c0290040c404082011402a401101035983d230780301300b4988640703404185080360301754095140d203600b0a09008000501130700c0a0546100c041c0340c0581004d5a500120b40e0320f001d10b03c14401040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 445101528 1250 445100278 445100297
    0x17031008012007020d050106031a1e01060f08060f04090f05010e0109030f080c090a09240803070b130618031d010906050a0201060e1003050114011a1e0406 68
    0x154424040d44580c0d02e840038140c0c2079024100e2002085100e0404000d000f031203800381c0b0380706005081d4820b01c0155000031144500044205c46c40100075000ca90f00d030b031081c000400c40e8110040c0014018143e07502074070340f1845402c2c07c46017910700c6000200a01da201d42c0584c0d82a03166143c9004071002180700301c0341c201004080c0d15019080d259294541e400c180c1c0341195503800720f83d00140c1c24070801080c2c20602d01540b100b500e229498811012004c1d084a002d4100140b4500e590f4010003901c0390030944d034008060034561390101403c292080c0c032150b03070042c0403c601207031140d4011a08882600303415240c4003140e54401d020703500803c1c20158120140c1c00b80c4414150000030040c88544e034641c503607560381110340000e003020400b4040c0d6000c011001c40c80d103805a000358400c030058180031800d80003030b14207090310041ca9662800211400c0d428002d0514601c0030013280903050710036040c200d0038416103c42c5807510581000120441641c80d6070341843c00f5810510007000a028607950f030700b410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 445102778 1250 445101528 445101539
    0x7140106260607050412050709020f030603010507092301110706020c03060c0f0307030b040e070e090c0108090c0d0f06050c070b090a0c090f020c07080d030606050c19170310 76
    0x4110038260180060381002e003c2100f810f030711400f01c0f41980c5060b16851300003240c0381030007490015103400c42c500b800c0c4002500450b404a01c80998840c8600700c0090000369a044400c4030181140c1c8550303d0100c46540b808640b000c08800c0d820060311043c0760004c0810704200c19a0b1421600340e008c0300140e0818a00250350782000c1c0441d680c400d107448036180c608803a54500c12440d01c0300a1404c0f080560700c0c00c10008590320354000c0c0c40200c41c04022528029100e112100e4004020f6071160300d507125410341030b0015400b5405142c400c84001c805410500c004800380000420001c1040340c40321082c0c92300000050052155a0041c2e12b61600d8584400203481d002458080140c03107691554400302c506400952823000d10000d64030b83d4500410407603101000100030f4055000c1841e0f1500410300c010411420002c2c124003803046581c0c0510806644040942d840c1c03060068011300303900f003000c58080c0224221b200da5100ca01c201140794080305d000a01c4040c03504165590054120a40c104210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 445104028 1250 445102778 445102829
    0x20d09051212060901060f0f14033102030303040b070c020a080d26190f020a0309020f01080601080714040905070c02030f030a0f031a0d1209080a0201050f07140106 72
    0xd003c82e082d80c41c9009941001030190040c03a05240c01c00c01c20a00c0c2135010807091203403240b1580810390040d19a22402c00042c03501d0303117080d0354513040b10101c0a513070000700703d903841c4400010058000d80654a1a22245c45002c40544000c0001c0305000d0a01c1c5102c0040c0c0b02c10090100501028014002500b50f00d400140180300540050307507aa2820441060304e031400c02d204940010600050b000241f2403036203270350003901e4910502100300f4808186c070f16216800d9049207601520880d020121031240c0317001503420b2401960aa4005022400021001800380400e0309114000000850500e031761231042000340c40017101c4403000115040703d20400c600742003054051055180001d542400c5040310001c14485201c40030104040d01d03180402c84c006c40902026940400250084080114900300304d8510858006a03100081c80c480c00024031010101d080c0e0f03110307941607680300c3c507200303000300c032062280c014007020354071090910303c11503602e071091003140c1c0101000031900d207240040181c0c42e103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 445105278 1250 445104028 445104031
    0x150f070b0601080601170613060b0717040f05010807020f011a190311100c0c0305010b1306080604140c0d03020f0111090901090e10020f040f060e090a020d09051212 72
    0xb41401142e0060005070b07a0009404190101910294102542c40070001500c001c420480b940c10755261660100782240b0031001030401901071704148040300070b401e983c0300c0c0070321a902c11500c42014800050115603c54850580c11940a02c115880c10355801046400c480101b440c08020b610416004680d0f41408038464600150100898041701d156441d10006c4031ba00c110158494000c01e9055680180600300007400749402000707200c0c0540c0c507032400c0c500a150401015100e2303064056100c80c0200f05003d60019983c0481c0904800d8666a4480c044914502000403141c001c0701400e1942d502d4602e00070071014081d038020b003072076a200d001c0301c0e0842e000c1500581c150a070401403024a07848140740766045a003a0007001132103000c101040c0303003807042643e02045001d00001d0154000f0044034050000d80344810900c02c12980e0b81c4d1810b50b5445544010242c024490a0000f2814401d69015040c4402603007004607103003400d0703541d2134208205d001404030291f002151b0001030418141141d0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 445106528 1250 445105278 445105291
    0x10806010f05042f1b0105090f16031502370203070f02060c01150b0d0606050a02060a050901020906120406050105041e0203041a0a0219090b0706020306150f070b 71
    0x20050100140044595042e0842441804c10b1074420b660300071588030350845038034480d041d0a140840d00040400d034042c0c0360980f800801340c400e5041400b240200131505e4072000700b4109120f0005855990341d0130020390407407548418250309022101107401c19002074128005040700e15039900300710b0f4030407003070011104614104641c01032044500080b80031034400a02501102c0c050348602058a245015100300000880c40b4084542d000405188010242140d803114a4040c481c054035081d00f2116400386c14101d90040c0c0c0501c0115204182583c803240d000001d00e00098500300d265030124842e13502c03c0140c000010f0040e0100f00c02d004003403080c1c0d8003400c0d00b22801e0004003030880071400d20380c03014000520103d500101040400031072a030b40c00010020b82c500c0c3d5460749030012541009400070313600c111104585040703141c42c0034810107000c4151b80540a0b19818130215840e500000e40009103250b800070100460f81510141c048041c11802c084401d49035030750105450030300301d500b0000c1c01c071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 445107778 1250 445106528 445106531
    0x30309150613112218091a1e0c0409060b0301050d030f0c021507060f0b03032a1005060a060807051903091a01090606020303060f0103050c040e010806010f0504 70
    0x140401561642055002c6400b0082c01188015040b150000c5a1040b0b01c09510000802e038440644442c810408104039805005440f980f041d0036010002940c10442c8014400441c0114000c0307510300c045e02483d04080004464022052200c10341103440340c00b42c134082e007143d101103002c000c2e10665000f035001900400702120b007954500f00100c3c07200040245c004040c81841e210100d0309500c11468a901e250700100960b844c00306c007261a801d542d200410580d0490300301803d601e10304200340034004001e10040d0003149404646501075031488140b007100300d80c1c103c03544810683c8000800c511004480309110000e10b83c02c001c410050105401d030300c800103210406080001e501c0d040011f8900022a041c0c0c02c02c50b0640b000000c80080218000041c03002ca1400038081c00803103d000310301d040c0c403100039081080c43c1e240c1c40281c0c2e480c00300300c5a090340020200010b0160354840e41102d500440420440b03030900382c5480e154003601909811108142d806017004200c4024407605010091505850 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 445109028 1250 445107778 445107781
    0x30e0c040c120f020c07060c0f0b06010516060b09130c0509190e010609140103110108100b070f0c061103090415080715030b09220c0504110301030c0b0c03071103070f060203030915 79
    0x80c1c279a94001d0103040a8001e0400400058041c0d0080007181e82c040100100d507100140203180c4040280002a10355001e010304c10001640204070181d6039004070b400644501c5511719000400201d0031000302540e00403000e071584100c0c0c800d018010b42c0c006824110000c5003035810000104211000da400c0200304186000041002c5040856013010030711082c6880728031b075036a80c41028440b0341a075100010001d000141e04050103a2041100003040c855680106095070b5210121a65011441d040102d908104102c504c285401d40c04005107c903003e400c8000700707a070355821380d007041c0d034070fa200e8014102402c2c00a28440e03498450b000d2100c1c0103c51311021410a44103440704001d403807800340344101036900a00188101c0c40b400d0001400001c0042c4514002d2401d040210b030420b00c0111406a040c241c00324070248600244e070b0b81c02c1c500784000e5052921640390b41804142d612105a054054010040b03214252001440301400b801d07001150340c1e04294818a107099030004840b50300040080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 445110278 1250 445109028 445109033
    0x1303140606010804032309060301030b060111060601021902031606050a080106031406010e01120203100e0108010504170a0311041203120501150f090b180a06030e0c040c120f020c07060c 81
    0xc9a56190b4031342840412106c2d070880d01044880c4148100c140d44103030044000810000700c660b06034400d00c030a82e112580800170141c00d03075580d081552020b015030094540000119910301d820350388280018200c52040d031140300305207140b5800da0007101c00104002100840c039074100c5c0c802c0303004002a203010400024042084610b010018003601c0c100289a889940280e11030b025030103070300811704400c660f20300380f035181c0703800c0d0790114824000783d0022035000048911040c41120700c1240c1182007154500c000c410082070540c002445042850f58549280e680c011030000900080c041d075108503c10541b030380c18040d00309009a00e0701400d440c100360041c441c115402c0400d101d03c001a08010070503030040c0f2000c2c2d500d0700f542e4200c01e0b5426030118560140c0c1021000d41441c01c541a04c0d4a01d5550b20340030201c0a032241030b0340302801c51b401003a1900d4682841d5118503255a001e180010003030b00c4100c800e609440601c80c0807090b55270080b40504040ca824009100100880c0c180494001e03000d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 445111528 1250 445110278 445110287
    0xf250c03080c01150603020307090602071a0c0717031c09050c01050c0f0102181f080c03040f0b070806120c01140327010504060f0209060d090305130314060601080403 73
    0x5000040600700c02192003a00344401350030011443d50307001d001c0c80702d16455400040082d002128880005582114002203c0380007040fa43c0c1505c40070780030049070b000b040c01c60310725550107611003a62502c10000001000d102e12520041c0240078031026503950664031144178440c0030311380704400006240030029000240f002442112490007820429201c2d4030481c0d9060078013503e411501065400054061000281c901c0c0101000300116001c40312624007c010030311618490305080c01181d502e4000c52070340d40c0040c02030341d80284500d44014140d43c0c903a0f20f801101106442842c04120500103004031845c11032251460058514010021040b40ca4002809100100424240c1200010214840011100b403900401c90041e103481208940180514002c0100311341c1a192140703840b10b0415103440900071220b166800518550030003130b0b81c039140e2004098180040301480001c1041120048128104200450140140303c0d02c0914241c0400d0a1540003840c1d6410850070b2005c000009400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 445112778 1250 445111528 445111553
    0x509060703030515120c010f020f1506090a0e0a24062c1326070b15031c0f0e040e030c070b0f1b390a140f150f25 50
    0x900e040c00e403207231910f10141d0421001c50550b4500d40104200c05609074000c2c20030a000740b0081d241c115059070b80905c1b003003c417840d0f60072120554100080707480102c2c02d50b440082000c503032000021017030b0724034172220130894010b13900420328a03031140c0c1c4150081e91004c2c6800c80c004100c0301107140c5d900e0103c00c01c1c8507840c583c0030010148015074034154420f8940d400c8207400000805d161a0f901e01c10b038200815000821500000c0700c680e2549002d0060a0108821010400400801d0950b50300044c06580c0c2d81c0118007100104099510f40384050380c0e45016400b4500c071280091170b0f450440d1144541000304d10340003000d0000040216050702503030302c0211000c0403021444800c200000038091400d00300c68224038600210740150900000c40b562403040c5100602610b4540206428001d01018294510a0085580d44000e654440c1d04180d0070005070792100078281142c08134590061030940d080840a241c03012070104000c010300b0070b582001d2074420040c100ca500311302c400b035039541100c500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 445114028 1250 445112778 445112803
    0x20304060c0f0203010203090309031009021c15060b090f01020601050609060c15070f031802031c031e050a18080708070f0602030702011401090c1e050906070303051512 74
    0x814618400d0024140302d071550a68014025550790070610860740c4d80b9001422241c1c0b0071702803080000e90a0301d140c41001c0090303501410301401d0613a9807d007071340c00081d07180054a07002448a401b03000c0e41482d00c42d42014049d400003a6844d070404074184a03e10303800070078050540d4040790040c1b080b50760344820380b440342c24100c0c4c04c03540d03800b8022145401d003081c5a1030f40b207a40315441d00f4130056a8105070004030f01c00d001c0d0703000c004059510300081c0d8078003400c4401a401d0741100d0079107449201000c00c0c9604441d40c500300880c0c032110030000c000800c0c84c1250901042070f500c5081c00005c4406008000c0846540d2500c8601c0000c0f0ba11000d1051142180080c01020b000600d0810040e6210340000140d070401411502ca03d05072030003a0103131041c00e10081001e90b400c0c1c00071900502038495140c0d044001d03a200c240d102d156200190740c4050382d0504005003c028003500020b0340d1a0390040004500c40d0368089218140f00d240601d840c40c036804c0441c0b146c00c0b044c0a0341841070001580d0b405000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 445115278 1250 445114028 445114037
    0x161206060c171905040806060a030f03111204030b090f0c030d030f0f090f05150702030403020f030c040618052d07120606050903060c12060d0813060e10020106030302030406 76
    0x22049480c401042c0300f18031054041c110f00f00f10010105401070082e100312038001d8180c585590750358041190360030b214000100035055001a40c804240724101940320302c142d24003102e50303030f540a445500b050781081c0e108a503465215820418207040074041007446400701802003555034411b03c00241c81d90b9100014008140d564042240740410507000346c40410100c10040004040724100b90700e21b030011290948042c4100c000d1305010130498061188580d149a015606041c215820000d2000d481c100c000e50610a6402d2040e041da84ca100701d030010015002c1c0300b11441c0417641400d06894004010341c00a04c58181c003031584000c1d06041c040000741a00b1010f03640e540300c200580b81c981d0400201d007405c40c0b402c0400315095800100804860b1011800c03595240d4413241c0c1c50450b8402d00d00550003041400001c2407541c204180301111180c41002e15505000c401c0780140c0d04200103034044800a10909115240b07400c4c0901d030a40c0e200c0d000e2000303001403421520069075a01c81c0740301c1d900411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 445116528 1250 445115278 445115303
    0x10b09071d0619030c18090b0409060212010303090b0a0906050c100903020304060215100905040f0503130303080c070b01140f03010e031210060f030207021305161206060c 75
    0x3959140385980448030050070305441d0180043c141000100a11907200824540a1042c01c102e0049180c0c910704940e45003803201250500c2104030181c1209540c00f0340058503425800005100341c00504034603419070041880d03540c552309000f40381010652151038401d904200c41c0308140c1d0301203046411740302d0b1401d0032962107250307079245882c248030140c0d01241140340a80d42010990f02000074400c40b2140e5007103846103440c0e2582800000001c1c1e610489250000d02c0c10020170384c0503080f81d507115020f010715100c41c0019440c1c00b030459100203603200c0c1600109605000301908281c8842e00404074030b4810741041d407a641d40b43d0420b10180141c074800c084664803040950f64042c403965803958050003d0014940028a4654941005900305c0003070b40d5030000202204281c000450450300e0980d5400003807442e00070141c0013988a8842680c000d00381034250300e500255030044900411042171314644683c0c00120041201070307200d5021511906002c0104005540180d0130702480744c201c1c0700710000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 445117778 1250 445116528 445116557
    0xb09070804021c12030516030e1906021e03040506010e090d141c270215090a03020406230901120b090a0506090a1a130303150305010e0a050f010b0907 66
    0x140c10769141c003d100340c84013080030401ca60f068001c0c6000d00c800e540b941e00301905101096090320344170b2a00300b4240e485807240c0011a1000c0780101d04e05800340400524003994142da03241c140d25042c1d2807000e486000000e010801400b082024010000301c0c4070b030740840c00c005100540710303250044d41508000c00d0116010411051004641440704901e2403821614941c5000001401c2080d003428402039540c0d04101c4003003043e50b02007440d1a4000c010079070380307041c10403504019046180070a41201030b403c0701100684070b511071031000e0b00d5070818089500e03d41c00a849943d4034500c462600443c0c40c200104840414185400c4199501c40902180c60703031500701444c0b0340080d80c0700180c00303032140ca0b040c011982e00c04900007100c01e01510140680303192900426000c00b1041c0c0b016140300d05514180404031348243d0161604100110940c042d6a07a60780301d103400d60b004a813290f5810380001100c182000030070812214403180f51b400034040440700000280002400400700c40910a150320907905 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 445119028 1250 445117778 445117819
    0x151003172a01061d04020a06080c040b04030309051309021e18010312020d020703150207030e1e04060504150902070305071703190e06010303110a021e040b0907080402 73
    0x50440c2032840110459041c019480d0191a040c82004090008401c0034460034030742c103a0240c8102c0e00500302d400720601e130150440340d41d40010040e20b4106001e02012a20414510013000218081d50b203120144d0b007410200261440d000080e50501d9140000d10030042e1a4071810348241c41e6507034000100191484042164144640c60100780c402450380080204080f0030000060341d8480d81c02c464408000900c00d99940344e407800040c1540d00c030228150b41d403607400d80003407625500ca80350a0b19601c003408046203050382c1028040e42c0038000c5e42000800d40c206840380c1d07002044221014061340c91150074484c50340e815406000d00ca240c0006210040c1805041243c82482e4030124408810104501c481c0068000303507008001e8015404c00d0440320007490191400c0c103450000038216a929540c0c06942122101740100030600418940c880980c4c1c0d0120782c45402c402d24549101d00d48040000c101c02c47d040399490f54800d4422005112065502020055015505803420040450f11895005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 445120278 1250 445119028 445119067
    0xe040f02040314010605030d0519090305030307030615030c050f0306040e03130501080a0603110907120e01050604060807080a030c080706020a20060615031506040815100317 76
    0x210998000503001040042040d00a030214480c0002001311903112400c041c1ca03812110701c050b001038024481d84010400347c80791350103001c0c02c0e03040c40c203138040d030705e0746d4050541e0400c8680d9004a9a60310f000c011190a081a030a542481c80c50308014082c0b0098001d8a00d014041d0070580c2a074022001841a403a5580b0070b000440041086070b0700c0b1843c50381015900180d500615000500c4400411244c4c1c0d001d0242d5820340b03500c0401c0fa0700058450060090407103000304454204650840c40a0004400e48200000305c40d001c0d001040d1454410244001d40725242e010900aa1281c85c1c02c000b007803004103d901c541503040c07034050603081190405d507019003e060070140205100007040f4100381d41100540d540f001c204005a20344405008600d40c607440c007140e1440d00941d010760000d007540001c400a507401105103001c900c3c07006041004c11007540254000c0c2d001c0703602505207100395004906440d40c4c042c00007820041094107503035031070b101b00940715400004070002241d05491040c1588601 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 445121528 1250 445120278 445120301
    0x60b0907112a12061905100509130c09060f050306040305030c160c0e0601080a110313030207120507050909060601050405040c1e1d0a08031909081c03050906060a060e04 74
    0x2c2c50325045600d1a150300c03040c1d84c50741d01c5c000009914034460780240079040c800d10030342d81c0d030300c0f88a40740406021342d0000052211104003a124000c2c00040c100280b280c001d04200030001070940e06168440310542c90704d4011500c20740c1710004010029a0000849a0005d40180c0d060346031a001c0c018522880070031600200030307c600d0f04010070b8588884030076900c503110903660723200390792a01a00c0500301c80c1207010700e6900d0f44041000450580a081400900750301c02d204881000d980c504c590204100f10000454141d00003a40801451420a420340e1304200480c0140c06e0900740000080c0a40c4154810f540c090398072410390f01e4a66001d82c1c5c0c481c60044600702c2a55518114000040010601c83e4032031540e40d103013802107202414a444800c00340c1c1c0c030b0074005515104900d0020901d443c2c0080c0b2a8041100611000c00d02d030800744001d0307050781c5420040c0181b44031181405002d480c0b008004010031382c01903003004447c2e030360407400d80e080740d4860424068030713400d0301c0c0803402074400e070510f4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 445122778 1250 445121528 445121539
    0x90c090c0503060a1d010e13020406030f02030c1905010e040609051906060c0b01290c030310060c030f0c050705120304030c091103190b040504060b0907112a 69
    0x924119400c07000031485400b0484140c1c810980b00c1c05c1424031031350780c0d904841d401107001006102d16550581500c0d00b0100703080700c07910a659194001401d4134950303041145c00b10b1030340c8405011400c00b0041d170f00300408100c5850700c0481d400c0c0d90703202105880b4441c1d14104a016003d035503a41d1659801180a410804414003840c5000c00c01a6282c3d2205c8a008440c030740f40100000e10644100100040c0c00e0344180790200d2640303050a007020341a00e000040c01c40c84007114000c154904854001c00700c11101d030b8003450720b9203170800c0ea6001143c69a400641400b015a01c10710001c0d0748580c00c143c0e01c0d0b8030340c01d04403461242400e155181c12a1908200e4201071100780b490300c4410000050800c40303101d1528a043d07a51585000e009503040660400180e0b0018004107080b2842030b5403160017498130383c0e80000c041c0783c3c2c800010207440007a5010344050350740f030491000c2818403480460b4400300c0c50402034401180c84034020b545d08648900020060303160b00034080d0140d0188024200c81c5070040c030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 445124028 1250 445122778 445122791
    0x151809111816140d0203040c081c090506040b030a02030a0e0d0210050a020a090b0f0d140103020306060301050106121d0a060e070f051f0201330e0c03010306090c09 72
    0x20000c0080c58195081c501d44420410a594098400c078403003080030462443d0b607410301d840307541d1000203904050000c40300c0441807240482d0706101040303401807042c1e82034011140038111903005410380426800c028000c4c80100424084070000000320790304203548640c01a0b0f00d56440e44020300900c114101d0b808640140302d04a01c0c0145d00103140d4400c6030f00c0c4002000760791600907400049125a80c8414086203c40a04106170700b8014060002c5c484cc0195030f62074074400941160854540a104005500c01d007001841503050410590f54082c1c0300b40c1c0204030030350605001502089040405240c07980c0c44000581d01c1040030751980714119020740484805c41c034249410030182010f804400c016101d0050001081a010414102120b9002c0d000c00410303a41d612038440c0082402e41800c007559250f0003200c03903000102c07107500309211828004030903d81310345544611001850380032140342c079504828028001d90034003c41c4d045030b9121000169527511440d01005242c003940c00704140924011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 445125278 1250 445124028 445124059
    0x2450120030301050103140112110a09050702030304060e0f1b12010228180e0a06170d0e01030603020603240d0609060506060705060a0f1d030c0115180911 68
    0x10b54142c072000d8901380900c0c1507038881540c02e41005d200714500300e1450b02017000414401d48200c2101c01c40500240c2031551210003000c1a150152810300c0107901c00010030040c043d05120f0144010007501c0030f0b180691010203030f10b5862240ca08801001c00914142e214244d403004403a42101081300000e40d101c10401090b00c0b410820054003800c54100c20402007036047c03180e0300c840030100a90108600745805c1c0ba82400000c44018901021507035a0b40700800c110080d00240d540c00030425000740007191040000030605e130a2054524181400d00c0020710069459000361380d400381511180d40802400c01c4003074114245a4400c80760401031039078041e81400007541000214a02950307007888140c0b2a401441400d1040e500041e01540294005c00c01030714542d082484c04081c0c240002c50010050400003030120b101072313a036a00c168800104401c1813002809184039195605900d10841e601d0304038444078200728800719090751946c0303201c0e0500b00464103140c48015000038240b00c07904007650 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 445126528 1250 445125278 445125283
    0x1030e0109050a0c140a09020c0a391211060d151a0702010c020105090d080a03060810090210120f061d060f06190504030209090102450120 61
    0x20f61040c1c030400140380c2c02040c030700030f413521401d00050080c00c04640240341403440002508583c203882c0c03007400342c00b102d6000314449246540740400004519040c0d0651000b254416601002e49a0540d50006008008001904009042190300a0744c4100711420003800240307240714a170708007855907240213200040c80009075090400e49062101500d1000400800e14402d0b0144090082c006a40d5420301801035100b0005440e501d4800b91001c1e150900c956103140180e006113500b2000070380e6030304003006203807800c000320307040403403030000422112b0510740105668000c0c2c0180a404e000034410300b45c8071650360b640100d0340034001c00409c010142e1180c07200941068031820441d4004a2030001c1901460601d03807181328281c0041c81c281ca0020742c680b18040b04070222902d0001d0080500000026803140a501407003404440001656841f00d03002820f01082c00b440d000614000c041e90900b201c1a8001c154028080c0c503214080f203c20030000101c031900344071204030f01d4580d5000c40030364016100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 445127778 1250 445126528 445126543
    0x160803180d0206271009060b040b0a0e071404090204030305131d04230a0f02040608060708011a0d02070309050a120c030209071803050a120807081501030e010905 71
    0xc1506444501c0d142030002c07640c41c030040e1840c3c076030845103c03d81005112101500310103115020241d40c00b00c4000030280c0115072642c042568026115000d5400900c0c0511a4116a00044a802d920281800d038242000c54000b080d0109200a01000d0080400201d0a4070f00a111040b81555540d0702da217001001078101c81d9142100d000d040f80c0c0805c40030030301000078100c00e40a034a584e02a40d215211030ba0382e101c0311803102c80c8560183d07011001d00c42d0280002c0213068081c50f594400513100b4414801101c5c0c0c2c40e031048055400c881d0500c0a150360001426046610030401c620560b03a4101701460382c0d100b61100c0502c2c0c6171002501130100f40e00107544a00b01d900842d280700f040b039900d90881c0e800032800c500040c4074030400b00c1d092006207032010b0039030f4100716a40303450701c00404403100400d0350241d0b5400550303140c1d0181d44054100700c0e0103043d05031405d95130300c0d1803040c90600c10000f070040e12003e0125400040b0307090141c50181d01c2a80078051008401000b403200e0501ca081042d1100c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 445129028 1250 445127778 445127821
    0x70201181a01090e0d0e0a05060d061509150513050d0f0b0c03090a1b0e010314010e0a0308010608090c042d14131a0a02120f0f010506160803 62
    0x8141e0000141515240315103107042a1000180c40940040a000c580e9182c1e1001260b82c05084290003144a0311501c1c0a40a010400000040d40900f012001c00d0182440c40800040003103140091140f150000303580c102c5c1c01ca240c1016034071059100110804480240c109540240d9032412103424804a00407044089018030782c8008a0b46071010035a0141c40b046030244059401005660002403040101d00100c2007002d803100342035034569081c003003d02400e038000d0341c10305038804804180150a10580340140d90500017011190b03055074000c0d0541005108000034001080c4c000b9007002c400707100140542400800400804604505461103401604c5159680c0540b001c0780710150007940c03154040c1d10380f482c040c0d0481a502c1d13204030003001c1a122401c03a0b98201400312820310b414000384480c040c0907040000350b02c1d103501c414422103200d4000c1400205043c0c244c1440003080c01140c045040d84c0060725210b03507400d01e0100311400c3c55060706000304050800000c1141c10200180307150003265 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 445130278 1250 445129028 445129073
    0x906060e0910090c0c030336050c0402030c090315011809050f1204080c090108060a05090a0f0506070e011b080c032115030f030a0516060e010c080604090809060307020118 75
    0x407081c01901d4500d10050b001040e1441642032298135008c540300d254055034410303401c4442001d18100883c1c280e800580340d40b0910301c0b02240500d9903203400d1026a444200324407020b0015031402040030895100a0b6a0160349680c401c2c0d10405d0040c24010703404410121f5003141e0b1099409a240b00c40c55000d0306c11a80140a0761040800382c2c600041071a04807a200f0f40140441d80351302504100030a805400c00c096481030860070000142501d80760802c6038000c601914643c0b801003c041e100e940207617036141c10045087c6070030100c0714145502045a42d002082e103501c821491715058518810503901e5082152031841c0c0c0506c5514410100b841404610b20070020505d101c000d159a0300c1c2c480306030003501d07041400100e03d81e911503009004402c12a213a0f120225080e6100c2c0350489031200c5101e013259440f204c0c050340442d00580c0081c3c05c248191000c02121300251600074240c0545c1440342e2003841c002011905080c401d400c8480c64030809400c45403046620710f0300c035a10002c450342025019 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 445131528 1250 445130278 445130291
    0x3130911070203100b0a032310270809040207060905010e010b0303031302060d0c110c01020f07120f1a071b0b071206230103060906060e0910090c0c0303 67
    0x18442001a07031801980070b00204030301800c01c1e0252000c2c040064925400200307440000011640701440d0041c0300300360380020940b4021111000d03040c5000c0618000c0c440d814290f000c85100d580694a036154982c051800705c0c101100e28000e0000c0c840d1140c03455101740040303a010309121030741e4440214103201c1e90081141003100421182a04c01d8449220750642051000540a105102080030220710083c0706506d00030700c41e00079070100c508000c1c41d980014002468045041030820001e845040c00740000c0110300c0d100e0000959407407560042c2401c44005051810030002c40995a844284c0d00c500b1603c00d0801ca44040c050046007154900d00250151640340350807001b440c441340703031142c00a00d040708680e81da0720f00307440c24050f11005030700c03d558610b0002005d1510f280306200c003410004510254848280004042e1110b41d007005245528000080211640000c1d081c140300c00c055460301310f02da603044a0341c210001e45a00003213203d4240b140c00d40035198000408a0098440d44081000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 445132778 1250 445131528 445131551
    0x90a05010b1902070305010906050105040c08010513020a02031b0303092109060315040c0f021002040b030f0415050408040303200c1302041a030901050106050307020c060f070203031309 81
    0x95410030711400085000402c01d860000c28a41c6032540b811206004807400d4650f00e581d02030031030321001001c1e200241c1c1c4000500c8245032501900e0000e654516202075554101800144807804944c5e00c500b4250b0b0001d14800014000d04c10b03103980c030f00715644501044408074480b5850b54021034580c15203014800500d840004d2014400300d1070103070440b2007420100759034284502d990001d82030341d180380c09001082c04995150301411107008030740d03521103d03a00d40c0c030003010f07107400e1f206110005c82c0707401440140f10b01c00b41071003540c0c2c0c40031100c414808551268207180c1c0b0030342c011401109404d41814100818810804d0007001128071a40d00c080508402070060a01d280d0142005016a0000f1441030154548080c1c645a1507052260052820b561032000c00c0c1c19491549407050505000310030020004400c0c400c0038010022428000d2443c542040000e441e00040458035104820105907414140c3c191000d84142580c06811265a02601400c010711889280714090b444e6041c44180c20300c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 445134028 1250 445132778 445132781
    0x120609030f02190303050c0d0906061403030913180f0507140a050d030807090b1308060601180614070b0f04060c02011b26010303050a03050a09111009090e0c090a 71
    0x910f02206021070144001070394048010b882c0150640c00d01d00da080c00507504103ca680300c2d151000f481560b001400314600898601c03292040c0e00f20030300c660003d201c0c0c2a07081e110700358040c0601d2010340c00003480c800c0c1d203209a00f0302d1128180162020361904072040070004000b61500a50b645140044242083d0a007003000c600301c28029240c10807400d035014030009004a80c01500608241003030700d0320380c0d01e0321020450350304141400c00d88008202c8007041030400074072219400220a00e000b51035584078010305404000d50784158420050380428600410801d00260703201c103644010000403d0030042c100c124540f40c1070720160384039480c025204a01c0c030b0051080c6076480c02c0b00100c40c16548900c07030083c0c4102e0389881d001c011580040b41d01c08240501c0c440140c0c080e40c440e49074281c0380d443e02d40c4010215003004280c51406442c003698030340840c00351800c8185c044000c40743c810103c80070803402c640c07000c40d41d803003000c0603400c4c09e1004e40c0c40000842c04004000c030513910040c07107aa031190302c4030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 445135278 1250 445134028 445134043
    0x803090c030703020d260c1f06080c060c100513030e030f0606040b060403120215130f080901020312010b0a260c0c07030b011202040c17060118120609030f02 69
    0x1703500043e2010300300002203918402e0800d41003140c0d080a14222207885003442c3c2e50001450405580140111014585045c00443e445070b6596404105070717400e092100d079941d01c10460840c8079240104000468040800201ca4040031001041c003150070030705c20000c6a08038060080b400714003d80c0e00d0b0b007000c0c00c000a0300703e00c41c1c034420010492a05c9020600c07000700643c01600f03400100c20080800401e190b880c100d000582503034014180a000381c541e0f4149454042c0c05148000840200c0101064550507603109854008464540e00c0040e400142c3c5540300e50503a260944241c0c80001038402d824801070300300d00200d500c3d0540d128220742a02e07148004411401c480350018040031910070ba8003200902054580082121400341d104d0311981040c20f001d81c080700c0c0050300000c2135803c60409000d00e444d12041814884044844011203c1c81c40300000c1001e410006c80085c81c0c1034030036101c0b00b41c800400c095182442c404045060640191a40c04816030110340d2003843c10b84c18910009001c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 445136528 1250 445135278 445135283
    0x10b090627010e160f080f1003020d03020609010c0e0306130c1e0612050601050304140106120302030306210601030f060b060a1d0306060f04180f0803090c030703 71
    0x10029998000411000e0803a514110400800341000780c1c00d441009a20395002c1c0c80c140284945525004114041c0e2100051801040002c201034490100e40c00641190b00413085010003a1140d44040c82201c0443da00d610107544000307000420018141c000c40d2031340c000c0480400034450090342a50175140d44a62a1900ea0140d220b540060107081514080508813403081540407101039072002c0904021841c5840003500202a0f107080221503046200f4032140218100103000b03a290a0001030014000240080e0800699a80040704040203512003c05000c4401c6150f00d05105c03414025075940040344c0550007800020981d000c00d407200d40c544110405810010310703070740e82190360740341d261101c419007240c186454648030611951240c000c1c01442d40c990382c608400c3c0e06400c00203048803040c2030810b40650030100500c03410361501c100c80d41610030195070103d01b81c50030001c00c02c0500e00346000134203182504405402080058401140202c801d081250000702c1e01004240d101e00451100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 445137778 1250 445136528 445136539
    0x24270e0c010804151b090f0315050a060b0a090e06031b060f09041d15071d060d060e040b010609060c020108091f0204080d0801050307060327050105010611010b 70
    0x50000a600c00c1c24242e43c4a445881000148200c007030380d01c800d0300c4101440b90314850300c1560241d1059440349411000348058803402c02450329617101c02c1071f45580c1d500003415141d10758000881d186c45640090000780340020304036a0b50400035100a12545142c001c1e201c4144200000c18054680080c1040400300c221080e40c81212042081144c664410b071345003503218805100c1c2410740d560f14401c5400001521802d103041c95a480a800e0a02c00859418800d0444250611000030303071001c6030903c0200c6180d501180d0946402c0000c031903000c0d448040d0841801c0560100c0e41507609084140034601c1602020101e90f00c03994252603108550080d580060403810302c0101640c8504e2902e0740103e821400e40e13226594107401080056a900200380754150000740402012804014800c03070600d05150801003541414002034a4001501c030700e108040d200c104103040081e0544114413103506030040c005107940030b4940035001e0b000c24410000031980134099100354038418000c0c0c40d44184010704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 445139028 1250 445137778 445137793
    0x1509020f04060c1509051b03010c0f05030a110d022802030306010c0804090e0609190302030d050c040e070f08010b070b0a1a030316050607020f060a24270e 68
    0x41250f0151119030140d800c2d44000a581c034901905200d0301c41018001d4014202c0c211002c10303180688558928090b0080c0e00d07164800281a030710542c2c000000000f49402ca543c1d0304c1d810308078005000c958151a0503030000003003554900d001c9a000f091454400c5d046034902421a0795803400c2190601800805a001000020742030340c0300306005458188a141540c1c1403a45039140441100c0404040c0071055002005000c4030000c02c020310a441083c148101c0361320081070ba002520381c01480041e84441d620740d40440e1854102205580107402d004000e140d441c2f40030305e0014a968008051a004034500c00c0010640071001b5003180c5c140d41d041032011180351100071f104002400049400e90b5194104074041006070b6040c001402500c80501440102d010035041031410300e08050540780039540694000e5500700c3d00440d085900907003541d800078441c00b44102003034601c0040c50407810140c0b178003074020031000200340284803030840d540b03001c1000d24840340c05e140c1110b6041820900540c030581 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 445140278 1250 445139028 445139039
    0x9060203031506070b0c07030e040e0307021201060305010c08100f0614070213061d010e060f1309020d06020c0f1b0d03030b060d020910020312040b1e0106031509020f04 74
    0x150010000101030505403411280d45c41d00c0b02c60400c2914140342e94100001d00c0701c1030541c0021409000309048070104400020600358965070b10803c00c009001300113107400701c06404003c1d0300810085802c00000d0100210b07450008106640c2105c0840304880724400114104822948150503203440e034498202e40341c040007d5019540021104a9015141c5500d01032a4165801018001d080d0a0f4486209090f0240355030107080c4148c00000400c04d0b51001c01500d5510404bc4171400807050310156880204102c43c0006819900c8001e07402c00d030041c00100030441d5a034001c051501880b0203866500f5203000c40f0a480b81e10074a090044c02c070304000d6a402903d8144060070307000d4841d040c00115000c14401143c10754005e400860b103607550201b10f50303855040161072503c0b101a40e10155141440c00595449a00400b03030014014146200c001680c602e0580c54406401a82140d803803c1d560b510600100a8030213034191080b411900400020000c0290082e5480c82c040890168101800d08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 445141528 1250 445140278 445140301
    0x9010b0d150e0d0e0307050411030103030503091203010e0a060603090201020a03110c0411090a120314071e0f0c0b070224070f05010e06071b020114130608010e070906020303 76
    0x4880201c4650303100d540101c440300402020309001d0071600c40112414081003090304101d1542d221174011814812051050b40c81a0101ca0659a05082c22034a070740b13a600c0e40398500351028645000000000002060514109a42520401843c101480301540314001181549e02400000380541d101d42c4100303000900079460302c4034178400441103400742e64814001238260f840006002041e003d000a00305014186240d440000c2c0c40c0808143c8481c001603900106002821140c81c001444003181030010000c1c0545140001901405010340341c004034100003504011880c7e0445021060003400610384210200b6501e812780c005015404000d40d402500d115107090b845032800c0d052041058200150246940b220f03071500442c000101a18400c1100340342a00140070343c1c0c1888016030581b01c8070907200c0c2420524903420303c4d210502c03010b00c030804002030080c524650b4503d240d4580124819038070480540c1218980c0b032a40160780c442d00310966a8881134001c01d1b0050704104000b07480c043c0360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 445142778 1250 445141528 445141553
    0x1703040b241c080c0a031112040501080a0c0201020708071a07030b150c0a020a08030304060513020a05060a21020c071703091903080a03021206041a21030d02090909010b0d 75
    0x510710a8039100390803081d1360074201c02140440110307681e0804a000b403c810041c42d503944100307a954600d49803c0000280421000400000600d41c56019503201d140c401e40640f61903d030b115540070f8030340a0301d16000904203200004e800c40c039802c1000240186120b40202e8020300009411004420343c5000d0807160742c1c0c050724000c13480f0703c5400f0b0404010388820210700001d05940d000741d602d03400c043c6007e00603136101401541139a80e0584045015950384408081116400c481c0b940d07451400c0131060b1108001c04032901d0541e00e60f01050444070301503400420865080c0c1c1e06840003c2c2d00e4410410320b4a0f95031140e101c0701d80c0240002b0009081c840d40c0052001e410810180f6042d540782c0d540c0300164071010780040066000710f00d1070700200c44002155040342c4103c2e000c3c000f80303d028003524007402410903204d103c0c0b4100344440d5900b000100c10321400d0140e000030707a5074403018129600065844115818014000c03d00092800c07181803051840043d0014960385048007a9120038008915 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 445143884 1106 445142778 445142783
    0xe010f0e0303120415110c07081218060403061b0f11060c090127080c0117010603020a050c0109050f070b1e071703040b241c 55
    0x1000b0080d101c21262101080f01e140e0b9481c01c0650603600c45024040f43d80b46468044025554404000c105042c846000c0b1024180c1d624002959000a50101c4114040902045501d805004441380d0710b210000c0005007055100d0321030303100300c6114418a11016000c22042202a50400007000e102c4100e402c28445503102d04400548407900140241c40c000c070000380e81c0c0d1482c1e0155105107030f182c503010b010184070164040c4140481605020310100e91164401d0220b40350300c65184c0e030019408aa0003248036918000040d80039401c000703081c8013407150a00490100c210244035503030505002d50010001641039070849402c6c82078a8003c030b03940e00c03803c001c12103928800001d510200f07403e000c2c03042da8402090412000001211a00203840c0400205002c01d0150391159a0300074030180010701c40101500c0c20102e500050400d425401003110704c180c0d01c010050344041840e890 = true := by decide +kernel

theorem cover : BRFrame.Cov 444964028 445143884 := by
  have h0 := BRFrame.cov_init 444964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 444964028 ≤ n) (h2 : n < 445143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
