-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0462
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:56:13.628982+00:00
-- url     : https://prove2.me/submissions/86246f96-15d4-4684-8fd6-011fcdb94318

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 82913670 ≤ n < 83093526 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 82914920 1250 82913670 82913681
    0x60602070909081902101104090b060c0714060405091006020d0921020418050705010e0d03090b090d1205030415060b1204020f030f0a020f0409030906080a14071101 72
    0x120714070300b411840300202d402c2600b59202a0180d42c0c81d40c45084055078201d007002c204e41c113100c0f500c0b841c0c4604000410725a40c068029101c90303a00800408801c482088254020082200300c2540485014004050090403000d8640c0c07015207818205070b2500c000622130b40c02110741110003040003804110080d81080300e00452030040c00d20880aa003002180c140101005005806902c42403102d5021503d07161311180505000380101c0c2c1c904803052504948880c198810f8500080640c5050034440c9017202c81103400d954103840c2c2c030661500d40b03100022941c01c44800c40754030020004200e404100021204009028180da90540d2850107103845048a4450b02c041c7c08004c0c41c1c82d40502c05a10a80111b42126400041480cac05907103920000302111492168240c05000300c03458401c2c0c2000000d804c4000385d20803200c2d41400c105803400e100840f03064000240005046150401446004904d4190044551940890010171440d400740c060b0205658000c001072510b070310b000300e2039400c0c40356 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 82916170 1250 82914920 82914929
    0x60913110904020a03151203050a03150b07050c03010b0406080c010c15090506070f08040b130f290114060412050106150509010201050a330807091d0102090303031816030606060207 79
    0x4014441505413001406400ac0c06125418581d40b0507202c0344c982030926452005080c10480b440c0c4c0d4280c43d00e0500d45034030707001d5a402d00a60800d060600b040c42c007400f86505a810000050400d094a080115070380d103054a000d43d00c28032007041142d02422580608100140600d0040403181807500004040c943d50010300b0041180c18024000004c581c07030b110b1500100028100c041c400c4042c20303e0004080350060080401d04046904031191030050070794200b152036504032800030f0780e95101406c1c0543c0820483c5070300c00020842440000d208c2d80c0444e500030f0050000180454a4564007a6800c0d0208441008103a020a56039429030f824041d440d40700c980404203101c0d4003030801d01c1400000200c0103004200c9e0800d0030842d52680d00356840c500034091320007107481ca50f236038030500c0000f020710302e40c001041460680406c1c1000c0741402200c0d2800405401103155590790350101503a00714075a030041080c0101c0c1d10303100450032041e2a55005c7c50103050300003102864104068508044c5602 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 82917420 1250 82916170 82916189
    0x12280908040302011d0901081e0106030503030109050c070611070b1305120307180f0815100506030c04080a0b0f0a110f0c070e071706060913110904020a0315 69
    0x62000a445102a20122642800c0401c00310303402c1004584041540d80c901c40d0031100003c00010f98a100049081b420743c140540c844114196080c800d0980f05903000140c080e80c000c00041008580b20382c80b00c1d500403c2c0140c02c42c14031400e03903912416a40c00c4184000280070101d8030100303021040c607025401c42080483c20000800e1a59800e4907a00000d5451203020800300004991500480380c070114590381d540c540441507111f442c12032290078039000e034900900c03c00024140340944040f00b1402400c10314401c003580c0703207000d080000c60307031009000c2d60b550103052100041c0c0351001c00980a4030b0f40320f0466120603180402000e0310324107000702442c141c5418620070740083d076030941c00c45152030004400d02d0b42c1d841580c40401d140062690181030804080002c01c415103034031111070507494941c440c40c10300c1e64889004106182c010b44060790703400380f807120342c1003803803a00c0740c1c480318827940032100e05030170710f110540010101d0300f241440e03102107030f114860190b40010102020029010742c19 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 82918670 1250 82917420 82917431
    0x7060606170a0f0b0303040602060f0702030a090b07051207081c1104060e0301060f060206041407050112020901020a0c0b040305151b0c0705030a06020703020606030f0d0e01051228 79
    0x211100300d421000b9150091140e51a0081242c0100b0307034021086580001d400c072951640d50f90002580e5074801ca651482d9a940f02c03003c05d07000713403001c000c0b104c02070103030303a00c210489007442031611980c3c0c081c039422581071081e40c000d03451904110003d040c01d2801010780e25110042940d44590b90854000f803105042e1400100104104000b0241c07000d641451270520004068500802e005188640040d4500c040e81800021929400a0050710661180e04101c85c00c10040083d19540c0900303002d103601099003094147c910310b015901502000d881481180c0c124034203a00d800341c011040303401201c403c0c50001420300910004105007071400141850f00d880303034076150030103000e1855150710b660300059000031040914001040a800a802d00500f5242d80008500c0c0c0180203610170041200076000e81000259607150116420341c000d201c03840a070441c2c2018040441d900070303480d80c81790b06000c2c0c244646c10f61441803c080381c1c400d20000070300840c0140c0c200740d9000001e12880c11480340ca420701 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 82919920 1250 82918670 82918697
    0x303020d0b10080c0702120a0b01060f03020703020c1221040504060602030c0a0f1b0e0601090e040209011e18090c0e130b06010903050313030618080304080a2307060606 74
    0x1844150b4002c0e072503650545c03244054400201400300fa207c011440b849a41200c8061001d0000401d041300d816031514001005040030980503402649000303005600b01103c1490a4144a5640321000e0007040544181c4101c0421001c02c02c01d001c03140c02001c520108080c000d85c20300b40725072400fa050303600055082850200c0c0403940c41818a100409070055168090100240407030034040301c8400c125000c680036120405c2c00c13032000701120f04500241c0003040c0001c1c0c24045403c22400b0310740141020100768201000062001302400580c164070b00b840e00b00154070b0881c500b00c03035080303000108003055031031450034030080d070848a0b086141c8400154090100e04414000c5a640091b4080c80e8080035030364000040c5ca0034200d552000d082408005058034036004400a140166031041408001500c0e400f90580c201405503000103108000410228000c034140380e0181001c4041490302d4a094040d92480107640e0000e030b00301015101c00031840f9010007100d8000d11018000c50719140c40c641145 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 82921170 1250 82919920 82919927
    0x30b060a0e0105041104030507090c1e0813080d09030503010305010f020a020616020106030c061e0e01020c01050c24010e07030b060a050a0201060b03090d0816050a2105040303020d0b10 81
    0x61043c240700e50790303459048120004c5c02c0c042e5002990050300340c070255a5502d400c4000741144500c2c1900250a8020502c1c102000f02c4040d81043c000352740b9902181c0c0c64516405040303141c1001030365413402c14402040000e80502a40d50005d21070707510a40c5a500d10700c3c04a095034442800202d1680c01070090005d51680050895427249801a00040c0103074402c034103034014000c81e040601483c41d0140042007090300100b003420744048141c0305c00303150032020008840d003040b10052240160442040e0b4030f482d62082d0054030620700c1480075641e10070001460701e542d20035480001c02c042c101c1c50b0010401c51001e060314030340c8015241230510082a041002072603910403090882c080c400041104400580b003544082c0151100c50140d9a80b410f020021a41e10840f801000000911b100002046d4144c188170304e140412003901c400b801d201140206842c1c2020820114140c46026821401110528000c1030b004038001c0c0c9005036a030070020703c110143d82101c10518000d03040442d25400d1107a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 82922420 1250 82921170 82921199
    0x105040209040807031101050a0c1d06160816290403140706021303140f070f030807170a050901030e0a0c0612020c03120601030b0a0f09050727030b060a 67
    0x81c0007480b6136960060745402d03591410a602402d0301e40d8601010046080056400704603040d01c03584441e0952401810880c460180b1603041d281c01c03078803c0c413950340d5107c0300c00b040b0307940f1510651240b400c0074161b402d20490300c120070350141c136480110031125004003807524414003640054040700c911441d168070090001801c040c001c401c1c9420008240e020b00009a06494840256898900c5000e0340d074102284100040c07011403038070380540034070800c2c7d4140004920044400758900b00d1100c518640700d03100d0a030007a41c016140c8a502600101f02c031240074004020102060300d4282c5c4032210b041c0010300f03c075200f1410207840d5100d4082c6001044001d02c200b800c0701c04502d000446012120341c503d029025018a41c14148004907420310051000c2444501c59882031f6020401c03500c421080040c3d65603a40b00d50b4209190581c5e0030700a0000641200b0742c482e100c1d090035003070f0741c042c1c00b0807103060b051103423416100358040c00040c01007200e011061504003500300d0300d4008960405181e204880c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 82923670 1250 82922420 82922423
    0xf0503040e011d07081e042a081b01030209130204140a0302130c1b23070303050706020a051b06060405010902181e06030108150112030906030506040603051b0111010504020904 77
    0x10444c000f40c4038004c10703101c0d103020f030055100118103410146040c0041e071100082c101c0810f01011244072500380410600421070380c4c0704004007441c0c2d040e85a20185000600ac00f40d040503003c00020b04291510040250158800d02d8016583e600e0140003050181c1c0d180d6809115428018040000d80c1e603550401024041c441ea0001e00c03281c0e130b00408e40302e00140009980c031045c8002c44103402d100c4c10803049611034110213a0002480034403040c281d2204c501d8080200031440070301c019008100c041c0d02070010101a800c10919288403481c0800303602503203100c41c400641c490010000c0e9402c01d0b0140b0b03801040349000170340c107000b00b0903030344001c0d0503141c40c505003d10010034405201002d15041d101004001911035a52540c4401007142c9904030102e0403400d60088400010341c410072425203280700d0f41c0555803201303000c0c03e080c4110040d020260886038800e4841501001240c41489840c007444c1c9000072055040105274005000380380c8100c6e054406915290410002d611540032855116 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 82924920 1250 82923670 82923677
    0x703150b0a0306060603090203010b040903050301270501090603051005100b13050415050306070f0503040605060402130b0322020307060e060706060608011802340f0503040e011d07 79
    0x1840644086007070206540e0000e042e40b8100807000071038a4156010031841c038020b40080c064024180144000d41d80016002030000c1c50410040249074071810007448180f40b051203241c00d1001500c0400300341d6000b81c125825141d5070349400c004001e4100840203016440540501452401c1d034100000f42249104000040d180040d00d03a0781d802c4c8441900020b85001042000b41c20038101d034442e4400c8080c01060301a00c181000729802c113005000080184080743d5420340345543d1a44c4600240001806542e0803940900078019038003803a1076000007510020300b000d510307844c08141030f2103501c66404610a0400540002401684011440710300359903c50400304211450400891668443c80201030070356071800c4008296940d010038418125010001c010106400b0740c2e2001c1c04034071925a50090b20200300c0f17520700c104240e403c02401510080c1c4604040140b407038807103e01380ca141800488003501b0004042c403602e04150482c038090040800a00d50003100d00c0a0502e005e0005000141403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 82926170 1250 82924920 82924931
    0x13080c0f0f0301020d050414060603061510110609150a0b030304120f140106030209010b030609060111101103220309030f0c0b0c01021206011112030604110301121103070315 76
    0x1d030700c094040350007003040307000108024541070410106400e00245244028020000460b00620700010200c0c02401c034a00d5003903240d45160300f04443d0900e0720a01c01f00744401d84035805450b03842403005c42d21032403052014020a950304070b04030043c404024903038103802c0d10302044164a6100002914190b41c03001d2818417440009007400b81c20b0f0008100000d202031071003840112500410341003142100e201380c2e00a0b4141c3d07260700d148120b81c042110344540020801c0f00103640b0b0341c410314450071244c4000003681d03055040001403005440800620800301c400020910031004048060300300300060700f1001d421582c00c60341d8001d003400c0f19407002070310909221040c0787c240a807213400d500003803180c82003003591591442502400f075000707405e0038942c0803114000942c0a5020b500131b4541c40e00c0b000c000d0100d078101041011031581000c0d001c140c1007940ea82c5503c584200c40402107000e0320a411184000000c18540080218080d080083c0641c000143c1080018000310f01d042c0c0e12601c01d44003081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 82927420 1250 82926170 82926199
    0xb09040207110d0312180201171302090a0c020c0303070819140a0c030215060a0b07060b040501030b0103050609010c0e04020702061c0c1701030b01091d1213080c0f 72
    0x1076002c800303841903026880a060504040c3c11248103010100d8008050010032200c0c440c0e440c2501036418040d022865100007070181003168154194441c00b40c54101324155821313000320701c2c100070844040b01580e5031200f5880c1c056030100050459090200c0007035103012076a6440030414001c0750540403c1c000d1001e07a0707000850044801d0400b001042840c961151200240141020040340003035015016441a940424076030704a00c621503000603124074403491078194445550303881800141c81865944d855009079554074003a00d40218010514140309504505209007020005080d804640e0324004a1500f01500b114008001e1101124016120079187c004034a4505c94ac0e4180c16440001401801c403442081d8023220098800d0b80e0342c455001c101200c2e114044500b0300001e0b11007135441004000b01c9000d070700035544210210300b01900a00140500f1490105502d01444003594041002c00e40c0480304042c1400802c890002482d01200342008a5642c0703803030000850017004031204508 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 82928670 1250 82927420 82927433
    0x60b0403050a2325050402070c0e070219050607200a020f0f0405090d020c01090b0f09040902060a0309030e010e091f0815010305070905060907080a1404030804020f0a0b09040207 78
    0x10403000c1000241ca880d200d0142c013224402081e80303607195020410000128140c01d20b032007078460740c9500c503daa14200e030901483c104003030b4009100008500c00c03640f81c2088074000e000e8441c0603170300c03550040009091080c00038011105002c0c80790703003280f00010301c8210100002030b40041c043e01a20100d1340004540302050014405c2c4d5101d54000c1e0070001030000c16480007500141410840d4207840d41c06186400454000315039211744002c3e40020300410030007080c508014100007100803c00100a212036001c5000343d00700c005000c000c640d030394215005168214201080540c02481c111942040c4080002c013407034009000c040101c0c003030301c4a038118480c941d00d00d07a01924500003150183d43e1845402940d40400340000c40722802113180010b01d10f0b103507020381409140c00034560100c035541c041003141c4500000300703004031150301d4075444024901640707803980c011b9002c0c1d078420125141074010301034500300b5405000c0c001e44001e5001c000d40d200c004280c4807118812180540c1e52910b500300b02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 82929920 1250 82928670 82928723
    0x3060d0f03030908030702061e0106021b1201150e011d011401030905060a06031523040609020a0609060806030f06010504111312050d0906120207060f0501030303020904060b0403050a 80
    0x130465a000070611240c1a0002201c034800d1041482070504040b03080381e4072481c0f140a104003809a0701480c00308200340c038000e0580c40c0841018102c400c040884101c0320307080d60b0b00f40000101c0360002410601c18032001501c054091b042e44111004102040880d04140c0c00c014400c0303072808c6503864520045603100350840d440d6190080220744050511091040062156220864440e0702d483c8410404c00c500380283c01080d82458211804012485000104240c000f0070444000b69035542e002d0042e990030701182e010304010b681e0b14030342c5410540d000d803146c40702074046071280c2e00802092030761400000e4800d041d02c40130350300411002000d41044000d0302600440581c2000315400110b11404903420b401e448034018002c52380b814100741e80a886030b910314000d460009240c40801900d521861f002801d403d03124080004804d0030518804040758000e0b081100025000100c00c0c0d0745281602900c030241c600f40400519142c615a105a5902c00030600202055003014511080420000c001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 82931170 1250 82929920 82929923
    0x10603050108120306010512010902030114181303090305030c03040501080a09111018090203060906011d0d24050402030f01020903060f040c05030a0503030f010f050609120c0d0614060603060d0f030309 88
    0x404469584500004ac00b0703410900803441c20510410581100740392100000151341c443d030040600c240c8607802c0901600307600e1041a0f0a22402da400000002d10070402055441d01c80000785455a080500051a2480107480b04190324180300c0000d000c605005501c812004007214072604020a5071390540b400c0303403d41942a00f03e402f0b402c0000b001e02d1143c005500c0b8510485580720301da030300e000040d5500366015241141c1402a50125131023810a00100c0040d503005402c10101c40d9048a410094043d440c4020f003840d5884406000131810700300010b180790b40b14040250f08001e0248040390383d914008080020b40d860b144042000c5c40f06420001000c1c080c040c0544d2031681c0d25052aa541e03034000e80300301075951134038000000c2082c0107808090603074200070441440d1000c25020400b00c840c00d24403200003805010b0300d03a80c442c3e1312801c05905642c803030400801d640c0101c0e00380ea54410001450309020754001c10070031516030303034180c0c81c411200d40c0910203207a08021400c3c110024190443d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 82932420 1250 82931170 82931197
    0xe01020d030507030e0f25081504051914161d100902040803040321080403110705091005150a020c190f0609030203010b01030608121b07030b0108060106030501081203060105 76
    0x1c3e0f0600c00f1601081f00c084050100040070b0a40310903407070860f091401071042a401c0e4001e0300403500340000340060f131070b08540603130115004101941e40e070131201c003401241113500d84128081007441d010300303112509102c0854000c00403124039100c0400700942d0403c0104012640b84400541002e030455180d10180c69072410031900e07a80c4030341200c2d5981e03002d8001500c0b8400380c0c41c9c0405408580050840d250691540c48021981302c03650284d03100e008900a0a56a000b103a001280940b60280141e1082020076540c0c1c0d5100d03d0f05041c0103800000340d8864030100700c10800d01c4120342c0c0004501b800100c05460220700b81c04504400c040102c240d80140d41001800d43c1d000490580c010109030659000300d000f005035003140d01c0150b0445000c0e1041152682280214859486900c4003034003060410703151221000c40070051090400b8510f0f00119058001c110044c0540d43e1f040101501500e0320381410030080d4142200540e4902c00e00e0001c2000c41c40000014510340d200e1800c0d17684005582c078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 82933670 1250 82932420 82932433
    0x6010e0310091101090801020703020307380a0b010503041e05070e070302040609050108040b04240204080a030e030f15040809090709170a08070f060b0603130c05010e01020d030507030e 81
    0x505410008003c0d000280050080000071881d40c01c103200320b840055064000714a4038074141d8802c540d040b2114680f5081c01110700d010508007042d96008440c2005a8800c12210300c3c0808100d400c54616080d00d504200e002c0c400c2100140e607482da83c420301168020001d0381c407a02ca01d8441d140c1040e541000074030070403400034400183d800d43c0140007554110740b2100515070304c82004440c0032004840150812184c180030502082900034000840001c034100c1242c8501c01034820802d84c1d001d540040b030194003410549013455409a420a1824001c4018240b800c0c1a003628070350301d104001c1c00c00000102e00b0085010800043c04407044800054a14071140c070700400064141440c80c850807803951030707400d60812103850102c2c0d80c00405038000390302c030705010307071034892000c0c0d4400308000b1200b941d5580781c103101d1642c03003201541c41410f641d64095007480d0f9918040f4400b5600741e0109040c41020320042d0324507a00881d4242da4130180d4a070009180da9608011006413001189000c0c3c0b50203100e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 82934920 1250 82933670 82933673
    0x30c030c070813061205040b16020c0a0602060118090201020607030209060423100f020304060c0c0803070b091209090c030403090f1811031501050d200304050f06090606010e031009 79
    0x1040d8007804c988441e05d58030003040200c0003120580700d085400610442d020000107407030465035044607003d07803050b2040b02d52030b40c000c401150f01d0b414070340c10450250388441c00400500c0d4141555103224446000d09100e5140f26900107503a444001d0156802d0503004281c60070640c40f0b40040d10000e02c610b510b41070303550003110f440000081100c1c0419015120a17800848010701450324080c11001960082d8981403414104170b52403003186a04403070b100d06000000800704000c202400c1d07a64003a0901001e603085c85c6003003c0ca40650140d2060116000744141c210941d511406154440c040003019a0f032075840340b40840c1d035401d083e0002551180748101c013007000c0032120340940301c80b0309042c0200240d200015410750310b4002180c0548460381900403c0c003032075205002801d13401c000090003281c00001500f9000c111350801c000c00c01c0b141c90110070401440302c00c006201054003288050103807402d010302101e40b90b0340014605410300002002451554404120550300001012800c11064905 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 82936170 1250 82934920 82934947
    0x51c0c06090e070905150c01060801020307020105010611061006030e0a06050405160f1202060a050c01020a05090906061e0306030307060f0606030c0504080a241802040c0e06030c030c0708 82
    0x280c0100caa8040d10240050ba40f00c0c0070346004000d0300d40081001000407501401d01c080da501072080340c07529540302c80c000034074440300340007641c004c2c005600041034641c10051b0003420000000784550055124105008205007250a654282c607030701e01e4040756500080740d03807514040e4058401001c40e0301e0700301000280040820000000c84042d002000510307a00da200c3c2840301141d001b00301d0a070205500301c0d801468500000e02d01040d150800d54202902d0141b03031030032608071aaa420215100050704000c6180c203130302031a4404c004680c004d08080c1c0c108140c0c4801052003c05035500b82c000008070b005645c0030400c2c0c40516600a40034131950701d441c4003000180840c8e115600c04203040c038010641035070250054400741c0b10110002c1c0381411040e2151034880c00641c4007880c0d0800310084200407000d00f4003172100c06064a00f8296980e448030710500003214444482c403002c2040b144842e803000d80d2082c04a9820040c41e04c042c3d03446e03440f58a103801c40b07841007410003000101d0019991a50700711 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 82937420 1250 82936170 82936187
    0x20607031d040b090a1d07030503070605010b0c0d11030d020d06150201050c0304030c020a050d0f0506010602060112020d020402090604030c090e03030c270303030a0b031207020a051c0c06 82
    0x20500c100e045010307032500900c802d584107410459444105440001c440f0101a07002030524007014059442c3d9070351848a640c1441d020703800548940d00005464030038400349008880c01010142141031a180c41b81d48120344070002c000c00e000030412811803d03122008204240c52043c01c5550f411507a408110a01d1001040103100b04c80705080024609003960f4018440c2da4490849209900d00e940d89642e02180e28095024049078403004000e80070a058480c070031f01c2c030f02d01482298a00440e0429040c458030306407059008108540c050030061100e00d40a280c1c60644075816250208400306034030008010340140304850f07800100115002041c4079400141c14112165420100159000180070300d440344401c0700d400c40c15030000c10903181c0c449501c00c0d0104400896542007840e021142c400031742107500a4413050302c015207a5280d00c25a00d001d00c1800e80455190300c0e004e1070611a5804920008901c0c41000e04c200000041d0b41d5009a0035103910340d01a50103806801144d45070a00a820501c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 82938670 1250 82937420 82937447
    0x110a090501020f0c0105041e08121b0106060917030405130b100f090509040302011407050a03061d180a06090609030e0d1106090d022d0907080106030504030c02060703 73
    0x1080007555045404049540b201010042c0d40b910f03d0a810b0080231812034007201c14070380e48006c0c10100000d40c44020312604a118090310030361790f03880040c91320401c07500b802c24440948030b074034101d0100a12034000b28240c3c100c80031004132060142103000030758218000c5a00c10307500701da808120350203404000d50100e01c030340604903503481006051000480fa840c2034460f074400461002c1405002600c0d18140581d4090720903c004a9000c050140148003410700b900c0301404220081070450b04c0c56003502508014001c002c80d000070007030700700414030601c040280ca24500741a000750009944c000c2440003543d41a004901409140c1007403070003030010119008103400041c030601e10f8000da89007001f0040c84d9075802000c0c40c005409540200950356204994051b8040124404240141c1b90b01002101095440010442801241d20001c5c14820104409031182c0ca400c010000c0898020a00d039055552500c0c00050b43c0e522071805840096102002941c0315501141b400300b0154440403e40e040c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 82939920 1250 82938670 82938673
    0xf050312030705030c1b030a180501031a0910150206040615060e040b0609040f06090e0604021804051006030b070e060a0c030c02061207050309010509161404110a09050102 75
    0x4424451103400d5404180d0310360000a0040020454400d03039100038101c04140442ea0b003000e80303580300f000f0b459075105030454000318040054200c054040108241300606c1c003820b041c410082c0d405007140010084c445403078801c803103e00105000c46250b0000d2000f901c0042c0745900c02c04002c07640a9502c54003101c0444200d402d000c9444440d42c603c041040480c0c00a4441d141c070030b0300e110304100c0074080c40440702d074020310f040c422100b44d40c0e5140541103410560500c006115400c203a01c0e0000c0c2c50b185102c003805544a0741c284001038803941103001c2a40c0300054448402e4445250050070407650243d80401300741400310100600005402140c00351055803106120000860300303001441c02603907100c00100d4100070800340424042e4071480300c502e03c014469844e103c0e8981742c01c8003e0b03200703031680400980c011040041d619001d110302c0d500520b85200515880d441100d100c105c22815000d0201c4c80c03234040c452010661030b240c02c101c0c6e114a0f08135400c0c2e200e90030b002004104007414814140103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 82941170 1250 82939920 82939933
    0x90f050601060804140c09010b0315060a0509090604050421030618020d050609090706180b0d02130f0b09040c1704060c0e0604030b060108060109030f1a09031315030608070f0503 78
    0x284080000c2000e01060302400c02c0007e03a180660403062070304014a1030041b0b5440199a00c02c568403040240205402500e569480300151001c1c803680e0400104414050340c541010b21012900c2c0c0c00704501c540242103e403403810151510100e01400055100f218200100403416446c07003216009400120807c0c5010050365403000d0401c110f814046e181d8040d180c000d0141408074610a1034010b45101124240303e4240755641034101541d4000344400864aa020917480040080f203011103004084469003488101d040010f4095688181c15266104581d01c44d00d0302038940c020780c10303e04828ac0b410720f11500c52501e030400002401d0030601500c00215540001d00c036a1501d94140c0301640d800c000080b1159a0b141c2c01902d0040700501070034103220082400100184002c209503203503a10456114160700300920100342c8841f0003405080568000b0701c401c07846000c2506100f030481d200000703050349502101d00203500401554011160f070340900d8502045140c510004502110340036011030300c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 82942420 1250 82941170 82941203
    0xc05091305330a120303050106020703081c1d0c0f15030103110f060a030605030709090b040b0a0608070801060e1012031115071d0f010909090f050601060804 69
    0x880700222071500c00c110644080c00380e8a03290b4048800014200c050820840c0301440000b00b40703a0841d8001074558488651800030582d06000d43e9006002c42c1c001441840c1c01d42e5540d80c118090b01c540503100070002c1000d4040803141c3d40000c209030012017061030400c50303044281521007040c144210b020303800d0005181000c2c2401250801250380b80c0451a04690075a80c5862321b030700f114544940d001e0102d244000007641d5010044c1090252510001405c0c2e141405060901c2d145034030031407405241100420100358001822548603a00c090100c1d45940c40100c0780c401405580c11548007880342040c0450350000c154041c82c140c8030444260030882c0e5509000c0300403507126000d10401400401c0d201c0d400603001380e03405442c1d604560191944807003a24120207000c00100c1d6007200003045424240c0b00e412525407514801300c0d054680100c00180280041c207484982d100381c040a50b544c1031803505110100909501c20703a401400c0c0c408550b96203e006140f07010556054a50100000c1c1552 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 82943670 1250 82942420 82942459
    0x40515100b1206061207090f050d0213180507060504050f0418030f030f0203070e09060d03090611030912010902090a09030c110111070b0a0306080303150d0804090c0509 74
    0x200d498501840d450b0003810380c0d8031000030b5400380045410800501060380400307400100300e071240c505640c4504205145c0684038000001907030143c0c2c050b05042c81c070700c13015071281e80c5400001c0c000c0c650301090b9011003003860260307410031b210064030038002c0c0078000c6406075105004108031501242c40c00b00a00807002003000b03d5284100d0a058035045c0916000060300440e02120303418440d04000400301180740b1100283c7c3d000f12030003030003e008040c0c0410107140000c1e070705401c5a0251780b4010310303000c0d50303070054400701190017103009102c081c020101c5140400c02c00c0329400f44000d4414000c640200f2111400b074805100708030f22504401f4002403000302a0320601160980541d10300d50030540b1900c4501e0615900c0c00307024104002902c001c0341c900c0c400c100c0305000b000a5034003d96140a03000004080743c150f500140540e400c10401d0200501040c42d1402c00c400084031000c04161042c80c02c12841e00c1198001c514450500c480441400d400002802249000f50f43c8030125074003140113803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 82944920 1250 82943670 82943701
    0x306070f11010501180b0a03080705060402041d0606092a0d06061d0105090406030503120106031506021b060c0f010c030b060703020a060905120d0b0a08010513030309030215040515 79
    0x605c4210b00e44801030b440c10341c6940207903501c024040c0401c481952261160426584500002c0d41c4503400032092204500f490710401c2d003036004d100c0480d03001000184059132514070141c4030170310640402006c12a4940006021480d042007403c55034144107503901c0a0040d500111034003400c4031708d1302c02d00240c024025051403c03ca110720580c0240031a4a1005551079004460f569411a035951008400100100014550800182c582c1401580751000040c00d61f01c1c4903040050440241c1e408106031500007070324a4100301c4c00b14070305588094070000301e4264001e62300348066500c9401c0300c1041c3d004040d03124002c0102c0c0c40d541840b00202c1c6030103000841c4260030005006a20240629000c50b070303d40d01481419100d10150386124050074011040c90700004401080c0b5680c4440d050094908001c0c80c0d002003403004c000380f0861418041b800200311151402030709141e1038108100805d4401c0c090504609000c0d1200700c4281400c4c284035694500704110581c00b140c1000101e000700d003150560 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 82946170 1250 82944920 82944929
    0x40b09030f03011a07020a03050a02041a0a06030513020607030f1202070312020913060605130905060a03030c03021c120f06080c06070c0f06050c070b0c0a080a0e0306070f11010501 79
    0x1642c070b140d1801c100780e404008940020107881c1c0d800d028241c0140c0c0c950318643d00a60007100100b044608138010802180c440d81d1a6260007645035034208426100c0207801c0c0100c82c2c040c14001081d070f59812010952550b2010001c4d40724400040103810035400585208540125603039140e001802e081c20801240304004006e008907402c840031294881080e001490740710301c054008503000d086400d103031003500c002c0d401860202c2e1010444804180311001450000d01c4090000c1c0024180480400e9480000f400058200700c2480104001c0c54001c010003142c4034a80c0c5519007050032040e8005000070800f41c000646c10b400c104019062280601624040c3c817801c00150100c2e90008081202075880388004070703195000300b8000107030350041c40d051000420b105d40ba181d035a241c46040d1075040c4030640d08904c3c541c031801e2180200b4800300040341c1440a60048074541c0e20711540307500387c407000d9141110036810b1240b0f0040284a9912410021502005446085061001700318440c2a603000f40913 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 82947420 1250 82946170 82946197
    0x50f0a0812180706020d141905030711030a0905041802090f1009060902130503210d0e030a0c02040b010e01020c040203150306070201090309120305180621040b0903 72
    0x203202041185840002c0d000116032500d003880e00720401166080c0110b036481000503030484040a0040c50b00080b0004d0204200b0804c1c619100c1c6100b591209030403140041000c018002c00041d02e43c5019072031401622070844210303619440e0501005003000d43e1800345900450a1440910360003100758a80304141e40d00500000c002d0b900e401e06036414180041c40480b012240c5403002a0818051043d41f0180002c1c1e000540d491000c0390221240201560050f4044d40c0000031004140136210100303070380800c218030349a58401c00f601000c4040e09115080035418040010340480c45500081c200c447c9520039107061048048a81c015034407403041c0454540941c000d40c1c0440a2403406900440d4003000c90140999200012804a843e1550490307843e00941c2d943d580220515420441240040c129100848403a42f40f90303038003d00384d01800c0b2178030109412010402e055643e40f01c00341c5840c400200440c0c14149402c60084a5202040d5002c1e10880210808500c00e0400031003220780c040460308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 82948670 1250 82947420 82947427
    0xc0f060207060503040809090415020a0c050d0503190209060403060608010507110f0c0405040510050903040801110301050f0d0203010b28091a010c0c05060307050304110a1809021c0c03050f0a08 85
    0x40a2007401c81000b44110352525144502c00700142b0f1a201402c411001030340e0b100300c0c16007585442458068010309000c00d000342401004421100740c40e29000d1400040d9000d03880e00204030105005000390340009100c941800408188030704150f0000b4440c012035a05d00b8121030609140580b6202148248441d80e081070090f800c2c181001d8101581152088040301c1d0000c280305115800c542c400e42e503840041d04002010441000c090284008003000c1d03c40491955244c0782c0091240d0b41100007050040042e000348805541d0294802c020140010b890081c0c0d07028408110880c9005020005480c01c81c00e89010a03605d200344202a041e400980b54880020003400056030700340080841210140e0000354003160585502020303501444154841d0758480c1000d160143d445031561003e6801018820760800015001040703480483d000880006400d22103070020860a604d02c40d04641d03150f44c4042c001c401c0100f0410740000f103a008009441e40100c0501c8050f4071b40701002806481e0500a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 82949920 1250 82948670 82948687
    0xb090906100f200109050c0102060a0c0206010e0c0c07090f0c03090210111612030e0301090b04030f0302220303020706020a0c05090703020702120c0f0a032103090c0f0602070605030408 81
    0x11101c81018030212000103c00701840d44207142500c645800c01c4841e900070805500065030104141604a14580018410860406002980d490b814881c1a00399080381e804101042e1524040750b54642c00741c400d0f152219191503200000d400e01100c00b082192501c40d1403a5503c0c030034410568119801082d118070400528000c5a404004a00c201c440d4018041c02076181064010300000800c6240c540c0102200c035400c0103468111090400360007a41403209202c00a140d4000407944240c1c1810700d00d141b91043c0004030024000c04941154010000542a02604c50000d030075080301d2281d4201c440d2a501c1c1e240484c2c43d000c10400c018201c654614003400180350442c2500d030700c40c0d032a10b03006040c80c1c9583c0020360141c0c1c58001c07850740d036000391030002c819043c10f101000b01d0000c00e54200a0840c0b17035503200007110040d9003d0b044c0d00040c0034140301c0d41910035002704590f55004000601040d4507003c84031711a411030310481c005840f5204000030381c280914156480380b50032001103420420311 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 82951170 1250 82949920 82949927
    0x7050111100c050405030a0b0103020103050604061203030e1c0509040510060c030c02190303170a0209031005061203030403050c07060c1a04050709050a15080a0b01171005010b090906100f 82
    0x844401d109103e030510002c60140c030108902603403d402428900c2043d451400094103d4401402c0759004a04100b0203000c2c2e640c61000d588403860707142c80c00181442405003c6810a51a003012805004010790310a6400303912502030000210111010003040e12040b2044031616a180301d0600400c24410074000868000c1040700c161074009020518151560352804490200541080b4041941d2140d811402000205440d40c00708600d102140751060040c0002d50f204c4580c10124550394071400004e042e6101c801c0c1d481c80902294040701e4880c100b40c90054001e420075003d140b943e204007a40000c000b44640907080340113800c41804481001301981c0706c100410000c10596040c820340c200059560380a2083c0c5200d105401c2c0006004800742030aa142c48000b644800c000746c0c40f4a00b55004100508040c904458080707041d01005000d00c803510307082015082d291b1000c9454040000752100320704006000b16101118030f84095070f10310f401c12800c110241e28520024000d041e505c040c01d0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 82952420 1250 82951170 82951181
    0x319050a0510060503090a060204060816020c09190b0a091b020c060712031508010e070b180402030403090b03090303040b0717041212020412020f0111030f0d1e05090705011110 77
    0x506c0050311030204140d244c203000c0c0d80c032940c800070014a8041c200f0801e80901170090324000e0300d0744040d2510004910018900400103070800080b411038804509060001740c2c401c034200340c40a0300c6080b808e07550359a00d50040c88040349258010f60310391608000f50344049242401c07104003c000710f040c0030650300d940d941e24807403400a4060583e20008039507001d9611540e000240440000818504203021229003002c00c0743d444800c01d10400d01c0504214035201e001400402d805880050300d0b0390350b40c141120200000d921854280c1c5000050004580780400250b02c210302811000c80c00d601c0d8800d0880e42c200d08401182700c11111034001c100003c0010207800030403240c5d45002200303030a00c15003220072640298840a403022800d2585000c604065409190703608007402c0403810100e00743c0f040d944a11421100301c0100c18001039811204445502c40c03040c80d43c51700d41c05180307034594081c0319004100c00c0d02c3c2c2f80e03020700c00c4450000c0d0b10361280c9a40d11442c42d1000180400c42c0c90500290040d19 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 82953670 1250 82952420 82952431
    0xa02070c0803041a03040f02190504150f0302040e032205090c07030c320105091005010312050904020403200306061c0b06060712090f0f030b010501050913020319050a0510060503 78
    0x98140c0200c0240c3c0e00e44450270000007000c000515002d1401040004460303401a16140303480d964801048001d00700b0303000c40100c07070701910040b4140d01c0da401503a0840c800d4804070720f107002c484920810290440740c1020180c0307c080d10300d4cc10380d0301c1d048074a40e00c600030400b00400081e010b0f01041c001502c60000a40d8845a101c40490b088500080e8408110403c1600181613951842000221352040042c0d11071500c030b81c88104029411900d9004c0313081c0034040b5120a018000550f403880340c40d02c0d1304075001542c111303a29030704071064003500c00c030443d00401c4110303c20311440c80407500d207250602e801c514401d00b0b00e40c45601c0e846599100114403900601083c0e2002040c080900481c010712400c0030a07a0850f500c2c181c6070760a00d000d00c1c4400390980c01c10a2802e1110f901031000486022880d415200b09080183c0c80701011000190788021021440030490b0000c000d11603108000c01410b111881540f81c1409940d4500000004456040781c070880c807003c61032001c01c07869000310300660708035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 82954920 1250 82953670 82953683
    0x30602070203070b0c010c02060f04020108040210021219030b0405150409020103090f11121501180902031506010e12030d020c03310501051905030a020408060a02070c0803041a0304 79
    0x199910a0142c2c0660409007401a10380d45440080c47c800b83c0c10b021086c0d0103003284c22100701c0e60401d034000924095000740001d01803000789110030380690003007206000100c1181c1d451030341c1d016092140300390080642442d0b00828108861400d9a142900826104030107032003281d9415003a00b02007201400f02c0040c242c0c1456511546480401c95808030310040f05d0064400c50728550b03030800ce00a41e010162071403d0343c1e81000e251580344000c8400518115a041380c8a80c03001c0340300c0540d840c020052000d0081d4140700391200c90020102c0e5056a910403c0262204e180391a41c010500c441d42050103178400164104200490701514150302400228420804403828005080c014800450015401c42d40220444c00d4807889903550202450190000780303892800d00d54100003d058401c4500700d01401d1110103c00200400c105a05070350042900f01e0803100d250820b40240802940401016114441d1450020502050010458040b94800e4082d900d0741000385541c504150405042140d50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 82956170 1250 82954920 82954933
    0x1518031214130b131205070204180b010f1505040b0c1509031207030209030a020f1306030803010f05060906120c28030c020721020303130b041706010b0301030602070203 74
    0x148032103107246502c9520306410790700c510803950402841e0a440201140c9952040a00803000550a42c04402c003c08460070001d81b280d21b03500c0014003a04103024450080c440324151a400c7c44010082d0034100c0d900d00e402003c140e034480240030742290b0b48840c03e00c08680100020170843c11014003c046404210007a908040c1036020404148601541e14450561002c95030324040c100c03a20240c1d400c42c030f05090440c9014030341030100341c40c0c2182c19000380c455600c00c5212140b035250101040c1640d0271000040242c641c491400d012103400c20b0140250741c2258010110302c41c18510112115444020003190901e01145080703081c00600403d00886500d00340f060790905403001281c4d115160300c80042d000c1081105c0300007801c48003011015011903116910810007640c40742201c00800080003087d203007610403800030070b1541c4208584d505115402580010780c107101e0300c1c00781007036503406004115014041c03a03100d907840780700f0b000c1d41d080e4503010030040000610a60007000c24a1019096414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 82957420 1250 82956170 82956191
    0x7020d060e0a0f0b0709120210031d03040303030506030601030c0e0c0c011505010e01080f0601030e0c1f080705070c0501052d03060f03010213050415030507060c15180312 75
    0x20202c80080031103a02072000106401c21825807a410341c8510941b4044076400d240c00c1400044110301e01c40a8051000306910316401e078813980010703405c895241c0c13030440c00d9a115400d880d42d0f54458401600024607010204505140104425040301d4119541c409400d051004800789100e000e8003072041c0b50300420004030100c9007801402411400e80c2c070b40c90925031400002400141012242e83d04014265040100610003450b040c0d4102200b882c0015a50040b01d030610701c0c14034035481e1642d104c10240e20301c000901c0e503c0c00380c0c0428081591740c0000f94840b04800d451718001c0f070300010b0800000b40428002540b040010303120f040c06442c4d4603044000d001081c00c05038039040250a0320414000708004203030411046082e469441903000b140741200304d40c0b003885908160700a081c80386840d4041c80d0020901e80d440c00e0046d58202e010b4603441d40d914580900541c1041c00220f69820101003c000144c04034400c650301c035403103c8840110000241d0341101c0d8070b03c50003030007041f840d5240724161 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 82958670 1250 82957420 82957423
    0x7050a1106010905010303090503210901050f0f0706060815070f050f0c06010501080c07200406050307060e0108150108070f02010e030a0207050315090a110609040207080d06060306080307020d060e 86
    0x280200403c034800911035055040041580c071840d04210b0080c0c0c040c9003261048031103d4100d0307034016481d00c0c445445442d2400103c03200d1050724840f0307181c4840030646e407403000344040007005054031500040200395a903070307503454503001a201ca100c002d010140000e111140138401c034140301c890620786103140941403c2c0002c13141c3c0200040c00c05550010006100c90b580020013641c00c09200b8500138244604ca94411240d1020740c0d5a12070007000002c0309220760386554100102410b001000e03500802d450303420040c80e101c0190300d1140021400e60101e00d049090030b482100300e9106a5070500c0590b5280400d588882095103c001190b588030140b001001090014040d036034801d90140094a1804c4105443c20001c4124850094491411b200040e800040c402c0c0b1050b0380014500440809a400074689000302a1016042400080d030707c800c02400c03c00400840301056802c0101648a40c1e088040390310314040d202c03099004109003001b6103003851603108450700c84e41000ca49480d1110509 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 82959920 1250 82958670 82958683
    0x80903010f0c02030919080a14010f110c0c060405060d0203070210150f090c02070e040f0c14090a1415060405180910050903041a0d050c04050406050a0b0307050a11 72
    0x14401600f02241e0045c007071408881d003100303a02071524240226420609141c0d00c500c0341100089c610701454003007100e035035001c5d0854558001802c03070400c100352004006204960044031180001c3c014092041540e24102056034180c070400303451181070240b5040006e0080d07202900d40d500354851540f2000d5600d03031900034a0028440c50b444200360501e0141c100ca102809074001001e401c3c00c0c40303002201d1580c00581401260040c080481c07458607542031500c582071908501602e00d694105010511001c0d00e00e0395040c3c104251400c01d201d0b41c0e000c020008840c0c401c080066600c1a20021a0700000c540c4401040034500820f000c0c90990303103800044140e06d44444802410060300f04200561034203116103241285c82d20300038040c2d8640403044c1038403846103011b540100810b05006241c01a020402d0301c004100407d4104603904200685010980181c410a0302c43d03810302c1c0d0b01140c5801c0003a0b0a00485408410190668075040d00a49442d0022280750007048a0140480b05600080007076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 82961170 1250 82959920 82959941
    0x60f0c0c091d010506060a030b150409020421030804020f010318060603020301050619060c030c060c0201051f031505061210050708100e190605060403080c01050105010c0f080903010f 80
    0x1d04062980c650810303050200b0560405900d00010450b480c1c0b108400c480074101d0a00d8000f07030451012002403c60600440c243c00150000f180c0440c4040140c1c0c004c20a03299551114140c0014214420908000003000240010f010101141c01810b0410820800501c141404100c44200040b86010768003075403c29140d20752244410025801c081c41155000300f0140c0e0b0381e0b542282e4540d0107030481030052080f40100000b03001400c050520071501c007000194800c1c4c080c40329440b41007000340a02000c0d540c0200000c146d0805650355141f0205000c2100e0b80038030132141586000403d080100001854260485c0c550684440d240c007042c0100501103440080006240c1007040000b04007403002000c80d141184520800c0c48070482800000d0b90001c40d41c80d4084041d2983d0840c10050501a4001900840085004010851000f0190110310b06000007004141e0340e940044030702c090000c00c0a00b86140340686c0380b000c82c4d0244001c10012201400114184040c9007082086036605410b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 82962420 1250 82961170 82961189
    0xb030109050610060804080a1d06070501090209070207060e040e0307060507120f09110d140f0f0609010b0d02060d0603050a0602040e060111031b0f030a030606080109090c060f0c0c 79
    0x10060520440080710018000c03a18103042c083c41e01d681c7c4c0d00c0151007030b009904107100e64100240c10443c2411402c0400d1080505000e0f1038445030318007a070180c4140a000c0f44181c41d013000148070180300180d001c046401540e9414614448802440010406828200c019020810109012070824042c032402410b1595404602c501c86c580c0907012510150410a80c190070b040c1c2c0003020a801c00d0765041e180380c1c00c45296000511618000c5a00320365410700e00901d000301d440c80028420003041903078003903488030b096464035500d6000141c02c03100c04002050348002d192900c072000d03040400141038000340600c00001c41544913240c1902d0203041d1a0121f442030b800240c00d105c065001862550012020308164081c400c101407419124020840c80c498141d5050710301c100c00c41010001e0403d58001d82c01900d07035078010200010041c18050143d040820300c1e843c000244284188514014a41c000c48402200d90411a048940c80b031400e9902c0d0410603201c0500340410860071540740181420344 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 82963670 1250 82962420 82962433
    0x20a090203070f0f094a070e06090603061309051c0206060319021207290a0903020402030a090b0c1312030207060825020c010809150105040f180506062e030c030b03010905 75
    0x2600540006c4018408420000c00c00380e203580e43d071113035810340e8107410b41222116120340c0c43d4004a103901c030b01903004c40c0b101410b0203010403d000c40404c401200b00d80400300b10b410030382c600e0300580c1d40710b0095545d190581d0100a43da98545070140107182c8985c03000384011050344d03211036528036112258200d9642510714400c00c0d200000e00e100d80e000c0099140f4141030034000c5080000e80403485e1031002900031038001000504200141c3d200d20030042c0e00844a9031242800100004d007500300c40341e52980c07407150a8021507103607030341d0803035840065040c0e00900b08682803444c11a0104c401130040300d81680c4401c01201800891440031034042080c2d4014104010210001422180060010629500800e0294a802a0100d003050540307005940114800004c0c003018030003440d618241d4140702c102c5400070401c03c41c01040d00343c0903000c125a80603944c594140000c0354030404015003080140c04543d00d106540c025004001c0308806414001440c11103500420300399010820101c80301c0e0002d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 82964920 1250 82963670 82963799
    0x3030702011a120316020102011b0305040b010801020408030a0c02040605090f06031203060a05011d0907110f031204120905100221040b09120703020a090203070f0f09 73
    0x582d00c106164121200c1c3c480309001542242c49104550010940400000d80a03065900135000f00001c46417980e902021403071140f0000340184800d40f070450f15451000c0c0001a5664140290f03003e5072010740c091454103142e0b18090f1540919400100e0300580c0ba5980046c417a507e604500d44940140070444280746803440405043c1510041c02094245090044c40925100c01c803035030042e42c0007824500181d00600304003440900d03c00010781c0d4407041203000c0000c2c3d560700020101c22403010704c1c00c40ba4100c05400101d9100e010f440761a18503542a20000f9000c200707000b00000d17162100d411705141050b00c820110b42c0d032000d101c408801503440340c40c0501d408068514165000c6011103035442c10720f070a01c41c0440309481440040788c4205a41c1480ea01c5242c014009070703000396401004501065500c00f48140070b13400c100c1d003031008141071111100000d40101920088036255640d03400203d820900408110841441c070f41002c25030f500017001b00140f0b00e090206034074220003882960701984 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 82966170 1250 82964920 82964951
    0xa090506100309120c050102070b1302030d090308030a0f020c010501080c0f0103060e01030807050304080708070f06020a0c05090a0e01090609020a170d0f03090f0c0f050f0303030a020f07050303070201 88
    0x115807400805140c441c041010071149207142102100f0342c540104520941e003442c6002e8041c48102501d000d0790751044c090302c106220101d07040b035031082e810b17a900505010740c151220041480050020b440c100009240124540c2c0504c40000c40310a00509002280780c41c142103072400d0f0080749450b0720000c8100070524003010343e1000150300f484d044c0421410080d10030110707401844010710b09940450503904014050007510090151001225a0103a85076000755031041da84c8103030380d10030a08400c0407a58a1000c0746006100f504030411030000792902c1d0502ca02444000d207000419980c50341005060842801442c4d0054000c55002c070b128a100d00401546c0b1440307a0201d4802d4a91800710004102d011904400c000420708000000c45c2c1c049174203401030140103c2c01840118010702140802000a188900340c4403c0f40201045ca42c0314024400703210f00d540341d41fa0b07240d030050001a01d180034680003480000314020200c0c0c109000c0740c1c2c81e039103190410340f000c81c0503075110350304000c1d90f446 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 82967420 1250 82966170 82966189
    0xf0304020a1205250f09050406090218010614042301020f030f0c0615010f031a060406120522060e10090c0e07020607050301060806010c0506010b09040509030705070e0709050a090506 80
    0x160107440107041482d00170040300c18045446071880703044d240c200003014884142d108803c1c1c1030f0090646000c501e20321100b030f04460824095100801c1d1640500c2e000340301d0800698081d00c040d90310045180c461a05510b010108103c200d50443c4900070a00181810130700207868188683c04c02d4a80714009601035500349040100118000032000c00c005c951070b031f0300202104101465080c0000c106929080350090311610280094010700c00040000c0c2240e801403401c0c038000401e502c02c00c50340d1503031180c02e400050021808a9840c5080907414081800d641c800f10040102c0400c5480c00c142252000307007505c0c0820402e50710010002c9080148881040840e41e1111039440504028540024064028007041c043c030410407011b4000038899074010400c90905c0c0b50808111207480d80c1d1041600c2c03007075000d00b008038012418000860a80f100010641c0d0216520001610f291410710055401c0060300410600030054031390800111307038960040d03030400f80c200d4050114903403601209118203070700c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 82968670 1250 82967420 82967473
    0x6040308090c0d0b060a0f27270f0f0f0204050f040305040b0f090306070e01020f06060a0b070503092d09010e04060203090316030f031a090403050d0b132408030f0304020a1205 77
    0x303051827803412030030711640421180c0030800c1c44201180d203054180a0004400704000905d00008515030340c082c8030012100c811503134401c07a01131140d5680c880c0c0c0940e81c3c6606640c001c001c00c0c0c2c107001c02d101d144d2810024140e42ca01d1180303294241100000013914140c1c064072210007092120ba4a4490703540c0c1404001a1812550001c06071810290040382c0011030310300c0346c0a1700080114403070301042024412101011302c0285150559103040003100214940c0105030110811f0440802c0c00074140440100d0489104161885007540d0355141c0c0c0000e50310040c80c04141d400304000403440070103100046c00859019555244c0d0b0b07d6492140681180c480c0c1e00c801441c1c82100341503030540d43d5509089540680e140c80c08a0315045100c03035120151548016841c1e01c440398a0b844210186698012204100b00000ca01c004414030004481c501c002ea02521005030020418601c482d0440300003560171510191003044456030b171307044052000403026021250354024000340501c19000380000c29841 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 82969920 1250 82968670 82968749
    0xb130201090e0f0105060901050d050a0605120706082208030910050609011203032f030f0f04020d030f020a140d0f09050d0b0c071406040308090c0d0b060a0f 69
    0x70b0402c03c201e4040c1240510506106084c0002c40d0445030340300300300b601c09980580b001401141002109400500441d0140f14000c0014021a503441500020114111412601d810f02d05072034103507090401c503160000429200e4030b5200d41c00c0026402e040210710400c5150080c0c0051f20207020344409032007014214910071055a0010b1080503c03800558801d507905040000e40d0304c213410ac0b10300e243c5c903940a8014848003900c448100b089400002540302c0d0050002d001d0045da280301001960740010798000e500004c0030070640000074003803c0c0115264440f801100c55610680d40c2d05403c0d00d4055119070115000101d541a420743c111a0320400d4040c503041c442078035410440460141c800228014040c51a0000460301588141302151001504610800e40451042580356910b41d415901280016600b1000030b409440c04110342d40b0450300201038540c05802c1c1d88518810707800c003401c10b962002008400142c1c45c01203d55a000820790729011001000d81d048415801c24819490351121 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 82971170 1250 82969920 82969949
    0xf17060907150c150c0908100504030534060605010318050619060b0409050412080903160602091008090d0c1106070804081002030a18020109150c0b13020109 69
    0x442d003200c1c0c1c09540c00301882e01e40c070b010340141801c81c01c0b8046282d040320790915100006800c0ca03032003240c00050740c050708219100e00703030072100e80c000700c407004c0342e0103400121b091040b94560b1000c402e0800c550b00c14000c030017295085080c0c04c01101d04c410441150110f9550f41c1c00c100c2c0396007600401c5030b4002150044984e0010711380301c1645409008009488c0c03040002102031801501d50700035405030a440303816a486544034400c0000421060300d050340c038006140c410034442c521a00c0014401c503203d001440c140940000099003004494604a40c150b0b003d2050b4139041e140e400c180b00800420365510405401c099580c41e04050a04880008000b10340f2200d2010130f8196a00e106251016544181c4d10842400c0071241c0c3e0185821408581c045d041103c60242c80f280c02442c0a25011032040007020230040c0080f030f8002c4e1014000340882c15070301080084000910741124a0360306401c180782e9003101031343c40d401e02a204a44002078031b610b00994000355684103c0140251420307003500c549 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 82972420 1250 82971170 82971179
    0x50f06030a11030f060a090516180b06090910060e010c030203090904080903030a0e010201060501110c0409060b040e010e0c060a080f0a0f020313050111030705160c0f17060907 77
    0x11103110403603000d480c41c8182e401c1c00c07101d07490801c00400f00c2c40d805002d4854604103240d62001600c459003090301e451041001d6807c0003c54410400304640c021010783c9006500c03040c0400103450360b5000c0d254401020300655010392178843c10544605041c5c0e290705995414814068051303581c051606c5d0401030060302182c000307a0004111845000c2c200c404910f06d07075036442c002150b03108040d81d00707070540000300e018542981c100d8030681400800b41c0007071014036160401100c45c03003403508540056030300462054419003000e42c007600e90340d4050f000200e0b20544e20000700c0c05460360501c3d0000260365545141e1000f0b034040c85000442c0700704450382407400d00303400d00003001441c0c040e03e4182802c11000110346405456401042e00500d40035040d034603032401c25245c2d81260045078042d41e0075402c1c554800303d1070b81d00c0802c0340e110b074005440c1c03941059826840f00e10b54074100102115220304118020843e404205101c030001c4c4115185904480806120182480c1c8040c1500b138259004600910 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 82973670 1250 82972420 82972423
    0x90c0f080907120b100801020c1501062105070c021f090e15130b0901151107031502090604090e07170d30060e070306080f0606010e0a03060f0f050f0603 67
    0x10f24242c0041c0c851502c1d880300d20b4031010140c3e0700c0d44001c19540c40010a40ca0000b40490300d1001600c00c4050401d0584c3d8400d0140c403c5214042282e520224000038560303410020780c40740350090640e140020020000b0750214005c0040d03c52a1125096078240004055038481d2030715018007070541500e443d0741401c40d410069400c00071200d51148940c07070141c4148050f00c0e40003114100006001c03e450b9696080350030308500c00610300c440010707001000ca0842002c0024241c084070303408010840c81c2403074514108000d403c20403d480e8480400c0000041740070603030150103101c440000c0a00b0a442c5484464003c211a00007041c0d005d802000c0802d0340580c01280700c0e511f0498080410007034140e42d1054107101c900a81c005d10303909281903404540d90504164052040c3c1880d142001490b45451509a0341e03440e00440d011154401c03000540075501c50003d2030240080640031800c610f8880e512081a25401c40f00c07003204983e1410409040e400c140a0a80c001d11601e01d8034401d820f1040100c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 82974920 1250 82973670 82973699
    0x3060915050d0303050402151201060806100801060e060d3e090105130b03070207080111070b0105060d021b0a020307060f02100506031603030507051005010f15030204090c0f080907 79
    0x1c3d080c160b40d40d00103002e644030440001000542100e2040d40d07014000f1648041c10801c0c090800001d00e600005001401c1c0007440040c0704046840d40381050386040007c413444c0014901c140e81041c418007076440744651724014580303860900d030703150f01c00c21119581041c6d14103001d98450070608a84c00c2c42580d0f480c2ca05c3e0894900719400e103819540c038241d070600540400340301d80c8400424200041006022540403c410302560f0000000303001c00d144880708400c3c640500e26014000429520040105240140003405501d00006002d814410000848805d02040014003172058004020714007c5180a10004002d88110f0078084001801240c00075a0348070101042c1070010341d47c2002c01c401c0c1e5001c1203802181c589618800f10441d0710b030700c0d0040c00ca4110b11021143c80c82402c0412100c00614010076050790600e1814081c81850441d001180c0b50b0200c40d071005043d420000810381c15454003030401404841d869000039a81608001070078444001c00c11a010f03081388001344440e40105451 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 82976170 1250 82974920 82974923
    0x50f07060c03030e03042105011109030706050315030102032404020f0d05060409051036150e01110306120706020c04020904021303060e070608010806161e03060915050d 74
    0x19000f04c1c40c00c10a803440c0f146400c081c2c8000312048402468048003035985640ca84940003d104429440381d400700d070b60007005161649070b00000802e111051180014652180f61010408051806030740072908986c0b0039181d49815920302402c131422a000510302541a01054a086151030110b082000c0703140500c2041481d11600da901041069a49801c285841608a0143c40001d0200110740005084243d05285d1610305554024004d195250104502c2c0907800c810701e10030001a660301070000700d201482207019076220100c2c0c2507120248926003104a00600031940c0b81082c404101100324401c410000d154400c00050010590100307030301d00785103003e81c1c000d07845051080c0020003074011414504000c0e02403410003c00e000303560b081440c00324844004c0d90303600c03925040c048410b03030780074080d90303c1541c4000c011902c111143d0305a0184052103144c03048819002d5206d101c1040740b0719a410380000c0d21080240314040c82d81c4039583da03e2801c8170f6220280b03442d05011030710b01e981d100c07030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 82977420 1250 82976170 82976177
    0x403030b030c030f1c020f0604080310081504030e0d0c0b16080309010501090605011713081215101d12070b0403050109120305190c020c1804050f07060c03 68
    0x40888954070208012614204001c055640355000484119600c102000c011300084c040100d450092500104080081c001d40304060845961592030b0070303200398800b03031040a56910b1050b00140d0380c041849210010b4003400d0a82d402c034101410700170010400799444601c40c014101170540080d000810400848a55160440d181c00c42c101507860703c4800d241d009415004000108070704481c040d80300a040c3c80c0031142c02c000703030364a520046a071440000e121141e0005400041822140c02000c040800b511442040d480c0400c14040b0101102c0280e41d8036880514203251140c00b4a02141c0000d00c140f59841e100007031099119188509400b01502203003d202800b44002011009001c2d8502910144080316582c9503203180c4180200030b141c0342566440100c401e1651094480d0065038000d01c01171450007172001c00616110001d003e41c1400b04154442c1c040b002d501a22107507418182c5a0380e0024500c91490503003049810041c0d0590546000d41090005024481c2c2140035800004e4040c0fa = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 82978670 1250 82977420 82977431
    0x7140d0f1506091515080c0d020405060403060902130c0c02010309050a05061303020d020114010512010f0501060e030105010b040e160c170a0e030c010f030b0d080c0106032009040303 80
    0x10180c000040a52261040e40d0400c0c02c04540020b6541009101c065881c68090707100355566600e038016002259900006001800407a040d0344241c800f8104031070b40c0c2c002c010310305070741c4500049480c2c0c0180e004440c0c4507110101c0c0d00039440c000c3e2456110201c0c6800c00d1000c0c92600c403004040c0648070030001e05140e50b6600b0541800700810014034440e80c4101218a41c0c00c11004807003268103900c134110010300c00d02d11a001d0491040c050001c0d4000074100b104226400d20301001140c1c0c2c00101424925943d418070f010f003d442e140102c0f402013a460300e89240c409081018142900d405070440c42e0244001c1004200806826005652119607112055254160f8100c121240050b003036014100c003000312503a5145a002100811186c1c0c003d40314078120007041f4060546801aa030309042c080b4030f641c1001c4048a000c2d070842d6200420045c00c1040042d03041c1c1e9564580d42003100200000da646034800d004209840c65002003018a0402440d048041c4c080080d03a602c1c4014401801c140d101c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 82979920 1250 82978670 82978673
    0x102030915040b03010609030512210a090506070504090c0c020604030f0804090908120a05060a09021b031c060e040b1f0504050a0f06060e06070b22030201050105010207140d0f 77
    0x420542e80030305074036609540e495030750704001080901c0b5408141c40328040d0180c5030500300303040c1d0f007102c18040c10000c05075580e501203400c0c086030700d40040c11041d1185e11020382100080c0c050040313510a42d102d0700c8690310341d4180710800b81100c15001903034060146e0500806d0242ea40d0030261030480ba4414641c0d00c0710044c9180c008064007070387d846940c0036800c02c0b40072020008510040c00c034607040300321411031660318072030030a055810a8079152b030044c2c075460081c86070388420780042c003040644880d510741844803000020f181d58007410813106001000d40c950340d003002c0280900c20081c001911a14498141600d0308410160050410040c1030850002c00d900711450721142002082c0c018070400c81031800c00c0000010f020244403029090b031030f1440104809005510015008101402c85030070501c082d52034103280c14000d032612060040c01300790508003a00c0000045002442903001207000d514080c00a0b02e041500e80043c0483d41e40c003100524035450781c00008072881c0d081003007414261001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 82981170 1250 82979920 82979959
    0xa120f02030306150c07081b04020301030803060d020a05031e06010f05152506020c0d020613022403041b0501030501050f0603070c06051311040c020a03080c0405060409050703051501020309 83
    0x1405c8502c50a8061500001031401c0082040b1610001002d05070011080040030032007244024040208050010301c04a0b1040c2440080803020383e1015001c0305c103868403040000c1c41c2c050009504040110740c14620441600d0038465036005181c0622a024068245000039600418111f2410314008010840100940c141b40c3c05200c88085880d15410750289401e208004c0e501c50b0744a54028032036840c1450007144002401441005051000203100503030751300300b068140e500c41091901030038550b030220384961101d0045000303900c2025078590035003074081141c0328811154003886c185441c1c000100300c0c944840070391b0002c21b0403ca4810381d036541c81800540300d1a15064014010300e207024100040c200030206445c2d0205d026800e14540d00b034800c020002502c015000040042e00071440b130b5000a4040c85c116900565501d40300e9082a0310358020a006420036400305618544510500030900d400d4411030b900540002c401c0e034814465540042d6492040b0b40015006148544441d0708001c403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 82982420 1250 82981170 82981177
    0xa0605281503200306040c0f020c0d05030909010b030601120605060901140c0a03111002030c0702041d01050406050403140307080408090f06040b07020f0109080a020f0612090a120f0203030615 84
    0x1020f044014440710022204042074200f1500580182e00d8001013441650041e1146002442e0030b80c001e011304500e950a01031441c0000134221303517034441403040c0465980c0708081a4040d140a010154403441c0c00d10005115400d4401c4000703085140c41030610085d21080200c6250710741c00e09140d000300d84440d50314017107481401802401c0780501a180807c059100b0f04503001e0028213422076001140c0345841004030700c8280d4071603010382803c006100050802d6040b0103006119950f015008841741da040301d0030745034212004c80c0c2060785d450070001007603040310074010082480c0d00c4250440c035210300c000d000c0c0c04000d80007501c4a6800b080c020500d40e103160724000e1915010b0441a1500d81e00e4440c0c0d002500005012032140380030a03c030203e59407240c0c2400046513a04801000580080c0d02801440f200f0000300d29044101000020088030800d0f40c002d003e00590001040c011640b81460300104c04003d4042d410001c10b200100c0c103c03a8004203498000c0740454000101c80c0603002d801e0345610 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 82983670 1250 82982420 82982441
    0x80601050a11011506030609060b07060e070312050d0f060501020303130501180b0a0605040e150901020706020301120210050901021e07051206090601080a080301060c03170a0605281503 81
    0x1828161000c03050300f600b030032040440d442a2028041d40d2348544003901550702900031403001c2041841b0001c003042080d00071001c101e8241d010f8402554913604d60300300402c403070f03001c00020680001ea51001e0403d00d1203490703614000c0d9030081003d80d0034400002c0d120312003e84203e00c20b910040d60726040c01400e60050402d20b00d03c20441440b0100c40c5001002c6d10401c550003c489450020006118105801040710703020300325002e48210044030000340844000a0300c0340804c1c0d907080c0b20400015480344021341c0a8814900300613100360440c41003050000e041c3c1850420400b052020a40f03690300040c09039142e0440c3c402d840d002007507004403546050100e0b8403059200c106035814125502c4045a403d004540c0300041c0c480d01d0b80c03200090350f9100b0510381d00401d64441000108071551103850502c0b4901e20a02c5e08004070340c0c1d01500080991026203c0e4010f180d641c036010030043c03905800084602001900300100c5500c803000320b103000d03403440c03003040b009400003080c1c452064440d900070078402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 82984920 1250 82983670 82983673
    0x120f01150e0603040204020d1d0d09080c010807081f090209041b0504120201020102090d061d030f12190617100509071202130207030c170711041d01050c03040204110307080601050a11 80
    0xb549c08480c1180e580100d02c003098042140940d01082d80308000c40c2681c504d180617141e000c0c1c40d45580c0c104444c8418010310750700700c3c00b80003510503043c0f11006451100601c03c502015131500464030801c42219801e11130882000c10f05003200626903001410f40d802c0310503542020b400e115003800143c2c060700c101420558042c09660201d03040200c5d582c170103d00e08000f90307028104415000c14550780c912a040560080350024410307800503031100f21215620214078984c14000008000104081d20125044900720300a841a502d41940d000c000b070030284040b002d8180000c0c100528801e848032081d003d403015082e1003101d0038055440c0d222a000078442600c00866075040c00d4203004114038000103044804000070729400e85500c85070001d903494642c028141000513056902000003c10b95500e40c0c00c6106503d090b0156410401e00c03560b44241c61581c2c00d56628601841007200321144900500802c540500901141a43c880e0650317900440c05c0c00d20b00d548803941042900c0e40321a040d00e0110070b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 82986170 1250 82984920 82984961
    0xc0d082e0311060403080412060c0f02100c170906090105070509010e040203040206090d1406060607120309050708070801060e10150309020f120102071a070e0114120f01150e0603040204020d 83
    0xc230f1008100ea00c0d202c5000301010450b90900040c1262032420400c940d00050b4001043d1031609000d170b40c070450400c805402d10303140c00d450003036034504980030803503110540b038001804001001200303000c0e2951102d844d2526610f0840d203140040d008180303c3c029280901d5003c0000380440d01c07038100715803a0860090030101c1c0d0200c640781070455a81103520005141c05524082174890074844251040c40346e200354001c035600003521084004100c41c80050b5001d01c500000014101014030940e070140c400c40002040c0c66040a140e450607020180503010000d0035100c0412400f4410340d04a003100b815858081401050f600000d00b80007601208039610a41520704554030030815030062002034464003219201288214080d503049804845e02310120f4003951240700c40b0742c450009040089024000c0341d0400b002d01c580f40940c1d50049a0b0852a40c403100014484082c0b07900c9900d030314404510b0030820303c03441c039004600e0f28080584000e0113241c001c02c80c043c0420564000031505071a000a0303070396 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 82987420 1250 82986170 82986179
    0xc09020304080a09050301092102012004090b06070308040311010b0a0e04060b0415090c021005090a0c12080f09030f0105100f050414070509060c0d082e03110604030804 74
    0x302d603070184820740040354151100180b2404e040c011100c00341d81108651340c0d980c119101c41000091514040070442d541c0d01902c0b414040302034805001c0d5102c440260ba140c0d820721130b9403400c490109000d9485500c040c400315002035031024603d50b200d98145000740303d2503040315105000d460f2441c2e1031680480f0032280415032520480c13a0500c918060b41c000e00c0402041401d00003100c10300c009030b44416850241c28401d881c59a00f00c414500007a10446010003001405001182d00554261440b034200f0081841400440d00140f80540003501110b01081103075a1a801103226402a40d0070601c004039044034980d03000d1000f43e1025009030000c3c040741c90818404030b000512030041c242004031545002c036040c1040d1140318203007002d000030083d480c2c4403000182c3e41c1f42c001c0405942c7c4000c041140401c0820103003d82440000c080e110721019060005010b501d40c030810659210303600b000400480768060081c005011a50483c81e0040810001404180c151081e42c00241090384e00060008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 82988670 1250 82987420 82987433
    0x304050303070f0c0302070b0c10020d02070b091209010f11011e0c0504030816021c0c09140601080f06010210020a0804020f1903080d06030f0b0603011b05040b070c09020304 76
    0x610403141950f80000340035068500b66405488840f026006030b000c4201844102c1c4540300512400d20040100c2c0d245030340400040301a03034882820b90032040d8000c0746401c20041e80e0300a550f000042a0054402010b820740b00003218000c4481290400c030f4040f00710324149005040092a07980c02e40000c0c0440d4902e0064811020001c2e244c0405603407510046420b290320400540381941d81c419152071510645d0780b000421103500d403205903404125a165110300b44c02c4036134049078007885155410145441d140218040302d511101e011001c0000c00100500303a030780040141ea0152000200390b4080d2503c0300103c0c0340041c0000ca103a0810710024040b41c070190882d1005115030701c01c450808a0303038054014400800c500040f05025141c9039001400041d036464040c000011040c1000900d0a9a0751030348862815981415140d8403c100c01b401642c0c1000c1c001c07940c3c081d41011000c00e4840c48481d00600782c1c442c0d0b120f910300f042d40204002082100c0402003000074400c005d010b40d22402d0608060 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 82989920 1250 82988670 82988677
    0x1210050913030801140a0b18030114010f0b030c0f0309010b030105090f1905150417070308150f060a030929010e07030e030304120c0209010608090f061501180b03040503 74
    0x60b0042408000006060100b91070b45490138040038041306010361811030798200c2d13a00b120210a600c11000008045c56803024498040d40c2f012440308440ba95151400c03040085040d900400440030040040011000c0c800088820300f000d013007071982d034a9a46945150060518000c1107034154240824000c0c08000003c85010f090101d400750b071040a204e41c210480401c440078000c02d0354008012500e07118151b8800fa80e8864016881c4d90441d0301458400300465009080460104001d8400d00007201d0340f030710030407400201c1901c1034201444014001002d83c010799a60b4010141c4400d40d8908005880f02d18074103404032820b0180000a00d8114140100c0b000d00031180c041030594006280c0510038000c18400d001c802c0055803858035191031b1102c1c0008140800405d20001d070b041880141c8907011414001c0c2810703540d1045500308490356500304013443c41c03050013a42c040c2007440000007c00304d4001d400542406c1c04000111034803202d0b59003040d10380c40341000200102c00c02c0b00781b05020004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 82991170 1250 82989920 82989923
    0xd0803060f0103021201061404030602040608010611010902010c08091504030b04020f030303010e01050d170c010e121309090212150604062102040507020309060d06030b0a111210050913 81
    0x8052107400c90004408a0040d00315040b0044069801046020701407814031802a09020503d07140c1a1240c036400283da01c154448400125800c00410069034400c50b0454002c080c03400a220407185500002e084645940c005003030480b00080340d601c0d0740d0740e40340d8040003424111812030729140e8a062140c0c2029084800781d000d140c0c440b095040510300031085074180c442c010501c209503400c210034040710040540084a10718881007200300c803541c40a01078254241c06500200d1601c60100d000c03070802400c0784602d01362007403c0c45004d1a81400b5140101540c40060001490541300c0c00056550030311005620654055081e110345001603e20380300d4441c3d40306640505c05950340e200b284600c0c41c0200044000c0b075201c080404d00500d0190052038001070b0910440c0c3c24100000000703070090380558601d0340100e03a101d400f001004003800c22980d2050310b000b800c1083c81d85108107960303184039848030a80e20203142d40005200c6100c071003002000d09006404080d80b0301c1d040310b200e00d580d2840c540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 82992420 1250 82991170 82991179
    0x20c03060a06030203031206040209060d0c0f03060b0a030e1c08040b10120605060102010603020301110c070902041401180306020d0608060a060506190207030506091608190b04110d080306 82
    0x402100071070040d002101d42c00b40086180c0b8240c4c2c4109402c150f4054000c6034801d4081106280303980c0c40701e0183c22a054407480000d0b045048080c0139100c0d504170900e41d030074503003881810054a145d400a49125840303500f004200e0201030b54030641412980c1c046980e51601003900031201944c0140c40920652162000d01c0b4551154594138158003239522400d20380c04100c07040f4000281e200d0b0811600820180000714980740c403540000c2c2583c00101c42c80c810854082078120304900c00300581001051000b604616160030401d01d100e8990b120700c4030b04e041c814454016252070080503801c000035034000381b046444441180c0d01d400a0043d5114600e200d01c03170180401c500f03200310310419048420003001a45041030302502c103104e9001c204d0345131095000d000340010101d18244030b03491080a6000113444c101040e41c101410145581d0031205203076000821a81c414101c002c00310150350741110600c1500d50319482d100c0105a40c40c00225002500f5003c100c01704551031000d14050700741100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 82993670 1250 82992420 82992433
    0x8010b031605031207060b090403020d17040507030b13050601140a150917011e020a020601060207082a03011b0e0d0f021504031a0603010605010504030f03110c03070303020c03 77
    0x346210101c1c0c20500845615400003691283c000403007500500b55248202c501060841c0f0b0740300045c8038003c08440590240e00600031010120350712039601c495296134000070f00703c2400c040c0c0f6566902e00303450000030000d0340c40c0c6001c00d442031403080840204075400b104076a030540e120905c40329021594895a4010dc004040c0460200192034010352415010355841107041d250a500c02e4585030300000c102060756a6031000180d20024503006041039035600c80160341c425800000915100051307104d00c0454100050034811602c020aa0b1080c3c40317a00c5841500328180ea00001841c0205c49850550541c603110301c42003581c1258500091600c0c00b51143d804c48903149003400000140000d004083e200300694580044c40c0c4040340304c0b00d115008a010b8105600e039501c912150043c2c01500080d1039401e02040700502c1c0900404014001c2882c15504052440d61480c41007903203884020240301241198611000040040818110008044420035590703824041c1d1502680350049001e4000e58 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 82994920 1250 82993670 82993693
    0x9030f030203190507050408070e0117010626030d0504030804060624050d02090301051306050127020705210403050c0301090206090909010917120f0f1303020304080708010b03 77
    0xa01c00d4a100d460041800c1000c221a00d00c02002040010058424802c050002280c8604100700384000341441c007aaa200340d5041c031540c3e04d071326642d0803a20301c003903030400d0b030140464010079a039540882c05907010cc00c86503046803400d41c1580100128000450701c0d00081105040d031110aa034040c0d409801d00300401620b42410340030682210014000c060149040c1601281c4604000d00180f50a00001410a1a603200082c2503a5099941507001c1128a5000d411701801d40320700d0317004008150300b0708454030b00800005031109a0070700007000c090340800c05206209040c0403d02c1c0b40400368130b1131201c10220b0208104e43d500075020581d590300c15403042e55440d080512446091940050020b424900c08400300312280e08020480c0c03031075548070035440000816840c0304500d04104100b1380398880d041d9044440c6900d03c0142000307580c485100c14000b030003055440241d00710900d011050869903007400e080c3c0c40e41c4200c0d80018110720880100090380b04e810b5102640c0407900b1025112a170201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 82996170 1250 82994920 82994927
    0x30118060f060303140a1e0f110f0a020d020402091206070e0f03100203100e0702011b0806010806040209060f0f3a0c12021c05070315050d020409080301030609030f 72
    0x503002c0240130598403508401720101c100094142203140c0d140030a0b1a040990340c0c44849015801440040b580740f580504030b0507000181c0c62001024200280390507815600c2c603943d18115114040e0049244014000640d281d5070115460043c3c0907005010b001c082020040c1d03110811100d0030001623555280c200c1c0c500d00088068005000240100054981f01c41154002c2d80b02030811324444540420002c1d6124040d88c10034442d1805400004618104081c0302c00000311194680c02002040c00c01c1154682e0000d414680040b819140181c8036642e20011400d103100ea440400d0311101e001c01c07404513000084005000243c00c42d140341c0074032940495544038803806840700ba40c506c100c1c0208207100e100b061303100902080c02858a166201050310010007203030302c003800010100300340c10b00c599242e403c54020280c00c01d01a203000c0100017800a51040400c03c0b5001c4e841c455000b40030340324250340d40c5801403000700d0780040c02c0d02d5517035a42e4505900100320201c0110b01190b1501d61082c9901d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 82997420 1250 82996170 82996181
    0xf15110903100b01031805150705040b07060c0e0303070b0402040f021204110102070e0a1a0108070e01050304080f0309160501080f151801060e09010b1602010f0e030118060f 76
    0x5018004007801d4040d01031580140003c0f107611410103940349024001101164007200c03800e0b01550140c80c21001080001043c5c0c01300910035000d000c0100310401c900d10b1441c0845007580c0d0400400140348403204000c480e00070301c2c0600681d1500c070124220051106203079100340154801c0f2000c002e0401c1c0b84504105074013501461355058082140002c0200f002c40b2156642544140b060360a440d8440c505450704a40590704039840ed1b5a880910107458024050041401024204100ca900c0c10f414001c0548080003113a034108040031001c14100031050042d01c081d2100680c40780e8580c64805a504c0e40c0e19541c001d070304110020040b00240c613502410b0700d54080d002c140c044e071416540e18215451803885143d0416008017800303070000e0802c0802c3c1a128040c1840d540c5014098001c08100660180103801110000c10208080050903040f410b0402c80c595081c20491900c101e5007400b61401c200c2d4010340d64165092601201b12500e003803402d41c5200d8030540742048840d074101441700c2150b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 82998670 1250 82997420 82997437
    0xe0a03020d12062310080c0409090c050303040312120203100b0307110a0c0503070512030307080702070f0326090d02120f010f090b010e070504050103050c070f1511 72
    0x801007038119603028031a0800d0601c82403002030103e2820307540d440e41c1419040452060114a180042940403407070b02c1e44010221012518080a090801100301081c602c03880c07081c00e1340140d0702d56182c1d040000c2da4400300028000141035a072120b6503400c01100f100c510014100001c1da0804003408408064820b4038020414079881200320303801e01000303c4e441d500141c020f8090050020141e01d044504000700016284500d002c030201a1410301410f25160740b51300308070300c07846051140705410000001680e5200d001031409a2254a03054000c0e0304001440c1c004400c61400000003000740903007035400d41045003000d0400b14203850340359800c1e8801d028003c6229405183d480c0e0403000f51410b5801400800c041c00f080d00c40441e580b80883d800c403120703c100c1c8030045460300c00c8c20040c4a2400000c034010401c1d19941c0c80366140194009005114900946061503a5400481c5000b4000700a5a40140d40410f00342080c0d08035041c00e1a1101140380400849401c0c000100d0403051180c0685040c1c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 82999920 1250 82998670 82998673
    0x6081608010312030609020d06080d05040614131d04050c0f060a082e0f080a08070605101203030e0714010207050603040f0203010504080304060b010507020a14030a05010e010f0e0a0302 81
    0x2642565940080110f1011460003090307120b40c0c011994559602c0205500c11020b0f900240072803400c00c00d5418013003625520800c0c010140810070640c3c2c0c01030951141c06c44803c54482d03a4404510140d83c0c1c1c810213800036609400202c40301d01c44098013a0030140594011421207c0c0c031685103003001240449500d0300b6070410300502562407610700032115190840c03a450000d40e203038801425039148070040b554210001c0d01240700d04110510005c2c1d40385000d0455103018210110751920358a482e03110344000245090341e44c40000e038481210084c2c00000e0f002851640108541794280200507041d50000290507010380e100c006014210f011181c100c0d61410f80140644500d4041042801e40008106846080040f24a400166420712580344100c1c0301c5c1300181d0b1217040605007107003160808010581404010020309016036030f28043d16040b00c3c00a0710100001d895040407d0520300c0d4500c000f0841d40c20f0280f103001c0301c103040d0480c00b881d0100150412820703021a944c10b40e01c800c40400900503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 83001170 1250 82999920 82999937
    0xa320a030813030c0f240b040b0a0e040803100302100306030203010c020606032512240e07050603040f0b0103030e0f090c0901050a020f060a1a0f03060604051e09030301060816 77
    0x3410802c45201041d000f09034006c4814016600c103c50900942c0501103420b031b0b0307030818801e10b18103849101c103402c400352101000c003410706021100c0d0b00c40c040d1018000c08004000a141a0b0140e8030380405154068003e210f800d0844c1c1000d4003421103804124880c2d4240b440f0031001030301c005000d0780f09060050081c00c02540c01101014403031744100038410307540c1002e0404191907505401ca0412580304480f0003150428045151019205500081c0c244c0c5040c180ba403440d41c0000113100b401c0e51f40c00c44a81c0c4d9a41c881d480e00341c1401c00d1b900320052020519000002c18140c1222580c10107c000346c0d203458a1030701040c100860180201d0701d1904051090281072625440741c006400343c842e9a004980e20105102111440c244040b03410030b00842d2141a0100c80d080803040304921a40d050b10380034950582d400022780c03261801000240506e41d1100020700042007444450152280341c0480c0b511410080782c00c540b03e074424059100418005400b1681850820b203000c80300c0351199445a08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 83002420 1250 83001170 83001173
    0x1a010f020606060a0309020303040f15050412032f06060f010f1710080601080c040f020a0f080a02190509030c030303012313021603030c050a020a320a030813030c 71
    0x2558004004c000300705591204d49400503142000180040d06075030b82c144901521300003030b603002c1c422445101010402d06000030028640001034134503a56601d8244800d003c11080303503c101e19403c0400710641400c0c000031401d228100418658001c210680b40c00d61014000b800540305042c40d955220005100402d800e840c0c5c440140038107070011440301c001c0e00410fa9030980d0600d811020b03000440c49400c145143e41c0e1901e031503c03540e802600614019403c0510840700502170800002100f414011030f8000180d0360702e84c03030b0b0480f04c04490040004813009892000201180c12070450140688a00324180140b8580042924100c0b0790a200180d100606227115155686803992280d401c03924520000d142100d20f0300241c61010328501c40294151240d040082c1034a0041d0180000c2c42008c0200901c04d580c04102c882c0c43c103070000d448100030601d1201002101900a0300c403ca0010590a4007045900100e008941c0398080d50341c203d55a103903050988031b0b400200000501240880d5071840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 83003670 1250 83002420 83002429
    0x3070f03021e040e03130e010608010b091201020a09060e240c0309030a060b0306060d12260703060614040506030711030c0706020609101103010909080f04091a010f020606 75
    0x207041c600031000b240c06003840030012800b540c015062907070f180d401c08074400c1008004880d41400070300121592002c80c4d490000060480d000600580c00c00c141c00050411080c3c59403c07100a01613001c0008550340d1014120082821030540100c400181e80790101c401700340780c642d189400b9009281b10b50f000600c45180810005da10072600321030240018045c0500d40c0d13030f0034410540c2540c000c000100b40d007a95a0100f40c2000c0000b08031a200301034854101c0042405420105000101420200c8089548100d01e62070380104a01c03180da0750710360b2010800c44917850303042a400c42e4a5916540e903d030722050201507080c0a1406200d400010500002d00b10700c1c0701d400f6111002d440481602e02d8201c0b0004504d041880540100e80942c1c070803814841203000030059101c1c6005003a404114440340240350341c040384010b00c01c0c048459207030400c00c800e00c1999000c44129074500c181c11555250741302071072400341800c43c1c00180605e152000181c0c15500403a0301c4440702c15543e002d05100d45d0340301e0820 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 83004920 1250 83003670 83003689
    0x50405071205120c070306050a1a010f021203100f06090b090607020a080303040309080f0304050d1112060109050601030b01080f070c14101a030a02030304090e0102130605130503070f0302 82
    0x10340b03441c40f50945006404a0a030010702c90750110b100034014860a41c180300e41581d801504c5641c0103450442040c4858907000e000c0c02e420f00d401d2801c84031400c0c808604034905951010035010301000002404110b150304108103040b102880c907061445692464250340160440c860400c11460401c00c0040c80d1602c94000c00c0141e1008041440c5c0d2070f00c4051652540e041164110003241c410002800310b26410428807040502c20002145058107190214200d40341c3d0a0000f411300c1d80742e0281c45042e0383c61001c4030044036100801c0b601d0035a910601103001d000240e501d2030211b03260000070204c0c2d521800f013683c0305640e201061206525400760480d0210840c034030941c0e4089035244c1c241c18501c02440340f082404c5180c0b602140d40c11036110400c54401e13100103101e02c40e900c001c01c20401604c0c044292402c5402d0362400050411402031018064442c01404c07035130181a105010031001e400c0406040c480000b1506021019221403d00d030f40d80c15240210f5025a6000b202000185007031030b44c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 83006170 1250 83004920 83004923
    0x3060303040f03050307060609020c07060c021305091f06030c060e04090605010902130e040b130c12080403030f0f081b07020301020301060e091303170703090b0c0307030608010504050712 82
    0x100c07440c26590394189075400c050ba41048540c0c0d0800070343c003018032000b0b008032409000410b2085140c0f641d04040165114001d208890501041e41000015956201c0f00c00080c850002e505010b240b03009980b140d1140c2982440c0b81d0070032800e4005503d0340440784940016a907101c55000c000a040450960300384091400c0d030703503210341c0f40c0c40301d080003c0305401054024000c007000503881d100e0103d101040340d40250005001c480035881040045000d1812458103c0496407604404002d1801e10059010711070700940c4502600e60310160070403035018010412a4000d035908130400860040403030b01c00510310750a00024107007d02051f01c06282c503a10710481e503112030310540307440b0f129400302e42a40c100340d122030089183c082549a181c10f0041c1819807001c000c8060b05030002540d9030103403541e5a8100d05100701b102d400009030486000754810f00344a40c2140f031140035894600305d0f0b04010340c03007222500006070500d800020450014000e00380156488005000d1242c10042e5110045084000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 83007420 1250 83006170 83006173
    0x32805040c030b22030e030c0d020f090718060e0906090f04120c0c261906050c040302041b02160b070f0813060302071106160b0705041e150903031202030603 69
    0x4c0c01c41c2c03516060f503800d0141501c00d49901942d41d440b03804050400215042c03243c05041d041e401a03005950342a000640c010048a61003000e4072142022140700c4148201078050352442c0e58045a00354000d401c030040050102c608040741c0d0340d14010f00109480640c0c1c01c030500e00c60000443c00245043c00e150011444901c0c06543d21400c6840355901034016510842c441c4480040f082069244281081060840314008107814211a046084030b2401400064500365554000c94010a0800e045600071500144240031403444a4a680c400118841641c1c0c003500c21001001e88814502d501502120301c0e049840d400c140d0603444900c3c188810000132518030b901000909048088040c1c4400a491665001070321100c00d49059002a40c540c0040d0340310314010321103015115941004400020f0748a0a084215261204151250701907900240d411a062544100610445a201c6c3c0c044902800480a01404096003070710361108a00000c0c0010b500c201c003121314204950004c0da00400c0c080d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 83008670 1250 83007420 83007451
    0x81218120c22020d05040c050103050408030106050901030b040e25060e01120209040e0a050609030315040207060f0f020d1b0807110a050304091e0b0609190b032805040c030b 76
    0x541c000b040ba4001c10800c9001540c40041c0014013140e5010f9a01900f402e0804001608007512040c4560105100391807c005001588038810b910079040940300780c0006e4414000500d103405600e468440d072610040c0b860440560448404820202c40811924103444219103030810030b00440b5a210b840e0890380c02c140c1c013001605801d880d140b04020041c4c0409000d08903903a094a0500e04106015104813130760b40c81070040c45135035480d01980103101c14040303400590350f03180c40c41c12401800051684040e000c1ca0010308031840c180319002001c01820904040041c00c41d10811100c4140d0340c80000000609444000785001c4d001e0040c2d2100e1031700f200201e40c0c41210a03a1070500d1544249c2100c10079036244d43c0e00d15501c0c40c0e011000780a001141606103d0701c8035000c01708842c1d00445913118400d032060303c00e90440780103d04000001c0c0c00f120285170307074a183c540c1d126582d01150380420f0b8080403c450001c000c0040754410706028030b41c410f0740002c900e8515110364420080140041c21280d0707490 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 83009920 1250 83008670 83008729
    0x607141909080d02031c0912080402010315090501051003090f0204050c13061206090c021507110109060207020a080d12020703030b030f0c01030b0105071a070306081218120c 76
    0x40040f200800c03107581c000c59650014000c018140c00180009070f01450401c004007001581965040f02d101085181c03010130340d51540012006807403012510b4094803d030341001f01d1034401d1030b04114181c1d0810788840440752901cce0300031012180314407006404015010450001864550040c40c5c03c480038143c07550804420b00d400c5c000680f0160b00000c0401c40c1d0307890404506c642030040354000c0c07010840811004006400c003a449502c2002d01c1c00d0031805120025045a029000683d0b40c1d11140c0b000708942d05051030101b00035403101c8001d074481c0c0d610756030000e000e04c400a49036481c00803580e1521140d09510781000081d40010200324141034440c48400a01c0d10100003e4062401c4c00c1d0050070310b0550f042c005022202c1c0800345a04003d820030990b80850094400c0768032641540c0310240050b40c444208030014940350700700030301c0d9000703040554051012610141c092181b9a04c0c000c030503440108100100d8080e2485d02a00c0c60b000f603074105a5601d041c0313005100520751014030013601d180c0c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 83011170 1250 83009920 83009923
    0x303090a09060905150319020102030408070e060301111603030b03030d0c0513050a05060a1d0604030c030c0905070906050306130e0307150504050316051906020301050102060714190908 81
    0x15801441801e42d403400100036500c3c990040c180c10040b0449030303100244103800840e032180e4001e80c1064000d5034040b001400c69200708101c4008022000c01c0c7e401c4691149041e05154109444051196003446d00c542c400c801603004952101030041200c05040c071030360b5002c1d4041c0400b4000150315006c1803003481e20034071040c040c4045203200381e0303200b80d0341d100c00c2144484042d941d50042c034041c092008051007aa22000b04a034185066414103002c55030320780700031000c0c80c03020712149600303c1c5000c2000410480c0b6082c0300710547c0c0c4a00c1d01304400741c0e1100e128200300c1c6c400b264000c001802410081020a00460082d0b070061400780508442c031801d0740782d03202501d90303411481e84c1c10360000500e0f2050110003407004a00c1190400b0034045800c0c0740d21031913a00e02442c414458074090448804080000070403203401220003943c0f00d202c2c1a1540c1c1002d030000e4109108070ba016001e000b0005084500c41c095540340d480c80e01418500b0084103a0f0302c0c0c21403111400d808020710544540101d0350010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 83012420 1250 83011170 83011189
    0x60f2003041205010c0207032d0818091602060a020715110a02010c0203090a031b090f090c080f070306020306030a051605010905060f040315180b090d0f0e040902030309 74
    0x1018060140d550481c1c1c0f8280e400c50389944140421900039080a100140c01124586040103041701800d2801007840e0060550390030f0303544d0050280f900025141c48501030310800d1103a0036003c0343c4c68903503565071940303800c0310b2031816040300d00607080b00002800d51184e5902402c481c0c0e016026201448007003071116400c45100034075490800038013180300c80078250b09010300c9013285400d03c051800d1100310000b0450828031800000e14080c8044200994040b004030000d00900c9018400d1045050781043d00b0010056904192148030821b138012030004800140041e0071450704000340140307482c60701c0c2c10380250800340409a25020320644940412810030404142d41c0f10880c0c1080e4003441c0c02c00151645105612281c01104148061071401800300c06980849812104d0011340e42051420355004040a0b4506601241e94180710000d001005c203085218028180c1242c0c105240280c040d60400b10a80d0040000307026a0803007403031420241c00003084d641c030180440b070914040c180081c21860 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 83013670 1250 83012420 83012429
    0xa11090a02090d2f0109030212030f1810030603120804110a0905100509011a0d0b12030a080c090a05012007060f030605010320030618010602030702120304060f200304 73
    0x4140c0e22030307000806140c40075403c0b416105204e030300308282080001e03090740d9141c8000392140b24140c10018910500f1700440703c210194801a0303a840c1c0003800700c0441e8801c4250068041c07614001a000c010340a80706150590790043c03440c081074040c009040b00c031404024004c071001c6896044507030307007a00c07820440e4000e4141a10f0126440c90302e01070300790b61030680c1e82c003052240180720010007950b001c101b46c40320081d246a90107aa5240c90503550005040c1246442da044514030075581c00c10200400940702001d001d03541c07402951552100c200c968010011110341c42419000304002d95805501c00101c1d9203644460380164000c0c008002c0d04200660340088040f41100390148000356142c801c000280109090422030040c034103401100c01441c20020349455000040421815a00c6844102c10b403049402400b105603180c400c000e40301e8001080403401408055900e0600c1c02d0044182c4007514003554a000700004e00900c00c64000d020710200c1409040304080280c80428148021320282 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 83014920 1250 83013670 83013683
    0x2030303151804081605030f031509061e0d0501110c1c020607020601060f0c0203010905010b01090b03061302030402061b1b0301090308010b03070203040503060103060b120a11090a02090d 82
    0x4000c04400c2c0080c1c44030740b1000410b80c81c81038080000280c000001d4407045030f00d01ca03004807a40131038506940341d4403840076007412401c1c01004010740c0c90080141400880c0c4251000b0b1480e0b1607800c14072551211211609a40c9940d001d80700c0b041e42096001040e03ca030284002244149540d4070382440780c1e1100301140410340180c11404050190038040500480052004089034a01070200070b40342d22040c090182003061800b21201140e00c600d032000b2a49400400800649c102131520b50b000301120803c6d940440c088500005000c0c3c80074080e6882500054210b039211a117044d2a180251702c010000c07a400b86050003040108001c41c011709404000107c001e020600c0a102070500000c08290854860b031b04255141e40081d074009400c604503004005041d480e6180c0000c00c0c1c0c03e60069402994044c4a070308000400e02800e60841180e80f8403e580a00e100c1c203107481d650f0f27207410300d03040c014001c8400c0703ea0700c442c030f414185980355000c05003407170050608120600142e00c1d02c100020582d0030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 83016170 1250 83014920 83014951
    0x4051309020f09070e0108100e0f16050f092b0b0a0f0209030a0201180b0a1e03090506011203050f0a020309090603011503080c10020a2c0108130f02030303 68
    0x31401c02050b1001401c03400ca0f1202958134100e03070010f000c00340a4000504125044011422a100c240c0c4810050301c0b04024004040c42c1c070440f580901002181d807080340c2002012000e00c0c1e5405041119003168007001d4a5103441840418041c60500b1010101d680c0c241600907102940d0256980713103c024401c1c4403400e172609048040c9401c0d540040c243c980106d2042000600d19980007403100d01c0310780c2c2820b02d489013002400c808842081c255128048002e00003035510490395100722448401240f0055107030b000903206008a003243c00d001d20040159020314014407260080001c01801c0d54400d00c0e0880c40c01401e8000c000d015040301445502503400032138581940d01d00880e41517404a016402000113040d200025081002544000342c946100080c0c1c0c1d80600b802031091007644120303158103558404e01c5c8a00141080181203510341c1e042c01e42c0300042034074180355100000c407101c160740b00c5c94603858002490407890031100003200c0488014a070300c1d00607101400590b02c40d0070b000140c80c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 83017420 1250 83016170 83016173
    0x708030c010b010207140d060f020309010f20031816090501030302100b0307150201020906040f080607030903050307030f1d01020d23010308090307030b15040c020105060d02130204051309 82
    0x20364400b0100b0a06642003100309101c0c0d0407000d6500030000c0c4c000ca600001503141410040300414031400c0503450700b4000020030081c54015080403524001e80c0340d0402c030840240e041194841e102e03070000c0210b01c1c0100042014914020181184423440c0c1341514042c0c3e0540032213041d400f950740c0c03200107043d8a81004005040d0140642070100072054010300124200d0300020341c0381d207000d0050174046030b601440c08024520035416201c080d01c0103003406503196245c84850b6907503901c5e840b40010314810240002c1c1100d2023800b03082d0300d8680c10746849003142c8440714103501500054002c4188155640107001442c403070f10002000c91050000010f0765140c0740c2c00c0e51402e5074010380900a05169003003601150701d881032500b1741113980240c2c3c1c260329085200c0029041c1140c982c00505110b0b00d840030b10021030341c4510786520b44807003141c08001c91207117030b401a401d07207500b203401e698410040c10070030016043c00a0345503141d10762404010301d4241c80340b0010b804510b1480481d02d00568900f0480c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 83018670 1250 83017420 83017423
    0x8030c06340c03090b0a0903080a27080c060c03031303050d0c081807050102100b060c03030901020406082d07110d05070606050301051308070c320103060b0d1104080708030c 76
    0x13003d01005c02605242c41e44451018001450620008150030300c0000c104c2a03080c0b0828900c0e2041000b244900903003022003e1142c1d4000319400303001010300855000740d120740f41a000300c030240d07800070b40554110303556000c003d101c0c03400d854429014813800304514650b0703e0503403007a4401085c0c541c0b03d103070700c1d82801c00030440744111149160380d59501240d000c0c44560707000100d0007a28042c00e200410300440d41030126005005040344120144004400d000e140c030010740103003003a10b4580da2084500c2d44d48000100100002d001540d42050341161045045400040790a074003028031b081200031442014961803038030390304298041c00544081600c404020503801100002e00c0c00714000e0196040030303118008440a13500b030003814610001900c2040020040144c030081c840b981840900e281841d40423101c600c1000c00b00303006219000c0e400a0b0540c0280708450558420b0038141b4140203018031480010321800321600e05004050000040e000c500700711340c001403d13181c0c01544c0c8401e000419075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 83019920 1250 83018670 83018687
    0x20609010605010908031c020d18060b01030203061c0609020316030c0906031a0a060b0316030f060e01090f0b030111040618150c020402120f1008030c06340c03 70
    0x10f410455081d0081141400020655018201c4070701001541c104042000001b0b00c128003024642605010300b203807100c0c2e0f603281e4130000c56004007020f1052003110401103003284000c9900f958403860f00200d00c0700c48681c51a00e03420141c443e08001444030702580000b464242c50021242498803440011b10800c520401e03400014400c4500c00c0c028242103550707504507a152881d07502c1c0d407607444500054102c18a50001750090800c0d0669603560b080ca4400c0c1031a065031400c010021078180650304800060700c1c801c1c20308076a44071507004526420315140c2e001a1101c1c0704003001181d240c11901c845581c0a00c1040c648808900d10256100d15207400a8a40611103480030016034800c0d804014200f500c0c02c01907211010b03032815210322542c510002d4001d0044054500310b40f0030010801c0010228622501d0040100c407002c0f81351640e03203c0c0160f41c0c920803140030705240d401040200300c401c940f01c04074120100c50706a2410401c040c6107c415842c000410946001800c0306d0b40c200d044c550001303001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 83021170 1250 83019920 83019929
    0x604090c15110a080a03110712050d0b010203070b0703020d020706020c01060e1003030c0b0a02070b090a030909060308040b0903070e090604061401060e0108190e010f050f061c050a02100206090106 86
    0x24000e04100c40d01d500d9510f0043c0d2170007000f807603112140b01544e9902001280d000c1503112003021111591042c0c000c0203900440e084080e1a0f02e40200004158000002e59040550118184800b40d61f900c0d8210060340083c10041c5440d50240000030004032680090a12840000000070700e5901d05100003020b00c00150115405c1000781da42400407a034401c040f00301140c0c010aa000c0e0740d0b1945001c403402407103206409041c0c80707500c1c0203200540e080403078090083c2c0e019507588604103441e000310b0300071140c4a1000030480ca20800c0304100440c04030003c0d000182004059480055603128080001c0f04100e40304d000715000384d0304000c00c04c074551040000321014055120030940c1440c0c80680b00c1c1d032001da0402d051146410004546950340c04801d0301f40d002d040c5040c07020f44950315050340600b0000700c020740040c3c1072000165000000100407480381600030010020401e607030b00d0748014a2282002030742d103400780302c0507140941c48403000300302d00d003115500902051070140c2c030362821103010307400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 83022420 1250 83021170 83021173
    0x604020909070e0d08180a060906170405070302030604050d0801080a0201050315030f12092805120709020a08040b0906010302130f27050f0601060c03080604090c1511 73
    0x200318658440c002055400031060030169081115200018440c100581005200d03000000d10f0740020b00c442c4142100d8000c00f80c4101c0c40c4541c4886040c4d5078031505004040028615001201603400401026904180503900382e560040c1c4a0700132a0401c0400c50b03042c0c54a40c00b0814210103180e1020b00b1a0040458002804c00341803180c0c0020114840640302c1c11411a005031100d2083d5414026084000070b80b0007100c038a9130002d49036110a401c0903481d584540c4407010340c9540203001501340340003219601c0210200c5d030b09107070405c1000d0107040d101d000700d44500600881c00d0300607480100350300c514a442c0e0202510303040c9450018480018203201c00b0b504880d00400050700c40c402c001c521071541c00d0300030034104000078801c402400035a0900200700100c004001030741c45060409901c450103201910000015042c459aa8400a00c560030002c0c42040201300402d224038010750304100b00400200310f40c0d52a0311207443c0d4061076001501d525802d146845001034100740d840c0000780d0108d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 83023670 1250 83022420 83022427
    0x102031914040b04020f040905010509010f0603050c0d1b0e06100512180a020406031202010e070303120c1101150501080a060e130c050909010204030b060901080307030e031906090b060402 82
    0x41608000c1e40e070241004006078100d002007070841d910010148103503140035004101000e620709015000c0c101c01e41d0301018a51030106090199580c0780245420b8903000340050025501c0603083c420124613030300d02590310342480d500412940110040840080070044d212108a0901c40c04204003038100391812402d00c00304004c1074482c15003080c0c0340c9522015103911502e12210713400d8514284598148000d610610303102c0301008010f40c8a914440c0c0c010598000c10451600c86107841d038400300c1e070001a000c202840c103460b01004c12034021485030110382c64541c9042c09c401d00d0540c02e494203076510141d860b0f42090280700b01c2d68486e078101d40c4600150340600030903180c82c1402c500002c01030295051a4490301040081c0000140e0b10402040040d00041ca18504040c082d8001c0d0003a000456403d005034000c52441c0c50540c41c454140e499110107503240610a980a1b14880300b02140a501070160301e1540102440e09095124024000c10700170519400519001003400030042001c0c4c40f4501c1072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 83024920 1250 83023670 83023691
    0x50609160b040e06040b0102030408030409050a05090601031a0903040e07080403021203072a0b0f01080d0306060f0e12030a020114090f120a0302070204050c0c010b01110613030507020a03030201020319 88
    0x442a21380000f01510300245608586004030b0840c403c0c1d401c4148030344000200001c40020b294171852190384c42d0f0320704001c2c81d00c40f141102d480d0442848080c024903031410060820031200c9412a422102c00b208503854107a503403e0391341159100f2201c1002141482c400c02041c50b40504c045000308900106492071440c18440241500010703046141c01480035036000c02e15200f04483c961203881d00032010b59101d10301900c0c03034400c2040034040c004950240b414200049400382c00f542080c0c170b0f100d4441e07850380c40003854120307050b42e8103000c3c8a900103030b140000000a00700f8801040081416400818200c01426001400c1c2c1d501410425182d070041e044050742210110380c0811401028400c00e544121a200844c083e000d0704a01a40c041e25200511100344161001401158845030082c0b001c090210f0064410031101c290410a81d00150700054185101030302d001c000358032908095041038905e0300454104c101c00d41040300541e50010902011081c9a600383c080d14003190350600689148 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 83026170 1250 83024920 83024939
    0x3010513050f2803030e060a060f060203040e0711031b0f010608150f040302120c07051203090108011806090906020403050c06130303140c0109030f08060607020a05060c0307050609160b04 82
    0x550b803d4066616000601c00416200c3e412458400100300c01302d0b00b0310704040302c480d002010280310b040e04c01038040f580065041c3c008002d0b1801c0b07603e108030114150f40e0301402501e5100840c034401c1464001000101180d00c4102180d00c090f1082c0002800860466034130b50b82150519046540554032107814080031940001c025580100c0c004149212501e55180c02da203002501c2d0007249110801103204a0400400140c00044400403650541c401c81542d10300f90310381c801d403000c543c00565181d0042c0000d86d0030010360320013071540c010b00240e807540d1a4082d504a4609a804491036034000604009010741002112440c0b0421034886103807018900b00303e89502034521005052040c2202494070748500b5106603412a0186002441004103610b8011301c2c080c199140361002c0352501020403440c1c2000002d071248294050070b081c488904200c2000302e10380001a201429200c02c0003a4000103c1c02d00c101800b070384480c001448d80d420101495060302c401d03070300102c00a040c00c1c041080740811 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 83027420 1250 83026170 83026213
    0xc0c0601090c03060312080a0606080c0304020f0a0812120601170f04020f09010e09010c03050105010207062109080a030b0f01050702012006150901080a020d12050903010513050f 78
    0xc0070440000c040040720703000d801500860348090080051084c0c4d056900c1c1c0c1207088640700c0c1c1c0014404119240e1145402d4558900030f484070692203070144000703070060401d507201c01c40860b4003c1c46008034558402c03e1600e8912604000e0884040204607046c0208540424640100090030700312542000c000c980f02c0003010080490180da403400b400306065441d04031221903908005484e50361550b0315000ca110364207030251078540003903191407088418103100307108050603280141d018110a0749087d0040300c2c00c0300169a201d540e8042105d40c0c1e01103819502c40c00d0390a600c1035803c1510b4048400703001d01122010300f0b5840c05084411500d1369141e84c010100c40c84d043c1d0900b04096001120901003000c03502078041d150720b0b8440c0c4810702400f0b140480a10300c5003030044450f910b550f03884091068640031000720094101c61b03410304600005a40640d10400040d062030001d0030716408000080c00d4400aa0b902528000ca014400003801030a111654646441f0ba005202034480c000c1000c0441c0c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 83028670 1250 83027420 83027429
    0x60b0a0e19090c06110c09070f0f0207120309030b010609031505090a1a090c01140301030b06151606110702030709051807030c050a081f0b01030e01090501090b0c0c0601 74
    0x40109401d4080000076485100340310380100101c0c8a060b1515000b6119805041006080e8820300003070703044c103140c0070211920075403055642601079031803880c040e03075070340b94a0403800158058101d0201e10300d5a8121012810ba01980d07440310614650b0403341e40440d4181c1140d000c01119000c10b0012440c2c800c40c0480803400107600003000d03516400030078188501014020320008814000e1032200a481240d580611003800658041256003001507a01c0500c41c0780d075540761070003880100082403511409942c8910050100541c14a6640003140c0590084421002e268000c00326001844540d2041e80000c80100030410300e03140d110b0700040c2d51a15103102d42003000385c032000066004014200c951848900a00488054a03100d2501604501c918002c0c14085c0b908410700013030700100010001e0040300202c1d08860390200d90140500039218016070345061549580310851312410034407600c070040d40100d00002d0280c02c24544a01c0c0000080d20040d0301c0c0038103004d42032a42c40b02040d001d0464 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 83029920 1250 83028670 83028691
    0x4150608280201030207151e0c0804020d05010e030307081603020f09040902041d0a150b0a090903020c13050a060503010c0e01030f1104060507050c01050414010f020f01020406030207060b0a0e 84
    0x9a01c1d03880100c1c0603104080c002440c40031203c10a0107901b103160013003000001d001c000d10041c004101300190480724501444400950365802007005401c06461403990640540e002060b6409040390b00c0f03245500503205000020221000c000d50203e1081c25070210b1516403038150300d131880d00350800d10180a0092158130542c0c0d42c6220038110354465106040b65150402d03200580c108094020303403101d12007001583c442851001d46c628810300ca10684503400c4000746000c2c8040d00300007441c1c008001000044017588520b21644600e981d070900516481c003a11760010807540b1300045064141d0340c8a60006019a050078482c000550300030b004003543d20420301c0c00103100c580200011000c1c0c00d000e400c841324503400090100c0c0e010341c46401001564011030855541c02d112100446583c0301d0f61083c00300c44007140110032400d61007200003589614951040f50128102940e640c0e003242d006034002c0c40440d900203241c608000380c40c011528220390464011940c540340a0b43c15046480080210064 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 83031170 1250 83029920 83029993
    0x30115031d03090310060e0c0304060f090602031609050603070509030c060a0807090e0402060301050f18070908070905250504030507080604020909030306010e040203070201060e04150608 82
    0x20920070341c000d004010840d2026642804260300c05034407544a076040d01c2c001d0003000f0034221011130b140150800c0f220780243c2c09001e581e41012000d015003000e801103610941311480c11280400d14010f001c0c5980c062400160350317091010210b03055140380e014a0040c407280c21007c20450380c5240550b0b504c0f21079414142d5894800d580002d080401e6010071641c814004503005580c244d12a0205110320403585504002c281c644490040030081100c00940c03100c01000103111504040b03140083c1d070074015100d1804000448074251002c8001c079000720014014982c10095500d0400c840402450002c1c8100720909007400004545a450b00181e0003061803448010411031003603085400940d040011f54001d41d0702e40c0007060321001c05035000d900c0b44981c0c8010401c44200407040b41d002c1d9005840c5c0b442d54003400700a02c006904002d100f201903569031180003405d406546002171140d44a0242c1d00b6a0a143c240c0003405c651042c2c0011081d0f500080302d1031101c119202c0c0d506001111990074111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 83032420 1250 83031170 83031209
    0x4030e060a0e0303030103061d0304080d030c03020906180f1815010c02060703020319320405030a0b160207050901060c0c090f1514180901090605070203030906010501020706050301 79
    0xc2c01e2121501d010740510000000205004c0c80754424012111034034041a20355442240c1181c3d41d0046025503034050f0400c1081084c0036000394004585245241805407c19400c0303800030340b071a0030202d10919640159040714030a85010040505524022282e281c01005100c14514072054014a00300c0610300c07408940005038014589410035550042c4100d54444007864000c4d2203030041d2500400412260001140c00c1c1d0003a60910307000c0c07120113156402e1010440c0840e00604c0c03100700400300305800300030100d42c0d07031428065601c86501a220841450500c040c489000001d8100242d08641001d402132140d595000346250440786540b400e201d5200041c1004849825142e0015842a15181510064200680080074008040d00c2d10140d010380e281c2c0141d103408000d260b00350740800b0f403080c42108441080e03021600b080d03200b4000545600c10b81d4540044441c140c4d10070000da031022040103115030703003003046a01400d000e10250280c00d03e040c2010701a40018096110040104075540d032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 83033670 1250 83032420 83032427
    0x306090507051c09020d050706080709030206180d06020409092006030103020121150312081510031b050912070f06080a14100501110609060408210709090c0804030e060a 74
    0x104c1e4160010300100e40700e1120301d00780b9541c1030288540307000b1981d04800070b0440b0303008003030005c1101e4002c2c0007641b91503180d07009400100c549c1c5461070381c48400070f513408020515900c0a000030340b60038200000d2152586c20032480d80303416807010440c1c00610b003400744e20b20341356802920704495081c2803480c0d000808800e055600200c11000d1a0070620f4200032410080480c00c1d0030301201d001d20421910684007007401c070340b40721044407075040e4920600b00312800b601b8070500c051140d462038070700080e8004444408003c10002810000c0c00220041502c01c1a0304c0c01c00310a42d9000440c000504d02103180044446080000d40f06010a0080020000350404c0340e9170014607983c04c001241c04824900300924040405803401034600041e0756803440500c900000890600403c0c841c401000255259551905c1d00d40c4a54401c1000c1c004840b60403c0310185602083e02454030340c1c4860a1031800c1c1030a400449100c071b41030008000888043c4404243c2000c500860b120003900d11301e6480c0203c000c10f0f07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 83034920 1250 83033670 83033681
    0x40b0a0501051606090b070e0907200f01090503031b0403031209020111010e07060201050c090d0b0414030301060c0312090201121d0718060f030c0b0c011512030306090507051c 77
    0x90304c036500b4a40342500704548000c0031031045120342c07520180300b4001c2d0203004407140e007200d6110209200200005075290110303500d1050b806220110340210800901c15400d444d041001150994404000e04c0400440c0b6502980c1441545d1002401c05140d0385004005c84100241c16003405e64031b660708815039101d408030b40c51030780c21100244111400d40c070100703070355000314440c2100552912001c00c0d25500ca0004035a501c01e8003c281c10007140d03040c1c03a4060080f00c0540100c5050050003e5125803141c203002460080c01a0b40358072442c0d5000d0704001d0b18210010120010651500d50286d0060b80c01c209007001010080400052200c0d0003032405038030090103040039407140320f110000038000400d40701003508442205400d01070142d640e0305ca0301041e00346000041c010740c1c41420500903030314410054218052210000b04d40c107114921400d1851400b50064210514120600c0c4103054040c001c0c41c0c014079007054100007034501248000e000d80507904c0d07140c1c04042c46103a44090b03240540c105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 83036170 1250 83034920 83034923
    0xc0b060d020a060e010e15070305090303090d05150c0301030b0a1d010609020d06050a0e06090a06120c241d010504030606061106131e02042004090605040b0a05010516 73
    0x180c00b241da4543c90050030f8607844c00d4810380010203411a1102c14140000702c0c1041c0050607101030b0505244e9035080c0e4664002c0f09906070544028000d002030b0f907489005620030280110082c05a2140707007401c900384400010700003105460200010400108002c2c44141c0c0440c0c1c07900d001682540b143d05401440b40510102c032115070034010b020455001503401801644000802046010b5442c001d003c000c1c0e00921500c4483e804c0e4400241450404114546e44038004402c0000c2c0d80d61240c924a1139021040c03001d9490071600c040c188407003004540f216080790142610030b81c0c4000e4075039005003802042003004400c082d60315078a09660b4090b20541e4042c0d94050014071616440b1840100321010f0550050340a00c103030302c045040c03903038507203440c4840c3c03a04a441c2445000d2001c50075006080b43d14001c0f07800035980d1507220010b501c7c170284d00e603c00081e040c04d561340c0da16010790306040c0d070b601d0380140344154a4920720390034035520031141008a503c28200710381c486185007510054140c05040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 83037420 1250 83036170 83036179
    0x100501030302030a02070609031a04080c03030a0b040e0f0a03050a03091401050a062102190302131406010908060f04080417070f0b0313140c120703050c030309010c0b060d02 76
    0xc41010303000302c040c007032004440c0e00722041a980c030710049515005a1001038588048001000b03c1c40001c010110391080c040c04506140001030a0710074070710303442204d48580f1159210548481894680140000c5040402c010300860f02050140d40d2512218900101404800240072030110300a41028004642085d800386070255284543d82c080d10003180d8104403a0f00d0841c010a148410b10001d5503050603840c8044000b440300e80c00d0144402d003864007402c9010003540c0000c0160344500e07400343c09600038070001c1000801a00030301480031001e007042c0c0c1402441c1e0010300030414001404e650055807803080c004151610b04041d0800d01c1503421560040e46000e60342031100c5400288002115401181c072005140d5401c4910070754001903995000c080d24400002010a171043d00790050400002c00b514115810780c000130b90104481c2c0d02d03030b88258000c02400c20a0000921140003000c40c1074000e58645020388000804001700c08100800749a803a00108004e6110100e0f0800c21960262 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 83038670 1250 83037420 83037431
    0x7090608120f45090c042412020c16090506030a0803060607050d180b04050a030201112a040e030406170a06080d031413021c030e0402041e06050304050303130510 71
    0x110031283e80742e5031508500403003038039011560213220541141c0403640c4009000c1780ca51600241c0c02d00d000318210866080100b44151b2400c240502c2c8000c14036010a540145440200341e0000c3d14003048135402050381c5450407040051070b440101c0d07295a801c0d800040e42d41d81e075840c0ba0025055002d1b032903024007140308017a40d812405401403000a19106840c070281c80c8903503640c1000301a48100c0c0502a0040c1001a007080154080e100349501501440300741c413580c100710325600b50308200d030340760420380701c02e609142c003089003094130402c00314002d0072000c0d500c1c040c00d1800143c03481c0030703001054888442e050001200303035032194081c0002e0544001500d0b007201d0b80100c000e001d0030304d6015071602c0600c110f010034030408240c62051001c0354040d05000d00c4803110612003984640c0588207a080c00141d86460f403440d5514801800a00340000d074014444a40c0140101d0940c055003000d400d2100c10001c0c0404a000001903961101c80c0c031010049056052802c20304140303051503585559803c11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 83039920 1250 83038670 83038777
    0x80c060403080405061f03030e011112030610030605030a080c100509010212060f0102060601140c1e07081603060507031b080603010e0a0c0b0901020f07090608120f 72
    0x40b400c0c000d40c0103408681c40c948030b240302001b0060100c0400082425618810030010740140c608651036101410400c3d0301c501c9841030b66041054100100c4074402c0008100318084c03518409000741c521040c03030704100c59410724006c80e5a54032406405085948040391107036022104100202d076119405100340594203090103810f002c0d400004a02c3c130750f40041800124281080042e00c01c08150580c028140c98a81000544102080012824001a04029040044108025070011903980200720310403031811140307142c2403003210341002001c0d420010344858003824051204048c1da403c1a0009020349900600340c0003004110000300404143d074802c82807607500b081d0310510803002a0001d2000000742070b16641c49106280e0000c100d0080c00c0d20901c100391503140500039100040c011268080030240c2107601c0d001d480d50000940c130361600c2050110740c80c00d000e40748861202004160601120003113900890082045040f03844260328201d90104800c0c2e9010782000001520710b20319200360 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 83041170 1250 83039920 83039927
    0x813030804050a09050601020d080705041509030515060d03030e0102070204050a0506040501050406080a08210c07060f0603033203090c03060f062d031006060f0e030d0309080c060403 80
    0x180b041c24460104603000003604c401c24056984185016030292080aa03c18426500040040d009008128051001141074440c406007441d04040e240c0300e41c1e840d1491441c04034504000c40c1d003115103c0c0030040c11b0118a40704e40c81000000303036040c24080707170328690300190754024000c080c0080c0d40542010103010320b602c900c0c0c1c0490300070781c400da50621681c0c2e00c1d1000c0c00199660f61082c1e500561050210502160030117024003000e84000c029034a40f01401c10204844403401e42c0c603450810030000d4110102308c500d03c207500da0303008109403d000181c51914040d220140003298500f20000c0100c0741d4a0010310303007100d401d100407900040303a01e17030a00b03551003640ca107a0129900c0c00707817188401044072001014a102c0c0318080c005c0c41416000700c102c4030351403507000c00042c141040c800c8164505055600b0f00c45000d01d4080700703200041d03242c030705100240100400d507490003c5c041c0c0b80e58105940e840121341c4002010540c1808962a185c42c600203449100e0100301c2082ca00541090204150b070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 83042420 1250 83041170 83041177
    0x7050304020f010e060a030228050307090602150103022112040f0603090b06150c010f0f050f160f0203040902070606060906050f0406120f0c03091506080c0d08130308 73
    0x303a80200408190b00b00546422090020460340440184650700301a03100b60024650a0600b0b0038010801308282c071050a003c102c444510003040d0b010040012541d0302c180410b009040c81e200409108083c6100e10090340c0c01800068090000848800c0201ca0f02400d1480010706030300403500d983d44802118141e981181c0284640d12250b41400940b0b5032190041c03440c1a81c0001040f0502e0321507100b00401c000900180311000c02052080d081d44030070a11400003040420500070408000242e004021141c00030090b1940d04115800c0c4a45000d108420803080d41c11414030504040c524070041e4958040c940c030404c05140005482d008018940c0c100c43e003112255200c4c0380a058903048140d03014003400001d0b89020300709002c100318292003080c00c0b010724072210342c0004110b901c49241800751042100810003103511038892504010a61a0400c1c1519032a80200303d41c03414901066202c400780003105100fa11090281003d00200740201c075002d1800e0300d84c0e04000d580d21710700032110383c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 83043670 1250 83042420 83042423
    0x40b1b1b0a02040e01060f090c0c021e10050f030604090314071b06030b0d0605060118090507140306011d19031a010b090a090510030c0602010f0b0414010302061b010507050304 77
    0x1070410382e4211409205008080c140d80220f00940740302070034030308d41400800641c50100101300782c0500103005a1102c1c13142c2000c28044090010382100300800b0b003d4140c20809050307040081c10044a03440501600641c0d410203003c480108640c000d41c18100c41d9060381034000b09291200140d040c3c1044000044154050a6000b45000046e0b4900c42034003205c1c0c03c02c403c207800090a4444000003441640103a600c80b405041a0341032000140c0c0034080b0348840d420414400d580c4a081c08152500161040301454110101900c2d40c038080740000c054080c62180398400f9400c241c40d0f4126550350010501d0482c2c520076620120650784d050162407111900440b821201000c1c001240c002010380484400c0c80000d410001901e01d040784007001060f0082c2645000c41150744040300040c8504142001400198004903001c4502050002110074081802c0c0c4101d04d05815096040040ba04039411030742c0440f50340303480b001c054040c800340c40602c0085d2240c5518040821507941c0e040405940502d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 83044920 1250 83043670 83043679
    0xc080f01140c030402061b060106260c0f13030209040804060810031709190305030d0f02090f01050c03280e0d030915020a080d091a040b1b1b0a02 64
    0x4102241d5488140801a00c121004203400c01c0042c0140c2000d1000348480f02e018005010641480b0040c5401c0c8102a00210001107070440d0145210003142c0ca00c41124031a5103505913103081c500c04405080c484d154682d2045940403c15100000601c1c090100450300680146100d20385468001c1980d8018007440340403400d80000300d1001001440c440c07064940c0400711650304100600361414a8100881140e40003110841c1500545000a2040000c5100c2c10003035841c2c04188401105507150308c00302d00903003441444020001c1d96895000c003042d10003820f242d41d4901c1600c0095046120380424407402e013800a2005034901c1e40002038440429841d651031180282c2c0500300720700c4000401018000440e8610244203842c01815030800d4008140111581803420350380d808a29001806901011591050310900340400d0114407a503500c10303848414400e15040e80c407010700c404007400d0b103990020809800c0301e011110701d04035526940545a559244066210711941c1c852a03100102d00a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 83046170 1250 83044920 83044931
    0x20f040e010906051e0717060a120b01170307020604090203040f0c0e04020a090209010f0807022d06010519060e0a0b0403050c040c0f020c090603100c0f030e061e040501090c080f01 79
    0x40c2c120001700303134060002035a45000310180d442e080000383c48064241039100721442c0000813040c0414030b17400221481582c081c5495890004c0c540300d4045100300f000041e4004101500c0103944107c100c0c0d068480c402c0005032079480d6030900d0b030604004004024031011500034041500f401201105118030302c00c03109c440380291100c09600582c0103c003961330108800907060240c0f6800754184a9000c0c0d01071044840f440c04441c080c00074501010401c000032190920880c0f8400f4040c000140500000e03202200e1404030745201a02c80040c512414081040c00b0264055903500c0001c0d0000038101d2010315611107440781003250b200d82241e40341d00d2065141c80c4c060703480755019591031400c1d601e107074000e02400e880342d80c1403010220000b015070b94107004072a61880a440c940c4203d81200e0500d590f0340c25109806040901125000d0078a801e940e40124100640c8025441080c0329010700d0369001402c0e516541f03440c078054441e08100400100e85960049000301c2d0001351700c00701d004424000d110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 83047420 1250 83046170 83046211
    0x1e03030a021f060e06040c020a170705011a01051c022101090b01031509020d090507090606020f030c030d0207050c040e03090f0a1412150f010302011e0903020f040e01090605 76
    0x2299111301c00c4801d0b401403031001a6261406901441102800380152005a00140d80d44e8100d905002c403480c1034500c022811100f070100c2403081c1075102080c000d820044101c0d40e00040c005008285840d4480c0b8002070f6040c0e401c413850340517901144a0f5000c02101140b042e4480c03075190070240600320000303281408802945d03120703008289655100e1110700c0c14846c00c040f0350901940c00006c0b00340f4074039150954003000032000c10409000308812000007a001c0e00700301e8024149140c40c60002e040b0743c4144155040303d0008011240c910815400051b550443d510300359080069150310254840e2030080c250300700e203002000a09100d00101c80c20007180b8421000c1103a03c0e5003901941c04441c90000d44002542001081018018000d00807280d81290352030f41c01e40f40702c80c200c2c2d40000d0103000000400440d40c01542c047c07a455205c40301c4204000749804020540440c030321019118a00d400c1c01d9000540741e40e8404019000c0d500e000348030001d031908107034001d0714041c0c40024503d0300d10100701c1d9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 83048670 1250 83047420 83047483
    0xf08030a1220130314030309011113050918030a030e010b03010603030234060e0f0609100e040e030c030403110d03020706030e030f0301060810090b010207051e03030a02 74
    0x1121541144032064082c030b41020520558003c203403a15810409040007001213103c40c0c12214024aa040c0155039901c1c0218500d425584101e0301c842614600b4401c4119011280c5018003d40d101512040749503521440000503010303050f1009030347e0f408009215554a54035820076030728008075100a010300b40b0442d092500720f61661001030b00603003224040340d00789861900301000849000c030452050044600d0301841c003c4041c0e0190021506441074a411801c000800150070b900440d080da04000c194030203c0c0c002c0e282e00820a04101c1c2e03c0059076856500c0743d10107250030b03901c6801c6070340300c89603440302c0c998aa00030b000907503440d039403001d0b40401807070700c034a04261075907160303001c0c150b10340c1f07411001d0b40a07107050700e01042d1600050098038104040c640c00341d0700905c1590b8501c4110b0601741040c503c00070890b00300004036802c0c20040304659070000390a408880040d1009050042c0c00001c0b00180003d004a05516000006010307848039030000e0244002d800c45003d51040d00000340102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 83049920 1250 83048670 83048681
    0x60d05040b060a0f05220b0a060507030e011409060307021c020a1a01030c06050d090204020f12060f010503061201090b010e040201090e010602060c070f0b0703020301091401080307110a0f08030a12 86
    0x2135211600d20801e850500c00c83c244101045982d0f000440d90b201461f0024080b80c40607000500041c0010995100b4150b2000c10341003518028280300050055a0762420f0311407183d580071380e000c1c03130000001c650140c1c82000090468000200c4041854085010003900e0b04002d00d403d5034001c4c403250002c1c1c0808240d0220324100c036402141880142d12303102040d541500600710b00e07111035540340b0074000580c4890001f01001c034244400e5035502e00e440d4801000e4000301402e602e01803810081c2000c103c2e43c11004694016608035294044031081c0340200e07014215050009007102035880001139042d00e0484240e000d00d100340c0300c4440a0340c40350000c444280c024418080140d02801c0800c40050345a2300500086014004484280301e0700d4680e000001402c0e520140065400001004403580d40e00c41c80e00503c541c0012030350b41794500301605541e4080d50b48058495802284041810780e140705003d00100340c003504000d040703541c0380105610303500000121801304260300030702440c0e1156840348 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 83051170 1250 83049920 83049929
    0x3415020d1d0f032505010807030b031510120f030f0203030708070c0c1d0402120114011a040e070e01030f0902010f03050c0418060504061e090902060d05040b060a0f 72
    0x580344807020800030056000c4618410a406001d080d8014029807410708a610f1180254402000c030503152400050000c48000c01c03040406140188428180d500400c45e074094040703401100040e40c86031406510000c049610070752000e030700342c14203504204004060883c8280242c0300c8035000c000304c0c4d01c00ea0303d03840125411800503c0e400e0010b03400c94010170401240c1c901941545c3c840984032601c650340c031034001c4480b41035960b80307808000c01c51802421221500810b44001d100804540e0b500915002041c09030804048003080084c11850801c01910014410040001c0b000c0c14002c80c0580445020040c05000900340000750140000c50300030925120390696450014000703002d000c800504028001881d8a030341003100042d56440703c10301c03203111003102000040181c030f01410081156401c2c0e02031001d002d00d444109011520f04140c0030100d601c42c002c0805c40d00d02030301c00203556102d0314183c09145440c107410320060143d20800395200e00802c1e501c0030642d90f10b030200384600c511240f08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 83052420 1250 83051170 83051207
    0x7030207140411120a020904091b06020313060509030c060307081f030b0408030a15180e1b060d0e06010303120b030c2b020d0602030412030504053415020d 68
    0x141c0015130302c000d00d041c0e4403e103d20401420104800001400d6030501d640940c0c4030304000003e8400703100d5250141004150900040d4138108400629441da1503003071085000380180402c4281c10380c1c03014450401038201c000d18440c0d5928103c2d0010f0480d04007611170911042c40f00c13841c11171200104240800b03503a048a400902c80e5610799506446500c01080403264588070503083d2400c515402d1000c02400400394046400c0d40c0c1401010100c030681d0b1828003907944140402c034040c1c0e6440070700048500d0280d4040d0b90711017881c0a42409084003005a00c65032245078000018194080c07041504a0185e19052002e804000308056503680d0302182c06a1202ca03882c40d050442d11420b205010460b81c0780d1215040200300c1d00000d000312582d1070300340e511580010812080001181e4204a03003107143c282041241029120303107035515180951543c0d01c0c25031808412040100154001c820301c0080c100a091a80750511850302ca5409120140507120f460380d0701c03850038058404000110300004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 83053670 1250 83052420 83052427
    0x206180d140901180905090c0a050d080306030f030a0504030320060a05060d0c0305010c030c11060402060d060b130513140609181b09070c0209040b0901060b07030207140411 76
    0x441c2610315405064601d061126941841142510b0703c26494010f102c1540c00064134030341005801d0505012503c810301c1000e1681c4c0c144400e0756001e030f1282001c0e03005452681c80f9618940424a465911003400c1854480880e981c240103601100a1003901c6c030941d100f00c1e049000403240807800e0588424002c2e20303000f00300000c0f440856948000e6010000801d400b5983c40241c40352203614010b41c0041c1c0e01a510b440c05201210740600600040e0f80191a1050300403409810f041d840b01d5010f04028400c500002c0e2581c0f4120540c1c00c280090720340800e582d035a9a0b829494802e5403180d5110341400b40d0b00d051082882c05843c3d2190841c400360813084044165604802c102224030014003009490a10b1159805240d20401c201c003600c17002400c140b070303a5070425010400d180314003d100c401003003501000000140c45d0144020b8001d6840344506000f51980c480090240040c1c5d013103100000004107210040c15070005402085031031080f81d0442d038041074018802a81d2605400b03285408041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 83054920 1250 83053670 83053697
    0x10090903020c1201061508180303060901060c02031507050a1112040909080c03031807080105130308040609080a1205160e0114160c080606040902010906030902030304050307060206180d 81
    0x8195002d145071103c0000240c590310f51142c066031130800c46011002503488000c000f40414000300302d015509444009501314980380c40040c0090300c050148408000703902c1540d81c21910208001100c0360b10710a21070155160010009045801c403101780b17000160182c5150440510100301f200c0b456071807007200c928260802d41041d0141041d030104071a100010401d0402c0402c0c02e101450181c001910801e1042c0f16440555107000c1c0782d40c01c848026450141400300708443c840c40300c1445036040c01c11814aa03560f050030402000c1455000d080031a0004651400903803024202e420b900c5915002c01198854452104080f0000c600a101007000200044019800752464006540583c4039151620ba85401d542080c0d004142d000c80d0401c4140c101803004190030b02c10107074080303401e540c1005403018507000244407000030b100c0d000606944140c0c200c2552400c0c0115805041e01030f0440b00d01c180d40e104025a1040111921002d000f417240300010301e0f0780d01041c8540f1200c4540d030703544400d8212 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 83056170 1250 83054920 83054929
    0x1406030c0a062703050304080c0321090f0607060501060201020a1706030a030809190501090c05190506090d080f072a0603021b010e06070e042c03071a10090903020c 72
    0x1107140c10140400705903c00000aa000c000400151107103202a10b0303c1d40922061629100d007200c2d0260030140b0380000b8440e030701407040c02d90304225001c50b200020141c4074070114020380305021002d0419410305001282c4c807030b0150000c0003c1318041d5681c10380c0e2400307007022244420b02600c0061341070308048c0c90000130911440845400c1007a00054615a100381032210b00503124480003100d00c0e075162190303030041c42240d40440004001c1920045a0b01d041c03c1c4c84401140200d00a443c814232002c24802c9294035005505034615a0041100d5500c0020a01c860550f4110883c01c85200c042804014400b1422104003580201200d0140a1050802500f0340c040c0d000342c1903a48070091421383c04c0481020900a010005400c03502510045c10310f1031000300854421413440340294208a651321042012a0380e00c81d0362540490390402a8510303048047c00c5204460019080c01d08a196018480038180d480d24020110760005002542c0d0b11001c4c00146d80e403080c0040d0158101c60b0b0420410b050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 83057420 1250 83056170 83056217
    0x1020a0912060b09191505031903050906041d0a0902010c0b15100c0501050705030114010c023f0c06071b0510020304210b06100c05011406030c0a06 65
    0x2c90500071844115000c0466240d2004440b51300408208440d1029100590300c29101881d2003900d4807040a4141008039a58642041c05040ca410003403050701d090612803000c0d0340c0f0514005100ca03136925a95544919400c07001081881e00d5040300d070200c0c1400365240b041d810070a5042e100d900c6565415102c0da03e14000003095851442e00961050845070b4940d14a03558848003070700c030440e071403009041c41400c46078020010b8061020410052145440400c5002d0080d002442e180d08150300620101701040d90b90000b1030408540036000c40114507144c020b0500751000c8070400fa0b041c03a14181d078141d40700e00d4440102e81100c0100041c2010031340c034044404d80064a0f280c6440310b0f80e6200c0104140e20429502d8030b006800c0800c062156558004002c29511010b0440501741d854a46460031041c0e0702174072080c8662414082c2d9041280542d04a14038507070850000c10800d040c4d00603801000200b00d40892181c042c19810038410710740128100159401540c0d551070401b44401c00c0e220300314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 83058670 1250 83057420 83057423
    0x403080c0403020901030605040b0603010903090b0c0309030f031b0c0109052106070201020406111204150921171317010905190c05031b06070c090c08041401020a0912 73
    0xc004200c04000360301d403420030600135441002c00041a140504005602c0b0001621591181e4104207091001c00c0c1c0c41107280d010390f0011100190340e074510641840c81d602c01c1d0800c0d01d816020301204203403c800084080c10744e6660503088000c20000351070b81e10b03885c0e182d0003c03000d002c2040c1000038170035824003480c1040d921045142007151002c0c1c41c180d440c41d1980c12111000140c4d0005000c0c080b0542c81101c0b600403008400080c101c042d4140c840300401e0103140110401401000009864280325001ca0320060148a00382c010183c499080c03203554032003040056640d107603150303003108200600c8021134401d0700c1090780f407501311800c00d0b92842d280c0050a00b0b8255075921a0205c1000c9a0244054400d401d4103800c10403800c0000d140110582d50307682d005074402d0304803aa490702c0440c80e401c0d0640c5201000c840c40c9984000e5480c20a140d0300d5035400c0908032918000d8900c3c081508100c1c098041d900030a140820450120700c000d082c2e11030000c0d84400210042000c1100070903001c01420450b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 83059920 1250 83058670 83058691
    0xd1a07050c30070b100602121602041401080307110906010f030902151201050307090c020304030f03090f080609060c090604030b15060a09090b010201021216020a060614031e06040308 80
    0x20b094590141e84182c00100054031800d0b070000c14000b142c501c40000c200104900c2c000303002d04c1007030585801d10b28094464134014080e1002c10910840d55950310202c0120381e4071520101958442c0e00b0340da641d8020f148112510702d0b00c064260200c0c036000340481d100c0e01050391004014140101c00720040c100c000c1e070482c0c101d03134000b65400b4001010000780c2400b06c40c42454030b03030340d600d40000c00d4070b40203407a44000045890300410500c0c0540c080125015240c02000b044550176245c40c08a980b64456404506d202c00b00b10008245d40402203950381c0140c0c0f8290880b80540c03645808001a07200d8400c600303500501c00c001c20000100302c0124141d00c820108034410340b8410140100d0f41c01d60042580ca030029600086c184480c0080e84074000a984085c0300071410b04c1d900410001e081d10000d4984150840046600348040b03108200d400809540311206101d131503070f1441010500c00759802442d110340034010282007000b002e1042c054250b40b5002c002d00345d40c1c60342c0d01d00381d48041c000747c40440700c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 83061170 1250 83059920 83059993
    0xc0406110f0706030b01031404032304150c0201110616030b130c052203080706050406090615170129061605060604050f060a0501030b030a020d1a07050c 67
    0x803100344840b000500440e01c01250040c2c4000c0010b080b50161219400c1d081d0800081c480800e610020800030030111142402c1ca1081c007601d401c1d894040d5030300c0341c0041c8a03100c804a550583c840b810034040d610070303281c140507070840840940e1140022a061041100d40c03c00c0040c0b9a4440c2c0c00086c00d0007000340603018540105101e40c420381760f640341614045000056410442c03420405400b0481041c0c3d01803034003c03811603440c1084d07840f07420030242000d9100d802241c00d11401d54802c0c1a0b179035100030100b10700358100c0c96002002119201b41100c04212804401d250003040c01110400c440c80c0c0600304500740c4080071214001c400c60507464103d1401c2c440002c0d81101d507005108036500590040c01c1d1803408c04100003c1d608000c0105004848007001d04c055a00c1c0d285103081a51424200840d1031804980400d03d09090168080d41c0181c0c0500d1040030f1144031550781710794001e0b41c4220162070351042411b80d1140b0402c091880260f1000200c00d8000300d60f1684440c80e02c07264000c500c0d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 83062420 1250 83061170 83061193
    0x4170d0605150a020c10020c130609050f01030201090602010209030304054c1110050403120f090b0c2104020402040e1501020c12030f2215020d03050c040611 69
    0x10603550300d0b42040030b126000903086a40580400100501c0716003100c054180c0841080025145d80c04500c0380c5000d2054a900082900501e801035005410031382000c0285c1d02d01072950b4000c2c210203110590108680000100c1d1492040c000c4802c0303400c0140081d85030914110601007807030402440d001000c3d00e0b000e00d07554040748011881d140603200903e00d07410f00c1c6c2041020034042907004113401c00e10004080310780d44920301090300303083d050540300e00107101d544905054861400c003c98209207280f40500c1d407d40c074040d0358480c070718080c011003c1155a5840302a0f04540303214000402d40d66450702541d017124490310401e85035110780301600c090704040d074550b201c031614081595202014a10400140345a5904100301202c090045a2149248a80d0041075449204514072904048400079a140c4501e100c060301c03030040141c1e1451460400d655504003c00c855000008a005025038800d04045074480d025180c025020124428039151a107841610501c1005540e00709500658102d40d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 83063670 1250 83062420 83062429
    0x909040c03080a050304050c0105040f09020a020708030a02031c060302061209030f131517011806231f020c10030b15030603070803030c030a09030903050105040c050f060304170d0605 80
    0xb46820b0780d40b505910303400c6c280b41c81810048408102410000140800c00c0b06050300080c10044468207a80180c0d5055954030407410701c120380d0445c00d03d0340300024a0840e8103030300200421107103146003d5400010041c50100003551914440690701c2a81030050440c01181c503c0640d400000c03603801c070703440c3c0685106510741a800020001600c42d5070582c0c1000070701d041c99050240c50703015140010081b040501090000101801046e900d0360b1260b0390104180140d038000006050101c50906203880078244041d40a08000012400303a41d0400e07001550320252040c2208491054015125112202c4144030300001c0029090007095283d03c00500603032510303500c503400281708103c5541e0b64a85031040c146003000300c0d44071820940c030800402114261880070b481d0007810182c0042841071981c113045602c0110740d0800b5046501c0c040034041040100841101221401e4a4400e00001e007041044203900003114007601d61000c0194080407030039a800102031b0b405000100154be56295404038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 83064920 1250 83063670 83063677
    0xd030c1b060501061d0d11010504260f0d0e0108060a0506070c030b0c0c0a080304061104090204050406210201030b03010e01090605040b090f1002070519030302070308060102120909040c0308 83
    0x19240c1c40c1d038070001403081a5018995940100740c1c5800300d100d5011190100b00320020442001e0000c0040e000c0f0112203030701c0348084900501360303444c1d81c0c08840e0740030040216480d00751003c01a2440f80303d0803105002c2003c210908500c0301e0f61039090030705402e14010344500c400140700316401110351030701203140d0303403154040c210342405031819502030703400c41c0b410303041040b40588001c03a40342c1e00b84a0340380f10b03d07800908401c01c5540413009070b4903a191441d010000e400c1c001c00300088100041008646108103034060800c4401c120303400d0003141e84e10303900a06080708202d00840e21002080c00310b07000d54029081490545006000055112804040142103d41c030034402c8600503150020710060100003404190002c5a8602400c07002c0c0401110035583c9003644a602e40e4507030082071040901101b8801400e0b0101025901481b00c10b891a00034000d6201040c1200800c007d40d0114880d5440081c02c074104000195500d458860944c0411a5221000b842203035840310503040440000e4040001c1d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 83066170 1250 83064920 83064923
    0x80d02190210150b0406120207060603050615150d020c0705120d030b10080103021009080105010605042405041703070204020d1413020d02010809010b030a05100b0109080d030c1b 78
    0x1410100302c456250400f074541c902210510300010361018040501c414048a08480c100d0600602d40403001c0d40701d1005e4010780300050300780c61030450000309001d00420003501c164920b0314481ea41101080811047d03140a00000c0602001400303c11040f6203640d00411556802c0011541d85641d19000110201c0c06280c0420180e0450a091000d00d80c05014944200301c0886410a500c2d4026100402a07441440f010348207034040880c101c0054043c803418005000260024071141d0f03112113029020f5030161040a0100040c031a00700b00311442c4c1203003103200c13000c0383e5660f502d4245071461040708034a00c0118500c55000810954006941d00d1000300f150301300090012130100c000c101203c107495002442d140685407400c40400042e60750441c0d00c0c9040e80c0c2400c2500554440f0b0704601d0061103900b0000b0781510030f48101001f40500040c202044191400e024403280c0d15080045030302441c0f038410580c40340d008501c3d40c2030160103038011103845071007481d145a1490103031280c0350500660500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 83067420 1250 83066170 83066173
    0xa060602010b1c02061303060207111f020616030e01061715010806040201031109030d0c060c09060207090e0f03040b04050916080610030b060c030d0c0804030903080d021902 76
    0x104010680d028020b0700b0003140200c46514015200b52405440c400c00000300034840d41002402c543c1c5488001c030b03040d001d960080d00464072030350783c0e1404c60303403844505100e944604400c2054035041c241103c440c0c0c0354543c059000d0b110b251601800c12601d403d9603400d800c1815140c12000e544140244a003a0080c40d100a192804411000e406410080302403c0c900000301c1e5007005002800300020199001682880c001070141c40c0c0c07042050160240c2c0e52090f82c11301071140300701403246d441a0414845d42c0201010030000c0c41010b03040c0c805450510460780581c0125104202110455004058072140749082d00d00300c100d2030725254116400341c0c001507003c050101c1e041c445800e140308904d40c04000640c0b10000c02c0c07400301c005400c1034002071440e4459004141c4550403d4440d4010f03030303043c00c005490b0300e0300c484070294182d41702e4105900c0782c2c804074070b00342c249c0d18150300c54182e0500498068443d44040360440c2c403002c110341d00115076004c06640800420980101c02465503c4200d003650 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 83068670 1250 83067420 83067431
    0x30b1009051206010b031303090308070501050a27080702191d0a110702120c0907090302090f01050906060a0315030b0103030201140403050a030e0c040e0109050d0201020f070605060111060a 83
    0x7420006031140103040d610b103030b50114005004246426044039000740107240310300d150541300e1400301c4d00794006070801400796801140c14410030405400090007001820300501000804805001c070708040080c060f60800e000841b4080491881c00040070341e6030001d00611000114040c1000740351401d40c2c0707c81c0d5444041c00415181c0503540b142150000c2c00441c040c40441007a1200030030034090214040d00c00da401c014031494580040010f50f200e248050302c1c0c28904d150050014101241a102c141c0c0100b11000c0011120300c000e100507410b0790f10090041085803516814840c05410009000c0e080c0740d0388100008030a003680c000600107510030a4603110940c11490024291410600c0d81c035204c444c1e0b03000b80700000e030b0440d0a85550020501d400502c0b02c80c042801031502001c001c03c0780d046850440602c40c074620640001041c14000c104440c2c1d40e103030303100049080b44980303401c2c00b05010040c8068000100c80d0341080f80c0000c41403420b4030101d6092240780e070405170151550001960313104c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 83069920 1250 83068670 83068679
    0xd050d0906051312180b0f1207020c281e03050106141206040201020607141204080901030501060215131104140106030506060c06041b030f030201060609050603041a07030b1009 77
    0x8144d01284010301e04201002000e41c0c8241203140e0034014100e54810110307100c061220b070b1078182e620600c0003240c040d0980c1800280030b5295440b102d4810300400b07040652486c0c1d104030f003207885c0d022410716180c1e207800c81c94042200d10321100000c211342150580480000070450034001d401c090001c54a59851181011080181c204a090f8040440303030405170030131000d40c0e008118240d00c10160706040224110315064081f03540303d034100c890001c030350080600003807050000160040003c207803010806a41c031114160b0303592585003201140100e2080001340340b00303e04980d450b0b500e8828150030307030007503800342c0098295400030507418802a000401007000b5981400b8154002c14180c420301d1411a4410701c05888640080014003500183d60403030300b10074407485d0315000540d0008807150f0911761901e002400f800461207140001208580c02107224549901101c2c0201c0c0e10103d03a41411003d81c841085a40e00280b913002071665031401442140c4a80819400e0308027560f41d81c400243c00c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 83071170 1250 83069920 83069933
    0x111c050112031b020307080f06090f01020301050306070c060902090c070b010b04180b0d0507080303040b09060c0d0e1e0a050709020a020706081305030d0605010f030e0d050d09060513 80
    0x5a00214070030440110903404203400c0100075002c080054075810906200740040b03450600c0c180c1c044141480f407000d4030041c90b100410194081e0b4600313003d030764840410030303562803d0340800e00800c0c5d8150000c102248000f0b004070807441d01d6910546001c900c9042d0741d00012440c40e401c8030650030800c80003070032a040101e00c0131741e207014085401401d82072505100e05020042040c402403103900781eaa052125640c1c4e2141414500181d0000c11034401ca5281c14103551240c00c01d85040320a8414480402d940e024013081d402d1240010700368060901c241c401c01c400c0a00400800105107005221707a01325a0585080c43e03004800c00c80c8000c00d40004107280c01894011142e12120030103105106030034100307034040b403004220380f154506294a030325405500d140c1c048810341c00801e43c0c8400a09401428942d41128003140d4090300c035102c40103441c0000350151040512101c0705d42d0400100c0b40c0000d8050806040303800c215030400910852213665520440300300350740140c0c200c10103030351080c10800f2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 83072420 1250 83071170 83071181
    0x20a2103140412110705040c0302070b07140f0d0e0f071406030f040f05100f050714071203050c090a0308041505041406030402040b0907030501061b030905040e01111c 73
    0xc0500380c08110b482c15031034041e2464200010b0900300104804000002d440410120b0302400d4024020414004000c070003400035405000211810400240010907240c0250844100d940401c80c1052802000400c448610360048100c8516150b460390380c030a05400800c40c0d60a07d0418400601c815801c2144c1850b10505a044943c4104002c004000072010f181040b41c0c0c02c280c2c801005841160103180840c03d019141103c0b004091030486020440c10841e0060303402281c00d40c80d03210440c84e10320a1000117200d0010b010302201520b000340325031140300c1e611940c7e2040380d905102d400c00d0b600c48005803120441f5032007035400c0e0402080905c60440c00042050348080300e814041c0c82e140c54145894081241035250900c240c001000080c207540b02c0d0341080a080b1001402600103103800c29025000300800c0c011000000c241c810701d416040000d400c3d141348180c242e101e02483c00c8c41c0004100241608078070b4040c486d501c4101800e040285038000d030001512101401500c811003500005c01c903079 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 83073670 1250 83072420 83072441
    0x9091406010f0609050f0f030d0e090601030e031204021c080d110a12050c07240506010311120919050304170a020f040c0903020307120311010e0606090403020a2103 72
    0x10400d40c000c03c001d94004000342e04807103042c1c0c0d019100004460009041070511030700950540100c2d041140201c2d0302446100c1150411600740c54103888280044044030380758455840d1aa104200e04c000305240f00100390b070300c01e01c010303c184080501c0302c000c01c4410b8100101160ba0030000f00303c40341c03071480d1409900916210310300d16030700300b515401c4000e01c0d510402d0600d150351399031400485d104160f440202e40d01c441c0c00501a640303410100c1e61140c404420b0f00c680405e154584404a41158443c3c0a2091008080e5140360308100301b11030b04a81c90500545040381603c14141400307030740d5940c00351140f0120701030320140d61114500440840081014030102001d500301030402801030745c83d4003000d001000c4c01d6600144080d5501e50558a0220700c3c1c0010f0b40c9845582d000140000c400320481c00801e22076a12040d01c500502c0506090f56102d201c800c0309900074000182c0c160a203582402e501a0191045400450b03040c1c039074080b81c618400b1482c22006c01c600d86552a00d41500442c060070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 83074920 1250 83073670 83073689
    0xa030f051e07110304060e041b050301090b030c03100509150402060a1101150e010f0605070506072304060f08180c0603100f0e060a05060c0303070305040204060909140601 75
    0x10314180c0d0a840c0320012a85160301e046035541d022a4465120300c011004001c0d065013160380e11510360201819542d4241030f190304c107900b84212907290380505284d4005084140c0c503510705503402c2444640c0505081e0b81d886402d0302c81c14100003015a8204418151094119000200e50421038036960410722150302d201c4402c03520006200050306c907001120607613021850314210210a40919a02414054020250514800e600412180000f40200b412035203464585175030301d5a6000c040e1600c3c0500100605a40c000100042d10309004002d8044a1100301010008180a482801c2d00641107500480300143e03d00d40051011a080001e040d003015074103500b004c0240c590b00c0460f503900038019406001350008030120301034000c500c00410140c0001160480815280d200001040c18101d0384284a61a20303c400070702030410004031500404110055890345d507489130142d0280c003010b80704030f0304190b0301c160004e0028030f140b2070030301d406105200440c9087e01540b0110710b03000040e00200c0a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 83076170 1250 83074920 83074931
    0xa051501090e071212030e03070c061805060909040303060f0f0801050f0c0304060c090b041701270602090f0d0807053d0f060806070201060f120809040905010c050a030f 74
    0x4d00d0b42d4041d1901030580c40900000458482c10742200904100c0280101700d11001c0394240410400100d2042618240c1da01c1c489040413607210445040c12600c10345030070840c1000700c416241130060300660f1160103420040303000b40d507030399041080d04415807080041081582c000d200d990000e001c1c1a4024440c02e0b43d2580c18100520310002c50b00c0003900c0100500c0c1e80708140e08005000c1e00c2000024a9404180b0f03880b140c0d20741d071008039002e040042d040154a040b0928100c43c0900301241d6000701e152182c008e0724130303072692032000039402103031126070010030366000e64811f9950b040e2503e4214485c90040381c848000340340c198540303050b5490801300320300c00c00f164502001c0c105854407044001034280c002043c59221410b0b0081418405001007681860804141d080340000c5842c052032603a8001c000741c5980308416081c0205078010b914010800408520101e1606809088048801040090300c12129560982160020380c00303c4c0100d000442c044e1240f5070180f242e0a1740110ba10b405100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 83077420 1250 83076170 83076179
    0x190e0601031104090e070317040611030a020303190f0f020d0506040e03090424080109020307061706010309032c1206040f060504080d050c1b1516020a051501090e07 72
    0x102d0090340a900d040a07540d5601030294541001b80c0801160445c42c200300d85855070a254280382d01c603014020106210348100640c0c844000200c5040c0c00783c036400b0313500b15221b210102828039043c0701d601c103240743c84040c11501d0209500c264002020003682c016a07881086d01c1410542c1c0004282c1c070b00c41d901d8140e01186044000c412990300c0c01084030001003603800240911181a40e41c00300011096068a0124440300150720411000e8000c4046400550b540c11040311040c00d5103002020f08071f41040421341d0755004c2c0c2c1000c41e1081c0709081c4907103050704c2034803080c0356070b515545818046006164031540c00e0808005c0c8070400703181c02015108516142c1c8450042100d5244c0091490303689800181c04d0040c0002503a08502c401c036400c1c4042d0414084040c403d030041c01038200802c48040c10b202d03003030301c0004030000c9524070069403541541d6100201103102c6e200707400d00825402440039940c0090b0040c4400a03042e01c050b4134410107941000c10070012180001d0048446903c1000d0510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 83078670 1250 83077420 83077451
    0x403081303140a0c240506150d150512010606080604090512160203070b04030203011d2e1103150105040e010b0c03042103021011040612020405190e060103 68
    0x51542e841d030510241d542c080441c08684a00701c03900080c1c034071101040140c03044280c000134189030054000c814440c07a100c1000704007049000c0741c550505080d0400c44040084d6141c1c02c880403801407071035035410440d40c0c2c0002c59420042c4109000840c0d54420003403180300d40014200b90080341c1600c0821900030b045d9980f5030b482155000b07110b01100b02142414051506940035010554003405a6641c550745800514003038100f40422840b235400e210700c2c032500020100128500300030a0300188281c41603071495100d501a0080703101c101e0f44555020600c600c44500039800e07903240c4800403503900d14200a5010008107039068650410500700700800c8014681c141c4d0505480c04128860782c0c80200e103410901d9481103520a40020f5811030100d050300304841c11009400d8000c0d026a0311401d42c11000c01700315005c42528482c04502408280102482004520101903201e10018a02a150030004998110b0102030380c00984d100542488003640c1800b905812080038241800140c0c0c2c20204007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 83079920 1250 83078670 83078687
    0x40218070507110402070c080604171602010309020f0303180f0301060b03072a0c030b0a15090b040207051c090611070306020a030b100801090c0203030105031b011103040e0403081303 80
    0xf0307000c1650a07040600710b0f901c07541180e500b194000d0518030500d03911030b10b450b12901f0440f01030752080f079864612118011020121803032444e0b40354040f240640c82e68010b4004044400060b600701c07480f1040720802d600d0810007060600365414010007204c00c05010401c0004041c06194000e9060410402c03000d44814196a00000503040c000b80a514022052100c03810800000d04020b4010908200340000b5440c05002c4e6070080b124142c240c2d403403d10321000d0310140c1500d101e440f40038a2003080344a4203a80071140040e0300500240c50000305441c3d1038607001c1c91404101e5401822081c100440b038205201400601940c10001441801e06840940fa683c0d103100103001a6000140d001d5907a21a62094510b004000c140031034407020f151008010880034041c0041161070b00e04103945183c000405d890480300018020589074850f1141a209459441d200a0521154500305a0301840074005080507081c01c1340e070318900340341c2424002e0a80b0405891428568400020317280402d07070101c4070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 83081170 1250 83079920 83079923
    0x915060c15090f06060b04260607080a020f040e0702060717010605090d060c0e0307170a02130902060a0305040606060903030e01080702071205030c0c0102010605130f0603060212040218070507 84
    0x7580307103160070308083c4400d49041c000d18091070f10401152190025003d04161400708080c603540030b00030744c0c224490b403083d22102d4070795602100002c2d9045100e520340503402000b20301d025040407282040c01181e41c01130340140706c0100000081020ba180d0400005612080d03d24042e0050402d14801c00e841c0711045c015001003240000300d0f440152500042d104025030712401c00c0040c040f003481c4c02072090080003a00c0348203004145000400c42202056003202a0007030000d0b0103924000c2d800c020fa49100d480031000020748034100000581d80d07030340240000d2206502c001c103a03441c052800b0011152140c202c2400e001070748200740003080d4001641406124207081c21502c6c0e841c0c81c0c4050f031415170389510081c0a036000c0400c241c2000004809082600c00c074404481448180034016401c2e5074441c0104c42d0000d05400384108140c0f21038200000544824000082440d101d40307a01059900508400b045004c0000902c400c6080441d100b8005a031910501d61140c20071420052241c8185d080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 83082420 1250 83081170 83081213
    0xd0602040518061e03011b080601090e22020d0605070206180d050403030305190e1615080c0a120c03020306030c010f120b1c0501090c06020f0a1514010915060c 70
    0x7070b130850b4500b50b02401007000c1d0410285025a54170000802d0207404031003c0d400503100c80800220040c10768a05400f41030202c840b550074143d00c0d2035401d04d42003441416070740825020130340c0011812605c5554001c0d0481e40c0900120300c2c0820182400030140318030303012554040c0c550810040c0d80031054400340c80d0700d0f160102d1583c9880c594440d040e0140306c80e0801c8245007a03000c8034071071400505c5c4208103a4524000312296944c4030b040300e007030501c05c220380081040b00c0b001a072392403412030042c48020414140b1040e9500d01c400c0c1181110210034844010982c000240019490b041060308580e0000b4600b5075610407034020000c040300c49007501c502501391101902c103010b40d13400c4007451403a0840201e42c550769203141825800790010f8502901d403d0003109020070120300c04521881e42066520080850f00039543d00c200c2c18140906a0408d9131b5034404049a00d4500010028002d00700510003040707071410710b407010f078407446c0992007003040c4403040710b0500000d400d1640ea00c400601102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 83083670 1250 83082420 83082469
    0x91404020a120e031809101401020a06050f0a1a0f1504030803091506010206011d0406110c010c02060105030c0d1202190c080601122a050d060204051806 67
    0x30151582d1480c072207001c2c80c2c681058030f00368500100102900940e04031410a046000c00c07107040c01200c1d00d09540070700190281000a2044e5071004194084682041c030480d0001950354441c041212005e9890303c200140000a005040c8004d01420214010044d0440d1100380d406001605c5c428186414600030402d10279240203c459513410b490055402640e0a07075039241101005480d1060b000c10340300b4105100340400d11755480010404d050700d040c403085041c041810350f0000000500100112000d503162a5862082450480a0040c1342e2102c000400e42203086c0e0806401c0c000141c011500940c4001d010080780d6840c070250408203070b00301800c121000c1c40c18008034241090050600000c5007090901001c010722281400d048401c2c6406482569032102c0b0b81d40d603107104481002c0c0202803007420b860148022840500c064880e10010300e038650f613650f404151102c101000c02d96815501050130019030802074420007408000707107007580c240d24002c8005003000141001450607820248c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 83084920 1250 83083670 83083687
    0x18010807051b0303041a01050d061521021305061c1b0f0f080106031119031202030d050105030102031b0f09060d0501060e030604020a090c020309040203011d0709140402 74
    0x4800701da41900d464181e8001402e41c80200c15601e0380191811218411900251008050390a50480c165500108a5000d012031030721000068921440c400f004548200c0d0000350140c483d011a00d07a03455003103185031280e0743e14010050b0b200c0c8107810403000d03182050100440350b61190b01c0d1600755900396012188103492070408955601c0c2d80c02100c08114103000012a52040155200e42103031003180ea000c181603100c0d90107500307136901031200400c81c41c0120911042841c0030250006240d407001c40e415000c0c0e940380c640345070116180c842c0e030303025801c0050300781c601d41961702400303000d400b06034003d501e9800d200e4800c020b0000c41c61011444c4040202d8410101c1ca100001c8403841e400c01044241c1ba80c41e09142c640081000317109103408540c01c00d00c8490b02e4103000c901c2c0740c41a13800810100b0b5961034000583d02401800526170304600081040904994132480030f503001e012880030f00c0c40048000a4058140784005e4280c40034072904035801c0108109100590600840a4802685480c0d03407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 83086170 1250 83084920 83084927
    0x30609120715050f060a0b0a12051801050a020904060602160905071107090b0108010e07080433050105010207050108010305060c0f040314010f0f0b030604110d080403061a0618010807 80
    0x10000340b100c150420b824000d141422a08140c0030300b104036000901d40b55281e0200b00244500c1c100d00000c05d04205451941d4580c5910907903205c1c0d0b11614003594031512008460031200100c0715001384542c04220040282800e2040c00040c00050004101e170304081420074a00f0421441754030003107626a0000b40c5920b02c24006801d1a040746001c80b4a1aa110351024001c0c18100c03e00c50700203002c11000242d600c541e030402500034005510b0b0402103440c0c070385030030484039800791070810108c10410003010081003404072104640c0c20450300049039414200024201415a4441d9040000d4280140b000c0303013000c2040c0b500031603180b41c0740307a8800440c840464180219840504028030040350205007a0064200d2135034202c40e590100f00301c192809000003266050065190154880c5e0002400501c80d52480901130000400302d03a0000c0407a03903008540c3d801030304100c1b1159180d40c0004003d07a59000002e041d081c086650070b0038800380c000e4511040344100c61090400c6540c1c000300e018a0301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 83087420 1250 83086170 83086193
    0x607030e0d080304030305071e031d0a080403023c010309151a03030a0207030303050405030f030c07050705060304080706090c05060415080a020424050405190509060306091207 77
    0x141554608071020308140400c3d810485007034001c0780c14000040c02070340c498a454514405580c8070640c610982c80e20480081a01f105019041c10b2202c09030159a03108002c2d003c4d02c0340c0309481c40c6949a0541c03040c0918881d043c150348000484182e9035802d4001c141508040d110001700e100c407108030030790700101c0240c008103101801d1000b4400800d04102d006412441c04c030505101d503e6103400251041c16524031541d441200141c200e0601480020710031380001e50880c3c000d40460741483e180101034500c5074419940c074049484001140801c000d010301c5000300504085600364110314040e10f40f0141c03807050201c018405981e0364030400c100221001088082c220240409885903107401408519054030b80200c0c0104180400055500c6164003c540513207034151048101800e1060035083c64052140c418801d02078140f00c0402c258680d980038440d8462040c3c0b142100c1842c01c1c0902c5000e900c0682a1401f0b60030503030070070000140004214400f01c1c80d0640c0c0950345d071200e09001d0f82080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 83088670 1250 83087420 83087447
    0x110106090501150813030509040c03060b04060e0907031103040209071101090602130b040803180307080a0b011505130e0a0e010e010e0f0d02061b090402070c03060f0204050303030105060703 83
    0x20300c0c220002c18000348103c05a049110992902107880d1680142403c03003940310307400100040e03010000150182004c1d00304038440100c0c0d06011070640e40310030501c10030341c006401c43c5000a40a0000c2001890301c1040241c000340324b0f00b010040c001a41d08110907503c0000d0002e40500c4100020800e50b910800501911905a40007003100824515100010f0f500068007100c84044641012480030524003c403021108400020340c40c0a440050000b8452405403450703034540141c800c0042c051005200c01c0c04454030a004049403036061406403440d0520040c0311404020040c0420303200442c0320f0841e50161181130382c00302100d9580184ca070010305034040d64000075500b0030600354210b0405400502040c130100d03080e0b403840b000012840e680d424803a081d42d00103074414400300e2503044900700756035203800c0d80041407454020040c0200c0c050703030f0040500321403507220085c042044c01803911848070340c040b100b0b80c02d5140600d4200065902e00040c01030501c1540000b400c08105406454480d100c0b2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 83089920 1250 83088670 83088689
    0xc1209050d11030616020303061e10050c011103010521030f0c010207050c01020c180405100204080c09060f0d0303050a0213080a1a1e0403020f0f0706030e0c03060601110106 76
    0x10440c0d840c080d160410b80100250181c0300d00000301c0c50315907013500000140722280d4000c600350760365001000008a8046007a6100704105045038041d91606c039100e806200b19a02c0d0140d503640d1a402407400c40d010321715080d080b0b107024070041c04030340c0c0d46a0f1480b1710701103404d00882c00c00030403820b142e0542c451038940ca07800345000108641c4584064010303064050040054131181a54100107903110b644035101d696004030608000ca41c07004100075250b030014025802c1361812001102414100da2154100300110360020111300b003d0301d0044101944030f18140d03403e448007600c1801203150b04076040c0700201490785440001e04040030540c140c0b44480211030001014503602d0040c82c0d1107640f00642521a0400340c20004512406001141d0107811515642000c042e840c080d501419000613000300c045004800481c90050b00402218030200c1a40003d409940e14150001d402c484040e014040c2c0d64000c10b00c40341d00b0380c0d008140c00364050020300308200221446480d40e801080703190080c0522 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 83091170 1250 83089920 83089939
    0x60b030c13080610060e030a020a0506031003060914190201080c0d11040902031e2a070203010c0305071107030c062001020706060306050903161203090c0b0c010c0504060c120905 78
    0x4050402c2d140c40403a01252540b05100b06c80d01c06040c1c41d448001c0001c3e41100d00e0355810062400c01c500110307400f021807904521002d40381c0c0d50b000184d5058540542e05c8640d030713599180030300e803040c0192000300c0801c050044205040380d00182c0107100042c00017000560219030008a030340c0c42d401080c2020001a4040d580759118010007000713420664080d020000b189032002c1e450b41c103d20440c0d000f015007980c0c4800c0844458140114618606000c15050006002d2303240180c40074050315a1400a9440200700c600e4518001004050f2100c0c1650059011040c1000413807455a40e103400e4410a01d02400044080700f084007800d8800754410361650720009208047c44481d074001e10641e07200d5103003444251a00c40003540c1d00c0c044e004411042c0310030300d0030f00c000085040a41085440c030505010400e41d11a0b00d0342d1061201d55440342c10520400038410314070b64001c1c42100301c001c00c0c0742000b42c2400c1c01c00e4002003404100c0c400042c04143c168440380b01183c003c0c1c804030000c041c010300c1c1004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 83092420 1250 83091170 83091181
    0x209010e01091d071206061d0f0702161e12050615040c0509011805030a2108010e010b030405030f0a110106060f0203070246050103060b030c130806 65
    0x84040c09128000c0054601404040700c46242800600c0c0260400010002075040c003c0c3d0010b468142d9500f1109140e031407400040c005c6078050352140074090300504440c146010210192404002010340045400c40000c1030720fa201140004420343d06203440040c0505c03100361114001260a4028040103e0482c40702c4040050020f000ba1046034180071601c81c4a060b48107000c243c4842d01d59000210f881840603075007551144526a901d0100142e8001c00303240d4a101023400c1c940850300075200460a500c1528000c040c0040c2462810124036154406600d000c4880d8074215043c05004030012001010030300380202001aa03104403d0803042644d139410a00c0050400c0901c44040c00481d4240040090014000d150b02c014100e0b107074010f5031034425160700304094240b03945110301d00f03041380325160028002c01c2c044000040481850560107500c3c0b140740d9174004111540810304160600d602402404002e5058980081000031915160f80c008840c40b00c2d41d2030582c0142c001485070b40100203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 83093526 1106 83092420 83092439
    0x150c0306010306030c0609050f0d0506041712070306080f07060519050f0a170c09031e031624060b0405060a1e030603060c02011404020906010c020901 66
    0x50a95140d54604145d200d80380c00110018054500503c4641000481c0f40240070080310030080c560314541c0c41564a4000038801003505030428002c1c14074651500651381350803d101400700c99880c00e0003008005000724032840d41e003442040c01c209640800401c0d0708090720030994915103010400b102c505c580245000780c907800c0050030802d03c8002c1d030141d005810700400302e94171303c2d810038030320030008444900140045d582e000c0d00300040d0716281d070b00140450114102c0313801181e88401018610b0f00718010100c0c2c000c12080d9040c0c050040082041c0207810214400707108500541d00605071004640081c0a003c5046c04200310502c110b01e4014054044125180b0f000401005090900d241c503d903503c1c01c1c0e802180d1030300c00500c00c01c2071900a8144001191000b000030000c0c8018107500c039500900040d0040c0038540101c0c0c1c0da64030031a10512080d070040d03e1010503595507601e40c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 82913670 83093526 := by
  have h0 := BRFrame.cov_init 82913670
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82913670 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 82913670 ≤ n) (h2 : n < 83093526) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
