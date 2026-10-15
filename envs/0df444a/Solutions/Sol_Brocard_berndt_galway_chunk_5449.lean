-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5449
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:54:25.328646+00:00
-- url     : https://prove2.me/submissions/69d60877-7743-454c-9012-d7026ec2edc9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 979856115 ≤ n < 980035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 979857365 1250 979856115 979856177
    0x6090309061d10050c0a06050108191a0a140702070e0604060b07023a06051605030103030f0c1205120105060910120b03030a2106050607031112040f0305011b 69
    0x1040480c5c0040d40f5240c07034007035071040320410746410060110a00030410b046040c1c201600d103102c1ca0010b0380f914640300c9a280c0709031600b0352071800002c4844c2c2c45504074680020200139215204d00e494000291204201d0182e6460414120701003185403409005120a54520300001480c0443d10350030055000c80500c0340071183c045003010028081d2040c0242d0068812000c607982d100311030761800b1401c482c00202030500901c8141d4461400a41c81420b481c10340f64181030000b0641d800039070648a1200b031420007000110805009440194000040c0c030200340c400c80e01c140c05980740e8003002810f00a810001c1c1d04411041252001207214010100a071610384800003a900c507a60080b90943d4403403524a00406c032a222070600e14115480c09469000c1d00300c2c020440d6a00f0031000800500c03940e140a010003030f0420890880010901044946130b03404404107903a65901c0c61140070700c0c956880195015480c200b4002d2a1040004a0340003200c00c6541c8d01c80c110a103500c8410551805010582c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 979858615 1250 979857365 979857367
    0x8070c0506090a03020f03040806042a090b130902010e060904090c03050c0901120b0a020d0b1201060503120418090812070315060c02090411030a080706090309061d1005 74
    0x120100d6424404103014603101c0025101d0340c0d50904000c0d02d80040b070040164075500800c41040a0070002c130b0203d170400e41c041c41010310040c2a41080072080c0d81a41d0704441c501c00084006803051080d803102c009a90141c1d0040b020300700016045e001c460700100c0182c080b0b8000140c440f40f41c0f900174000c20b01c010000303100003120482603d410380c03007181036002220300e81d200c441d03101d1051820a10083c0100795040c0a000840c4190f55000c1c0941c0010703000d4204e0750f8010407c076104503030343c1d0089049444043c1000701450740e0100001d01074421031207040c1c024040c1c03c1048507000400d03422207041d10204ca90b07a0001815a80d4014010070541e581035031000c01c01d200e490b0ba95400d4400580c09588190b5001c00e425a6032541c40703041c941654800003c3c05840d113030000060700d0f19142c0035030098001802404440c180d5012a00b003a40440c0c006004003000200b41c010400d01d548111182400f950b100c018460f20f481c800d40d83c84200d42c0c180c10b120341e4800d000c00b030f0f03510b0024200034000c9840d103411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 979859865 1250 979858615 979858637
    0x60301060b0705031e03070c0b0c2503090b0f040315020405030a200406050102150604060f09090c060e0d11180103050d141329070308010918030f0807 66
    0x490000c0c0c0184004490320f400015810482d0405281005a481350051700c031031035418807542c040c00008940c00c00600317201d00704001038081c0005c41d09441c141644a86021003001c0300010103c1c0c281d524140c22408551042d4000c1056146102500c80c400c0c10305281c03514141c21912000c0c40d004c03401028000c4d8640811020917aa202440158070380f902c14100c06040102509102c80c1e100d11000006000c0d0303250003020401aa8002034501c460f04007180014800e03211003000c9400f40c11284c0204a0a40c489100056110800d0340f102201c80c1c02003c172141c0443e00e6960868260000c1c00d0749039801303d100794802c404503c3c0100180200d03000201088180b040002405a070010264010389483e040003c542c41c803260030200021401040c01c02961414580035041845040e1900034020805000c00c083c1082100c0c11206440020300c5580c3c0340d07100e090524005001003424002d400c05c2508010100e030807495040b0a941c3c5060b0705449600c0480d6000c0f00c00c54803ca03004005008201a03a540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 979861115 1250 979859865 979859879
    0x51915060528020d113f0a0203090a090606392f130f0908191404030c0b0a020c040c030203100608040b060f031f060611160501030506030106 62
    0x2c001e0071001c0e006442041030b045030103040ca000400004500f0b40110704142110445003007a065a03420450300c2e40c002a40300503041c0031032017241c004e4141d6443c1c00034211401640000103414410821a0190a62601c1e80140001d841c1140300b200040380b00204a800e00342c44480d032050b01c01c01101c4545d154010145081d10800d20710001c1075074174080364800c1e08007400304046610b034110406080f104401c481c200200702c0064010404861160380c0c0c1800102c0c10b81d4540118060ce070300305600540b20304a400c5440006890f81d01808040707086031102d038285075109000d441c1100e4002c1a0b80c00c2c40b03464008410340d15400032101c801140100350228a03160350f03d100d03c0d43d0040c3d0641d001620303441c201c440c0c1c03000d00c01603402107403e00080e00c08000002c0c0c10031040660003101a01d8a018650704074000c00c2c03605100c0b00000304a203000d044131400700c095079844001100c2041d40d400001003501341d646030701d5200c2000c28000303203144040305101a5000e5041250010005400054800e603140c41c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 979862365 1250 979861115 979861177
    0x90103091b0f050a0b2d0408100b041b0503040605040f0803070f080603031c0e210705060f04030c0314090d03023412080f040305010519150605 63
    0x41241c0c0711150742014410307414085100303400ba041c242c2c8494901125080b40300c0d2441000e82c1501c078410b003800046c00750b00441c403080e54001e001e02000c07902c05208001050000c0c2101f201814092844c02c040341c80810030551403600d460116490b8145162103c1e05d510001e004010004d0368054480000c0c1000140350030000d40c45010aa41c1d0070b50710405244004152040180803144070b68003e1292050303c000f1000b5503200d10010b00000108001003440346801c00c900040d01c0b1003104c0903048a401301e091840002d2007918800d6040d030b0242d035100850702200940a45c3c028002806055010780003d010782130058548a540022a0400c049140010034541c0d0b0a4002c400603082194005100c0d4030440d014081c84459808102034001c00c0086105000c0c41c5202d54202c060942c4e02e418144000001100d000350014401c540d500e41c3c0f28140903010340001d0f100e8440c0400c00300c03081d0142120380d200342d0101c0d000c3e80b141ca0000ca0301d096021542900701c00100401465207403203d0300c1500381c00f8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 979863615 1250 979862365 979862369
    0x6010504030b131a0901060e010b090402030a1104031a01050108011d1308130302040b03030304020d03050307050405041803021009050c0d080906040303020610080d02060601030504060209030a081b070b090103091b 93
    0x9030713401c220340c03415000f01400c0d41d24035808039903d06400b2005018a405403000ea8521050655005841350385120b90800035141c0b5002c9250ba500c0300003404414001580100c50a040c40d0041050340c69984400440c1d12a1091242210380c111204005a03007800780d407080303a00030f40d003401e4100c0c2c001c045444040e1690310169601034500e5a40e5400c10841c203041c002c2041140088000e181036140540219461451441c0b00400308200040081c500f0343c09401601c015140280080120484013540d40703042e003181040c20341c0580308058034440234910345d01401586035030010151549284042c240423120b0007003041103030420414070607a030032911100041c200960290340204154207049001c0120901641c00c203a2031900010310344403005400082c290b8006d5001e19000405036118248030b80203004440c0460341c10302038005142c0502000002400b103a000f2001044000d50b00c6500003687e03201a44154840c0d81e1040c091418290300070303480800701600400480c2080b80c04c2c1c800c4040c2d0040c480d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 979864865 1250 979863615 979863653
    0x9110a0612060b16020d05160909061109030a020405070c020d0f03171515070b04031e021b040b060c0304080645010f1e0b01030506010504030b13 64
    0x84201d0503a1210034003402e001030210a030450302d03040b03124080d0031a072a41c0040c0613001ea10f00780c0c880b00400000300105034482140c2c00710701c04240e8544941d40302622040205132001ca0400c407600c078800301e40a085903600240140102020780c256801d00001e00002026402403119400c0008007603140c44207800078a600c1102040e040310041e203000b810030325109450b401c001c8080d40030004103580c000041c08603d10103c9805d40326400c4018080f40ca4801c502d401801025450305000415030005d803100c45503007414002e4103040c030b0740d000e081740d441c0460380f01c1d801c02c80c0c100a402071145c1030a6000094405025000c9842c10b244041c40c949981d01591020403179500003010404550164018403180c1804c1206040404002240002d072171041ca001107d4402400700042c008030009601a81c44001480e07410b0001d0250400c0a020318420380c00c0340c80516041440405c6158442d10690780714802c16150340707052a00319100e080d9200e00003480c001040483c4a006c501181000c1c07a03c42c015889 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 979866115 1250 979864865 979864877
    0x2d0703030e1e061c020d020a03053103030b0604381c0e100c02070302010809010624030e030f04181a040f060f080312101809110a06 58
    0x14000500c18080361800380010744142c20010015a5920710013262541d499004e2600f141d90381580b10440280b0900f90520405440001c40c004596003641282c1d105042507998109041404d00e00310403800c100c40814600a2211402c85000034080d61083c084480c01034011410251101241d50710401c11361140141e07520074500080403421114004281c091058030304509011011603e80d01c80301c030020034081c1080c1c8407100810320b84801c1001e108202042602030002c00c281001c003a45504050006a00003240f14000070f608a905005d44403c035032000c001001d1800301050300f002001100d4404a080546448400c0940e1500b00003400f8030000740380000341e94529001c5002030b6540c0b8034060701702103400e050000d01e000e0600d6070400d544078410b55011401c000f40d0b414185c0149043d1b00945568658108003150901001020f00800381d01c0070040c0c035258846c00301d200304910b140c1c85219441200c03160014000c5009400c01010711307204995039031050b18110f000542082c3c540c1c00c07000c00035403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 979867365 1250 979866115 979866137
    0xa03020c0708070609060e2202030108010e0303090303130507090c0914040c0801261c021212040f14030313061802060d0209030309120a020109172d070303 68
    0x40c0c240522401030501400070400e0510784040034001c080c20344522001d000d036240c00c184850b02c0300141c10184140313411031803100003e0901c9420080d04203004041c00c83d8a0840b000000c1c481c0002201c0c0200804002142980d442c04022003407803007404400c603802d000d07985002580840d070340a2400e224a1a0f2100099a0f0820740710740892803401e81240c0c415410907420b000d10301e8205403024150345400141c0c03903c05446415010100700d0554000c02c1c1d031704c225a885c440502d146146804103049036403d5500182841c00e25041074000d44001050148450000c200051001050995030522840056000ea101c0c10801415500115808000c2c506414410020040c40d8840c03a400c0310400b000078030311038469170042552401501440d02415500003020742c026a01041594400031000784600c0f002214101800c0d200c014850301280424070104021510300451b02c14110071010300c070010400c15082405401d0341d1003c18502d5030400034980c5103007140301c2042c88040d0165010b40c9a9545502c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 979868615 1250 979867365 979867387
    0x170402090a060e1503160312030b010203090d0b0603100b0307180f140f060105030c160c0801050106020d1706060d0c110f07081005090c060703090f0e15010311030604020c010e030a0302 81
    0x7001b410008260308428003800014480301c44a01c004010f85400106044400f0040c1c0c0386201d6035065a500443c0b00b060501040b038143c3c0640d1180c41e00707800f80d43d00b03020340494403815114030340801c2340d045c0c001150a020740304031a07644080ca100c0125012a141d014850420100d40d00400642e11501c2c509040142d55506100e405411010a20b4514130f0b61503c2e042c00150307406002c12110700c2141c0c541c071910a02c40034000441c084d2a01e9002003190356903868000e907a80094402c1140441c003021500c078100c1d0311054410b4403800c40644500d24102c03150010704001e0580c41c49203401c1c03001c0d0101003028020104142c8084200c2007005084850628480314a031248003242240c00c98140010000c070300d40003003034904d4040004d681040e180d100503e02545c581240381c02010722039580c0040015100190306141d0302900c0f0482d0a40503901c5405c00441c240ca81e200030b00c080908082012543ca030400e40d00500440c040c4a000080060354811643d055510140c1c0c0d0350006034000c60000000b03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 979869865 1250 979868615 979868623
    0x3010b18090102090a2310021e0327030709090c031e050d02060712020c0c09280507120e0607050c211306170619211101170402090a060e1503 62
    0x1108111000b40903051f9a2100030340c0c96030458202040f0004102401140c044200306451184c54003641000041e030703081d81c90090504c08000a18480d100c1c0c0040007500c1915441070b54112604100d940b000242140c40d12014041e02016000e044441c0c50303518004200c042c020309070030940c01d9010b8102c504010fa4003c00004070506010040f40c810050001002c1000480805801741601c9a103010340d903104c0800d00108185e0211018550020b0b5610380e01c0354a40e114038400d4003d5140d18810380707070f9039040d6000c590010396021544d074080c4001c9100c56004e040a81940b00114085445402190556003039000703201080080c41c900c0803981e0b900140c9d494044401810301407078110143e01d50048104039040e40a001c950160310000403010034510030090400184c034032849000c1c481f132a0890341074042185d01209403007596056400c07082540c41000c1540c000c1b00c91200348142903c03150204100f4903000b800e1803d103950344410006412000080c480e02c1840807880e5942140142c40c241414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 979871115 1250 979869865 979869929
    0x30308070509030a060e03070b010e010f0909080d0b03030c0d0504050406090504020a12030e0409030f0f020f030a030e0109051501080f0c100e0409170c0c03010b18090102090a 77
    0x1444002d1080040c01e440c00a9500700e0a41c0261012a445244090141c20741c410580c015045440e40c030008588440c1c1040014100c484100721400700300d903a0030b904811152000d0380240010410807903510307068125000317080d02500003003e5030329001a02c00c006207040094000032000ca100410f0800652510f40308813002030130404010710040c507142d0300041e1440c03460b0007000346201c08118600e0515102c1d6654100400c0c01600810000c100c03402d01031301c00d68a9840642c0010280214000741500c040751410440e00720304010360800140c1c05058014184854440025641c1d40d075129003c0b900800503c048840c0c0b11284805650614424505088005554070b040c7d51000422007003540380c4100380006003030359140225660f10000009000741c140b03c5006080b500740240842c0421001c40c00501c204410f940490740c001c0359050901d400c0c0c0e43c2206040390b000310119101914692084241913101c00c48000052811103410f0005400701c00307a41104203041041800c000d8010805144400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 979872365 1250 979871115 979871117
    0x40f0509060a1d15060708181f0c03030207062a030c0801050603090a201c020a0b070311030316110a02090612010f090b1005010906020a230a060603030807 68
    0x40c2c00e042030700c403c544071402e1074004005403081000a03080c1101a050a01e22500103088a50703d2645d4200030101b90008121701401c000c2d0613202005618000c40500100302c4a011580d403a01384603801901d00644d04002942416000c00801002821074890300c840c403194181d80751041075854500c4074a4200e581c49020505281c070074561201034002010904642c07084032042d54981d102441c035401c251005c03200900f82c411420310609841d00c05a4490020b00e800c0d100d04043c1351060040d0841c03540718140213034109002031424803a41c00c6032001402500e02030f0401c000582c44002401e0715651086881c1840074415801014026030f00c4003900506048480041c2840364407a000035500040207403450b4803500135581c11000c07000c000e400800c1c01c2808100200841125420702d0707180c201003202c3c02d80c0d400002c09808501580101e05c205c083e00d400e54004c080c19685980c03180301c0b00c880302d00710281c135001d10b600444c12031008104580516200d2000840c0003482d602d0040c0009038050040d030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 979873615 1250 979872365 979872379
    0xe0403020318040209060c0114060d11040e19050d0206150603070e0310141005011e660308040204020403020a0e040c140604050f0312040f050906 64
    0x440426800000d9828140c5941480c020942c9042c0c00640288514000141c000b403000c6100d040301041903101d1400f01c1004440186c07207a4a401c1000b10209600d80c0003086404c1c00c0f03100201c0350605602c408907004c035900c102c40140040291050b00303000c1081c4111621361280002e0084c0030f605100030b94000da29898081400c0544c280064000d020040402042221500da032120130f5070100031240740c0e110b50031005c21400000c0921031120840441e0042001001c4000000307142d4401c540b111207041d0010b25543d00214095404c43c4e124404403185800780c0e06075101c02007409090803903d91380ca408825000c02000320708110002003501001d0105161085051290740651009940003103190300d071400401c00c0d40e50b440058001d0055800107904013101101c00700d540008410190b00031405260a103085c50303568482002941e07074954130160400d2080c0700410107410450f14039101450005c00b5592241d9283c10b0341c1d11650440c1d840003490055016040050307040c000002504442c05541c08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 979874865 1250 979873615 979873621
    0x90303330902071509140c2e090e1f0519260105010b030a0e0703021c0c0902030a09020928020f0903010f020a030b0109051516051605131a01080a0908040f0f0e 70
    0xc540300c0d503040800c0c1ca1a981c08d80c100d41a1030b11417614003001d004040c0c200d1030030341004040000307509140c41c1c214a9041c00e1a001060b185094000b001c0c0b01440c050070305901e24100540310f104507044802c004890314202c1011a4180001c0c000c250103400310110a079124506161068255000119808025000540184090f80314134440c9803415030021030071551170000d4648078143d03405560103049200c1c400300c1489200c0e065a0886041e5500813100c00d0015101d202150701d910700414465491500013005003100040b542c0c015007040c1c0304c542d1004e403c1c294180046802d660ba10000e0000942c2c0c000b030720550b43c0e038240c0f281e200107880a1070284a481d00342804504c103810350b08440c000b014004201c200f400d4050340c000445859001055030305001c0d280203204442041c5004252064409071b21a071307009042442030f02d85000504400e140e03074181150040d03a41c8413016183e10200e07130300da1007180b0106402d04000e00061000c4994400085d207889044114442c558101c00160101c050038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 979876115 1250 979874865 979874899
    0x1020a09050d0b04140f060103050f24060f180a0f0f02090105090d0f120f0f050702061c0b04060e090f03031306110706090303330902071509140c 64
    0x1001d81c015400b45100300d0180b582d291729880c01c00302d4182d0322247d2154900101c05c04c080442c0c444008208042229501200000c81030101d1407c10707103103031044810710005440f6160034a1390070f010002c0600f0140e9801e0003020654040601143d00c150340e5901c03a039540c0d95080c11031041c8074444414010031402c00381180002080382c42040c209030300c6140184221024400c0002e408201c40f41e004d40090070f030701c00c00d103c050304244107110b0400218911082d0f1580050040048404860f03004041a241038803c3c03014030608003401c2c03000c0c00c441e6550303803004c0c1d8291180e01c9400050151501c0d02500c518012216a20b410400002061180c0040c0144000da90340d250358880001c2e4000c20100380f01d00d0740c4000703203401e006004010b84100d06102c0c0c99020305402da4410740140348800902002c0c0746040fa80d540010f607108200c1558640f0640040000002c00d602504103503114074a1080342d000c6260038002940c3d81c800d01602e440c0c181c61901100c41108001302d10401c14103030b9204882c2e0709035001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 979877365 1250 979876115 979876133
    0xc06030e0c1905060301060c110a0f050111010b03060106030e01230f1b0a030207061407080c0904020f1b10090c05010f0203090405090c01022a0d0c031401020a09050d 73
    0x30360700540103501c0214102085200b0880a0310001d08525165a07503040c000301002c100040079201c0f0328411404600030300f01154560140c4110820802003549001e0044441c054540e00101d8a0755076001080800e82d82031100e107000f0a1651f801003003191040c44242d08403140300300b448121400031103c07040070705280010154012001c40c0683d00c16134844a41c80d8400030003800e80c05080400040c0303030416a4040e40503183d1103009a80811031215030b40ca0791005881709030b82040100700c4030000214205500001441c04c888050005804c2081c1d05841d0b00060304144505109611b1014000d09040400c014860f800008030b1024001c12036a40c9a500e98401103000d414100513a00c105030340807d00030002c60b88040c10150007004549090540035480780a042591401401001d6080c88420030f0101a01040c2c1c9040480700f50b60204a4100400d4058055045a50040c403a00020200b804c42181241c0000c2850015a440310781410041080303006400140c892000c01c818540403981887c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 979878615 1250 979877365 979877383
    0x918010609170f0d1808060705120112020f0603090a0803310816020d0209090604110f010905091302060d0605030d0525060f02070c0801110301051f0c080a0201090c06030e 75
    0x208248880c17558502d441e8504682a070000000c0d4807403c4103005605511034000c0c03000104114810b102030742c0350a0030b03803840441408069030094010221003510f2809400843e00090f100f8100c03182015170307070741e031401d04e41080310040102120010b200d0032507464118008038031441013051038802030701aa115480c0b07000e10200039200c240d02c02001021911800703d4070410315001482a4000d05d062046295602001c5404560180104240c0f50715424200c600389104032051315804201e034123103800d101026000420890320b0500c1840082c0140e00e80d21700921070400410004288141400c0a05251951502c0ba09040110803c64081c0b0400c0f502004100c4401444206500003414100f00d0007800310398004160041c400a4810b04211240148034104c440c804000d020000ba1410046614003092040c0c3d0340007800ca20001440d014001c014080d000c800e4104041540c0c59501c41c002c0c00d0b0800e651382030141c3e5582c03224105000d80050528000c02a0345007c3c0039003025110050b84402ca84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 979879865 1250 979878615 979878617
    0x50c100903060f141306110405010c14030d0207230607080a050601031d0708071d0403051620090a061a090a0e07020d091403060c0918010609170f0d 65
    0x94041200d030f6840b103802442c10400c80c2010303100a8204800e40041c0350102050488483c0d01d4001209500d1541c18203031070031900140c403044c1c0b444e512616076242e450a03d82d1003111600041105d445014000d101500005025040400f1090000c40d105480a4000074046003558840d20400501035803040e03410340c0c484d0491102041c41c0e1100720059000e004400c0b81c1c0505000039010780c080890001039803034204c0b00c12508840c02590743d048c0d0907202240c200b0303904040c505404000340100780500b000f4601c00c0350500b00c01c0c00704021034581120f0011400c03c10180f000d107246000700c1c54a0b2090140740c014141a004020319813078105010b48440618000000111000c80c58010303943d12110000300034441340c0c442040c907251441c030094550901808000202c0c00e54000032940e810084440784440401078000c108948a1600000ca940c0140d250030f6030044c000f007400c3d8060200450308600a0900d034413040c540904100941003515146c0b100705410740d101000061400b0301c0018440108040707 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 979881115 1250 979879865 979879871
    0x3060106021f0c0e09010945081c0516021903081b070b01050406060c1511070f14010b04020a1b03020102040f121e0f1b050a03030507050c10090306 65
    0xc010425544c410824800541c40030b8020300020b00c20703900741c0103c90103070100b100380d940d00711041510f400c0314210151243c4c07415409400f680052440d2910984c403903802000070387c0c10545a41041410005240d409800e81c070703201d1007070088002807468884c0e055a100e00141c6840140c2a40c00e01500c0007085018040208140104841441c1040304803088040410461b1341e681e502d082030a4111002e02c80e51303000d40d203400400540903210b1511450826448410082ca1000d0311400342c0207000203008040591004104e6000000e0484801903201489001144101602d5015850840d1034901c03002d40075074010081c40c4442540480706031011041d070509030070b84c0c5845050480c0240210780152003a9903c10070003081c04050b41103600c00d038134030a522400c4c1000203800b00c068210b1003031a0082c18040f6000c034402c0014104c44104400360303a54200048180e03514000603944036896403040c1c0c040349000076101d0034491709100d00305040105a660854885048a00900b610300c2807002504541e9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 979882365 1250 979881115 979881131
    0xa050702090606040902180f0a06080a0203091c02060a0501050f100c0f05010228020d0504210c09090b010b0301060801210b070e18010f06030e0102040b1803060106021f 74
    0x18510013601c0151400201c11910740c0c0b609002e001d5010f81d004c6d00356101c0d58400c004040d5510380444010b0a4558541d16203409441c1c00c4002e20103500050001400760240c00d1401c2c14117038029080041044080e40103240b80c0c00d004161200300c58043c0c0000e805880d5000311180c41c1d440d20348080f00a03512030301e48044803900342d003480044040c0307000004005500000c0d26412408619400914440908104080c0c0511003503041ea500c030b180b14801800b25030280f00800c02c031410594000300c0c080d00040302c05142d5203141c2e01d5000617100c0350840c46d080390390380d002c0340180000c031403001b4050064580002e25650600801800e071001c14820a440c00d4403010451561010b1900d4440d001a0300001015a6050114010b8415282c2030f084d5406466a60022135546401c5e00800c0d0423590740c50680301030103040400032006440d100c8070032440c80d9001c0000003044600d1303000800540c00f610302c4540380a4112010107080080682c003070001c5501c80540c0050350300c281d2081d101120000840000c0d488 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 979883615 1250 979882365 979882369
    0x706092f0d032606100806030c090910110a020f07080616050409060b040e07020604230f0f0a020406050603041e11060d0e011b02070e15130e120a0507020906 69
    0x1200065890038a0f020503a0042c203181541074600e0103500c0407030f611040c94040d010100c800711011120360743d060380208400300903400c00c00800c07a003004030241610041d180c80340b250b2059030451401c04544e4480040c1b50300c4155814000940c81c01c8400c030152041c03d18100c60a81d4030039010388042101c08500001b50050f60080341110000c120340c0d0001c0c414190f4540080080b5045072107400d201d040c000c0d0025407194400306905100745d500c40c071116110b074120180110050584a800c00c03240c40f03503008452406130b0030006295110b00080081c586903a00b07105000c244c0d0620362000740204020300900c03000580610041011480c5101d0105481340703d8103010110241003100d0a4000c82c00007074580c50490329812018820b04408004d0040d00c803103600f558010061030111000680003540c048c0b226076069a4170540040d59101034070054180c80380000d40c040c40760309004030400e5075842c2140410385c00340408074109080400c100c0c200001808041c00b02e10400d0402807140d00080002070081e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 979884865 1250 979883615 979883627
    0x5070504030c031b0b030f1501030b1206061c081209121908091920042a09050d020402221202040608190f05070b0706092f0d03 56
    0x110341250040b84026602d042c034403200342c1c003d40201c1c821200c0c444003040c0c004445007200d00030803c42c80c08030341c44d036a0110042c540d003c0035003c4074101034441150070311540e00c01d01c0503043c1c01c003100e0103001070703051102c204200660640d000b0300e46d0001c54942d00300403c0119060724905000c404072208141e959103d20350030006540c148800d100700110303602d40303425980300d02070000b50400d4441d0701c02d0303890380c2512907913408803d0311015020010303801010000d4130100c01e0306803485481c60038121080809001606694180520300c198500200010a26240c0e1154007a00d8550504011001d43d04000c04150260348440d800380c01150001260703202c0c14207406c4890b03104071a40c076151940303070341782c6022a1800c1110341041e031085042c00b03004180079102123081e20b032080982c5502c20300326186960b50149000c07440c2064880f4025010000382450401e030040c02101d100784400208040546485180314100014030300482840303072000070308000161350320004c06c4400c450105020b5040d240c112a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 979886115 1250 979884865 979884869
    0x31501030e0109080a3c030509070506040b0d06080607050a12090c0e0903070b1006090902040803090d080c0604060203060913020f120309120d0e030a1e020a050918010c090b0d05070504 81
    0xb40344403d8011000d403076966070406d035000010b69060000b07032a60300311305650b6030b001d000d110b5000302c0422003003001d003909200600a400360040c011030032640c2c4410382418503508807038080104d403001446200c080e9001d03810b0312001324080d201300060b80060b00d402030701841d80d004d4184c0d0b90039000046000d104013041600c04055100c084d8070b102d071529000c8603072041000d01c19840842c07404200401c05c540c40d40262005d0310a61401182411101010000c0301010b42d2004d880c0d03c802001400c103415001d001c6184603030b0140c0310243c1d8906100c002d010b0200d400030709141415030121144c100607070700c1c6c508515146400701c0c0d503844d10081d04410581107100b4070344540c0c0d00903400c2d030645c006c0890104208107030405503168200003c1d008014145c403202c0741c02001700101689503c5840300d8040c116600d040ca130000d00341130581601ca501050140e041651001d0740034015000c03540c0128001d0040c5034404402d03207803445a040c6403040c40300860280030540c114150311000003400442c4244240c0e80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 979887365 1250 979886115 979886177
    0xb070825081b06090d120c05070b04032c03031b1603050601051f080703110d0c030504050c03190209130f080309070603020a1b050a08031501030e0109080a 68
    0x39595000d6800341e0003140310070031a00e00030b0081c00b0004098660101d0900789070717440c0d906c2d51030f4203500714881e010041190b02501000d00c00309000100c003081201095511903440f90721a42c00002c200060082941110701e41c000b454600007440107151b803800302c241d070640c04500c0a01110146840031b880c0c01c1010300f03040490759002c0d28400100344040010b1180c12141d064800e603948005071a82c0c03800034424500881c0200d500f8001181c04148258000007004c810061060704201c2e41481000a4a200884a0000070b4442c4284400d204c801d0103030001c0f0000c1103008040d6401036010f51111413002240c081d04c201c0e61440010410780c9800c060784206503001c1c0030910094150729040502d90415165540144500343c0d010807104e0081c4221250203080b91036407403401341054151007a419501e4011102c90213262028800140a100a94029890040d81c41c4003108280d000400721038503003100d070313500ba8104608075000c0340c030450844070b0083c01d51402024143c140408501c40302e0401101170 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 979888615 1250 979887365 979887367
    0x2517030a051801031b0203041806030f15020d05100504140108060c0c01020412060c0206071407060507120c0302180603010b0906031806090606010305060d021509012a06060b07082508 80
    0x2074500c0786c1c040010002c0d201c43e484c0e815107000c0c500004504803991404020140b0740915030040100b1700383c5d41c0344444140d030040c02501e40100751030003d06032581694440310404c0c0300c0c082444549000d005804040c810188404a030351f00d80081103075143c0e40542000030116001801895a90003034048901a0220b1100b440a412a5103010402081218002c50040c01030b200421209403140348171400c035500e0800d14070301b46031040d101c1d6001024041c04010600450b0400140060700d1809040c45050300760302d005880b841070003d002c410224030a10036201d40010401070100494410075903444000907280241c40c0c0e501c0a040c103c0000340001005d1840c42008100440f60800003849032050200780d80902c0307103490721001e00480f102c5099000b5404940340d0102d102031100500076004c842814901a41c6040c0359840d400342403240c03e9000503031455105000c00c180502401038000811040014924206403601c54010320300502c080700803034100c03c500401c3c0320f8145242030707620260801c80305 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 979889865 1250 979888615 979888661
    0x9090c11070f052407080d0e0a150f02040f181503111c0201020c04090c050a0303020303152403070201021b0607030b150703112517030a05180103 64
    0x2020310b280341c901c215446110600701442070f421195a01d01c182500c40006117050101c07a030354510240e009001d042c80c1403646c0320407104080f54100403c909660050840320082d840c2c0402e40c500f510b8404100b440194010170007040309040c20319880c01215820804582d01510710313030759500540802c0d440d04207240c1e1402004024801d600d65000300e01f100450b03943c0040103e41c110111000710420019016800140c41105281001d401580c0c2c568420034586c0042500e601c00100e000e40c0d10340080e40168000f0040240801c4080c6c1c25842200048440c0b01c4900c045e01e0902c04000010040c51040c03100110100301218001d405840c0342c1086c44214541c0c1d10242405240e55203c2100d01c0d000081c20807600a0087c201070402d002d00e006200519031a24806803010744446201075442030161260030b80c0c0901c107032030581c1d034100210840d039001c000243c585040358403505004c07000000150400c000c81c4620300d41000c202e038601d402a11a003074281c000c01005a00810803103024441d005250041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 979891115 1250 979889865 979889879
    0x130308190516090905010b0d1a04020a030c0314162a200906011202090a09090b0103140c0a0e0c160c2c01091e0e01150e0709090c1107 59
    0x2070540038803001c1c0da03440d40c560303504c410402c140d50003032180120456040021401d00641a0072452070907240101c1200203000e12000714040364480000b1340000b0741e03100a00700110f54107000e0403144840c2000e44202c1401c0c40a043c07145c3c038008001000030300550001d418840c10802079800c02500400307801d08110f54041c1056403080e11450003e01030990001c84e503858500d407540355140501010b9403007407400c410700e9051070001d40c0040c9602d42d1040c551140041c403a0054007491260314071030405007100d0351452408007c12041c40220f11000c2e044082d20440c1c64035404120411036000341a40104c940300c140c0c0b13103d410320a031060031001a412072299030034440d0340301c184011551000340e0b841003140100c0d072080d607040040058240c6030745820010042015550080388801101c142c2424140d06040320841c115103e0b804901c585075103400c00a20000c1090000c8801445254581074a91811003002807800195000d0790200e2a607420b03a04003a68499041280034140300c10848411544940c0c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 979892365 1250 979891115 979891141
    0x9010908060106021507053f0a090c0f0803091009050d030c030e040b01020712020315090a05060f0f0f19060b03240310091e11030c091303081905 64
    0x244034401d4091250101e51814420800c554081c1500e540150034241110801070151104440e01d134200080c44a810234446003040201e40a03c18000b00028050180d10f89040300c0700301544004c90f010300a600800c5611400300032600b4001d812074880004d801195000d9541c2c3e80b49812068200c50400344040c1016000303000c58400d94000d03226518140802010002a24414001c0d540182c0011108207c94a9550f2032425034500c02002c1e1000f4983e00c40501400c41007c481c2c500e00c0d41d100007801001d1000030300c45540c111400c840607800c00c0c5404001c0200c4020007500c185400200200010090f0400150701e00100f00041c60510429648090901c4260401c1c4c80c1010602e40d0803c00c0800141d00350b0315280b140c10042d020307014110100d035880b001000401c10940c0d031014207080ca00e10382022808243d044511504001c4024507020051501e0000c1800e8418096023140c0c003407019000324100d148011a9052608034501d641d03988450506000380d103541c20085080c002400800e205c446 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 979893615 1250 979892365 979892383
    0x80a0204030c090f47030102031009110a05040e07111b0102190b0f100b0a0801080d11190f06090309081c1d01020a05061906091a060901090806010602 66
    0x200c01070000c1c400114150b41742504c2042228099491781c4204402a212a41e00d000304403c80801006107602d404086400d90348111341c0040f1141e0740c100c00b48240e02e42841010b0b40c00d901b10304010f0925a1405014015100310b00602e03040b00342c8000000c0300c103842016000c1e0050504000d94a1002c01416903810403180c03514400d01500500d0070542500c2082d12148030790700c0d001f80004216849208100d000298041c0c6640010340086c10040740c4910418014034080c001541d82213030070f6251040103410440101035010801c5400c50f002020340100042d4103a00031890710002c5144c5410713180900d07002400340801880c6a06200d222402c0c9500f141c0c01c8811110184151448045000b41d603840481400701d541c0e0100d00f01c0c0c0d980380d900d1800504a04454601801210650245500d0301071400000322a0030000104404042010000303502481e0002c142e822018171203501d8103c050100401c24000321801404003241e6408507a1007682840011311484040d40c0040d612000000e440741000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 979894865 1250 979893615 979893641
    0xb13060306020409060b2a1606120501140f0103021602040f090203150c1608071506061d010504120218040311011104140111030c0706020604050c09010f0303080a0204030c09 76
    0x100ca0001100344c0320b9000c6501c3c2440e48660b20190724203000c4591107d040c10007004100f4851005042c1105130780765004000f5003480c0d1104211000819411802d80301c058005075582c3d0181c65040b080c540b15030f8950701c1a24002d003030140e1a280342202c16082c036401c85901035800380c00e003501c98401107210351003507485038026816100544002c03404401d00d080700341e4484109003020048414400102e11580b110740d4840c520080c580310203030f01c0307a40768101c10080110f07440d566403004104954121501f555075080303071400c2c070b000002444000303860b5000c2c520a8002003400d04201034119a107061451224990524a0001500342403c00070500800e80070645070944ca0001c0c030f640303684180800e039070454100a07641c1c4a409810001118041c0e19010400010301c8144a6070701030203403e00103003000e491254010115071916090181c0341076948000140a8604100107000d00204190385d10280c81e090308001c1080d0301ea030f83c1058024441c0d9840900743d20b40c0c0c12004144191640c04c400c1941c01c503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 979896115 1250 979894865 979894871
    0x60a1e0903021f0615020c011e030204090f020c0705090106050409151703030a06050103021303080a03090503041508062704030c08070b0a05060315061c0203070b070b1503100b13060306020409 84
    0x300e900f0130787c0c0d82c1a0410040e03000c071f007038034a6030740142d803d2481003200f42c843d902d405400c056890030005c090703602c11002840c140e60003250300340c3c005400b080801d0040c02d0031070b28403216525100000c1c10b6032003a4010b00130115110204891101034600d0380e080144041d030946240a240c2010464603074000390703030018829003002000103a540c42402511060283c150303100320720700e14550f03c48056030300c110580c000f0b254580e40c4000120386c0c240082c0c40200482c1d5a50f140c5221000740052090000510030392048000b10701d00884548095165042d0020165045045403598102a00c900d0b841080052a0240000341d403010803520804140c00b803141d68a0900043e156102056141c3d080017441d0039140021500044103407810490b1003211031403070800005090b105d82c01081c2400f016410600c0403c40008440c420088241c562a0703000003000300301c1c0800e4006a00081c2c83e94070b41321030b9442681c6c036444030554541d00d0300e40d0b001800403111010001295645030100113500300d4030440381e1440c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 979897365 1250 979896115 979896149
    0xc0f121107180f1d03090406121a0603120d020a0f0e090606092425030c0803040c08010f0b031204050a05090a0b030706080603060a1e0903021f06 64
    0x14000900c00156200100006850b8489084000080c00458a501d0541c0c1d20b0710b940c40242ca0400301a111101302400141d9a41c120801c2072109540340c1da800452108045102c0d54081001d82c01c0059985075000d51038044e0f41c071920000703464031104841103100c0038000120100c001178154020700c4003a03846d48030a646180c1401050310a01c4400481c1034105505400141103490300ba0010314029500500c20311161040700c0010402002408984e0444040041d103c2401d110700001d00c9040c00c6503c2c2c0c0d58400310015500145841603019005008810100110301080500481d0002902040c00208400070780d1003002009461112041400303405100b441c0701400600703104842c00e0b42c00c094007001d001498501400721440c0020061016a643c036502e0402c1ca41c2c00303102c40c0c0c0061a25503200d1940f03007800d804143c14141c01514072852180f51440c1e01600e190306600c0c0443e04490904002030407803507400c1c10790804902d005048904c0c00140d0181c2005a0940c0c441c5043d240383c0c2c804000100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 979898615 1250 979897365 979897397
    0x406020607080c07171b030717071a060315130c08010c0e13091e0b0c040f0902160516031b0b031b04030b010b09040f090803070e010c0f12 61
    0x20606681d4151001410881030001c603094881180c03000b17a01c41c2400d071510500d01c240809580400e903500f10305400c001400340c00c0c04186006c002030000c070307200d40c145001e00c0c80e6515044480380d64881d8400030501e40c002441d95400f070000c0c07202282180d881601d035180801000c07441d9020000c089420011031a030200700044144248600c03075100361609180a4141420046618100e00d01c50025a844001c600d00054580c0e255800070713a07602040c2c04105126190024001717000614140445001f40700070841c007048041100201c0320000c00045e603890240300300003108610840041d00a1281140003103141000252842c11203010b07030007420303040c102070340d283c2e01780700481c41a10b10b4103070f040c0081080c020000180c6004440c07201607603841c20341d40344c0e50b0b8004043c09034440506980041240115401c0074010140d401e048400b007001400c0c050b40e582d2019010241035201041030781826003480e039000d2a4007060b1603030013400c4049000a1441c0034500c0f141200c0d17a0000080c60440d00c0002d01e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 979899865 1250 979898615 979898627
    0x302060313060c0e060a180513060e0114060d020706150f140a08060115090314010209120102120a1509020d020c0f0d3c03060608090d0e13110d020406020607 69
    0x41c40c4c0100510b20380100150211000007201003002c011449129001469079100c1a42040134200c140010a0072807509084440303507507050384000e00b0100e00b80050301503541e035881254042c0c100780340c0060300d54800d8201fa200030900c808030300c0341703640011001040c07100502d40d490b0f00310f07640810803d400c01110000e10400c070815105000c21a4000380050016400c1005541010320551503c5095a584e0f5101e4200042203920a8070780c0346d42c009013440c1d6a003001d00b0001c1010f04448025441d1802c11500d804a14100600603a541982d03070401c2b10680f080c2400c3c2600620410409540380c40c190b500040081d40416425402881806406520b002011840211416103512803211180344141c00d08080442c071a204204950308840c2240b1188010003200303103240c1240c2c1c001856504181c006072520401403c140c010380d01001007250038503440329958010400940c4c4080a016100000d00c019140c426042401c2090100d603210031180f250340600100c89840d800c0302c0309034607455026919 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 979901115 1250 979899865 979899887
    0xc01090807030809030f030d0c090906140d02060d060b0d270305090a0312120533030a08030708091005070e0d0212030d0c1d1008070203040302060313060c 68
    0x5a8200c50700810100d450100580307a241c8000d02642e0a5000307082c94142150b000c130201000ba103550300f03440d82c40341da070200c2c0c86009440c1201c404c00940b820314900d43d610250045525100f0000302200d90b00310745851081d01da000030406010b10549403204111042c0350031141c0250a414036200b0390b8001c0d0f10114129000403803201329201100c25603514120740303a50040b100036420840382000040020040054a8003292003581c410b4202c070780d43c6030350005480300034124040c109000811060650462003074074440c0a030012848100644140100b41410300b8400040d01c410004810069030342d8210140c144244100f10a58902800c0e940c1c01c074041341c1c0159a150005a60101c9000050810616841609000a0031028043e42d03003203540c0d196600481100010030380300c019081040e078120007014052507920b180080c03013040c85000b0a5003c020b0f80600740c20071142c0380c0420f201600a0044034055a0094440359603444c3c039041928204480b040704440c042d02d45070400c882944107d00c1000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 979902365 1250 979901115 979901129
    0xf070e0c0703171003020603100e070906020d05070c081209121f050c07060e010b0319080d2c030a0906020610050f0105121e060603010312031104170109050c0109 71
    0x20040f0301c0c01490a05805005110700c03484100d083d008070140c0e4500000c2c41c441c4500c1308030011580c0c204940400d8005001d802c000c2030241200003808107513004105011404154601326494002c0c900b02140d250016501a94003401140d40c00003409114000404482c041a101c0840020000134900d541e21600381c1c4034102c901c000d11903000240b400e50401c0b0f400c404041c20707003400c0c4a5180c441c0002c6a1104003003040c0380c0e40d590380000150406000c0640304200300c2d00340d501c0c44610340d00e44035a140f08046804036a955181400400c0c00700101c1c0c000d03145080803841307402000d065900c1c10fa030b950000c074001f004294503000009040e8400219540300d00d44802e101c100e1b5510b4841800382e262124041d141c10302034140040c062421280d90b0035031080034544074100c60821010025800c201c005030041d80a030701c040005001240d0510000b0b00040d26034034000039080c00001c6034100340d0140c0c1c0c00800600341004072522054005402c50444e0b180600169000c0043d0a8015100501a441008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 979903615 1250 979902365 979902377
    0x60e0c1005190306030506160801080c1c030513080606040f050601020a110402041805150102010207020108070807021207031112090d29090d0210020a09260f070e0c0703 74
    0x24841e50030103030072030b46620407414045000d45c1c40ba5a0720703061000444022071002c4180d070f40708100e55444101c041c01050a2005052504014004500382009a1569405071994143c030442018800da04842c0341a000e010400001601d40e81401d4480005032280f5100380c1c1070210102d0111440c1c81142e00414050700145003a0ba403d03501d40b003884040760b2540361b005901740700010b90f9452082c1064601c0f9907619000400703250043d05485a01a50610341d411684144000001070340c1260940d600070180703040111084d940c1d0328003249088884c2010081c80000494068100340e00044c1940c034030104881524013400e44010030449600400c0340e5103a01c00d4155001001044030700311280c2c0718240943c2c1d95100889000702610540d901640d41895a600403180204900c0e818007520740100d11442d0158640f04243c0c03c000c08444050003194039104407280c0003020285c0410400884071020342c01e4a40c105170300302c1420741b100c420748200c5505401440006607120070900448080580c141c03655 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 979904865 1250 979903615 979903627
    0x10c020d02040f0606030f0615091a0d180b130c0501050a090e01061e08070c0b0612060f010611070b071b0801020f0a0e0603190f0b0d060e0c1005 64
    0x100100a1030a410398029603a841942059026401401c026205907140424040c01c1600a00121203250b0300c4401402c00401c0700701c45407680498040c0c2250803041c0700305901720007021040e203a4840c03c0c0c0712400d458540b0040110303500d145080085028060808501d03140e495001c1161300d5054507800510112003000103014560042c030152100d0f400070b1415440f03180e2104e40c08008500207800c502c0c0400c40d29485000201403420011102d41d142d85009002400d2a410140c6100d158000c02080801d1071b03800240c00d9100c0440030708581c8011411104241841c03040c007c9801d50030300603940000d1895800106131107000030707100100c0303401030368040c503144007a151456501889050b00c200024101000900c081c401d001030801c0c11074203407402d65070b01c41190026040058800c1c030280035007002d00402c000150520200703203a02d00c0500002c03c0c030445c400740002c01000d01e0a0003a81c401150382281041c00f1040e40b0480e01801064100c4968000d50b404001040300b04c03c5485c00011020014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 979906115 1250 979904865 979904869
    0xd020d080a0207140c090124050d0f0f0902120c0f0d060e0f0709140105031504020112061e0b07260418020c010b06040b04120212120304051605010c02 66
    0x240c0768850003000c1d006050482590340c1441c0402403084402c016071282118504620305140c5440c01402030040c80c054030709250000401d014441c40c0701c04103115010800c910031381240d400031500d0140d500c2041010b1290312461000803c0c00c10406da000306240140e901c9914000110a54481e000400001841c00319101300100c150310032908850443d1917182050700084108040751400c04614082d00c13001c3e040090960444d2500c00460162824100041101e51030114110140c806205110f0140e6529400107981020004108492040c64404001071401104007444111070000d41c50b146840e5880f00c010045000d2150060030a4070f86036001c02602810502d40302c030039030f082004242819580d1030340200a1920b941440e000540000749549802000e00c02c081d03078040100e40c41420075040110030043c502490140d0301c1400640c00e10201503540d01201c4481c0008004c04840584486001c0200c1d10b0300240c600b110030303228a2500040002d00f031807a035800d07184181d40380030341d264080d02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 979907365 1250 979906115 979906127
    0xc0816050a020714040b040e0d1701180c02010e030a0c0204151a03041406041109160914060f0f0a1b05060703051e0423060c0412021c1b080d020d 64
    0xd00517030b01a41d107206040c0c590700c56015444070529500e028041800b08204042c040380d5001e444288001061401031042c400b68126081450f103554100103040303420410183d005019140c246041d03407201041c00c45000350301c1507094104038402c3d107052145030066451010089200d0040158408110402400d00c1044601944d4030600603500c40c5081c5114114080c10402c09030b4041e200340c20910340600407405d01c0059550402140c8001d20b100754801d40c0020800703243c9005e0009403541b4200150f10a90743c15050710000003c0d500d003c0e680d40203011003c01294407000508012036080d040035104081c06026650015402c00050980c0f5582c0c00c0e001c400500004203908646403944220301000c02c803160030300c2c1c802c038400d030799030403030040240c071040058019600c107076240b40c0c0318100f002810440c26040c1e40480d03414402115204011380300140710030185612103c004a10b2401c0802405400c84403840c0d41c414910381c290580da102d00308161176240c80c0f1052740c050f0348480c0399003c4442c0b00b14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 979908615 1250 979907365 979907399
    0x1206100e0f0117101112330406260609030a020c01080601170a0c110a2001140f1806090102060619120507150903030c0b0601020106090c0816050a0207 66
    0x80c0c151100c4800e0b07002ca03002180c0c4820030380c851050010542c8961007000c0c1140b0350704034524500d40940641e00d030707503407d924212106080c0c00f05461400e401c00907031902e0f0004e00c040c0076800d8618030100d088540c8081c83e4103440d100038095125001c00f00e80304c0e42010044402824640e800341c41e222500308015114414040c003400d0401c604440c2e4803200741e41440000f03010760b0059101180300b00c1d113507400600c0951840301c11000f40d0800f0315281b00080340b41c04020b001202c80508612000240700040e1080e0511140c2242e90304000a03200030100c0001d8014803040e4910810711000301140014425030740108440980076038025400300d011403420b0080458018114440ca50500307445003483c041210a0190884842d40051414800e0b0a0000c02104020031240741c058803040c61a00d00400001c1101e0010b000c1442c16404185240d02c00c0d0059400f4014031001405081e6003014000e10411040310403070001e140030074400014034821070848841007103e60081188604102400540603110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 979909865 1250 979908615 979908659
    0x14061e0a09052a01120c2304030f0309060207060c0213200a050406120e0c100212041d06030f0618010b090a05010e0f010e0c0c0102091206100e0f01 65
    0x1a01c512801004a5443c081000c04015088122020070303c00240003164400c110b070b032440b402c2c03c01403010503034000d8512424002140501781da503001c5c507007a55014070503a040542401818440d8206058201ca000c0007112242c4c1d0817900c9503a034880f400c865180b40c51000039845081c402d684109802c2c40c1d00140e03c00d0058025032030140c2c03101092503400354000c0d81c00c880031890100d001c11002d030300441070828000050380c1c01d000c403044111915442c2c0803a40719552240018090595460b0300c2004000d005508840308566140d40f07607814480c1d620345140360003005c1410701c00080e5040c1400310b401c1034260196001403c4646501007001c2a184602c40340c2c082c03c4d0340c0c0b0b040400b025914100c845000f00e141d89000601c1e541404183d280000d00241010348241c10b6600400034441030450460744030400c41341950701c039071b070141401e40a4443c0d0142e2960201c40840c54203032030607012504902070703107404545a181c10303034402c0c0020450100312400080d0425041c0100241c1c010704100000400305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 979911115 1250 979909865 979909873
    0xc050c032b18030c1b23011107150903080403050a111e042301170c010c050a1203020d0504060605190f03110621010317070b0601121814061e0a0905 65
    0x1800501042002c40d42c004101d240c84c0031114500d006e80c01d01c100f12240c40a00e44442240d0022440340c1e660360f580d00c0f41e2002135066444065000f44114240009540d100c2c44c420341d80d03685d07400d100340d0301d184140f41920a00310040ca281198509248040036841c030b9000020000c10b0620b04100003458a584151a8050a10003035104404813480c200e02a2000c0030302500c085607e40d90b41c1d031074581c4c40703004581030010800e4500003282e80080ca001603164055000c03443c2d803d0380d00c02203000c5c0c012580d0b205409800c3c4010701080040d5a000315043d1399094a0030007800d074103082070140c083c0e07040c4184041900b00d6501400801c42e4448001c81082c409010545008030050895299070607107402200b012441c07600520411003980003500900030580c4010703041c010b1a8503009142400905031174140405283c0340c1400850b69045039419506145034140c00e40c941f403c004c0f82c0d0b002e9404501805004c0d0f80001a403804481c2d0240d250200000c14018040d03860240010003002903d00585540c86 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 979912365 1250 979911115 979911143
    0xe01030f02090a0b0d140c010203070302060103060c1b030206040516150518121c051309021605010e0309091003050307030516050714090a0608030d0c050c032b18030c 73
    0x40c2c042c1884442ca1182c0c0c0021006043e000c8610b0034035002c40c840c1f078119081001102c0c04a03500007240f50640750811400541c0d6440000305a0b19103c0c8103102e42d03006030200295400349500421064800d41c0a03100b036482c0c0070380e050002095480f45000d54414446040c12030f44031244144060480020101b0568040c0d48102e00022450060032000002d81d134030495001c0080745400c0700301000d507a828201682044d0400302c4441082031a4050801140c0e800b00d000321908070300400d140724607034029008100301200300c095241c8952110f6405402884040c5c00f1030314040007160818202c0b6008000f450901007107075400c585a600c0f9248107100d801007900007201288041c881a0001c0c88003c0c21001d03040e40c41000e2001804d00201484459031a1820411007044040215294080b00707034400160300394144400c2e915401110840c5115220225980110140907000075890b850780e034114000e415581d4540c2002d60705814005544100744541c0c1100082c00743d0705403040503108040c5009006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 979913615 1250 979912365 979912369
    0x30708090601270603020d050705030d171303050909010b0a0906183c031103030717030601032406020c031209060d0f05040f030801080f07031205160c0e010e01030f02090a0b 76
    0x1000c80f01c82a545038109c900300b000103180410840c5018410340c14000144007403140c194003103c4009203220250b400c207140801c10140f044040320a42800140074001c03a58403020310001d1034021f1143e10010034650600841d000e8080e42040d46582e44020304000c0550074402414400000307071783c83c084840004140c1001c0d050380781e001030800220300c12400c98103d185d41440b00302c100711070400c1c60094004014580c041442809001c5000354680c8210f40d80f5210180103c0c000c0c510142c03081d5103034040f54402c80360054001b2500045a5440e801c8540c0100e80b6420562540c0d4801c040740c0c012442000521340078101100030703120201400c000000d034032940758100c10548030212000c0350200d40e140c01d00170400d60042700755400f401914004000349590343c3c42c3c1c02da0300e180328040506102d411702c00c0981080d10600456034009405082c90302d101100340b500e030b0000c0a003402941640e0700404000716201d002248842e0407a030300700c4000350200d08141c003400380040006d0568a86242c80c1c81542c103050f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 979914865 1250 979913615 979913629
    0xd09290c0723071d0a05010b0405030d0c02010e1020062206060b030c070c0b03090309040203270d0f05121f030c3b271203070809060127060302 63
    0x218502113144485243c480b550108641058001c1c4c1900d80c070600c0b060015850004d4603e510304102c1c101400c500155000503030b8600e024420241c1e002d40301c0103c0c149520340c801c840b1039018a010010781c404040d220405511858100c0304000050000030343e280d03014240c24107021005005000000e50540c50703580b0700889a02c100d8503481204400030f022020055514a041c0040c62004045800e604004548640f603210307140246105a80100205a220780c450702c0140c1c11039a4580f0000050390085502a10b460f031200705140450780101c001e414071401a811244101c1001005800701d0f03503076070100504094408884e81c403102000c80c001c80020381000154016001101203598980c450200495590907a0702c00d0042031140350341d1210a03180041c0b001500811281104040036403401132205c2146c005d0f07800e080e803030700c501511043c0080c041c4009500652031543c80c0c4d020344d501d03440c3c2d040c1d58090030b100381003160301648001081402a040400440f084441012525580c0d0350001008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 979916115 1250 979914865 979914899
    0x3180d0f02030304260d140901050d060f0302011e0903121e11010b01110d05071b14040b0d0506040b090102220f06020a0c05060d09290c072307 63
    0x2c54030b0750032034058a06009456050354400c01000309055808009010f1508807881d44c40e147c0d400315000a007030703003e44142d845031416414108a0f00d0381d02d403140096440710340700680c0401c2c1325080f20000300c41503050f56099605a5210710300c00030704e5a515002000d031210b1a0310200058600d4144140600c2c0d00303441000b070420780e81c041131034803805c000a08507142203c1050500c15520343d02c03298a003020904c0d040c6e03c1c11030b080041c1c48007081e0500200401022001c2580501103c4000c1600d88080c102c85880060aa03410403000a5010034084880012903001d08039a2000000900085c0c0e00da50442d400504000007600742008400c4120403c80c20703074549081444400e00501050703480460b900d0042c45244024542c9512a8541d00501c240c1409260b0044d00009440d00e41c0031129040951880d80c020b05070b030f40940c03c0340300c400b20161010751104014452080429500c421070800d9802c81d6410002d0001120801c401c1c44101500000c0e00b54004d01035004d00151000c41e50b071507810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 979917365 1250 979916115 979916129
    0xe040f02161203060806060d0c05090c0307080604091505060a151e03050c0d1107120e130c050f16020d03080415090c140414090d0e0303180d0f02030304 67
    0x1c400d40d814a08190707a8140c101e000400c0500d051000c0056060004086801100903901421b5540c00da0070074080c02d03d4580c1080d6001880c13101408800100743c8011886505550390b10b128a484034420803061310319080001d024100500308400e071011030f60b40030300d41054004081c51389065030b6840881803c02c8007281c81340851507484407a074000104020701c03103062840c0c0c60b013040949080074085105019001c1c140000c0d60f95004040d65040a040071100419085060110341e141c501c8402000b5483d1001d24601400fa4030075029444117081c0030760390030f030f11442c0c480034103100c21202562003a800080c6003b0b1500300013810700f405030b110081c03d1000b480c0265140d64882ca4a800e03e01c040960030f410015a4074179002c0c0c3d10001c10030340d846020940e015200d0100c80344030002d0000b03010700750341c4201c45805102c241c1842601e20b000246405600e00c1619550014030461040603220b0080075280d0a1103220010790321500c1c90040d004914261081c0b4602c4880113058010915540294003c0302e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 979918615 1250 979917365 979917397
    0x10c050903060c070b19020c010f021b0604050c061c0203010311010206150306012304110a11070302060904090c080a111203070210080901060317070c0b07080702010e040f02 76
    0x521541002c0c004a42c0c0002c00c4040d662800c2920742e01c98078040c4000344045500c1507480458903007640250102c450013001c40c2c0090040124400c4070b4002580044c2d0038240601071402d41011001d00851140d208a030440003500414110005020b202d5114810222103072400040c2c44540400910165010b1030041042c1c0007003c04940001e071038003101400c201d034501384101840900d642c000415038191072a01d90040d504110562025543c10203403180e0036845070411006040810704440505020441a95442c003920b1312300c0c118544541f103500000e0340100d000c00202c4203601705a000b000c180c1c0d21426500c00131603518442c0c541006903001d41100c8030007516025100c20702c1e11010541000b01607402543c9010540da0010b030705c1d615056844424000e2502c0015403030142984903c0c01150807291052050010720000b5200e940701c454215620406024081801042c01003900e40c441d0744010003c0c41e00c80c8503001514403048010a495000d81c0700e40c00720060181c180041c2070558040346c165 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 979919865 1250 979918615 979918627
    0xf03060406020d0b03061902090d12021f060b1e07051902100512040b04110d050102042d1a21060a0b09010903240608031309060303090603020912010c05 67
    0x1140c1614890b0380300500c240d100340c0500c82001002000100e40c60a00b190040c3d40317941840119444011164024bc807070b001400080810b00d402081c0a0704800701c00c0641d00c20142c40004600441e1241c0c00b442c0392240d002e000c00c3c000e20314415078100500c1e0109000b6410241295611407500c0a4080b00e07500c5c480460004404504104400c0360008c0207a00b84203013440b03100441c040c9000700c0180043d06044881000c10b0a02c92540030000301c001029007600810b0030203040c1503000c0d40c4580f140f054078920000e0180311801c00c00b01000104021b80134000000f607c0c4c03410f50070808801c03040c1d141100000300201d0820800319004401c1401000f41d10b1440c03072a0602c00c01c29206072681c026a0005d84c01c000700d0400303a034410202819682c0c0541c00c0c0b104229690910300d00741d665512900c048504d000c00101c0c084130004060181d0741d2032400c0840d841a1611103480944031180310080204844560611159001e500580b000e801e01400e074031046c0c1c0300403401a00f59010102e074000801d10000348 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 979921115 1250 979919865 979919887
    0x11071a030c0403320a080304080714060703090b0f070503040308100e15010f021b060c01061205011b050c0a03030e011b080105100809060703050705070c030303061d190b0f0306040602 80
    0x109114101c4c1c4003a0640700300a40360040c40f84401400103004110010b206020020031603c03200c2c4040400048461b9803078046806001802d218606a89800c8038000045080c10b46a4169219800c11361341d0500b0b50701c4555060300e205c00050410312110b81001c1c00441c0c409440c0d10b016110b03405280c1000c0560b00e1000000d801340c40d103068030702c00315080004192b1a5400b2801a1030f8600783c1691420f9660807041c01c00b0b0f00514841d00030715081e5841012075028400150443c2d607078100d80494010300110b00c1c05d01a07400c0d10500e9200c407050780112000c180441d00070752100000f107035244000700d24029841701c03240e000b1518042038000300b45254010302171030500d905d00344829071144c2071540450505083d0a0790764034000f0505001c058031580000c0050340700d0310076294540e0b030081120103082c2c1c4030b1501a020300040d00903801100d0991600003c552142c0d4000c8d400344401807000621004201c00c0a4003038080050a1504290501e00500310794504004503440740c3c1c0036020050b220300700704107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 979922365 1250 979921115 979921193
    0x20d03030b120f062d04081309090c08060105120d080411090405010509122a012a1e0c0204110c0d050c0706141219050405060711071a030c0403 63
    0x41c840d64101300c4031700c01c400040540b0065500a82c0003134010f51640300d090103a81150042e0307048046a64200901902008002d0420005890440d4191070b0940e0300c0d1418020403ca4402a50080d54880410010a42c1c0200c4019070045d028890503c220505480815000340e41a18101e0b5560354030000c00088070000c0c00041300c00e9060345c403680e140c08180951158081d00081e0f42d001c0030881e484842019200961200d2001690b85140300742d50f40140300103482c40c034403120440b40130840c4184c69444a140300603201080692a44503103104450a4003800000c1c400c84400c00d010540070809100000d10400c0b0000c01100d0980d04c80759074000c405c8145040440983c80b500034018400c06450a0314501070030380d96101d0007a10030707191035501d140d48210410744910355612858909405d002c00d0060115200d8820600b603284c0c84110029850503956800040c07003400071000c00d03032801007401a8024011600728440741c88050400e9204e841d4004003d00b440880c05600702000c1e190b07110340e103900c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 979923615 1250 979922365 979922401
    0x2031918020307060f020705092203020a0b011e0905060d150609060f0614030903040b07030302071214030a0b01050903010509060711060c0d0e190303061809020d03030b120f06 77
    0x5ca49890306010b01c002c080d640c0d42c260300666101c0c402803000105009001c2000741e40a10752207200b0511401d5a0034085d4540341403101c15a480e00458001195141c441c02c040d4000809030f610501c0c8081c078101c907107801000c000e400c159102003498440d0020a24200c04000000c560781400034940c1d142400d018100c0b507030341e4020248804051002c02125800c4601b5607940070740795810651302e5881c0381816040d0712480e00810b003000d01c00301d54007080c591300d40d0141c021a0b11401c1e01b0075848240aa080e14840d07910b11454140030010800102c043c4030607040400d180d60181025800c010b002c00009007550000c4a0440d4258000c50030012407961141039101106124806046182008102081640b10340000103826039140c23040d010104401300901c0c520300c114503050680580c940c0c035000740980031a100700c00c2c032900c88445035804e12071944289990640d000304044d0100385260780031b41c09414408c104075480b144020060554000038001c0034000003030038010b051070b4940f131104412150461 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 979924865 1250 979923615 979923617
    0x20d052d01030b07030e15100614032802070b0f0405010605100f0e0d1202100b01050c03180103090c0807080622320a020301060602031603030203191802030706 70
    0x100e0041010a00c04010142c02005a00c0d0101d40745092001c1c3d58604180d00c8000b584100200041003149410341d01420240c034403070755409064141e0f51242e41044d0106480b40a8010f80020b9041f110240080c03500325400307503011001d82072100940362540100c804440c610142d0f94044c0400c07017006400c0c483d80014002c121201c5010f001c02e40001010582c000000f442808414252596607a8540c14150555035202c4e0341408404c00103580251101c0241c60b5280c40c090401e168480c03190f01a83c2540c6104d0020802076040200500418203000001881541856515102e0340b0100e012503000b040640003450045c800c89150040880c80c0c001e0040490120419500503446180c040007003011819070412461184641d0810503800c5034800700b0708070300201d090300e4158440010041801000c49008a008004060342c9070403c2c1d849109141c0c491200c0e40c030350210f62000034040d40c042c2d03030406180e0996094141046406008917080760880d0040182a05084e800310310b02040904040d04030313 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 979926115 1250 979924865 979924951
    0x8010f060e0c0309071211090603060112061806090b0f01121101080402130f1d0304032d0510021209120306130b1c03180b0901030c03020d05 62
    0x28001900104600203490b04220560003c08a080920208003820180c1202103001003140203600c1c05c1c10041c808021901c1c020000e04001600358600440c00314100d40f10100580340071501d9030f841e48000e04c04002c2204100000c48016008994684200c1217564800c039020b20ba581040c0305544c0c2a0003050340040815160550b20700006100011031507070010007802d01e11003036250f910024138242c038080450700f0b40514180a10040c0303e000d0308440c545552003a10b2030a0010000c101545038801c80c0409081451807030365050584821141d14020030004403031a028451301a40c03094280041c001e041c0007180d4020407000c54000a521080e030300207000c00001d044c1e20b0030484108100b4013008005511410149441038145d42041c2c0202091aa00038085428400c0501a150201030b0340101a00080e40310386030300d40414100e61188007034a012120981c01d01604400460290001c20b0314842090340901030750510340418003443d8040c0500c04401200844a45091b4030503442c603a22425407045 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 979927365 1250 979926115 979926119
    0x6040f0c120201090e072318040b1c1a07030203060907020c100813052a09011a0706450b060415050901030f0218060102031c060f0f08010f06 62
    0xc0c000742d807841203c0362440701c90f0745e59903803200c00c0c5d0702e1001c81407002d00c001e0401c0c102011261400030060100300000c80b40001445120400e21007280c001c0e0b0119908101c10080c1c4080ca20030759403a8005071071103851141165541603401641d01c040550700400400e402205001c001d20f011043c45601100c140700415000c1140c8002400c1d122070311a214050105510129a04507050307a03100e00ba607908402210a0903075001c0c50000f640b292095104403802c40b1403146081d074034210000c00d04a80b100c0b000404040c0040c10440019032050710120f03202c0d9661152042c1c0c0000200205400240843d048640c07050840300d0060441d041c000302040b000c5048000070009030030b10315116088882542c1c0002d42c1c0710142c0c00041003003860341000303230b0200a1400000420404d10344540b001c500c20303180010400c40856005658420589280340542c1061002c210414000d2104620301c15242102041403561281c103503000c50010381014039010f07400c400a0148500074010380300d11b840d040c001000028 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 979928615 1250 979927365 979927367
    0x9060809030a180b131a03040f062706050403171009180203061f050f06040611070e1008070b1e07030e091305150f0c0703020f06040f0c120201 63
    0x300c42e0311064014410901105100390000300395840c00340c50100881c40c0e0719a082080c20a014502c0c2c8105800004c400e19828181c9050b103050701d0003a58440d56880312a2041e03035a1070b000d0b0403a02c45a0170400e08180c83d019000c000035120b031101c0d500400c00000d00d0f0a003424003c22903540360316403a00c0110100180310b20385614280603403c41349410301c00181b00c080709000c841a00c0741000040c0d4584100d5052242000f500000140c540301c0725a000c0140306e5489003070100300d42004141070381c800001d0000b0004240150318502c501010042902c84031034803070701304506015054810f01000d1514102c01c0c8040780e01040704034040c0035050085420400c0020341030071706080466024800c1580450458100f41c0201d48441c00b000006243354580d00e0811410003605c5015403050320b0381d100d850500021503c21544850081000e43c2001e8070568650395140034550010904404510a10503020301e0382e82e040c89414000c41c480d00d5010402c44041c00d03e01d031003419075005100240c501018600050b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 979929865 1250 979928615 979928617
    0xc03020c0a173702060d2c0a02030a11060d0906020c0f2a0d050601090b0a0603050609061507050a1b061107050910170c040f0c140708040518070906080903 68
    0x2065a450f48000b50719181d00c04504540280040400c4603030400e503484054840c450b02d1501366410608100340412820603000f42c0d900c1c603810010750540c003d0300c40f200124492550440c50143c02601240c5000d140d082007404036050080c050351604e50101303100c076054106000c502003021074540244511003005a070080b07134403610f43c0940d040402402c0d00c56590b031200c0c00440852500803081d1039403980e440c0340c0351b4064505100514420311020b40d010500300e021384511703801800d0186c01c40040303542c1d01081c04400d0303d40217408000304500303000c9840003a00411400031000e100d50314462000401e0f09182d0103040f11034010805000c404804206510310003d00002160030488654140d5103d012055400002c10b820140042a01b00a10360b601300780020a81c0e1815001e1f81c0400035210000003840071944102072001c0050034007a07107058010202806800c280e40240e0b0828607069481c1c0024a0b040c110002800c000d03030300a01007003455900502114000c1a080c00c08452900d00b040c2d00c44d4032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 979931115 1250 979929865 979929943
    0x9030a030e031b031c0c080304030903110409030813030e1012060504021e09040b0d110109060509030703032102030424091101050d060302060f220b0a0c03020c0a17 72
    0xe42000300460345d00b407003001c403944040d4214941650344d00381410018140400c0f07000681e20302803441c0c3c0c3c000e50350070300d841500c19154259070307125459110304c585000c0140030418185c0c100030280319450309907500c00c4540003004034036481e000100180000090300340d44155005a11503481070050b08111441c0e440401190f85034047c44c00e503940d000d032000900409031040c0030703600624080350040c00c002802c501650001400d885400c0466036911040300c80d485100501c4c1d4260b0424182000000d002d182654801d80b211400360724100a4018a4000c0380c104a4056581c1181c007405a401c100c01c3c4a4000c0b184281c051081c86961841d8864801c0703540d40b01c0711a4100800001d0b07801c1d1041459100f01e02566009190b255504040084117400d904281e01d040b030146108084a5045442e0104001c02c44004810b07070380c01e2244900c0c0039540409070910580940c044d01e140d205107a034800b00c070400909101d4003c040c642070850102443d00c10700d0040808241c409a4140b80041800e0340c0d440c40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 979932365 1250 979931115 979931143
    0x80f2b05040e10080a03120e0706090b0c1e07260604030809010b0925180b070c08100c0306150801150512040809090f01120b060609030a030e031b03 65
    0x403030340c0f01c07100c1090608545912100e440d000c0c80580c03500f0141c0c05440d89001c4a0701700c2091040b8030705e40d000280c0b070342094410030f0040f660000c0708205945220001d0110411800203030ac07010448103007044d810f0030202d14010a0b86d0410a818000700a4030750030f01e6070092481043c099507140b0030700242c0d40d607000600f001d030034420100c0014801080c2500b040340d1504001d81030406605002c07260000f000214402000c1440c02020480c0185d84900c0d80b0300c050827016402d499480d4a444152125940020030030344040c800c0d0000415001402c10000111113403c40000410b1604480024200da0f0542c02131148102034521f05a195580006458190795900422440301d4010307080c15143c2d0712805c00e40000c0040c20804100a102d03403080500500710080e21243c03c1039507110701c040414903007406401c4190030104400303008100c40c00035a5510140240070185840304003c002071500d03292840c1180040c000104103405410240b201d9001c501d01ca1448404440b000f0000944448001947c95 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 979933615 1250 979932365 979932389
    0x7060906020706080613090f030806060c0a02041a09070504030c0f0806161b0b0609010905040f060506150d09050c0a0b07031416081315081f080f2b0504 67
    0x1700940e550755907443c0100c503020703800c005c090203d142c880140c80d1940c0341640468030400c001449800e004d001c40b503172012080082c0140c0c00342a82040b0041c0701c03034800340c01c4002c1d5410742c0007010b49414841a010354420303140ea5031214618035000c1102003031a041318031000034209040015402c000f030f0940e00144402900b80c4000c0d40044100c84502e6161120702640c40038100d1003050001d144140d901644050702c8450355a80c89060207410f548068400800c01e026818042d40829010307402183c200800038070701002e40a4407503038410b050300b003000c2241210740c3d600c12090410804019204841d282660803800c41440c10030f00040b80c1c06500b20140038001000060710091046d28129002c881040b08030f81c581d41c40701e0070300d994240c02c03801441345502124400899034212001c000301100d03050303070741c0c440c02c0b0340d9907030306c000c285402c05800240424a0307418003054049040c0440110b0303255980c003c05603201c2c00c1d041e00ca10703200c12042d41c4001d11802030304c0c0801d580e0311008450035202d001c1c14003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 979934865 1250 979933615 979933621
    0x204050a061b0803070306050102010b04050105030a1412043003020c04230705040e070206010308090d0201050c12370318050d0314010b120105010f03090515010501020706090602070608 81
    0x164010a0301070b04000c254200000401c240d06425a10000035104203074000c0018100280500c41165028014598540d22100c0140c00103007031040548608001031007170701c00700d002500b00d0400742d030825080072070b400901c0090000c0c10301020041d20b000290580d694801350080f40c81c041e450780f021320300e414002e544402031200320605600e1f00c0b0742025602040b100451504d040010051742043c000c401c640ca1a04001c0f4002c503200040b86816079800060b00d520304803034442049400080000c04038107224041c0703c40c180c90320080c081541c048a00d0412169200301d02d542100141400f4681d03251001d020b130442d0400b01403c8012040008241e0a00042c403114013690b4200c00d00312504001c103903103d5000754003c40d03035064000b201603280c1c060025050f6622078102e075540307004007079485500e1110360300100300c1d6601c100b910405848950900094000c1292107082c2003601052800181103007c100401c46942e04000a02c020300307080c603207509000d0500030001d444065902c078071000c1101c490b003c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 979936115 1250 979934865 979934897
    0x1209020a1e030b09030d0c02030a0207050f01030b03010507120b10020c10020f03190e04060305210f040b090f040902131e0c02010e010b010e0a120804030f0b01180204050a06 76
    0x1e46000303550003600246a6292100c10966250301c00c248522a041c28100c0c0103031aa40000f081c0ca040e0b10103500a8403482c0d04080a12600b1240440c855040540b104950382c2992400c2c411203000c0c0d00c656a40d504840e43c01e4090906803403040b0507081c020b62070594130b403e0b0aa40402c000e20008070440b01451040180041285010450400d14145000000d44181121081f005405540b200d944400048a00701401c001c1251528071015010b43c01c956440c00b5004551700307441050212003c601030034404810a04a026041078220002c0346100280d18289440d1007085900e2105080780d0500c8681713244d50100c0c4003401c01034058040c0c1500c55200920320b00540c0c0025203801c080031410840a501403000070701070408074844060b0741d4609600080a5480b80e030a03200c0c8036802509035034965240500d00b28078100019001d0311070325801e2002100180510a004074480e001e958a41c03a20f506010706c11281c00654610358561a104101c10440383e143c200d01d0104031903603810181301c01105911 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 979937365 1250 979936115 979936169
    0x60e0d060e121201090c140714060c040e060a030f140703060f0f0e0c100e0d0f08040f061d090402030313080106150804231005010806071209020a 64
    0x800d400301070099021690000c5240000303456103c1425020f1800351340d07141e030030b442100c0c10f07404000002104001e00404c40710101c0c00510200d441541ba07510054502428103003040d409964042c0000e2000a04101941d00c2c0840c8903007040084500314440c51440d5905120320034440802000c807003e80c0320904551209016000046800c01020f105821440d51035600400b2074907a80d000c002c0c5810f6280b1034111300018030042d089405400c1c82402803500300103541002c4142c1d2001c1e03000040e5840d11001600d10250310050130300c1501d240d500d40d1b08210700441500c00e81e4211808200100c2c1034200c80c042c220394070401e180b4041ea4600b410391a00d002203070440c070507003c1c0c4d0440070992040019944005501c6841215400c40311036540d403031500c3c02220b4903441902c001e400d400c51480c80000840710b0384001d11140f281071040f01c40d00e10481103030f6026075400764010700d001e42020080001c0d10390405520441254545003c006610103540000c0850b00a401a03400b10740c1c00185d03001c000348503a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 979938615 1250 979937365 979937381
    0x12030115090b0f070b0f040f1b03080d020a2304093204050d05070203030909071b1b050607080d0b21061b0a08041443060e0d06 56
    0x203014039682d04500210420b0f280c1c00700e40e007158982d42000019500380c159956990180354822078441841005450700c07186800e1403022009212540340d00000050100b20082c02600440c1d8005a1074901c000006441c10b89408086806051486452110101001d04a40c01d542c41d51400007844199015111035a444208a00e007048410083c03218044c403401c100a840340740b06034111800455004001c42e9140070b1194003d4050707005220840c064030b031250207282c0c04051031a101048402e818403101c400311503800243d50741c1d03c80c01255440036500c102030202604040d10350514100d05c5940c0c0c04500d11400d11080e071050360307450341d0107500e56400501d921007c1c55101c64500380d443d0401a1520703404203940b88101c03542540030520040502034140c54043d45940c1301c10b030141d40ca81c0c032541c1c44150300c1c00301c4000ea40104a084020000301c54114101c0b15200c004141c2c1b40701081e04250032161030040d00e110440c452100400c005544000c0c100c5880d10152008641400140340441c0030744404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 979939865 1250 979938615 979938629
    0x161a0c0106090515030d09050a0e15150c07050a030213240807050118080c21070f1d090c010320032a0406050f0702011125081203011509 60
    0xf1041c001e0200706a418804840021016100c001d407502c11305407112407a034445c180e00144055400c0060b244800b40c9a03a200540d03600e41d1140100c0b040c000746840495102c3e0f904200c40100d03800c41c0d8084200059009040159901580039041d900028031440c002215550f500b0f44980f14246203082c120340700050603807480a4580555124040d05460740e4841c06090300203000c0082c640310b200c180140060403900c0c14401f0346011100e65051040c0708103a40755480f2407030180303c0240c0fa02c0d44108545401032000d550700e10615410720842e010007034104d02e0445058600401400000600495080ca001500342000030382d100b070700103c00d0185680d0f20300d00c0c41c1c1ca860200030401c50003070354910102692202107a1404161070340e03800d00c140d07002e68058100000c001780511000001c0d040020040107005041280104c00f0f0400801d250003038a910505405800c0b00740383c01803055400d0400e024112400c0680b00404113102441c48601052040c1400c0c002d8107580282441e02035640d05001c0c0c56a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 979941115 1250 979939865 979939871
    0xe0c030a082d0403060c14040b03040c0608070806040510030b010b19091a0d0f051305010b0f011707051c0b1c021e030c0a030b09161a0c010609 63
    0x6082a40e5503422144400b078290a801c005101c50707a1400c07501441003102d00d00060304043c1103440f2040140f28441c040c1c000d005a026090070320240c108040c0c0000c0000c0760300da503624509031a04804d1401c280c0d1000c0300344030340042444100354020211781d038025819140081c0c142c0d5001e02c9041e1400380303580060100c40702ca00010410503861070090040f4000d20703d070384610300c0200c0f0041740d42141600c1901d080d0707801590000441e40c500c030014030034020801c1000c2a00d030558154038045810035607201c0d4031074002240e000e0801c9001c4c0640c0c880c5000440c0c03014145001000041c03c0100c4104009050701e11190000380198050015200800c003410359080c00c00e0b40340800314000307109821105104450b00018119011800349413030b020303164054118844818001041d020001c2841000381d458028003001034015150708424100841c081c6124400506110b108507050030008489803501d000c808400f400b4080914000140700c001480341c1c0ca0303540441611042c01001290000c84807141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 979942365 1250 979941115 979941133
    0x2d120102130b042405040306022101050406080705010c0213180311031306080405010b060a200604020a030b0405070905270706120b01030212040305030103141f0e0c03 73
    0x4015805005a6103001c1c1d210900507456898002c65405580b00c0c00b0300e240d07078048000021060040d0224003070005810001e04240c0c890b6a2403003647c001c41e101ca2001d03068003d1070751020044490b42030040c58240c2d401c008550a01803100e4440250f8083d541c107020080d50408110b40342c04090b4503001b064904100503c0311240f03000c044070030784a441600000e80c20074480040e020080100c40b41960803920b01b00c01c06160502c140c6050f04010029541765590342c2d15040f941d00c50070020283c0040315034410a80e080c0b010300c0e550f8021052a02901139601110420005071600c00300101034070b402451070b51160780ca0b40b070080c1c60a485a08480d58680c10001402070700d000328200103120700c00c1444000f890034540c040b080e036100d0f0a4852000050700b88082000c0240040e400000d151a0615015140600106c030200c090300054604a0024200100420500001c01c030588c00c4460044050702c194050001e4092810b20030f60402c1607440c0e612800d40401400411102103070b80006402c0e503044030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 979943615 1250 979942365 979942399
    0xf030a060e03040f17060402121501030c0906081b0f150408060f0603060709031721070f02070303050a14070f030e040e0706020a15060f0807030c142d 66
    0x9046441890268603e030200414200605e04a02110744660350007800c5d80e544a4003003103050082e510464909000d1001741d0020000c0303500b62140170354040caa040b00c0b001d02d091201070031103d40c1c0e0b200380ca0682103840440c3d5010508440b5010080080315102c94440e0600001107220900b604bc041c4440d4000500042d1a04c0214400c0c1c0705020964016030656286002d00d0b03102c3c04c08842490008021000500004441240744450800c450f03c1207800c214801502c05103541443c9800b5210300c024004110f84280d0202c1e41400001c454405040d400d484e59a01800500980e122041400b0303c401900500c4240e0708243c80110fa00010140b0701038182d0708001d0602000c0900c6103009a00f40600103160100000c0c4c02021240c682c2d0042c18004555101c804400b01490800480e035a00d07080001402c000b50b00d1082d01802c04080501102840c510340201c5640c0164024a00c500f0030761000d5000303946070f201100c3c1010490040545100018410388128110300c014507910410301c2c0c40b2100c2c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 979944865 1250 979943615 979943617
    0x6030a020619180e01081b10030903051c051b040e0c0c0c040c081e160503150406080d0f0822020a0e070908010b03070b070212010603210f1d0f030a060e03 68
    0x2c072104c1095076824107c0d0030400801c0d10a84c050b00d60440013070f1030b03c6004a031090b407004006a00914001d401d100c03400b460180300406641e00700c0810f80c0c03070310103210040000c984003920b50344001c140325240500c0d203c9079212244000700400d18001000c1022644480244080400060014800c0084000c0c00380d000d850700c0da09076039401b00100c54100401040c1024602d0078040c13a500c4580c0c840583c0200d00c2103c1642c0002d0a0b44905820785551440e10744650058174042c10224020340292094914014a4807840c4a42c1e8030802004605011151030300d01980d1208510780000c00710b5010003030001c5008046103500c4481195900c9003000b080c2607201032143c06843e8020002e0081041d4081090b80c2e98805029240c28100200182c034010300d4150384020801400b8000850700d19607030303154040010b0850490781e440190b0442c601200c1e66116260098440490800c0740350030050400ca0800080c10700a15406040130b02c02a55940da0200800134034954400310502145114007001511f07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 979946115 1250 979944865 979944869
    0x4031b0218012d1505040f080604051924140f09100515210703060b0f01111e1203090c040509033402061603020606030a020619180e01 59
    0x14119251824580100c1c0c0c1402070f225040c00c510402c0c25003401d01e003850b00f600c461441940103100b420071000800c4600000680300425055000c0e02c40c611306809c0850802c4806150300c100c14181d21100030000c0d109441c0c0c080094600500d15442141031001540107140c203445544c01c410041080040148211001c188962800d00039183c003802d6030503c103004d40340309594a000700b071850000348070380381400c880745050268001b9a00008112144005080c12400c2e0016100745488444005940c00e0009144030507600031b18140000f600c900f21141d86035280c8402c03841541e000701504240c100c0040085801c40500d20070101e0b92401c2403004181d032590300f0a02640a00d040400103480b6000c04019118080d125040030100c009400d10400ca42e07240c155100c14419401039045c00150b22204003030140081d440e40c0a440308001810061b180a0005103110b2082d400040003c00503180e1400352070030b904165030003000c551122502690003140100780001c00d140300d4000040c4005c0e8003025141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 979947365 1250 979946115 979946129
    0x1502030c0c01050f16111002090409080408070e060a1d0c0c010c0503060307060f0206010303052104060b12010209030c19080616030e03030c0412171603020609010b0904031b021801 79
    0x519005d0002041c0c80a03005664109003940000d41e1245081c5160707001421440c0303000f800021001115030388c0f039550343c0140d001000603500c45042403250070070030400c40c1e030024000c50f1f104c03000038540480503500b002c1040110304002c0009002c1b4260b04c900d40140c451110411000744115442c0c0280186950412528948244151040080c141c0d024075032080903642a60302034902c070382c2191010307241580560348030b46c1c01040c4680c80c201d145101c04070982c002c40c4516000f1503955a01020000000120481085c1c00e920400c0604940e44d000640c40c891180c058404020b4142404083c4a040140740c0c011b42c8580100e40c104981240012614210211f064408008034682d0f00b022554a0000700c4407426581000c0204ac40070701d40c420ba204c1078091140e41c41c201c5001d00301c1d5041c08160880c40903081d090504801d41d0b0201601803012a500080c41030003040300146180c0001c2c883d0300080c10140910400508100c00703c0c0c00c1128040c0352640240c02100324449185000d40032030000d1003a11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 979948615 1250 979947365 979947391
    0xc1e0109031e15090302070302062b021b16170c030102070311150c0703140d0e100c0c0b15120604120f02030c060403110c1e010e0d1502030c0c01050f 66
    0x4003290310f92040a01e21901680200b100c0b030308503400d100113507202c082c03003645409070401d10740b01c030030388030201e41040102000b80075071586980c1c3c100b81802c6080170141840c070381007074004201c2c0c0984000034500700d0b20003c43e15200c01d03411070710365030500d004040115055400020210117040d00580101c0a444007101200d0f20020005500f000c503000c01d03107114449103020480f00700400e100f4000c0c623001c2082800e1151401e681011010100d80c1e911920f5403481e048110005201c4040c0d2003119000103c44c108601c1c45030260356240c01403200142541051108070050f038405482c0c1554034404030001e001112448d09150429400c000582515000040d00d0195510043e910101c10b0f40c801d1140e00000b440e90b510703140d4080d2044040369001b40c8103032203540e1070108e40d690782004103c00c1a9211056030503090403003000400280c102880e081c054402200f500000a0100030700f503d118811910041c0c41e0b031100b084009642c480d0010130651582000184603080740810812401507003080409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 979949865 1250 979948615 979948643
    0xa0309140618030301030809060f09040e0d0f0f09030f11090a020d0501050406050303070b25050706060b0903030a080c042409092306032b030c020c1e0109031e 70
    0x209543e0303c024000104881d0051283c54079909011006e805810072410350741d803c04076501c0224040f070703410310034240e0b0070750000c03400b110b4094011201c2c0700043c420740382901600340380410281c182c02c018840200080080500ca41c24084800402056610010301d4001d0608003001044080d405c031004006205190500020342440d16208260807100042c024500303000068441c0801c81e000140455180302038207002d1a48411085900704c0d22420a071a17030340c0c440f801824940100c4d43e86412181c4441810840310240703035400015101884234900d05052555904845120350303009540c401e840c10702440030700e14220110103056010112081d0354136500c03130341e545100300140c458510505070818521700308030092140009820742c2c002c2c8090202d4000c03600341078009101c0c5e00c42c0001c143d810301442c3c02c41859550316000d01403101380c4a10040c41031140d0440055640761212104000380400030f4030192083c0d005240d2507004640054050940c0d2400348020245216410011034043d000b14043c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 979951115 1250 979949865 979949911
    0x118140709020c39190806011d09070b040b0f0d0504080403021c02060f071e03050316020a080a0e010318060b180c071e0b0a06031401140a020a03091406 67
    0x409144c0e04048003182d2068000040c081e5080b494240c01042d50b500d0040420440c1040064600a010b04602002554804420402c084202030044400340d000540304000e139015140995080e9032000030010ba0b128401d130310740c02d0640710380c914072580d141c20002000244582c3c080540200d074000d0382c1325880d0350008603904c01d245040b028000c2d84601d0602204103800b040f0000f40032454400c250808040400650280c81092454030450019500004010791280000380024047c0002c0c00140300143c880d80e102812401440e800b4810030500c40801d920903072084d00244800141900c51480341c1c509824040e0140181c1c86a0394010922007810940c4060011011031041c080d00700001d042414641d40d0411180c1000710034424541d29040c0007000c00c00002c0e6840c02201d804d04001142461841c2080d0603c0d500c1c0065400d5034900969003041841180c0101d92102859800503960100361700140d00900340924090101042088950039460001840b680a44a1610401454440c52103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 979952365 1250 979951115 979951183
    0x170126061009020d06030804090914030313020d02010e060a090f06051c0507031103010e010f05040b130e1011040e011a0708090d0b16030e0118140709020c 68
    0x140781407a0426414104611811540a84080d008801000c1016a03403500e4032140d54010741c01c6000651b40d03443c59030741003010b41000340b1901c14494000c1e50551824001c0a001086180006070051071665192001c5a114004c0d030f10b4455402410540c885401200c0107101d000c1074000c2d0856502c00b1280850050b00410a503003589a00385014020920034551040141101034040d20034192280d10303c490070905c040103035010b42840e4800948562400f40b011091f000c003607000500030382c40c0a05800c003946810420b1501c0c4c07401510080b501464500140f440c1407503413101c441070700303292107900380900c1200f1008008541d5032016021543e43c0b5040030000080150180301807814040040d00000790342d050140c140b158006040d1403202000d070320343d401c9003001100c41960424040c2d04128415805101d8043c502100318020860400740065041d503041a4504c00f400403008000103d1a01c0b00030822603001d4007500405544035001c01188907030b2114010004008903402043e03070701c03103044954 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 979953615 1250 979952365 979952371
    0x60b0a090611100f06080105010b3604091103060c071a091e070302060f0a030f1104091a31091e02030102070204110d20041517012606 59
    0x840a003c4400d03007091800d000f080001803214680351a000009010b01c0c0a2007558020059455803039038482d140100001981d00d21101040f0b14074a0109070000103060100500d0244005d5a0024210300340d400d045060018031151550b243c0f1a54003003101d060381150141c0151885a881d81948540c02c001c1022208411110364482d03500003124440010100b9072207420300428007065a84080d126000304160f9401018140103d801c001903a24544d50700d0701c10301c204900e02080070850149900c444085520179845031030365803034881d640b00c0400301110141d88440c0030018012a04450001d80010601d880801580d110f1210800d240016411502840d008a9440504400c400008810050000380c846a040c1d0305590b080c040c2b0b90040c1c44512901e429803003207210154990301000f401d036060310b60078441340402d4090b4a5001100d149050705407802d03210230881c408811010f0041c2101d640b8950344042881603000d00c00001c00300c186810386014403070520300f080150035000ca0180c0d6210720603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 979954865 1250 979953615 979953647
    0x102070506040822030506013210030633021f0513020907020601180b01080103170f0d0e1b01020c0f2103130906061202031306060b0a0906 61
    0x141c0010001903201c1c1c02483e440306183c1c01c0301408900c0b00a202003044158000311681c0d40024018004022110702c01d1103514a0030410501102c0d48010301d066004035140514010111007455901d1103019400103070140c0311030001d00e00808154040746184840c0807210308403215401d000501040e1000c1103040144683e0f0940a816018458201005000040c0b004014402d4201100c006a032946880350095001e43e000b081c3c02d50624160300a81c50009900300106403401607440c0301640c0011119044a4101c100700540c1c3c0c50f107540b80509842800805010318000054131510141981e218001c006d105400b156141d038201c0b141800e00c0108212440d000d60310821402416151400d040146030310050310b0081c0b03000b100300200303260074815a8400c20903080400c0030128031600051490041c82d002c1e006125081c503003a070107850a40c4c00c642c41c401154002002426007031440044078101603018004014603903443c02c80c0c00c400d401c0455100006520b454000880503c941460340000c102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 979956115 1250 979954865 979954873
    0x303070f02270103110102030f0c0a17090a09050a0f110c07091a0609120d030b0312211b04030308040303180215070501060807080601240206010902180d031d0301020705 74
    0xa50321285d030041000307068181140300802c8034040400810000c2c02582c0b04405c000d08180c80b076031600c0d00403140b46410466840e2818000c90b00550756130f81c198002c0b00c846131000590b43d1030b0910781c6805001006005e0314550300b8400c8200150754210f000702012020341c015a91102c1d2182050307000e40d0f20b19804060140144500815285480b2004058510004200c41140391944031001c0c00d1002c0002e409011940e104800081410180042e10b04022136021007483c0110718940b0070084040342d03580f00b04040b040800608800c030a1803058801c1407140082ca9200da47c1e0f450700800f0440e04550441c0005c2c180b00b01200881900c0400f410010390042002034110805003407107281ea00030780d03001e03503581d901c4000000715074030148030480261400030301520740e82d8100000c4c1800b240900015000740c800c280001c1000c0399001ca00907043d036407811005695003120b58a4240d00d2601042c00a6019108403460710400d41c014900310700c4001c1668000d080150085c080508034040c0c0b40002d081c40d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 979957365 1250 979956115 979956119
    0xf12070818040902090c03011809080a0f0903080403051c110d05090f0a14010f020a030e01050901030609020a110c030706021e0f10050a181a070e0303070f022701 71
    0x440d4412580840c50182c00099007200320b4001a00d440400d07181190605000401031100c1e12404059070310b0021507002c244070460385075072205540c0c03054038403000421038206401d02c0300604c901c012000542d0800100b41e10b0710348a0501030384840c5c140050391024206103600c00340e403134002c4811803a40d0000308003612000002550540c2e982c0d1060000a900103901214030700d40e40d80f400408806003150503c50900701c80ca480000d880c0d10010308480042d50720035055180025440842150045800c0c40c00c1911180720400580142150b504a100500d0022a0b08440c0e00c1d4403040004203100c0c0c45007200c4408156101b815140c1c0d90f28014200141c02c0110f4070107424198602d40d2001040700d00882d5040307025442450f040101a8554000341502e0314103024107012140a17104e204100307941070f1040740f1880e54901e05003640d0f600c59241444481000191418083c09402d01c5000024003600c1c1d440301c480c80c2040765032808900880c410180d90601003c001c00035111407154000301c040c2541d081e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 979958615 1250 979957365 979957387
    0x19060503160e0301140402130b031209040b0d1103300310030602041203081005010503072609030d050a06050105030118111803102d060b07050f120708 66
    0x300c0300c59081c001d108000c1050000ca407001d20560068807407034003103510305007040c0c41000414504d07510f070112020f05100000080750b030042410741c2039102c040c140590301c02e048004100904900d5910039404402d26000b002880500a00d000366250210156502041031440041408a9041c8118001c4c1d4080b01c400c44903019030402550810b01500b03503ca03a076640e03969258280c0c2d2141c1c0044044170b0000c82101c0400d60040b2500360030080b11844894400d09000008002e03000040c40d401c10030411030388844840240c0348e41e01800c00f8080c01700034014500421100d41d030368814982d410701603141500166507211644224826518140d45262840c0d1070f0000603000128004110882c60765140000480c010600c0b0040c001240d1082049121824540030981420101140c4041007400c1c292000e0b2009001d01c0000c0e100c0e00d010300300e040f0f044030404640e002024103400c1414000c00006d0048240703c400a0411512100704085500d1014070400e5202c050060fa00c00814095091041030842 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 979959865 1250 979958615 979958641
    0x1180b16020f1b0a182901020a0b0a3917041202030c031305040c0305090a14030c10020306040b01020d080601032a0c030306050406030804030605042a0519060503 71
    0x42c0400602d00ca0713140d41c8582c0c2100904814280c5800f00c0360756113031000c61895440d503603180c0751b24400041803000070352403001075283ca500000003001500c8000c0040c000c60107581c0f00b9007190320303a12a02684040b0300001c01500d5001c012644a1010441e003101202504c079032418684984805e0210b002910b842d074a000038081c15410410940c00180011480c582c000c0000e044204420081c00d10790382d00d032205002c04c56000b0101e60302058106001c001ca400320020b0f000203501d61024180c5100748400303100e18118020364541100710300443ca10308041d03100d607401070740c00340c4c500b07d9041100901d120010780c2e60f042d64800140c04076050b08009041580240d112180d6144051000c031281804003041200c1440b004209002040001c0110400d055051103800007500307080c0c8003082032905540b944c0d10940510702c4010a17540c0c9440006042003d00880c0101e4804130342a4030880007416510640040d0590144502855004490307085043e0241001c0c2c04031413440c1c80d800d203540c4484451a0f01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 979961115 1250 979959865 979959913
    0x30f02070203191a0f040c09020c250b042607081507180605030406050a020f070f050705041104090b0303040b0906130b0a030c1206050a05090901180b16020f 69
    0x4a0441d04100d881050139484007540b00310486003165205203040c1c50805c07940300b80c541240351070030310500141e0507074400000e820f0390106d42a10309020007100404402d46002c910341203080346540100b0009403004100040c0c0a50281400801e103041a042103010b5a40c070b00e0b4030641407181d005c8820704400340003201076140c01c00214504101c904a02003061403041c8901d902070400600004104006d21500e8403440c4d400080746d060551910f20501002d8041d40100780025040b1600700850f0300801000700104401020060030500042e968104200f516030400d2245103045d604000c01c61105280110884050340d0101410384d04110085007440950740005600c0300351000c9083c008580d480c411005000f0203096960085a0442c24a0004000716003400000c00100d0501400344560396420341c11101340c030015580c40c5816a22844024003414480c2a140403a0601262000c140620104814800c0c030007144110716200343e80d9400c9070754000b8049031442c81c0d007004c0a18180300d0600018004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 979962365 1250 979961115 979961123
    0x8060c16020607110d03050909070f022104031707050f0102090105120c2b0e1504023a03080f040b0604050a1d012a090e1909050d030f0207020319 64
    0x7000d04e100c00300e42c2c90414410f0940c0400c1020980000c02c0c6803001ca01588400a80340400c20101c4103034019603a03a4440002510103402c03540c3c041c0c44030700b002d01540c0046400c40ca00444084d00500001c02c2648428000e84450141e100d9201c83c4007014021a0701c0240183d407620314100d851100f5415101c005408140f000e1820082140300100c04030070b40095000600840c4a030b4019040b0300005c4504268005102c0d400145207031342219485800340713500c15010749034000c03029810b08403070b0251000d034214a4006803141c900c280d1015410610150904d03c640c0360f000b51034881e22980c5809420480f0000c00e002040000a03145041540003942c0244580001040d0b141200004901007a29041d411400c1d070365484200c14540214828041c10b0a4801030b00d04404600b1a8000c01104689c000c80c000d007000c841c0802d140c03c1ea0741c10141e0b1401d0640c40f00b00410403e51a00d10784a40003040101e000a0800b0204031060850340f08484526a005005004541110741a0703001049080c906403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 979963615 1250 979962365 979962383
    0x31302040b040c02060f100b03010e06030307050601060207030309140915030f1e060a090b0c030405190602030a05060301060f030605060609180708090a0b1302030f030409020408060c16020607 84
    0x41d00d40321030080c542040c499801410140c50b140c0c060042e82c000003000c41e440c01e0800c5d00c0c10405c409214007201e06440d90b007094030070716594000202e8958414560000e04071b1040c180000740403940072480c0c8054034425924101c525644840400c00000b8059250313500410b1100880c046080340b00303500d060020040c0607180c0e018042600305040410402809d1b1000e500b40d03112005010043c0403840e41300b00e0000003044080e6070740d1140401800e005114107108000000414240442003204010815160244c2050106c4500e04000607420a842440001d428070021507003502c2d040c000c45003030f2403035402001590740c0345071500009424042c0980d6000042000801c24035140c6400c0c010130440f400071000168208480000c118401c020010102500240c140f180080c00d041807550304501d41c511039a041d28443e00009007007611074425a8000c2c40000740c0090301c840c0d42d401400803610079009440440d511481c006440d440f41048000b4440c51000c11500186803807000b0741380082c0109485 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 979964865 1250 979963615 979963631
    0x3150a0c05030f06012001020d0b0406091b0503040c03120f020d03110f0a030605030a0302031b03070c0515160c23030a030f050d150e01170a02040e2503032303130204 73
    0x6c50883c0d1000300c00c03d800c01d80320b0000a0b42030810303014081c014010707000c4c04c00900c0041d0b0090b030706842034031030a80100803001002c034050028a9000c0c10156411205424a000600d44080c01e0300200c0912600076000c0c80320324071246d900a01c214001c055940d602140340004003505000b040c2c0c03041210740c092650350440882e268408204203121b29109400a6994005071907104400d43c48810030030801d5802000700000140c42d000e603010444100fa10405080c12480e00060000d00075401101d40b8010f01c0100c0030706200c10580c10804076441c40c21100d01c803920380242586000001159181c01d5801800103071f000030320600c14008403c07482e00c1e04c582131400c5000c031031040d180600750300840d400ca41d8006101808565600030700400507200c1c00d888842c0d00800f6962074a48803900070f84201d5466464440c414401d0040c46502201022682c130003c015880c1342c5154850381c081034001802d688181340c400c510034500c61210100308000c0d503045d0740e00d07a4000c541e00154010100d070016161149 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 979966115 1250 979964865 979964927
    0x90c010e040c1106040f06060f2301050705150a1104030b04120c17030103031218200402070c0905090c01120b060f0c011a010e06090d1103150a0c05030f0601 69
    0x40c4c2802103101e80d46000300d004050074114140c0d56144c205952900d0324200c10410708820801d5460210351601e0400d040f0a40040183e031103000340c29003d0454015001d02465002000c1003587c070a02e2150800c20180705403507903a07041c5005500000300a1100b91010038003280c03c42503405680825890840c000351915070361a000c1c890f055542c840302d40c4000c0014010160854409a24080d100c8820810b4420408205805492200d409002564110100613140340d1800703c8004004001e0025940c40c0701c580781c02c020005e50391081c10342d01407518000c2200e00c98046484000f8040594500900a401c9409440280102c0901031381c410001c01c00490b0740d00580d0080c0c01020b040d000000703000881424400060700c00700c00c26904200b032004614141ea9101c200351180c414056036110009100c624020301410384900c0350036418801c0c0e40d01c0303041111070790b2052889400c24850900400c007680209468a0000303032040745107090210000b0f04d20354411341c0c819401000c04a907240b1907040741d2030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 979967365 1250 979966115 979966123
    0x902150c0a14010213150306082805100c270f15020f0607090303020c0118150203070804030606060215040503040b070813090c0212030417070305130608060405090c010e040c11 77
    0x22200f1111002c0343e120a1032547c142c42048001c4c4000c1020b0030303e440d10800d0000341f8004600c0e1641c0505680c80114041c04010400f0f4451a0304810f802c02c10f1000d0401c02810302d4220201084607440703120341d07081402c4075030f0721180111004460f009100c14144151800e224a0040f01c0404510407100744c00104282000714a00811040d05c5080000303046017002030410980000b21410700200c0e081e810307007600381400d4540460304084520000000c0040301241503218118000c2c01c1c8890101d808403c1c008194041001c0301ca05808071030b010a1205403882d84520100d80150075a00706001c00c2041c840204002c1640d00e200c0c0000c24980307590300c0705036000f420f03803034001501031603803800e0707090715250100b005019400603481c4e20703410b524040e0344890303464020070f4400310b0400d0042400b00c02c06000740d0075240e150f40b00072846400c1ea501c600c0018083c005c104c41d9540b0172414140824030100004c81d0000c1644410b030b617119100041501400094040220103104003d010807140d050a8800c2c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 979968615 1250 979967365 979967369
    0x81908160f080316050a0c110d02061201170d0207030b06310b0d0c15050c0708012a0806041e090b060414010e041e060509010902150c0a14010213 64
    0x3400d0540b6814004c1e003140105128100100c24001c00300800c00e0b12540007401c0001842d480f00104005134031071f601040710310410350b40081d081680860403010890611280ba0305a964842419401e50542d640d0302d59070f0003c3c2e038008005030f08002000c0c00852040801103900000107411a15200307071515481c1d2042c0c0109101c68807800c1d0404954a0030ba1160140400d0740c001202c00b00c0300d00040f6101c036030140100344101c54103106024030184a590240041e651908410408e0b6142c1d00d9980000074042c001717084c0c44480590b1300d6984810072210715403404500d40c0b40d90b680c18110740d64180503c00204030210010260308549004070540181501440000c18401e00218841e03060000c02e0005442800d10901001d542c0d1400602c0341440d5241a150b0160300100c02c2c0000e82c2102e6040324515008103c05010103041104106039020150801140c640c403d452040034000021100c03001d50150420505d1681c2000d581040030a003400b4a075001c007808400014a8176a940c100c0713000f6202c1076 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 979969865 1250 979968615 979968623
    0x3180729040e090309030d02062205010f020a0906140403080403060b28050312031302010f0e19180903021f0b2812240e1510081908160f 60
    0x2400c545170303013018003019036012401d0004081d0340c104030005402e0004801c030407580390f621100845043c80703000d40244042c00c00d0700030115598034821a00500c7c00b1010700500c0082050080b001c1508090340e0119130450380c20110545c20903046a607083c02815051050307540c00341240031400c29180212015090b0004200941d06105142005042c248041c511028420400030320070840c0b4148035801c0224420390900e000d00040320407110580d00919120026a008288000705ca00303407900b540e0f48207003660360684135000700c0e02440303406009642032000000c0042c2c21030545101b602100b0f804030b8110700c0390800080340c101181d50100b0f0500c0c1c0b0403901c00b9940704a1581e07080a00130038101c844c001d0312508404841209294a41444141e80c031610f0885183c41c4611140e0f401e10a40d01005c0002c0700e01091314499025001c10580c1e40c1410b54015000c40b02400b00050726000c001034505117902003803484800b071328040c1c841e00703215001820500c00c5c0d81100c000c00400104e40d00d140a03a020b00c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 979971115 1250 979969865 979969867
    0x9140102040f0801060503070527010e0f0c03060a09180614010e01080f0a0f021507050a0b0717220b1f0608060d0f05010f020d0203180729040e0903 65
    0x38001c0045918401c0307a02a000f5a45414002e001c07a490110b11141522019103501c0b102c040c0312070030201c8089148000504200c0310f0400456456041420940114400b40b0303144095259041200390501c4141ca0f11039109030100c01c100410100390f00048000361000d40441440300c1c4903254101600d0340e070140500869140001405980a51108280501a0003008003421001d5504503955200c50007000352051005240e0001190303142404e488005540313818240c1c40e0b408901e00159124214141102c0022071a00084c20076445000e4140d103030250922085555290034088001426417083d440449088003012080451945841da078024403106100385d404403805600c40e8410526a0005802c100b080014407440d690703025031182126402440c42801c0b54550b04e411401000d1078410290014004200e5000705020b43d8055440340c01c02880d001010001c0c09a00c07038843c40c25016841300e402100c154911241130f80c1080b00e10f01140707226000e00c5d003900ca031482a0040e4045503075208a1340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 979972365 1250 979971115 979971119
    0x6051804020928021306090503030a050c070306020c0a0209070e060d0b18041a07140405060a092102011205010806040b040c0e0f0a1406060417030409090308010503060f0126010914010204 82
    0x45d480c60024010310080c603013a40c80e41d00704000203841e0b200d00d0305448108000881d42e8426004240681d0b0001c65001c441195565250f59005865000516017070744282c02800000b5550340c020901003007021801480c040c80d100140084100a0440a249075080440000001c20880c1c003626202d0061707014040c618501e001100f900c5da06204c00406000401c1008101d00c15590090402c0d00c09440003100e21645401e5080700485008030103a011141150185070514070400400c040d44120318001e0b0b94084c166150043d42c40305603242889101550341c410030008012a04204103184c00612420894800a590320007e00d41c114090312040c91003100c140a00422036071511816071554804c5028884518005000070440c3c081c1d07200e490340900c041c19501c400c02d0014001c031806881024410880d0011605004145030700034000c0f18000d21a6901140b1032039055100d240c100c41000902e180a420761a080c41c103280340c816038107001503484500010002d130041c01c15051124640000503102c074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 979973615 1250 979972365 979972387
    0xd0f05120a0c0b0c120c0c01060b0c060a110c011103070e03150408030703290f030a050d05070f060c0c0b0a09020f060c15041101030605180402092802 66
    0x54908805095104010040040345a030840081189280c100603a030f03c10799902c1d0350103d001e00c1001c1401c0080c44000040042407402c0c9006800e19402d4040204855034841c0403410b554400d61010710a2540a407000a04214403600315600c50034004038040d090040344250542502e0085076400007002001c400c010304964448a41c00c4003580440051000d0300401c1c4101203c4180900b0181100d00c000002501071070003a0001e0404140010150584e041ca0546884c1c48900054800788a5444a03084800601e400292301c0402504040030b0600304002d0070b026102940001c034111070300e00e85c2100c4d20003c52002d10560f900c150043d21501c5840c81c940c51328620030b09004060f0904940360070795281c0580c0766600c403030f08209015100d183e80c803458a00540c2c070301000002e04849000310001000200084034881044d41c81080e00d01b88a40d07a122001c02801100452a124050920341b0001d400b604e04541010381054215031801d000d02415201f083c00740b80c052144503051500001d01c44644 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 979974865 1250 979973615 979973623
    0x2102011205010e04030332060a151d030c0a0806041505091009020607020907090e25030f0b090a020711061905030411100f02060603010c1e030b0d0f05 66
    0x103100018010003681d810100200c8422101030006010590b4602d0451a2004031282c0c0d81e01e03404401280700842100544103001111085800b907019a00400f00040c144040d00c56502c013400c4141c8030185400000280210f4000711441955410f1081441e91000f9448040448019080355009000c035072500f030030010807080800300d0003280c0619060030020102c40110301000202c5144401041895050000412a014a803c069444100c0070107201e01c40d9080b031400d20464110048040759075540200d0340380c004030364042004841c0740a10f00d00901e64881c0d44202194040340e41c001810761200700100e024013200710b400030030140c0d0000d41c11007401840c000a01189804441040c44d02c80c5102003c0740e006a030000030018498080040703030820009900040c0344100180c0350790180c007054140100790024411050001d8000c800110302141011300800780d81e009151250450403100b0f0341c001c041c0050b02e40300d40003010790f41d01c0322a00e00d41d03a212072001132902501981312202081d041803824 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 979976115 1250 979974865 979974887
    0x80403030f030e0d021002160b070206010e07020c0d02010c0201050c0d020601050411180135061c031709010f06030f17030114060f040b07050d02011104060909020a020106210201 78
    0xa0f070b0303204040386a0107581c0055000080b08404102603140c101d072400d0005035130b500140003803281c065441004101540006c0d401d04845203001c40e0440394030303035100c16610b40300e114203100d4110711240c003000f01650054003002d40c00351040c5405864a10b403c2e803080c0c03c001c600b0681c04010380002c4010082807070030b0b0041c02000424a9031442c580401c3c1540d01c5007c10715500d0040c1407207490070f50110841e080400100c111040c1c4120700000c0c5076800400b0001d800c00716480340c40340444850070b0a5410101c85450070140e4103886203400380151080051b00036600828480c0d0369900d50306100400c83d014080c580c001c600c00c80104000741d48502c1e20840030717001030000702e00b01c0000707000402080e2945071702060848003d650030b07951b0f041055445030140c8959002706c82403032000203149080040002d800d0301c0c2c05010394020400c0c6403426002c242c00d8880d61240f900006c03250102849000340540c0103046440c218000000d240b1740d1241c4007101307040f42ca850401c86031031303c10603201956002101901 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 979977365 1250 979976115 979976141
    0x503060108010c050d09020301110f1e04060c06090c17060a1112131109150a05100c020625080c0f0303070f05090d060515181021080403030f03 63
    0x1100403e900d200030010f01907015850719242d110b81c180c2c01591000c0d0301c188800d0503020325450369002d010280c030319554404080300e129034a40e4401d1102140d007400544050765450f0355034080d03680701e60303c8200c00b80044402c00c5c0c444034030746040016400209a0ba0003c4009021301030150342c5000282070007159040e10600844003400c0044550800c01407580030f5111580f0100c0ca054200c40741080c59103c3c450081c1603402c01c00318400e00c841455a00b00c071810703945003101d4010449440310144040a00301340880004525136074071b094010b19117040a031100741c005410301e200c43c0e1070041a00d104100e0180c0142d503c10b0340015042083c001c140144800085a103004500d9805c1c026002003826210380c0220041100106801e002070390340041e2003080f150030220030b1020382440340000c0c020480520010f80700b1a42070141180404070f03680d105101381082050959075a1030001900300d44100071501025000d803816040c40001c2050000d08040e600036a1400c80d00c42100c1d0018003102c2c000c1c0f94a00d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 979978615 1250 979977365 979977371
    0x10629030106090512121b010b041a040209060717130e040809060c0f01110a030606090e010e060a080109050a06050609130809041e02121008070e061f09050306010801 73
    0x300c0340c82d8000d15104200e9400761a061880b402800c03181d4200311b100e8110302d1410400080c0c0700b40480107090510390780b5590000030000c10350f8000400044580290025114008940e030342c11030303454590301a004100d00a0f080d14641080c41d40c40d918081c410b0b00c4401c500c2e0703001080420103490060008406441d2002c150442410680ca8000c00e5000f424003140c032400002a000b400e644d0300780040d0383c0d600340000003400f2420080401e00100c0d0410103c00340001e14140c0d00041042c45020400100c510703da540f0012039003040c2d00312281c000018040f0381c005a40c03040006820800340304c3c00300014001d40c00741c14613045519140080d0b400280156200d001c0c420107024509070140c00b6000680d41c80002a6903078074100d00450702420038090b448070203114100104801c8240c41e002080d2111050743c40c03901d941e035000c0494410320504c1c000c41c0720560011106105942d681116182c002c0300003004142d20300c4c1d0400e035009070325815643e56000a44030140422450504100079409814900028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 979979865 1250 979978615 979978619
    0x309071a1b1b04050c071b090e0309060304060b010309120302040f050a05031005040507080a05061509040317060d0623070e18100b1909090902090103081b0106290301 73
    0x66070580d000c2e00c080d148a181c2e200041115501090203d41c07a42e03910000b182c00482c0d00300c04841d03c3d98814420b403840a8101300c81d0300007007900401100c0012800170411030954480b903d4440041c400841858107150791500900b020807140c011024111009a130003507600c0e0709180c45856410841d91109008000a02d02800780d80d40100d101d402c440341510001400b540c4a0914a18010499000413114080c0d009030750244070012036010f11074442207034503401c421001d0b010300c010440221009000a040c000c0c0200c0d5404031a0306180e004900140020f1041c0d00a884a208a4545c108521240040882090481c03084507260075844150780c10a505030317100c000d0105d030800c2d0082d4140107049901300e0000d94000d403040184009400c1010321192114400700c9030903500c602e450300704400314001c814005a080c55070b02842000e00e50103460401c5603440e5642c0c80d0240e41000c2c1e2a80c035400514400d03880000d100344682c10080c04208908404070502000707115010001c04004424581c0401c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 979981115 1250 979979865 979979893
    0x423030606060301170c120a031b0203030406050304060e01320402061b0717010504020916020a0b0601110d050301050a0f0311120a0507060903030807020102070b0c0309071a1b 77
    0x5590464003c48160a17140b401d01c43c541d804c2c00d03081d404865000d080010701300c1c1020400601104000c2c880d172142c9400d071518204401419845040c000d40c0b60b40100b006102c410f10507005903411a1144001203603c1c5c680400c40c0703003034850901d44030b042c039005000021103140c6001070302c98200306038281c50036480c2002d4001c00d01e10b02c250001c1a070026500184c6001d001010841403009100c0c10030141c1d20342d0101c07601a400790005480030384c03007198800085400400d00b8800880e5020f080c2d00205405182a9190515000014603641c18400c16810030946c2480500803c200301100c2d0303880301d907258144003c01c02c061007140c00c04044124114010700004040b08a150150501100c03959611130101c101c441c90031754515801001c0c0d0207030f00400203034290060141c4055034820303240c00100d9680c080d0128200d02410102908890180008c600c0d0b6144100046820801000a0343d800707545030380540d9200b034000340c0c142503032440020700c20704004030300c46001200720f2108001e01884a032410b9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 979982365 1250 979981115 979981117
    0x3070209071b061104030c0e011d01060522170f1b010e1c0c03121b030c02010e0111011119181a12090114070201020324060f042303060606 61
    0x70b0080a0a82d00ca07002e004210b004410313280215804411592160b440b40e1041000c610203100d03919070b07081c0a81010001d005001503207030503601c4660307542d42000305c0350100356942d41c40680306507010034200c000450408104104c0700030716450300c001409a032a00c129400c0c030b03010350101c4100c0300b0300b90070280020036a4007030055000c0b03840842d40e100708118004070b140710304a02084010101e4002c50000802c1103c40c4100c10940c60213038a0b00f84418001d04000280303440000001400074684c1c85100c4010346c0200c0c4100050003061400300d202c0340c2c48075882800c4030b02004054425000104450482000040303030700000c00c03023078a0304a20782d2080552022110b034260040b400d0340350842466003c014240340c2510554628450a406107041c55800c2c0c82c020404916151001070440300021040c50050003108e009564400c007004d05284080d9a41048a2886d08240e912940400920b841100341c54040d0000c1c01e80190800103889100c0103202d00405c1c54030300035000740c1002e800c1185541da81d0b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 979983615 1250 979982365 979982417
    0x140d050403060504050c030607020a03030b01180905043e060a050403080d020c0106230f03100207030e030625080f010b09130504060506040e010e121308010501080307020907 76
    0xb0101103250780b00d910f400e078207003481106941d404d441440200581a42d000403141d00701070003900d04101c03810402c070045604403550702c00c10f41190a646000c0110000340ea02c001c0c7e0160060030300d01c0980801c008040c00000c80f5901b055850b544a801c107403c1c0c02000501c000c0d141e44100d4000745414520f18018200b0f000c0c61001900310300000c61100300c0c4401a804649004c4201002046999215004036491894003c07041e41c0b003c21142c1c40c550036041000700c1e4018010024020b03c060131044100300083c3d803211308120304100d840f0901c2000783d2410000d06000c3ea408880c251001c2100043c403010000701c074654071040041c1d4005005424030309507241410740e60b480041d240c0d950010400b0442049080d20709250483c034040401c804d12040340e100f503010307900448044c005100d081c41380c103080e030300100d425881c60b41180c042c20300181070344002454144940843e0200c159620701380b403400c40c0d0099120407407603080050414210f103404030803650300c0304884c182501d81041d91002ca0002c10011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 979984865 1250 979983615 979983623
    0x1302040f0f0312030e150907060915020a081809090d02011b08071409090a060e1003050304091a10080108160602060402100320041d06010f03020d1b020604140d050403 73
    0x41d06000e62140c500b1b011069440808040440e00d9040c402c03d600d0b6528620300c165000501049800700702c0c0c60204d01c000c0340c1110740754000c3c03c04a0712903d604003160310101014086401945401000b41c8910010903c5561601c000c1c100c1045200406802d480d24100c840c1c40c0e221248224032055a0000e4080307070052524940700c2000243d0165200003071107031450284d8442c0000d020800c07a83d440360004e0045d24040e6240200030345800030860034400041c000240250070605c01403002c0304542d0b212468469074068129001000000402c0358140c80c03591000001d4000c20044c04943c40410182c8016041d2104c0201100c1c902a0021349448010380001d20900c901d0404192440c0329410295a560f034070518244a108070107000e1240b175100b032181889200300703203000561391029420350341e200c1d60301a11100003024040c40c0440c02035200d0040088895928404c20b40a034182c20060f00d41e000440d0003d0060b802c0c0303420004810f255050986d075203075000300018207441d079000341a00d04907540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 979986115 1250 979984865 979984871
    0x509010b070203070515070303060602070f090506060403020a06050c071215020d0b0603070f0810030b061207030506150f030c1e0102011b170c03010b16030507021302040f0f031203 79
    0x7061001034101000c0d940403035400490301c03902c0e009200490340104100b900c2a101000059a42c68081c0e8882445100d0803204c0e9200f14020022420700d038010f10382c0100010a214a413545039030016419448503004200060030120307041070351101c01c000400c0079054803900a1303103201132503480ca24507943d40c2045100c10303900469002407400c8175400c5407801503001050503840e480c0c010401006880d0030f80d007200003e411700c004140a000e071440c02d01d0980780c0042844450340d645005103c0f541500c01490038107803041010000c00300380148480e9020304140c0402c11750325081d0700c017001050100210500c0c80382d000248000d00d03075a120301c40c842c110002003205070032159047d40140e00600240304081c081000d00c560800300e637a030007503403030b40c805003c06080304181c1c50b03440c1c00380b185000074000e80030491400c020808002510890950f456482880c00381d10380b850981c00320300c0c0350360a501c143c28444e40101d424800030b050340100401410740e120307a0040c40c1d0f280d40c40d403824012801c201e400a0581d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 979987365 1250 979986115 979986127
    0x18120212160f031814100c0b181e0d03050a0c0f1d13020405030d0c1a10090212061c03051b0c060f030a0606080c1918090f0e070509010b 60
    0x400f664071000c0441e031321864191001d5035503144000c03641002038502d1140c1c00004802c60300c01e004915280425410140b0016070380e0b140d8844022641440d80503440c1880b56040210f809040700710b2001440e0800300c0a1300103400000c3c0040c05441010700031014450038081d98606195001c2500198407104d0300e030801d01254480d040102e0320007a00d40c001d03041681d60503803100c03540103500104201c4070140c0c00c44d0304002c80220211101c1c064200c0007030050503900d4444004241cad015031990400103514003092003e9031010742c20304a80c09040c00e41c80d490507020400815140c02c03910035410074a02800c0d80645402590028000d00c1405807103203280c8499996441d03030f400200405207003a080645000c0d81c440034038084d90280c1c1c008403144000541040b0000c0b0fa0f0390301c07603880180941b810010460803e811a1804508130703034007090450030071000c114110501c2c080307920f8507402803100c0b940c0000e402c3d040221250a40d64881c914007142da001e440104520f49130343e038500d4119118044082d403541 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 979988615 1250 979987365 979987367
    0x30c06070c200a090c02060f0a050405071202041b020f0c040c140d1508150a0924090c0f030b160c020d050715030501080d0f08150418120212160f03 65
    0x180c20b4000c4c03080349203860598000f10b900051001d01921004042c503881d56580d40b02c44042d110100d900510781e42004200300040780d074900071411020b2000b4004100030310b941480c1885600050034100044c0e00180140c42d4000c2c050100c007159480c10380f401e03c0229021000a0042025241078050354000010b84200d800c0c1e0603480648600c80c1d070f8100c04d034241e689020440c0d40c1c1031030b19050b0016000c0100450180921840344000860f070001150f05140482d6881c0107803001c00c0314107140041c1d1218004400180201c0b4141c0190482030322030b401143c10760805c248040001800507024036401a50b420045400440c503807109541100c511450b0103451400314103140b40c580c42030b18030400b43c110001c00690035030011416510b05004841d81c51b2150b940460349a0402c80200700891400780204071201142081d404c000320025002041c02080c2e10041d4148449a18040e00c0701912103c4054449905112083c43d02003d6406541042c1c5454600c02c82e220760040000c01007403000450344205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 979989865 1250 979988615 979988629
    0x11404030609060b2d0904060912210b03121e0c01021801020105040309061d0a0305060402010f0f0e01080403090b0c1006210809041d030c06070c20 65
    0x5503601440078800341c46149807a5028001296040d841240c00400c10405d00e801c00c1c3c065140307061103055008001c1c0410042c132146040c0a00140e5039591103503000808251007044515402102e651040c29104050390704242104440e08000741c0c440c20702c203520320300e0f540000d0b9403013100c2c41e440b510a54544c04101b01d00d08158954082110403000850350605418040d030191401c81400c500302424610b501004a080340c0e8206c500034007048500409000c2103114442c54542c0b25040b242c980851040140000d2501446904c11503d592140c4108030465a02010300c0324012060309103550075058a030800f50000c03c5040440c1d0410011800003410305110b5965131004180388130020780d803820348220064407000340a00e4130041c1405c0c42c00c001017008444100542450820750b0b281c41e40750f200d41c0c481d03400e60b01c8050a5a840364591403000903110070001d0004041e0a0b080c0210b68031a03103a1800317410901c000b401001440503a00c42c0c040812a20300420480d5200c01702d0801030b9002820014040f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 979991115 1250 979989865 979989869
    0x151809150a0608100e16030f0f09060501050f0a06020607140904060b07050f0714040207020a0b0406051306030c12021605060c070c120503191202030a060306050601140306011404 78
    0x400122203200164040e080200300307000e0b40b0369130480ca094a032070704d4001007042020b4403148000d812403050040c1040c8282c0c880401c00048000120350505120f09000a0b50712112003540c005558100400c12803a1800b1520700170b1600f030f16406410f078600301c4040d40b142401041c2c0406c3c411019440341d2000c45110460f8680980213100f00807032512402e1042c2a50041c000071142e40c0300705c055480c02098005240e0f02103a41001c0c0740f000001030701e010b00c0083e4002000c100d0304043c21503000700d042c2072010b01a002410315039503950341352048560b854075007a1003507000c402410300d04240d8a21450340001701c40f0030b0100b6407a02596499641429840e42e0b072407104094401e02a82081c03051380b65203034008080032406200c080720040d4407101000c0e00103000c035100408550040200300c803290108001709140402170309040341d10011190049003070743d204032507a04200b50390711428010051103205e05500541301f0310300520b14895034008428140303c00340029040c040c40070351703d4500703031134200c01c642c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 979992365 1250 979991115 979991119
    0xa03030c15091b1401030627020408061323070506032a0d140c0a110313030507170d2c15040602070e070f031e020705060615180915 58
    0x300120b510540c85940c80c0c058041c0f1640780948200c1d030055507110b1f000355019130710b90b40c2c110441009030403d00745c92541d0601081d00010f03020300001072040010b1001174031a152141046104510340d144c00ba001c4941400c00300c0f1111190030103940c5003807000600354155541038510035941d48070512410304c42410078040800c084074010001d00a950750a0140c400c440901c0e005014281400000015100d401c640429002405002c54118a407045e00c014980040f480d0076280f4129244440220181a40c1c1098030140e000c80410040803180f65910495118008007420920b8009200213042d50043c1d48006403561541c0c04c2040350424030f041500340403000a040c80c85522564090385001e0300603200d0b072000760059040c002030008004038000e104081d155203040d0000350700101a001054104a2003d6003001403032a250824030720b100030f110007801400205100d2070440c0c2081403010032542002840c4a0501550f0401403160000d402c13100342c122205940380d0f0b1004c010152051039004029 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 979993615 1250 979992365 979992383
    0x9060807140d060f090e060c0306060c060408041805010819020f03190b01081f05040609080703080a060609141309080f03010305060f131e021504060e0a03030c1509 72
    0x82500c20568801c00c01c45140550012400ea543c4018904840e541e900151968000c0e000103400c448c40c140007103030300c154020100c0d070520b0a100c60251500c60111001c48162030002014442c402e07900a01090783c407641c042c107120303560401c0e07103003a05d0315a03029400a00b21082c864000031541c0f00110398004000150454240304481031051526450381c0d081526602051000030580700400305d10001c1e05485400c1002181c40c1c0c1040150003400c00a0043d1042d6603984070890000c2c0c405002041294001d6076414400e0030591a1182100c0321a07204101388031b8000000c200c030046452605190303600441d0361402a142600d804070150140c180000d00b10200014030310600815100650305a13801007089800d07540d0b5440b07038440814802c1d103001701b03401c06116000000a118a58090419881c2504002d00d050b503640483d2111071848150b049101007c6803d121295100c060b420b0049000ca60035010326103140c030007501804074020b020300b248285051740605101181c200c5480d00d548107001c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 979994865 1250 979993615 979993627
    0x3020f010c090603111306081806040b09011406011e02010e120406080106021912200d0215012303120d0c080a0209030601060809010f09230d0906080714 67
    0x2d001401a000d540d011a02d48160322482c405d0310002e031115100c0c4054401141400d10300143c41c018001410518843d900655050000105000c454000c0c2d109205060081c00d20400302400c2d100c0028102030401710039402c00c115030f1391000741c01c18200303000c100c408201560300e68101d0250454048805031445400000300700d4904401c001e2045500c45c0d40c401e1043d980b50002280c07a50255a07007941d032038a000c1001310208030002c00b0010840d807030b4141b10102e4101107a080c11401c400710b03850b51181c0c1010101c1100203030140140303001809100800d4007a981000310444101d4011580c0000c0c00e8038694010105840420800000ca00c50b011807a031130304480a0500081c010039924900022465004904401c950b4025500d65800081c054040303a8201041110710500040240780031307640b07415401000d007010344141c00f1624060551504c0b6a410f421102000a031007100ea8150703580031513510b0311000c1c1d025040c01c094940502e0710b4400750f00c68000440b0203901c15907003010300100018074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 979996115 1250 979994865 979994867
    0x50f030a0813080a0f02040c11061621140c210601030603050a050319110c192304050c090603010603110f1912020918061201020403080406020f010504170703020f010c 73
    0x400c400c1b80700301c2e03050203598a00d00c02119402c014410104a0340e1240c00410b030800094040241c5e01001803409440000381079880843c0024a54a80310402d560b80c900148120340e08850164001207204546240942d8140304602001d14a4800107460001e00e010030101c0c1c0c400c0c1c002c01c0055411100b25007540d80c050808640b04d0740071642140c071404006ca00c00640500804086204510040290540c031490704140314400030b1402a4040b2482c1c00880810000300d01c0d00031094120741440c0480c00300d03448200303000882d60082d000b030403810002d00800210f0741d910021281580c140e071502181da020183c0c1075030300d43e0107803030950010f200b00031a0010100c0e80c01c0c3e4038003060b01126913504501c1c60140500310102c0c0700380c0c91003a8120181e49400e070101c2c10f40e00c03802501f001c0c02420001005254a1406089810580040350906c0b40003900300100c81d4108291110241250020000c50401c1d0f510294071401c0d1680145c0e5000b004911722040c18000e02c00c0f40b4001050704001d0103a1609000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 979997365 1250 979996115 979996133
    0xd020d0e0d08131211011b09051c08031807030206030403050307081506180307080f0c0a17030d050601031d0d021002120105060310030c0b1201050f030a0813080a 71
    0x84410014072a00b00040d200c8030918030f031030203c03078000c3c044000c640700345042202c00c80090003081c400d40d0f49074029802c12054800a03044000c0c1203684101c009814003041201400d8079007001010760721110042400b0070044c80450b90070078401084007420b0200c0c01a42d60811035a80c0c0f020b90b01c81804000c1006240d04507008502c90680340c0c0d07410943c0d6581e41140e24210035481c1c0101d0300b12000f4420b502d120700e203850301c00d010100010304942c80c0580d2130948610f00065102045d030b0507002940f41e40ca035414014094005480d00c091008080c1d145c00401541d03902070081010702080c3c1300c0e40420342c0740e40a40c3c2b100d036480c0d1481d01d01030410080301150550720440c80710024014429058800149a00c5100340c82c411a1124002c1005901c0d00c41081580d402c080c1010f50346480286000001910700c82d08200102039100321207440310122a6040c0075040140d2141c3d010742410b94089069540121308038180541c0104441c1d11440d452000e05900700554000540900c91403214600b0b101004c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 979998615 1250 979997365 979997383
    0x30c070c05030a030e01030b010216090606021504053d051015090509070509030f100605181b090409060519021908040f080d05061207050a0306020d020d0e 68
    0x6144640303550365034014960b81c1e0051880103400070704207070385a00541d803082d080010300c060144101e500302d074001000d100302200603034080e042c01d130760341c920400003d5014001c49000485d01c86840c4903a260648901f81c5171606510744288c0d07982003400c0780481c0c0035039200740950192442c3c89054030307109048441000306425079500c2d10040360142c0000c0e400b00035282c80756148a00d41e440c030b50020311b0178040c8054040050040401d222040c454040503032000c120001d245400f00c001080c522040b529a076040712074903007103107006030007410407004a001100041d40d00001d00c4400388299402c039408000841c0603098100780d0250030111100b06105460700a540240d1848080c15121520900500d049105000ca1141b481c0641c050b071440b000d005039140c0f54854000e0790695501446651241e80320760113410021700051303a403414400c25040262450121200c004018038441e07041c00d00054a80d102888020400e98000811240407130380d680540344d43ca0700c0c10000b4040c0c000410a200d480302042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 979999865 1250 979998615 979998623
    0x81603020a11100e0f06040b0c0a120f051902071503060305060a06050a060f050d1506020f0601210309030501091101141905070305090d11031203162102030c07 70
    0x11808448510301003404180a46a6407900e540803c194001e01034003c1090181a03440306c01480000f0340d072001900205508050300000e40303c081c0061500c0c0c2002e00002c1c1c0c036101002010507021070f4580c0c100086a00400002e003e90402145001c4201e00d0641141c0ac040786541041007180c200c207805410210507a4425403d44420f50b032a600c80104032400d0b84950380e40080c003c0c00c2001154040d180185480c42d092070840e01c0c003100c2d01d08050031b44e01040b20540782c241c2542020031245505014008482c060306006d00300c19450540900780d04903800343d0040d400021300802000305402502400002c45d4010020300a018403030038000b0002d48410741050200d082403080c4003206400f1000c40d07421018803085125401120401116a500606000c40a100d000c0000c1000c0c2d6a502c07150028041c42100c52410440200d811301d410003a452a03e00703034100c0305006100d807140c4071003a00c0c100201c003450320a00c43c0d000000342080e03245507464450319140c8000207005920f11650001d002c802d0103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 980001115 1250 979999865 979999883
    0x10b0a0b0d1d070302040c0903080301030b071b020a030b130204050907090501050d03080a0c14070b070216060c1412030c031509070c0204050a11040824010302030d0804081603020a 79
    0xa03007960750403100e402c4828100c1c903045000e0900043c41d080c2d00200c40b079209490204a129266555008164000e8105403010000d0604010500d58030524007a02d02c010300b00038503038001d61035000c0342c0e0004843c00018034100c01400051041d03140d140b8048a40303900140103120f182800348c01c20f41c5400c142d005480815040400106072420101c410200180d41070343c916006648500d403400052101c58100c1c1e040004c404641c66003117850300c0103003103824020008000a800c15140280ca8030030b800d0a482c6c0003920006080003265000b20342c0c140c400b45c101040118071a0007400072070604503842d2203422160070100512006443d2003004d14401c06d19030030150700420000302000984a011124600000c6001c150240103060907041582c003d140703068003084001c203181b4150101d40054118010390351011400d030044880380e80c042c18400c4003050b0800704550442d00400e80362503058654105005078007001c5403c208030a81100c0c0c034107179081a265044846850029107030080d14209079040c0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 980002365 1250 980001115 980001131
    0x1230c03070c1d04030203042115150f0f03030c0203150f01032a230a080a02040b040606201903080f0f070207260106060507050f030702010806040e010b0a0b0d 70
    0x80c0c030480c244c1c007498264004506281c03901d1202200d41410107800d90003600342900c15800901c10f0500360350328461501011401d90303203460600b40142c00383c0e40501604200150f0420140c42000900c40039207801d460481c621039211300120789405803645904010f070841d4001c01030b0f0300e1034000901d0f045e42d1041d0300d481107840000303018000350001001000c41e1004030340340400038501510007541d242c0380c5502404500c038511074000340b074951499004080c190030090320201113151074441c200e42250129003c101d01d43c101000100019040ca031082e08084c5001a680402c000c1009185441c1905611a80340340030149001841000f05884915596207420003240398480301b00710051140441d41d00910b1000c2c607046e0301d0941c40b4045100e00ca8210954030909034108001e020f140701501050b00c802c0d40e207160605e00f442c54445020610019034100b80114401070ba4008401c0707400a004860100c0d8804086020900400703d8402896025a09100c005142d602610142225000101d410402d2007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 980003615 1250 980002365 980002409
    0xa0311010209030303010504091e150606050f0a140d2a02060424060f0b0315010516110f090a09030206011706040803040c17030403050105060f01230c03070c 69
    0x2c040c2da4010740c1c3c1600188014005c6003482d51080e200c90f400f80e820003c41d04003214190880c206590301c00e944242d64041401c5400d8004d008203001041e0b580341c90740c40c11202000c9051980120080c410401a41145080b0010032403000c2e01e920240c20039042151101c41c81d010040004184c92407144004030070b10b07480c2c6090022400d1445950000649401440f922076040030404015045201082e0340c0d410118030210542c00076000f500c1c044844035a41c1c18002c641c0030100c498549903a0400008009040148006003500384095504c042c07202d14900002e00020701c250000000542c1145215040003030346141c54002d41c560500039001e41382c207030342c035041004140500415084803581c00413000c6000111440300640d8054000c202c0410101d07104c00e04124010501845644283d00100b42402030040a1040c0da8000310103c0742007409880802c0043d100c09034a000020b045c000d503250042c0c000000c4021119051200300c192551104240f4120f100051035004460402082003d060410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 980004865 1250 980003615 980003617
    0x2130207110402040e070804061d010b0f1f111e0c120607020703031101060806070c0c090216110d080a170a02030105060f0706090503030c0d050f01050105090f0a030b04050a03110102 80
    0x600e61782c10450625a6940505941ea030700c0103441240c080d5980c0004c0300210418200d0000c0001800b0300100f543c443c4a01000f6211500440061007507070b51b83d4402100b4030041e501e11505101e43d040800303403d008450102c0c10140035544002120449044605a0700f901150071074100c2c10031101080001001051540d9900c021181e050160380001800d2001c07a010700a004a441c408200100b8136a03128003a05040100650f12500440c031410040340030016040010005003104100450405201c0c29002c451103450444c09804500700000e1103400c0c2e01c6815110100c03079040b814480c1d45445840004200c205940c400e11080741181c40882e19543c600d0088070b04a03880109418104104041907440340c0c0e004840848550381c1d1140b80f000007030360500c0603501c680b0820380d0141e1524074150342c8100f6079500511018007501c1400040c0034070b81e080400d45001803420b41d58103504590400c01702704030003210b80010340706041100801040000004500c40e1a40c4a82c0d210032181e0000100e190907 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 980006115 1250 980004865 980004869
    0xc0f0201060f09091407030507030209070e0a0506030603030c1203220c060e060424080603060702060c0f13120218070c0204050a0908190807140f0a0504030213020711040204 76
    0x2440d0000d24041103c04080e402c00c8031218080d1464007210700c41038a84628010342a030086236a0742103003800300150f2801c2006158054880c0c2041c50740100a4000038003101d0141c003038148900800b001041c4103413010020b4035544482041100c101c00400f40c0c0c0102290021a511000040410035030140130016104005d88903a10020000c1070a040c9036040c0d9804000c1e0102c15003001050000241d07404ca050003041d076020500441031004000d50740000c10300b1a00424260080c3d0192041c800d43d542d000480f154024a1071003036507101e080300100e5010600c9110100d03210512040780218001800004e03900c400ea10803640900001c5a503190101e280c0000c45105004ca1800b034480c0e409800c01d80c104541c403405108000900c018103582e081c0b140c1c0c100a80e0f400c0d41032146001c0c0081c07140c004002c982c1180440c148460b94504e500d401803454030031081d04594154001c582400203d0240301590081e5a0003041c0c00384035040200c80d44001e400041042d9986904081e480409041501c220f41c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 980007365 1250 980006115 980006129
    0x30207050d0201050c0312010303031407022109040608031b0607020d0c020f04090b060f010e13150f12030e060a0504051e0909030d060e150d080c0a03030c0f020106 72
    0x2a1040c6040308121501680306016030511800308440e11580380148001c1044a038404070758280c0c1d505500f0010210303040b090030701c0c0401c0084c0b4107008490b40c0009061114030580d0881c901e81101c04044180305008281e1600e030010f040030001b1034140c0011001d804402d008907051580e088850400c9540c410007a1039910150f08003212109400d071103182400050b41c00a8a1004907084003030102e170440d40803140994010184109000c414604a4810007090409183c12100c590341840004c0215190314a013034031b803a90b1844038040c074010b00041c06004002504400b940a5036401d069509500705000460000700901100c00e0140780c04425100341e280d40d40c1d41c0d0743c2428285010700c591003203214000102e400f4110315400c419614101e0380e030702c2190004003554035074008141c0102518441d40050203000784000401102e1240001d8015200e5800c68400c0000011801e25400c18451200700d950a802050f80301003d060f0107030444005c0e9685581c44090a19419804900700c68890103943d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 980008615 1250 980007365 980007373
    0x3090909011b181a09100206010b0301180917030f0721050c0d06060e01020c03010513021c050607031401050d02031b011404080c15040e0c0d09020d2604030302 70
    0x7011911034244440121610070382444410385654010004680c0740c8090410344c0800074011109081900840030781c2c0955000070542d079411b08031000141e0105000e60f85c0c41444151211070f0b4141e00340c100c62091508201030745c07880301c0740c1d24660ba0154001c4034138181c07001e1114082072065108a5481601c44440442605180720070300703220014000c060305403a440c10007032000d0a08200f03244a0040140fa070740c4c8a180014000c04006403c0580705403407144070341d142c40704104005c1a031a4640404950444d14040d950603283d80036007007980e4500380a09988203400030800040c0d010b0384840c256600e054080341c02030b0313a21030402030071741886c22000b0b40517005845001c20360148901800c509160505003503a0b4840900901d90f9540c000b903020302401c0d4415018001c007810b00c0d078840c500000016400601d81802c1c00c4c5038107175500c40507014030002540094580c24081055101030100d513401003030000d0803c0c0e6824501c1004d140d07000301c0054038080368a181401d01a0700202c9003141c2d85038020b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 980009865 1250 980008615 980008661
    0xd050a200406180e150103060603020a050d0905071d150418032d030609140121050327010908030316030515030a08130801090b160306030210020309090901 68
    0x12103080030303607010f980c010341903421020503100749507198544038103900c6842c0420392010200040656030540c1c4a08203251042100206040c1d06c482129008082d01d500819148001c1c5413a910380b8110354080c0040c105808880c0360b08001100032540611070040c0082e10005a51017000111080490200d0300c05404801c958000390250804141c1c050b1040131036600c0c880881c00d03580380e03105800c50746000607035100424058031410b03100c1c080c10003100c4030380184c940d81001c05041440241d42407030027805122035525000c22104004507070400031082e005d511408034001c001002d205264032410302040400b140032640300c0d8000103491040c2082e400c159855200404190001c0c1005000320001810f034804a600607103040012a2945108003201d9580300c5045a040e0105000c0c2d0300800700c203904100499011a01c004445a00308072b0b00c0140203138144038882c05500910041e40003c0d003105185c5d981c510b0640d008000381c902c9510644194405a686044060888595850071640c3d03c000303001c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 980011115 1250 980009865 980009867
    0xf0f070e0114031608010e011b092607090f0e010506012307020303180108091504081c0e0102030a0f0209060d0207020d0c080120270301060306020d050a200406 70
    0xb41c21001d0700043c0c01c0e18603903d10346840d262a5016500811546d80d1141c00828900d4400d1080c0c4c510507403075003c514501a44000010003032a094412065200040100c2c4140354100814411004490302d08840c00e09581d0050700010b8600c0e0030a1005d001e01d0509aa81010410b001c1c0de032003400140d41c0d103940b00840900302e2101e0f15000700d0702c144c0c8081c2440b10314010384080000703142200781d403142540700180e10b0740010509003000740401d8140d0070919030541d5100712500481d0304245e100e6412070b12441e202524029104a01150044403402c00d00300c049040b00c190300444c080c201c0e042091124031496044002644a0881410f800000801280f11544030036400b0781005c41c4020280c400b403e000c1d0716100c514011540103484540d646403201c50306074100800d030003200c07080c1c908000d00b44110742c0f40d000c42226148465240300c060400d100d0460303644c20350090001d0b42d0721940464540614020750f5009010488094510398502075210503625403591101c400c110135180400d1500b824500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 980012365 1250 980011115 980011139
    0x14060f071107050a12060605061908070c050a0b0103030f09030f0204090804031703091b060d0c12020f0910030b0619231804020301080a030509030703140f0f070e01 72
    0x11010341c07501800074081010364550200c0d130014141d042a0b1030342081c1c181042000c0381c0da550705c410f10910041018802042d8280303603100d0400040e08244070717071759078100c010f5412480310b0320b00074000e00803010060104078222000d18107807802959000e00303100d02010140c4040725036000140600f03401481d6100103140541182024034414255603080c1583c0c0d90740c2441e140e5900701130101c40c55020082244405003000b00010030011048001c842d90000700100f0f150744140c001c0000e84c03d86856148242c01e0046040141481c9ca58004554500d00b01c28041c900c0d40246810310310601141c851000c20754403a00680c2044540140b000380340c5044003c07115001c100c95540704007409042045031012012810f0040134032109007842036921080c443c00f540700b0740d0561451621a074410310044c03241c0d4a0000d507085285a0504016a42c0c600b8a000603113488051740c00103014122004421301202c5010032800044003405c01190f1240003980541070b2601040d005880c0e0859030380e8010410003040c0b007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 980013615 1250 980012365 980012387
    0x1d120702150405030a05030a1211040b130e07050a021506010926030403061a0108040b01090c0c0b011212030203161409040609020a090f030b040803190c0c14060f07 72
    0x419903280c10f0f034407400300e82041c100c0c01045d82c00780c0000c50f0700354407650058202600e000350003104000c51481c0f095030030103501403400f072014502c00101d81c01b10111420031509000c0c20200c401c1440305e16005900600c0b80e848110800d005025408225107989511644039000f800d050710344000c11828550072990440480300c0c54202085c41c01e40005448205000820165024050100c1c685840c0540f100c0740b1454030203094100480b5008200c0403a56201216040d03480010000c0342d2a4611441240e40e011003040c05410040f03007130000280c105e40040c2c41e00e0403501c19030031001d00c011007a07410341c202d0004035149401e452000517484040c512403106c401440d03c0840c412400c0c140c90101240450b185038100d444104d80c00200b000c05e05401c4104007008001300000c80100908555410031284005000144209000b1021820300710118103200c0c10290b000504010460f42401c00801d4142070a00a0303801543c1e440040040340c8010503d24420340342c802c0e0703038881034135881400c69002c2104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 980014865 1250 980013615 980013649
    0x106090b030c0f011716090806061806010e040501090902240711060d020c1b190513020403020d0b040303050a060501020a0b07051c05010f0602070317091f02011d120702 74
    0x81301201c07028150704218074061000b034881c1c510036444184015007a511f594020781c01070b80c41841008480da54100c0d200c1c019140583c42300545880380f10040e070b9081d02144109a1190030a000401c40010550100140b18002c4615400c1900c012207024402002c1c000011140101004120301140e003203041000c08060181042d85403c0b9410302c43c00417600b001452240030f0700902c001041007850709007580410a000c0312003015204040d180b1446080e0726100301c5014402c0ca4050303c0b260203040c2d0580b4021034010b40f011b8007441c036502d0f105501c1d00c82101c00300c02003480d01000c500c0c451001d100322015104180c0042c440d000395500e9254200d000101070388200841040201e600c19050010404801811000030030b081d4101605545c0c102c04542140e000c640c490a800c0004c41c41d9500900189205400480d0b540c0f903020740820011203200340032040c01c84cc60388403207a0300c1da4158440400901c03029a42c410342900d401e03039281c41d9820041c0c800441203040c80f100d00035203404a080c4400ca245 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 980016115 1250 980014865 980014877
    0x213020c030d05151513030312020c0307081306170c311404140612010920130b0f060a02031905041508010503030304060e210c0106090b030c0f01 64
    0xb0108907034043e01d8007110542010803911080404908024441d0102120009255402c000064807100001800b0384005001c002c501c907420350f44482c00c1e81c11034402109040a50341d4038401800d240750558020140b04035400452840020001c0c0700e900355148451841291500e50b40301c9489181450300308110407002a9241c03561043c42c1c05114940c405a4401130080030407244c50184042c8000d211011014000c506054070f4041c500300600405038081d0b4219441203131100d40d90740d8980103082a0b00010a24402c0303584072403059007900c1020381107200c12180f180318903151808841c1640c1c0c00d9011260010b440030140600c0f4a4090050302c07910f40244101d03418604a07031040c1c0300c00b40c50600e5200214030005418040f075001c0300c0003041240c646003856002c84d4940b070046990792000400140c4440d81e81e05251045607002d00c003145001400400044e00202d5400708100b00b9404260030029542c6050310005040145004804800100502070b180100040d41441500040141c4e003504101c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 980017365 1250 980016115 980016127
    0x1b03020a03120b120717030c100e030c100b151303060f02091e15190e012c0109050301090b040825030f022802010f0e060705010e060c04030213020c03 66
    0x310142e40241030b848290051144e075107040d180342c610102c40e074000446c5800c200b0800c00c00303120020384c070030641e110003d0018940d2201c2c00c1c068114020788a1a10640c02a49036401c42c80c091508002480c1e001100e0741e66001c041d8803843d02d441c0c840e0030030303d42000603041c0003017010076070a502c8181a0450148054980b4207400001100301c0880b03600d244110f015101d050209003044602e5560314514502c1803071502508802518215080c6544442004550301348006281d11601e10600c4807170242c04003442544808100c0c018420701c90061600160b100203001030980350500400b060941c1002ca6002640c84944800c4800c2d4802141201d00001c556001c00c0201081000f1442e018040d0307482801c20203400000a007480526036400d504041d0507900383c03111428450030300702800e60900703100402c5400c00030b060780c034641181c0034140c3c01800031414800b8030906420010079848207509980c895035540e440201c2c280540c0c040a5080001c241c4030301400ca00b03a07030003403aa00842404a81c140343c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 980018615 1250 980017365 980017369
    0x90d0e010e1003020c071d0420040614030d030203280902090c030415090c05041e15050312120c07031715030115050618190e01061b03020a03120b 64
    0x242c1d465450703400294002910080000c0c10b0015001400308040d01c1d86d80c0140041c00c9100543c40a0400f40804090f0300d5100c1000e2000314030a0984034000d4018080b56a440c01e400b0304003104180d0003806405508450f8800920a1007264031491b29000d50700d103051142d8401c019a00790040011901d580e42d61a0400940d85070082d2a100c0c25030628a26500d141c5442c00c11081c0c0d0b042d225800001c0d003000c40c80000101c8401c1c02e1010b07100c040d240010004c4080d10700c030a1007015805000c580034a0541039410270b440b00300d0176105603501070741190f44811240786051850f101c0e04029908405030803022500070300c0f06000a2000500a00e001c2c0303481e003080f03903036800c00c60310030368000820103002028600b40781000e00418001c510042c01c0642c5280c80c0501091452003448404c1c003211200700301003150769444100e054610024020541c203050f88070911070f040b141d07007805640c006c0388446003071044032a0042d0380400caaa5241d40a05171110642e071b0700760350341070085602411503600c80e403080c0d03219 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 980019865 1250 980018615 980018629
    0x25050d0b180408032e1a2803111242040f021218160b0c010e0f0703060f1b090608130308010b030a2301080c0108090d0e010e 55
    0x160f40142109541ea081070b00c80100094828081d010111585070b0700c004050245948440440b104d00c0514401d025005582180e81d105e40c11f07180c3c1121481b83c0b044181c00b9000112032010702c045850811030321420301080402401103a40420910ba500e50020759188401072811400d03801d10f802c41c480084030003050840041c040c1940c0c811140e42480d042c200340c80d20f400703010000d80c1210b0003103142c00340b03910f00742c0b0002200030203010070b10742503001c22003040c00f04002c01c1c0411201d402c00206c40341d031034903007080040d8401005103070250b081c4107180c018a000401c440401000140c01428201c4c074550720031015100700d05d00c2c46540c56407001803070f5804040320080a8019000e68034072210505004001d0100302028101d10241c00680c4080740c0000e401944560650351034004243d141d0399680401c402402603800e0116003170000070342c900000e1021840315810788490b901918861400607004644e0395004541007030507944103144c144510ba025403e07200e05110189002502005044086114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 980021115 1250 980019865 980019871
    0x10c050c040c031503056901020d050615030f0903091e01030509010605030a020f030a080703050714010c050304030c0203010b0901080f01052d0c13090525050d0b18 72
    0x295422010b0748204252041e03202d9000038499160510061540b61400c5055940100b00c51021188200383c0d076401c11f203981e254a00608805a43d503a00442103040c250107904024101d010540c2080082109842d00c038080742c80e2640050103039400d41d07685180f00c1306402000f510048190000f045003034216241e0300303851810314600340c41c500001d0184000040071580300420314400c40e45424414459a50003043c480c80741c03501254088030304030750100040c0c113002c0711640040c0480c200141c0304c82055009800350640314050514000d0103881c0920190aa07081058250002403003080040c1c0043c0c010f40092040030700180000420031024030100f40d2968007078121001951003402100700c040c509001340c0307601c41503e40302d480501c00c101c003440d94030013880910b0745000140c000000b044d03074410314150b84002d8402003140b0811941d4640383c40080105903000e0200392141c04408185501c1250340e0b0720010303140d540c0c00d4686000d04071264020b058101103190b0006c4040d44000901683c0d041c1940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 980022365 1250 980021115 980021123
    0x4082b060302011d01090b070c08030307080115080402010c02013227090601050a111c030606030c0801030206131d0108070608010803030109020d0f020703021b010c050c040c031503 79
    0x301941980005481e04494030800202c020b03240381d5445842e68400000300c00c0750b903030040c6252180c069150044c0101002d4000c184144004000c100c0c2c915071248540e0b0407103054220031405a41e100c0c078221003980d81150040e01055a990048006510603041e6051a20812000c0c03540500a0004e00c64500880c46a2180d9900c0200e80c580107143d90a0403440e2541600348011032500c003004c007041480e000200313050306000000c02c2c040380040c09603c1c0000c0c13a40201d01a9007548150b0040ba07070648618414810019141c20008120903010344200a111001030b03c03103c055030f2940e405c120742c1303900c034102c20b9461008014001403162540d4080403030706201c1200c124910b40c141000300e8a003000c1075000c4010000184010004510040100c0c1d0660340040d0000d03036248042d401c000e0180003810307802d0a000f0710000d415000d1580c0494802403c00041c80c80c8511505100011501c0c80c07503814014200b0b4005400c0d002842c507103540900024000e9007000709149481c004c0340d005450041d40291 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 980023615 1250 980022365 980022371
    0x40207030f030e0d02070e04020117090f01050c030601021b1c0b0f0f010b070609051c051c06181a19030b0f0f01120510060603020a02121204082b 64
    0x7241505801041c0c0d40742d48841c0181825120044000d68424142c41000100d410217000314086d64801c1e4031540f6602e10f14640d01405040900c600c580d20001d1150414480d40f0700000305211340031682c12240642c5059005107502401d410203021540d46846500d94071400741d17551000c42d102450707081e408441c003410340d840031480e00284650b0340301d2005010b02100032000006200c107005410a942c0003a800400014143c4e940b441c210f03141201c0d82d00c1c801500c000701c1142000d03c0758004c0082040d50b848044001d10242c10020100503103034640a801d2502e8095001500720440d10381c008565041d40300759a80b10000360344046011840c0000130340f540280300400903c184428062500e800101103406080d8918140100580c152410f00503149214000c18032001802010001c41144100400f82080456901ea50150080d80504402c002502071003000c0310000c003004040e500320500107039005c10300d5500e83c1ea86e48095803140d081e044004100f0f80030352103607810720f10070110340007a13780d400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 980024865 1250 980023615 980023637
    0x62206050c070801020408120c07030b01270e060a020c0c040203180d0f1e0201020c060c04051e0a030605070903050a051f0509120903030c030c01050103030f02030307020c06030a0b04020703 83
    0x1c0d4107200c041d800400c0642c5c0100400c100380c0100145191405100414840c1c803503240c0039519040069540c0054080500c1d4000829000001350f80845003000800d015075920311040c00060540344200d40b000c04903080540040c0107407074190024000741c040c81c03094a002d42c41d40000035003244c00a07150103000d1200c0054400b107813241003008001d00e00d00c80c01d00c0f55840058180052007040e4400200b807030341c0d4403950a10407ca001350180d0303520034103c00a030b507454a440d000e010b40c00d030410f01c40d0070b00c500c3c25a2400c07500d0088a908035141c0c0e0102810410305c403429500e0303a8000d088040e24520030003420b03040000105109200808800e0705c00d00c0a016001c0c94120301c5071140c42690100c039203580c640014407411801c0007034400c880c0400301d07070800d4a54080100080c154002d6184088090000041400c2c101e041980402d06aa20030348450104c404505012607582c001100c801000d030b4000c000303641721441c1c4800590f50001e40d00b20086041d04003038000c1021ba0300801001c6022074102c8201c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 980026115 1250 980024865 980024887
    0x10b04030501060f0e040602090103142e0509150a0806240109060509010f23090901060201090525030210031a0f180a090203030f251106220605 63
    0x560f80041542880143c1158140401504030300380181c0010b00c5113034001070180301a40260800c814481050b05e0316031980c0b800c0c681c50710716040c20220201500c48901f002e40320101c0040444029150041c1c1031140303559448000a4211814500c0c1079809606c0314400682c40d00108103061241412012100d91041c080d002401c9020b41907858038188001c010042c000c183d4080181c03880c030102440c003580e2152000606036000445038000702846e80c400b00c01c110f04a904034009004904041e60380c0c0301c2c0c50ba641c107012401c030b80440a00400d66000002c1400c0c0310304a0441502d07070340007113124554440d070f170740e80c001030007011410b440c1e102191311031700300400141c4100b003808107281d001d6460041c101e840300d0004942c801c018078035051048441f404505800001e0784210400781d805002c990b0b480344041a1208541c01404824070140d11f840300000441401944003112254081110700c5e621422a04011154220382c810081c9009002d0502204003a0301e90410010f0941d915010b590b0f07400d100b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 980027365 1250 980026115 980026121
    0x1b0601050114092404062c0a0302060a091d01090e0d201006090506130605130c11100c021e030f0702060c060115170402030d1d0405010b04030501 64
    0x200640c103122040c0c2e111024494140116001010300310b4000c211075243e96003401550812041c82c50801501180106545400c209826461152400c0d4803203458890f040112603146545201c6400490403c010001030604501500c4044130034200400510307101d010362440b8001000e901500c426100004000d030901501c40d00a1202103040a00642d07001c2100140c81c000207201c100300440c001c0740403104040300034824070004080398002030240aa4607200e081c09440c0c20303a00c0602c2101d00300803801c3c1800c80361203250704496000e0b0540082e010f20103003030401410500241e100b48507052113801126501403240152103541e8135000540d2621840c00249030004581c0a2803081684016215182000106a44240303032440b640c0c41e6194810310200303000c4c3c0540051030701584107580c004038040e0301c2e11640c02680c0059a40320800079091840d4640042d9098801035095040f003880790000c1387c41100f03170302003072a55403000b51039a00340c4001050031107030264081041d246004c1828010080c080c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 980028615 1250 980027365 980027369
    0x305120304020f0409022b021513080f0d0c020a18062402031902070810062c0f0403050f0c10050705030424140c070c0906080a080d0b061b0601 63
    0xf443c2041081790a074040b403503114114011080d60b07694070102060440d44900345030400ea50150507003161070300c3c25400c6213007900680f100c080200d521210101d102e060018169039034106040c0248040000788038240c9050500e128141e81108500601040300c55907250800181c5000e0b15000400c01d241c6400d20100c02e05581100c002c00c0301c0e000b40743d110a64000251031699201c11072694200b04c0041e4264503000e090340c08030405008416045013070300126445001260b00024019240c608640070721901001e10a000681c5440080040340b800d80581140a030320502c20b090440c9080c002d2448480300e82c200901e4041c4640c40000aa41c403034180c0d000304d94200c00c403804c2c21400c5041aa4a080c80030400381928420740600a012000d400d140d0b401010303903019141280036490500562000483e40f04100603500c508005400103440280d501c545412908c114016000d2059940c1c0c0743c141d81e91028101d0b9010715111501180107036203060082c20300031007407115800014440c45295003440c50503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 980029865 1250 980028615 980028619
    0xe03040e161413090b0d17130f030b0f070c0c0b2101080a0f08090618100815120319080105090f01080604080322080a0201060b09060f0906040305120304020f 69
    0x18860f00f041003012907102415106642c4012801c0f02c428404645007000e02007018007500c0c0e40c81d2128107030740b810800030141d240030401504440b075101c000101c1920140d00c4000d00c02c950504c00100e911491032600f6400005030b141448811105443c0c070401075513250494180700000065100300d908200c1c44105280c1e5801003000100e40c5080541034840001800282c01c404000218104000c2035004452200d00010704454850803900400a20b10b00e00e0100035000b0103041903420003841c02018070300e01ca1450907529002600d052070901650f41c505d203c207540644010300610200a080841c207050034180766481122940c5044108840044090008404d00f4848001481411004075901e80d2240c1c0116050b0fa0760b0f2aa88045c040310a12001d80c81c200e081c0c040c46020400550000802b0102c01c20390091100507124071020728940f0402c18490360001c81040303c005108418005001c14543c000c01a0703090642c0c0f515150304040d940040300d10300800c0041040218a42818010040082 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 980031115 1250 980029865 980029867
    0xd09140d030b012d180e1005010804050703060e030d0207060c020c1005160804091a0f1e0d0206130905071202092808030403050105060901091503060e03040e1614 71
    0x58450f135003060041030300003001c448103074039542001d1a000b10100002c0036191858014000e54440e51410780d02000d644084142014100028480d841000d0305402544c005010704000f601c2d40d500d2400030110304191031018001408071110b0400e2502c040c000b503600540010406510100b0028204440c0ca03211505c900b100c15400b01c41694408140e4403401e00a050404110101e424201c1242c01950712100c8280d04200d202400120160b907070011a800a403a0180140300e0a4104410380c4035800e060340008106400c0702025260004000d08154005841c16250000f07401440c8400c1d8050b070811401c040c1c4030000c1c0480c0b02c0d44042001000403c0400c11400c0502c004006849440d1070908044400c210440d107440d070b1505c450f051310003094007200301d030707561503a9180c680c1c041c050454120f0300c241e120900008031040140581c001001182090402007810b5a45610082c840031034482060700c4180000304411b40c400c4041070046904140c154240d40021000414000e140d00b441c0c860090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 980032365 1250 980031115 980031137
    0x306060111120d06090207140706030b15030c071406011706010e180705120a11060f0a050f040504060b032a0d0c03090203010c0804050d030501080c060d09140d030b01 73
    0x104200c202d000c0e40c041100d07a070310302028000c0d0162080380c2042a00602c00070b820340420100102c00b051407003160056540c00742c2da40c0800c0d070480b40c03041181038126088000d03103a034100205008592084004d2a014100f0500da203d0224a14240000c810140e0002c7c0050000020107409204011003610040000390304000d0304c281d803d100545240c45402c1d540768034203c880c2c030902914014080151032480420741030240c80d0b5541e022002c0984000356005001291030500c20121101040024459860141c000d4000c558603030020081e07824038071052101084540d524000d400090140c16011a00c030b04142d15860703d040503c809075500204880c14150b04c180c5030b803060304c4095480440001c2c0d4043c200d40282c02234500341000a50551074646000c480340e0700158628044c50180b0103c504160107980d0660449e4000c1c010702c1c581e5402400c940980780307410300c01041103c0a04101242c4038000d0b9940303480c0f8038980d1a0700800c5070011005480a641d01d4410700c4c1d4009030920b410103d000e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 980033615 1250 980032365 980032397
    0x20105150f283c12050a0f030f180f0608060607080301060e010e060c0606090601200601060f0c15110708071a070c020f210303090d02060703140609040c0b0c0c03060601 74
    0x1a10131000c14445900b1040144001448950302e80740e000b0306126802d409525008101c0e0700d0240440022810a0200e0b20003444103c40000903141014203480c2e0903030500b20140d0b800c0d0001403203164406002c2111400180c2000051802003045803a0361502480c40000503144140140490780202000d1044c0d01113010000f404a8024106580c0d8802c603442d10310040300c2c5450017141a50211240c020005183d240009000d4101c6416a407000101142d11408460040e0881c01c050103c20780200c042c06420120b80c0600180c401ca0106245489955540d29a49802a0780141e8407107480400070543c04000310020355002c082807030100e00c848601c5c2d00180c0e07181c40c40800c95003d0f0507588020603d20440452042d038841c0c4940c226600ca2521001d869903859294500f8001409840b011030341850081c090009010042c0c0310107245603880b0b80c01e000b207004c80104103448007004100b001861314000300040c0b115805d810041c0049070354100c00d0520f4810090001d604002075151140f40740 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 980034865 1250 980033615 980033729
    0x6060c1b0f0103050603152e080f0303010807091815150e0603100908041a040602120f0a1d061305180402030a0f14100c020105150f28 59
    0xa214910210714680c03603411404030148004518041106c23005040500446481003d0743c0860781020225040008601c01c0151603000a20550301d41c0da101801c18425490180c2241007148603a80d010b03080c0062585030103000e216004080d80c070060b518000c60001e040c06281c400d0144c402c440810300d032428400e003c82d40d64090070480070519a65a0082420003800500301c4000b03000e00d400400390307220304915609807a4018820140035114540a031300046143e101503410b1402c035072041c0750074035031503040c1a07078114842102d0b6402c2c1c59060100404603991800505845201083c1e142c10b514201402d0040c500706150b070f014a961660707010480140d4001803004080d43d40b01c100078203000c00314074060300d00680307034030038024140a4000441041100341c2d00c640e40360130065000b40826203d21010101c040c006000303c0c1c1d00f0140003003021b1950306082d01d00c2c625226201e0504e0904100803501101c0d008226040a1191400c0150030140100c01c8007051510f11640f014240105040011402075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 980035971 1106 980034865 980034883
    0x304051e06122508040807150c02060108070e01180e1005010e04061b0f0531090b090c04031205040806070c030f090501051206060c1b0f0103050603 65
    0x240b0204020140483c041e40d88820007292141d0b1120111984100c0c41900c80480d214640b22281146114107000c1c3c3c101c0d81d0251001d07506041e0203c2c14030445a11050a55104000600c00c010180300c60302c0600c4103034400060b40a402480950411001e00400202c43d0b1a100c0002503500030320320403d10962041d0700401004018030850402e040010140d07000240d0124402101c0034010402040000607000e040b0000700000301008908180842c0801140c622030142041007003031a0040300c1407603030206c400003541e00d4494620304843c09688030103000d00c0d0360420310720302d907170b0188003100e02510082082d521640f070007900180c1000681c041c00c0340005c2d64030303008450403441354032000c1c1980c60582d40c0c1480c00c41e01c4001c1102040e4040c3c03605034044020084801e07030040c1004000c10320350030a0450580c4036000020410007045030010a41410700b40070802076144d43c041242e0f04 = true := by decide +kernel

theorem cover : BRFrame.Cov 979856115 980035971 := by
  have h0 := BRFrame.cov_init 979856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 979856115 ≤ n) (h2 : n < 980035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
