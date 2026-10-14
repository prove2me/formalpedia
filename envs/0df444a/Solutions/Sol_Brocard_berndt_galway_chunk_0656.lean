-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0656
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:58:13.47266+00:00
-- url     : https://prove2.me/submissions/67103fbb-a52e-45e1-8d01-1952c741a10c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 117805755 ≤ n < 117985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 117807005 1250 117805755 117805763
    0xc0804050d14040b030a060501110307210c12020c09061c0605040809030d020102030402031506090705030a11030106050a120506032805030304050607030501050405010b03040f140f0c031009 83
    0x110a41ca58608485050510552881e008020000010b0848103000554040c03c01480c0002d0618504070015012003a117080c3e0300d5068000f8045640464042050075184d041400110740003168021800c03503142c10400380042120301c0e041c021491040e400207030201d078602c098810018039160a41000301d1032007c0c181059007500350200d450001000b036001160042e1041841d1410101d480b13000070304201e05c006694005070f50100801c42585001c21040b00002c01d11201b41c0301d1404c040c004210300c0b9a0040402e02030002c0040440e100320740b980d00801c5500b10100c1d00a441c0d5031039000c0140070394425041040000c20344800e420038010244941405200010001c000360f4211010058207040500c0c0c12200d0390100d4014840400e0003071004502c260312903400b400f61032500c6580501150011b800c0580280c0c0750800500c84007040c00216504036400102e2a03480c82c10520b80120002c080b405120b0b1079018031011501450000200302e00604d008034240d4901c880c0c2541703c042103070715200000e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 117808255 1250 117807005 117807013
    0x603050a1214042301020a050d2c09010b030712090c05030d08070207060e041407050307080114090711030903070b0a090b030f16110106030f060c081501030b190308040305010c080405 80
    0x1c1390108070034007010b00020b0180141c4500440640ba02c0e820a601945807201060703401070700d990040080800401010f144440c0e072800781401c02702040014030140540d44080d0f40c004013241b910343c06032041c0300d90401c0c101024041c405191030050484c10340f40c0b290900920031183c45201035401007040500c50b5056900400400e0b00c0d100040b11400c0c41010384a8120380d440358140050f260010b1290b1081c0001c1c3c0f582c6640c0d09142c18000c02d03542c4164024030034054100507503182c039a2034a20040d00000c0c9032401440c980c80b0366040900310b102d43c6180f1a414412003200068000c9104007600c0800760039199865425610710b0441303103900c000c403014198850300ca000180030185200c03015a40390070344d141c68980184001141800c441b02c6800c02d440c1c0040c401043c10030010b0703c2c0107035a0380c200a840c0c41c1c000303824450310100070a0282183d203410302d17485d10100e04281d103450300503418103840891581031103960380c00c100505501c40c1c00f054070103509104150f441e150003244800d0249178428014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 117809505 1250 117808255 117808289
    0x180207031e0221090603010305210a0504050112020d0e060402040b270a020c2a220e1002160b06010f0c12170901020a03141504050603010603050a121404 67
    0xc443c0195100302d0008552109000003070f070b20b86540000d0750195100c0c5000340034882c2d025204100b1460010f240804030342040201c0400c03240c1c01415202110300c20701704015402e181c1b40061001e0b01409085101c00d40c606504021009000500c66020754000c0d20300700425813201d011301c18100318002090161018400d0704002c01c403207614025030b00c4820214014109000300d0710707a504000181c1064508003808011109124900d1203083c0004242202c0e508030407034902c6082036041d602c00201d03042503641c40c034200c00210000d006000c9031a110071411036840040140f00304201c000461706070780059132240000c0c00d650180312440c5207400181c84480594a85a07508194021061040d400304010307a48030302c20000d440d1903880e004822520002d0707112030500d50000c0c201c1c1d801d6440c2d0842e888950040c4510b90704d6941451010520a880200c0d0664900d000302c0c1c090401c0d07a20061041c82a2185030b0113100c0d0701940c807440747c0d40303076502c1003480c04124121000038000c90041c550000d24000b84 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 117810755 1250 117809505 117809533
    0x50105130614070c03120e010203031012060f0e0a0b010803090f19030f1202060f06010509101e05070b160206070302070302010b18010f0b03040c0519180207031e02 72
    0x4038003a480b0501518507028155445134010422507200300c4140313030f8204c65150000d4020b01c0b4681c1448003031000b03509502d0b181c903070041c0384400c0d407042016807080c0d43c03101c02c1401040c1d04409081203208205220117864200201c0d5500d20710302080d20804000000401c3c03980b4040b08846079280000c2401c10329041410400c80000b46410f80c4501450384004000300103464442854007280c05168551101000c2000190800100a10750051211500d040003042d07038011055410340d200c190b0746154070095400e41612024800c1e201a240441d040380b00003034841c2c1c00802807054038803030b0541d0711080d152818005078404c0c29a8080026801c44400109443d00c0b80c1d0107403070080e020b07100100d11400d0910101d15000c404c00c8180910f074284400520074411a94200b00040004030489851882c00d07441e441d1429240d0300034a8450041e40c2090f10303185080590a00152036268a40352613542d030624004000d41c001c1d44110302003207080c60400c101d03c0303202d500700c800d020382c2d034014188680c075030b0007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 117812005 1250 117810755 117810767
    0x120709051003050d1e030c09031b0b0d0506010f0807080c160b0403030b040515060702040e010e06070306060206060913060c12110c0f030406090b0913140604060501051306 75
    0xc110000030070440780000201e4020001009140565101c01e0900c16500200420310459000201e00f85410140780d40c02580d40a000302089a4100c122008100d400c04042040c10721141e1080000480125070080021035a80c00a0700803c804d0b00d070122600c507070700fa00b900d03110001c450440120704910002400004054014002c4401080400129003c1036a809019110558007a00000e580d405070948904040c454180c10122aa6544028070391440c000364040c810210000e00035900d0708c02032403c40d842500040d01240307182090ba9164603001c40014001c02e05440350f28018031800c07010841604040306441d000d05001400c885401c02ca0b5100c0b10042e104a402d280c081020011f40ca80750b1040a00c00c0c0c242c14401c561005e555140e5140c1403500d4241c9050119503276400400c410850f0036089041c11044403600d608203a1141540d400280781c210f058a4810284d500f081c0300540c00c24a071624051207810115002c12040e910398004550034003640044105d2113480301c40c20302445000751 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 117813255 1250 117812005 117812011
    0x4e160204091203022109030d11071208040512040e0610120612050609030307050a0804030c0b0103210e0604060e150d0204031a0702030412031b05030c010b12070905 72
    0x1034400300d032000450703403150100c0b2190304a8400090b0f0124680400341c041c0e0308102c88050150700800060704010f00c41c180c4078401c6001000c080c0c2d41c1e503c40c1c01290300c124415101d1190300a545015840e40084010f040554100c508580d00d00444103850551400740c3c003500c0c1520a88070340c0174601d40d01c44003172288142c1a0f40c030150901003c072040d45030710b00603401007801074414070201c80c92032007140c80c11070b143c450b01a007001e40c140c00030310030080125400380941d9103281207888d24ac45141c41d07604065402c7c050000c00034040040c114000302c20310844d01101d420328501c091941400074014a8211030001d400c10748990b02180801c400c200042c0f146208004c0403a009001e00d900e4015000410303541d92003103a400072450b0b00070a081003800b0b00055424060703101000c01402c10b24150078002c1d1648100d02800014040740300c0c00c402814406ca400941c000380360300003910903241609095035240c010351801c05c0150f003002c0e010509401c215000004a43d1010014a8158201044000071700001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 117814505 1250 117813255 117813259
    0xa03080f04020301020c070b090a06080f0703110d06080c120c010c0303110904020310050a0b120109020d110304030c0506090c09010308030c0712030b030d140307030903024e1602 78
    0xe2181c6d10381c80c2014403602d030040c2070b0004150340c0c8554200501000d148250b1000c024807da810400040303a4001480c1c952000c06407800207000300c1c200901411902881e46200c13010751030f0610214800d80c00046207405070b203040700da1a010340c0501400a80ea80e1054003001d00180f440300313034040040d000c4d0700801001200c0e9001c1d1810b011005c0d0101d03049800840300904010014a410000c506003908490003034144400282e2134840f91403290811840113118000300d03558006070349800501d43d98002c0100340c2a0191199a9003004c5c01c00410907910000300756858024040400c18100c0b00203401d9030324403000707840e407032090703103940c40c1c04400e600020314401581c2c1c41082184000303030320072a034444910700540700000c5001442d4145440d1481100411040c0084402d603900584984025258810308600d4003107164030240c502241800710240e6000f0003020007202e02e000031100142501c00201c0c0f403800d250101179209070100030044000d81300c4288503a042002c040c03a0a00d00000c08101400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 117815755 1250 117814505 117814507
    0x1305090106050d08090901090605060301060c0c052214060d03050d0b0901060c0303050a09031403100504020f091f1b080915030106020613020a21020a0e07020f0a03080f0402030102 79
    0x15031004110f0315494400304440580300041d403054145001140140501a036810801296050030049245407006004030828051300c814070408101300304c02c0c41c4000d0720000d80a00320440c40b0f240c1100a241111038058941428644030351100f85400011901c2210018904101030781c07140c60a0b02c0550140b10880010b9851f00c482e46419141c40c0d995078002c04166071221000700d0742d810004c0c11940c0c0506000e19440c00c04004e1008254480c0c0e800c80c0084210002c2903590720380140704a100c00080c0c0c002c603006400031400b401c61640e200c0251411020030794221045c7e415610f0142910904c981d00107000c41c440c90344c4403081640001c901d1850600c210251403030078541c040050500c400b001030340d405d00130000006100c030b50390521820340c01074101420400120203c0d40050542103c0d0302440d9540e14401070703030840c0351031120000b0b003d882c1c01400346d504254031108840c1d404801100d214025204641e05000709c0c400009442d046180c15607180c0c201621200c0001280c0080940103907410745d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 117817005 1250 117815755 117815759
    0x40f020c010903020f06090f07030308090c030106032105030c030109020a09030501020d0902041409070b030a06090e0a052b0c02151201060807020f0303060402070309080f01020d060b0304021305090106 88
    0x240c2407046000d4680207400030400e0307040c125081c901d040c000034461074041d00500c0302e02013038040c0041c0710310a580d07050504600c16035405108a151188421900e41d0641c00c0040c0001407040d01a00d0042c243d44001d4411510070913860190764502c03050390b40281544c0c04000401440c01554040c0601c4007040c50045c4800340e407600c0d803600b6a00400754640b00c103a582c2d110b8104618007441144c10030140143d100c075041ca072200380c040e110b0040d48030f1021540d0000001428000030b85d4007000140907445001c011000c41d50340060b94403100b03140c04031a00d2248000b18480c59036a85038010881d0140140b1030300364031030402d0481d0300c0e00e0b01040881e00030003018440a45105100050903030104495407101c00e5604d0500001d01d4031102030501e405540000c0000e504500c00801125803000c810364026076180010304e011110900c855026031501d00600b0301184c103912064004045201030040203200c0703580c940c0c04440c0144000e9900035804401070204140e01c1c13001d904982d500000340c000000d1525 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 117818255 1250 117817005 117817027
    0x2030102070f1b050405070507030e0312131502030f07120207030b0109050426120603120a02060109050912030402041503081b0f0d0c02150d0f0207050c0d05030405040f02 75
    0x409000045601c1010701c03d410440d21010b80455004140880d03080c4a80c0c20303c3c200140c010b10488501400f001204100395141d62410840c091a24290083d100e54410f855005246552114050101d01442c01611018814400020768000105243c000340c0b030600740e5900c0c0392811048041e41c90942c06590000000b2a0440705c0c114020f1402210129023880c00746000b20355103d4081100071b003c44040b06090502da070840990710b0452215000401a88840c00000d180c09520b00425000000c0040c400101c1c950105443d0b040300d6002d1000e01198540c41d40703964403400c9100c3c801c1d9111206100160140c5050b4000c0355450902d2041413051586a880d01e1400764403400c58a4040384007144100081101013102c0d16107458084040c01854030344010044c034498440724040d104954a40120703a40c1c02d041c0d022a005403003682c10801a079001101450041c1d04170503410349030741c0142544014541422a400d07004039034418080c501d4107081c581000000e111000041c201180d007071080200762 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 117819505 1250 117818255 117818273
    0x11160201080604150b0a110613030206160516060612030507050601080a05030307030209040e010609020910110303070f050c16060e0303120708070306050301051e060d0c050105070204020c0a1406010f0602190203010207 95
    0x11188907c8127030501d00d0505001e40340400c082c1c40b8213100080310440c0d0620035881410354003042c0b8420501c035404081e50410401500c3d10fa0001d1400c50010102401059000801460611f100b0000c0c2d07a110303a65499000c0d10b4013140c00001e0014ac20801c00100428441d03801091800707401800001c410300e007612a01d00b1035006800032100940d000841d150207140500c20b04d2240e16841c40c0c00e182241d12101b00d90780360300000c2c286405100d4221825485140140e0542d51001407010880d40594460102092031402d1885410045400c000f13a44880b0b080100c1100d150720040c1c80ca0f05016100c102c0c007140d00001c020459010141c0c2d46201250a41c1d0a000e007900030742107140d100c0390481030140d2808914901501e580e100e820f030742c03080400260f4a00c00b66421900300342080c50303c0e20715500114019100741810081580114081e000821030090300090000e8050b804075040c036a01c078080684845990700412000da801500c2c4802e8074600985019a4244003030000350400d0810742e0b0f07003541 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 117820755 1250 117819505 117819511
    0x40b0406030f05010917070201021002090402070b150a0605030c03070c050c1302090901050105040f12030c0807051c020105060f120f010c0207141806040e0111160201080604150b0a1106 81
    0x6a80d448030a050140460240c40c01480c162071b040462416115130b0020796989482150142485c1c0c0208001d1050307950f540c1034401168200c40f030f074a420701e00048509000f961151480d8403803601340502040c640e01c1903017502d1040f4070100b0706070b20b5901c90140550b5050f00308a0216400d104a02040f01940c840106014082d4182c48001d80c5402c01c010400400f00816000030f410408148020010555040000303802c841c00c4200d0042246000d05044420024404018140b0071000030a5802c22400048400d03041e045204404140a6040b0040f03090f100c1c140c91040c0d210302c2e0007000350303a40e1400c0d1030139400440441040307035086080b411070b86080d14100d00c00000960080d804c100800510407842e0460090129404d80c0c416006108441c6200009800c81c0d00460351865140c50f40d04095100c04003011035690543d1311424403145d803548011030658202e0002e082c110102c0c000b82040d00810301d1390030007031100264550030880c0364881350700450186820003041040c000f00c502014030001e40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 117822005 1250 117820755 117820763
    0x60e030d06030b09030304020901180b150403032601090c0509030f06040308070804080f160605090304090e150408030c070c030c050a060e01020714010207080118051e060402040b0406030f 82
    0x10740a1942c200200710302c0e00100040b1541c5c100300100b1005941d05607000341503400c00310381504c0c40c041104904005203803694540f41c00285c000d942c0b0240003031940160085900c01e44c1c400c03100121220114442c2006881c4031050b1500300c90041c41044a00c2c4c001e241c401c021482c009090046100009203407203500312140800d1340021061100341940203200581c41040e90502540364109a90f41010510803800200c004450110705581c5100203500d48200c043d410a0051005051140000b070301c0764071511800035107620b00341800c41900c0b0042641550010503840110f01c90340d694461b03101c0351348010301c2601004020440c80c40010401d0355080d014601828000314624280400c0c041101020742010003802580504004540e900068823011783e41c1c92400a100202d0020050740380c805140c014812650800c00007000b50750303880203840e6072a8000d100b1120120802400340031b408011140c40312460700184000b402504240d08418640b49006d071001403100d40c1c1e40c407091032206854000716 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 117823255 1250 117822005 117822011
    0x20711010e040f05010905220506010312050910031407110613080c1606030b01090302091303050d0c030b031005060d08070206070f03020c0102061503032a0115090606020a020a050d060e030d 83
    0x40003088000c8c0038045160340000c02c0c11030000d400c1d04e0340c0d5a0350300d05200007408601009005031107c0d105006842c0c0000c000b03885040304400900c0090007a200d40044041148070f1030f00061945442110142ca03c2c4c00e60700b000e0a59070b00c9100b500310320440030a0050700c060008211940c85240200446441c41032803400e82c05501d802c0460040988034402034850420007002c40a00259441090b1540c1003e48100d1b0540002e20503d02a6418010038498a01c0d40c2d19003015500429099085080f05032421810348241c500041c01007011214181c2d142034000c1d506041c0940001d0003c001400350354002030806007804401e9443c80700c1009001811001078001032400c4000e9601003205039004044102c503c44c8020500c00825078030300031038007011501500e40031302e05080d50000b14000032542030b020003071008218200000038240c070705209a0300003a00c0d0040010304548003058840410350b000f8600d011807484c0c0000c100140c03024000a482c6181d8601c2c1d01e441b079080c2003004110b10642e120b004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 117824505 1250 117823255 117823261
    0x708130f080d1706090a0f09060c180510020601050108040f17040504140105010519030608010608061014010804020f042c0d080105130c261801020711010e040f05010905 74
    0x400b055980041c5142010340003042c0241d81c0c0c1c0d05c02621350310842840c8002114055808040050f1822140241807140790407440618942d0260500c0285c6040340441980c240e40c8005010080074a02e0b000001070304006c0043c4403540c070034201560414011284100c0c0703100301d500c480343e8841803410f050fa140c20000070304104500740381c042c0415407a01005540115854030700082d18034401c8000d4501620000b100b040446030090340960064011003000f0400346460391295961044203407040c12100144030400107040d002542c504050004c182c0d58044141c1702c42c0d09104007000e10f05000c581c0b294a81030712040c89003020003401c10300d6000c13441800e8a940710440182c01c0030b101c03c0c08142003050440c018001d50319140e424102090302070034000307940e952010341180c2e000c83d10a903000808014516031811445100e58040c000e5291825100b003001010034020300303d2064242c01040c694900c5681000d6602910100d00c58a02c040c00220303550b108049003104a6200340c2020075641d95550038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 117825755 1250 117824505 117824507
    0x90c0d0813090203100b0c070b031801050108010504030e03071202010507031202030907090f060308030402090c04170609070608010810111603020a050d05030403170a02070f0b1503070b0708130f080d 87
    0x9070b20b00a1907000c0c0e81500d800c20641f440c40e11800c0e28040c40c8011200040400c1c8100502100d40403101d0700b5000030030255841d5810716005e0300d416175094000607082c0100941c03518021603032004070f030740890860054103620317130041daa00e402c000d40a0703081c001401554000940d81d80000d51103a00c0c020040c001e185e0420a00108803082000e074120b0b1a07180010900c0080c10410403281c201fa0101c8d014400c903654040c0502d110701c40c682154031000640f02c003241d03e001000801ca4012040c8030306903114107840380c2c4c0440e001013003403041e8400c83d440107100d0440b1400907407051107003144940c4110300e80b101c1e00100d001c0e45401c1200440050384061615001c0c031405100700c0000c03c0680c5011840d604160720000e00c803000f680c40d040e02288495010034199945641162011765120f4100c5000942c142400003650340100e03501100040304101044140ca40411054140c406003844981045116264030100b5044034038000d500914035030340813030802106604480188280001043ca074000854 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 117827005 1250 117825755 117825781
    0x614090d030e031218030403120905030307110409020d0c08030703031406090402100219030c02130b060d0e07080304090204060f0306080a0303050402180a0b040b0603090c0d0813090203 81
    0x4800304141ca00310070844460000f0007204c40780100c800854000c0d444003580c19507030381c3c140d0082000920000600004018213002298110041c90b10f07480390b10382d50754051507224030545a00030040040000035110619095210640d032900180c8a200000f1071036880ea0040b00c1c030ba40040307409030320100b0107004040c0d15006404800c0414800303840e1900700000421100100500001d100e683c0d1030200d03607103c0384200944030761070038051001c802d1202d41d07003400f520110f001c0505900601d00700110b01868030142c080d020003801c001d00180d2410140c00f085500400741c80c6555084c6005140d40081c0c2d207030003040600701601c8407010040c3e40b04d2030100054544c0181c42150800d0504241c0c2c100902c000200705402c045400d400d01007480d035036920004808590b5640f00070844500007040c0000d0301c0466000c142c1c030603401c1d03e04000c4803003e04104070342400102c640400b15406a89001d0450405000c001c07103040c8a0000c06e404d0403803503901c083c4032001c990807440c0307000e034040108071650401c80b03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 117828255 1250 117827005 117827023
    0x190504110319020f0108091623010c1a060a090608030c010b12060a05040809060a0f081b190908060705030403031107020102061f05030a0803152b030c061409 69
    0x44030a58007500b0743c04a085540d0710180e10b410700000c480050722a610520028950301c2e0022290301c40c46483d031504540c2003000c04600c13135140403c01404503403540601130006000713401420100120000ca885440300d818014182a0804044500041c5030788460080070080c0807000099500d90b41ca00c0080c0b82103a0148444502c5034990040b0f1800112700132a0498101d1001500810176644600b400105031003219010f640000b8009442c0d43c025911402c142c25138845903a6018050700e5144403075800c03068100f000060030408114044407030350010b080c400b10b00041e05024602964900540c0e0804030100d599402013000001041b04040d410310513141150340348600541002003580000b95100030017440025190364402c000d00701e04510b8a0f80ca070003840000c0454040c44130500e4080c01076001980c107a5900080a01081141d182140d2000c030b140600052810a81200300500d01604400380020350a00000c0054400820010300440b11582e46106943d400f80c2010080c4a01e003410030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 117829505 1250 117828255 117828283
    0x927050c1206012c0c0a03090b0f040201090602010204140d050f010c0c1704060c080a17180c091e04260c0d1d01030c111006051203040501090e1905041103 68
    0xb2005a0440c00c100200b8182c00c175181444a075101c0003200016001840c0305e4074043c1600c0301a00800002c0c4908a02152085100382d8904403801d030b940f07009034280e00a50185d9070a0019552000b50903050100403511001e002c0c204507030025030780c0e500075800c550400405800051074010150280b0101c9041030300007000a2000a141500c4c2003402000b16281c3c10000f030100c100040c0081c45c0e40c0c4a14203000c0070b550b0b000d1003006141000601c4080c4001e030035040032200d000b54110410380345007001c041d80c80b460401e0360448480d41c0a01501c004000010401ca43e045124407040c5600300c2104005015800d540707600d199150080b428191800c0d0741c692030501040303903158010540414070507281d0740c0e00c002800c1c00310392205984400d56003030100b03128581071845001c84103040d050031600aa4215141a280003624907210894580c41c1c1c0300301e011b0f42c0d000c24016102001a0030b500680700750700c061408020b140c0701d1113858101041e54800d0b10107403503020f50f04e0705090b0340303190600c2819100060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 117830755 1250 117829505 117829559
    0x30708030403080306220c020c030c031207030503190203010b040e060f0a03060e010b090a06140307030c03030e010e0607050a02090a060e0f340206010927050c120601 73
    0x245a981000f140300041c1a103008269008540b440e4070718010101c00b41e070282c00b00c240314845000800035500d1071107001041c424440d4100403d82c03818045a080800000519001e280000a44098606a0001e000641d811a0800e460300b03901c44644081e6020b080c0e69010243e4903454444580b0254078050002c5100d590700142c0c03040160385e104c01103c1100e40c820740216502c2d9408255a0041c8010310340103401c4001d40c130401c400c80d842544030038142c42042c02c1845048526006043d03131070005000003880c00d0540201400404d0248841544140c0d05150810350000c5144c0851140d07040b00c1c104030740ea5800074010404525081d80316036072280e002c0c50200141f0b07280c400050b84000e8054600b80c41d01d0790101c081480720380c1c071801c25011909015400309250045401c0789a0700c2e075042c04540c005001d04000031030b440e40240644c40c10000a52092210101c0350b40c0c11381007001d1080d20480e59071103040d41c90307021904c41c3d070710000aa1406001900302517242010520340d507001901c0940f95090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 117832005 1250 117830755 117830759
    0xe060102060f06010c0215040b0d0524090c0d061d070801061e0507081e1305090f160210060b091314040b0417040b0a02010c08060306060609011701090203060307080304 74
    0x1910071449420b40c1e40481d0f01003c500c21804081d07c251085170405036003000c00107040c00e01064660882d42c092401007030b03408080081e0607403a44d410b0002074401b60b40300c2c004802040610a51001074822180142000244030342e440d0354012680c0089a0110141c14205080202e841d800c85035550040089040c01c403020f41142151203100c074040700038041803000110f1000240800c080c10f96401400802112004011400c2594503582045c00004020343c164200810b841c00c100d80d50034042c060b051040803071074542d0b0500ea203420b0304202d651400c41c1305481c0c50700c5c49a4403900070080141911218207946042c2c0303209000c080c000100d0080c010342d00740300414003032011618400d44e2003034000100c02156200c40c5442140b074007070041305084a58001c103000c1500c4000800514514140b40c000700b00d0105800000e90f0120401c984c0e4540c141c0003880000c0703007070a0800c018421030805240c0003c0119246800b460140300a801041c03880c0e0307010003040410b003802c200301e42c05441c51030000c5080038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 117833255 1250 117832005 117832007
    0xd030510060c110a0303091701200a210e0c06031303080903040911030a0c0e030c0906010309051005060a0803030f0a09030c061404020a0f030305090402030711070e060102060f0601 79
    0x10300901c035240c10811058106418020028090300e9603401c0100004001980d90034010042400f50085c2046040b413142100c55440c014401c4686000411804c402c2ca00030b98541480c0b40c0d085484803000f4004d03040442341e0309150408003082010341482001614490368003a80385010a140301d41c030300a4104006010320021030491400442e9031615010005940305040c0500b0360003550f020019050400e507403074494400d282c0146128070240034003003140d409188022200340391100e040c0f070b400d03400140f200401c9050190344140e00c079070306040219040059070340715231504030110100c0981607a19820300c0054034002400324014543e0304000c5007182040300121200d92009400e0500030380ea100011020140501c6c40503200f41d4005904000c411a02034807144020011981284600c1d030030000420403604c1c4e04048001d4030b406560b060308040220042c0b10095001414003018020322a54607580b250702002650007070700720a607020841d8200440007900d40103010700601004103481042254503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 117834505 1250 117833255 117833281
    0x50a0f0606051606090b0a0207050c01091d10051e040605010212033601051005010201110a140912030c010f090f110103060317090102070e01081e010204050418050d0305 74
    0x40104103c840d01580c0702d030700d03240c4000d24800400800c4c600c404820042d4250080d0b018100050068054443d1450380302c00444003801140a0fa9030711090031040d5480310900704441c140e12124240c440b0f506252640000b500c81140c84010381c0ea0400e9420713460980e0f051074024000205403e0009010140000400e0740c0e540c0001402e1040a58410304c21500000c003001d84007129070000c0d0f10003910001c01182480c00703440225141101d406243c4c4000071594414410a480240101502401c24581d4001110003169800110a48107401d00c00940742e507481e04079640140400c48001d5a40d0f001c03c00c0e015083d10031100320303225443d00d4200a400030440351000c6428031031303110300440c221071801001640201000d0304040e1542039040c1c0c8400400f100c0c800100756180e026021a42030a0303980306500f121000c00d01607001c26030441000101111045010000045010b00c005401c00e9214004502111010fa49480748804030403032800034040103210380d50004115140c18812807038860005a41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 117835755 1250 117834505 117834517
    0x7030c05090705070611070506090a030207090b0a05060a0201050709090b0f060a02030c060405061e0c0405010f0c0b0703150e06010e15040f08030301080d11061302130c03050a0f060605 81
    0x540d84020009450b584108100c0f80003d900013030800c5810804128a601500180070407140c600c86e68002c508000c5000581c401c10951542c02811450704004290001e00302e83c0c0d0a59420401520020032203503214000341090071800e03400080c6a1070a403070f008140084941c001140300386802c5884640c0d889001c6000726000d02a12030660321201100200c0c5103103d0380f02500b0300d41c01002c0501080003404a0f5090150032058641d40c02c800041c400c01215481c00d440300c40e80f03034008000c200b145501500111101407018184034100180350b40b01d011442408880c9900013039581c40e40c0456181c038034100c8402501c5002c0e549003062130302100281086480c1c4450504c1100c1c040c0c002d20207891000f04484c06807034090010400300e0342d95254541d41e03800a015182050041541c0014142c0c8585403100040c462500148955225040c501550300308074035099804c14505844400c0d85d8080f40100d40b40204c03143e40005203485c2c04500c80c001c80d00c2c45528044c1c070a04012041041d15800f80a55403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 117837005 1250 117835755 117835759
    0xf0108070603020f040306050915060312180111030a020f011107080703030908090406180c0216060e030717060915010501140309030d09030f030e12070b071206080106090e07030c05 79
    0x20f0389944d03007607011a29003c3c0f6440105060f040c00d08100404001240c83c66000c0070500726941203885840070991070b02c0c0505000702d00c03000140100700030480389481404912106042510303030a0240040141164040c0151a000d40d000740340411fa00f0500b440340c46030b0480b41c1c510745801c18169650300d565038072450304042d01b01078450a00b04c0501448030300321101b800004004101150b50303820b848440801d80300c01d512860346040c0c243c0035014004030710305440e04400d00002072418100b14046d41e15490b80c00d4050303014400c0060205180021344c40d91260a01e600c0d0050a480c540301e01c442d840d02034850846240105032030010040d590704240c001240c08080c00c400c035229500c0c6090f11346103010703101e07048103000d0621300307a4401d01d50050009c10310381030380340d070180718400b450080304d5074501007030962800d18041080b2540205100314855a0070982c1440c003200181884402a41610701c25000400d5a9568400070800c0030801e108034400068500042e214151640e00c501c1e00d41c0c030440c4100d80c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 117838255 1250 117837005 117837007
    0x50108070509040e030406030b010306051c020d11030102040e0610090b19030e06040803180a0b13020111070803130905152701260a201809030705060f010807060302 72
    0x1200c03d643d03507008401000e00c131204694960380e583d607005000c1c05c0241255408645059000310b070714203110075910030f06183d4490698454509a00b8003449007a0344505450f8845924403036207841e5000e000a000501f0f0184164041c1d06040c0201b18207c080800d00005000406008005c25885c000c00e44403100c2d203500603010b00071a108000d0b00130b8155402809011702411080008020303800f00614021402200a05c1d030305182c10410a969814642c00a8680c00540c0c0014a0010f000d00e4400b88081c03040c0352000c504000d614075580380c1002030300187d00d550004036407e02c0e028084d4080784000c2202100900580c02c001c2c04055280780031079030850080d600300155170304407411100403405c04c10105680410560790381105101c000200480d500c00ca44880303e01c0c1d0b040800c0040e48240c9190004074490103600c200d072084c0c905041e1390300d80c66000004040860b0030740001100840c801c14800c4003540c0d603001c4514040742000360040030f038840010090012f000c48580001c0581c2a10401c0c1001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 117839505 1250 117838255 117838267
    0x303050903040b0c0d0e060408100914010e0a050d0e011d04150902071704080606010809071a07021c0c0e07030f090807020a050603011802070f0203150106180501080705 74
    0x50840c40b03203400c80f030041040003490240441c070004500b5140c1d295951914100d09410b410080350740b00318480c11106600c03000c3d114140700038940c0050640b074442d0000000d01c1c2d07281c070641c41c2903c01c40240103c858004524020501c4030501035140500c45901e4589001020503001a01d80740700e132030461405914124495060b40c4840c7c1c400103007014440261140c05580c3c03036098002c1c3d803101204880301c0000032000e01240c0030440030307242500d01d001c000d0040d641c0e4110044503144030040039000e0328030502c10000790000311144144810b0b4182407209036248014010307c2012100d03540300048119070036114502180d410280c0f0380c1586c3e00c130312007202161950302c0101c02405400460900c0103140160900410021000809145100742d0b12040e01654906c10062940024441c01009041c1d081861240f441141d006200d240d20038140382850103071070340120789403c880d80313451402540c40f9401401099000010004101d14120300701c411030b0b0501c000241f222001820100c103020000c104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 117840755 1250 117839505 117839521
    0xe1e0a0b04150203040b0115020303100b07050c1002030403060e07050a180e1b0103050a05090303130602040e1f09020403030512090f0d08070e011e0f021005131109060d030305 77
    0xb07181c0020b400107001d5460b070030302d810510208003080c41648860b0725039401e01c00c850740c0040241e034820030311401d92031005443e20407600450384c0008000c0384c1c503005030130584096941d41c0d0140421952158002d40d01c940c2546404e50443e500711022910f245c2c4a04801c0040e82c1c3c600f000c0c1400d4a0203000402040500c540000015045110482456000e101d90b520004140d82501c0c541d40c0c0740036641405191a04180300080717460550f41012039410820001780e520b0b03601215420102d2040f10011b107001da4540c036203500c00909841800c030081000207488250303d1010802d402602c0c074900d0452801e450344e64041c05a204a0180c0e4814021403000a2600c100900c5140d82d0490418143c52180e00c2803d4010300d2404100c0b07400f0045401c0c841c1c1c1000e030b54440d580340c25110b015100c10548680e14101d091711010b103440d0810003140304042c0d08081821090051b68000c440401c5584407521040c80c00b074468a928440c03880c09000484100300c0c2c82c2da107108038501071a07018140000c031034a80f185 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 117842005 1250 117840755 117840773
    0x10050903060115180b0d1a030601031214040e070207050105030f1506250c0909020918030f13060306150c0b0702030c01020f0304060b09010609090b010c14010e1e0a0b04 74
    0x340d0118258402c0d00c001420304d0217800400c0380e2a03140074100b1030f103405480380000c07980c0b40d010b0300c0343c242e0312440041c4001b0340d0301884130f040703011030741400380f60303458181c0105045a105800600c0c201c0e0100d014465070307680400c0104050882403c00c3c40c114a8804446401060700811080c01072181c0c82038000580c880000300c8850310340f8084840d004500d0b21400001011010404817055840c411002885503010300c6019080c0f82d0041c00d2050036143c0203d03044150790090040b0b9a2400100b11200002440307400a01800d40306640c1c450b6120302c2e0110182c111940340d4031000c07154140c000c09c1c2240b15030281c107040305203a0001c020f0245031a0220201d15500a01d050740c0483e40c400940c03901035442c00c5000c1c1d4880c510948050203925881028016a064284203100102c0c402400c24002010b0507080122a80301c10300d0003403040701080d01c07880c10300101030309108580c0e5034031040604035a03024854030300c1407441402000c4020b40d109030b44568400150402610030740d2402c01040030421048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 117843255 1250 117842005 117842027
    0x1e0c09190c1812030e03010b0f010e12070f03050f060106090b1c0f0e10060605160f020d030302030a0506010e13150e160f0c0807110609040c0e10050903060115 70
    0x4001180b055407141201261103410031825808200c145000e08018581406068000e03000607014128440c0c4000c010b45900240a0b00c282c0d01c0000c0c0c9001001c00c0204020240041c2003080100842c0361660400a0078600c03401c4103030f9941c1e0403000060203d0341d0001483d9044400000e0600c0d5504d10518a01c0f4190014042c0c1da034a00d41052100180350a454000000c400c568006840000120410490407243c2920600d4080764041c42180c114090050fa6031240718055401401c40030951750015030031554140c011004680d01005011512205210311544100203090502d8089042c1001490210581852103134448c1c5a0205500b801c042035460070061844481900c0203007024540000c1e821651004c50300084d084400c0b000e0001c0c45800d0b02105244c00c072000303524006164139101c000100e04200c07203801a0f0200656102078480d0b10070010418076a940b52200b10081c0307400c114810407041400340400106000c1541030390380100c0c40c14115428100c588d02044080c80c0300303641c22a088 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 117844505 1250 117843255 117843287
    0x7120f0c03050912010f0c092408090f0a0602030a050609040b1b1e0d0c02060f01090203040204090f0b0105030609030a0909020a020a050d030209090c0403080703080411031e0c09190c 80
    0x6c0710300710304522150003444000e030b07042d150b1142c03454407203501011100c2c0184507217520901105561380701c00c1c0200ca0007608100104140c0e03003031a900e002114603203c580c030401c40d075041d130000c00c00a0b16140c030b20505820403001ca8080741c203420651109560b100000d031030032650960064a91019003501021901c410b0f04120031850051080021501c10381c0107807400140150800c03604281d054400716545204501e140049501c903404c0903120070080d08018002c0f40c2241d036610a440106100d0740c072032009944540c010104960505040c90b0030030302c01900304000c3d50300a101d000c40e03484c1c0045805090f25415440140c48040c0c2c020101c1c6002c1b20510013600074050010610306c9180d054000304242d040540d113400040e110101500c9080c42144005400e6000030320880f00003900c112607503038005001e0507402207124444c100007801c00303507074041032a41004500d44603540d4040c00d00005006000403074013440f01d460500317034020003085800100c104035907540c50314917101c1c0d002c0c9030070713601c10041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 117845755 1250 117844505 117844511
    0x171e03130303020c131503080c0a0204020f09041a0609010c0c030206040e07020c0307140603060a03080309070311040504111507080304151b0e01030c0905130207120f0c0305091201 79
    0x1e6400d01030340700d01c4145030145c0140400d44070701403100800d00600d100800c2041264200b14a95160510310f90071100316100f41d0302500b000c0e6000b583d03560004c1c1c01e19107d00c51070107075604114410001119002d105c0c034840201e81020414085c1c2d98401914903100013070901031640b00083c5071040038203005400095010b18081408100764010010051142a40b0b03022500300145890030956503c1051084940c0302140041d42c00b85803e12801858000c000605074580c4151681d03120340f21508211071013080d960165108000380070f144031000a01c1141500c08020780d044c030b40c443c000c041e000c0154442c00ad44a090708002030318604400c5540c0190404280d03503c0e81024a85104042a40d40350b1520290812640318010710955960043c401c060b81c0b544a81c409252005401038800600f0b0b074028401318a03400659a11196813a21424182c0c581c010380d81c01e0185013410000e80401402020803106045c0c0c0240c071600700807600030840d0141400c6844030400300008907040c0c0d240000d003290f542 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 117847005 1250 117845755 117845759
    0x30f100906060801060e060a0f081207081c020c010f09020a0506070201021e0c01030c08191a030f0d17040b04061109270603160e06120607020313171e0313 68
    0x54440300300d40c01514202c0b4034000c65951a50302a0805400cad015501d4035070401010503103220500001045043d109100d03050078815a81611000e8501401d01040707a203400084500c1055001c2c07140c041d400d00040d0b800c2280c0700443e008a43d200f2880d024003801600e0000310b00040da802004100d481c00041c05c0001a103108000ca0702c4d0b141d8070f0000503140400e04100400390b0f100d018005485c861358a0a40011405041c254120003800c3c00300100400040f1240d0f01440e50344060041c4000c4c0940000102403000350603000a00c9000c02140b8a98440011000d0000050501e02e4040d00140c01c003002141c0285072800c1421144503a064803a407012028113050007404240042031140f4a00311140d980030355500041c140c54150500303603803480f80b40024003030040030707611945a500b001000d069000b84103c19480f403446c041c400c0e11500090707800401c090000741d5080c0e000740040c00c0743d0680d0040c00c0407101c10165641604443c000c01c030040c144140c10341c45a040064480301d40c07254103501d01c016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 117848255 1250 117847005 117847019
    0x609050a021e090f0402010509010f03060b040605030f180717010209060c0606090601031a01140c01020a180f150309030c02060310170a0c0512030d0507030501060e030f10090606080106 81
    0x1900c00c854450192030400c0000c1c4d10256621000c510441e0103840b250700c2e1000340c100454080040750844000e050f9100b01c080348000f0340c070010704094985511001e680303081155105400c010014008085401c02c45006d507200c0202080001c121510a812807c2c104071010b0018003a0244041d0190454000309091290003c00940140030b5042134178082e00940310100110107444da5070102c01c11944148200302855440781c051000b00500b0781ca0f020f030400c030011034080c0c00da901010200001510442c040c1c20300740c1060a07150020304146454649082c50032000303985540d041c1821f42c040c155205420030506008100341242c40380c0c014170195480c0340c83c019400a5400c203024801c43e5004403c2283c2c40c030301000605503100364100512040d003901d00401c10080b40500200c658560205000440d680c00740ba00405001d81035070740300441e90390f040c184000d00c8005c01d40c00c018426070068640d1081d503030002c41d111101100020300460300140310700f400400b8007810750006605620340600040c00c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 117849505 1250 117848255 117848299
    0x819051e0a1704111302090402070302032203050703150f090503030109110304050c0918060403020109031101020307120c0309080c1011030403090608040c03050d0806100207080a0609050a02 83
    0xda403a01c45410341c002d9800001c1d15101d08581c018030613503032a065000c05140042d07982c0c10507401e80602619118041000c90306a070130000084016034008500804c00d019a4400e08409002e42c0d98508025455034840307031b076502010300c00036090008504440030300c060203410260103402880790134401200f15203440c030741e207910921940b00420310f0700421060185010303045900607a041070040c030f48080940100421910b0141c0141002080c00407842c01413a81808030501c640d0113034000150006007030a0281c0120514151818070307034810801c005280303400414140802c05814000541c032500d10000703070b00800c039441c000381c500f170300102e03504a21507030008100c01000070101c0c00340b0024124440d60b84c09070005542c000e01003400414240700151061f0822580240140107c080349652901d50b603003005040c00d034810008406c54100041414040d1000c070b54042188000e1440c01d00e4404015215040040c0c002d18107503c0d6a01e003014803208000024038550002c1031401c14a001321010840 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 117850755 1250 117849505 117849517
    0x71b0515070f050a091406130b121312030903020c0301060b090a0503010908030109020702040207060c1d0105041d04230a030e010807090302240a02010b0405010807030819051e 77
    0x7803001d080c01500b035118005962645140340c40715000c0d00c1c00c01a0032880c4015180600d40c11400078858045c4080103290900300502c5000b902541d149170300210301c005040700604044001204032001e0b4009810386070043e00c00a483e01c5c00142d814150314040b4102030b51110340550542c00d082b40880c07240c0181000b86007000f01190f0310400c190340d407400c0c5820f8500e0b032403014088810030303c0104580700320f940003451903603c006c000600c0c100d100c0ea41c800403280d61079410b00004080c100310030446a21034a1581014009003029801c0514240111518081c4140c01031111402c100118082040500a140314600c280c0341d5412a00041c41c0059a984400300c02a00020316111400469501409949018240743d44d102e17010f290558003032240804c2c41444821440340004400041c1c030130100b010700a41d640c1940045482103208041000b5110180c0100600b078004040400009102c14122401c0c00c54091082d40c44002180e01650f0031300840390402c08107440111880b001740144801000317 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 117852005 1250 117850755 117850757
    0xc03061b0215060303190302090d0602041d090d0f020a021008071b051b030c0907020d0306050405090a020411040e0c040e01090c0f0302130506040f031703040b071b051507 75
    0x2e5140b00c0c42c051044a22040e01d042ea09504100500c0c1c04911008a035058207045c0313814050300c0c1043c00c502061b16102c078180b003618502e40c003050900804410b040401003028544e070f01d00120341045040c0c00d81707406110040c001800604091264260300a004100c0303800c0d0010b00c01a84100c044034043c00d0200212400000540c40d000c2d00d0740003082d41140050b065411200800041c524140002d9012034800240740c0d0510070100c240302d490362083d8203d8491189607000d80040c5980b0300c030240039078030f5680140f440b40f4200020003148100005004c1c29040d011100070503043c02040d41c8007518400e94100500c0c0744009010440c03690000402403046400c40c40901c05e4036a038a400324004c0b103944400e000c00049513074400c000042c1c42034002e08000c0440d495010740ca15a20000201b0a80c0301c1d03030002403c61400781e810030074031a07562a22041841d05040300c910b1031a25031799808925000821410512910007241074401041480b807200e86584030003128044802c82c0e00d6080c203120200c6001d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 117853255 1250 117852005 117852013
    0x13020d06050d03020726012c0d021209010e0604030302210313110a17160f05031e070b030109051f080309040f0e030a1d0405070e0402070c03061b02 65
    0xc89007401c40c0c0b59010b0a405501611606080c12890036915071a121007511040054001920840e002c1c41021015041c400400c10703001400070002c1500020340020b40169000f2015244070355401003403092407202042c2e035071540c510980005884403228001a150007101c0802d011041540000d02140464000070300c0506c41d070140620440300c0c0c413044030f50140110101140e5000102800c040075017907000140303210a460b17280c03d10000d40d580d90000b8020705038081c072501108024014500303070280c42d0080000d00d106081201280d503c43d0700c03042c800c0c2c8042c581d0020b02102c0000384144409440080760039552540c1d134044140c090307c4207075800d050a01c640c1e481000900300900d40f042c211600c40c40038500300602001004018042c1c8400030302444d41328440c0e092059030504c0140401001c3d621182e6a100051400c61581ca480d442410b024524060900010540020458545040480740940c5d5000c007841c02e032300684402d901c002d0080c0e0810b03d0411070700c03a14442c2003140c440240d08031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 117854505 1250 117853255 117853259
    0x15080a060b160b06010338030715080c0d020304030c02010e0d0209060103092a030311060c030a0207060e120d0c05190810180f05060103050601021005090c13020d06 72
    0x3885051040207805464628402100e200103080f0020395a0303c1041418002503a00e1440220f2203610706044d40d07110b5014200c0c480e1140311080c42c030440c003a10b00a50061440ca400c003081031a101e07104011250030b11090800081c0035048120486850401d200000e54a90415142c040d1802c00f03210400c03804510700c2142c0c1e2160f03081c440c8800b140307190001d00e40041e0b03031101d0300154000c00312444203403030742108800c04100c0440b1400300804075004820221510a146041c01010214400c0419110390451000c2c044018015000e8980011441d4001603a40e4200e03e0b09900510000340301c03e0542c054902510860410072000c1c240203000000b040c000c1c1440068100ca580c03089407100f14030f868620100030b43c958803904a02c0d034090802c51407620029200c205030300f4035407840c40310381c0d0310180c03200c804202c8a0524001c0c550012020300b001e00050808900103503c5000d00200f1705c4c4110f03560340c0007601400d410000551010006440d074041c8503080200000690701c0072640400c000d003000c0300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 117855755 1250 117854505 117854519
    0x60204092904020f0d06120204050603030309060411060d050a09020111010b0901140303091507030e010806090a050a060902071b0b04051c030c08180102010606020309060f1315080a06 80
    0x10301d0450548005001650140d07100c1003000940288502c450189014811300d0040b03451486598080e009400d0042200d265900c100000d0b45c0c0b00419040c040c2d001881408018075000902e2504254880200380411000f140402c8650188200c43c1801d2800c240074011500481c1c0d001a4500b0f000385e0b5800d8410702c1c41c030441800d0710840314481c0c1d0003482090041110301c078607648550824500400750b03803511581000041e0340711a54014a070b0098030018182c1c00b01500090f100b440c194080c20055081d180c00c50000da2500d40080804100030b0b1100001210003e00b030344031502520046204540350a41d904020341d2580400361880103200c04160b001c1000303030000040e18201d0f03500408501528580842c00044011900d030110248500305500310f0025a00da405004000c1b4601140b0070300900d203030300081c00e4441e42d41c08078080d9002040060300355111a4100d401c1d0b55144c4d2070b0981d0b604c0c00144035225814465101500c3c040320301e41e45019180c1d204e01c5442c05550f02e22000c0c481d1545a02d6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 117857005 1250 117855755 117855791
    0x120f0e060a0203071d0301021227151603062606011a07030c060e030a08060f0f03060601111c02010525050403020d030210050126030f0d15090906020409 67
    0x1602d80003199944103591038003000c0081713460318200f01900160601003071200540108106070b07403001c403006a88008000b000801002030321701c042180002c0418898020300020350142c050025452440d1441a084a15000740c010034001c1200410030641d82ca052003d44071010f000c100110194001c150000400c20300d032003440c2e03003103403443c100c41864001c003654259000d0815020440e58517458000c4075610000920203850703400c3c100e4035608003603c0d041080181034107400340414440c25400c81515841c0e00c00250044e40406c0a08202100f00120703c0b00c00d1401550b2224500300c0c0300d03a03017903a05106606410250040c01d80c2e000e00b581c911803c40b001a1400120141040054003e01c4200054980305441c00c4030036001c0c0c010340741d0b101482120b41040d517809800142403802220b15803204034913503440d000140744401d00a58140000710080c02c3d80b80c030a1400e0700e40c11540b0340740c0d01161840c8401c0050300800da110307030070401041c80c1e250440180d041881500e2a59103020030348588051221 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 117858255 1250 117857005 117857011
    0x103020108062806260c0903070e10060f020f06040222020d0b0901060809100504110603040507030209220204020903030c06090a0302071a0a080a060b04030302010209030d050f0316120f0e060a0203 86
    0x703001c14103580c0d078128030422250800f041c40c0c0c0d8236100300200000c00072a002080b5004220001c041d0815a080c808050103419a00341d800c030840d070220710035003002000411300540007a4100d950175000d01980d8840640a000700e9000040d051002070003141e000381741d1b40710704164030069a9507129680e8a02050315821000c4030b62100640261806901e00c09450388510383c018070500c01400c5100001c070105460350411941141ca542c800030041c4203520b040c00000e82d11000740030300c4191005c010b07000c80f1401c03100808020701031a00410011000e0360181b0684800180b1602228001d1402d12442d5994165000003640540036191021803040b840d480a02380d4504411441c40c605210140c00711265080244150306032a618040032410340760030b4005000841c0698000350f1501201c10401d420485104005c3c002e0200420140020205201c02e80781e0000c240c1000c0000c04501e4081a03a43c04c00290741141e03144c1c039025a100700c01c60f040c0e10005100356180100d1b1903ea0314803246404900c819 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 117859505 1250 117858255 117858317
    0x101a09150d0803040f1e03090b031005150c0d05040e010e24010306080709020403060f020301050d0305070302070e1014040b0a1406071203050f0901060e0103020108062806 75
    0x80312001c0301080100006541081c820030200031011919220300001c01d5803001800c0c414001d84050000741940302081d03501070700c1544800b500d58244a0250000601c45200e5180103d00e0b9020301d640707032681881583c0d00301c21f5140584115451780708000302580d0050040d06c48400c0c4690011601c450000a00c504c22450106620200964220120081220034221904150b29041c0129501c01e0500442000b0040582d0150700c4a082d440c0071402d5a101d40181200c0300e01c10310042106a480c52546058183c050400d60f50751032486c01d04909140c041c1d000720b0000c544d98002e020aa00403000300000302c44030300391380c501406040c00402013a200d020300907581c0710240c0c007001e00c0440c0521101e2007500d0001031420749008046d03a1060b13206030503090040c022071b594008100a030b44801440f940e0180d442c400810003282440c0b818410401c06000190401000e280020015290060625030580c0b40c0e80a00c400e22030010181c10505066005510002d0210480f4500e452031050328000c011241d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 117860755 1250 117859505 117859519
    0x60106020f120909090a050a0305031512060f100e070c1103010b2110050a06050a060c05030f030703020408011401030213060803040b0a020a021017100303021b0102101a0915 76
    0x3d0104000d030900503022000c0717070250001c4400010010000008114460340f2120340f40e15000741c00d43c110034504180d01d801044030301c4a150480a010408c40d6001c203c1c0301200f006c580320794601e002e03140113940003186c0d40301400052140b0903030441910f0752124815121000902c00320000c1c1802e0315454400791386c021107000110700d1007039548030003111030054150480b12001000003070300c9c0075980141c454901d150780d0b42401344050300301218281d01030131060404007103009144c0ea407207a50307100d18044002e02440102c0490080c0740320f90101d6005014001c000d06c100060f02c010584420310a1208910816004149483d1042c0034002c2c14200e07004800914241450591552215848501b51000314007450504000680c1c0e904400342c2c403a0380350707a240810343e4030281c0c4a00700c001025103054080929040e0030000680d0006190300858076108c42942c10410310380050b803501c0f180000c8041d40e1410070b0210145007502c10550200702208a5900d0440e85904044001840e4030381820340d00141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 117862005 1250 117860755 117860767
    0x302100e0907030c032702090a05070804060203100b0c01140a0b1c080906190e04050411010309050c12010209041104030308070c031103030c07020915101b06020408060106020f12 78
    0x400fa0b40a070034030075410300b07001ca442580042c4594034810310480440d10b11b08000484801e41c20105001c80c2e004141400410103410907000180589200410003032840e500000000c08903c5040a9440109030071407801d40c4814009402c14040c20241d84103030a0f403010100081c60081c05401804016072001c0c007000014100c0a8040c444504581d4040c2c03961702c0c0c00c00c029505e5441700c0e002031100c02c200480c43c2c60300b001184002400113070720340001441a42000248008525104082d0001000900300011011498a400c50402000408031a8030803104e9103000b21480d4107400030400d903242114208501c0c903081c5880e41c0f242c000d42c00050b0000b00f0103000181014021030a139000c10b400b0382008411402c0c0030705282d1840d0f10840700300320a0100400e0500031403d2000b040c07a0405041c500ca036019a10b45030100380328141e9400240c0401403600300b0341401e008201d40245155030052401d41d9510340302c0408a0355840c080c4150302c0144140d01c4228111000464441c000b9188641c079689411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 117863255 1250 117862005 117862007
    0x603010515060a05250317090327040b0d05060612060c0a2f0a0309061d0906040b04050112033b06040b0a0f08010b0a0203030a090606080d090302100e0907 68
    0x142052110703841a101300000c00201048007255808464480e503a5011342142c07100ca100c4020360040e10a03612640700b40991900b50009007000d150300104104142c840115450006005e48100340201740c00c1281d04dc0c3e048140314022030000e11401044d210040002000c2180540e02c0c03104a138007445418090101100340c510070755a1449400354114080340d03c2c66960080c500c0180b50401d81d0180303034001d411a1003050b41112010700142058105412810312044c540c1c8510f0041f803410030711a181c0c0c1f80025001b65141d0344060340c0349402810402156840301108205550340c03030010f601140b6000000c00b40c0c070340100c0444500962200c003628088103451818541013121a4140390300001c28480854100d2600d0064000d00c042a50b03021802c2c030303500002901080c01030f084bd0f030044400b0460b0b901c205400100300c9401040c0d1007000a40d080d02030401c180205402d80104400340114803805000c1684405076a09490080300c0e8480c14400040741601c582c3c0b0700700c403180d41225482c0c000804503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 117864505 1250 117863255 117863257
    0x607080f07050717010c02010b040c0512091f0b1513030609021309080a1404050a0e1306060b0301180605010c080304033605060909010e0c0903060f0603010515060a05 73
    0x90710407000c80b00b0203910b42ca0038100c0704182c805a04c095039955128880380720744c24007401c6840d0f00252801c10040030300c40401003403442100c0340219099452008100009010003c110250142c4051240496911103412025210421800340b050f0345200301400f45442c858120344540da2080700070f11603103166544100162580103000d9130300000c4c04801c1c503214905d9000715200740340f08064250b030300c1d150600d01810b0b1a2003038100d549034000500c01071010303803519164842a210b852034041e00b0350780c6100700d00010a01c3c05400402150030300c10300280800e40d8101540c10303280200150412080003510f100200c4000d807240c24000b821802000d404101d0500081d90824060f240210982e49418039003041c01c42d080e072900f000c000c0e05040c0700f0004112250590081d00c4200c40c028030313000c401000100c500c0018011006000075800104004440a804407608a900502607840307514221a41001407107044131444d000b0350910002801c880700c0b00c21400c850b908018a400d007001241c0340c0071a9a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 117865755 1250 117864505 117864517
    0x303050627090c03030304030c06150e15030a050717150f040803071e090602122703031c0504060b030c010f0305090c040905070302010224070f03090b0406090b01050607080f 76
    0x124010b0b00c500b0000f5450500065101e940292190030f003c08091400790300b2286002c880c6400c2c40c28081040c0031180400342420b4020035000e400c409070300f01d1200000d003030104070f0000400c00e00c02c01c00001050701011048441c9100080103a40410302d0f01502001c00c01000c0743c0030002900240b0009000a91000184bd002240d0303283c0031031440c41a164460342e50180100c8540401d0b0b110504100d0307240d04001c1c802801080c4c607c02424020085158101251801d4050800320860070a10046c0e88040054840b100301039040c4850b10b03806c441c0030700010982070f141900e0f51410460111000d041c0056044100c0c101a5140c2d22840c0c3c1c012401c80041401a060f100c00b40103015019409980f18001e25000e503000d0400f5111003850b61001900e04000303032043c80048462400d0041c202d101401c800340e44001c00e4181040c0113a4044001c400802d10340c20010310703116110050000348085540100300580c4070320945809070340c885040010701e0144c07500060a4030320810030021205003c60281c04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 117867005 1250 117865755 117865771
    0x41208070507020402030a060e090114011401111509070f0e0a0f021306020c1c17070606030c06021605040e03090105180301021c0f0501061b17030901090303050627 72
    0x2c1411241e07400501680d00075903400d0000d6846030820f104484c0c01040450300040300c0002080311141919541004180500c03c2d810188190303010f00b00d1590140400c509410705200544a080072440c40313214003c50140c0e803510031841102c44c00304012407008800c1c404d035411541e5607101c9564250681c2e02074001c292030704141540034006151b032100305c140002e01610098001d0000700c14051b0030303c081440607400e800c1380150380e070305810007049002039240b01180d81c0ca031220f590340a0707030300b01040038040d503500003084074142d900c0c0050090f6001c40d0342401900d403410860600c1e50307250700700420344400c14000403841e0410041c404042d0f000740002d26000300c0d0b031660303403441c8012803000a0890300b150583e00083d40704011052400841445404440d50008004109950610070010a000380c02600c10f44102d841070b4510080c032a850406140c0c00e144844419542c0c905425418040c24031440300320046424400465911b2401206007912400c905900c840206a42c010300c656546000e0300d550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 117868255 1250 117867005 117867007
    0xa0c030b040e0a02040b060301031e061b1106101410020a0501060807061103070c05040b04020702151903060e040320010c0c0b160c12260f0f0412080705 67
    0x340c103403924000d81040d5400d4501900094071580188015074003007441c5944140e8007040140000395034000711000042211201c0100e912031460b105001740001040c0b1320f20b4180c007500d21029181d2109400f2001851343c82507403299105e03484103082080c62801118143c02c03e01c0c06800141c10b0242c2059801c0c80b90f80704444000c88540c4440d42111a150060724643d0002c00062280765008540700130907642c040d0017185082604d844050541c01c8501400c1d21a6031030343c1403035083d13a596405032441541c000703060107507034100e81d00425216031140d05000c82250181100103405ca00a100c0c0c101150802c0b280c2c03251075035495a0480b05103030040301d81d10b00c1c01c0000d0303400c4008a109200d882240d0843d520f801400d280b02e400c280030354010051070080c41003d00e41000705210760010200090641c403c036010410000e100042c0c401103d00d11600751000042c80400315501e0109111a02900100907201c205443d070108201d1485411180a00703403035991034807425a188100d04039503000059260103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 117869505 1250 117868255 117868271
    0xf0903080408060106030b01020d0c030c031214040203161d0a1d0106050f0603130308220f0b15030303130302160902180913063204060b0303030f0a0c03 67
    0x316800307800542010790154050b10061100c681c240c4141d041a2400b400200f0702126040750050020b5560203009042101c4100b81c002094050308103a048007914400a00094030138000310b1500140442c2c4c20380c441d11400f80407030070a036078980800302130ba408404011004505251004c04440d409080c0440f030759074542e4503949655031407815003111034060340045129031074001006296030502080307503c201420070038402c24003a04d200c03500c29180d02d404c01c0d04442e0b0f500c00c00c0c5110b0741e07403020095254551040c00e603420800d0040d0400021031180007021078a44071560150302448248a0054140e4810004522084489150340c064140709204882e40d030400d812211004560991001c01440c0d00850200a410860300e07002040c400159a03086c450300d0f10b00c0c84034160889a00d4003a04007580e0340c41d589540b091403144500340c1220403000000401c858440311280c800210b0301650170516140c1681030078500070046a000c0d00f1041c22a62041c0c44004103a4002c0141e84402824140e07240d0361 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 117870755 1250 117869505 117869513
    0x90e0a06092d1502040608060f041506020c01080a1a0607050f120910080c03130609021c0507091b030e150f010603060e01081c051c0504060c02010207020904030f0903 73
    0x48500d4640b503080c030368041c001a01e00300e650390543c00b242424090040c0014006c0981c0807964544c0720000300d40b011964400f44011400810b05010404c0131480b90203008104c03d030300000c500d0801142030b6070303020b410f90300c2d148501c2c200c4040038070a86040c05881d580e0f009c0b41c6007581c081c0a95500070b0094032117440a4901091829000d1008401c48000101c0c0c8e01c1d40030f16000800a040c415142003407070080c0787c001c00f80310b07242c41300800000e00d5076960595103060102651000680550180a000040c051448244810040700707078100c8480c482c0c4070000c1040d12050081188888420800564100000c50154050045070115210074850440080440000702c00c000c0c1c0100b40401c01c041540d414039a0003025034400e6008400ca0304004001000021000180700c090500f08850003009085a000102e41c5c601c14030b0030320081010207551010742c403d82644041e00880c4140c800704003121501c54245c3c02d0b400381e03070b202a500001c4440000c002c07a000e0023030301b82c4c00344007407600c08111502d81d92 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 117872005 1250 117870755 117870803
    0x20a08070608070f0203090904121101140603120414040525120e0703031e0207120c450b04090507030506070507080711060412050c010207090e0a0609 66
    0x100c9440040d400e031043c00003007500000074160503403075440a0b502c0c080000c80070400302040a0310090244041d83c400d812117610824000d0301c110601c0c4004d00500c040d5809603044080c0c256000303446801015070700c80801140b501203c044a00700010060840d03180d40402008100040c40704001d0a003c026003503168480c0001a0f0703001c1c407192115000c40e400310309204d04440c1c0c002e08411113071380800e03020710110307801c141c0d100c1040c140e81600c85c00c0340001d528201c0c140459540068859a04a144c100030441c40d90440c0e400e9545161510941d000c0c11614200128444454070864554000247e000403070b070251105003204134940d012496001280200d001c0314244081a26550011841841040024481c003a085403462501c0c5080c200f0302e44a4840503c04c15070000c04050900ac0035072600e032254800e44008190180002200f4411400c0264652102c07500303050050003904d00208141c500d80c4105214084144000c1811000a0741c83c04020f1906c01000d0364481d0344406000441100c0003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 117873255 1250 117872005 117872009
    0x60e010308030f180a14010b0907090e07030614040e0705101d030c03120a02010605030313081606050a1103040b07290c03061011011505010e0d050a060504020a0807 72
    0x7481069483c038001181000b080e00140007994185611056900f40580006180720321641010510a18881141d40203006100804010741c102c0d42e10010040760070b8214000c9070031a00c0c4065902c42c1603031240000c4007141d42a00442510900060410314541003551010b05403944030b100715521213403034800180d031079480700c1d00c50f20005900540791410003400361510011000d055006081513918140001c3d1120f82c100c2184031008404070361825180d2007504194010075018094035642c0380c4603010950b0305c10041c05a0040c4e80700703e1108400780f0301c40c106168100c854030396504d810a1081c0000b01d030144241c0a425215100070300c0302150f42010200204205841240c0ad030182e4103880d0a040005100101d86030000c01d00d080420008507501c03401c81e540300504035400b800e000c1c0c131440241e81100240e42070f40d04d550702c7c102081e070807000c03800c0d000800c0c0e130001d88074509900303102010070544c114a0700e00100303140c02c184d06c6000081c0c440c0d00000c3e0031500c0206480522078407080054506101e80d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 117874505 1250 117873255 117873263
    0xe04091515050103060b03042402030c07120e010206010b2a010f15030b01120201030f0c03050402150a050d0c0c12030f0b0d1a0a020c01060815060a0305060c030703060e0103 76
    0x9440c0c1c401c48100001c8180d0010102802d0a118807481d0032001d684a0100030006400c051801680842c00c94290298001b87c4402d01800c649900300f041c44400c05d6044040d04032510080000141d00e010b000c0e544003aa02d000590041005a00b0500c1c016920741101e900d10104102c1c50001c2591000d03140810036440d490203000080b000300c52040c480039619403803001040c030400900d052010901010845054a050320ba100d00403820130700c0101c0083c480300e1582100945020070751300d4000d9043d080140079500031191009440b0031905102420311410b034801b404902c081120480c0c42d0b86541004250100c5c03030a045240310300540341c210490b140c1078580000203566030009260422548a400c41d0000d0a44004201e2440c0da5251900b000c01d8000c4030f00f420b503100380040c082c811240c046404070480e180003401142d96940c441075451000043c52040c6000c203600156403070a104016130100d0350002c1c010703c4543c0303521200c2800c507440a840c1104040d12140049038407111059094021485 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 117875755 1250 117874505 117874511
    0x503070b0d050703060f09020a1b030302130e0702100b0d0b070f030e01060605090f030c060d0c08061e090c0d1b0219030203030703020913090c0503100209100e040915 73
    0x815103840c4202d071402031101050604c0d00344244944660b03480d060b000d5404038071005950350400300c4166916000040702c01c80b400040c01028003050b9064014107017030310018526030301054651202580c041e038119048001a48980108180445603800151500c0e101070f20310007000ca0f00d910349400440044800704003140e2200d04414156900d44147d291050b890f10007004060f041c07060040c814410036100520a00405400f481c0310340d0300748090015454010051036540c144181f0f0740020303000c202e2152020840342000a401802d100d032401c1d2912116072050030700428400108115050042d00e4260800c0b4103000c0806105110710980c1c0d80d41d041071717081038511502042d000b0302e0316030318024508403081070440400c0002c0e000000c0c1d90f04000c5034203000d82c848002601146807040400100c620748c5003051003840a02604203408400d80c3c0b410303020740c1c218440340e041100030ba11030440003541014245502c540c0d03180c0310720f0241c005400002c001050412003516141d0700512030a040401c05c5903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 117877005 1250 117875755 117875767
    0x414070f2a050610060c03020d050a0201020c0703061e140c0f0403080c1507020a02030601060806010509150409060611070927141608071208120906040201140304022202040503070b 79
    0x4c2d41c2c41030000208604d00d0403041d580c02c541c0d0002d465200d10014042881408505800154000c0d015291400d20100859405038ad0700c0c10050003600203013034a018240b00001c0300f48030a16040c020349010106d60002c0f00c68580325501e0701c030356940c005810300d51300410600000c400074180c00700424028a00c40300070305c00c41044c40e1a4004c000c001821100a41d8000c640303040050b180410228116041d03401c22038511396603003006950507c10311082a500c020260307030902d00795a11401501c1603032004034041206a450310010788902c405002c28031200e6010074401c10900d1003540100035070804200848044481145c02c4500038002c0c01400c0302c0c5502e0240080d45040c10800c00d101040028280c4442207610f4103840c00c0d240e00c414024072185c03058000c4440140a8458119a00d0880d40080301e20780c1e01d0888405c0b521a0b1007540e040380080c803401d0740340c2e90322220041900d00494008190781204100d800050f1184180080c0d40d0080d10380030b110000341c07a6000d000c004009c090400c0c0c405c0d6624 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 117878255 1250 117877005 117877021
    0x160c030b010f0e01090e100e01110a020109050c0d08070f0f02060c0307120f0c020d170708040806010837050f0307110307060c0f080f0f07020414070f2a0506 69
    0x1c160000c030140342c81c190802441b0000040e01c0b8586a105c2c44001406152084200d40036000965400c2e954100002c1d50103010769055000c0c018447c0117009880d0700c0c010382070400100500c002c5000d00450014000000802d00c031310b20303800d407080c0700c0c0880f21b40c4141182d0115030290081081c42001d50030205200b4140702103035503080d2105c03140c0c1c5000d6129108000e40540410b503008400303401851040041e20400c80f0141c1081110b2000940e0561205410301e00000150300ca030080c1c086074043ca40002070790038000102c403841d01c003c11020941c84195400f01481d04001003a03d2540042d440c0300100100e0818070604060303101c100040c65a40c40c0314104801424251385086000ba449554204645540660614a6258030201403000090ba03802d10003400e000e0000e0346203040c80009034520800f01030b80000c06130343d0302c2914140005022910041c181c030f0000c41d0b00601040c80c3c94420345180d40724006a80110740c0d580544680c20705010350018540a58030000c41d1142d0003002884405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 117879505 1250 117878255 117878279
    0xc030e0114040b090105091c02010215070203040b0c010b1201060602010b06031014150307020c0a0b070c0e070c050a0b0609090706020c0105070807020916031a06160c030b010f 77
    0x1090203082440301200840d070301088900c01d91186440d01440444c004445038814021a01400da004081c8001c40068490501c3c0310409134208034098444c4a840146000d2400003141c031881c0d0b190065800c29280a02d4811540d000f1916100295640d0650ba6030341d544001c034240e140b100c9540000350f00d6080040c0642160310b10040544a450248100003044150500c1a000e403141c0b01d102185800350f80021550524090184400300c400100401480583c00035008020a504540005805a03640b4001c003041c801c070040a041d2051080c401e10141744c1d20a006c64102c0650725051520740d885407621030400302015800c0b50584914004d0107202d1402d50319a07500014044098440a403411501a5440035007820681c10310001050900511002109444a060300504403500320302d01070801c45039060100b1001c10100e80f0700070109030380c03c1c64060009410311001c0c0000d4980100902c141c04010703c0c824044820340c8000c42d0120024084500c41c03402400003046108550741400c1d4203540c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 117880755 1250 117879505 117879527
    0x310080a06060303021605150f0f07050d020c1c020915031005010512070806150a0306110d14101a0f0c0304090f020711060705011104060e04050906070906120b030d0c03 74
    0x9056a00c1c48244a25238911300d04c070045005003d100c50350349613070b03450129560141c1801c10450390000300d05401884000700f4007100c200d000b6400c1e0382c507083c0c1c5d12041110811503403016580c040400104c6100504100b449160072000381c078006144101c1100002c1c0c5400c803230300c9010f1100d50b1a000100700e05d0405c401c14150070321042c0301402065062800e0a40d80d003200420310900101c07014a0043c00b501c6020324540a10b4008006102206030900b1000c035640c4074486400d503151a10000101c00300447c80380c580144081200d181e5881c1c50924480800044c2516a04646c0700421484807400c010600030503000200c10051600c40e80303403074410400c0f69030340424140e40500410079800001c4000c00510540e020131900c903a1285050f0902c1070050140003680e00b100074000402080b40c5802940307240000c0800ca5090201c0c1d03642c0b05401da15080c1c2628050085002c8a03014030205000361800c2903400d41030440028404004000289482c44200002020800c490310050a01d40e2105c0341c484 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 117882005 1250 117880755 117880783
    0x90c0a0810050907120908070308040b1008030f0d1d0106030317090309091305061906050d02030c0d0203160311100305160e03070b0d050f010602070810020310080a0606030302 77
    0x1820342ca40008950402002480c00c0100b11070a00303501c5c050503255101c0801d40c0e4200c0341b0680c0b01c4010340b50140c0b802400707440c1914821a0100080e1511000004400907190010055414070845407120005a0010490040c0c903540f0b41d500c00c2030803048190012840e48104c800030a003186141005080e8085003065414440c40003010480003c00010440d4210f20041c5c0e60340d00d0542d1407941682e1000007a1500401c18003502050082c1c10814209607003401241c04403c0200c1c5640344200305200420b460001d4040d044034401e1300c10b17441d001924101031400a03041c1c0c0e810b041c0303c1c506458001c4840d003084a40000100c041c402a0405050003040140305040c2003045051011000914140c640065010048082c003514000d031030601511005014044005484401480d110b83c05400122000c3c0c401c82e6180f80002440e0703200007402e104551801c1c025101071900c600a070700103540010035100300705c0741e0a100010a50710030406010700c039000d00380000b8075130b045140084c181400710071244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 117883255 1250 117882005 117882031
    0xf0d110a030b060c030403171b07091a0a09110403051501091107030c021201020d1109030f03070c0603050a14011707090b100c061b020f060f0709030f020f090c0a08 72
    0x5141100d001080f1800d0b2900403408984005881c40004400d11803d02144271000c004c4c0c1105440c2140010340c1020fa841c0c4040c00e10011704400c250714400401141190b9005a402008010076115548195054a040c0c10715a1400d0703141c1c1c881c1c9140400400180740440410b00041110500070310405c0d800f8030468030020310f819110345006000181c03440020f1f1080b0703801030142d503100000b5411a240091094070a00c28500e009000e00010b40100503060b00078090343c0c0004881e2000401194500d42d4801c2040c2401d5082210440080c03500070800d8401c1581d800b44511500607204e905030003450729800101c0f030b2004441050b800d054960b48034400072410403100340302c180e403500c410041000380c034941400741c04114181040604200304001c07a0b44d4250890359488140e010a082c440c2d41b0614003158480c3c1c0700c000015000201c01c031515400540050410b01c0018607071032a403030300b06000800651407010b400d000141c0080c02591917910207407000500140303598000c1c406a500080c542100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 117884505 1250 117883255 117883267
    0x8091605090103080a170108010603030e03030c0715020a0512030a0b0a050102030306010e031510050a0f0e0406110c1e1501031e0c0e040b01030c0b0306030d050f0d110a030b06 77
    0x807505076801804010501c880c040742c18185076100c2e0b011201244110504088156034500c0904c0c020040743c041900041e200f001d1402541c1000411150b006511174010081070785024603903c0c0c0c8180600f25881140112124079001c0b40d404c01c210703803103841028031559903400c0030200042165210707500140035581d2482c04010907070700070042c0c90341b000007130030003080c10404080040d085c02e010010881e1100f03017000c2071212404004e244c8406854080d00e03094100307600c403142a51055201e1140b19140f0325007400280000b0070b07030341040d1000164500c0701400c0c0320130f50701024104194104080c5641400740445d00e0380f03d8042100d123500120f5500001e2035941942c851911100d501c2c440c4c1c28034100c0c2c0c0c00d600c60402c4194110030000304181c8100320341a0403d49007034846020f00b0b1009403041200c554010603800400000ca90140c1c400034000c0c00389011441c030a550503002418048403580040c800d440c031581c0c250240d014141c3e070f20224955a10300c45240a001c0398000c0e040c041c0a10006e00072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 117885755 1250 117884505 117884509
    0x207080912010c0e040c0c0c171905070618090e0607090f300f0b06030715200f010c03020702040c05030103020d111c0302060a0509062403070902040608091605 70
    0x503400621010390340400c12120800095881c180040d40041c6125665034000609040d107002780080c91a184059843d2244100d50300e00780084840300180c910382216204209030341c0a00390310203921081c0e02c0250b00e2943e0f0b401150007140c07004440d440c2c45400210411202c0ca902c42140c4018000c2031900080389820300c0a582c50040306601018104014a9403420040580360340700c0d11002d031320210015100051b0300d010850200d064548a00034899100c020681c10601e000c0113800f5551545c40790301e60540c2c480390382600c9640306c8105940c0d018102c002070b8140820b008203407a401c000d13100581d50b682e0b644148012034112107082001c1000c2880184010b0342d9600d80c14011a4024400802d0030301c0d240002000344000c46000c00034105a902d00d4020550081130440c411181400c081205a50707404080d51540d00c1101d1804006488488480c032400d107200001444ca80301804882d001c03916040c085d412a0b010f80c202802148094081101c210030402060320460651405030054501e0240 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 117887005 1250 117885755 117885767
    0xa0504020306070513090207060209031603030908010c05030f1003021906080901020f030105010c030306050315090f06010510030c1803060603050616020a0206030901091b1a030c03060405040f05010207080912010c 93
    0x1c0d100c0007d4000030060b05002035601942c08000000702601d00b011060a00502c0c40e80f0381c0e100403030102c1c1103403c000410030030611030040825003544801e851950f69511908466400400388a00307003c20350f1000c07016854800e481080740750390003000003a15050000c040c00c00780c0020140c0c01c00340c0c010003a648038a480c10b400d5030704441080c02c0584006096107000d50252665400c100e0f00741c03195101462003107441002c070301c2c0a42c0010003904c0c3e10140e00454292207403000d0042c40c1c1c108440d01c02243c4030501c42e40c0492403106080c070700591100011100003090444075401030b070303103a610b6510500900000f0312015130401c01a5007000e813054501d0101035128500310034061b21070300000c00054480d100a4000e070a019600050348080100d10340403c400c5e11001e4000c90000c070340c41020703000c07200440d003013200c0c001c00311040c04500b181c1c0c82c02c0410014010042c003c40d02286201c900900050090024243c51489100700b2500d0307050f02030522454904250a001c5a40c0c108030321400303c0b0707800903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 117888255 1250 117887005 117887009
    0x110a0501061e0f0b0901020703050105090307151808090427060b0307080c06031506070309061d090f0a09020d0b01050103140402101409060d090c050406030206030106031a090a0504020306070513 85
    0x40c6510384051740c0040c3d00700410707a44003038429401c01042104c07041000c001421141c3c03040c0d4464066140703000960003200ca0340d1b4a920030100d0366030030b00c9002c903004602802c110704000300081815400390700078203810301460118448920079070b40032000304043d1f40907183c1c01803400c0c2d008100031480d0046499444011a4215000d500c001003c40e58509074034004c41c0c010300c00544515038650441c0380c02400360030503214080000c0c40114402541c0c2c800f04040e0b620041c0028050425901c2e107045288800707401900d0500400d0f034507650030005848000340c91500c54000c0c0d20b0030701590300d000c00140a0361190070f92003641c00c3c02c1c642004010383e0744c640000b035500d20500e0001c3c04855040505003a510402500907803081001c0780407a031003030541d0811070300036114003900d0241035916028030060380d807030740030081d48104203000602c80039100e64029481603508000c0b4011121030103002c02c0d10068181c44196209444004202c1981000c101c80fa0700300140340b83c164944903019500d10b5400c1114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 117889505 1250 117888255 117888269
    0xf050c0406050c071505091305010602340e010311010201180f06091736011214040605090f0606030c010f1e110d050a0504060e01110a0501061e0f 64
    0x10400c04240c3c001008480040d216041c01c844103910000809451600200c64240c4100d0070f001a4890425071401024101c543c0d0f50020306d8410100001132018a01e188000c0c0e040c0000d00358440080108020040000c1800200502e031a50460070000402d0268070301c800d0540e810440700150756200060008002900031207a14a09152440d01f034000e01418080a003821040c0c940d20b03244038075000d00604a03042c3c0060f00c604040044040d51008c40c00d5041000e90300c1d021008424425400388220702c0c03034820580320001da8190f1074000003902640a98041d0f50b416900d604101c0154402c000800041d154035009100b02d107012700019030f9a80c03c0d128540e041004c44000e001c4502d00580c80f46c08100101e0051540b01d0b40300e0f141c010240265a51244140e00ca414089000c0900034001c4545e600381c0c5070350b660710f0142040c0c000c0c1c920041d1007040030b042240f600c0002640c050144102c01d402d03071041e8008101c0d40d00d00180f50b0442c00303001c0f0528610081c4054100f00c21780707542010f00c04985e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 117890755 1250 117889505 117889507
    0x70b090a0e0a0b0915010917100c090801091a0a14041101140705010903140705032205061318060b07140f100b0a06090305060a0e01020c0a05030d0f050c040605 70
    0x651904a0240c10b003198104d13042002d0718140300c0e41c14402109040041c0080e40c8030141156544c900484004070301140105541009880d82040003040e000340d5810ba101e418800041541c96968038212045260240d42d421105410014120420a200d07500a460010140944404948210700102000e4001010181441d070303070b42020f0f4083c0f00100000704180c003c070b944a012500b4801d001c0c0c1502ca40c11000110503807001251454144261400c0d01e0b0008001e5007028074043c00244402030300b10040e84101e04403800028540d07107080c000d00c000700140b10302504051401d00060390404150b1240c2c15000d0a0000900c10307080c44006444442d5080181a2005c10051100c6428107a52000d61140c03400703040c40486003011390390480e64103940192810070280395603810842d14991a4080288150440c50105500399440d82241045403078010005185c111304810451811071200e50480340c07a0004240c007070105480b4825520001041c0758140007603c1c00c0751070401944110300802c424000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 117892005 1250 117890755 117890761
    0x50708070c05012903060106030504080f0a181d0106020606011403130c0312020c0f0603070309140706020f0609030a0c02010c0602041e14240d0219090305070b090a0e 73
    0x1003d4201640000f00e244a185401151902c421518100d84da0580c1c0a44901400056a1413291041500c104e412146131401e00300c00034051840f96000d5001036080218106014003500030b100203030b0300281901410240e08450a10141d0381c00d6405034810825900300c030081042d141d0704485040102590700202d959203646100140103400c05d0351300054009105400d0210030484400b07042041c030f41a0b6021035180e100d02c1420801001801e2940640002052000c5640c4c140241c02c000f800c2489140002c004c40c2d083d07103910780740003103a81c014001640f05604041c1c122000340315050300311160001444ca4800c0c546009483d2145201000b41000b2092a00c00180003007a41660041c10a4000501044a058046101280700f038011505107a15540c0c64200e03a1601e000d168500b03417002d200480c81120300c601c205c00c240e0400742020180039002c12205070303d8002d50a002c22000815100d050364141941400703868450250454012800100011080f6584a4410604944ca050041c6c59203503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 117893255 1250 117892005 117892013
    0x90219030213020d0f11040501080a06140f1c0302030301090b01140f0306031009060606030b180406050a1d01060e0105010207060e0f0105040801020307030b1221030601030b0315060310050708070c 86
    0x44517042404846140c04090220010070500910071224243d89144060f240c2c601d40d802240c0c40e612880c1ca4624003403c1021850406074024403911600a00004041c0f82d2480ca940112884200880050300000010322410310a4801d40b404a00d0a1804025a000810302c1c001c09100741e09401800c501d0100004d10641d40c1000807403a00040e071441448015050718001c0040c181d10f01400d401b00741418180714150402c40c01c0d400340d0210f50501c840040e01c494031400d00410010700300c04a419280d4194000314221610704c05c0081058200000300746180c4400c1812441040c1c2116045401458040120a512846408101d041215507003e9a00c010006844910440d80184415400401040140c6405a01200540400b5a500e10101e40280202c0d502e4440f4107107100f0705001c0020b4900e00521503407016544c80001130600294101140000a142081c2c08004940c040900741c05c10403982018060b0301c03c900c400050a00c000d04103030381c0c050601d00c1c2c002c0c601000c2040da007160200744 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 117894505 1250 117893255 117893261
    0x60c090d150507030c0516020f0a120b09120c10230405010c030c0318060f0207020306190b03010917030714040605040305070b0403050a14160603090219030213020d 72
    0x1940d030041c40500e0001c007400d03880d006407404451040100b440c19000a014502803021256070a402003001c81180030b0035402c0000005000f0041a00711f69882c2c030100394400610703030901540b801101d4800113840c100300313034500e424503814140b0344500741408030317400400c3c00292213120840485408108818401d4582001c0c4403c07800d42c5140f48134240071302c8107110043d80110f455080940d41400840700030f040c1174003503886105640012004800c41c000c04205507511410344840701d070b8805407400300d054000a2401c4d80540750002000380132402083e6805041c40340c1210700034280c1c001d000400341a101c2207005e100041100e04602c20000004030190300c20b240545071421080c401e40e40700d40d180e88004203070390018082101d040c4610080801e900c0e44007401c1d1021242e000b001052038016550320030100d5803080440d0354140c410b00d40c480c01580c81d41c00c8424003038000b1f650b0014808001c0d0041228211607138140e4540240710240030b2000d82c44030150358107025004640581d0b07541c00c002d0500c0c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 117895755 1250 117894505 117894529
    0x10c0f0807150501051905030601091a0d08030f13051b0d050a0501052e05040b12100221040b0615040e0c040501020d02030406020c0f040b0402070f060e0a05060c09 72
    0x70002640010b1044240141d01140c160f800641d043c100212400c288010f4442450245a5041d409000108680c1560f504220780a40d00c0b203016139103050100c2c1c0840e03403e0b8894001241c03460b0b000300400500c10303010400917038442030b90042ca207031605290b00d400d81c40c0c0c1280705007115608846603403403040c0d484281d081c18020394003104030388824410342841402000240c3d520100c012030030203501140c1b120681540f00e00b507007005c0c2c8180007a18050800c00284003202417130707402614224403010085810b0040000c485002c98003d039840240307203a03102d0034040c41c120b03064620700c8810500020500c00100c80c0e40c0003800362038482a030810842003242038001c50f4450a1400c810004029442d004038028204440b03080e0225440d0400e00042a078803400303903002d900f0051780080304140d0715203420110480c083c00007400c004ad50201040c04030b410303640b010324259030b006591038002081000601c038011a17100e601000c0c02c1c103841640d4640d1f403112005400021100e40c04501c1512681d210f0b0710a0b00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 117897005 1250 117895755 117895763
    0x130f02060f0d060f050303090109050f1503160e04061203031a1003020d050601110d2607020c03120903070308180907020a030207051807050c120f070c05030c010c0f0807 74
    0x2840d0420165948007402c203d001c3c070441e10301000400640ca04001023030b40d160f00416110760551034248400e0040c88400d405615a0100c0407018203c00d8cc4080b20045000e48071582c4040802d440031a0082c1c1461442481140035500e040c00800101400d00c0c0010310b56941407801080005048503e0301501d1903075107049500030701c1c40340e00c026030315015802441c0b05101ca45003440710b560703450700544840001c0c45034010660040700c0500181e620a15101c40c001e206000c494004030760361648012094002c03079811001d60303c242036248980c981041004a421000c840141c42c140401c0040303503c50300240f0009107904808108408550420440648059006051620103150030303c4001c3d81c95050050a401500841d040031400e400c2050054a040d0390b07403a98505a900c9a09040300d103075010440131422401525204440c0300c00c42c00040c00c0100c1603018107610359500b42040200030700140c1c8518840e03804504c8021160341c0002541c600160069003040403c14141410070702e034413610b08010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 117898255 1250 117897005 117897007
    0xb010c08041211040e2107060f060305211b0f010f060303080906090601030f0f050d020d1101062102030715081005010e2125090b0603130f02060f 64
    0x419a030700c000c0c51040041c3c2c01850709080c00c1459005000845e60104220744154008031000c24401e0f080c2c00c2003d07501e1852070242d5240c807040b074840d01d0440c1c505c80c080180403a11128100f00b072240030404016403030380d110756080380b460146000022500c20003103850041001e8a07031444070f0b50018448040d001100400900c05111805405001460b19000032004100060003040796804000f490603c9109410300800e426400c540392110645282c120890701002d44007200d4001400071300454406103060b8001b4003580450403000750045820a24001544c1c0c9021010070011054945541c880e441a980088000c207133030001ca820406941c0148000c280d002000e015440d5001603598031600c000305d468208980c541004480c183c6100681c1e036030140c6655055004a10020b2100e10041052012241610a03500d100b011050317040101c5007040100110070003101c28a0300403c0b546040403641c0314503501d0010160050391000103805480101c00e10000402c6403204422168103034841051f80f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 117899505 1250 117898255 117898259
    0x5010212090601080a0804030b130f1a1608160302040f140a060804030c0b0a0612030507020a0602010504020a03060507170a0c111f050a060e04050615010804080307030b010c0804 78
    0x3824200d24180c4034200948199400003403000c0300401c0d003603841c60307006481600d040d1554031381101e806070203001100708420900588001800398031580004610560210700c40003401e003103c0040b000c00070000303441d04000f4400320030705650080080394085200d40303072182500c006880450080c00b8540052152821521011406010300b00c080b1035520001c46407100e40c04c0d00c450085030b0b23040301a0b4005020171a01403640307002071450b41003580d00c042e1005000030300603912049181c0f40420400250003203040000d8010960500300c800c1005020180000c0c4040c0c00c080d4085101c40c2c070f03a1302c8041c041c20741d108082410a4450521610f44141c620281d000d00e04003106610010018582244080b0303491112000900c9000714424003003c2071016107030510020960458090240104107441c0c0c20380e00c00011500168020074039000e03a000b480105040d25043d4548031300400144042030501003c0010040024069000c03241c0c001c1540c0f80101c3c650050340e0050b20314600400008002c42404540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 117900755 1250 117899505 117899527
    0xa231305031201030b1f1211030d031a190510021009080a02160b16020409080f03010e070302072001110d050a020d030b0609040b030a0804090f060501020114010e06030307050102 78
    0x114103a034007901345028181c031003440041038114009613201e818030f501c00c010887d0302c08440721080c03810301a10766151034203210000207050100f0b04520b070b000700b0355541034204003003c0010302807400c0c50252500d04c0909044100100150340c54400d081c81000c040900c840c5042c0f00780485c0a400c80c000e441070100c00807034580b00c040d540008807050300501c510342140d03a6001c00306404d4000c030b03250617481e1f0303140c01c4044200d00b0884584813416a003040d110100b010014030601c005001c42c004950300c903500c1c4e5050203007888804501600e0901054011300c640008181d0b14445401c18035402c19022200c0f000c210011b854009012550f0b40e100d0080704030080480d604a401041034141c0c0364203582510f44560002e8003200c11080030795410100601c100091070415034032a01074080000e04840c42501d040c4d86030402903000d9009081c1140c0c8840040e28440f200b80180d00151000740028440340c41c500410a080b103105108550100500c80040b039031944041c801ca41f0f0064125001759a54600100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 117902005 1250 117900755 117900787
    0x1a1204030f0806060324010201021209010501060e06030108030a0518030f06160309050c1504080d03020403020103141302040510050d0303020403020a06080906041b051003140a23130503 81
    0x80d140c0041658100050038a2801c841240d1042560110f41d04900700250120340041c403201b4400e505565080040300960841e021000d4800c147c00d900204041d8140000141450403070000b6034082c00b401c1c00188100f14000c401d80c0e4041240b41f40c403e840b90711003404150281545200c1c03d400d030041c0075040c0d0400d000403415511803054204540010364000c05d0460850300c1206000c0d0903030b003114200c00f5071458000043c441c104038001d5058185078030382170517906040d01c00949802080d0300140803c115601402162540e500d00c0f04004800c1c58000e00c3c000b5041848100207104030754481c00a0103d83d003010088010309405800f4135a86041880d014000b90721900099210381342e009800030b1620b1203107210030f00c203041510180100703840d6596541014030050000800c0100706100104150310303143e56649400301c681e030740400d015141004000314201d024200d0400355040144040c8c1100241c20100c2c03020300c40518001d07035135403003290154000412a1700100b15003c00a00c1140d8048055 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 117903255 1250 117902005 117902027
    0x30418020304061b210f14071707050306100c0803010f0305070b04050607020105130b070606090c0c03020d0509010e0406030807020108131e0201052110090b0603011a120403 76
    0xc0d070200b040e5500103c1c80000f1910600e50a40007459500c0c412401030008840501201e2a17000c0c08510a00025584020b072200072410a9440b9003500800c41202d501c07040c00d12450980c2c81d49440b1600307260300020b00511000303080c03d0041c1040c2203c0d4014500c50444440c1c00d036001a100da0f281d5848207042c044208680c40140c0c0c0c0d42c0f01d039001c0811810b881c0011a0201c4d48004d100c030749844c81c2d030760054449412030b130417489100d00800c800042d00182030700100343d40da114081c0010180d0800d45a94103c44c0714112140401c80000300034400240c001030411105030082c280305071140d2032200120b808502050f10300b0340203800e1040000801c50300c203001c1c10090b0301c01d0b2200d018030f580c0c400c40c01d102c054a01001910890300001d0100341040d40d80d0140c040c03e4010301d4090311700103607000d0701010440211013041c4220018010010580c88454400020300142e03803081c80341c05101c40c006070b8bc0740018000e07145c2d01192510900c0c00504003000311604440240d030750340304518060802414000c405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 117904505 1250 117903255 117903263
    0x1302031606030509010e12070201030e07080304181a0a0e091e0d02060f040b0105041107140615060a05180406050312090301050c0304050604030c02010e1e0f010302040b030f0405030418020304 84
    0x2040380420031b03004c1104100941c3d41e003161402c10005400441c0909600705d0303c04c541e405241300100e5860030620042001d000100c550314800150480300d5000c840c0342e006010a414006a60840c143e40d8200220003251141180c2c4051501c4441a03503081c268030b801c0b04030714444880300344844010082507030700308400b25800f0f40e580c80d9106c0e800410151350440740108180310810060100d4a0701c2c0d131105180b86c08554065003050320660b41c43c4c00c9208040341624195100300d0404c44000040300c26444220815a0480e003400b4119401600728000c1e20a04500d104407064444455120b5a010500405004044405102d050400319001342d20031006103029500700030000b40c980c40b1540440e4011644540100482e5503540c40803a076035100c0340d8040741005050318403001159200510403204c4084610480301c0d5812100800c070b8039200f251607035410305005010400442001500b502c1d07000081c0d5100803c1131b5141e203011811842180c000d1812046041032160040f1440c0e806544034600c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 117905755 1250 117904505 117904511
    0xb0402090301060315061406160602040f0e040b060a12020103091103070b0a230f09150d02041d07020d11030c120405030105070c080906090109050d1101081e130203160603050901 78
    0x3d070181d0712031808084031031f41d030020010041c41c0f1064150788448226107018410043c18141c03a0010940300090750f9000307170620400c00f42480184904600c1407a0040c00c00c4a01420080c0360142c5000d40100c08203019062641c1c40320302805105c4645203203000840010305586e170f4a615501400450740061a0f6a00007446229108a030600300d0000d0301800d032500d042d0b060034241e00742c030103580c640e00151450303030004034402c0140100030412303015100b11f00c440c00b00562198140b8140b041080401241c00001e02c80c1e2030b040c80305083c0c0100d0b05500ea040780e40340054400c503241044030300c2c62007098003203203240c441d82c0c4e0404103124241d000f40059507070840090049448692040364200031511020f0000f060030054080e0614244000341080307403060400843c5160340c2d60003e800e041c010042a182d001000c460030500c1d41e4000016507204103000e0312929548099812286062401000904128101c5000c0320a55504200100110101c1004160041e8880d0070080141c50b040d10702c6041c96003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 117907005 1250 117905755 117905759
    0x62403090309050607060212010b0c0d020109020a050f0d0b090102040e090d02060c0c070f030506040b01060c0f080f0c010e0f07080a03021f060f060c03080105040504020d060b040209030106031506 86
    0x211901428840640541c2c80e546034038103120400c9825844003100b1540a9820040e0800da00c01e500547c50003456071070070386a00c032094013800318104522800d00004591500210600503580e60342003109603070341035460300d032030310f010303502160840103034603000307894a400c0d217042003e2160150000e00549040c884a02601c0d200c0840c859610303802c401c0d503103000d030700300400040010392440042c205c000340103000c0307030312199541c4100300218800d90030a0b202500140200401d01c069521258018400740c500b000c1ea00e0741d592600011001c107118018030780100050010010504c00090702d140510060003000301d0116217044d190b6031401513401d0500c600030504001101d0741e020810340b0380c0c903070950080c1c000c03070b200301541c40e1101e400441c1001d00c081d919000411039035036000c0d040000d02400c0e201c944102c0d07901e0802811400c0d05900c054815418102048010b8441010f4881343c19400200030501d0400c0c240014081e005180c2c00b10780661a1190000604c085440400c3c4680314180081040c1d42e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 117908255 1250 117907005 117907007
    0x903010b0103110d050403020c0d060f05011203051b03040f1203080106110703240204060801060305090a02010c030e040902060d0609050906060108041e05150621190c0503010624 78
    0x40703a1000841c00103405000d8640c1d44d000c1c50b000281c4c058400d1056407a49404c02c4c0000d00150840030055429903500d500441054690f0310600380986200d41c2d81410f116501d90740102903118140010b56803003010b4120007020b09080003a18040d1220100f01803a0342d4407031203201e18284403503400b07030005415100005450f03401850490f2802141c05c0181050604549071322034a0051308185c220303200d811300c8103030560030320340e2002c0d0001d064a96221601549071031002400d039080034100300d0f40c3d43c01143d00500143c0c2c0140c420107409915050980410900d640060014071000c90007a40001c8000fa541e00659a194010f0f02070b1921341508125a844201509035204401c40341240401c400c6804a0301045c030300c0803440740400008107036410290490390707810f00f4404210385255004400c8014000e05140c0503c040c842d0b01c03960809003805240c25088184c1d1201000410011910010550000c0c004240c5009002d000c0107802803140d1503580c1c160f4551404d00403a09080d211180710fa03040c1f81 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 117909505 1250 117908255 117908261
    0xa11010b0a031a130c051009051009050a08070503100c03020d060303020708010c0503040818030a060e0a0c270f060306180b060306041109130b0f07020f0705091b0f0f0903010b0103 79
    0x300303401043d6820020305003002d01521901d0380c80b47c03000340140c994000400c8c0d41ca500402d28140c440c1c1c3d440380409450007003400042c0a50350000003450f0803110060180e61000034402d90300024403080030582c42c0400d8800c2e002032151898a07441e941c10701201209054000a800e421034809070020003620300544011242c5010940307006200c03a100704503041d002007009001100c2c15000030140c4280700125a02c0100701c402c2c01d1303841360041d08620b05080c2032180340003003900201070740031202052144540134511045044000311040a60318840004030701e6040d4001c402441c1d0100c01080560000000402c406800b541d044030f404440030006034541c200441c94900071079000070710604990322030003008590b8200400d0440c0c1c000c2c428805402051074105564050b440c0c1110050480c104500001c0c01e149159074030541950180c0f80810168842d84512688036222410045212107144a48400c9214900130a544403070003251240c443e500180c000c09c030000080b0000c018a46400d8015025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 117910755 1250 117909505 117909541
    0xf041b020d0807020706020c060903070e01090b0f150d11130603021914030f06011407060c11060114120102070605072105040b0103200306190509120a11010b0a031a 72
    0x1030708500907808c4103003407400190102040080541c0c4410351990044580c4040991208855a0700d0300c3c210312246c18400341000c4030390000c1d2600003824a890110311050310860800350243d554600c014000f10302d2000c03d03550b107104001080b0304960b5407660010082d400001d2103504100c11003a064170483d004058118001241c103000780e04582e103103134074591036a00042c40241400781d202203095a05408000801c41d1910409001486c0c0c4819400204182d080d4403812110394040c00050054882d44400d101c4150400c0754045405054800b500f80640030b4446e0040c0ba00303043c1400d0203503290300182034440454800303172030049550351740a01005541043e82d024080850340e00041c004103604901c00075191000c1c885c800507e05082000c0703813601e402280e4215698102d55062500b00105010b040c2c4c0141d1010010302c20240000300c2051a80f080680c0c400c1030004020400011200a42010340d1000d0020450030401340d803420801d00c5042003640c000241c0d81d20100261f0248015001104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 117912005 1250 117910755 117910757
    0x4030203061008061603020c0d0c0b0f010e19020708040e070f08042319060606140301030213020a230301061e020a170c010906090203010b0d0b04020f041b020d0807020706 75
    0x720b501c0d204407503202920303095517000815130200305c51303a141001000941d90390b8605039101403800d802c504040d1104403010740720791100680c820041005640141180e50056901d00818071042004203154009100d045001030001e0404500018140070b03605c8003501c641c1d001c0c2c5a09101c207502c0081100c05030002c82d4020842e40c0800d0003180068040b05010501c0c203240e05c200c0f901c0c00281c4801101c0b4100310341c402c403415500c0714000d210140d41310221882c0000003480b41e0341103504590000c0c0e19a103044039a424020350100b0030f03440c090300c80c0b601d054659039084404800e40345401c0e406a55940240146004202190203020380700c00c8600c4160b5414405601400d82010242d841a07200200140780e107495002c28816128008cc007032043c21801c5125650005101c485881850300399500384805c035204500340c000e00000b05100b10100c41c0e1103541280e0072501880f0303880004000348a02d0702ca08000072901038049076115000140c5018084040d183c03c91642c3e220b48049a50340001d000c1c3c90 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 117913255 1250 117912005 117912013
    0xc110f0d180315050a0c03090308010e0c0f0403060204090b0609030c1009150905030d0302040812030603011112101e0504020f040801020a050d0b090c04140f10020304030203061008 79
    0x51941c400c00c04280c0340c0c0200c0030700005255803503c0d81901c991100a521042550710400d00000901500c11002550780381d003800d0220b180300e13480182c040e030814400c0c114061054000101c60761804403c4038058458614040d49550722410168025081402407401c101e14062104950703281c1501034843d890401002010f0b09480642401021040e100b050414003c0703c0e44082422030141010b0640c0d196240d460340c0380c6a103888101031515204100c0b0301305140c4100810301c0480804241c081e00842c1c0039081b50f0762516401d003c02e00400d90094411441200801d039503c00100e85d02c041409100320002542c80785445440d04801043d42842c400107070200c0c1d0f40f080002c0c4c05c0c80d4000c0c0c1910b00304241600d080c00e540300015401d9038000b44601c0002040003c020400f14100d1042907055001624644000c0c40d000c80300910300c3c400c03402241c881c445480d0408200e981c5442110403040809054203035514035141010355243c0180c04100e11a000d00000503c0044803001e040049486600046c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 117914505 1250 117913255 117913273
    0x605100e0114120708010b0102060a050c040b1303050706030902120615040b04020d090f020108010b16170c0d211b030504050f030309030d0606030e0d110106030b0108010c110f 77
    0x40301c209180702d032800360460700070b01d01d6480300c40083c0f14001c020b22080c0d00203c0c4900440c0002402e10758010700400b070181c030380400d102400081006135001d8030017868810b542e81c02418039451810455a2005156105455011807441e6242d0098051240709442c003c2520003c019855207801c401c84000c08248044c5417400758924041d00156400303803000e0001460041003541800945001082c00c1d565400710600b140b0031568446035403401041c103d0b81e1582440805210b030f101e0710318401d1010b400071403000301d40c503c420042c1d000c541c000340c005030403980001407204c800703003140c110000c138180042019514116099801d000f0b14001c225482c0350040c4000307030f0300c0090340200300251084d155440380d40c4000d0400700d030400046024a11410043d03441e03a54004103e000d450300c40e0071000415050006645542c4000282c2840e400c2282c20269600b507121469180109407503400544404d042c080005000941035010041600280e80d9860011300c80b549101c3d626000f40304850050f42c01198a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 117915755 1250 117914505 117914519
    0x9060806030109030c0b0a02040512010b2e080a020409050a0b0a0503032a030f030f040506011a0a12020f040605070204060509060a0e0c040902030702010212010e01080a0611070204090803040605100e01 88
    0x140c0e107c28080e00050400342c5807800301d9248046c44400b8011a9510581e418281c81c206000340014242c2c40d580911009082c10f140d1041d40d14072007007405120b034003000700d40b184182c0c0c0c0544003e044006801c01071840c0c00d042c210094110000942e0298200010100e00c0d42404030489040d6256051940c4855040848a4400702c001c081101c03035900052069100d20100e480003940030351020b0420100e81e00706420304c00c0c03c09a042c1e0007050200c1344007480a00c281d031440142d41110b00e46090280410b440104240084d100300b8401e13403440e04000a02150315900507000d03290060003510304100040c1c4420a12441ca2401e0b94445c0d40009220000c010440d1203541c010317480359584078100d081c581d40f2001d000c183d070025241e10300582d40204040b01d40004101c119801407210807807505095141c4050301d80c6a120025002e014907485000940c2c4000100b82113032543c0707078054802c2109107014142404150410b480807140e150812010841c07100710400a1010f4403442d42070180d00340d00e0056 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 117917005 1250 117915755 117915773
    0x80c010806031e060123150c1507120f020414060d060302040513060b01020601181a0603070c05100507021506130e06060406050402120402100c08040609060806030109030c 75
    0x201c801e41c10320465414040182c0d00b4003c0c5012040c0d1070f4000c0010f541011011000114040c40c040703c0c802e100020b40071180d42e1180300c00c10014120003c2592101000e80d614249274482072500e500c40150004c2c002c085511600c004504071440c101044032402e2002c10a041e48620b00c18803403d215081419102498518014201003021120020710036aa82e808a01a604111034410800090050000c1440014040c032000300c40c007403000d08155810725a60040321054900121800c0c0c0c1e440d804145034010396a00550f03c0310000308001e84034030344002c004080f8441a6401c58150040102d4034101d43d819007d41c5001c3c60241d0064907518440421700520751000620b89544007030ba605802e11a1000340c4509000c90b204103014010b07529140c006d0109503511076109070b0013144104070303000300f0014a05100b5003240c2d0442d550510000070003011039408000c44406403901000040000f50a43c010034150b0840d4899100c401003650340300205803c0362407000002d404560301d907620300f001a03492a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 117918255 1250 117917005 117917011
    0xe0114010507060c02031803030304021003020d0204030507090c09050a030309151e030902011b0309031523040201180e0703050601110102040b0702030c0a080a03030216060e0105040b01050901080c0108 88
    0x890040d041c5161a15043e0030383d54030402e208003580002601c48210010511400b4491406500541c51420a98041060a54044c0010b0205540410224641885a0103d0f0000c41d08031085070190760312800e8880040c810b5500500100d0700c05400010f5034244903a0307110440340c00d52680701041d846c01c00e040e50038a1403034290004101a048100c240c1c03103011104880541c11541e00010341107854400944002040c1422100c039008180211001a600c1300446040c0ca912611081c03154883c07007107442c054624020340c41c03a0281d4130301d4500109228050100c0c42035000742c0e501d1882d001c03644030030030081001d0b005280205c01c0c0b440006051074046d070860b0750407500c1850300071100e500364020300d42203030401d4101401450000940300190302c1e0410100c0350002c0100c640f007041c0ca1070100403554400110700000c05040d0003081914a05041a01c0241203d411010601403030444c503032102d0080c841110202c6070303001e0400000c640c40c18541e0301c0c42e044e1f0740c43c0001000b40c2100640192281c0d9001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 117919505 1250 117918255 117918257
    0xc0a020309091306050a06080307030c050c03060c0309100501051c0302070803130f05040203061c03090f09050115020a020a050d022413060f02070501031a0d03050c0f06010e011401 79
    0x708044145626100041c0740710303c00b6604026400c08161a181040d120007801555a41d420050103204504000c011100d60980c142084e008080481c50014103214881c110668103009440030042031b012800011403143d248081035500d075600c07000500c02294401c0c0034543e000210200c4000c0028440c08006003a00d010b070048503402c65880035070a15641c0001d6141100405582d41003154035020341c240750140c0000c860941c00c0d882c201c00420b44e002442901d41840e580c00315001030515000701641009080700c9201020b4003620703203241d00d0283c4000e02c07400381d0285130040e4081c0d0062001c11810b070f106900621400d0322501d0001008003c541c80c0c10181c0c0d000803c000901c11a801407600c503040798030070301c19440c2c0b912a4245580d05454083d4804000e00000f0309800e0902075001c80c459098500034240010058240c408185030f40a09280c1c1a070400380140018081c10b81181c003400000c100341044503294440c4555072030f00e411080c410111480002d90040c4005940480c03541128081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 117920755 1250 117919505 117919507
    0x10110405121f1b1409011809060f0f06080f01150207050319061b0c260c1b01030e070902160b151503091b0102070f03061d150c0a0203 59
    0x40084095500801c000c0c1000030255204841d02645002480803150201c5900302a1200d10380b07a80402104d00c98205c1c03140c1004030394044200080c0c0401900001340500d420200401c54903404101e074100310714080d0190140c2441c1d40000c070903204038603c9108441000b41c440d02c592928031215100e840d844030794010b600402e080425244c030b04200315040890710000070156609a0300309001203842c003121840604040e41d0400400341d801403680102c145c3e1107000c2040c0058400302001180c49500c050109100300003078844c0c0d1000c40052507012001010340e1148207007001800650072250150002c3e14075401c1648200031520381a03018142d060075201110904d140aa560500010002c0302e0403002204050760340641030804207030705081d0b01f4050040c0f40c0b450500a114a039100c00041d02603902504000e00b0744080d074400e00c091802040200052402c0e81d4803890050003400b101011081d0180544003030840d034900018030714066818494404d00c03251a031265000312548209802419840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 117922005 1250 117920755 117920773
    0x160203091918060f0b0405010f0f020a080f030f0c03070f080a02070f12090e130b06030705030d0306060201200703050d020f0708250c060f03090503040e0103051011040512 75
    0x40c4101d00c01c5002e40c120009402420721440f0403040b80190031210050500303200030f02050341c200c0c0c109ca0352101c407810543d06821000200328900202c0d0040101007150224000c1544820600514064a03031806009042e9440ca0083c608900040b901d8500144020841851813130042c3c0001d5007000d911a40545080d513152128542008004d0084030303112038522003400060340c0500f41c900038020401e000006801d01201450b2064400711002d0200706200f004264275036000c20580f4000c0102906540360300300d01440c0034008000d1440303448050750a203c44100f41842d4405280d40c1d03d00240405802e003005078404803080e400c46421260115420044c41e5600001c8501030406184101806a510034000000300c0c911702045480300940307040d0f4250300e00020300c40c80180c0141c850a2030301e07164400019800720302404182c080a0001d002c006000b08818610304ca03410b0689008001300c0d07100f040c1c0c40000c40c2c22030703180d11508a4891020300040c440c501e0071800984804c80040201e03400c840e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 117923255 1250 117922005 117922019
    0x180503070b3a0b01030f0518010e03030c040303030b011103120105040f05040b07081302120a020a0510050f0f090306070c02090c0703080402090903070f1103061602030919 75
    0x528035080410007140210301110300740780c50b44039262001e00071046901030060481d0300b05690b9880e030842d0702005448102d03800050340309510072070610041c00024069410401c00d4000040e11100c5111219420808072100840d00001100d000b00c039001c2c02149044d2443d02c0c00c03002040c4a040c03050402480c07030440d0b20070350810800b40220070840c01c44070f0455450308007000700b1505d6106500c001c150070141080045169a0b003050f900054600300245141c1d07441342100c5044004490095020b071042c54461030301000022003904141c825211014101c0d1524104074400400c0505a00090020400740f01c4005210300074103c00070134081a142050780300e0700000d00b085000c40e0300d000052a595500419840e00285240c0c20114903c8528030f05990b6840060075100c00030b101038003401e041e01c08101c2c80d286c00c02c2180c1c480c94000600c9902007000303103040c0c601820514a4140f1900c18580850015000e00580181c02a05a0020745c40c0071114005d20000c0c0500e800c40d00c403800c42c0c0040000d802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 117924505 1250 117923255 117923263
    0x10081e06160215010e0702060114130c0513080102070203010b0114190e04020706050603070b040b070f021801030803070f020105010e13030c06060b0406020114150603040c0b0a0e0f0909030307180503 87
    0x83d04e0300d011407800c02e01d011b440007868548168405d01d041ca8240c10038601c19142c0301c174050f00082020744086490640c80c101070300c0754410311002c01e1009084000000b00c00740c066000d401850301c21002888201a040b004484461500460840c0701c02e0800a00408205028030000303407a925050010b0745403a00f800240c201c1e0403680c1c0607a25141c0322010060349283c1801504082e0900b69561400d09040110a0100d0b019841d0014141c05001200f08195503400381f0301c5407440591184c440c81503860340780c007d019420aa45650100d4180030f040368545006008441c1030705d000d8070801c800c654911204480240200b80103070284114401c00b400480c031140078500c050081164500c2c2d035589400c40003803c44003040041103003440c8007000d200820800b0705000380e142004581d00c90712900d56007000220005d0715800101c51030800900f544c41540c2147c2000d83c000402c41d541e007803164841040c0070610004441000c0c10340c00400024141902446962400304105600f9003006a15003000c24a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 117925755 1250 117924505 117924509
    0x11210a110a0302030a0e0a030915200a0c1202030c0d0807060501140f03150c0702012703060509030705070b0c03070212030d051014060904110310081e0616021501 71
    0x40e800104015401556000e80e086206d0000010315580689440003850b209440c0508004212941002c1080c2480781c03c680e40d808113040c00229031800c4001c00316a50301c2005174200c07404a650240080c001140b80c0c0000030b0307650080c01130320039513500c1410003201c5449408201e901034024443e02001c205144035980c06030940e00380b0404001e400780104103000800002052090744041e035130703d001c840095511508030100c40d4045440b0351703041c030041e180304900c25100380b50035907152402840c071440d19502200f2603000360810441c0362030f103e801545900c580c1078050700c0356011900401669507100d00501107000210196400c2c10120b034005104c41d002400b00b212580d1011445221042442c4569900000c4000e94451494600003020003061561081184175102c04101d907100c90b101c940003800003138012207000da500e04e4040d0040c3c2c1c00c0c3c0c200d40600345030b074401c1c80600023030440d9011192602c1680d20300144601d81d102205c0d0388030102c101001030114091424008100e00c440190340e40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 117927005 1250 117925755 117925757
    0x5130905040b0f0a18060903140706050601030f0606210e102a021e0709050c0309010b01020c130b030f0703030c050607030c0f0302030a14070906020111210a110a 71
    0x21480c01c0c5007000ca0342142004c0c00807201030345041030112124941c42e1282003c80e61003800442c616009046c15102d070010007030480d0602c04e0007e8043c04019040e4440c5104007001d0300c2c2003001200d01040780c0125001c50049002046020710414050030300a040c064070501d00c480003003452401070000d281001d00603da0320103441d0b2101d00c410241c003620000003119644d08a12217000c080c0c0600d000b942d904141451455803c084460394030b100205100982c00303494040c0040c419410400e5190200380e0048403120341e80d501c1e01003d41850f41c80031428280c01c4100034441c1e80c1a4010071201c1000f800240503265243c81180700340b1907000414486000118082e4032444132501437400c1450414030000c0040082504d001410807185822070340c4d180c10000705103030068981d925030a0005c010429018090580d200c0007007040703442d80d0300c00112000c3d00c416038001d200000010300d00040c42e0145a80d20b16400600f03c5072003d9114003001c069a000c1c03c007000204100310040e0140c9065480780e031607a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 117928255 1250 117927005 117927023
    0x9100e0307020a1e05221401060210060b0d0e01020408060702210708040b09010507061b02010e0316080a210f0e060603060f1e09010507030e0703050d0513090504 71
    0x200b54540740b8072420007401c1201031001c104808440303250746021140103d512500311150001c46a00f07011410400c40c04603c0c0080201d4036001300c09084104003441890018400d0302250003d6480780d005000403140408207940c104910301c2d000501900b64450400403644d802d00c80003810503020460540101456000f80c0701c0340d00d900004980c01800c100300032100d40d00410a080018a0440840b4100c0d01004600c5848204c00d00040342c5911070118050407250801200c0719900143c5e01000c44072138003d8008001181280300655224052045414150030004c00800007040c0c0b01c000420280b4054030f45446500d0402c1e0002c060b000348544a04503195440c1d103810500306080c818040040d4181004181510349540001d81e988402021196040c032001d000c2140c044d030609007a01c8008890140a0031450414110750080070b00301c0e00c5500090415610484c00d0b80b0110705001641e40040c0504a00b810500040e29584e0048040484c5400503080000302c1e180c82d4483e1601551080200c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 117929505 1250 117928255 117928267
    0x50c1c02010b0303070b040303090303110a0e0108071d06130e090106030c050109120213020d0e010203040b01330e120a03020c030303070905041109030d02070306050c04050105040b0309100e03 84
    0x30300b11901c0303600e031034040d030300130800d40000c9161380342d1580d8020362516000c034081803e482c04801410007403011600d046000303d40940d0719500400c0041c21184203aa800700580d50b50a011544010050920070071400343c4e40c12560b25040241c024005180b01c000c3c007640065480703100c0f050b000c0d0100c980c00d400c0e940d01c02e0148100810380c5541002003409103480030400d420305403036004040100300300038444d0f0800381d80c404014080c3d8054510380c0c041840d007000306440c001200c47c041e510884084038170303401401c00481c2a015440c40340c294074040c09403e0300c03010400403402c1c03519211f003118502480651902408141d0740c1d000216140b00c41000030303080c00c069900c0c01030714000c030381040030b84250800e00400900030f42c41000b91003147c00850300030941011040e02a407061180384115038040c010400b58110712600080c03448103ca11a5100300310954941100801f04d0186003d202e00003241004100981070a80002e550080881000d5a444c084001c1900046903103100706480c071500003080b6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 117930755 1250 117929505 117929507
    0x70e070215040b07050d0e010509071a0a02060c030c07060603150e1513021203030f010314070b070212150709061206030f03030c0c060504060b1f0915050c1c 69
    0x4409071000340540c03042014105a61a0003250780b00405500801c0004100c03940ca240182c0c12080903040740301e000708114100960250f8036170105001e200c082030003d42e94282d1820880c0106c5143e1105c55018260503211034091240d02c0e80302514840c00c05605000074004a1440d1103070300300661181078049180340c1c01c05800410303100e401a40a14503000202148143c0741801c003803690050b9618000421a060703840000d0000e04017640c2e0400502c03011041240c5854402003040c140d0303000d60b00c011108518806102d90b180b0f25030150161003e0144800340050400340285c8601000d518240e408002c00c0500c203036400c05048895100042590008100c0c1940140250708500340c19142172011900399158000741c03c00341c40d0000d0400d981e4600001d490ad10480310309034501d620070000e100505190074640d0207070112000943c800c0083c0c0c40c0c0072080c03c5003418130384032003199a2031390b0702c45510b010303200d0b00034080120352401441000c00080d2164001808580140042c8540b42504d010303407160 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 117932005 1250 117930755 117930763
    0x307120f0c12050624041d090115030c030206030606071416060c02010804201507060606050403150c021c171602120d0b0a06020607020105060105160b0c0903070e0702 73
    0x181520b040c0351030184451516290700c5416a0001c0802e2201840c8115404101502ca01d0303002079665400303080c950341071205140e0010b0088080d00028455002803ea40aa176120140b000901c06038025000b000141030035400385a1084000b0401420301c51542ca03111605010b12000517102d03041100c04061150814203102c0140c0240d01c1c3c00768000c0f100354000303400858040c201420305940041d0fa80400240000700c50311415000e0807072588040800750f40712a1760400442211080c1c28004081031840c410815503040b81c0c2c20441e80000039010382440c400420220305407500b11300132459500030351104805d42d102441195511540045062400244900406000f1a090300e4003030303596104c260750001e8150b2140c600c16400d43d50f00c1c1c0160703609100501030625141d4118403580b90000e000394001c1080c40c0300d501190001e1240d0342e5440d004681c1403240d03102e12910812105c811f01c0200d441d00c10202d5000e10740c0c0d0401860815150002490310889501100c5003a0540c4200300c4031030381c140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 117933255 1250 117932005 117932027
    0x204060f1206080a0308040503090a03030807080a020f040501120e190c080102040501020a0308071815030e0a02031e120409020c19020901030b0405030d0c02070501180b09060307120f0c 81
    0x201d41007107440c2c01c00c40d195464a10580c006801c200103040804c0c20f00c601030040321071040d002400404502da036850013405070b0004440d4100401c0805000a001c109940200c030844d1301a030b140a8070301703418a00196420481444100d140b20780c0d4003a02009054100194412120742c9200f14504d003a1620b082481700d0350a03044003800341d0041c0f00412069800060900c1d016905040120880d681c00c3e0003251103280c4028509500307010704800080b4202c4101940d245c2c041d0a035020320210000030440355450303101000094040e40908800c50000441190300c03d003072100a4159190381070b20402c803101a8104e9000700440036030000745810005810480100410325511a42d90181030a8000a00c0006e052002403c40c517442c4000604021007401102c0c0b40280c0000200604c520201c0003d41d107400c1401840d0201d404400601c022001c1c0350f08550403282030130320300c0e40340401540c180f0889401c090308030380c02c0c03082d4583e00841c0c01c0218003071658501c002e4080040c0200c1d1f854402401d5103026 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 117934505 1250 117933255 117933287
    0xd0e06190b0109140d080c1015081609020a11030c030a09080d05071e141501060e091503120f07061d0a1211030d09021503010e01060c05010902040204060f 68
    0x4070000c10901da202d0758624040f00041700e44d1101d02c1141c0c241140240300d5008074040c00e0040c5002c10142032259405445416000d400c4140000c0e20341c42c0b450b603185601c2c0401c05c012505d0007020400070100b50014140d00460385000da00c001c00c543c6100d45903400c407040444281e040400e000c8000c540c05010a00100050001000724012112002d085032140d00c0c1e01408001c1d001c800d124141c0401c914051503540e00c2791021031a90002d6140903100e9603502d0710b0741130300301e095400001c43c2c0380724291a4207540f0b401426003107283c0380c1c861503900c080904030409406010300c0f80e51200580340540a00b8610901a41180e030f02c4e0f0381c0d4070705a0200c80804442c2a00c4002071100620700000000303405103110b602c01c42c2080340c4403010384103030740c001e4071542c44810314480012107450030300c1030b9008060200c0c400e4883c80100400001101c2c000c1c08240140b00b5500a0040100150f40c0310348100050b942c0107030000940300c0c040d40c0120782070360702a40101c00411120b11a624a1652040040480201c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 117935755 1250 117934505 117934517
    0x201180812090127020a121a061002120904090f0b09010506010c120e0315090109030e0906090402010c0c050306010e090616020d140c01051005150c120d0e06190b01 72
    0x41d802d4482c00c003c001c2d21020700021030095030704d0215115901000b0143c80c1e01507030f0360b0401d101c6290210b050901d0455628040b4003250114525007030150040c08031021503000f0304000c007200d170701c141d880c2c0e00110400e0754481c0d120140400801c24118040c26410301408401c0010300e0100400ea09488010781003904108092450101269030561688418940b030f103485c40c241203010000074a001d142d015031160b03031982e510901103884815445001c8031740c440d40b0f440701500491401c200d020ac001721420b079040700e041c7c80000c0040d8424a4061125881004080460b03500c2e100030910b051030036080f840ea4030240b0310500545042c1008160b40c090341c03412420003460068603009480d800180d1329442404000c0034071700103d00344d83d42070340da51101030002006035282c00f0000c115403524502c40d0500840e03d1200d451104a4900d049620310980da00050a4205030b250b1006250b034400f604940c466640c0c0c0301ca150068000b8080ca41c080c518100d60001e401040001d07007800c90b00803000e01d50610003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 117937005 1250 117935755 117935771
    0x20a02070608040b040201110c10020c1315140102070b030a091419031202040315050708010b040b0a0c02040e0a0303090311030c06150103110c060103031b02130c02011808120901 78
    0x21840404c0742d0f000b030782071030401d00003010480c80c02c2c40c00f24031b0028141e114034400c20003501c8650004e2119103040048495009800e061b0320403400700c0701c82080444030100511006c1c404681e4203100d03500c211034188100e0b00039980e103e0a2154540003903503080da0054940c0c281c0710501500140e60f01c400c1207441d01804104100c01d0341c03440030032440340c1c0080904c5010403c0700c1100381540d0540d4002d5400403100040340505207100401050103d5000f40070801e0078002158080b0040c05a40903604400301c490324100703508030281c80320041c40000320380c0161960f203001e0315070b04140b184451842c03081d100888c41000c1c62901401e01440d10380310380181d90007030000c5100581c0026125803c01106001c10b4940002400100c018007242d0a540ca6420f4000904c08440c60001480318102c07400ba548203821111410316180f440d404441c8040d50040340d403102510303200f4060307000b0011084103000000d01c0c90074502051840c010412170a071034641c03001c10303200401107160b5112035010f0078480081002c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 117938255 1250 117937005 117937013
    0xf0f0f0c0a0e04060503070306020309100908040e060d06110c010c030c0905040e160815010f1206180c0f05121516050d021201090b0904050c0415050603040303020a0207060804 77
    0x202a141e908400c100c86059030041540f10340e4409409010090156520140c503820604003960090320f01c0b498903c1042e090044004061082c0e0703501d5903021020a180501d4002a40301e41400904091342c4074800c0207030100003d445118030180ca20300141c0d00c2d40c44100c41c500c1d00307007150441c0c4070140500d801d103c2e001c031035150b10041c0c6034165178040301c0006000d503e00340c0d06481c20080340c0d41c040300600074040106648000080004c104499107041055603030300c1d1a1b40c005404043e1040e020802001e0011400244660704901810040005003a107803400a07100da507080415584002030008044405005a040020443d02c4048450000b44800204481100807040c030007041a00e41c51088501500c1c0980704034111800c086400500755110b520101c1200807003003080c030034607100310318060140d042400c0406805100e943c01c803000e0030407051000248006090352051211800510940100b004e98039500658003c9020755030050329115814806840c0241603000b41007808100300c1000002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 117939505 1250 117938255 117938257
    0xb09060a12030c08130302030d450608070216050f010e03030d020403030e010f020109030f030510090204031b170601060e010c020319050d0e03030301050f0d0b0f0f0f0c 74
    0x1c1e81481d09208000c0114102102c83c2e1600000061140b180001c185850402c1d440c002c07802e4030300071410f40e0402c5040190070747c0e50b107a6011010b41b40740c4190a5013801d0081c01034880ca00b0004c550b004000e00031182040c07120715900e41e00201c02049910b800d0249003981084515210103d169034440180d0402d00000e007070b42c001c055480c0c108680b030401c40e41c403038806105444110a500c401951115103910303024000512500703810703000907285010b640700d452050054034442c94058035a8040300107106801c5000d0000101610621110f42c44009000c81d52840148000c3d8020310040400000564000d01b0300d241c0781e40510b03c001c44682400f040650003050076811290f040c18146940f00381c91005a45551038180c002c1d40c140910341c02d140101b006040c0102c50207105906860b074504003020300303880d1090003041c980e401da4410b0005201c581840e6103000c0c41e000c1300800c069603c086603510b03031481e09130441e09a041c110310842446224404600701c15084031180c40245003d14004000b0b2120b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 117940755 1250 117939505 117939509
    0x3050c04020f1804140901200702060304020f0109051302040f0803091305060d02131a030609070e1305060709080d080103020d0321020a020f0c090f0103080307030219030f0b09060a 79
    0x48420f40c2c03011985580d50355002d00846188800803507101e10f004811a0f000b041071928448182141212000c00c006110088684059000b4102c0d810343c0c4940d001d101c075922098815906118a000340459940d44041e88907180d074500c0c45015a40c0d509202002d01102060f81c0520166802070141c000036541d414840503180b47d482c034000440340d440100099503180b058402942064810140d10401c1400350032010201880840741c21102d03000d501030550712002101c80403406d0308920350a0201c80105030509400074000042c000b8004050b80741c443c107090084e21002c0108004000403c40d100d000d001528202c001810400e81c658034540103d02c015440c4a4020304100d01d00341028080c41d5241d038a000c01d0812043c045480d1010b491002e07540e003158007001009407282d0658103500e40342c00030030103106004070f008143d41c1e646580ea4a00d49504050300c0201803580030301145c8034503036159004442e00380712680c02144101c4810124401c81c2c100000319400b600e6007008000d200d45034040d04100b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 117942005 1250 117940755 117940777
    0x2090106050309010603082809080309010f020c030118030807020111090603071b05030306010e09160804050a140601050405010e150f04060506030420011e180e0f0103050c04020f 78
    0x142d20755900000c6070040250740c0008103c81000700d0401c0d00c90414a89861840300c1408000d08403220001099514017124820001203074010071521095511030303008a42054044d0040344d1f0602a5070300000d003903400a170488642030340c0244000040c9a441080355030024000d00007001001c00701c010704c6400348200c2c102c81d070042000201281c403480c401e013a003e269400101084060b8005450625180d17030060314070300e0005500121650300c61824010701809141d01c8151444494800c43c0150b0301010010000d4505001d11051032010422404c1e01000018001018103d46d41c14501040200e41c4182c110148460700c0b44108243e040686484d2100e01000b12451001c9094880005001e0103032038014a8019a010041c0000c2010f91500313940740c41d514024085503440c1d4400110380d120042203000c000d8041d5400c06500050141c0107091495964407881e01c00241c40746005141c0c62400d90388114621b840d9001001440000d10000b6030301c503c100c9056203810303441c481d00f00b024022601c200d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 117943255 1250 117942005 117942007
    0x506120a110c060703050105030111121303030b0a03110312071a040c0f06050706180503030403050f12090309091006050f0d060e040503071406040b18010906020309011a0901030209010605 82
    0x34800050a0342502c1090030150100c62880c600840010040e160070302c502806903080800004c641200d0000b5100d41070b40321407411006039190030401c0765170320f0b0043c019014169102d426448a80350681c008001d1402075105651004202c1b040c1440c04103102e4a00d0b40c1240c0500001d00010006c8540c2c210704034400030045441d44460030301c410102465484070005190010b8009440d94000d00a401c0c00c03809210304024810304401c6409944600c0c1d840107001c0e4004100250000340181e01a085110101070b4050500b0006500300c2c4252000355a1007071070b944041522000351400c80e44180c0c0c0804a60616103480d441d0603030290981c021030391591844500480c030700091110a512800040406100ca0520f6003001c2c1811030f205c2d4003145d410b8901a00280002c00e0038000018110701555104812301e0b266515a10300e00300000c41803404451654a98a4060205055002450240020100001e8602d4640000b00600c134252007000d40103504043c01000941d441d0007003281107030100d0500c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 117944505 1250 117943255 117943271
    0xd021918021303020f0118092a090501080403090503030d05150a18090302010f09081216230c06040308060f040b060f1303080403030801060f020f0d03020d020f040e060a0506120a 78
    0x10b841d04004910311f8481c030510305100043d403c0150b0401c0568010b0758104902d40013031107074107840d0002141c00341c1022884401c020060381d4802c448043d03001e4000e2414403403443d00d035000241554020401d100419460300b042c840042407131114041d20748011a04c0d203400e1407402d620440c0c0903002541d090711117079440ca64501414000c1d0411000c1040440d0f00300240d000d5407900740c9040c3c00ca8031070b0145841c0c04900041e60080c182c0911100004962030b003070b00b03202c005d1802011600c601c43d04850403590a010b090302d060020881e06010301e11a468105043c900351042c0040103003200d590324421818004d41c7c8001351110300c01c5550b0b0080c904d41c010780d120020301815105100c9640018400603001030b001040c9540034103018107889503569000524507070040120380d20103860703806c411940c0002e4440c003c2c15009500030840c0300c5000102605010b0078400910340d5401c981d2001c2d08004204042182c58030700301c08088054075049070184d00785050000d6406408034000c0c0b504812690310385007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 117945755 1250 117944505 117944507
    0xf0d030c1103030405240405060c03070306150806030d18030803090c030d020d0f0e0603060d0606050402040605130602120f030a0212040f021503070f08060d021918021303020f01 78
    0x3070881004001411a95681410314005542c5c0d0001041031207418514454121b076000080c008901490308a4000d040e161070383c140c4e40703100340e001034810001d040d034402c80002c5001512054000400e4151101a0649840002d050410000188079001c1080c0f590000003000919104072060300c0d00202030342d44950700c00d0009440c1c880d031000701c41c0d89031155484001d44039600040840c07989074035584d4030345412000041600c030072206440b91903210409100060081c1021000c0300c009074000d05c008030b5a2646d4401040890348181c002070700003100020100580700d00541c00f940101194401000f8a0810469103074150040280c6d800d0039140001c04a1072800582e01550400c6209a01c0380009041c545004600c3c90b070312480480c00380c80007a0480c2d00b884041c0c01603e10400090b283c060301400c43c10011108110000d1070f2540c09400d5a8110340545c039200c1c0d03500300c80c0c0040b03114591003e0030308403070100b400e5140058640042c01003141c1d042202080311008222a070545004101041c2440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 117947005 1250 117945755 117945767
    0xe2506111011030103062f070f06050c0a080f06010912060207020310060512010c0806010f09081504031103130e0603010f05100f050402090a03030810091b09080f0d030c 74
    0x405a01810540101c641a0b038031001103040340c0c4134100c01c0007442015441080200d08400f114448241c45645061420084000030704070b0724450504003084143d9555100300702c3d03500341c0303c00070004800314402c81c0b6142c00c0161260440c0260b00103401d0751030040b000030410441401b900c100e4411500c3d00303208004554050380c020a50003070075110380b41c10041140d001803510340300d41c620910550244240d80c0e00e0612800018440e183c0d1044515030344c080054840544101c901020882c05081c0000d1404d8240001c01c0c40d4851380c1586406403c050500804c0d20a502c4a42d07469900100504190b04038041a1401243c40c1c0d4100c0c0c002c036039600301c0020300600803007480b0f1445030304020402c1200d40218180f101950b903003e40101480e501c41e4184802c034000e1040c0943c02009441c0207001280c0220422a40880c558900c014803a88501c054400d84809030822903103241c40600a803480c64015a09602a001d688010600022400e64242e511039101d094003046c99038602400c100380340b11b00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 117948255 1250 117947005 117947023
    0x8160e0607080c0a020f0117150a0503010e030307021c0203030115110a03020708010e12090402090604120507080c100215100b1c111306140702090106030e250611 71
    0x901d056200ca001900c881d498013039130b0500700e201d295a4a186440c1d503001c0e18205004803040c1a50b10800d64800b001d10020a200700043c583c0107580c40b01c00951980e09001d00141c0c07034a090051612420030001c041e20700440700a4081d007240a400c0541880c1e680001a2411600c403526080c00c5400a4030050728009072841000305240a552482d80505400145c51012258841f0007000084c0881d0b42058a5040a018650305a0802c000202c41450241c001d0b0003180002802985081e541b1100b1045511926100703d900e0f400201003002400814071000d01600802d071a5141281e0340110300039150300710b090589107903000380300100b0400080e565022000e401004549035035582c44190a04600002603d2030180e1401c005681e0b40d4085100d054984002e100103000a2090070010256016012030461801c040000d00c0390383c02590b103d00106008290603100003444243c4bc0020b6400c1c00c6c00440b4200c102c180321550001a00350082151040b11420710700100804c0c064402e05080081c59 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 117949505 1250 117948255 117948263
    0x30708100f06020303060102100e0a020609040b19030501051005090412020c1005040801060b0a0504030b09100f09140a08040504180501050a0c0f09050102060c07030c060903020f010b0108160e0607 86
    0x1e14085421600000110b000302d90036002c071221000040035010a0301d0700342e14415201d8210140100060616201400c42034070014008111001c425002c01c0c5220400b107984016035075170700700070000d110080c850b4a800c51004402c1500017420100820503d0343d0241c030080903200d0700c07030b001074600f0310030710054811a10003007200358442e45816000306150014002c00d2110351070100001842c0c41404200c079941c0c07482e6100c1600b01461516400c4881c04010072102003401281c2e00048045991b00c52070303890200c0130f01c2c002003002490606000c05010040341040d958880d41815010540020070f9404440c000c44001c9502038410000c140140f0403d60010420741c01c1c1802c1c00408030954006010007001581c0d036103594107200e64126940c0f80c0e1032294a0243e007254000c50101c0100c0d20041502d540681803040704001550746007401c4454035042500103800513044a41c03a4003003802032070501c03642441d28a04900b840c1c40f151000e100d0b250b10307074000c0c004c11445c0c140107900e45000f50384820b0f808c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 117950755 1250 117949505 117949529
    0x803150301140a15031a040c0b030901060e1e01090b0d020306090f01140103030504060509060417010506010f11060606070f05070909020f012c0316030303060e1005030303070810 78
    0x6500c0d4840304402d82940c0c564201410b16146261502d40031201508880c1c1205d1412400700c909131800e544c50502a1042e541c62841100c0440c807130440700000c600902c5031000025516141144208400c031000e845404c1c0c0f00c1c03103c034a20b00c1c04840e00c1c081c00c0c103480005400040c24612400003440c074502e80c9000075014000d4000f0440c8400010451400343d60401009010400120001c10041d520900000340800d2003803009101841c0709401500b41000041d20380361600e922400304145500a52942c81c00503034596080080950b841002c1111845590504902d0b513118581d80c15100c41c00240690b0080d500801c00c001400a00b098100c28076803c003007503c040a4440c0060801751089071001da004c0c3c811000c0c03804440d4840c80003040404d02c540c0042d400f044040030000c401d40707a000c0c18941d062254100c410200380c0c0264180300110310a0300c1c0010618071f00428180c56100007004000c0f89084d4400822240d28044110703070340900d01c0d191000d160b9850810041c0c601e0b5464200c8a80314403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 117952005 1250 117950755 117950771
    0xc09091805010c0c0302061f0308190306091512020301020915030109050c090d03030c0e0301150f080304030b0106180306090609020405090f1c02030c030a080709060c050a0803150301 80
    0x10591100e1414180140000c2c0441000401c0a490180c455031008005030700c08400100f011803441503c000900d841400302e42d60340d542e03898086d80f5401094013240c0102c441c440d6000003580501c10800207100c8030b07505000211903002140c019444a2003070000300380200d14020115030b800e40c121075501030000d084500c10890080003840c180c1007400348940b034628180120301d4521241c410b60b44154401400000f0055542c0c0c0c00310f02804c00c0b88004410f000910003d040f40e96003c1c01030660740d00f5000035003002545055070400852669500c10301140d08100800e20201340c490403018152040381c1040309400701845407404085115500c0901148d25101c10941041100d401840400d802200c041c40b80f52560210580c0325580c0003800900396010340c0c00343c07400204591055442203da80141ca0814080b070403038508603800301c51000001303446141002000703500319030100043d29180c13038602c0107090207580341d40e55910b811001600c03009012001440c04070b10050881ea41010250090014075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 117953255 1250 117952005 117952031
    0xc06130906140a0602120904110715050619030c030308070c0f1a07081303110f010603061d030304050309011d030316110f060301090207030c050d11070b090f040c0909 73
    0x2484521a041c490216020000b44c1248001094450756000036500e170716099a15041100504803501c41d010407400c10f00940700480e00c4082c04480e808108040410549840800c1152207440b402880c1803c0042c050180040b0340c204508009680e85401d0848040c1c685040a071032441198038004c0c100b0001d841103608202c804000403c40800504a6203050b40302c01d001550000c80866244074240d44850400010a22034051411925140c07000e442c030b28100c01b10b926013522070940098400c980c88001070f5111700354030310722007640948035000f6500f5401c0a9946a4407031003030600e4a030400030b0120704820407100204841d58203600045c2203a42d15184110450030001400005507080102d1407443c1c080c03400c100c0d001510981004010625580c01d0100c4000290071401d000d5042081880035000094800c00c10355614806c5a140e8800240025110328501840754011545500b030030702101001d522030b00664003808108403400702d01d03410785610407940d46541da40410324560030801c80b07803442 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 117954505 1250 117953255 117953279
    0x3090a0c080d020c0f100309081e03041713060c020f040212070f110a02040f1b1d030102161e05010f0f0f2c07050a06120e0604050c06130906 62
    0x1d10310b0303602a64810782001c0308224400002e40c08060b0014a00100c008403240f19a200b03a00b080d205403a520705040400c1040c07040c084940c5218441c58000200f408180482244010a500a44a40103240ca44400b160b036130561864070859060040200c401000c6665200c2c0c45200404040c00454030350402d6115216919001d0741c0d00300c0072440c1d9042a0141c94401d4044802021004000308504601903007070000401900c006400015a51003000c0d850414084114a01c03923469a9001200551551240c00d80c00420401d148242e00c100255400c88a43c100b80070107980c2c0101542a180c0a449081081288441c070010002d518081d804501d070000c50340f161040220711001008010650752941c4211003084a884e2406050252400c801c3c079010030410307919840c40320503107481d03e46d5180480d140000c99000f403070201d00107888031001100b00c1d208460140b41e808000700a60b082c16102d0503101d510304002c09015034070020f031403184040e082420100904114030200000b43d601c5400e0440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 117955755 1250 117954505 117954523
    0x207020f0409080f03100e071e0f140c0f031201080709050f040311010f0f0519090c0933030b0a02030709030311030c0a05060106030c05030c030c0d0e010203040f02310203090a0c08 79
    0x1060603400409c8040702c1c0b280c04030706c8000040362920b02844000c0b40040400d5000401409002d124480d0111100301040c40508003076880030502200550400314642d04002880d00010025450030782003100318180401103913007158141c105038941040340c0a540303014140174000c601b06142020700e0b400340003486602c6144100340c01160f5100390145103000d682078410085026142050640c0c00b406065030075446144407000c562150410485c44000c01c1d8101030418480c4c01c13041c006814108144000c0b020200d0748040c541e00210710b03602e00000c000d8040d4070a4000642000550480c29a000004208548403045114212200192185401030f9964001d014000000b8140f4503003800a50140c0c00380e0b40218410400035066554a40600360190402e4401041c10348c0c60b8207017018120402e100440c0a00c1c000e80c02041e82f4001c034014001079525030b203083d0640702c020006141080046404501c0b0070040c01c40056580c0e11603e070418034005c000e100c05003101c0a089400100d458002640c155 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 117957005 1250 117955755 117955787
    0x904140402010305220b060d1211010b040b1e06040b070609051e060403080a060306020c1b01090501140c16060809070e010b040501052107030207020f0409080f03100e07 74
    0x7590b5882c0f0440c0e142c090f2020401c3c07003172405200104000750340d40d2146036100780042c3c0b0f554040030031a110910180010901075020072005425004090320a006100e62107174251801e0002c5401d41307010a040304881302032810f440320002502c0b40e050303490400b218014410801210744034074803418000020005c06000f141c0500c594099036246100101c0b58190781e8a40ba8054034013555980c4056640b10001002c1d2101141d555001000007205440541003510026004210295000e01e544000a400d42e020f40d040c007034080010080e036031380b0107000c1d0040940008180c0d00c0799a1002c04601d025001c5a11030705501d080705d00881c103a6031103840c4520030403c84007241c04c0340e5598000d40710494428011452094020801030103694000d1006114600c41114480500807000c940b50500e01d5055480f0000240c00096002c103500e016860030f04c2012041790300b023020340081c1e640c943e054490780e4038100c4140c00200004210112003900c04000f000140700e04100da161003600203020b4042161454 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 117958255 1250 117957005 117957011
    0x15031a0406050a06050307031b0f020c01030504080f07020406030602220b0304050a020d21020607090b0309060105040e120a050904062c09010b130903021e0a061109041404020103 78
    0x411a454580100c808890002c1c1020a1080c241030044178191b10041c0298181501d5000c00c91a2025408594184000c3c1e6a030340c5520141001d00242883c170828920b5041505040900000c00c2591003114858107035480300707554600e214404140a04419480501400d1010a9440360b2005504461110740c41c2104031180880d2150316050190200740d030f001c2c2499000314900c40041c2040051003034024010760b20b01c0d040140c03000e4100300c60f4039012420001a0801014421444e0b0800f954401501c1c0f440345141c00d61a005203a40c0c0e079001c05102d01c80c411a1902c9148110503818403006001d4520001c1d17241e5074149514000d4020351220301c100e40614509400040c0000010b41d0740780c8103004035809164080004e24a00a0b6070030003030000505550396a501142036600d06c0d000d610781d0080d4060100c0c0d41007031400c0203824400f0040010b000d503e401140d00403031060100c2e00c0f104c07042c1c0c4644001024403004186500c6406041e0270306401a1a0011007458000754000b40d9206070b00c00d982c18 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 117959505 1250 117958255 117958301
    0x30102040e070e011b120504030501020a0c05011d251e051f020c0d08090307030614010812030c0a170903070c06050a2f0105160201050105030307020907050a091503 72
    0x440d05120010107a8040c1080024568009a00180c0404030f031616032030030a0408ea206d417200f43c02c81c0e21506440d4082031842042e1001c102c130038080c0c01410700c140d800c7c400d200044410310300d0b126408001a4414007044c011405803040010b40000f0241c1810440f8401d12236107694181000b040c81e02030030781719502c81954441071407001d0038003c842c048a907000d03014200c1c0300000c0c08201c01c000942115040c4003482000040d0318100030180086001d0b03180450b42030b244840c4840ea44106810880041d00101030480844101104803904202420012541c4500d4000c1c00c6400840c0d12034140481240003091140121001014018150098901118440e50b4420544542c8190101c40c0041038051003981c051041d00c4101c2289040680198a44903450185050854070308940c0d65040130204941002240d5092288601514066000718642101c0b5000541885c4000380750030300f08100040c0c05414203104024440040841c248640201c42d081600030380034103805514054842880c44d00c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 117960755 1250 117959505 117959507
    0x60d0f050714060304030f030203100e0907030204050c0a0c0f0606031209061d010e01030b030a08040b0c150603060f0a0b090907180221040503161b06020105040c140f030102040e070e01 81
    0x1164043c0751b06444d440c0c03a22860000a4000c0d400c010008280410708540004403508031041c028461a080c20203050382c00d0851040004036000681101810201805003820b140e400c074a07000c03107a94000ca86041c030080c90b40b5050014003580c0c1c1000301404010b0800c0c0d00b02a411146000136281d003511480c5580d20507803400d859891110704581d0010b80314100e41c0b480d5501980c812803604201405540924216480fa40980c0e84507031b110b640083d2000030441010401402280254111880045c100b400c04100107642c0e45009011042c023203d01c0d00c04111213200369488072619103009001c41000e85000718445032900168030480c00305000254218000302014402c482e1064020860841d40e03c0c0c42c054042c00c2d58a00500440341032204001025800c02c40c1e14258400d03c0c481d890070350a0000859000078580b066a01881c1568181814031001549904000b402e5482134121030840541805c000307200200424101505075100113800300d80141281944c0707105103103940b01c03a245200e480700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 117962005 1250 117960755 117960757
    0x6130b03060105010e0a080102040803040303020c0303040b3403020a02040513030203030118060b0706020c1005190b0a051e030c0904050a03080a0f020a0c0b010f1a03060d0f05071406 80
    0x2405950640014005200a6004020030241704101070501c010361922118403a00720b9029070440301095002040c10000c140e41003140c155454402d401a500302494081400d1907401004202c194010401410442c8403030503520b1960808031440c2148c40b200143d00707010b901d0b00310b03000d400d0740514100400a10042c0400d081c4c2401030343d05500540c5541e103800d07904403c4102c279221000710140c491034005001ca41c40d03400b401d409400350b2030040c1d13074207508a040340c540f10705031054159407030500041003003100010003220790076084c004022070848a40b800140e80400d03107800290744003120740080c1182100700c50054a03494429070450361820842b07420040705117030840d80241680d118003401c02c0004d115001c0c140d040420720303d0101d038200e0a80300b01c0059822488030000061440e0060f07205004030317401c18900521048041c0d401c254246003280f42c40031480340c0441c46403400000842c005455510300c0c02d140036006203200341a00e0403072038003e46520140c424205045450210aa13a9182c440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 117963255 1250 117962005 117962021
    0x708090c060406050c16080f070914041211060703020408120903030f070c0f030b04150b0f010e061314090703020c0304060e0f0301060611010f09020a031704031a0613 73
    0x14595402d01c0d280079000c0b2a1980912035201c2c8601440c0c0c0d24540c10b00180b180000500b400d00e003c0d05003112459180f074600851035211400d0241007611034012000c684400300c0e0020307085a4a59460f040750841a80c403050080039050041c0310700070030480c0003a495406001541c8100e002e41e408010540318251030390013060000307179050700100000c10a58040c00d004000c1c0501c52212225410b035120120800350b0065802034500704007400810041002c4907881100071001a40704112001040d008500441d040810390350500030390411440c021354031481910f80082c02404100a07a98650020607202251240c10a002e103003c0d902040800c0e00a009030f500c0c90195400860500b0700d40070080324920801105690002c4650341c40f9046a102809070344054221911460746040c21a40c425003140c01e22140c810044d454040b40b98010f0f510420403900301c9030800922803400038030032144443c0b403096510040c25860015428080c150001600070b11900c400c1340c105810006078865081544d41701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 117964505 1250 117963255 117963259
    0x20c1006090e061e04050a15020a09060f09030204020a0203040e040f02040c0203030c071e02040f050610090f0e0a1122060918050c0c010e010e07052d0d080d050708090c 74
    0x18044c51410500c0507002c203500501410488803120025206c2d10071065071000840c42041d00055808880c9030000d413402c00809440c644000412080c0c2c000810407a285d002c000d02c07598000408200e40c9108100380c42c00743c83c8600c0010600e0500d4601304440b1001e00108901443c1044010703032045002000f903a100d04400d1100d0791504000c1d0f0742d0701c06544108250001031002c54a05500036071914450358080c81c02140e400181410b0a1080004842550b1044401c12280b103100348481250b44034000e0840d102d0b110030210365110b02c00c0d920003a2000c5081c415903130201103901d00111803100c0e0034803001c082c042944004075440c0d03201290446244d0003003045007600b0265007000c0d82000e0b0300c100d038054915141c203070420340d81c01401425148080e00d00501c6030b441d100300d00c41c440c20501012000b00030485404500c0340c0d14020b803880c00d084210180005007000c101e40c4682d5100d41c1c9081c044142d206400326510580c0078031413002000103491540000e948680007840a9030000380603800f003100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 117965755 1250 117964505 117964531
    0x1104031506121e0f150e030c0309010309051905100c180e040c0e090c010207080d020a0209070e0402030a020a0e010212041221020102030412020601030c05090604020c1006090e06 78
    0x401d80761200701c030906100f5034808004071070564000c070381c0700414514440e225030300c0e40380d808020510400583d95000c481c450180c00c00c010700011030400008a818803034082c203000c03603070010500b031450401c00200c0102c410601aa207843c07040001c08143c411406d0100c20082010442d60070044500e40803103c000c1d00c00340400241030202c4030481c1c0c02150320511071076580f2042d07519030043c0301c1c103544269582012036119840c002500d6806206840142004000822040f180316070300941d201460a80030f4020003200004ca25118440c80114100c003e01030070940d50790074400041c0d0300950128001000040002001a8a030361004c140d113550ba9421512803400d0904003e2101000d2030329440803140f01107400b0104043c00703030b001e00381000741d41540c00041c0c81e460641001500c42c800116102d0441d00007800500000b08440e001906891068441c203a241d1740315400f02d0002c1c4105814100140705e0f14048410b945540d4118006582d074004043c4201e0340039020266a502042e5055000b03446 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 117967005 1250 117965755 117965789
    0xa08031e0d14250c150e25062a14010c080f0c030420040f0f02030105100c0b310b040c06020318100207170a03081006050702040902030106091104031506 67
    0xc04d2003141c500401c020019408428181e40741c544440e401844080441c42d40c1c0e1004d00d87c02d00e44100004048605000140c1c07955003400740491050701070060034009088071142c00740008014245500e00c0351034020003c012084e50040c0c0340d20012141c0c82d2010365030000240d40904203105030790155074444544141f000120b0281002520b0810341550890340c1d5600369810800036018030301754140302c09030041e5254101420b000140b441070300c4100078001d43ca207540300020504194998040180312a841c601c114a04107003100004c14cc4903003003a800204c200c4024805440440c40c0601d2284050151507035903220241d03120f0292a40400d030007610300c10308a03120f042c420325056075500300748143c564041c0c540c5400e0402c148010303412600c0e0391042e04007604141d00070018a40100494004014441c42e10100420078130409400034015500d4841500440d1000d41040c0003500307400c00280002403505c580c48030103810a10060764517a000f018480c0800c3d080d40300307641c00d4a00d81020010340305 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 117968255 1250 117967005 117967013
    0x605060a080a11120a03080114150a050706090f08090405060111030a03180f050f0c04020711060d061502010c030f0903080106080c13060507110a08031e0d14250c 71
    0x85502149401c070903004c001c0c44415070103125250308070384a03031500241541060081e080100c1c039960458026955448085415001a403e0702d00714190792070115a50002468900094403800307200428003040c1c08019010400500050450b0900580e01004a075481c0c00044403081d21035040645290010051410700a1080d00003a00300b1054140c81a0002001d5403103801e0020010010b84964112500b1600c2069090140c038000f0801202c0c01d5003003988684444680503002d0842500c26100090030702c45802103a008000140150340084030710a911030000f038040c01c011010100001c0c07030301c80ca140d98608948503d41d40c4507015650310480d40e0800d41e0681c0c00000140a60143c0c2c5414881000600c0c6941d43d1500a4050790b901d80f0f0b100c0e2050300d07103200d1103403000c0c1800c0d01c50141c445042c00102c8000050382c071103041c801c0c445040442102004c00103403084400c0b040c41d0354144000b1009581d580c040250050703905040004100403544a000c0d08007044410210001c0d00c0c100d1444089 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 117969505 1250 117968255 117968273
    0x1506040207050705030f03030f07050405100e01120c020d090e1302040506030307200f01030e1b01031401090504020f030f0c0f0a15080402030d030b0a0909080408070906030605060a080a 81
    0xc1d4070a8040350009038803a030000e803034031284c40261030f00c0b41d00000801840340342100c03965402548a0514504160501c4c0c00100840c2d04000c49800300600b4990fa410709a2207951810303034924095804001000007250029100d0f56070308010270101c0d000c40400500007080c8180d09209031000301c80220001c0d00d071340c05c201c082c11014103039550501c0140705800c08200c0e1036010003d0009a2040c002440d8202c1042c04001000c014000b0305140c60080d11004492010907414a4040350b100ca0307110a20000006800500683c11492080300c10480082038409190f80024081c0e40201e40d80080c501d003190805603a04408a4145103d40219100d036132503042541038280700820041c44460884d07258100d0358017403e200c14819001400700418041503080502074074105900c240707028408401420041500d000e030511500c1c140c00c2e65008408103005c04042590050819002031342c150a580307042a9021345024001914101d2800b008075480f403038450420001c80e4142d10103003008402c07a480d01c40c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 117970755 1250 117969505 117969517
    0x7050f130b0402091203070203011808180a0b040803090a150504060c060b10080601030c02010c0c0f14010507020a1103010510060c0f060203190b030f0307020d080f030c0403021215060402 82
    0x2c15024498015555258500780041400d24401140c498003903004160940b40c0101c0c180310900c00d555a208003280660302120940c400814400d86003065070030101c1d0684c0c00540c81020520340c08140443c1195001c0b00600311000110340610105880701000801266103400210106004000401000d070064110361500f6002c1d92000440380c00d81c40100e102c1e104600040ba001805c070000f040704c150b8041c401c1c40d0561070f04c1d02c0204489500864040c00300c450442c009000c080110221104020204001025000b00203000340428103201700c0207552484c0030442217448104440b07140080d0700b814800d9074451030150243c2d11485260030011344145444480c1500e5101c0480c9070032021a101e40019030140c6402d0b0248148900d0011100b000c480f41c42220521a0b00150f110014141000055070102501194000484c466900d000c102d98401c0c031791442400480481040010640c25000e03100712802071311307010342100300943c5030703500c0d01c0c40c071454003500415050104011781440c1d406003078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 117972005 1250 117970755 117970759
    0x19030e0712230a1118010806060103270c0602060f150603040204090c06020c0f040218013b01030f0506090a0b13180c0803071101032d0e07050f130b 65
    0xd6410303920b000b5042c100034000569030000089141c41150038542c07400c01c4e1810301c20b02c5080a9505003070506440d0000608014105600c942410078810500000040c0180840200440402041c030700150750352218892640940200000a82c1c619402c1c00013a02ca41c40c000007400b07448a031042000340d01d403c00f800903030b00550380c3d40c81000000d07207a001031405405a6002403540e0b405820030040c46240c100350244c001c0d80144484c00fa078071441112407040090900f0440e9104240c0d141c03448a02d0740c1003d490341c0b65070480071703014200e88a01c0c0020281080c20783e02071129072000c3d04c0c00004da40d400d5480f650413555001c006107084400342d0046031100300082541e0880140300d0034800a0300d003401d488803020403800410f202003042c01c41942000308480c1c8003650034060170b5226085104100d81d649810303d0346942240e13a41145a10059840c480110312003c03651201666100003401d00d01584807041c0325a24021400745000382500c400f90070010040d110081c020420310002d440b611392810b03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 117973255 1250 117972005 117972053
    0x90a0305211c1109060d050a0e1b101404090c0f05030108060415020409111305090c1b0a02040911100e0d140309030f0d1707090e041719030e0712 64
    0x304460b0f45d00320040c0440001403202150394144813854070221541c10303880071220b9120071280c1d90741c643c28191403038a80300c007103d450013892004441030316a081e48650315070022000107004501c003262a0310044100040e030399400a41d130130135142034900b8842030103078420b103500050001d0005240400c94406545d111000542040d9a500c00801a9200150f0034003d0281c0030810642d007401c04140d04008010403a440c00a03410107905183c80d42c4a58014003444003c5903040e201021802c02c485203240d40e01a0080142c40024140700c2c0c00004d00c1038540b413189198921445c0c0940c0b0a81084404540c02807482c1c2c0124079507616502902e060401490090005000b0706d042030382c062000c2000c0c03030b82140107801e021030304d0280202510404d075a1010030301000c009002d2010380c01a41c44003507900340c029440c0c00c0d0300c0324105800240c42403000703411078400000e800d110003501000301c203d4040c01520300340810341c003200c8155150520b5014080c002d80c8440c80318404520740d01c2d00b004c0c492102030718034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 117974505 1250 117973255 117973267
    0x503120a06030c0b0313050f0706080a0908040611010207020a03080d0b22020c0f010507020c0901080f0601060e030f0703060209120325030c050d0c1106030702100e0102090a0305211c11 81
    0x11f40c1010401c0654840300e80090000708050b5410411859000c04000c1d0104110740991760380c10398074041c40c0a01010000c99105420241c0d1096044070300341900100012521962807a000d041c82e40051042176286050a2b0b140036a030424800d624140008130340341407551200451075030006d4009441c440103d115050001c00031031001c1c450756014411a40c0a4501904260140054100107900c007a1b440d80c0001c1c00d0582c4050045032107810f40b10980b60008100041c1c000103880c0200c3e0940e00010303809404000000c0013280c1d40100b44182c403ea030103558403201144190303164000d90b10025002030f500d5010140c03e0750483c0c0c41c2c6107010300c6030070105c5400c00b094a0b0107107001640b030500c0c03001c06c070b2902101c030901911100107610341c10111405440c42c034114400a4861000d001100c0d5015160740038220150f40a4058030300104003e864042c201c1c0d40e90526035541c041c4161244405025942d41c040750650250441d0300280340103400c041ca08a150340b6840c018401c1104000c1c4200c0e003030000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 117975755 1250 117974505 117974513
    0x90f02041a04140d05070b0d0615030e0c06040608040605130503030f040507050901151d030a0c031104090b0c071e05010b01140c0d0305060d08070503120a06030c0b0313 74
    0x101c06070000c1c0c0740320242c0361410001411100c5200c0003219106a0044084078000b8900240343c000307031481610459218062084407102801e403d4000b519145510301c140c1c69400e6060f80544d600a03200c030200c0b0080802e51083c0106882035018107000600c041c80000c0206500381c101d140c00030060b28001040d4000c40d240d2a045800645403040801c004034140320502c0701c20800302e0060300c000c03910100d1652421610020482c90700400b034007440b219910207e01071041c0c0c20b000503250341c040c0a8441c1c403e0f051400d0340110324207000131034150584041c40c5240d0b040c0741c4914080e40d43d100c2e900200d0b90b22161003000716500704030304c00c6070300d650210405c0001d084184807a9a08074031940000c1401140c210001d000c00610000041070000c0a00c00d41c074032143d00040107484583ca5050010b1251600e001040e07440500c0d90740541000c41c000380b071004001c8004014004410803d4030035042d40c494010140c01d60b501844082e003e02403059091026184400c0250740010031007a0401e1020055a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 117977005 1250 117975755 117975779
    0x41112011206060803042d05091e010b09010207031b03080d061401021515010c0210020609070e010506070308130209150103140c0a081b1207030605010302090307090f0204 75
    0x10140540101c0e40c2034904000440c0030341c4000d041800d019509003401d20541500340303101c1104c0300a1542030060742c2c0c5000210402040060300c2c0c00352901086103408500c896140e03980540780113000a000000042454520060b298a1031301607000e45081c928684400d240154041c3c40200740c951296000400108030000520708404500340104400d4a09007506003202e40100805044d500004002d00b40c0500304d9000d40c0d40014298640c0111016540040340e4500c08404000e40101c1100e08a4905580001e502403245968100319800551140c2c4c00d1a040c503c2803041c0b0740c114009212400c0006c0c002c800303040d80102100d0642c20800d10075000644080c0317048e510050001e0602c020294156807601508080380e0301c8209061150030446022680d5114001c036040030010107001007000741e000d88100150b0302004824031030300d0f0894105003d410079000d41e240c41c042440c003100011a94042d0098444001d8002c02622071189009481005800491070601c080380e4200804038030002540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 117978255 1250 117977005 117977009
    0x106020604140109020f0105160c090504020319030e04050a0f020d060801150f0e06060c0a0305040905100308070b18030f090301050f1003080901030b0a060c050c01090b0904111201 79
    0x150040c845800c190a081c510482100c0300c0d550709906016082d40035848400e2003091680f802e107429a03a50f20701e4801c40d208035080013001420070043c02c000042140040d0000c83c0928021010354075042c0d11001036440c2c46650103801004900d024202044a02e044da1185601c1661003d0100d03c0d800000c8a0303404a0303200040040c08950380d5601448004000d11440e00c002c0c05610800600d9800d00d400010303444140d105040c4c50300d060070000303403070758461000f91444c0320f00d03100844e4051009460094059040b5005000080340f03858001811551400008411039421280b058544001c4d900d490002c00e01c0144400c8611803c181c20081400040000384900010b00a00c26100c2d0f00d840105425201c0c05000340000c800a0028401e0340701000049008032607000700b078a6916040300005030041c00d001140c1c1680110340e002c0000b1042d800840d20012148105c05071400c4980032001583c0001c5a40520300c880042800180144e0400381e00c148010328010100b03a042c1801c4540d040c40b00d03d0b0907 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 117979505 1250 117978255 117978257
    0x18050702071a2a0d110c0d06020c0a081213030c080a090f06120605030a21021f0506011101050408040603090309050d060b090115050307050f1309020316030b0a0b130e0106 75
    0x861080c51010a0901c000c54402d404d40c500400da000240340c0041d82d80742008565071148907144449007c11000387d0458940c0b0450006031004150329040c07001c1d040d0090281502030070401400034034049100c2902070282517064460700d48500b20f0361100249030300194144024000c001100ac140746210800010040580707a9130304044100b8251560b0544205521060081d400303c003c150018a84d41104405620f03c00701110540415100403442c0c20324440d0354461101d6400e41d428103069058005612400c801c1e01d40c08102078228542508844045070040d01495040c4011b002c0903100c1e4100031042d60082c40e09a03107658488002520300c0920481c21940d0f165183c101c08001c0c1464100a401004420f10441e090200180007808510000301450304000000a215001074400c01c10b45da41055141c560b8455240c540304410000e520a840310310711819110301c101c400d18440e0203000d000300303000351403000d10600d00166048d82c2e41040c50040000310402902003292040000200d00905039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 117980755 1250 117979505 117979567
    0x50405031903091104050702071203020c1e01080c0c07031505010e0705161104110a02061b040503100c0c1203050f070804051c0318050718050702071a 66
    0x108600790900d0240030510441814100424400030901681414500b40e40c240c5000c912a80d032a01300301d0809520346c01c50310018000c800d00e41d051550008641c080340201f83c03443c000c200082041079886440c3d00c108075000034280e01c00141d4851008025181c100007140c2100d1780c0035160390340c0c11410044103582c0c512569440700100058031511042640248450600301d01d800301d40c0803491100040c4020282c0300c00038018440c3c3e040d032150352000c3c028904a81400c2d445000c0c05000070744850050700c40c4c0d650100f50102e40c1c01c043c02002c04035421500028004c0240c07040d2460610050328621801105001902e07940c5008031f41b9010326003081003190382d40080c4618001841203401c00c0041d090034200040340040000042c000190f0000d94404040e40d0503595000c1002180070306007540010103003c0c020b45618080100014000003507486800d4541d03906060355000c1004c60700304466a0006a0281c03608210140005050036448021000407034648040000c060744a03a42d20005003070a640 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 117982005 1250 117980755 117980767
    0x601090218150d11180105070f0b151002150c090109090e150c1b0c091305070b0c070801180c050105130801050c0a02010f09020f10021501120201110601060504030b130605040503 78
    0x58030207541c030507600c0c09007005808c0a80540382ea01c0c41100051008000e00c410700007181082607601c4c0c0c8141c1420009082985031112404025103c041c1c241d510180c1561080c00300700c7c041420029601d0344075041e583c01074041c0c0742410700b8001e0240400d50310007500848408482c4001c9070240d192245910785481030b5191400e26244a60b040c100d0822805500500190242da0b9650f4007102d81029000354408000d400038280355003000703941e80c402d19001c0d030f0009484070842d0380400d1001c2102c0c01c680007040840740c110500d100032041010001e1406e0003540003840698092000f80007102c081d9001008601e44410302642124000d8920426100d00410a0000c03684c4c24055914010300b240c0e01441010b240740d02080b481c9a8181c0304a01c80c0d1100144804058401c00c0b08107000091020303090001e507512404500e082c00d2240050380080e1025161450300079000a2031412141244e4449140c5451031b03c51041803000903101050088141900d000030139078a010b4203000381e0090300911364402c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 117983255 1250 117982005 117982027
    0x3040b0a090f0e0a0504030e0d050601080714060316090b04030f022803120314010e160527210607030e0c0901140f0d0b090601090218150d11 62
    0x71415901c00c0c49002001002840f2051a101e02203801041c512000314494035946030a40e01d850b01072200d107401a5400c00c5a40601600203001070480700c602058600c0c65859850300d10111491400d40e0350801010801b040c1280c803484014003444440d8034099560035101d905606559000782d000340c2d081e0340c2d01107500003076140601803240f125000c802140c00c40f4090401c0304158000900c0044c2205003072012480c007240c0260840400c40e95005502111903031108001968040305980b81d0045194415448400341d0083c411615110340d0b404800c1c079800f0401000180060b91003206541100c090405034201481a83d0724100c01100312003d010b0510307048000034202e030030800a00c07401d0b601200f0301c03d206440f1101d11905451010910f0010001038002041c4626100c844c0711783c12180407040320041c040c0e000d102c18000c3c441d03002034942c20703641c6e0650380c4241d001302502c20803044842c0e0400740c0d180c80c3c8025030400c1605000012820003811141105c04c03264000144081c2c48400141d0030081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 117984505 1250 117983255 117983267
    0x50604030f170403020f09071808010f0e030a120504050c0a2301020c1c1e0804030b0601090f05010507021201050c0705010e0a03020a02150d0c0e09100e0c0d0e03040b0a 74
    0x150310b0208000d0f042c580b4640004861b40d10006015014005131004038142610454070a17990b919050f0f41e5030326056490800500910311040d421001503e0400c0c545c0c070046011080b40d8524540740c0c0d4140140e00791200d108010000904115031030301c906030074038499454603607101f4010030081201c401303d1481c0c0c8a9030603031044400c075014115003286880c41890754035000e00d049c2c04030103014406155031840c6071204942007a103200c17201d50610000800b0411000f60010010342c1d1142d0028005625030074019034542d02c46000d00d4a901c2211607052280754404c4d4050011513000074074440e05180766181c9035085a1044d1440140d0050000c2c491003408002d00400c1c0b410305c0310500a01d08000d0b9034034000d450340310000d0001d20070740f8501100844443d041c1c00799001800c58a40400490307500703840103440810b01c8419240a0051030000032aa05005d4491004554041c0107404042d520103840013051381c07107006028503d40d515600856040410005000038003040c40310281d941000190281c12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 117985611 1106 117984505 117984533
    0x6031c0e0d0c03050616080907030b090c0a09052a03010611030706020c03030f060405062b060603050303010e011a09010c06020c030304030e1002030a0c021207050604030f 75
    0x244100400d1260040040c142c00490b1507108020a0311506002c0b03c03201d15a0700445020800326046c240c2f02540011107009a038000001d100c0090301620413500140c08455890b2f00700605c940f04a80e5480c011400c4009400e1080482100031040340300500640c400c01a2000f140e103490743e0200140c2d5515540500c0954940030200c5c1060b13030701c2c3c00c11100410300c214107c1c04502d0501f420b10802d8020311004d0291615040c2c4440d5a40040c00240f107002080107240111360042030113480381001441c0300d000516669450300c41081100c07003060304411400081010000c401290702c40803a840302d10700f0709002c5a41204d40c1481e00090086920018650000104000406a02690720502c4075001c0305c0c6040ea103215144100d85d240200c0c1d00031004151500504800b52400d0190303464800c032008101d030385007034440c80410581d41127a80100c4018201903420020841a1094681 = true := by decide +kernel

theorem cover : BRFrame.Cov 117805755 117985611 := by
  have h0 := BRFrame.cov_init 117805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 117805755 ≤ n) (h2 : n < 117985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
