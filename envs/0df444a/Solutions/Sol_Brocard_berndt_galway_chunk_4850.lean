-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4850
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:56:17.539727+00:00
-- url     : https://prove2.me/submissions/b85e084c-5ba6-4f97-8828-3d19aca261b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 872122302 ≤ n < 872302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 872123552 1250 872122302 872122309
    0x25111c110109030801060320090d030e030a030c02100903080d0b030304181e1413231f153008030f0a050105150c01140117100c09030b04030201020405 66
    0x2d52182c483e560745121949446400390540740d51905401c40c2c0d070302d48986481611082001d90314002e00458500d4240c160724102601c00ea82c010709200d41500424500c0307014160441d86020100d40b003074640f4904080382c440d003200c2c505407030700004105a10800c0388000a200c2074000e410004401000d691074030340d450040060b108511940d2003610360b01c1c2c031018540940714815050f64411040802d204505030380c1301c403058154004102c5001092004100720600c54400314160550541c0442c0300440c40f003840000b03030f48451500c500307203040072100014441000107001762690110907a1881c240d44c1d0030203000071001400d0340e84c4182490150803040c480c42d1540c81c6101c591501542d0400e54174202902c0b50050b0050040c1040c00303607030520b40100819104c03204070b5052100d4010005440d40440c45c00c2a002d0a40b501c6a0040d02c0b40c0600081030681011800101041e000d104445104440820f040181d420390300c0d0104c04140700302c5003003000c0340901c000b065116109100051401c0d80301c3c03000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 872124802 1250 872123552 872123561
    0x40201031e0f0e0606060c0703030f03020c0111070506091615030905061f06050f120c070b19320c0f22091e020904110325111c1101 58
    0xc0201d61292a02c1e00c9003c8184202c2e5000001929000c0c54400e107100d9541d5120000e2100400300441903404820080c4254150b03001c2103848802032083e0244c0341d801e02840c0d0080340c029180c3d8022140440d9808000190b81140c00049052110200340750581154106409409150516490702034040002e942848614451881c90391404004202c00580107540c80c801d0700140709014041104000840d203010661304001300710030071003d0669407034056413258010014000d25100302c4000388501c194004803445e11060b040320702040407020031207800294550940502d444030310300c00503000081c101101d810380e0150f582a145403505801d4210040140c1c45038042006908141c0a1740040362000c02103540108400300040c080b4031490340c5c070200203419013194040d0550340040c01c020720781c45680113032400070001c100181c2c4900c2d142000c1c0714000b4086854401d00400411200034643c011010022940621300061600c0c010380d07881c08074008003008840b8240041007440704800e0342c1c2400f5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 872126052 1250 872124802 872124821
    0x80f0c0d090b040c031a010f050f040b06030a0618020f160c1a1905090303030610120f020c0d0c0b070309050703122012071704030606120c1d040201031e 67
    0xa9060345240f840c1410505000d200c098006c07400b1801004000b04074010300340c082520310443d200004036808900050040405118840d0070120210030050344010580c03106088504800e4030b03404242c10000050220302c51f414103801c409006110354007001d844c00e81d030520700c6403180030506002600c944920441d00c5215000c541030348000150490f403c442006101c0d404050350800d5410b1240c4040002d85a000081c9603602a00e00c40041d410f10381c0c0700b080079004071400c0c02020004911001ca03140080d620181c011085403181c1060818968070400d66000d0f802d070050703011191070f158424101c0c0580070751030040c2c41c544104400800480d9123032061f0b01d03015a407a00c03042e00d00116440b40d816100510284034110b50411100c03139180c2c5c035914044a440310b40c4a46000506030b95015070741424060707a003001e03200d20b24081000c54811540e1846940e0940180c00c01c0c030b0881c3c3d480d901c0c00d1802804820b054020b4600f800802c0055000780c001031044a458502c030342540c194112440201ca58010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 872127302 1250 872126052 872126063
    0xc0708071d01030209150114040801090516060818010f020a0302090420030601140409050709050910030305040306112214010c0c0b0a140c01091101080f0c0d090b04 72
    0x400030480d00900080c9941c000c0108500c07540303207603d540c0016220000081481100808060b0368101e00c0c1c3c4140c080c0c6021140920801741c5540d20b602a440c020041500d0807180f61207a00072000340042c1604400040300d0146d9100c501c01c0c0c0e12400050742c0b500f0b00d50318450aa40d200d406a500010703150000c0c10b00c0c0f511981d001138803145920208001d0b10030000155068031000700010117103803081001c807035000108bc00d044580c8070885280000303038811a84949103243c40c01d014020142c0c0e000325460120b600031038049986484044440c13503860001c1c030005020030000c0000700700140207500314140c00d034910340306a0f0038650040400b05414200502c843d6545007413941c03c0c00741545448e80001080b0013840e21303c0803041c243c1e44074280a60313180100c18030124041001c4900303510424030200f40d4480407050326118100d611003507010b440c6205084031507a55080e048940c0d54031503040d261050000140300c682e245c9554440751080c0e8030407882450081d840780300c0c11000c0781d400d2526502861151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 872128552 1250 872127302 872127313
    0x70e13021213140a050d200c0111030d060e0106020106060f022a031e010501081203041509080406020312071b150204170c090f0f0f0613050103081321170c0708 70
    0x10402442510501faa14401e03c099004070b82e01000300250480c4500c4007070130207149151004401c0f034694001d59049020460a1480c0882d07002c10381c0e0300340d6040306c0050b0003d002d945d031104d405a54101c8444050001a13000d15902c0d180d06141c0c541280c03400d1495040680190003030b201080c00d10040c40640c0305041c3c00141c56600000091040310b00500418014000c803081405003000203110241028050b513a890b121310800740550350200740c3c02c1d90300820b003960300c6a0b2007801a4480e004108009600e0440000050f915405458134100003130100341c0e00d0f40030f403045a5400246660f240b03040603403a64248000f00b0300f034040f84406020340725600c0040c101c010780354041109428004040000543da5031080c40380c2d0b40c030031030035442d084014400c3c0380180782e41c0c190201d001d82100d2000d003500d15080c6400041484001c00081c0056810803400242081d252a400c60361f681503048084c1841d41d10240d520080b03178844001959250403e00c035070b4540340e05100c281c1c0c80c00c03400740c00c41ea08a400c003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 872129802 1250 872128552 872128573
    0xb06041d0c030d0f09050d0c0905042405040201091503061701140901060f12050c0907030b01030c0206010303090b16060608031314060904110909070e13021213140a05 73
    0x20422804050302a203441320b15080029801440300034640306aa000e01800301c0740800300460180c095001d007905070820070141c0b400741462200704031402c07543d004429030001c640c2902d00460059030b1007a50107844420240b898455441d041142a02c1c000040560b543c0020070400c3e5080708002e503d1780500f0002ca0a88202510b10300e4401d000303172003038980d42c0c9020010031599013401d1554084807200c1c4c0d460071400115007021130800c4c40c448141e0340d00506580401c88180d030990300102d83c12a00ba0381c2040f00d80d0303010701c05a035961001e001c040d004c40c041e19001c000302e8004a0003001c2e144002000043c0640c5640c1c0c415003520320940200750325800c04a0040c00e03c1242900c1c42000303042c014a05c0d05820443d0340070520300c0c031800f00d0b05402141c40f0141c9510144d4070000f22281c000c0042d00000c218a00154000e12040e42e40c2041803040d540303400c40701d403030031041c0c000d4031a8410000602c510986a243c2d480700c0045492004440f40b000011600e420a01d0a000d000c200328040c0000c3d0905041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 872131052 1250 872129802 872129809
    0xd0206071a070f112e050c04030b0105060c1203060d02060403050609011503030c1b030213091203020a0e09060a0f0f1e03050312060411160512090306040b06041d0c 72
    0x21107034200c1c108080c40c103c560b185030740062001c060100c010213800c42d50940c00e94185d1a4850030103540e400c641000d040c0090f0007030b10001413080f40c3c00340301e4031041a42ca40c0c0811a2070300c10a0034400c01039111120748034680000400031078000c0030081c100003005687d54081074158016074070540741600600704000c00001c007030040707521440141e540e00789000c0c00d5a030090f001c0e440c4003001904140c412418108410031481d44e80024640040441c00610150310300d20024160411044510000040244483d01c0c024001e4841e410401d8895000805100051000070100100800e030f11441902000401044001d00c100180ca001400020b00a080c01241e24074051031610413452031000150800101e6004001d0710360b002c4183c0080d0303910380c40e0b5a0008001d026103601c54988030740000340900303c1c3c400c00002c000e10386e8840c03400d41e0707000c050321190710580c0c2c0901540c540c3c154015000050000b8000700c2641d9000d9801000015114000000f028a000700507890241035440303650304009515 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 872132302 1250 872131052 872131067
    0x80d0305220f052b030203091513030e0103020a09180902210f03031006030b03070b0a112404020111030c06150118080d0f0c08070303090b0a021303020d0206071a07 72
    0xba035202030b01c0250341d14020041240701350143e140d020140c1c048080340c4100d01c14868803060782940e403451122428040116049600344d0007007240801c1c140002c0045a5000e4002c4e551081e55681b11905894545242075000300c40c91048580c440d41d0314070751000165207405102031403e6600303500c241110791880e4498a030003880c1c01018060b5100b88100068030081c008080309480e8280b0f40840c4400c00c1c0da01003407400c1c00c540c00c8244080300215248408960103120f03c2c402041d41c034110b41101c040a00c01c05900d4104000744800740c00d07400001405940100c900020f440c8094044910b000144800326003418029503000c8101c1455020700015507911005058050304614005000c182c40c00e40c80300d56031114107a0150500c1600d0340c5030f0b402c2d103002d940f0680c112600203500d66a0765890340f90050003046215811190700e90f008002c10142d10329032007a40c541c1125111201d08041c1540c0800c40308072120303101203034000800c010980011f203400260300b220545104800025082c811401f60906 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 872133552 1250 872132302 872132323
    0x10e0402030d020309031b120a03020313091a040b060f0708120a020901080703150506030a020c061e06061b010c021506030f06011e0e070206100f080d0305220f05 71
    0x10b5001784200e08103a070300400c040a02c40b8001ca40b80e0441301000e40840d400c100c0d0814000c1407809880c102105068000c8010081c5041d482d00740c1d152962100c03510300450b98100d20640c2c450090408584c0f06041139408144402c1000f402c0300e06101d240c03100c100840d484400300301d508080101e03604131842080d421054010040c0d0300b056090018240000301001d500038503820070140c0b01c100c84000c4081070080e01014041c040d0083d80c0e00e182200c010390103944004070582152081d071001966071010b082135624040e0f4421484541070319204100301e03450704032108201420903201e090782e152003001d201d8003071210140d40140c038103041c8030311244510050003000c160194000c5805905401343c0852024190b40321600c241c3c042d4481a070118003030400c3c682154024030001001d004402c0e40021309644100c600e0400080b00342e071103081d110f900043c140329500d0664480800d121007280a90420343d84618444800c0c88110684079002c51030031000e80342500d82400c512441c40500505200c000c048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 872134802 1250 872133552 872133557
    0x4050d060c17040b0f0a06090c110d090f0306020307020c040207050a030311130b030c0f03010e100b0708180310022a011103240316080d0929040e010e0402030d 70
    0x841c9031503100c00013084c2d4000d0600605440c0900004c40e2110954064809403009050070012210004000340c190144110300304121303c50a22010911489800c0d81002c1e5000e860b451881245103680c0c04001e5007000d0035400660040412070700c00c0d0b0711144042e080c00c1f0302600040c42e40302c031141000b4040b602c0d8010410080d10003001000741c1034510243d404121090f842d1402d6072a0b5034128a16000d000d0b00400d40550807002000103150921580700a003d540c00d80e0700032031f401da80e1742e103205094860340400900e490400d000018050300d01c40d0021140600250940303800e1011206404120ba00c0203c44903034070300d00d03403c5080312000d40c0782c07a07001e500a22900800c1860a02c1c01c5420090200130007090081e1860809002000c41210042d1030541002c0c084841c004074104a40c210f4078582c1c001c03d9603510418520040171403107101c40e01c1c05c881400701e103001801c0303940180c08228811071000c6000c4800400000402060000605000b03040c3c54210106908251041506007803142064a04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 872136052 1250 872134802 872134847
    0xa0303050a142a070605011202090705090f0418022e090e04170f030109050f070309020f0910030b2502070308040b0d0e01020c01090b360304050d060c 66
    0x2180f048010520003288041c0000448081d4507920421503205000c0000c00031400c050000807a030f8103160f1001301c0036102703c4a0308030b60f50315144100c9450003254144c175400400d4080400c11410942c4c846491081c41c3c02d880d0b181541c99401141c00e464004ea001000035940c000c2c502110760414582c0c601c2c014492600c5220340d40380c449503400118020740050308000c4045c0b0000564074018048506d004140b25403652a582c2d44c000031802071004a0340001018100800106058400d11400301281e900030540060000200180060b014005103a6690b12a00d600b010000c41c00c08800284a8440b80da0610740002c0c83c0c1103000209020f4041100940d407101030248005850715040d2010f6400181d051a20f43e02c40168030390140c11850742c0e42340355510004141c4812041034000018080c01041150035640722078481e589038444401c0703c1c5c1c1020128150f906540c003080c081c41d80c030b00c101e0303c2c00b12070501b074940c0d0004180c21452070b8102c846a560340d00c00d82406400c07944200501c1e400040501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 872137302 1250 872136052 872136061
    0x50c040c1b080d1e0902011803081b100f2307020709020901030209090c070c170c040203060402070c06090e090105010521072c090109031b030c050a0303050a14 70
    0x80381c07480142004003005408901d51000904680c025241e185000b0b600943c800790b8102d0039001000d00741d406900207406900c081883c00c01340c03107400f404c59504c0310200d0320709500b4180105c0311822000a290550280c15203180d6400711a0050325144102c5003030000310a8514001501800c0c1c003540702d0452a0016003c00c003055801185020880300d42c848050b07920a29000100c00034450300900d90340c883e050700184140f0000310340251001314400c518a10001ea03c80003000950004040800c1540e48801595500390600f9005145c004001a2000d0f0a0888658646060307500f1a00308400180600d41c00300668040500034a40010141008204c15414840070860f03442861900c541100c00fa840e980d65000400c0280c48000e00d00c4410060444500a045a1100b0300c60407c12180415490200710000010b10174045a1ba43c5501c410505402d10b0109021002041c4402d4062001d03050008000c5441405081a1184259800646854410380c9601280c2551030403090240c521000c21 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 872138552 1250 872137302 872137337
    0xd0c090609200a08180601150f022107060209040c111c020a0f0213110309010608030c0a0303090f080a180905100303080c1b03040603061a1608040909050c040c 70
    0x72a856100c0c0d140c450a195170310350300c648800007595108422032107140b0000a104900c9100841e0030f5070b0607030714042d445d44070000c103e940301600036504078003001841d141d00303e15030490010135100b4441c00b00582070210880c0000e088514840f00c04d000701d120001d904004000c01d0004540c20f9520790722074100269411002540d030b00401d24000c1281d1010400102590340b50790100d00e210244d400c0910005854014014040e0015039401b0015800c006010036101300c0807040c0d580e890100c5000f0000070701540c404170042c1c84040c506031800103004810350003040c0c01c08024045d603852034a60f04051131000d00d8107284c03020242e01c9501c08901d001c090203202400783c00c0301c8045030703058944101d20b17442d40303a49a91301d03100b0503c0d807c444500964110030200e4010000d4400c440e170540301002241ea40320704d1990300190600401c201401d00f00f100c01c1c1c0310782d000f401c5c40c0407840c0035600003802c05482c0c0200000301c07982241e0903140707070f8403100501d400307440e10f405544a03003045032420f20f80c0c080300a40703072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 872139802 1250 872138552 872138557
    0x1203090e0c09210303040507050111030c15070302160b010e0115020a03030f0e0703050a02040c05090a15020a120c060e0c03151b071406060118140d0c09060920 70
    0x7124410307480b051007843c0410044900c4829811014292540c82c01e191810ba5500e245503c200782c04201c00c072444542409020080c0c400460380721014002c207080041e5105a05003004002c24180b6900b130049400100c4805500c40c1a1449001c41a11950600004008400050b40403143c0d0303c240184c401c8a8540c045000d40349140c6c10f05003c142c0281d003100c040b015000204a01c80980f0030b08800000780710b80040e204000034026241000705000400f01100c0c54402c1751000da401001c01d0000700300c9184000c0c0b6507000300b60035106490380b104041e580c141c03d005444c064403001509170032410060194038400d10081d02c4c100c0009140074403178000441d403140301c0007581c1640000d0560000f5030f04803900844002d011342103198159a43c041c0d280901c03c1c140c0920904189109a000091f1a07502a0382060900324041f440c601c0000e1625001c54040c1d00c01035880b41e0403c0340e500204000407415800f04018015500000c1412410301e880c402c102c0d108924a12900e040000003211595024401c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 872141052 1250 872139802 872139817
    0xc0534060903120509100b03030c0a020d2603041e0c14120312040312090c0905091005090309030c010c080d0c09080a03030219020303061f020a08041203090e0c 70
    0x5001c220806981016a502e010b10b0900201031400d0008200d5061404603081c005035807101c5042200400705818140c0d80e0140742c540e00707080d0b481041c0380d0b03015190003481da205007071203140d42004170303000c1c6e180030080210515280500303030034080280070030480319074420640d1543c3c0da00316045990250711540990000b611030382200340020005500541c0340c4d2040404030002040813a5601e40b80001c0c40c00c403411084605400241d580c80300601c102e0945c0c01440a4640c1241805c0ca03020305101c40c50008000c05807180300ca134411806810060803150050034815109103002c1c0d62607030f04210903d030400e400100883e0402c0024420640004d2039003040e2001c0c00c0c2c4004000a0003c0c1c070b5a0181da080d000e0f600958002d00c00d4800c02d6007010b901d50018090002401c0d00d195084203448000d80e5680810303207036203600c18940d540000a0940c1c144025540c0340141c070403141d88070b0300c60310740b154603030b2060f0050b40c8440e03070450010f420b06400841030801130201008d894880d00e403186540040303000303042 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 872142302 1250 872141052 872141063
    0x70507050c100504080303040c0603050108060f070e011106090a051002091509120a0c05041a03100903021c080a0c020f0a060b0f0a140f030607090e040c0305010c0534 73
    0x800c2d441c0701072141040c0c40141c0105000c50765a824541130810103408140b01c1c0c0740c0060300f040000300d5001d40c04031f04a8040d0035001e0a0b5902601c9510082c0e501070042043d241c102701603c01450a0b512013001450300904036100070340446181800c0080c1460000c0c840b0f002803a004003e4120291a9407083c90b0407080980c00c2540c4640f180c41c0011107040041d0044070f2203105138030000080c0040c040d60502152001c40701003050f0a8080c2011603002042d41c1c0060313141e00100381d0302001e151030380c02c007071010740c480d00c103031106d0741400c400c0039808c0c0c10721220700000640300f00104542c2c890036108090300c0342114001804952071052840341d88110400c002007503c7e45642c58030000b80c4030392501015000005011120356511050310504840c02007650520544100805014a090100e01180110002d64030b14200c1c5040400d1203064440242044400c0d040c1d04200201140e4203100e15900380c040c42da20341d561000b81204c10703400400b42c4058580c410144081c0b0f0708001c00990503140d415540903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 872143552 1250 872142302 872142319
    0x7031103010f2a02120f130302060a02010c120b030c060c070e070c020301140f0604020906071707021002150114010c0501060816121505280c08070507050c 68
    0x5a0100e8050015191103011050520310700b04144070601c005803000d240e0442e002080c80c01850012690f0f039550250a80301d42d02d080091201c9400040014515151030307810752501075540740c2c082892035200f0340071000103035501c24220709001e074420400014161102ca0a006803510400026100d0900403e0248100000a901e200469041c4005001080128036042c4140742034400900148900841244a03501c4c0c1a4800182000c401945008100c8455448915501c180910000351f11040c10300d44d1100c018004403001a004050b0280040688042a030b00c4640343c1c07043c02403000301c48a2141c15500041d07402000300703040c040c0b001e0460b08117420302d8040d40200b0700165400c03080084003801c903509001000c50310040021383d01700b4030802ca10000e148140c0c1d0f402e0341c906664142100500b41c0c0b80c1c80041440c42c0d0001c0d00322581084800b480300d440d041c4040040c20b20380f07802d007107000c4a694450503600102d80c1c00404540e84008141030070b6250102c1556500e4464098440f204d2103180203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 872144802 1250 872143552 872143583
    0x4060e0a2403050c03090705210a0f051203090d0323091515060d0c0315080f0c090f0417090a03051606140717090916030f0c020703 58
    0x90089480081041074503018a1011110051010026010300c08001c070f410040841c000341c13101402ca07442180d60308007415100781003408009918503a8106255401c1ca55000450788007820301003800520f10030b21041d03201082c0791814600b40b0b240c10102c00c482c41000c1c0f04002184101084410303255280f0304d00003a0110404495541d032140781075003581c0c0310116034100710070200002031143e0800c0241c00e424802d1341d2601409a41c581c4112825500301c0c409111250450394185c01041d0100b00d01e042c080761898a000003007084448070761085440d9400090b501078807120521640d807240381d050f6241c0b82c8500d0101c00f200421440588020007450111240c0c0d0070a4070110190303489500001c0c003041c034541c0c0d2418a943e41e22841403c8403c0e800c51040c0004001e40241e01d0100a643c580d44c11a040848035195a50071040035a8113076580b4504000744801c9603541d440c2e00740702e40d26050014030500880c0000400302c1d040340340714640d0149000040c940b02900000d032042120350006c1940000d619 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 872146052 1250 872144802 872144809
    0x70f0c030f060203190612020103051005190e10061413240908030703140a03021903020301090506120c06180307030c24090b070305130602010b040b0303030c04060e 72
    0x4295001910000040d440c00080042e143c0045001d4814018240c10704444113225030200d86052290600e800d01035104500154062f07006aa40510226502481d21fa621404105081c24803081130f4441e00d00342c40b080c090681c9401d40d460300400e07043c0998210b5400d10b400581085100603101c1013049022622408681c00c1ea10074402810682c420560170441c1d00d82240744024440243d4004034068003c041904080001070340c8015070155034a1004840100a42c902d40c0e00c0046c1080816800300007a50038400340700c1d40c5c80151039096a0040e0b880d803514000208079040609014031520140d1641c1d07400030700004000c800560200c50391641c4803c070a00e40b03800d07602d1825010360980103884000040c804a1000e003070484282c05072346810b460081c1050f2580700c110702114004145090000e0102038504806481407500c642003007803400d00c6e200140450f41040e64441c81c0180e441701200201410240580c0030703070f460140c00460850070100c0a011250069000e00e80401c40d20342c04201450381d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 872147302 1250 872146052 872146073
    0x2a041a07050f100f0606050702060711010c050d02150a0b18070507020909031305090f13030908060907090c140909060a0b0d0b0405070f0c021908030c0708010e06010b070f 75
    0x1299803c4862a084000c000360103401c0d04114154094035011001070400d000b00220341c01c00e030380181003504d070100035550305803820300b4092024100803001944400041082010580b19282a002400c44400348030740d448030b80da00207207e00c090509100d01c454098840b00035003112500a1a01c001d02950741090480350341c0600d20010354494100001e100d21800003200601c0304000c620301314a0f0541d00c038820300088100c1a10701c00c8107019400001102182d44030b00da01c0308944130703280940400b0781c0d482640d45031000a40b0f9115050308122410002c2e0380c0c00e03101d0300000d181c940c200700142403a802c2601100d40200c0e03481714060105400000c406954001e0780d40084c0060400c429140ca0005086000615000104e240158585030225200a0040942c0142440030351b803036440c1e002d00384e82031180f054840c503c0c081150354840c0e070100b04940148050030380e04104100400c10301d45005a01e9003510269070703a491158100000501606024000311800c0c5c1307422000ea0b84044c1c9040c903014581e603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 872148552 1250 872147302 872147323
    0xa0605070e0a0b04050306091204030605040606090f020d050916060806030304051804030f051303151506320318030412030c0b090f1b03030d052a041a0705 68
    0x41c20b104003c501d400a001c064010b49200740c04544481d52561262996542e0341081b80100a0013480b0030000a0415001151f00611a5002080003551500750340242c1c1c019101031504c258003c80c406d8106989445130f5680322041030014180c1001d503c003882031821090244500304600300f4001030540d1410421178004040c0600852a28622450000c19292081d00c049001454610101464910513030550b101c400040030754140c013a00c0c43e500c8401901840301140c18058031456802d60740780b0780341c1c0d840c001014580c6035510102403903404584440054901561941c00c06a05000003070f58031001c0c0c076030040010103200ca070101d111420300d240d4000c81e0300c5081d40d0f0f100408404100755004020201e55481000c0701c2d407141cbc0301d00d44a08d445648800b9410420741c13003103030704a01e248a550b40d00100140068184c1c0c2c50103100343c3c00007003640c508480103090b150300c8a0b1121002d1610078180c280303091020420301d04040c00d01c10501010030a034170281480d030501094038800e0100912114034803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 872149802 1250 872148552 872148559
    0x803062418210102030103120804020f0d0203012307020709020313141905010f1109100f11071401020c0909070605071a1906090c0504051e0a081005180a0605070e 71
    0x2400c0302c110006010398000d0004803010046d0030307000c2d10000e00600d425030059034000d04203032078004a1001d2113100c43e28200300b0382c0d066403a09080027101103e0701c03207400902c07240d05500349a49001180685020102c0c4d1200441e14410410080d01103803080054a0f036541c040740361109031180840e0f903482c100c04c0050a44124030700c0c03400d4108000056000802101c03c1d041d05004419008514008030300441070102c0e000040003c0c209003407031150350412280c21003810441c110114864040f440e00300360f40c0ac104080696165440195a0104a1000054001c9403a00e00901c0d000300700686038080d5106240912078041103107400c10444104100a4000c0504809030b9482c00d40401c0c0b092458021500295070314250703002c20f10692901540c400c203031468a071130344bc007441c003c01e1000001103070039001e182c0048100082415960400410024030780c0800414580b00100010005c0341c0300a041602c1a6021100e161503502020404458454103c0e038000f446503074502e0305580c50081404c18950 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 872151052 1250 872149802 872149849
    0x2070b07020604020a050d030507170d110301050414011d040204090f030c1b0b3103030228020a09021c050702031e09150a05090a030803062418 63
    0xc040307a00240b038511a0740210740d44c403034540c4c3e90f40030300500421002e0040c000920400100f00402d40d0f608100c00105075109040f850042c95440307604c221490b00840003413a44001004000d1868140a4241901c00c42c001d10411549400f0000c100c0301410701c13800d680d24003108001025507072158000d2120340d4015907a0103c00140341740c028010302031007408648403d10280c40e4195464a44046030581d481414164688000120007a000c039841517134041442250781c08004c000b440020070f5000443c443c3e0014091800c002845240800350031440394022601c0b625603401581d549c044040899403031100050382e806085094141c1007549141c0000384c0f90626082c081c0592740000202502c4100b03c0019080000c0100c8059840c07042d1000141d00880480b1120300880c1242c0003030070b6030482410460f14008614010803c0d00e102a4001c0e2110b100100c104410740c1821070042c1403640d2045021002c0d82041c0072203007440c0c000c2c3d80e03400c00359100846014140c1d0300c694044286070710036121000b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 872152302 1250 872151052 872151061
    0x1c0207120b01031e031d0d020d060e210a0e0f030a050607120e06040209060315070507120302070203062215050403031d060f0a060b03040c061d09040b040602070b 71
    0x1c056100030703c0b003180c00e03041d0903044c62065504220300c0c0f50b441c0d906559510928000e56460a0446200300322140d02610301a4601c0c0140d0f42c0d81c8440403018481d08001c14803504c45a172990170320002406803c0030404012001c020020b4110172a01e01c000c0c6424040c40c580e81070b50204604a00d64205150181300d4008088240700000400d41d1141c11166203203d40380581541d0b03442582c1488078542c0d825880040402e0040c98103006042c0e0010002c4e0031901c42d1a6500c40c15295104d058079860082800001e907803007030103000101e00925102c181400d600e48086540800d9803070388000c003002c0203a800782d00d802c100000d500d070307501281d0340d049071564540c0040c503009000140000d4400310080391402c1c40840c0043c3c0e604282c0782003089280040c143e81d5483c01c075107074681c001c01860720340c545a54890125810135030301c019600541c05100f03180149814502c010b004000c081c5605a26568200404440c958070114910b07481503112540c6a12500e5524100010780070303008005000088450800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 872153552 1250 872152302 872152313
    0x10060b03011505450105040b0d0b0d1209060e0d0302301201090b0306090d03020a02030427060b09061b0106050303041707090908030609060a03080a090f080705031c020712 75
    0xe042c049056213880c40e90484a9005594920580c032881d42141c20902090b14000e4855010000720080a40b03400095070803a50b80020046031000301101007141c101060008550064440c80a40ca06481000342014581c401030764a12903450154040c0e0040c94030b01241c001445403011440180500c0c00f5242d00406a2803400380030309018200c120352070700401900500e000920140a00002c1001d810410140b03182200650703c0002c0c2e0700c00394402000300042e41092407030782025484440f0320104010146041c00000c1e03601d550705c10034a07442d00f80003000160791030004a400d41480c45c2c0c0400500c4040e22141400b41c0003641c0031725410300000c00c0020300d01120503504021080310340180d4042c2c544070b800d45800c0310701e1030310082d00220042c000601036042c030305c01c52034010000030040d456066881c1c0d140c907101d5000c00004400200c0301c6204100d80c08210041801420f22100601076040c10440400d59400d440e9401c0f0382d8080380000c1c80d8011034000d00403c009040c60b41e0314650b4001950414 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 872154802 1250 872153552 872153647
    0x1503161e050c0c0a0f0e1312090e060d1716060f06080d090605030103232d07030203032b020409020931020c071710060b03011505 57
    0xc88425000c1d1122108451401101e104e06403000d201003000c030941000344100c00c0107001050303106044408455000407540d860303410401640745988414540b81422900000600090b06040c0550741c591070840004004a01d540f207054942900607403164040b00c6004d1020f404481c1c05170490740741052480c00402c0a410040030348801e001100d94201c034444041f10922001d00c1003100140c002c0c8010320000f0074891131402540c0382d44a48075500010802214100700405550800d54001c00030f0341d4110069480804860384160406082d8031403441d000300782c4a110707200340300c4143c0c242c50680e40010401c021910f03841c100a00c604544070b070780366103002d03000754040c00203035109155042207921a4a030000c6c10060328100448501c85555001c12400040e4100e092965000c2c000d40001040407215666030030041c02210340100815081c01c5000700880c4c14a8005810850041005212802005032905c0b109003192800c5640c540580d4921000188804100c100d446100040c52000a80743e440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 872156052 1250 872154802 872154817
    0x1e100e062a0c0108280608010e0703022701030b040218070f0314070c1401020904020f03060f03030c2a0909010c03050603030c0705060705070504140f061503161e05 72
    0x840ea20025410010b40700550126041503103481c011118401d403845140418111300c6020401284551f1070f2482a801d42d81200d0641c0015070041c482041540303000303140003c2041b440c01e501d03460000348540f9900901c80c14000541101001c10102d011511642c1c04070300c00c1c5880c6400c0f043c6900b0500310040c08090340d500c080000034101100c965400001c010702d00e01039126901c4501105010340d6447d403202028035480700c0ca6550038040e40d0050340b40c40c001401000200c4a00301d41c1c07841c0510420000000a4005034025401070184c4840c0312030001d00305403c520303280e610003c440c0c441c80b1141e40540b500300055400041c0b960a01094110542045d10b00420310780703090200383d40f10b0302172583e0f0b8080c1004400a1342d0014400b00301d282086802005424011015a44016150707004078064444015603074601020440410264050f03103030b13172180c00c854104c8040c56100600c0c0d00120050002600c0f0043c880c2c00460000c4019000e03120000c0690b05a01044418141e801d20160a6400004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 872157302 1250 872156052 872156137
    0x509041508030f0c010510061b03120501142707110c03030d0c08060d020a0501030c020f0102030c0c06010806060f0f01030b03010c02031b070503030f0a1107080109021e100e06 77
    0xd01043c0d07856042000c074010b83c0c000d5620f1727001c5e441001d00747c880c03200382a503026400c0c410000d500407424000f500406000c1e01c14030a04084161000d003d010181a8040091400f0480b15881c2002d02e5200c0300740a801c5904da00e03100001c04041c4030550300700046008441d80c07600c4005610034160b881034010440da004a41c0f0343c001c4903625a418810310160107200290710150301141400301d0342c001c2d8070090780c4004502c108e5000003003884045089a0040d100c040d0391040220f03150221501c2040288c1c05010900040d000c83d043c104041070308041c014a04620550010a080206074802d0f807011505200080091002a060090184d02d0351300442c4a241c412245078400da518143c0040c405084a1028005500d4242c48020022a42d000550319208020100d80360402c403400400604001e40700081c0009091000ea01c10000c0f03130301e4107040508401c1307901c02c824200380d42e8a00e1030a03480c098a0030500ca03c0c0e4405400134006100d880c148074000d0f0300d000790703004a8442c04a030f00c16400c200031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 872158552 1250 872157302 872157311
    0x1b020105430228030e040509030c010612020907170403120b03060709081b150a0903080d020a1e0f0c11120f1014011202150406081006050405010509041508030f0c01 72
    0x100209108803c5040003401044c8194814140d0b410541d10542d80200d040003900e05201103000a107003500c060364807160030794000c9280601075240034154141c0180c8941820b450025403e100706a42d500010030140c144005030b601032800c10031507000480d0f060030003001c0e111540340c1444007405c4684c543c052840c4902c51400102000c00c40106050045100242800f002090440b002c0a007544480b188000b0002010030000001d1040c2001d0301c032000c901c0e0005600c2d01e404080051488102003c40220300d294641022035603500507542c0d5224000500c2c2401d1061181e08101c00440c585800c01900545890b2040600c8040881e08600144021003a60000004109520140c07550441d9402c1ca149021004100b0200104100c9200382d1002d40303003080f0120040d56074003154110741c2c01070010949110800030b08a0300790108801901c540d040c0070b81000c1c1024002403560084c540c0c401d0046607a054a54180d240c00c4541000604a001c11a82d845c6e41d61002102c00b40c1084601c408150b080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 872159802 1250 872158552 872158603
    0x60809033a05090709020c010f09080711030d170a1d010204140303091f031b030b03060f1006030e01020405150c0d03050408160201120603061b0201054302 68
    0xd002d080d010b429114010b083c2607003031541002c001c2d406000e2100503596100304441e0034404c5030091200c0e5a0089039226221b000d14140003000d20a28601c1c6441f90b000400b4080301550000c0301e0090000c481c4c2c0140340d6a0340d50b6000360000b00100b034039140304801c15540500000e10150010010396a588000515158000702855a80c1c091203030403952100c14141c801c1d0f03070000d09140b101c10701142841c021811040c4903d107000283e40d144803860000380c40380285401410200040390304601c2d1040c1700c42071403070000b03100204080b10b07020380000c042d1515080f14003c07400750140c8003d40300c010200100c0102c1d020b4480c0f0b4030fa00c040000c141c01d0041070040f4595500a02c0f5049c81560000c00b184d28102608800f241c10b91401d1004a0502468980c8440c002c400e030b100740d02c0a540704810019000300c2c00c141d00583c0194001c10081168141001c000c2e011a4600403070240d03820056035210041e0b1800700d407102c0103001805a04066040c0d0841c03d40300c0380d0000360020030491407000644120754 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 872161052 1250 872159802 872159917
    0xa0e0a0e0703121d0310020c12030c04030204110307020a12180b0d0b010f0504030f0602040b1207030509030a09121703160e0d120c06060504060801021909060906080903 74
    0x458003013855050b0007005000340f0f01d0b04160010030342c0c0c144000035292121001e00d007408294109860403000c4009c041010b2045041510640002c100443c02060552904000003980d134003064100414111071151510007150096104091400b0306d15200f901480d04c07004070509540013150085010703070801ca10440654000d86504503c2c415560b1424074140c250b440340590041e01d1a403c80b0f40340d500f0880050701c0c0c0740e0000503000900e0340b1001140c02d820907010007802d842020707001d041c164008020640c510b0383c114030351a0440e1103102280c0f1280026040240216000789041e140e1003038000100034903000381403580340d200d41d421b40b100440341c0510028000447c041c0d0b10000c1c9041c8010440e500454080c50001e141a40b0400010914948034004607068030800d40c44003031980c1d00483d10100c0c0d00601141582c5801039850460034452901c48014000c54203071268030240031050000c00c0e082182407045402400008402d0800c2960302203032400b880c0042e1042c0841c0f20002c0407000c5c0c8150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 872162302 1250 872161052 872161097
    0x1e04050a0b060703080903040b03010602030a031a0a03150e0a0b010305071a030c030a2c0c12060106080403020a0602040f080d11070b0c0f0708060609150a0e0a0e070312 74
    0x40c0241042e41002d009540917618400082d140002611052100003200d008004c0118003a20031070303010316100c2800c01405802e58202d2450354009101c034000d40d4010351210007002084980145081240c000c500070558003c00711880310443e14002d100000c82440700b618145812244103004a800040c2d95501000050320783d1a0029400001000883c01c05007060010b16000f107041c05e0b001030443c4d00c00c81c969075104100e10713520401c8200a02203d200c21014803007107141e60420340c1c07420100a1401c915070345644050052405004074180072405240c4200443c0807034907031168003159074030345914034111508807600c0303041c0044c40f07405a00c400b511f215402d007800902c031820061112904200410000d40c0007440006180e2081c107219401c2200704104510040600380040c024508105e0305100402400400903180f1070005030801300300c0c2c1c0790001040c00711a50700c100e02005443e03800700e0304003a00c07908200164a120311040442401300d465032441000c04281c03640a4803c09402201d1201d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 872163552 1250 872162302 872162321
    0xd03050601021b0117091e0a050a030f2a02040b030307052a031b0301051e13020d06020304030f030b0415030f0321060812072f1e04050a 60
    0x1600980c0c11068802c0a5018900004005061800385d0440107a200d045482c000c49030400503a1104034800d50059494840b2409603409901400104403030b83c4a10f0317079a100340c072001000c00141a00b10903840388103007560180088010100c40b80d085030b101c0440040c4100c17101c1644520300d044000000c510380001105e400c9903204014201e85a0408500450509030b020320740d808088442140700a66000d2142211305603041c00302260760b01800c424103085402c014221241d10b09213078401c503039034100841b8043d401041d25418044a000c1c502c04265042c4800d00001e0116001100384000c141d08100ca4510036038031590100041060340e02040165401401c40c04140e0711480c9050001c42c2112085040359030003810030314200070040d580014143caa4001010010f5907580e4240040300051003014544202c1c140341c1414103405859240341100c4001907038548083d40c42e03c0311411140b100c1c101c10b481c0402080c1c0e2150300f10140c150012030102c00e1070350344201d14003070015114582c01d110307e0441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 872164802 1250 872163552 872163557
    0xd060b0a08061e03030d02040f0b072604150c02030d0302190e0f031911042a030b03060109090b0c0403240f110c061014150c01060b0405030d03050601 66
    0x21500c680c418040c41d00502c144035200e401102c00300e1403c0340c5003000206070b81c00400700700507502c80c0f9002400140a0440c0c0040c100c60008000810220300e9080401c180d50300b031080120782c4a550103401101510595205610744141410403061154004400019942c008e400b0340e2002c01403450220124480c81502002c00d011f032040001d043ca12079524030340c40000c05040c01d4182d540c600002441c1404444041e1401c100e0340c00980104010440c90b1a2000400e035010b1003540c828071100c01e000b460000d03494008040212001200360f1203070300550696500a0195a03c550716084110040c101c0440c017030b42c4144c28580482c82a041403800ca604030303500030307440c4071880c2c000401c445035410407050034400d519111900109003000510072602403007444003040c1d03946c501c1240c00c00e0800c00000c10046c407900540c2d40c10004e5080c1c04902c000003a500f10b6081c0c480c1c00c3e084446600c503000340000c07841150302c3c4ca5400300710004070300010402c2d03c000f00d0071030341c01044a030f108505486040ba5036500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 872166052 1250 872164802 872164817
    0x61e0602030a030209030c0a080106061d030706030b0f090a0b1504030b0703051f0e160e010e0f13140a15080a020d080c0a030e10030605420d060b0a 65
    0x1e14070071340c040c1090820040a64014841280018002465940203e980d42e552450100071594020f40e0361101c1d0500400c0d04190440c0c010000707500d480081c4549402d142c0c851b041624181e8890301c1f0500d142c0001840c201a40c1007042d2400d00400d408280c15000308803a240b07400b041e03441101924200c95010b080b2041d075940d251000c0307015201c0030785101d0710065446224807003501d00c4a582c45c0a040300070404800c41c641400c014031919404880c020034031401406240143e6445101d2a90f6805e040d2080c2d100300b08104041050640700d80480321415142c00031401004410700c12080c0100c99201003803001103854420f0101d0340c480c42c4514251603210184070340c018140002c45403d0725010311850b03810b10590070886400e10000318022400070324001d12801c2e90749007054840c02c101740580b90403c0214201000715203000f1814902c1148400401a004500f603418210a4035000078031080309022002d0707c407000c409030890180101c91701d0a0a0380492032107001c406807074520400b55181903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 872167302 1250 872166052 872166067
    0x30b04090b1f08031b0106080a1203050106051218030c0312090c030d020303160c060501150305011509031401060f0605070c0e060f010f02101e0b030a171b10061e060203 74
    0x4c8015205044c2e03d0b401c6d505c1d5070300007407070000a20401440d00d024643e49107007120070f111300070200d0f1380503040007090110074880514142148c03001a03a00c0030080c0303000c40c288811146624994060f102502c3d00c280300009000100304059026a402207450404442c0b00341015820161280c80540e01c88005900a0001400c8080410800d18600038035040405642100d522a9016254241c00001c2045a111200b44c440c551500c40eaa0052401d946101c2a49104601c024890319180c030002d400141e450785050707036408081d4042c030018481d00b801c41c14026a211005400c80e0130120040d900907248404c00244850005009032003020006d2510814400c00b100664051009020050451040140441c11a69148104c1c6100c40c24140d4002000c400c0141c00801e444140c40c485000b40c00c0840c442001441c1c10300c0320240d4000074600c40791102c0c0390000c0d000d0801950040460783d441009802242c4000d40c0c2c6c080c80940d034101e04c0d030602049000c052900c00b11103904c2410b0043c0c3c010800103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 872168552 1250 872167302 872167327
    0x3050c0a050a0f0c02060304060e1905030f0703141201150201020a0206221a060a0504090b04060e030c0703120e0906010806061e030a0c02010c0c080316030b04090b1f0803 75
    0x18110070030301d04003100c020650385c002c00c000b82c0044030102c80140d030710521b111304880e04200701c6400d076545400701c100d5041e099650070b03100d005091248410704408035051040500580d0b0640308060a881c8494403510451000c076982f103005c0c420074214004d816000340040d031042c022030303c1c0e11445400a00c00c503203403108261401c6030340742c41a00b00000042d1001000034a500c500700e4074520b8081c404151070030144100001c20fa00c076400303035104a180000220005488100c4154044e0300080001074503d0380d004000d0a5121700c18801041d400341003004020020580c15000b4400d0b0117a48080d000c40861050000d27a130380030ba40c04d5010542d0000041c090f4602880100300c50b201c85590540d0f901c0b42d002d8032004c00c0d0011b130380c070700c001e076032180c0d104600c0aa091080d41c11140c000e20303001c80c0e01c0c03519461b4441d081c030016107584040000c000c01400705074000d0300111030100000d8800c00c03401c40316040c0712401c4502a205c885504880204403440d400c01e075050310301a9076000d0b002e90325045080c02c0f00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 872169802 1250 872168552 872168567
    0x605150414010c021905010219150213120302030706050c03090604020f040605040905030415050a120c031e0b100e01020d080612070f0305011503080d022a030a03050c0a050a 76
    0x34281048180c10703182005851703c0ca40b48903624401d020f6490020305040001e820546d1040078040c03140503d4480501081c03004c0d82d180c0007050152001a81c840b544041415401a65080340d07000c111240c000e1801c059001000b48285c90146400304a16198400d030307883c052009444031802980000081005403600e40e081380f652480c010400a01c407507480700442c00340c0e0b0745a18151036503000407130100618840c2c0344048407007400b01e182c41890082c2e803400103000c801040a000c4e200a0340d4400440e01c80f8020350207913003c1c00c002c030072114012030323890f40c030a016120000d40c0c5030144000d00508405076005040e080070003181600500090155a102220300300c0c0002c0505900400d0f40351000e410344c90900004000c0d0603a800325406960450504c2400e440c03988007401aa00740f240c90400200b81309a003038a4120240e81005030703441780b12410741203000807003100c8140c0c02281148040700b500c41c004010000b50b0707980c0d1014080c0b5034900003030a005010b100240004101d04011055a0b941b05442 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 872171052 1250 872169802 872169839
    0x604031208060406031209140d02031e01060b0301090204050310050c1c0b0d0b090708060702030426072303030310090207020a17030703030612050a1520070606051504 73
    0x2c0004c0040d502d407a000000404c0420040100301d942409005518840c03030000751100c001c1e5610103640b540c2e940403070b40d103054015011801c51203101030a50503031000e401040040144410158503941c4481c1342c04000c0d0b0141c85154400e104010409128900303600503e403250000c1c610031410146041103d155004000d02500c0c00996540c003010040c1d0b456000100c070507401066280c5191410503141441e0100941010701194400c904010980d68000200c0d404d640d003000309211000c83c1c1c181c00341124000c040c5490312902410320046482c0e03002e25514625444c0c19141c5000f50214003050546a1009442c1c10802c034150b15024401d400c000d8006140441c8041c060b030030307240e035240b2100c3c0d0043c1ca02e07840520160000140700b41816818050080500740a10818074041d00704c0d61001e07604c05044400501d02000f2500000c02100254000c1402c20b1a40384000142080c3d02c10494980c1d000030000c030b42e5a0f180203404165070504614901d07440e901c038485580740c42c0c280007810009035040c14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 872172302 1250 872171052 872171059
    0x3020a02100509300307121b0e09010609050a0902090a0b0d060f0506040503100f18081b010b101d0d060f0506191208040f08150105060403120806 64
    0x35681c0015580c0c0e01c5102d00c038100d0032015140114101c40b10000142c40070840c2c07011000109004d0168054200880c3c2d0458464180425504c08403903296000d02444c82000d84510300c489200301b001600410141004407044a94103080e82c4c07654404c1e0356500c0701f4010103030070a089107020301c07e1100c85d034014020150001c107144d0110361b440e88800c2165010104041031551038080402540020022000242c07004443c0a403d00341404c000c00c0d6105051440154801c2e152080402a5101503010580c061900d1041c00782d140ea490404840395032210120f615080c1404200070340790307901881118082c14000301180c60300088079804540c80a0341003404445a194020400b038143e07510002d1000c100e110340e00211fa041448100581100c07802071071940580c507805240b00052040041510075156002810f031a02c00d440e0402d4402c90260b50030007a00c0c500c0071400403400c0400000c0031000c041c840810089180c0c0c032041480b03418055880003c020f404100c0c4020803250151403810b078441d5014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 872173552 1250 872172302 872172313
    0x230907030816060507020307051005010b27030106172512080c100903020d090315021c020a081f03030210020a0315090c0e09090d0e0d0602040801380103020a02 70
    0x143ca4180c00c8807800ea40f841c0150384002004010010709008401c410608103008008030340c5051003000303861150b0000d906541c105480106520800302d0701171100440c0c050020000315844070302003050504018491400d510075107100316420803000190003808804228090142ca10304802100c0109880000716030140003440061840c0c50100642c500344151600c02203142c410504004e0304180b0000d066074104114500c050001c90030b4080c1c0400c0c4581c03401c5005950b420f80c0c541841c04004850038691315980001041060340c0d51058110340580398100e99008203101c080c00c000030404503440010050b801c8040300e00000c074060340c00b40856800c07506020810035000003105400d41c200f0780060740c9450781c480c0c040740c1469120351052903a1400352031080407030400450003650303140d8100b4481d04000c00b108100d022515900e11709141c05611107020f54890b45c54200080c00782c40300c100c102c4281c2c00c05480c0d49240c0f020b9400242c01d003200c4d001c6016190444500110702940c803081d101810761044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 872174802 1250 872173552 872173597
    0x5030f19020303120f161106071218080d1104080a031b080309210a051603090e0f0411091528030c051203090102120304020f0d05012309070308 63
    0x7207813807611508403030302412020b140a503001007110704504020300070445447d46c22460030b040080ca65401c03840909002841d000c100743ca040c00f810704400c041c41c074200240352203420072040030701078010b56044103002c0c0070204200c0a03410903170085200e0140685c1c000740e21400803030701886848941d010092080c01e110850b60700e07907104940c4103451440059002180d121030a01246c01c0b070f80b452078007840c0043e00d0008002401031903405120041c0c80e011148402e21010140a0300c540c0005200c6a44603503003034940003911540c0d40c40100d03001c0d500d10351007100c003488a00d03004607400d00c204c0b102403026804502500c180032024844906c00e0001d400c0800044000913081c201c41c0000f10f208940190000c1c0c24402808100001d0101d1070115500900038241c60360b17004903600e0040b031840400b0325102c2e9104e000140310001c6080c10140c010071001701400c10301106404c81090701540aaa0840500c0c028000c4194030340d003103c0f95440b5400a103402d000081d0280b00510746100000028600c2420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 872176052 1250 872174802 872174827
    0x512090106050d05100510140603180a23190b061809010c0e1005041514040f03021c080d0c0c390e06060703180807060905030f19020303 60
    0xc04030016a010b0b17001408500d4041c905020311603225030414485042d0501d403842600080c2c5186c0d0085210386000b20000396003000424110a00e0346d900d0b81100d00d0110ba0381415800d011203000081c094840140000d010550b002411441c404a082c000240b0119035840b03035002d00c43d000d048039500c00380e8500d5031013103000c008801f2070090021000010b0f0807410114040c2c40708424038401030050a1500c03c007803030f094104042d03801301c0d00040101d280658940000301c0750a54018a4101240c101041c04242040384003002030680c1e03c280c6104101d403d10502c4a04103240408004000b0402009030b0070307400d0195080031442c0206410600352111841e0744001c2c3c01d410203030001c244150b9031030720300501c1590348602803041800880000002d6041a0815007122002061640503d000241d081d003011b1249001d440c1106802c0c0c500060981c0340c1c50000d480394100d1043c00009400e0300c0001c01c45240104002c0c010840400045c499654808585c2552a140d81010703a414003090151525950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 872177302 1250 872176052 872176069
    0x5032802151e13051c020d0314030703022104150b031204030609020a05092505121602010507170a090f0f080304051006120212030d06140a1401051209010605 69
    0x1c038100b056502c90b603940710034090314090740d80800c0c4510540b402026400b0241c6000a640c16010b441c2c1d070b4950801814240d07003244041e0a480200c0030000100b1400300d5041c1e01030306800e0f441401810207841e107038ac4a048542c4056801805660102e0341050010341355034407410f103203030300a410740b82d021900100381005600243d0045e1406c980720b0b020501146450159440945400c94455600f4204014840c91410b40741400a00202d4110b4110b14a2800360095580712540e24000041624100e80d86803240620358601801660a0501080d0140e025601e1100c2040749a058440d883d40c82c0d44814001c1e00c246402034980184c01c10004000c14034aa071000041da0040100c81d54034140317490200d2414030351400d032600ca9072401e6000d12004a82a000c04011501190420300d41343e45403508030b0130f52141150745800a40ba0100006100c20401c1608001c0c0781c04944050001750b941d2529a0700004c014621030006900f00031361000701c503482c040d490700403003641c000041c401d841e40c01244402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 872178552 1250 872177302 872177347
    0x5010f0e07051c08040314010b060c0109060507020d02030703120207050d0c1e150f0b040f0b120601060203161103030d1416140912070605040503280215 67
    0x9030800003007404542002040f07910440c001075100030421880b900e940005004900005110791038560103c80c459409401c40d8420381c20041c90390341e9451001c034907030b802014028000c82d4100e0500d00060882400450741c60501c84e801d802031440c1004907a4129400305a801c1c288192a50a100090205408000288540003291907030002080c140c00c244d00107250342c0300c07044005805d030591100080d11500f00e0070b1514100d0400803519480c02488c0c0c3c40a4207520f5501d6402a00d4440700c0754441029410000780c07481c0c01c0e07403204103125401081c0d0b0348880003405074101680c410000e6044151401c4080c4011a0252280c511103c0460000900310f91044600d010030701d880c1da10031908600000c1d6203640205651480014030200c0c0a8041c11003582810801c40d50000880c0030241501c48107050344090803120140d0303281c03e41714000a4407036040750040714002d224118860782c2200e01c50301d0607401c0c0c960300f00d005a0a8081a0f0810414440d480301408007050188100f40307082210f034810a514 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 872179802 1250 872178552 872178581
    0x9090a170a2105090f120403140307060e0102091810030b0603030f0409140106030b0f190302090a240e060933040c0e1804050123060120060f0405010f 66
    0x12070404800c80341c580780317a4400240d419040420200003031000300c4211003c90758800522401d0010b405c0d00e41c3d08500803000064903003428140d0301c1004980c19070007000810342c100c131060302101030341c3c10764902e452045698615045551200780085002d0000060740250300808492401502c4041c11203541c000743d01c441c491036125071007404000910b00f0380e00c0c09014645420400705410030b0015580f0010514100c3c010302c2034040d820700281c2d240140e03001031a0050541009401c0c0f8000c031500802c0010340746120016041070402d4000e03c40c01d001e40440c0c01d4070f0314152450f2190700070403890500182800a040003c880050a01000e198500403411004103078005d0301c048c50001c0c00195524048690100610900032698681c1e170b82c0c2003a001e03014080600e20040e602c03868803a0060202000c25000d0018110200708000b202d12640ea12a10080e66660301c00400301c80c04442d43e0352504d400c564150066000640141106002c0c958801e004a0011900d007d085081d1012a504171302c82029 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 872181052 1250 872179802 872179811
    0x319030603060b0d080a080606250b0105060720011b0f0b0604020319090c03080403080d060f06050712020a140f011505031207210e09090a170a21 64
    0xb0301086101c1c0d2011440152040c49032200c03160784078229840b6042844051002d16000718000d52100002c0d255a03092483c207910003142c045c80aa10000514032040350300c031880c0000829103060100030744401c2503010060501e401c603080307061014501c000c0074450400000b40c00c517045211504075030350302c0240103150044070b0102c41d0900710380080c00280624010340c010003c0c410030050020f600c0100d940d00d0b8a00050f00c00740b038640250741821f60791000d080d080c0007003008818041c030000100799080e00c4040030070116a841c0840480301005100d1800418801c3c840325020071620801707980484110300c15070384028915a03801b070008801085401c6a6449a15494003120702441071410610b62040c4580c086858400066034884c03c280e10305014101c08240b05041102d080c806011600b104161509403a5a54400600140c0243c0604c2e11600340e80010584080c40400c0407032105803c9a22004034110031a0200301503880341c40010100591480070f4103482c00d20000c1d1215401010f4000315 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 872182302 1250 872181052 872181059
    0x140a020123041a0402130c0905031615020a0201020a080906070c0b0301140a08060411120d05190806130509030409050c090f03070f1a04150201061a07021e0303190306 73
    0x10318141104140c82076804220f0144005a40c0e00c030070751215401601004980d0328035040040352140c60a6000c10341503c82c401c0e43c803644d40c04080301e101c10f45042c0c08002c0784650a03076108070794882484d90042c1c0940c0121481d140812680c2c401441000d1000c0e11052600310301c0d503204902c0c28010b41c0491203a80c0c0100040c4a000b0410421007501041144c4070380d84c05040c49000345c2c540344080d00c010100801d8000b0300d01542c640e02801c0000180c40d805540207019014030140c15980000e00a04007040d4a0714070000d140e0158101d5030140f40003030060608001d181a0b144001c0030050520f543ca03110505c00001c1b500e5843c05813a1248080480f4107132102c0f0400b0612035030010035084140300b500070b02d10074807009245400d0340080f54144129486214100d12601c1c86511550b00031a0150381c100c140000100c0d015003180702100c1c00018603900500300f42009001c1c6000d49a00250b0001d0020031500f000d03142408609001003000703090740d140c800d40e1a640e00350038600100e000302107500d4405c2007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 872183552 1250 872182302 872182313
    0x100f02010b0103020405130b1c030c1109010806060405040804050a0b04090f0228031b0f0801140607080c15130627150603081303050715140a02012304 66
    0x7032440510030308095083c182407100080c640c00c20080104422540c50701d10300240d44ea81107031400c444142e080e80555140140c10018500300d20408203984070000d201d1500c609092100040b4101c0304280c001d0881c07615010100000b9240140c81a68241010310001c130300c03075540d8003400700209000c20b41c4035542c9181100d000b0990300f03460307070b025519403040c051392210103103004040c008205420766946c000b0316104001d0f00209103035094515162824102c015246030041c2a0980c00c42c410740399411140e0340e03050302040c400440314085400042c00d00024000a031301d2806407401c01001e43c142e0b100608814001d03129141d080701c0900030840d40100040510006210340454401203843e142d85003d12541c2d414036400604400500d0000e00d11903100d9441c40a81c800c001031a4003654180d0398941d49d051034040c40079a2302054649000c2c0302c40c0090700c0c600200039074011072107548030700d4101d241e00c401070340072500001c030b08405554803810701a901c142194542018000310000041c90782c141821701 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 872184802 1250 872183552 872183561
    0x601021204060f030617061603020d090b0103031101050601020c100311121e040506010b03041e06050a2a050f0d0e010917180603190f060806090610061d100f0201 71
    0xf806c6a160096030b0514900000301e4020350000741e00c0070078800c856050703a04400034424550501c000924004406081018000c8428101c1e4029680c1164034030f00c402c020b6003200d00c10348005001d41d100281001c0d0b10308020b040c1440d0f034071a90600051101504a454010344e00c40030540c040c046942080050848280081c51720380047e52648000ba850583e030b495079140380c180141207110801000003010000c10048103542e01e001d8400180d181100707854020050607042d54819501410001005007822641c0402680b40803164048106034508410035110713940082d240f0b40b540e84040050801070b90321400360030f48501500c000080c01c40b0860800013000c2001e15500007000300100440ba000351a01d8070400604101240c2c001d50300e40310b100003003800b070a60440000d01c2c070341000130043d00c02c11143d000004503203444050720140e0751264501619140e0448110007019201c42040c048644030301040f074000c071003401001d881500d0f0417000821a4085180c402c00251441541c0300c001903080c0207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 872186052 1250 872184802 872184809
    0x1e02030426040e0c030c0f0c0601030c081506062d0301031208010602030711130c0804060f020f0d0504030e120102031f140f0a0e010b04080c0102030307170601021204060f0306 77
    0xa05600b040d06065502c040d03040c020f0407405420002002140c55044400300326840100e0421a051f48c0781881007111382c4a030380074482502d548141d0580050081004101d1403140700c3d0f0344040d944130341e40341001c0045c503801c05031071044003c0408040503103240f090a9416182010481c0c0288c596140d441c04000c11024000c00c03204100031000100201c640000c1030f1060b5070f0f4000b10038200040c4a0010a480083c0c5804405001d414045012043c6400206542c02035004210a103e504001003000080e48103081142603140c60030880c906d444080ca40c00150003138864a03008100d444c80d000000c0c28194111024451654004180001074604c4000300400d0b2000242c16910710f85807200e42d003040d1f02d035004540d00402c5900100300c1c1c41da440e4001c020260402c2091001c0c103503141d0790303450f035140c105000b21b40542c1314011901c0002d40c000000c2c0c9111710043e5603011140c103038a454100d58014080c09181c154812f140340820300200707000c09040680305aa5500a05404030307000101542d22070750 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 872187302 1250 872186052 872186123
    0xc0203071407050f01051e04060306180b090f090102070605010e071b02010210020d0209090405010e060c1222170310060e0307030308060d061e0b0f03101e020304 71
    0x4004020f90b40b035401d4003050f14542401c2c015140d18011003490882c581c410801c41344141c0020700400d00541580c00f203401c0d41e004ad102d00300690b0580504804071030300d89005561201c040c8000404441d80300f40403039801201303400050308107201c50361040e042d01c40a800100d983c54003a02000710441c2d104d917103803500086c000c001c00380000e05500003075100c2c80e414400001241d0002081402400c0e1601200c440c014003820021191070f003401c05a000b0701d010541e45580340100c10101d0840080c507000d0341c007500300681c0c40501a85552003a04804400704450440c0709000c0301800707010a14130071b0851a681420b8805030750701e01d0002d0410f032074208140c021000b40142840d44401a880003d85402903e906040c01d5502d40c0700d00d40010003d09040c7c4c801011142003034a410007588480390f5220391183d02ca07505000036000d050410150128450301300303130182c1c800200e00302d4062640d04036455902d00b41e1040400b60038950390841c00d83e4000c031410b4030741c0d00351900e40b100040c4029051201c40112607 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 872188552 1250 872187302 872187313
    0x4030c05120118080a03060324050c250201030b06181c11102321190b04150b03012408040b040215040303020c03010605030106060509041e0c02030714 66
    0x5115902d1508030820010780850408299564043e02951000c406035400c05981c4000210207440c141007000c81070a188180c0b030600c00800ca0501c90803040c1c8800103925140a0480f50cc038001c5000000f40008042c0e040544410911311140c464000a140d041c3c050104078520011820621818550b900c0704080c804158442c00008110320041800c402202200c41c0820040b1048003203485014101070000d0224401103090301315032003407004013003441020040800c100d803c0608220000012600080803901d2810110118440ca521480988200900005100c0400062031900e05802d40161008a40000041c010b58030390440341c80c032001c140d50505500014001000f40341d008090401000641c2d04404076003155251882c6025142c0c15003c0c094079143c0d6418001c0d0345641d0254002e0081d460f20801151a0806000e9070b0180d41c00e54580d03a240590300d1741808000c04040d200040c40d0703902c003030180752240d285003d1300d075030b9004d136500a549030102401e00c02c03e00c2041d01c1d03121007954040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 872189802 1250 872188552 872188571
    0x5150f0105090d1a0f07020705010c0c05040903030e0105130218010308120a1e05011403070807150201090210050a090b0301030203191514181617030c010204030c051201 74
    0x46416040d0309503a4030b41907a001346000d900320b50060a081041c0a504c074200b10000c11410080c83c42046603900b110400703944e4000654290030540c00280c0410669801440907051503003001141134031034070b000642e1b2455a41d84a08540c0140c68074800c0d04407007079004055103420540340700805036107805046c8079451a44c1d440600d1040c0090070b0912900701d000101144281e50004100800c4403c3c04410701e0050301c0d0410041a090280200e9030219004054660900203000c03025281d1403401031854904144179420902d0f0250144400c564a6805610050711121110808800c058944544845000d44050b040300d40c103400114454409000400243c2d4002451b0744d0303040010358030054105001d040124002400200e8604d81504029a00e013280c0705440d0f1051255550b103d0700e2104070303851001c55072554800080319943c07040442040c0104c000c0210300750856a850b10445c2c1c6000d407007440003402d80e0840e506c00e8401d9000700200b0415802c05c1c0000c5420300c42244d008000d050103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 872191052 1250 872189802 872189807
    0x4060f0516020d0c09060b04090509150604050603070b07080a08061509010e3007050111030d050606040f270c021011041d091504051207020109030804080105150f01 72
    0x60740019108100303201c0c48005209051900401512091000b4000c8544544501d01c240c1d01034499001054a00400510f4144011400c43e1040304000c040185076218001008041c2c2005483c0b5a890f0095a0380056650301c0c0c82c0082000b03500c1140b400d0340391244180003905d0703110300920f1075000d56200702891401d2410182203a0b803e94007400e18110502c219400b041d000c881009800e002c001e40481101c4400c0512441e4040e070820441c101d1b00d8070340d1100300445409011308005032041c0d00500100d400355605410061384080003502c1c190038583e03030b8582c446c10f41607540d100c600c01101d40c40b040b89001041c18902d200d000ca10303101c14000014582d600039562114410400c80e0030350b41d11000b0080303426890441c0c005141c04061a400b654000440c00103444081c0e070100541d108404000000f8035604a065100b59000005090703006811142036209070b02c1b00404074104011918040002810180600064001d11000203181c0c03820054000154045224691040c1c040f03181e041c1c40c50780d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 872192302 1250 872191052 872191087
    0xf130518160b0d110d0902120d140c2407030b0f090403030f0902060f040608010905040f140c0402041d060d0b0a0911061815130515190504060f05 64
    0x704808122a03881c1032410440004008004940d52910704c00100c00010242c90340200240c80c2c0211f80707500202c44402d000c10b079541d55650003103000c690761041000c0c055501c100a000241d2600d02070340d00042c1000c6c0d4052490034028401002c2e2440b220511171840d615100f100a00315007520b15502402500e4009104038800902c010304241d129080070030b509406810014001b0383c05010503484100740c5048101c660443d010313600015017041d00001d8403030014000d00713000e507403c440006a030708403940380c80c804c4241d100564030306440b41d02a05009900e451000b40000c000880b0440346004c81d0001c1100e014002402840c840d5410213000804141c84502c00c41c3c100103a4800029110411300d800e0720000c503a41a16540407001080b040d070f0083d480100c404440034102c904401c6d41c0b00d031101d010800d001d040523400100020100902540c184621030740c2c1d1819040842a09003052003807902c250343d841e14503030800103d000c0303410020250040c908540320045c41c00c0c11820842d40c0c4030507100d0030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 872193552 1250 872192302 872192309
    0x10810050c090603060141040b1e070f0c090c03090c0e0709031a0a0506030f060708040218104101030e070b0301080c0405130b060f13051816 62
    0x25100040880c6951303000320005c60006000c0420010706011b103200c01489043d00040780c5055021f001440c03811081d00c8001c5400707a904c9201e001d03080c0103c40e00100748100508c030011030802c0c001c000800201f8510034500760542d1040c022500e10368140804c0c2000d8400c00813005050608000c81d0708000b5469800d9101524550340c1e05032500d5a54100858a11916500180400000d400c9004e2220300b5800d009104a0301600c0070b20668445a0038107680d8100c0e600c1d02c0556030820b9010800d814031603440d1941043c00180300911494003e80c44110008054544003080071440101b001819401071030104465081100d0400b840342c0c40c2090340668409103442c548150f0000b1340300c040d0760701036889a40800040401ca64040742c41d6140554140d0007809205600d20440c055070030203140600030b191244008265102d0a0141907840a511050144c250396010b501e844910815884000752041c181c0c1c80392401148900b031a0399403451840520420040a40040305c0d6082c1007180010b840046 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 872194802 1250 872193552 872193559
    0x4020d11061c0204080d020312040314090a090905161a0f1201030c061103190e030724180b0a050307110607050d23060402070311060a05010810050c09 66
    0x5824000002590381c4200c07029080b00000d800004403080045601400c19240c6840842d00309404100c03007a41e0ba0700800045a005040c20700000d000070b803007903004001c5507000c01802824091035000045082070f00b07420219503240c0c1d960901060010420a59210120039004040c8083c248000311208000400320500c07103180018800c03c0c6000c05d0000c403200b04842040075000343d40c50b86040c21031582144641c00024000000c81c401c1e40c0808021a180030240c1e04861144050b2140107a6013035028020041d0700d4014560009105040c0100022855603202030b6007482e1089a030f8003a0101918405c08103060130313041300a00c90040f8103070887d1000f0490341012a00d0f982e6030042124070000409000e000c41c080c4100f40302d49683c00401a010342101d81c4c1040c0103241e04443e0f40b648000c3c0e1030440e4200280e101c40815440d0400d0b0740180310f4030740a481c0a04c0204010010703940b03096800c1d14400180790b580d90040140710000d00c130f0721442480001d801c0c0f0050a1007001410075000f40704400780f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 872196052 1250 872194802 872194823
    0x905011d0a0314030a020d1d040b010203070209070302130f0810051b342411120a0b09010612231302030d1b0f17041202040b0904020d 59
    0xc07692000440d400540e4043d543c03024030341401c00e10f540c50740c11a008140151061440c90781315035026007024200e002450744c2c000c50701d125040801c0041c00407580c01d0350550204021100c0540c8030202410320805003a100036035210b640c28545018003007150b0110b40d407044060400d01806c1004240b90710440c50300200451203807035411008030f028030000c00305051030744001000c5031108241640707102030509000c480d8407680a98681920080b101000c014031041c202200c100c03888a0800d1803c1b80c40d40c2d0325500240030303050040c40f803503d03502c51425068454505020881a0b800350b0145001c0f14100f5107040519500d40800038000f81c001520064200791100240d48051002d1030700350541d030207001a600070500f06a8580d4200c2050810164042e01801180940060150070031400040014109440310b9260380c13a41e080c01e64200e0002c03070303035059019942030700500590003901c003400c11200c20070144d510510400c4201d4844401030b501030404502000050f0b030310711158070300c440d402181e81c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 872197302 1250 872196052 872196107
    0xc0c03040803070b0105010207060e0d0b1f06080402031e07140112021801110615210114010e0a1b0c0f05101e02030105030c061b032701090501 63
    0x508500441d0440321a038400412032106010018034201c0c100e41c1d003a000d50300910744540d4101d8204d8544130895801000c3c6001c05400244004038a03580581080340c0c0c5100e0400303560b480c00d5003e04950207040052801000e000541c6000d201d840380003402c0307500e8080110811040c183e2a02803610411014807403142c03c2c61610b034014420a0301e002c41000c411565400c540800a001640c0d08143c5400180343c03201a100c0c5250004003d4000e41d480c2e18450309103a4808104428140c0505540300351040060102c5c2984109002e034030b900c0404080b8100140d030501c04200c2e82c000d0000d01d0200b100b0b080c0700f41200f94030112448e02d6100b00712407804031307011141400c0564000c802d0700401007a40c030a1014440c45040c80f0703805001c00500e0451100c40004804450b40c3c280d01003805015810781110b1803881040c80d0003402403880b2800e004c20300340d20b16591b290f180c3c15500203203030303d80c0c41d0300074801d00c602c07070312803040ea030066490702420a00341c46030400000070124851030b001d10300c43d0032411a120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 872198552 1250 872197302 872197327
    0x22a03031320060a03022701050405060d0f090620040f0302010e0607140d0e031b191d1503010e101e0905010b19060e150408030a020c1c05060c 63
    0x42524102c0604016602e5910030f000070029400034210b00d459042d00b9400212402c0030100caa81c118030165035050802d0704290030021164070030f0103038100312603856640c44004541401a41502e6005400004201c00c07c9910010303114400c000324448034a08010920500c4003240c0f482042c0c0c0d40a180042098a44101150842c8950503000c2d14200d20049194030700c040008400c0200403281e03071120b00c10310b80d038018141d444480c0c45824100043d55030940ba0789042038054204004000c3c0c00341d9481581e640e420081075400540103000c006c2038041044000803800d02c1007260000203400030050b18420071003080c1c940303420314500d01c80d040c0c50341803010200000758038100602c007031600200602d5000d0320305140240a90a5503a000707401c07403602505240c600003c1d09003240e500d504d65003100700601c410005d080e543c0c2c000c41c0280c210b062202090135002000502080c030650b400a0580701144c9040103040080d0900c5441000220343d0780b00005140800c3c1c0c1c0d600111181001921041d018282 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 872199802 1250 872198552 872198603
    0x103200316050903190c05060f182d0406050909030306101101060602070f08010203010503060112031719050105091302040504020a0510090303180b12040c09022a030313 74
    0x4242d051140c0b85d030740d81000000461030101070384500b5030001c3c825621014810280103800c1c1c0d802e0015824829150005600c1d048a00d03440c8005007148030a9200c0c18202d54001c0940c02118901d1200380340c480c0742401e0a00c101000303054101ca4008013031420000255807488002c2c801400703117604545405609004001001c425a51200240b04450316840004d40d00c2504d40b1174805222004d04000030341c0d40c010b200300d0303041c0e900140260146a00341005030031002060b40d0304508100c0754420010b0000c22070f42d40c641c050b10584080100ea04c9051002006941060308054400e00c030781c00a101d02240b0003840c02035540c3c2e0507500803c45da51540001080440e89601554000c0f018881082c20382e60701103402c1c0c0c1a24031940341c0344944500e110411b4003003415805140c3c8041c8007085417542194001a1480d4443d100d0300746402c0c0203442e403484005036045843c42204684140301c40c0d4020000a00d080c40321004040011400c61a020340c050b00c243c6041c010141c000000c1700030705008500e02520 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 872201052 1250 872199802 872199817
    0x3190318090f090b06040b0a150203040f0924050906010c060b03030412030f02010903080f1f0801061505090a15020304080319140909070e0301091a06010320031605 72
    0x8100114001c03100c591016140b0f0580c2140c0d1200c100f400030740c031450284654003a565000d000000c1c181d05160680d011508141d02c07280a42c84140030000b1a00c8040c005c400242140700004160b007a44400c000d100300c00720b291312600b1185a400300b8400740c0c4a22031007581c402000d20709861000001d042c5000103004080c5002d405000004010902041c65080c05d01c1851280d659003a40b8500300d2400c074206c4042c0c440060000b04000046141c074856503070015080702c0401d051607e14481c8825900000c80c0d15403194906035100c0c0b802304520b092a1100d400a0b054a00745a480e1000300c200140030403100c1c0c050301f461000c000300d03520100352081098501416544084903550305080c1403001400f04100e90203400500303075000d40c0301d070b0000c0b0300181c03000008003500008042d205d0500c00d5640c600c400d90420303050740d691385440307001c00c02070816034011080300d10341c2203c036041680004050b5281d1211041e8168082d144d4803640b94400d45c100c0381c0c0000d06034045c0c801c4c0c8409100480311440b8141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 872202302 1250 872201052 872201069
    0x5190506040f090b0f060306090d05030a0f090f060e0309010e040c030b060d02130f08100b121501081603031413030804230102010b181305010e03031503190318 70
    0x1c2c0042089a5501058001c0d180c54007554170750340d285400c1654802c4111281e81c0107401000c1d5100c44503000340c019540085071408046a038927901e4404200b10340c0400700640761045140c1004081c81418482e241c40d40d841e060255241c0b1000000181c5042d202211a9005a9a44102c0380b0501d210b503200c0c0210010044c13426554050701038054010790458410394090000c00000018440002140441142c500350040c0c40c0c00c40340c0044500c000c200e00c00d400c94005140302c00398034410f0000d104100402c010300a4180c0c640d410301000d04c0c40c001050310f070b5014064040402344042608040c102000c1c0ca07500c03200c19a160301860448410381101d40c0024545000414045650807a42403040c2d8010420303000710100200a0004900340c5001c000d00030f40184141e00b010300d046880c0c0307a18075840440032042d000195000c0c0c0d1550700f143c03d0800307046401d410220030b2000240c40c02c412a5154181203008000c05205141e03082d007001181200101800000858030000500941642c001031042c42c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 872203552 1250 872202302 872202311
    0x71e0c1406130c0801090209070c020f1005211015030e061e06190b0d091202030c1e100c0c0f050d02071208070b07171509070305190506040f 62
    0x51019011204400c1140c0c962800c420120744e041e814030504640a400416001a540301c115094802c6180c0200a0307030000c100714081d8a161f2180021000d01003202ea5035036654842c80d030009070300c00f80d00c2e521500a102c000802d000050f171050440805031750544200080b060034078001640200070000f07242003d070103140108a0840c40c1d0582c0501b00420f1605164a00c0e0f0300c403010061822070407035404800c4c080204040c44800c0100c0090100042c4404002801203480d032200c001650181901d000164400204c1e501e44550502c64051000b07820401500601e90400314030b611001e117200e800503420343c0ca46c80c9014803403090040d11030f100d4000c4400c40c030a001508015884062140010000d8030410000045500303682408038409504005000c2c14040301c0d543d550f45000c0701410722003c100110719200000480c41070140d005040202481c0c040c01214000d000549500520100c2814503000802c0b800c1403e03005254a050f20040d40010280d0b160300005000740104903c0b0040d0134580f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 872204802 1250 872203552 872203561
    0xc0d050709061d03070b0c01060902130302031c080406020a140705010509010501060203090f121219090b0c030909040804090c020609070504060f06030f060e1e071e0c1406 75
    0xc9110240c448580c1c030810014844000f2881090102504981551100404101c00340b8140007616110fa0454000b16029540d102c0308000d9070416603881480e804004030400442c681001815a004080b45680e04418003441c4050080b502c000e1001d041c40d5000078a8040c500d201d00b0042c03041c001b5140702940c403000c20303003000c60090504580d9043c0d650305e80400860002c3c000801e992034907074001c040d0000c0303694203018400c103032011480c81d10a920500400700526038041025000040400c2d03500c10041e5040320b4020102d444175406040c0685040214182140001c021940c00820513507500890740c0f03031440c02d00310500c2030340d120b6511940f90101e0384034500c1d400720f0310500a80050f41183d1083c0d84841c2040f04540183c0308074106248014420000307c2e0090304507045416006070001600c3e80d40e000c0c07103801c58204a501d485198802300d01ca51149126581003500700e80780703152900c005855003075402c010440c40d08110060040c8030800d03604004405408800310803080003134613a117041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 872206052 1250 872204802 872204807
    0x90305031305100f090507050a0b0702010c0809041d070b03190504051005090309010e0a0e070f2a12030519020702030f0a0c0510030c080f06040207060507050a03060f0509040b0c0d0507 81
    0x1403454084030507005041000523145001503207041661210310a861030309280e60300566860b040c5001c12260810b051114041c150ba0780d21074a0400c1040d041c0081c1c0080d25201d02500b00f1104d038002c203500c941c1c00e10600007036044000c080c4000c80b40c1c12000140d81e8540d03084c00c902d0300c0c11000b8560880f0741020104142000040094020b0100a072140003000440d0410490000400c1c0201c41d02802100005031a07644901b20b0b45000d803549007803503021074a52102185194034800040802c01c030391142c0300000c001c55480c0c09101035040d071034204040d09203018844448403d011204143c7c1d0b801061fa1825540d0a000540740c1c102c0c11411229060018580308030000243c1c070519100c0c800c4015035a010a009009801c1107004030341d1452160341c0c90301104020704c00064001904107a00340300e00300c0081c4051103254091102c6032a101d48420030842c008080d0b48181d0040c2e88848035000c010272450f11402c40c1a50025400700c202d00c540d0342e481d40c201d0030078007504010a442d80d04241c01e0107115074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 872207302 1250 872206052 872206061
    0x20307050d24140f04052e080303010308030712151811030f0f13120c0305070807051e0106030807080304020105090904060b0f010e012001150e1504090305031305100f 73
    0x3c005803104600450303d40700308400c850b030447e9440403018210400c50b03102180c0030fa0301c1d000d583c1d04581840701300d030b1101c9019285800c26003003114243e00c00028004002c1c0c0000f84070900d20115202030100c035168660308411200540700e160a10101c1e080400d03a804690b80091580140c000c0400ea103a1908030b000c010040c07001d880384603e01d40460041040d10914000f103841840d0010030750340c88202594003c1b1128649000306404000003480400b00041a405c010140240914000c11005400303d03214082e240420070300d01c03080d038500401080042c07c05026691400e4105400075140da07181e000584241c031901000079400702c046400c1004000d4541c0c08002183e0081c2c82e1346281c0052038005444a01821b010b860116506100078142010100320b10980341003030000104411880710709402c0c04551a400c40b040034120501005030314080112803601101c0202c5041c02001c8654901400300d00c0701a00c0004e00c00c5103501c51405001c0100240d80d41d80810781c0d070400c00c156003030440e0030003407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 872208552 1250 872207302 872207339
    0x50a061a1e012a051005090109082209020a020102030f090d120f020903011503060c051c02090f1e01020f0601030309121a010308030f100509061c0b130312020307050d24 74
    0x10340c83d00001c1441f188051103819031081e80100058a0b201c22a071400c06110355142c0743c0d02a840b583c05011801070340c1400680100d0820b03800250316801c240c0345c8680708810082007012550f110305803030184503034000c0c620802d001d0400c000140c0b42c00c00440c110042d125a41d2901d07015070070722000140d0b880301c0c14081c0003103e0140108004031304880c4c0e8222146d100d4800e00705050a090441018142081d500038108580e0062500140074907403004100300100301d80c070003500c1000700b510345001c0c0e5806004020b41c9002c00e00151103990b0640d40c1c0600780d842540500205896170107182002c100e41c29400011210125664000c19a500e2a1034032640e4401c544440420780c1281c0440c1408030325000c3d80d020f560004201101070341d40d807000c0c00030450000c10600c040311510f078880e0010030201c800b501e00a9249403803201e200d030b50504003d032010342ca6191090120b4070400401c00440d40c008199011028503034000b04420708001c3c4c00030041c0724a101300c019020304046000440c002c0a4002d141c50307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 872209802 1250 872208552 872208583
    0x40e030307110d02030a020c061c05040c0801060e090d0809030409020403150c020a02010801050609040f020f030612150f0a110a0309060f06031703090a050a061a1e012a05 75
    0x9041c16801c1281c0303d0003624002001f681c00414040b0592030900301034004c814201340b55181e2a58501d10400c250380050300d090752000e0b4584000c1c400402c080c0a0f44000d4101f14400d100c850a142082c3d940c1c5008141548081240d2280402c10a0006000301c038001c200d034180c2035485d0350b102d0a0800d001c0c0c0520231414510341c503101034440e000380086034111b40035805864554007607180c84140115035201c550a69071150351000c00320200d218034406084803c400c54000c585a00e445070601882c80e03054204651184e00c9128030342181d100f000c1129500000e1000d0f0506c3c1a211170405d80040d00911f8001110a10042500c0c06041e0f8182d210201450280f0003d00110641c0120b500894449000141214414034000044004103038019600209000e04076032000e103540c1c603180c1c203115070488112050390302c030b010312031902c00c3c20b0600c0c10a00703404403981c201c1c840669074481e080a00c96044103041c01800669001d0f031423114640e0f02c0c1d0481200300455503042561078216280c0c0101d24602d0301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 872211052 1250 872209802 872209813
    0x702120c01090e010302100807030b0a180c0e0306040809040902090a0b181b0f0c150f06040c0509010806040603020405070c1b0f030f060204080709020c01050612030d0209040e03030711 81
    0x43c00010300001034105ca130044c018107da02050300c011200c85034002d151100b8103440e07503804c3e1b00a071104001c0300014031881042c5070440d1150118841620f40000c501c2080000c80048480b01c0e940111741181c00c00d5008900668485280010802400c002c0350041c0d07000e1030704801c010054091750015041400c00302d0300d5071050304140b88084140c500a0f1040c99104c0c1d00e6524000aa5030307150002d0552204240e140707810403842c907010030300d01b00d0401c4000300080141800c1c40b82d02d10414000b1600300908803001e10500b000301400425034020402100d041146030004140652217a900c801c01543e0082c00522440c43c0c110700c00b40107201880801c03215003a1111001070038400c0310a8840c10f4074844403059901500c0d42d220301d540910b11202c15100c45608201c0010200380c200803020041000c4034015844465030021079085840003400240078103042204003011003008022942000510100140c5031814140810005d156400c01016680f0000050060b26508000e003241610342070000c840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 872212302 1250 872211052 872211059
    0x31b050414040c170c120d02061e0c1b010f0b1201090c060e1503010e010311060a0f080c07050609160f06020703150b030d030c030f021309020307050702120c0109 71
    0x2480c464080710082e082c11070b110000d001d071100c4245000400c0000c0300840d000c0a410f040000c0200000303038206c186660041040300590b41d010f20021350b01640288030307683c079441400340e10408010014501403140030700148440d158a051071504950b414014000c001c1c0e02c20000c20b4a00400c1006900c520442e0720310048900120305004051925500100b44081c1d645400c00503943c014184041e036030702c0f0400d20682072b030100c02100a036009000d521001c1481d54514100300e06c100b4100c640c0b4034040e10003040700d0303811142c00024000300710007685400d4165682e80006a0341034011030380000c22600a00d028085a48400184c1000850140001c842095500c030603c0c3c92000da544204070240c0c1207074800b000800c0c1c0c5040360140c03601c13005a001c990070f180c4500080c1000340700b00308080802e80d1035401c1419075030325118480700f0fa042c2e10380c11454050041600c52844106108201c1c0e02500003000801c05803044040e140c8240d8003801060340d002c0c0c69444542c0391052505814000303190081c001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 872213552 1250 872212302 872212331
    0x1140406031b18021c022104050a0b0c03090606090c0405130501090b030a02031009062c0f190809031006180e0316200a060c0309050306070522031b0504 67
    0x5442c0101d55100780120705d5000c1070a00c020350483e006c50078a2940c2c00c0b49000301000c003c011603100f20320a1001e40303e110900d242610354064094818290190180100203550100240140c0c010004807003994103680c0b900c03140c5506218a402442c0c0019810f0b0b0f02030412a2950061410b8401e02141480f82007041800c2c584d840040110195141e803020040304040c0300e40781d01c06d00d84207014800100303404d50070351000358409000780d004410080503600c44400307640e400e0040c00c0440e5000c0300074016007000344d401108441002080907100a81c001002e003031666040290140510000c2d03414080c09a840340c0b841c1030f05825003885000c460900b501200000004400c840584460784100c18150030142c4400f01404c16501d2482c40c15210034404884607556010054018880e5a0310329200120344e02e001845814290b0cc010300982c05a000c0c40301c00d94100050b16060401c0c0781d100310146034500030385100c0c441143c1c00506096181507004008411941e03050017510000d0f80d082c030074041d203802c49 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 872214802 1250 872213552 872213557
    0xa21080a09031707090b032805280905070b040810060803120a0b040e0c01030f050c040303050c10020c030703260f0c0c030c0a0c0b030f01140406031b1802 68
    0x14002698041081a030f0b1030203080b80d5030802c4141c90583c3e10301c0d8a9000741c5000e0b5000741c695920380e000d108406981c0910103081da04951000990500041c14000d00d1800c2034000e40c20143e809052621410b012040a94059001150040100d0315107070390755200e0a040d039000e401040b50f42d0084419184e4031000c1c07030007401e08903100740e8000c500d400034154425010f400090000f05c84251200d50721074142e41d42d8029040041500c50150000d0302c080d200250850390700c44e0001c40e640d41000200003254506005884c101c07501805c2003550340480709545814160140285141c02d4408038003602c0d1000e00002500001e0302ca03445042086107866a445d9400414280009240e5183c0002511560030907001e1504040b0001e00c10341444a8039030740c5030440e0403400c91409958000030703007030b001c5c0310301142c085008284080b883c2c0e00c0c5043c10341c4c1100b52800140900c0001c0000b0036441610760b240e0350300400c0103582000c0c0d500746080c4062800c1c6039001e103a00c45c84850301c0200d03d240c40c8a1105208 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 872216052 1250 872214802 872214821
    0xc0507061b06050403021b18040f081317061e0a2703030b0a0501031116020d080a0206100515040303140909041a0901090c170a21080a 59
    0x1060160324103101150108050803003041d481c003030001c85a00040036802014000c0b072007034015241130790000025880010216140d2845294186200d2032100b681d640c80300d4000d034229a90115819250411210f00e2081c288840c49200000000088113051444918036100c0c10f00142d608507124800c94a0031002001c0d0b070000402100d04c007013a964140c5274400301400e40701184100120440c481034070039102200400750040303a110782d034504541c901040e2a102800c001d0a04101e0054800941ea1042c0180035034603d600c88044407840070341d0b1343e14071400d84466020107500e64130b2608946c0207444860542c1c0c000040c880c0e041c0301040b149044001d17041641f801c0b007102801c05145440c00c0301c0f03035000d602c500b44040317108111050142c2c5449070141e104501802e0038503842000c141420421040040610303120f645861002070005200010b48000c0382e02c0a140705032000c03c00d1071a6400c0150718000101690131110070042034801d0f0081201075800d00752500344055482c045403174280c510444 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 872217302 1250 872216052 872216063
    0xd0f03020a03030f2904060306020a0201020c010b03030c060103140708100c030e0d0203031b0909070f0909060506090d06020d0c020607020c1804030807051605030d0501140a0b0309030702060403110906010c 90
    0x850083c5048210380315004a250010300207c0c9041da00c0d203e2804986c420482c0500503500040c0350030100009025000001c4800d500031854540c0052142d600c0e0b041c1800000c2280e581080c8c940540d200c20441d4901415107841526905420b04074030320010407000081f140401d0400320304070766690340840c684001d40e2083d0042c5180d5030300c03803042441e0341c002140c00f10000c001c14459000161100300d00d6074803c102a8550000c1c003441140082e11005296002c414400e05020080c00551205401c2c0c8110308410ba035040e1002d80103180810103406038522100b06685050445994184d0004640d40900a280c0076034000e201c00c501130040000e50960381c0c001811610303001c600084c1c03041c85030b035610840c58a8050700302400102d000400821121060b0380c3e80d031011841510311062441020700400e401d40d4480c0c104081980031641e00300c001d00c03070300201c410003100040f2404003c1c002c60300b80c40d5000b0030044c0d0700c944034545822900a031400c054041e680030400107503554060b00300b2a070302507040ba = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 872218552 1250 872217302 872217341
    0x1201031211010915061e15030f090308180d020303130f0210050409110307210f020d0906060b03071b020d020907031407030c0903110d0f03020a03030f 66
    0x544030000c8540c518004034040000705940525141002e21514081e20310485142d400082400f2203036060b6170705900500703c0884003014900c034429200b0021822607056101945081100404c1640289810540c8800c09401c12000c4c3d010198004e5035548250180030808030444580740186582d030340c003014030b507003d81e20410108480b8250071040040062046905156081c0c1e5540801e120440400410003c560007203028420f003107481c0216540360300103402c2a800c5140c400e100030100c8481607040c00b4407200700103210403907443e10b8008442c0141d40703104c10b55407205d10944a40040038526026281d4070325045001c10752040590880b0b00407521343e80c0e8007450800300070943c0010300300c401c000c0341e0010420b04400300507141c0010861040550f0744000541ca0740400300c00c442c00030010709240815140c1400c14160541103c42a000d0f02d40200800c000c588000c00407580e00c1c055964054191003000f030b0a40b04150380001c0c0c03008124460740e01803018000c110904016141d00382c0466015a042c2e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 872219802 1250 872218552 872218559
    0xa0c060e010207090b060f09130212150418060e150c0409140c03040b190f02090f0102070305030a0f020f1005070f0305060607030e01050d05091c090b19051905031008031201 76
    0xb020040d00423403c00030030b0b0840000c1042c0842d42203034003d4035030301c0380740da00f600c20001a00504800ca0f220410301707403018000c040010540403003507140f83c400100002e40d80c072451a19118100076640c014042e9003401d42250400729440c086078ac00c9481240c1d600b5041c80d820300301900d03441e030b642ca000352281c401c2c5900b50b8550750781e21101ca0000524108188131901040c07100d04c006030080c82c50030f00c070b0407600582d1421182d09015000801d40c400c07e0540d40545401c10024200000310790083c4064034100b0700c9040c0401040f4244034100400da6130038407030702041803020346171a8415405444a51a00c100c1648001400c1e0190b40048408030303441001445100040380c028142854401d80514080b071078060b074030bd20941155001d0f94020a41d0b0710840d481840a00d81412020081c009414030702403d52818241c44500c2c800c1400c3c032109803103880da5620400780900300b03a5402c04803092000d482107030700480040c419081151200740c1112a4000081c1907800442100c503680c1d0443d1010007180e08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 872221052 1250 872219802 872219827
    0xd0f06080601090f271e030503040b092d0712051e0d050f2a0a031b0206220e0103121b02010e1009051c0b0705040501021b030a0c060e010207090b06 65
    0x1100c0405071030184442c0351b403209480d5000003140a1510949521f52242064203120880d0b080080c00d0b0760044e845100c40000003801580590169186da0701c0d100000f003403c41c0c00c1c1e81080d1043e4001e140483c85400034108014000c00c003081d060082c00612290750b0a02140c16036144c0c0c050703402d1004123800b00080c5400c03a08240c01400507256035025640010a21070200301c100ca1140c000c00d546411580c0102d0406510510040b00d100c0711481c1d040004c40560002600c600c920b072010710044501c40c0f0f41401001040c03414030000c149004807140300b0742e502e0030901380c1d04102c40610400521512803c01c3c00800041500c1212a0103075518104c00702600b00b0b100c00880743c201d00b0014010051400201740d620140300040300000d032000704280b25041e19001880d080090411818840c4c184414429641d0004031003e5102000006007020451800860f0a249807032002401c00b00000c0004200a9001030314640349030400c0c0d0844680540d2105038100b16140a104542d1119081091210780d80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 872222302 1250 872221052 872221121
    0x1e0813080a09050a03030e013902030c040e100b0d0807080a18080106030224190c050d2a05060a1d0109051e0304050a0302060d0f06080601090f 63
    0x20110b0411100a94684000030002c1c4615841100000e00c84407502100e940c0c0400da410081044010740642c4441e0412444e5900524058010341e00b20141408000d542d001c004074400c07090083c00810040d10400b28450322034070070101c508100d5050040040c0f40d41020b9024030003c44c1c1090045003031103401d07030311100690b000a080c10100f000821212044804a50b5a14020004a0000264980b5510510810b0301c0f40340700c4038480c0424048002164800c00b000c542450300300b00007400341c1d4400804d003030390340c1e203003000b4042d0007071040100f07040249400030f100c060902aa00c000014071080390083d504010144035004107950070240c00700e0036026041d0003c1207116030076002561205031441a05003141c020b42001d07101c0351301590f20420300071041d1100b00608a4100041d6181c1303402d01d00407034000401d51100a00501c0000384086500b8419400860100034004041c800e096079510310565481c003c0c0581c10002d864605900894480f521510042e800500e4000641100c0c19801d1440035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 872223552 1250 872222302 872222317
    0x6030a030c05010b101d041118060f1219381201050a1104030503040506090607081b010e010b0d0b100e010f0f050a030506060904060f020a1e081308 65
    0x190341340c01d03000b0b50b9a5900061100303400d4540c1d0b00d0005000c04a172503900040460701a05004a1030900102880c0310300c9000c8440045c040b4580001d032040c2c0c05c000c60840d129000c40704869a00210720540808142c40c1e10ba406140c0c11904114003c205580301011075446681e54400100605994008840500021000c1c110814074134a866540d040108403a440300c0129051140d54407000c00c16064520301c5110131916a521b981418142107070346050b41e91080c0d0042c0c1e48181404030307640074640c0e0381c10b08071660715501840298a402c824043e4414580384407503468115420056090640e00c414411011011002800b03440b0716070391601d07034941c0d404001c1c100c581900b686180102e52b410f50048094000e08910040c802c0041c5001c914046c2440c06400283c03044580d004200081000000c1041c0c015900700d45c0c8086030385407450000020301542c0440d914803800800c20300092038008151042d80c15009440c1d03400340b00b03800404c850400b01103a2050651100210307103c00300c6d84520240002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 872224802 1250 872223552 872223563
    0x601120e0f0f06040501060b0903100e0309040c03050a0605040213050f040902040203130c1a0d180b01080106030c0b071a1305061305010c0305070f05090103140a090c06020606030a030c 81
    0x42041e001040c038100b02c0c0091000d4510b511031010b01003000000d10800c401007404500f203e0a2003400ea0000b0b4480c2c5640c001e0007070564942081e034061030000d000f21120900000c000308040380c04a440900505011a40142c142e031403c179000400e81010700031030304054800003c1030030850402c0c003080744a504d0174000c031360400e03030340c913804401a121880250b0007800340c604114020313103591a0141250300d1a800202002803000340c00300c946d500c48406c0e0361804038810030101c0c12500603a1500500e00403003a000e0510050740d00001000f000c1035004805490040c2078034601e15480d6582e142c660310503503400402d0341400c258454039901320103244540242c140840d0030002c4a0a484542c44e01400340d41e05150308205000781c0c402c00c402441441c86180329803c040c0441d1034401400307407c01141591020a0140001d542c440c0baa01c00d41c13041d011100004601e2580b414007a4450008009012080300d28959460f40450014000141c2c3c2d407140300c00070028040c00c01c40359003c07a0010780242d0221030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 872226052 1250 872224802 872224813
    0x150411120322031e1a04030509040510090f0209090402010e0a080a060b1e150904020c030316030605090f1b04032001120b090f0405160308120a050601120e 68
    0x40300b0b80d44540ba01205812004107800d60400011202c0040c9019454080f00c81e042c40000301110000d0a00c64011001c42840390780b142420f41e50391041117002a401880d110410003128a00134080c0306650614104000026407585031204a2082010495020701c1c0180000c0042d03106014075594884042c002c40d514560760402c051070b11011081c00c83c0c145407910034030001307170404c2c1c0c401c0c0800c1404503d007084412400d030082142c507143d41120a05a040c0050b40c134505895680460342c40024020480395640740c001583c2071080c220b90038400c00039051503400540c0f1b02d05107007003e015110010450303c01d0f803100240084445807500000d0840c1d0000e00000001c01c113414924850710b44845001c2d01143e0b1042c00040038801d0400440036000d00d84203045040307440e0405034a92204108140c482962628140a4a04a800413109101c1a01100040b08010b004406040c0c1c21004800c040150788030103800f001540c0c3c00b240c01c58001240a00100d035510510f03017051501a96044c00d541 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 872227302 1250 872226052 872226067
    0x80d021f0b0402160302011a060715090302031b06010302030c0306190504060605060406050703030509060712020f0912070312171f0504021b0606040e0d0f091e081504111203 76
    0x920b41d482801085e00541d558900619464541c02d010400c80e130400c903106842c100d0556102c650041c11440b072000c9040d0703034034410b0b8101402002150040040101d29180c02d81003a24003139520202404228068001e07074815008905000851600801840d00402c81c019000d180480040200420503111503890325000211a00d50350024005030a1640d104c079600c14032801c01900741d403405091542e142d440401005642c82e0b014200a903104e10251016954070380200e2540c2c200c0c0551200c9591100795448900715904000501c00c2c1100e2080b0b10041c170314815107509460119407601100354441a40c0c001507044443c10840e04964160a10222017854450f00482c08980080441004459010900b1113000200300040b9a2001048505000b83c42d0040040fa0302c3c2c000d030500b0319090052001d21003003100d0007164610b02401c1102940660399000c405404401d86991046e14594020703624601d0342041c100790401d10444e00207020a070804240300a022012840184040b04d600083c030881 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 872228552 1250 872227302 872227327
    0x30714030d0213090b0f03030405060d0209040606051210150e06120a0b1e0a171903030c0f0201231503071403060603150c0f0d090309080d021f0b0402 66
    0x4024060320044610303c0281030101303520440b28580c4005205207200a003c803c40c0d0b03000805c039016907800343c0d0b286440e2001ca52448019004045c0c21340e80c047d041070000f207030195112002c1c1038811000c18510342c1a40300c0050540303501056000e540f520000d000e83c4184a18002c5d0910440540c0180400b842c2003801c282d01c0118640c2075403209074030b984902c503c5030980384c240c8900f0003122603141c03a0750442a0480002d03418140c1485045404a040c03820300c0c2d9404410711088002840308415106001c080703180c018000c2c1400c040f008040f0341c0e0b04c001c0301042d40c4148200055506411201d80819001190500d0341040c001c01c007101c8088114481c0344036480a21488000b802c42d603148a68040400d0101418404000d060500aa002a03803204280e0402054290001d00d54070320705a80c0c2c1d4508020740c4852042441e50f00009003046083d07000c16030300c82210700403121043c003581c1c44a280c1c85800c82e01c803680d20300100b034011462210281c1300391903a80528414040180014507100d400c1200307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 872229802 1250 872228552 872228557
    0xa080a0b0c1b0706021c05030f270106050a14030d20010c020f01110a08180c0402070311072319030b040b010306150f09180204181112030714030d02 65
    0x100c820301d402040c804c1141d80c0d0108108a2000b80410740501341500c1518001c003d13000080910301c04a00c031300003080400030301e04190070120a01070307200d90038081c81d11401ca02800072881158080c409a0740001115100a4040402604010b0140c00051422541151141c0030030703105074900080411600d403044000d00c503080c4d0400c4c2c0c1d60003a00800c010f110078542180c500c4c0c02c0004509000b0000d61402c01e82c49810703c0d0340044180e04e0090104d00c0364240c107203480303481c00005e07070414400104c040601d9000500f84030416480780480b008562030f1210000120346c888421090b450081c59610342505c1d001c440900300388450383c5e201c08040d950342c0702c0154480c8103032415244c11560000501c280180d0b4001d01002c01d41e2260310900749894a10a20440c44030b6105503000d00c1d42d5281e4909106050b06075003e10150024003d110000504092081d8020145030488502e0005000303201c850804001d90704448014402440c21300c040c2e81c5400b0801030032028440454003040081c6251500c0d90300c013 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 872231052 1250 872229802 872229847
    0x607150222150206091605150f030709140f090703020d023f040c032010050c070501020a0807110a171b19060518060409090308060a080a0b0c 62
    0xc2692a00c0e500003400f03420140081d10300c9840750820300b0340c00d03e00918000e003001100c10235103480d401c4518884492456010300c2d1415007180c0000024400455071010041c0107490352480145110504034080104603a05080c03415088510480010141c0303019501604000490303000c05854002e428450107058040c0815221401c558002c3c1c0480035a2481848000000070303035030500c0d442c00c042c2c0700c0801040c45884000c100c07114034030112080103078414034207020302c2c80035100c40c53352461404040c105030058002c01445100302000007a1641c400907a030700c0c0b055009404035203494059140c811007000201c1d0010741008a68400198400480d4040715141c2c0307001c03014ac914010800c490856810628480d140301d14107003001d8416042d5041000b10444000381081a034452000007400740c607000c0c00b2003041c1d0002000c100020002800c0d0000030030b00344079030340d80000c1d60384031010041070749000e000d001c1480c0d120340c04101c0000c82081e90140c00090119500341404407060654144403569035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 872232302 1250 872231052 872231069
    0x51207030308010b030106080f1801090b04021509010801090e07080d03020d06050406061205090708300712080423010207031d010f0c1a070216050607150222 69
    0x800c005041e405801107000d4840030035410701d5945048401002080060b02034448110100040f42884112214401c007081804d4001c0c08191054244440d4507101100e09a01076080e02a0640c5c4d0781102c502102d80491050b12048007507420b25a4040081603000040f1842d03200b00c580200d060b540030800c04103502c55903540540d503402c0c01d400c00410386040d03900c5240a00c0c03c250041c000302c0e8000704250b2011800740000145a6104c2e045580780c580c035a808006a8000d40213070b4510b003d02a8049014005054504107030503401c115803414511408801a140e150b8514221135050b00ca40213241d0003c3c060200c42a01e0b0480a4142090349001c00821410340e50000780e03a0105508501a15120281d05001c20b80a000400018004502152030001000a0074050a0801200c489100d120802c81201d4204628000e20080c0da07440354400591000e142c05c0308001038910300340c0106c55049900c455a2080100301c4e48000b0040e400614403031054002c41103c0d00341581d5a82141c10080151740c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 872233552 1250 872232302 872232313
    0x1224050907180204050609060c01110c1506270405010b150d1a011e0903080a09170303092821030b150405101101020d061401020319180512 61
    0x4111400c02c03942c0e00d0002d01c2c8074014442045541e544074169011076805a070216661100b04140e02c3c01003640c1210300840c01d101240c1002601360000e08002c6d80f9041900002280d101c4104108040c208150f100c1e0a420321980910010341484440c250070500c550f001045002c020341c0020080c2009034071040040101282603218401140a004c0c0f480b01d011402c1b62201c07401c42d00003405610f042e170100000c01e08100031030194500c02d40c100d40095421201c00c946807441c2810040100b1200d1003a03032105070440200305902140401180d00510043d40185014240b494284010756040d803040140902940600c0001c40c01104d4140c51280342080c1d031205000c4680d0014086400c440d090b24020310070110210010101c5008076000c0d250b04403420380102038041c074110ba02e0302c002000c0701c0c90780d400812081d10105940e0013890175145400300782020001450012a0b0300c0c0960b210100d9070400c403c1c0b860400074051202002d5a2000c0352000c100340b511000032030035000a4040c80640c51b03100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 872234802 1250 872233552 872233559
    0xc02010c0b0114101704021e0402030c0c0d081312032304230705040506040b06070b0702011a010c0f030203130b0424020601030b0c0403060f0b0f010201061224050907 73
    0x15504d5600d495400c000880649004030380340c540d04001c100a009542a40a241d116a1924020000a10024000d5503a40740c10446603d0301d070000700880b01c55220784044650100d004001c0d09114902031298100a805161160110010124088014940d0f201400d004114001038031040348103101032002080d00300b44ca401c3c1080d250b00d41d044540f42110180601d01048003298042c2160340c101c0b008510380e00c8200011740102030003d000c5da4001000100c400400241c42941031040d22140c000304910b08040c080b103032004010303035800d0340000c1078504107000113100c00c0c0c02401594081c0c81100c1c144022a560380d096603060350450580caa0010508100c0005421141585485900030016154803510130283d500d69040c04001c04603110b0b100096081d11140703081c1d900554202d001404020103800c0075000a00b60b03d0b4ae201c1c00b5a000d12111300055005011305000c03100b1401076030754410419103507520384035441b080800d108200c198030b4250500c8140a62130003042c40d01f000e06070013841c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 872236052 1250 872234802 872234809
    0xe0c090112060f09020f0c010e0a0629060d09020909010902120f0307031b05030a030905190804091d010e060105090906011d0c090d08130807150c02010c0b0114 70
    0x240a98003484042c2030440503c4003240000d41081202d00c03503030001d03813100c00c1c80400b803a01c0d004640700c0c2010781d07207032084d021540100002c90301400e9000300000c01c5507004040f459071412010b04550400c03500d1030404054503041c060020418164100000100d002c0e5039800144040000d5030010340340d2391142d01d44130951425410586400b290100140035000700c0311440c544900a091000d8240400c1c00c070b224201030b840c0660400d40c203a014054076a41d40b06040094014411030206075036134807031140e1120420100a281104468000e0892410075207400c207054060620640317203105280e64520f100003146401d00840c14680c1c0800301030800d03036042a041c00710f0500b005000c1e1041d90310a40040110100c040610b08580c104009803803441c0e07032303142c882030014802d0040c1503400001c0d4007904c0080c85040b00243c03024490803162840c1c1c1d2a601e12001e40e44548600a0b07a4080e982140d1480050303010b1411002440e1041c14100c20041058440a68600003680440c864800d14840141c980c03a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 872237302 1250 872236052 872236067
    0x10e06070615051801030b0c030417070614180c06030703150905040b090616180512010506040f020f0f0d0b0d0602091008130f061b030207060c050c0619060e0c0901 72
    0x261955001307080e62564681072070b8000040d0480340004000000f00b41402a0038182461954011b8600c42e078400e0f262a0400c02080030b60210740c80c100c042c40c0403810103003560b82c81000b480030280050000500c1c1d1410000641c0c0b000e8148404e055842503071180258030b80d000e520080c410410001501e1805041c00c08d89070300020040c1290703801c83c81c2001032050020100007801040c0e880c2c15130034400b01d1414480081d41e69040207920036580150f850b0300309015003020b8800c0c04161404d0100c000d501d101e020990041964450348442c0500110544d5410f01002d0081c1d4803100c90081101d1000c540803e4200280340010740c0c000781c0001d2400f00c14140380c41d42201e0b0041c2c6260800075441c00c0c00d071503c007101c075040c0000c181c10400c4513010180291600075a000c0400110901c94244184c0b4000d0f000f0351218800721445030900720107082086c080c00c2a10b0300f40840348064003442d542c0c41060300d0034010850034000540e596030000f050800400050368881d0400b4031160741e82d20800e800161044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 872238552 1250 872237302 872237329
    0x9030105070203030c0712031415031b210703020406061706010c020607030f12020a02280512030721051e01061b0f0f111807020303010302010e0607061505 68
    0x150f0003041804007050f001c00880d4412500000b9400400c0c220318401c40240ca10030f40f280c1c910b070403002c2c244103503441d9107801c05801000c00c07800c0700d0318003640301c041041e0004081c021540c000511061424003407c800c00e441e2001c407070b0f001035690103601e950004089440a8001e6000a40b00321304030802140313100c0449400c04002d003040301daa40d22660003e003081c490000c000b4104402c20407408516805403440076034888960000350746520800078001d541d9007407600050320b00c0d00e5581c43c500310b076070400228244c0f40e60803501a0030300106043d200202540041c2410040001000ba2911601d600980010030200e80300d4001c102818585030100f1034000c85620740304500c1800004001035034111040422440e845030300e060400c0c08908094420201c20343c00075113a000b0903e0080104503000600304058502200c2d440184401d204001211801c210b5244016030320401c0188003541c002e2680f248070f0035005000e540307000c0c850780e20b0304165900103140303014100b2518018020784c540011324400c603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 872239802 1250 872238552 872238557
    0xf100203041205040f050f012619021c11120106090e06060c0c01080612010912080f01080c0607080c031207031d0c09060a1d0402031902030d030f0617030903010507 72
    0x3814100350b80c00b40d170b030003a80c8034461040802c4150004c00ba40105804107082085421100d4000da501030802d0420320f04540e2415003000301e8100305c8042041f0320a0304c0780744003038500d92104125005903107401040720030101d0b800c281041c00480000541ca80d00a40a40031942c0d90011251074001003604a040c0509454414802408402c142140c000b804484201003403801819646445000c940400c10040c00002103509018151051140d042106c0030744c00c10b40c0d620b400c0340381d5840c212144100e80c203024030300d056008242d80086514282e07016100b0b10b4002c502c030900d040360017022a890340d4008643c00840121140412404039010710031001c0f040da582c060342d2049886800c05c10340f580b1078484041e12075040c140202e10a038984120890141150041c089140c1c0000515180000400c4404a109101f013201040012801d0154002d2169000c0d00400100d1541c5000b070300a0504070009100081da0342c0d1002461400342080485240081c00246598001c0f01c014142034560040c2903406 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 872241052 1250 872239802 872239807
    0xc01060b041d100504090b040b070302070b0c03150402040602150124230a0504140f010e061c06060e0307090606020d050c0307020306010b031909030f050c0f100203041205 75
    0x10402d4540c81c51041e000c00050a601680d5500ca0288200a1a084150041d02e09000c5208120305006028021405848010b4281d940c0c41000c40c203a1141c4a0b00a2a02c0d04c45004500c00c0031007000a940c014000305015054100c078140031074105d0700300303600c420010b03130004546144081000080b50b02410007115005440b40551038400d07014800840e00300104a0280d0084500710f407a42c1d003080e0049031701c2c46102d07520400c21400900c4c540043c000c980400300e0307000725555075140490003200209070684490120104440c100484c0781c2003e2028010f056019004450018584c402e0001610003500c54000762184030092626101380d030f400c0722403803a01d00720381401050740001d04001d12500d0351a02d1581c1d5003040d8a500d06601800c0da000f07425108400c00030848010000186209496000d070cc9825000c075055208142e90800e00042e000ca24000c0c0d044001c24440d40040441d00c0c1d00030203c4031240d070180c20203440c06010301d4010200179404400d0104116050059000000b4249411030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 872242302 1250 872241052 872241059
    0x50f0d09060b01140a0e03030f03070f0f0203040f12020418050f12070203070b07140712020f01051801080a1d01020903160312030f0e0d0207060320090411071203020c01060b04 77
    0x42803080700f54000c01c0c0f0000c0d60381c0001d1a47c0130012a00441e856401d120344038141068064a60180628a040400d00380d0040c52040d51000050700c04840c420b00001a2040c680034020704a00340070b06060ba003064a410f809150003200d08949a107151284000701800300e5400300b0340342441c800398482031004808003e6440980d0340011040d040d210b480003010307038800c07062620070502c0d0750b4101d00e4800c0f8000e50500058118420040b0980170b802a03170300044094110703004586900c52980a54140300392030f000481c1551040b030340300ea840b1004079000201e854140701552180744d4140d01e07403a296900010180580d0809204044c00b0304255850040d4541c11a6035107110b85601d10462400c060341c40b00e9005110300d8540100b00030414481c280d40e1000700000000751241594040e0802003400c001e4584100001c01a0301085404114000c9090080c05410070000c2e0000e0303084940903440034000d4a01240840190114800e40703500e0060b80c400c00402c03000d0139609154000018100b050000f003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 872243552 1250 872242302 872242337
    0x61308040311040e06090d02060a140a0c110f010501031b0303050a0309050c0d030503060111030f0a030915181101140307050a020a0c15110303010303021c050f0d09060b01 75
    0x11800e5030b60040e094169100c50b0310214000703020f001801c01d10341c840d9209000c82c504002c12070102c20300f0f080c3c0c240d030b0030780c0c1e20701c11000103503042c06804080c1d51041c4d800065490318964042c00900d4198030b4092410703680d0070600e518010311a54140c52696444e0b00400800108054403c070804055102c800c040d07241d600c020b0700e03902842d00000c06040d116400c03402081001e021428108800408a000e0711640341001405600121103250100b03c1c90358400301480c10000c10f9821301e802c18121a4a030500041085000d031031170b0b00c070840c0c2201304181c8501e44110540075900001880b807072900c040309407038108503aa1036440c04c0c0c20b506004201f9605081481c80c0c0c2c048a034060014104595580201441285400460000036141003040c081c003140c0e02c07900d0201920040601c0d81c1c0d40d225295013900300394491100388002005640000c2913512421124440040419014200345040604001890301203a201c0750001c210156940010300801500e0311404840072028a44202c1c40014042d44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 872244802 1250 872243552 872243557
    0x603030503130c0f03030903030e030120130e09010504120804150b0f150d06060e03030a200604060903120c0905060c0c030a08030f390904020a020c0102061308 70
    0x5280d81d8030103a055420b0104000b000e038000c210040840101c13030f95900300280a40b04a004c11800540486c411441c1031405028880854500400710100d40005664520703050b40030110f50b0a45151140740080c20319441c0400d10301c0f6135816400450189440e1030311f40c2118a03807266010500103c801404081240600c00c5014111603070b40014015181c070000411101e1808145944050280c0006901d150b204000d0b000c8000502000c2c0071a17511402c0a0380c08811580354940c00d50700500c120307494a48148641c40c2517002c00070416440361003502c040c3d402c00c20211002d54441e0f84601e054000c143d40509511500515002c0401c51402c401074001c005031418410f5501c2041d01058041329901c1c284155000600001d003100c2d100c8a00c1c1c60b000c050342e0403c039007158840c101040020a108082407200245020740c5602d450204020225888a481c0e603031000c44000c44284912001c60f151440100031074490383e0000d0010b45c3c1c040d00020f140c003200901070380741d11944505050004880005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 872246052 1250 872244802 872244811
    0x30c010e0c011110150e040624031a040201180f0812040806150424030b07050c120a09030b040f1b0609140301020f071a060306070804060b0f030303010f05090a0603030503 75
    0x5000c05c103051540e1401140750328a4202c645464032003001e00007080f605038068160701003014050000168024911580e0000520001c0c10ba0560a18060907a0036141040c95200707205042c080980217285c1002c00d10f56242e50000c160725449024180520303641005020718040401d004e09203068240341006480c0c41020300760303e014220480a08040e543c036034205111201500c04404150000044d210b0102d80141c4803d90345084040041655140f0500841d1003e03100d9000034809240320519000407940408e284004006964401100203030069040c10300841c001ea030fa01507810030900700701c1846003d00d590016140c2d4802001c224035600060408122081c0041e14030750710401c440403a0180c86511401c690400c00069107408101d1051103000200d1454095041c0d01d51301c1105055030b0745003d42d00840400c89443c0004d00255164100c1582410042c006003005201080130a2450304203821010115030071400c144901e007400000f26a01011001061007407610b96100a011484041c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 872247302 1250 872246052 872246083
    0x803040e24010c14060a0b04240b0c070f060309050d020703020306061009051f090e06130c170906010501020d0203030f042d0b16030902130c020f030c010e0c0111 71
    0x12084030070712002100460040402038103844172485c4c240a01401404280940f42c45a843c140840e09100104580340300281d0f4004806040b0714103241e01e0075115000689140c600b88917001000c20031000c0c595030600100035540b40418000c180703280107400e01031a00d114204540c0031500c00c10140c0d400013415034219106a400442030007041c5011147c02d40303a60421070f00442080c80c04052021a0114002c00e4400c5035216804541c0b50828000114030581d000c0d82c1c480300da030402d020084242d502880c00340c4414100a41244c58000207086c2a01b02102c0310300540e0410801045a960103006058a10405101861962070800300d0702c0d44100e0b0160000d8181c1d860f1000d50301c1164444c209180880b18407120a4010070f54501d8000c03145507003224a5801d078110b01d1982c000c0b884c068000c0e00318480d80144103480d5541211580c00c01415400c10b014114499290200007105044c80103111078002ea10003c222100c5a03c6d050f03150400d070802c00d90410581c2121004034900c0403950301d205001c0b41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 872248552 1250 872247302 872247317
    0x7141b0f0102160305030c2107020112091a011511060a0504020d02090a0e160810090809040e0c0a06180e19050c030601022107060504080d05010803040e2401 69
    0x580100c2c50a2030905148070303101c10110f0701005100303002001e000019404000c481034881070b40038040760f10036400c0005124400c140702c060010340c01000c21f0003030704254030b00024541c0c181c3e8880244880070706445c824210301c01001480015038030080c2048003410360919182c0030700344c0103c1a40d1007a00910000501daa184045000c540e140e125003000b0940081c0800c6150400c24180002404d001f0000e00d040d06c200005d100040076000e0055007118090400ba14000101d130742d01d50003a00c040c4504070391001c420043c803402d5944510902c0c10704084100240704488555040c4100412207800c00e8040c001c44580f400d0580f41c20f1090b59080d00c1c01d1040c0701845881e201a81d80e041031112259900130707403e050411502e500c8000c091071103540241d08031440d6207100c0c00c60004a009011801c8088041000b180010541c180c100a130030911400240c0d01d4040c104130301070110b51702a0048070070394100240404c00c0e040c4001c0f0240d00100c414941d11074010410388a52000c0a808a5150510040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 872249802 1250 872248552 872248579
    0xf070204090b09061005090c04060f030e0102160203061014120f1c170c0f0a0207051305013002090601020313060e01091a040605070219090207141b 65
    0x1680c0000301129072002c5040701c142003c0780031944640003200c1035801d508201500266510704202d80c1801070045c441c43d20700c2e0a0820343c04640d481c401020802c02e058070760391040841a4240300034105d00741c50040814540000307204150600001900b04012190340d02424003e0104415a84da00c1e4402102c1030325000c6501e01042342001d50700881d03209503003d17110362020b6000ca003402282008605541d100208544840c0f00000d54809594800c003240c07080c000d0302c100010b00f000a06400078140100c441503952040010111003985504013151610ac43c0100042100c0c690042890f40500714100c48081d48003086003c07800c406d0f28060b02c101160004242c49074000d000b200c050000640c89a84190b0312880d01404030030074203892500003800d92100046002c412a850079552488095261600340703004000c4800c0c2c2c101c0d0800341e0784484904d0b0415807102800b40054020913000001580b00d0740c050802c80d51800c0303040032202158120011113501c400a00c114038014000445501000001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 872251052 1250 872249802 872249809
    0x303051c1a1c05150406050a05041a1e16030c08070c02010513030605090f070605131a1306080a0605060711130f0c08040b09010e0604140a080316030c05040b0f0702 72
    0x3041c0054001c4c0641c5950795505138030706211900c1030303015500500a0f611683c1d929401c40d032003160050141c010a20039050500d03400b611082e00700c40b250b4401c44400f1015802d40e0048801540c003101c460022050350710100350140907102e41c02e805418000e01d80c0c80d10240182442000707502c005c1c10406c2c0001d504000f42401d111b000c01664100c0d6040003607240c600e1001e9034034100000e0410b041d04c51030340e000500e41e01c21400c0310035550f617205c800350b4440d01d0104c841060306601d040c42d126280d400c1c895115108540d4900c0801091305685070020385c1006a0308008445a03500328501404041204e480480d8841c00054898042551a0703c51204400741c40ea008015001c03440000740e04144500b200f1542c0f0000c0b081c001ea01130000d0240c0c0381c44401d251401c0700d03000c00e001207450b0081000680820060500182c0303070f901c0c05080d10300030300c0745640d030180c5940200d40e20070506a003008040c408030360600c076140c40e00b82030f030401398685030800b20b10b001c080c010005000400d02c4005640004c43d00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 872252302 1250 872251052 872251099
    0xc10050f040b0c10050121060518061006090f06140a02012703180f0506070f0507060c03110106030c23060301091409012912070303051c1a 61
    0x7265a00c62602c0b1008943d100c3d0700e6030301402002e0500da003000004100707401340061801500101d1180440c0b14800b59541070040e010040c542c2801d00b0b480c9804c0b43d004d4800780a080d1140c0d43c03c030144c19503035080040141810086400c643d004c914204000c4c08807035009968042d0105054203225240d4100c0c00c0102c2c0076040080700000c2c42041e080c4e02a00040642c0d00d0468824400d80310f054902200c4040c503440c5e40c100d803103130801d00c041e004810000360030580700911a66015100c082c80b02c2d940c640706e2a03c0c0200e00c0c0c1c010000160080040418982e020760300c00b8103420768200070301c4260b2954440c04040318081c09140148401480b80c0740000031103000910b2004006801c4545070360796006070000034651001c100e0510594100090858001032046101d46c0c08180101d502200404105001403400c0e05074480e00050740c0c03842d100110004001d1039000318070075601d13a0740e1481c40041d003e842c100c0400310b0070141414403144002c00d0103c0500740c90038600036545c544d200ca030905416070048 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 872253552 1250 872252302 872252309
    0x11a1e0d0b04231c030509030414030a060516090905040506010509070905210c0303120c0f0f2719030f0c0308030906060102241321030905010c020c10050f04 69
    0xc0710018a043c40c48000c68141d00201a42ca921444820070f60b01c00e0701558003c461444403900104820300400040d2582911041d2000e0101c0c0d14454260760340324110b60050b9100d941540d05c10b8414804c0560001c08240a410104418000d5090503911250b8030346041c0103591084604400283c0031038810201b010007088001e00c42c080241c0005000c416003c0114000d440d1030194204601d000d007000411070749035071896036400e400759441c8115882190404c06041008040c20054002c0c40e5000c4409000311030f500e032032030f0b00b045064081403004000d030307481c03515001c0d000c0d60303481c0c0c1038120710030b040c00d0101d981018242d403040e40c543c5050551136007030ba0801441c420003c410b00c55014000140103105004c281c0859540d11031098041e0201c030301c08004040c46c04031a0300010804202c0801d403014091003009510320303940d44c91001d0203182001030310000001e87d542240c20240300b0309000300c0302804501d00150a10388600c0011400b10044440340320240b0800140039030040c490b040440b0003c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 872254802 1250 872253552 872253593
    0x3061211240304050c010c03080f0702010f0908030f07031817070b18060a0920130c0c020103050a0b1c0c03020405040f060e0d02030306150903011a1e0d0b04 69
    0x8111038079080d56080e40081d1010b80b40d5200307050103428254042c01c560710941d078042c0c4a402e201e945082940d0724041c001080c032000c554031800c03060801741950040781c0c01640320700b07880c2d600c900d0007112446c0040c0c0d000b000481003600b0324603952040c21003000f8000c140c64100989038040c0d41c0040c21813501e44658280104080d203090108820450100000366511040c04160362003038485032040002d0b00d00c0d80d1405010307a0340500d04070600807820341c41c452a000303016001811180d0040300c80d00c2283e40404041c404144150141021580d051051a030300c40207000d020800e2092001c0411048001d18a640b0310120003001d10703106200001c00d0f01c03c025070b80208184514942440c005c00c8425601c01c040b103241d030818503d014080f00109903445280450b60045081d0364483d02000101c0310404800c41500c6420824216183c80078020030400d066240101c072260413600d014098000b00003a0000350000042ca005400c5545180c1c0030005c26820400c0a9260b860b14204200c070490b0700f5a44990 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 872256052 1250 872254802 872254849
    0x414040c030b1303020c09091903030c030b0a0f060c0f0c0305010b1e010f0503130c120c0b030c030112150c0c020906010c080d0509031605030d060603061211 69
    0x400551560100c00c0e28490380c84084561550340007030780c810f0030b0034000801680150007400420b0500d01c40c3e85a114000030708032210760700390304207000e003140325000c00354000780d150b2580004194050144020b4900700707440ca65000c40c94014035107541112400789404000c402204c1d0400e01240c08030700c58405030003180d00081c4594a140250007400b0624803540100c0f521010411955005c004040e000c51042c0c5601c40410394030700c03044a40d039100900c8848801d030340113900c00129000c4044040600040040b00103446076508050504004a9001d01c8140740c0400400c4130540003101a070b8111116040744560411507403a004402000f5881240e01031803610500c10300caa540040c6103041203000390b4900202d43c54100044841c070000400c06404290104075803e4490800d5009a501c1184002920b0801c0010144000c4421240340251500c5d440440d641020b003905100d010000c059908003000303403e1611544000c900405a8050030074003130b401c00119243c850b88901e00400e00c0e600462070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 872257302 1250 872256052 872256061
    0xd0c1103040621050c0306040b040e24060301021e070c03060c0c03030509030c0316020f15070302061e01050607050c0307181d032713060e1b04060e0414 67
    0x741400b03020300e103289a15861421142d03490f5094440c06000308103075005140765945000038400036124840c043c941166446034443d6509005120b68291011960680a40d205a40b004000b800c000541900c1c0b003079104108091807116440600500e40400321866521003030542070421407105d290380085c1400703003415500c400c225400a030351448a4403e4034204440e40700c2e041c1107640c3c0d0040c0c40a29071241d20410005800207984d511085040d440100030814104904020502c00c80c905010078064242c040340d180c04264050116590100c141d424840703d0509000311803192200612546001c0c4000180c41403c0c00b5090018a112a0b4050102d17607a0680c2c602688011203140f0aa09030000e1030700e540c240f0500340c8103403a04014007096006604100c0b507503c544180c0e05141454561414130301980102e01c0d01c0d40b882c0040300e030303101c20000600341d8985509541e100d500108001160b400d00350303003c0c3d0603140c0340d801d440582c1c586240c401401035481000c07500400b00c03521880c100244072800c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 872258552 1250 872257302 872257307
    0x8060f0d020d1e2307151419021e0109020a03110310060608092e0506180106050a0f08070c031101110315100f09030605070e130c09050d03050d0c11030406 68
    0x140700304070a13581c0c0c12005a0072074024503117411755402021445d040080c0c401050912446034030254100d1000080c0c9401c0a010800040030401190200940c000144540ea02c2c5800311259520007a100024014002660f0000e000500e041c000207206118180818802d0384003001010702c261454a001c03c07034141c8610004d04441800c44621009201e0300e031119403204e00c00c90540300f4051f883d800d003001c2e0044e10b9180c4005808001c0c449500014000f41501907501c0420394140201595100c135a80c4200d940c1c0c005094500f842d0b041c00c1030100c0c0805104000d5440000713248082e4040c80c040000d0443c07406014050070904180c518594800310038419526070440050142c14011a034801508401c520241c0f82010405040380204000300410404944580c0201d544800140b070309040d41c0c0203807c00200781941802200700c07a40e5444032500050f542008000700502400c0b1200c0259a15a0364000c1c000c0c40fa8240d6890031343c0d12036031300000707013806203558880c03402840d000e80740c030b55031180d600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 872259802 1250 872258552 872258573
    0x80607080c0c151923070201090c1e090c120e07080a05070f240309020402070c0e040606050a050d02120a0f050f012f031e0c070308060f0d020d1e 64
    0x15400070007080304c02503182901c00d10514502140c100c080c410b40c22550014883c03030b2000241401d0944d5200c0c55040001203010401070007501c030b2002400c0403002518084002e40943c2e41001c80340c0f0b4035001d030000d0b0040e04941c040340040042400481e11005414245003054601d5010114501c13411011104011001c140030055074a41e41105c107801da921400c00f603580390480382c0080c113410507101280c0380c44c0c070a8104486903400680003500c0e2110996030000f0004c95035112014580f50030090100b000324900038180208401c60301d003003940c2c0c14403001400c0102d801c08000d10503500005c1507036842d64140a0303446220f802c0103a4452168040c10900d440f00d0107441d1011040d4031b04100e030545210305451462801401144109400503c80d14403200c0e9030014110034500f040054010079482e104016281c4691104001d140e101e04107442d000d4268000035000601c1480940b40d0645261030741450741ca20707250122090090100641030a014520280c0b010000000042d0400d90074044240381 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 872261052 1250 872259802 872259811
    0x203070602072103171f140102010e0a020328050708031b0a03020606060703121e0b0303090f090c0d020307021c260703021303050a02040b0109080607080c0c15 70
    0x810038900d24200f850720980702000003804500c4000300c00c020a42500a625444480f2403050310138000d011a41c09543c808030750006240c4c0c1501461814030796420300404902e07584c03490080081c00042c3d0700107510795201042003000e43c0700100340c042c03c003040c960407403800741d4004080d103107015180d00d85283c0341c0e4441c5000c6100001d600c44c1c52428130030005660302420390560f000d0301c15900c1d07042c2048041d078400031041d402c000518910241c210240d1090a90700412102d01d0703004600582c80f000c080e201401c845511a030801d01c4100030581752200b01a40d0103000b01da008084d55110705912849010340584103a4052001c401c00c038050b0340028011300c410b407c0f01c0c1c4404041d0ba030718100b201c4d42c010364411080c030072156850384840d10b6a003c070b1541c0c20100a04000d41001d8001034440750000c00c03a4815552039014100b000203505007445921034080c001e1910101181c01d00000700c2d95044060039040c10410780c900007403981400e0390182e91000d08a601962503c01c000d006030200d0417010b54 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 872262302 1250 872261052 872261069
    0x12020a0801060e0609130207170301030804030305090402040509180f0312061507080708180904120e0f15070c050603060d0803190504080903070605090102071e0e01030b0a0605010201110409090f020307060207 91
    0x304401c40049c21002d0f40c0c1201d84c0484000c0c90039003540c0c1d00302c3e00b58004491150b0070603000d200210301c507500c0004003842143c0d0820784c4082a911040d0040c03500000c492801c0003904200718000c61200395440e90340d4841e400781e034011504502400107052034442c10601904111003c140c003020807500d000100b20300d00c800c10780150000891401c1100202003a68000d1180324403036402c6401c14080c09400003500801480d07994116480400f2603041022540420a03900000500d001000008581d620280c80152040c50035440d00f14082040c8031080b040c050804600400052011100941e03000d0803c003100509011a00b4503140020081c0c00c1140014403a021b4024013143c1d242c850020b813035410700f0590003400c400d460001c40540782c0203800043d0001e6070341c0c0703100400c2a0203245080c82c0218801d034180003040c03030040c41207000c4031041e030011030440e41406958289948100c007507500759200c52400140500b090710340060343c6c466801c8001e406016444001803c1d58002c0f070b2803400c813002c09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 872263552 1250 872262302 872262323
    0x40f0f060e04060f060c060e0304080a060f09020303040e1b0409140604090201051611030316050706020a170d0f110901020114010e04080304032a0312020a0801060e0609130207 77
    0x403002c020941e901d030b0048500101c0b00032020000540b1950507001000d00450740040e01255004031340e4217551064103c0d85083e40484821070420146100303a025802c48a942003200c0c041e40e0340001d840788950700c01d0081200711803000c10081c0b4000c1d8050402c1d05c0c0105810766a0380d60395684507001c0e2030f0705503c000f0042491400608141454095041140e1f4140c0d115441c02c4824070001c3e0b0790440c41981a2821110b101260000b5241040140b0314210801580b0f6600c1d059450301034500990741d0000400c6400c000c4404002940301c126403285142040306040c1c031401044000c1c0b00503d07074510104402d504000c0700d080645850001489443d00a1b0300a1140c2c6101c200720f0380d0030400c20310400110b5070007940020041002a0081e40e0403521a1812400c1c01050145030722050304580e080e40040c503148600c040416800950b8242003c8050030254103004403540b01034540310051085105000003030141800c166142000ca40343c9400080243c0745800c004c030140002504254401c98605400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 872264802 1250 872263552 872263577
    0x703020901020a080a05070c23030d0f030c030b0315010e0601052d1606020301061b0b040204110f1b06060f060301060c0609060c081b1602090c040f0f06 67
    0x190088606400381030b0002c00041c01d255035082031071780c041d4958100300201800000001003c081c00701c0f005001c0525041150310340907801c00300108000058a22940c4080c400b0b0040e07981111940c41c1c15811800c1c0002c0c0012000340035030180800c150020b5140c0170b07440fa440180500c2104140c141e031810b1070710746800d5807001c006480510407903031400099810700340f000c2c2c41c823020344000022050310f5146045c1400207101c011044140c400d84c040300d0301e94000c401844110b500c8003d8040e02407581e05400d04d090b245445014081c003014001901664482c0700d4081010041803c980070300d0600c03480b090341c0303240c144694000c6500380c00b03c2c03420300d0045d0004103040d0325007464081460040104050f00c0c40e40703014001d84803000d0203e01194000d843c0c50b9150041410b81c85440301200d01611000303150f15000b440c1c0c2d54070020074020340200044c01d02142c1c0f02a04021802202030364143c1d5a05070b03540b43d804020b045030140e540109038040c81d0700400310b4400d030014101401c13580161544010b4159 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 872266052 1250 872264802 872264807
    0x16090f090c033017100e04030527090a0906141f08070f0b030a0917210c0a120e06010611070e010e0c07020409021503100807050306010b22060c0b07 65
    0x11141d61140020302240354200038207414600e140c0c0c1014800c00500709955032405039100719442100c0030341c04500023040189003204a00c01e5091040c1d02c2840e2b03a007918440000044000c030000e804403500503a00c4815208100142e842140d8074040f5403011441481c000c0a1b064081c0980d032512692800d032001d0004441c50000740e42c90a407011440742055070f03428181c510703c0e20342000740890001500e809aa40100b040308800ca000d0485c0b0322001c5070780f0300000740c44002050315410420b075100816410000410700340015241d2003042481c00c0c0886240125035003002d0000d12010a40724000c43c000041c7d45a00001c5446182c0d0300402543c104c1562071080c1102c1c10802d100c0c502c5c440d184500014480c04030a002020321900c01840083e03c0312040d00030401107083c4403130186644a0004c20b01c041250310003000030003070a0000041c42075500300004251102030601c1015000760000c0386903c80b40740d501c0d10703040c903c002503940280450f6580500030841c0920200555079407000c00c000c92010f62 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 872267302 1250 872266052 872266133
    0x140c030f0307060e0a14100501080303060d0602031e090a06060501140a0e010c1a0a0609090816021f02011b09060806010e04020c0102131716090f090c03 67
    0xc081034069800e114058803030304042c0064604945940c001c011134000020000810725048800780c5000300000a1940361030004c498040c0c100d80756a90081c000c220043d03992107a00e920b076660101015803241c803603100380f41d400c40c0842503200c09440408104080740600249000d40e0034001c610900140c3ea88a0064465078500300d07128443d48000c001c1070007458010056041525018540540803100d01d480e030b460180102c4c902c40d1030103030811040c0610080c580c041d0304060036403d04200b000f00403d40e036640c0c45101d40c1c9207601d40c08100007041c005540c1c4168078600d40307600212400f0300b24010b00100034000c0c288000d0509054028038502030f449441400484180c800d2074031401070715280c02c00191151070b208008580e000c4d40801103240c482038203002414028003824620a9290700b0b002404541003c4580700b00d00035442020880031002d002d44440c030444402000000b145015003009002131314813034101405146400400004000e008146510403100340b03881207101c038080c251a5042e09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 872268552 1250 872267302 872267323
    0x8210306060f0c0c040c120605090c070b06040615080103060f1b0c050a0501021b0708120913060306050c030f160f030e03040e0f1017100f0e0a140c03 66
    0x180502c8a2410380756500300400c01c418004080340e4441c800440001c00b526100d505a0b40060303401e044040c208401030244401800080716203040c00d20300862050654043d10b00080e0030302d08081d0208613503489035481030020f05420511010061709010b0054503a00c000e00c0100e95140c42d02d44036007041816881490580d03031107265440030b840400d100895010850240a48260080541c50000204244008c04044040c030700c1068210341c10440f503d0604a5642c03107205203810643e03400501910020480381c401030b0403280c04032540b00400710003000700314640000302914904030a101e02d4010003006140300c1c08007400c4501580da11101e1801e1400d0801c0e200c800881c90000922107001c0c029002801d11405017422281041e5441604000c455016901c01985054000078056007145400c078440c0500b04420101d40e40100f05481c2c0c0d5034800d4000724084c3c002d6995004810103501e50f4014100c17111302d003022a801c05003d410030782400f08199031801c0d040d206402c2038448606011642040e035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 872269802 1250 872268552 872268559
    0xf110a0c0b0702030c180106090522090c0e150f0607030903081e1305010f170622020a0f020706020d08060609120a0305030f0604090203250b0408210306 67
    0x500d030410642490b00009000c076814058803000000580703842440042c0e01c01100305250031949400c60140c0303001c005401681c06251a80c00581c0c5042944010307282580c007260340003a2601003400c00c500c210301d40e5000303408010062000e000d5084003c581a80369800110344207008400550304004062055800007004146484003c00101c0c0100000e07011982419417000c22081c90341401c00c606500c818628605101203e0049c0000c3d43d000000108500613410700c4141c400074001c041c641800300a00040c4100d6204400a180340340c118200301c202d108460040d515204203080142080a070000c40000500c02c52900190300b91000880b00d401401c0e1344c55118850310f03130505020b025403083c20900c1e040520808120303800001080102e00481c001e554030b54590070692030b00441d10402410081c821820011b809000d03030b4011074a415034102c000001840c41003036810540464850b540600b168040c017149c0010603003408114281c1e0400d1010803d00d8596882c64683c85501080e00c1c074580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 872271052 1250 872269802 872269823
    0x606030105180901020405030d05040f0501090b040b0d0f051e062d06040e0103150b101b14060709090609020c1e0708030a030b040b010206071409010c050a030f110a 72
    0x50094000c000c0070f4020030a903002510740380d22900843d01e807455072000180011000a0100b110301d51207450701006d82000d291441c8a94500840f1464600442c050200c4200f00000c2c3e044a00c145980401a0000780c10001d01082c9480f41e040141244190000307482c0494850004001d80340c803021000007290140340c2a00e40c492203404841080c8007a00d00c0c0da8000f18200000300740301c44d29600c0c9900a610489243c08200c2002c589c3e20162030205011380e014040380100090000d411500c330344080400d4001103020000181010303130450b02e0a514003080d5010300003d201c11103a12a801c041540c081c00c50910016581d0105401284503120f5907004907007019215851302d1304907550001c950910041100c5000d5202d401183c215880358190301c01090f074550620441c0d090034000d45031031003004d0024241501d06014054083d0005141101403800c00040c00706c000da01400c41d04040d00d4000d801c9580c01801c5160241000718908400004503000e9482c40700f00c1c01c000618850100c4c2c0c000030701203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 872272302 1250 872271052 872271079
    0x160206011202130e010b150406080c0703180b0d1d061f1502010c091d0f0907030611070309050d080f18040f09021507080339120606030105 61
    0x41c10901041012a4425202d800044411401c0d0242c80d261243d040d000080703000d01d0000300300d03007942a10166142c14109000409c0134682142041741d0041003030860f1a0fa48085107021110810a0070061802d20240741012030601c038108090401b5501240081020841c0759800c85513054040b6684803445e802600082c118800d03040ea01c2400f500040052941280c44454114056115502a40042c0c1d55450108031381ca5004181030004c0c03a03641076200440c11000741600721541c0060640b016080b218021030702461081010000568200e0810003124a10444c1e168080e442980c06030005103085002150500d050010150701d81d40c41400140362041c0c0510103d683d0b00040106c1d40c2003400398500660319102d50150312810311810030000781c440d4140c810400c81d075100b400360003030261060200030f0000716070300b0849030808500403880c08490500140c4030707052004602e01c02c4411200d03a0091240c091850b014003501220403c041d0b02c82d903a4001032040e070380401d2003060390044004200c030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 872273552 1250 872272302 872272319
    0x601030609020111031602090c040608060d03020f01180c0e0907030f03120c0206090105070f02070611070b070b0a0c021f021e130807080a050c01050a171e16020601 72
    0x16520710744181807000080c60011426415134000408540e00100090703520801c61030301651043e441030606e010607003040d0500300300918041c2c0013000103001d2103612500c9801d15008210f545a000e001e0310003488104003800d025011f000484900703e46103000780f070011a02e06460040c5074400d000203001000101d245441d8042041c8000e8815814441008010282034003207000e130102c0c01d08150000d11560a00120f100d0071500e004240d0030801c24804180a0466030104a0504a80e654600000900781d44181641480d806a20580410b00000f0700e80d8200102840e000b0b20940a442c82041082080c4900740c3e2100809000d0402c0610202803403aa400410b82c007a040082c04454158800e11004c914125240d108800020404180c1007041050700800c00031900074107050006441465503940e2802d69401800100b1814010046603284e0181d10480444141c25451148007205040900d2010854480824111b040900880c00100e000c3c0c401c590804008015a0040203907a107801d030744 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 872274802 1250 872273552 872273561
    0x90b060d060905060c03070e0a06021b010504170a1407031106030c13031103010c021219050c0d0309140a02011e23041d01060f03020904110c0601030210050c06010306 73
    0x40751a41e42d91940c400103d8010401d151003092002c40003541e0307041600e0050b00302100f143c0d01502c140c210072001d00c642a03010419030340042d500307811000058804070046e0780030b0140d81c02030021022854a0184a03240000c2e824000601410400b0040d40c0100d0300035807900e007075003c023608503c660f141300340d40b904040c80156400001c0c4400503042c00c82032800c142d0b00103a95401556018642c25110005150070321031400241e010340010300180e601260244c02500038020b04407a4501408082030700d250040c41125501c46003401035400c1d10b914010041c0040400001c2520200840560110110400503c2d0050981c058403103410011150706855000071105088108000c0d050905000302003c42c03040c05c80ca1010602030686982c10701000c5601c4030155820801d0460380c0d0001042410b8201800d401207060740d181c0540d0b20f900100c003050103006806000a0115400601c200341e884001c04c000e41a64422130f50071074040d07a03002045600e40034890b100041c90300410010000102c1680c003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 872276052 1250 872274802 872274829
    0x270b07020a03020402030906010e1003020a1502010b210d030b0f0f01020705130207020f0a060c0f0c032103060b030c0a110c06030408030a0b0418060e0c130b0a09090b06 74
    0x900c0741c1c1180c0b25400b00301681c105440c541650791140d801132091004600c4017550081400f1219143c2900d59000502c600c02184156003586400342c010310700f40c40c401c3d0842407003603d018106d5805c504c2c1c3d0b0200031005019510003000f05004401030603120512a004c1e007001502c005100300c0a00003420304004035983c00300754075810340c4185070b40010701c0c0e01c1d520b001e000d8142800c200180ca680e09030040c440489020006a4451044490103003c96600403080b61103140e0481d4001236002024600030600c141c4030382001d040c1603180703815041d80300701c44034a2440c2880c003a41e0031310840342d5541100c8400d0009403034881c2204030a01032140030b03d104445204060034070404030780b0840c4040c0042a0f0560050310140d034146030000800011042c0c03401a048030310300c1a00c04100c12882140c61003011562032200504441c0c4850023407801e01c00130072244000e503100501c01c0030b040041d00c0300f880041c030304d400c00140910300d00c0c03000140d1018244543da500941081e0000e48036587ca10421401412440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 872277302 1250 872276052 872276059
    0x30c030311011514030f07050d1707060906020c10050f060402070501060504020a031d0a1e2303030912040e070e130204030b46021c0c270b0702 63
    0x140480300f05611268039000340000400c1c4002c40140c20149411301161000c24141640802001c00032030f20340415a03245503400c00a06000300c4034500101600b480342079005040341e8105807404d000d0040990040110f080c02c18102c1c0d0800c0300d528010015079500b16101c49080b50440005081c03401c10713400500e00d55100b0000090443e0f143c00005040780c010b5070100e000a41d40317a104220002101105c000030300380d13400041c000b400c100d64541e801045580c20400c240c84138012140100a007001521520030010b81208820b80f440044a587d65007044602e21214840e82491440001403034040b181030320340350030143d20305503102030341079880d409a085074640090001d64420030604040c4090300c0950b110f0380d802d4a040c18020320818001c00075010255043c10b001003107409050114000c0219000c81222040074412102c0c03420b0020301a4040b5405400c0360101034040500995201d8000c8035002e443d0f140705480c01354100c41c2024901c002085c0c80080040007444100b6520f00684881031006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 872278552 1250 872277302 872277311
    0x4051e06040f0906050c0d23071409101206050109080307020405130209100348171c020c010503040b040519031d010302190c0f0803070c03030b010801030c03031101 72
    0x15603510782101c400b102c031b68044c0040426072180e400c1150081e1100700c0e0745d100b22188503104c070f100d0700240445c000d809035040c400019403044515102005440310510000c111900300a003000d000b404064a00d40c1c4001464500f600200351580034502c2d480540b1340310710040d03003051155424400241406400c9002075039403583c400d00184e03203101c5c009108054071450741c1c3c0491300e075203070111803405181c0340d00880c91014500713154403520100d5004500481c44140c0708044201c181d1840c1840340c160045410007440324004d04000c100040c2c0d2000314001d400c0c0e0096400300800040b40c4504006043c1400600204040380100f960761450b150400d002d036040d600c2c201c1c550503d1042d082c1d01c00d442100841c114422a55081c40b00d039a15402800080c241075191400c500c0c00d030f203944800b200401088c000581e03555020700c04010014180e085d4031048c01941e90400020281650521040480009051180c0420254070a4496138100da5119880c62611419680c0a0342c0c030000042c1c072001207650f41d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 872279802 1250 872278552 872278571
    0x6351b0105220312020607020a02130515060c030702090a0603021513080313064808041d1b091003091a090c010305090c090702072304051e06040f 64
    0x1229004000c510901581d0007420004c00080e052503401043c101c2507401c071110b10005612049208007035141240c1c0c0001d000d03512400c21284c1d0959540e85203802c00c0000c10740150a0f00c000004104190003120501c5490381e4a03c42d60043d01c2f0140002900991004080168602c40f000503001302105100020011a2219001481c0d07030043c81a40c070500c0c050110030440d40390403840070f1080070540c0c26000b050b6041c220920301500103051018002d0650b00071000200f5104c00300407420f09901a6000b9541e55581004100728100e080000c840a42c484001c02c110540103070300c260107030501c4035501d81042210002c10254400081c440018151074506d1078002841c81100d0b04882c010000c4100c060341010100181303401a019425414107141109010408000003014601403030200c44492460b40c3e036407000c0f814581154070440d821101840aa410707441c0c0c0d0b2249412007a01034500308045c0d170b920b01c40c0c081101c11544200b18401c110710003042c03160500b82c00c80b20840c044450040384140305c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 872281052 1250 872279802 872279857
    0x4020715150906060804110f1c0807330504021314010305010608030a050706200c01020406020d0519080601050903070305030301090509161806351b0105 67
    0x40e00c010070100c0e056200d0051100c2034440c42590013401c42840c0450131480d050340e4210016203040d06041c030801c00e0105c103121580d603d00545a29a2101103214215801442d10701c81a4000c404201c0b141c076201d200d900a40c007411508102140405001d0050601886030f09000920018109030707001a512070103050400000c0c002c01990500703c00d0300090030341c1b55080039821602d8036040302140e90820002181410b03803000a55880030781002001803842000d034054101800c0c0c404030300410f440c0100d01c1340b04064040d40034000302d40c429002c0d50088283c48101f19010302c581c2c644020011240c0380d442c00c80d14420b402c0c981d030048040c100103180c400d003800080d1514480d030340100c0b40f0741d10000040c898407406000312608408440000c105da20281c0418201680341400f4900c2c04042d141031205495040c0d401c15001490b074400409198840202e1004140d807071400c07040841950b40207020404000082e040f600c241c4010002c1524400000044074a079000c501016000c100e041d440f03058140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 872282302 1250 872281052 872281061
    0x80607080c1e070f05010b012c2e11030a0c081b0f0115050d0c0501080c0f070606060f140f070609080307030606121b030f091a01090609150504020715 66
    0x10f00078000c14455500b646851742c29140002040384c100400405511058806042610341584c007100541c42c116601d54089005004400c0c82c2000e4030031072005100030890342c000e180c01c809000c2d940b2010302141c0002e074070341d4901c03441070440d00203080c910240c0041004400a04481244444103145450144038200d250260030b116964075a5510f68a800035440f8407601c4030010541a110f908404400303494481105a191003018103100349000040c5040e840c110490b040200e010140341e4550555082c41001450180079840c0480c145000c182e04590040280801c21114040c42c18509041c41c01c1580701a000004105d508940b2100796100040a0401841c810300080d41c002800f0f46c540b040040840303092a05045111f4641550842c0c2c0d29651010240b00060500380440c0c01140b2404a034000d041b40380001d032581c0c0008041400da440703041200340c101c44500d08148484c80d2111508002c03074100512000d55078030300d02c904005504242d00a0300100380140d406904042c0d101e00c040c002e85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 872283552 1250 872282302 872282317
    0xd09051f05011e0b0f0c1e1c0219060c020307050703060b0a170a080a09050904060b010210020c0c090618090f07120b04110f04060902070c080607080c1e 67
    0x207440d0030040c04114460800302050244a400000090b490078003522510b20920407911000c0f00300043d9455180c40811450301c0d00c44583c0c49616004105580003605e900c4100e800241c05a4000c80c8000950720002c1d00201070428240022031044007603a8141c01042c1262104003980001d11181012071014062400114040c0d1400708414414500f000300e000290707004a100104070032010f0344800b038001040385019601818060f031361400240280d4000440d5413019070310803d0a401c2004000858200081140d030a80885035101407040b41c000590041d50040d074000c0d4800c8079155600c3c580b00d000395030440d20260070302625050b142c00500202c201203070a070000e5401000300b02d07440407080002d000200301458030740d000035443c6d0741c0340b0868403400760010f005400b1441901150b40d035114a550181031004004200c40c1e60b54008200194022010035500c202000d500065a5074000c22880c0c410040c558580605070b40b00a540d05094200030700d4100c0c446541c2d1203030b22240000c0c20042949 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 872284802 1250 872283552 872283613
    0x61e020f150a060b12010605090d150e06010e0c07020409060b0a1d07021b0f040f0c020c090a020901050f131a030609090f06010902070206090414040212010903050d0905 74
    0x5803030721205200c1640c61a500031443c0c12410071480c0b1034503005e90398040c151680c0c2e00c5c2c1182d4030351100340001c001d000c0d803810180140e40f92600c02070312144130707900031003c1d400e081068031226a81d402d60032a03603080440c4c030342032900403c011100043c549940040300c070b41c0c0f00303840c0024611002400314900a00c10342001c01401c21048409520030849144250310071400c3c80100b4406241da49101c000038007580280c0d01603804501c80308102d5450340c20200c3e603000c0c01d0b00d08220113010268000c1d079984641202600440c0d13641c000c07510034403481c002c4401001041e1903c520700150445800f24950001c7e10700100000d2800b40842d60480300ca400b148090340500300192203040c14010405241000340607100541c0c4080d000401c0b201001ca2003604603804074500517224491800401d19511a4400042d40146000494212080075000140c0907a0095911602041c0c40940392822500606800340120f102030015034085d500d2900f160310b0703c1c1c0c0300c0e10a45800040c0c4c004180561a00500d12014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 872286052 1250 872284802 872284843
    0xb0d11310e10021908040f0605040b01060f0e030a030c03090806010806060f03030a080c1e0c0a060c110c09130f03080a1815020c070f0306060e0a0501061e020f 70
    0x1c10300020081070180340078030003045151000c0907814510040b018858401484030110018050010301144c0ca243e0304d80220040c001860035260000425501f402074001003200b59007100741d43ca21510030200301180240080200d0212501d040d00e420303c01c1c1c0402c5003040036859000c00c140320b0a0200ea4002c1013008000c0020342080000c1214110309415080c2c00f0364401d00103203065035404070a6941143d10050801c0d034820001380030180c84c0b5801c4e8404103d110000500304803000d400107810301580e0140d0f4040000392500d180c101e803103000c020050350081c2e0203801c40c07000d10302d40000020307000a5a5607600301300c01d845035265080180c2807401580400c29510800001c140d490082c01c800c001b030b1001000c10920a6502c1010b02e4120780f210801c0301e64046a401c4e0f400104118070400b81c0362107400080029543d192102c0030b0441c500a420b0883c0790b04011800306d2160b802032505036242919030322058043c800940580d8a40d90244c00214031070807404442d904001d110184074090102c03201c20303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 872287302 1250 872286052 872286071
    0x5070303080c0c0a2004060f0e0105010201020a170705190f230a050310080105011e0f0506180102010605060a0e041103040b0c280c060b0d1131 63
    0xc14603900144a019086001c1000d005440070208012a28540c814103105010301e04401e80d03d01741c070b050880d003a0014036010020411581c18083c1c90121030007aa00c440b042d0f0b8030f6000480c286d01810b0402d00c00b00d60b84010012004114041095111106103081e605111440911850303503182100010040b0707070f20304451101d0342c0d40308160383c001e540a60310107105500e42280c045081d104030030019007004800300201c0c03040c1c80920020402130104600a02481d61501106500c011491212280a03403944d100041c0300b480c0c07503880404071900107010b5402d0000b5150b000b50b198800803512070440d50384000c046015610100901410115540d0b0500e03a00003640912080310012212140004014000c020000350190a22980100c070410074a8a40c0d81000ca00d0000840380d0701c07114110b9840751094000305500c02102200706020300c0d014000300030307080e040c01500042428090401085a9445496400c020024500306c1544541d031048171500141004681c034201d1b4600f00b4259195020324 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 872288552 1250 872287302 872287307
    0x1110702030a0b1f06030f05060a0e0c0f13030b25080105010f17070906030e0a050316020a0f0305010f05182d06010b070c0503030a0903020d060e0d0806150a02120f0903070305070303 80
    0x40e60001007039403512b0314141401c2324911080e8000b0140e6038803440019840c00c82d1004101940c0501c40c0500f0742101c203503103a00d0300c41c071032190448241140a0010303103400850842c20505180c51001600c88894590902c0c0045400d1403100741c141041c451040e0000e80448054864207120341c4441c0c0c0c8001c034042c24401c0080568031090551092940550b5524002c15004011580740702c43c88000038031a0a4588085a90038a00e60300424011101e61000418040d042d040002c0d0030504090401031961203010580f034185e0b8000c030401e002d40c000711001e112003610b0480903144007501c2900e014a00d00c40c81e0345a02d442026001551401c8010440d0b10420041b000c858000d808114051420b0503a200750040070703407150340b1010744102e00c00162082444590b900100d10001c1840c180e60445100c040d0207000c145040c0c41c40d9000c1e04980c840301c0c6010703240da02a0342e00301a460f800b8002e40c0d41c5070009054a40c00c001040004848108580301d110340e0100602c40007544190081c10509284d801c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 872289802 1250 872288552 872288561
    0xc030c1416081209040917070302300a11010f0c050942040e0103230105090a0f0507080304170d02011b0c0f06021b01110702030a0b1f06030f 62
    0x9040c550b03c086001e540c0d0140c88000d5039055502610005504225810400400740c41c55422020454001604009140d40071544502c10066030b003003011381001070040321031103c016004c84100301c00c0034818034001070f1045601c501e001d1510400844c80c0307c01d4003031001c11120241c441c407001c103000207084009820601e03200750759062001c81612003006070010a510b4565004201d450721030300425070401c82103607102a14007420b1251500100c0790303128038120000c0340030202c08082070a91098440c07a041014051507119011140c050050000d4540d6541c1c08042d184d981220503010b50341010805807800c10143c001051090440c00503206004091030410101c42110300440e41400c0554071b8442c00304a200d00c60055a1504024104403814410b0881400c004000c1c51107000007a1101503901185006003280304990007000003103113a1010044500c1307550070080d05a001260081c001c00c00c003d2200da03000c5a85102448408100c003002e840048194200c4004242d54006065105000f40b10303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 872291052 1250 872289802 872289809
    0x180603020d14010f060c2607151b0507050c0603090313090c0e06210a020c0d03050f01030803071b03260601090306050903280314160c030c1416 63
    0x410380705075410300c0d0002031521245c0c0550130130301c4101808441080f03007641c21000c00c0009444005045c04002d84500c5080d8400981a952880140e0442e030340e0003100e2045030850040f500790704100301360045080c0c0f603c6c2c005074403e481c0d84c01003d40c00840c94542074000e510620b4904069a034503d600e44520f070002d00290000052980352411403128903803c00d0708138a00120032201147c6841d002031251104c4c450b500745000b09403605006108488141d500030340359280d031000540f464500c1084080f021106c04a5a803003440c43e1183c010008513480070002e603001019490101c40c2c1c02203201c400d491304e21081804400054800d050f020724059811030704a01d01e022643c40503032034244000000c103008064000904990794800100d012902c04208132007071090300482c45402031021020f44983c184100c02001e0100703090040c550303100032412020700c3c8a24905a80e48050740d0349088120b40200b0500da0403420b010300d00708176101003040240c2c0040311490f07020041000c9003c450b01c0300021071440e80b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 872292302 1250 872291052 872291081
    0x305011a07020d0609020d0c030b160801031118041a07030b18060a05180f0a06030309030605190218030c011107061b060606020f07051f030507180603020d 68
    0x810306910a04040d048a005980480354a4621032090500c0c80040c1014000250300c035041102210400c1210300c0b145040b46c0c00340402c2c071941d58508051b0490300180c08424000116550014000990b83c545880030052000d0a0001c1e25000106501d80c0d003001074900f0748d103103100d07504030200845040ca12140e0200301c1d445c00303002804030000841c1d8014070707840700b1a0000c40402c002521640f58070503004010b00e001005480c00003ca03081074031801900380e49040a0004c0c0d1400500c3c0d0440031f0150000b103980c991b40d032440e003600c0c40c1c50314030003090040e20f8108405580060280d20042034000f5200b800e4a400d0b43c03540c604118402c051800d0901600103041c8410540c050400b41d001144480803188107040103880c96501032848000311034841402001c5a282c081c0c0031942d50b5000814819008081e0116142c44d82c58034100080e42e48114038114209281442c00c0016500c00d030403aa40027002c0b403c004400c240032210449030306049800242c002030b4007062010b9212110b0140c540261201b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 872293552 1250 872292302 872292329
    0x10c0504060e401a010206270a08040501270b0703050405120d080f01080a030509040b13050a06060302040f15110d02060f091507030f1812030501 64
    0x654040e00264441c0e40080c400c8100c40b80b800d00c2404902d510a00d0501c014840a00d141c10503c402e019101c152880c1e1440303a45040769a83d000f90441c04002c1e00403d05030020700490356280c02c0381015a0000b064010500540e1202c10754098080080c03441003803041d405261610300302000102501042c02d62440600300c1c521090303400d13000602600094820620440c1e40e90703071081c00c09441610030369015682050980340011b682820206140701742803803030f80e10f025181d02d4407903051175031140a00408405030001d0007a0400a401140180807c51000d400800d4107490000001c1b084041c0038600a410760325242007180d080d0051060320050805400c0446c1418104070f14603040200a0103002061107600744140c54070b6000302c8115841d11000301c00c0312002068803038000d445090035107460100c0e5500d00f02041c54000d020804200c03415108165a0955540c140c0480140200c0801c0d50401596a9000720003901c9080080c1c092501030340b1090146202240d004080b41c0c030591042c900603a50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 872294802 1250 872293552 872293559
    0x51e0a12051e1602010e0f15090f10083103021b060c0a0f05070b04090f0b0409020d12053604060e010308030402150a080412052a0102120117010c0504 66
    0xf400c800d40107454080c41c00a003007110120102e4400942400c0e680d602100545401c64842a503400071b01801605540101e41c980c9400c040c03003089405020440b0110f101003001940881e014040c820070500c020500004a0519003000c0e078031811400410740040e0001841c41e4020040200103005403a419180c052600c840e947d84d403a110070101d00010050240c82c5010300c18401e0400102d07029108580d081991655590414001400c481010b06000d50400d603812181d0718180c8505614543c001d40301d880450460ba580302d1140b80d415280e2030501005000301000326050304c080c0700910b118a81105040f0326070b40c980148030610000c2e0ba1b8800c03400c000d01849488803a10f02036045960180f4200d44035295440001c1092a900010103031812011904001d11540404941e0040d80507140f4007078042c81d0b12508a55034480c0103e900f0283e81c1c111003684407010244000c03800c28012900050030448280c2e020034940a0a030f0042c1c9808406502491081c482803042d07480083e55810000c1c40d1516 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 872296052 1250 872294802 872294827
    0x1b0c0604030f060e061f120b0a090201021c1808030f040e071b06050412080408160809040203100509070513060c0519032307051e0a12051e 61
    0x164080140500b90720032019003000b206400c603a02c2841e0030710603224103290918185400300000090074920010000001500024210b0360a41040e044004e2040580e650012000908101d042c200d04602c54074101411143c10704007038819081c4159554404071190071044006008142c0090209410400814080300ea440045038210b4200881c048650350b100c0c1700c15075490000084506c0b640321502c140104100c101e9000d6441a8407682400003070840003002100c00c1d11040b9002051044100a100030388002100c8a80c2e005104440f62880d05518402080c140c0e082a19042d4900300b9842050020785468002c850344600d2519180e0b041109401420220882a208680c107020210b16030030700340603061003640d100c0c05a84240b03075018046458000c2030445240d45030140d05000090b60110982083c0807120b025400500829800446010f04003544021002949041c400d25003240d00103102102c01e030a515a00c1e403a15a12001c10304a01e07503001d200c0c0001d0656010081050707100112 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 872297302 1250 872296052 872296057
    0x1006050c10150b0406120e030309120d1d030c0c060715050c09030d0f0e03071818050a0503030a14040201081b0c0714040608060424090c0b1b0c06 64
    0x1c00000b060b4900b540c4010b015140c0d4907084203110b4540060080b03503107500840c1d02480800d050360108001841881801d449000985c3c8400e01d54000700b160401074800f40010b0202180280c0300014004200607500f0010080540c85840540011990800704c24042c13111003801c9109682083c039001c055601c040e04c84c1110041050603a80d907001240e21540e0030020350304000006811100e54078010100a00000d0030b001280d80096010300c1e00d2240b600f400309031002201d02d1100c10460b0390300b121401c4006020301481100300300d080c1ea903400c00400d0080050701100c2e0b0141000d1950390904108190566009544d000304c40040d10703081c4001070341d0200f90103a20a0748080840d0302402031a46a2583c1d12405895050601c28410042070a140541282c65010b0044900700070b010344d10145c00c0d40310350781150080e200c014244a03030f01c540a000a00b6003580041403900040d03c2d5002d589241e1108400e0300b080544410100300341d80003c020000450b500e03114075004200070700443d80041e1051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 872298552 1250 872297302 872297323
    0x106020601052d090c07020a051914030c0d1410110706021804151701150b032e0e10030b060f01120614190e010603020c0a05060408031006050c 63
    0x1500f2801e103000709107002501e80016400e009102d40d0030f5091000a55a00b6040380b01305030b225006034a0009550314101003030b00045100540e188008501e8040119842c0d400c0c5412a600750042e4940c801c401d5860b2500e441c0700c0b0f031180d00540000c21001c61001c5c9081110342d507040840b40381c00d15406040c4a9542501d141942c060400341e0b03900341911509004c240f080c02155040f80c00c1024202d003040710040c0c41400e0342d004940c100107078040caa08941c26260300305502c04030080d015000b40a003102540c000c65002416460401c00590307414907000b941c1c104070360f1015060341100410301102211410858001d200b1101a030541c03421921440321f40c000c00340c176103441451102900740c456405400020302912010340e00f04030441d03590202407601204001164031030200c40452100c1ca00c1002111400d4952004006100340c3c00c00000354025030103c04299198492019107100090040205910030340c424403510b512414103105800200441c1e42018042c4001401030007009000041c015045 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 872299802 1250 872298552 872298589
    0x60f02210c010213090c030c0503061c030516050c0108090307022b150b15040617040204020c19060b01030b03031c0e03040b031014030d0f020f0709060509010602060105 74
    0x6603220544818024032526508480c01d038804000000c00c0389055100c0b200148840d07d0074000360700030f4503044a01d40f1046515a6010b4180c03400000092880450a00c80d24840d042140c03405402c01f04c10805103a10a4040310203034801503403951603581c8030481c80d4110b91120011070400c152035002074071085650480011011404401c7c555507100400c00a00b4a908440c10207660b05002100a0181c184d090701903000e1803052002101c0e02803100b08981c200e03030096a40f52007160495522121848003c1d00036a40641c090150004280040c0018102201d0300614070b2440301203032401e0403c0c0c5021aa4450600d440c3c105040c0d09900d01200721041404c28038945031105c544003a200d8000d06004e1150141c078480401c000c41c0c0d40b0740b80c10085000720203036040035520360358070f051402c8000c5c1d007000000c0d0150000b55000c43c940e4050728079058100c2e02e90040c0c40700010900606c51400e1520ba015451440e21208208075034100b81ca41140034007240c1c80603022660404000c1000d05051180e800c50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 872301052 1250 872299802 872299807
    0x40122001020c1009090c11070e04050c090f07091509210501230903090a090c2a031101111909050301050c0c0f06041106070f050a0c060f0221 62
    0x1510380c0300b80b108000303007107005040c65007208124000614160300303405614602d6191888280074940a0461803080c01e02000080035178030b007003c400c550340c964040e008a4580c4107131503105801d40c1d41c40d0310551180d00c0002241a0511f00f041005000c07a0203580901c5508105102100501e03070305c140d1200c240d03600c801d442500800b541d41818124021135001805039486c06500103841e81c0c0c15440c1c2c5c608510786403410388090325200000c503101d204543c21641d0000010004015811313940c0c1110302140305034104005105141d900982c041c400e003040e0009001030b0040a2004c06401c2800d4144000d5000002c00105000305a40d802912522103c1d46048468140071100140700e90308007805400042c00034016828280940b80c5a5081100840103500819000002110000811520864000309480e07108000307081400411ba111242c152840b031011441c0d040452010480b00d0031840c0300e044101c15581c03402400401414565070f1407002c64101c000c0000b95004141180f0400420a03e08a82d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 872302158 1106 872301052 872301113
    0x230a030e1213050112090f12020111040f03030e0a081f0606050a020a1130010e1209011224140a12084012 47
    0x6040302901d801001a517104900c40809140c0242c00015882d04948403401d101d03040100c19141c038102c140381c0901981d824031800000040e07503003006044ca4101000a0346200242c400642001a1118520303210758a408000f0010101e4104940f0311403201440c2840303110080c02c000410f1440c100380092102d000c1c0040340c4108072958003411008407540d4034111005e010b0217500b0f030070144204502c2030a00d01048035180c02c0ca4403a101c00c15103030808650609485080202c1800e58100e164400e12000114082d192140360908001c0f00000860201074020038076183d001c1414140b280020003161441d11902083c0c407070501c41900449481340c180196600e60b4814001c044000d4881140412000340180400329110205120050b40842c009442c017004140d6800085084c0200003906002181a80300117105600700d0004184190b1900724148845091100300e107040c1c0c400c1c0b034 = true := by decide +kernel

theorem cover : BRFrame.Cov 872122302 872302158 := by
  have h0 := BRFrame.cov_init 872122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 872122302 ≤ n) (h2 : n < 872302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
