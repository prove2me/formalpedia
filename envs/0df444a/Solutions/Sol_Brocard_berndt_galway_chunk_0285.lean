-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0285
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:57:54.358883+00:00
-- url     : https://prove2.me/submissions/b91ea7c6-9309-430e-8547-008abf78e5e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 51079140 ≤ n < 51258996 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 51080390 1250 51079140 51079151
    0x80a050c061606021303020d060902010311090102060a0905030906030f16050f030a0c110a05010509300703090b031f06030c0e0607080d020703080907151e020c12010f 73
    0x3014440e481c040e8950946840b000740140802092884d0002c008203016a49000c0780181c40b81e000817103028034500240e036010303030f6903001c0021543c141c41a4101c00c0f500c01c201c1c90521510301c0c0004d41d940002007041c040680c942c15900204401042625840d0308003e08a54903854982c0c540310200c0c5089039105500c80c030481001903c6405a0112850940c107419120716613955600d0343c80c003801103c801e110030404005194150207806024900b0b460b4032620003c00c6c00d0030200415443c1c00c41140504002151030342400100c05006181c0c00c041064140c0b030251615035500b0b05407041c800c039074800e10f800300000040007150a41c0804c010303c003038200302400d9000342c0c071160100c003141d0b9038204500c00b16122a810510920b0448050046944240c4003030f407038141d2501100090360440c8404401140b600c10505c03c042006000800140c11805d035840180074680c08006c007022001c6001c000d50f01420b04125640754400d1048500d03100c0003809100140820a040394028500c05440001c02c91411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 51081640 1250 51080390 51080413
    0x60f0708060604091802060c0102070201270e0411060301090b131103010b070609020d03030606080a020702030c040504060f050c0c070f0e070e061204030503010e090a0308071d0307080a05 82
    0x54100c103010314400390400b424642012100802814041c10078400d6442001d181c00040c0d07503413402003485000400001da12100c15200150110369030254140f800300d02054001e0b86000c07c00c181808803071032a00c1140564a990070300c881007840d401200ca0300310500000128a941d50780c2c010321600f40301603540c0c01c012180c2d080d103c0200d5100048103000c0c444e080004000c04a00e0b44043c01ca29405580005001c041343d40c0003a40740016090103e000c00c0c0c48500801c642508004070302c5c1c4c45401000d0a501e001d655500094407086594182441183c0d254080350501c2071550068003100c040c03000410007814620141c920729080040c1c842d00f5840364210105072062040c600c0c800300c901e40c1f94101501d07252540203940b210340403d0b81c00d0700454140201c00070146061065401540030b41c031020340d01c0d4101203002c40300802c02840085154041080b07400081e0b8030400d1030b039000c0c4580c46c180760117910b03c0720704042480000c0d0f032490b818480c031040450800d60110f8801101307407183c07048035461440f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 51082890 1250 51081640 51081647
    0x612040b061005120412020c060301090f05130503040b18060a0e040b060c070b07170a110714010c02040b0301060f230f03071701060f091e0b0d06090f0203030c060f07 73
    0xb44540c20584c54000404280000c6018501546001c1c0a0042e110b91100a00205500350402d9002600060b20b03400301101d603503544c3c4202c076005401c40803110b8254445460303c41d034910841c030510241d15000110080040340d030403100e00700d2800041c040b607622050351100902603144d030075106200d00d280414031040d42c0752040c121001c0f4000074020f01a80c074a4200441c00f5a00421002c0d10340e0b650141403078400803a0100100550075103512500e9924200b00400c0b4901406a0007000303196032100818640340c0e170080c50522000c0d60480300400d11070078080c04240584800e074020800041d84283c04200f180201d8544040f030b8620010391001c00394030008000810f10a03988060b00341c0c0021a0600074500c00313165103100205408004502d40780d80b401c80c5242009160b02244070160f50f1000b8800b510045040a204003030b120b0b130240a84800e030030006580101c03001e4018681c030340e52551350040040c2100183d044503001000e89071602400c00c1555158030f012190850b50a420800050300c1d0b030700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 51084140 1250 51082890 51082897
    0x70305150a030816380411062107200102030c0a050d0612240606050316120903050c0f0a0812040501150b1c091a060612040b061005 58
    0xc000c01111186165441e044910b500000000400c118244802c4000c10f525843c0ca14a4010002c00c02400ea010301240120b0314500324600201a40324034280004640c51902c070344048041180d40c80d03a662114691407019000104541c0c0d008480d840070803200c4c0760031005c1c51860310000c0d80e9a0441d100c50340d800a0803480110380340c200c80c14041c1700600260380710b940a0320036116480700c0003414645900c15a20981c00e500c40450340e001040c034840e03952110000100d5000c0d10600014400182081e501030420301006200c1440300251030450300d4034900c03d43e1840a840700d552030070022410300782002016644203200080180c0b0406426010040d00018030180d91360300005500d040201d40740300d45c40d034540080e105580c95034950048001c10101502d0351001025405210380c0d40d000784500b00200304080d900615441031600c0a000c02050075110150100f003c0c0002402c0290f90301d20015981d0300418a0b1101c824504104010800a94800c1e06010b0038003154851801c80400d4801c440310320 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 51085390 1250 51084140 51084181
    0x140408100506010c0602030c0702120303060f010f09030804090b030c03160603022b050604061205060c03071b06020d06050406030807150b03010f020403020f0108091b0411040905070305 81
    0x1408800d0820308428658031568010105150030115003910380c84000030782e04180c0d0510002c11740040c40404601d0482040c4654001c88400785040d450010b00003400c440e65841ca13141484540700d65920340714407034581c0c14040c507800407003542c0342d94580c04408020320418600034041d00c260010303140c1710f150004110b15042c1810080241060030180308030044d4104c00044102e03084080c92030100c00700035003480050580030240009052a01c0000c02060380c00c4c41e403115069480c41c00d4410049140422419070150404410725a80d403600e0004882c0c0a100d1807540d43c00c00700c091001820054650020440000c04000c1440540c0e152810002241d5552200a10112040043d480003c6a400880a0a150f1900f000403506160000b0900b901c104009401d056540050148114a048460031040c55400c1c40d1002203413501040c0d0350390b80d160000c084042c0c81d0417035200d6070342c2e655a50418117071506c495240c940c03501e070b85009103030141a0603500d03440030034245000121014210701c81420042c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 51086640 1250 51085390 51085393
    0x90510060305100209031002030118050c09060708160f050f0f01020909040f021201020d0e100b150c01090f08030412030902010f030f1104030f0b0106050a0c060e030c01060b0a140408 80
    0x1400f400400b5000354480141550107010307000741c8503251251480614002c0101181c502c0f101d1500742070700c10407a10020110b900b0f40500317000d090b065072982c4058450340c039444481c5903a01c00c21a00c09880f0400f040d5401006000a0440041006400b00f40741c00c080c81000211605400d481903403a00740e00988500603084214a40000c0200e0b00580c80d0381503c038005070041c0000204140180d0076a40010000c2a113070380c84d0a003c05020a040100134400704080400b00100070124001400074428000410400390020031001907019003980960070940d4401842040500d003440c05400f55003040314190780140c1c51202c402e80c464003e004001314258165200d00501c040708a05074001c0ca0b543d10500d19803913540004000d00800100108007541c020300c2c410301107003c075203011400e41405800203010800d042c0071703005403e60091507021542da840301c0d0104d21075840205051850081d000300c3c0d4100c1d82000e5000542030440c000504501c03046d036441248140f8038101e0361845114610480d140d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 51087890 1250 51086640 51086653
    0x30f0219030e0409050607031d0c18180102070303050a0605010f0e0103020f1204051005091b04091509140708070e18031e13090603080a08041b09090510060305 70
    0x280c0b142150404058005200050051480e02c80300c0c9040d2045681c800440e03990504545c80e0081181d0320624940d001c00103100d09001500400c06101191048000b40c68504011a45206680700260701c1107042c04000c5440d0b102c40e04005000c1c100a84248454528010010595500ca0301407011190a1a2240100f08a07500d004500a501140301c1c4000c0d404103201585413516600301084c041d50090000748068100b040f032480491740041c100b031006c0d900444440c0b607110145c0700540c440d020b00720f600084944d1181007602c50b174041550344080551400390310780c08200c00c00c14011440c00b4030390211185103072125a0b542c2d8071603650061004030720310f400018020b0080082d00c064060395a1054908100c5503803885007010360140c5250a9154000c1040c40d50500b07106031140007414028024031240d031451300d0340c1e0014855076804104200d122000a4180f00341200d280070540c007151500c0c0082541d40e160240201000142100c580c001c01e8090203202c80540550015a0740000140c0003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 51089140 1250 51087890 51087893
    0xd05010603060f110304140102040f0810060603020c0601030f020d150e06062403060a0b070c030308090115030f1703091005060303030603070e15041b02010e010c090605070201030b0901060201020403030f0219 91
    0x7c07070b80d40081113200ca990208070100300400028803000007011080b000f411200c54241d4203806448880c0c01c08010184140030b81c0007401e4001034801d044130340003200209024518004625103072078410703019050000310300300f2901c1d00790705500c007400d203221320342c182d40300394513000c0c100700c3c44502602003618182855803103000002d4a0200640e00840c0003440902905c0e9501851241138000080964240812206c10002c0c50f4211101991110441c0000c00554070941c02c0140c140758980000b604900000804908120000f50454031050500c0d41c466105e107050403c01c0d580341d0f150300381660b4050404012410505000060301d00440c0004d000c0c0090a0600152000c074000080480ca108406003460701c6681d12039226180c10701801c610007248031b400102c0c0103806d40b680c0550304101a8909400c4006960b8062007010075502545032080d40c0e200c9a0004134060441c0c44c0da03042e0301c00c24031070001620310340544c001e2045038400e07101d031030030940c038201c00344c0c3c99450740e110100b00c9c070300c41c1c4100c0710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 51090390 1250 51089140 51089153
    0x2011b050304140d02090103030302120f010308070f031107090605191d0613050c03040c05030d0909150f0f050102120c0309060304150903021605031b1507020d05010603060f110304 79
    0x141c00c020f010340352080082c60780d00062440102a401a00802d48c0080d0004008581c651251741c003400d0720755001129451a03440c40041d01c251700c800307010189003406400416104240303451040100c00112560f641e15440208003d00c06441010300c01c1001d020031204800303281400f0412140d00160007542d594401070030f582c42c01c3d001400a648001e4180c2c108089035141e105480c0a202d2107104241c89107850310301300b00190303815085180300e988180c2003001400d5106c0307100c00070b95440c42c1001c2100c0000491080c280615508044a10308030071b04042100c1c081c001e50f240440e00240e084601600845c20740040600c0fa03000c03c4811a0030400c000e0340705040c03000c0216013192244003000e042080740401030302100c0030000d048006030044140703048100390304a0160050501100500410310000c0300d0800301c8a40000854040e00d60a800e040032020b0020a5a40540e0050121981c03c0050f1801e10700801050004490740d6241108c1c0803400324062042c0032205d0144095140b40d5110364a0701e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 51091640 1250 51090390 51090419
    0xb070f110c04090201030b150c0c011106070f020f120c06060906150c071d06090901020a020705041104080111030a15030201052b020d0209010e0409030c081b060c040302011b050304 79
    0x51781816210703031101140b500c481c408a01100b80001c81580c4a142d603086460602080302001c0d41000000b42d04c10400c0b00c404514140c014005040280e440300520300141e0a104480300320a0032800b550000407140c00550000b8040140c6600c06d4450f07564680040000440e0180d464580080342551050302c101404802001441c541004a82d880c5a80d0000348000809000405442e0794810303050082c181808a00b403a00b00d40554000d50800803202e20095a4419038070405200d140c0ba401300120582c4034000b102c01410000b40288100c40c00400000c05a610581e0b0b82c1e4007841c5008136091403009040d01440a40c0c0d4169101c0345846140b07030f6149000b46400804151186200401d20201b036010700c014074100207000310250316120b0020025025100e0006118000c41c24070f8080d400196224003036080491748810803a0310343d034502c54916445282d044041c1d0f65403144905200403144540c029104a80c400d0b070310301c42000b988102c040d200001042004005a000782f005100e55201d070f0528 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 51092890 1250 51091640 51091643
    0x170303160e030601090f050709030206030604020a0504090509030705070f0b340302010501050f0103020c0a060507120606020a290c03060f03060109050106090e040506071404120b070f110c0409 84
    0x141e504498030700700181c141002a801448a980e9503501080c881c4a035005269020103141020300c43d01e45542c000c90050300c0700501d140e120b2079001410048450268041d81d01600b5201010410f6141c20034205d42d0f00d034825030064595200f448000500310b0740e05030700d08042d240004072007400c041c2c0744400c102030b203000f2551a1001c0e045040860400c924079484012100e4060360011440703524000c1480911100c06141904042c010007010800050000d101103600d68405070000301030b41c40c8201101c20740e4904d40c0c51891107080500000d2441c1c1d00248101c0814000c04d0090301000c0355008510403c0304d0581c444540b50248000140800e003108065a4082c00107070080c210100c80d9000242080800d820084041d0f03a50700040c0a00c541c881c1804024129030440422507060542f9900d0b07544400615100400c00110203800c2c40700d850809440040000c0060804600b89500c2c254441c00000c44951000401ca04010500380744124172502100808401600d400b030040700a100142c101c0980 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 51094140 1250 51092890 51092897
    0x80a030507091701090b01080c0109120812090a060605010318020111030904020d140705040305070e060a050a0603020a020c010201020a0c1112070b03070e01020309090601081f0803120117030316 85
    0x1400290500b400820f10304000d1100000501d01901c0e10b448046100b060700140c015a016400c16107071130343c002e1224425945422191040400c141c5040c0c00d851146aa031401c403100d1399800d1020300ba20000d4000c00c001d100b003509004a9484000450858070202c04420308c03810303c100200d001d540a8008505032500c090280c9243c00031810106041e40c2c0311140800210b5502c0b014521103280c501e80f0310760454000d1402c6480d061850b00c5099030b03020a40291155201c0c41c00104101e0303520041010028a070281664004654503180a002504400c0005015000e41000040c0c20361043c400c40d140d2000c203846100040c2c60b56103030185d600d54007481864100c2c001d88840140c8a20400800000704454a00ba6a403450b081e900105000c0d003201c2d080781075600901a2700c200d036503090391296100d1001c0c68601c1d05540c07561003001441c0440c100b600c41c103034080c5601042e0304002000034070a20b50362160710041641d0b107075000031896400c2d020b45600b0341c200f400410341041691402c005010a2444d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 51095390 1250 51094140 51094157
    0x3080703020127030809030a090b0a030e0106060305060f0109080d0e18040b07090b040e01150203071505060a0803180d140706120c080906010302040f020403081b1603080a030507 78
    0x103280c0030f03407410690b029050102801d01c0542c00c0591081519074080c000e08051410204079202c0034000540328011400310303410219408840030b119070f101404440064000380500c40c0c0d84c0802400908003a0fa07058016542c0041813101c95008182d21021100010300404002c1c0f548542200d05d081d4050902e40e00040081d5541ca030305c5110f900090165003e0360382403255043c400307409806104250b01c0701c00c0340481804100210130360f001420741101c42101b0200010140450100c3c01e620030048001c201214401c50307074161400c140e004500c0b0392015034581001c0c6403204221982d80c000c101002001814a90010000b4245401090343c05441a02d2408254201c2da40342c1d4205989030b0030440020f601c1441c00070381020709000342d901c0900941050383d40350034249113035a260041404040d000d03035203440f403082911505504031070095401418540d1a40c040450884400240590322201440303401000403a81c40c0030400c1c0800c0381d0b40a0300c0285044400318043c0d014000003400f0030300744103000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 51096640 1250 51095390 51095411
    0x1060f2d080a15080f010506030a050307110a031b0e010b09030714060403140607031802010e090711030a120e030c0a0b0a0902060a0309021e01091e050607050a030806040209060301030807030201 85
    0x400d503040283c80300c1c030054120305c00d0100c5560708440c0d0081070340d03100340c0c800ea0540d000301c1c1c008011125a250425020000b20300b25030040380d0740081c1540003c4c44090905c500f1030000342a070320701c070064500041c1040c525903611140c01d01907018002c0420b504d500041402c10500c2540c0c42c240400582c00b911190a203992621500e00702600c00c55080c850303070402c1e01000111645441a003954912007041102e9010103900000c0c01341820004241c0070311030b00c01c0841c980a000c0d42c0581034180034032049036030714031044500a20010f085081c2c01c2a1074100300025424540100544241c0d0100c4030051499002c0382d281c81e13203000b1018080c0c21a5503034440000c03001d6103816000f041d00749000c7c0c801040704001c1e0720520030100c03007600d105409003090040b5070350560ba0091944085880c001d000c0400a000c3d500749609040c8a580410783c024000116101003013800b20700c105a180c004d0312503000581d1000140801d0340b069403001640b040c030400c01400010541000390019600902c0005400c01c1c0a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 51097890 1250 51096640 51096671
    0x60e031018030207060309110603180706030605010e0a081515092d01140f06120405060115020102040b0415030b0901170d020102070b0402091b0301060f2d080a 70
    0x8541c580902210824105014941c04024030ba000b01795500d030030031001e0415220781220302c819032000c6108034400004140500060601136548002c1034081e01c081c15602c3e1000f8000f85014401c07640070405600807401603140941c14a0b040340c0e4000b0103041000324501042145040007441e62901c58001200004540c072800d1b0050f101f0409491940c02d440823410b030302c2c818100006c042061207400b00e40103012017500744464a011481c10345480c88200040700c0000d03032070700030110302440030064002000140000090300780c0c101c1c0e03080380c00f142140e810220204e00b80c1c8202c0c003d8426243c0200410044080802d100c280c0041891400045038040b200000705400020303800802a142c060620355810704003403110b518100700900085140520981d1508030f155002400640f00315030220000d003903040304c504030440301d841c0820001d50b25a1904000391010788d085c0c0604000031940d80c00c103400001c0d800b400c0130424a2211114403520350740c1000b00c2c1d2101d401442c503683c003a1240c9154411004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 51099140 1250 51097890 51097901
    0x3130303080106030615020a12030204030203150103060b0303030115050f0c01021303030216210519060207030305010e0705031306020f0408070302090703180b270c040e03040f060e0310 81
    0x42541c40c4186545405030050030740d13080c5e401109040c007000c0c2d03203050155000980310712155442041a04800404002a0005c1c0100c0d030003c0d4045c06800d0321a61042004d24440b816070380f00704803c00408500d6010f043c0c0c0e0b0f010074010401c107000540f440c020514043c0c0c014080c0b4240d000d201a1600182c0c408881c2681c0050050271100c0a032044280708168051201814480200a0810200c0d1800d80f104081b41101c07101514048010741c40c0c042404828003100640e024000054010f031380e114035002c0020350004805800081c681400411805a060a0140521031964640342552100032021150610007002221691341c02c1041c6032180d0f4088001d403000304005400b40000c40c1c0b81d40144001d8150040c004001c16140403c1c0f124980c081c84031a6690b00d40000f42c3c50307404c0d47c5100503032070401c00c180d82c0b8001c440c80c01c10b0440c581100010f4003e50701c090545061014481c0f0040e0703d6524000d40c007a040c0c000b4a001d1007801813a01c0f030b030f880f14907418002f82241c80030343c00558154110744 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 51100390 1250 51099140 51099143
    0x8010e0f060409020a06080423070603020f04081606320c070e010b0a030509060c031305010b061b0c09010602060a0b030c1003020301150e1302090607170a03060b210405031303 77
    0x8047e04104402e028031008003009500c407001c880c01092541c0524551101ca42d4007400e42450350200310b20344035004010940e00580228403c541c0d84254080540340c41211a06c03400000030110032010240344400030000900b6005512070b0800250404149400364011a100c84942e100e40e400000d6054401d03811301c2d00800d00400110b6903020540801400e40700003d00022041e401701c0140105075039004122680144010440341e44558580703400c50160207401c1842da4030210101c2d980f540003c003100001c0c12280c00b40112000c1c4520002848840b0600744104809a0013210024001045582020a02402c000c0580b014038001e2400038105036034040300480000d074040300600100050081501050b0282d00b080c840503504070000842040301000c0c4804c9150300401c0c1c146454031004140d5104541c05294280e46101c0c4907054644c0f07800001c001c1d80060308214002840001400485605040d0382c1e03031160710508044548441c800024108a4a81c84104421301c00000c2d628102000f45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 51101640 1250 51100390 51100397
    0x21309081908040215070f06050a0605011b0f150e1504030e0a030b16200a020a05040b091501050705160501020601060e220f060801090204050708010e0f060409020a06 73
    0x116001c08aa0448410340c000300020b00c8400c01c107000240e51244030804240101078903165503040d8601d0105040420040010000c506103814003c4003000e5411802c1903c03002c0c3d95800010744000c507a0004400303142c101410306c03640ca0500c50042100c1549220b1070035620b40c008680c4400041a05280610100201c1401c42203d002d200c2050750181349181100d41c1200c0004002c0c1c02c43c3c0f9402002c80f0060181e001741c0b500074403070400c440c0c000c0c12a20002e041c1d01c69016072903001422403944803031040c50106d218003002000401c42d4038140c82030201d020320191502103180e44141021240440a609050521105000c0c1000168041010446460310b46850b0729819181a0003e4030703240060304054240100685000c05070348030040c0c0010290000100800d2000070300103117400400c0ca080000e5440d5090000201e05000150001c1682c1c41c400e5a04000a45c0d403442d080ba0002c5017130250559400c0007101281c0c4041124180c9500440c2c014030000d500001580016a0b04d1030342d43c032182c0130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 51102890 1250 51101640 51101647
    0x30304060507110906010519020705180406060b1309020d0b040203010f031401020a05070809120f010e0f0601030512030a02271e010516050304030203010e0618030703050901080402130908 82
    0x30400c2401030f8401090094071401d600d41002130018100f806110541113070143c8903002140218400c020307035001840007078901d0500381501c280f900368000c42150192207407401c10b03c0c001103610880d01141c2a01c000d00c0b0401001c14141914000a0740c8600584408691501411074050f0ba50b0f2000314020200070a000354039614610b44010f105da40d03010303d48420f910500843d80125000b0007129502588601c000d96220310160008910700a030740c24200306e520810101c01c00d210310551180d852003007c0703801ca800039003814102d44d64459003404003c003e07410066400a502c504600559000b030809103000d17050207044c2042041900d9691108401c444001c0c045009506240100c90b8462030030744140d50b685000503001034054419800786c0000c1001015100040c45400d001340c2d400783da8000c0091081d460262400f640d183c0e0151a1008244a1080c0001d103e50000040721801c81e45034803020b081c2455500155a030b6080208181c0c1c0044446144e50b40c504814401ca18850f80b0441082e0346 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 51104140 1250 51102890 51102893
    0x1020315030d030204030807060203041b03060203091e0c100504080307080a092c060d0204050a0b01140310060f0309050d020a050c01090803120403030e10061401030225020f030304060507 82
    0x10b8000500c80100034103204000034000720307014170102c5a28580110700982c0d40c1d00d40346080c80100c0204500d484815000850100c200f0542e0740040d4080c0300e4130003c440f102c22850100d02201e1824401d1001c446c1d228440b54025810080b034006a28051424001c2c04e182d510680d4078215440071034201c948000c00509000c0054106449102a041180705180d00f030322a0104020b46107000c55030042c82481c1c000c00a480d80d514661980c20565000d4400d0040781091820b4801070103000008a02040000300038592488116050744d1041c540784d0440101145004001d441c0c1800c400300c00d508043e261800d40010032810094503014071455401032046004500b466403d090007044854100300130340e2410010b080000060f02e0000045c00070404094455181c1500141071542500001340500720041c055511294880e04c21110705090f0340c0001500d0300011001c1340318100200d001c0c6c0a00345403030042c11a00741084002688044c1202d00f11840c40000a440e40e0069841240081e600040c1c410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 51105390 1250 51104140 51104143
    0x15090a032604060806010e030313240e010f03090507030b040302060f01080102090f01050d0212130b130f060c090504020f040f0504020703050405010f140a030b090f04020f0105090a080102031503 85
    0x400c6100d00310900740c2050300f058801001c05402410190400c0004030450751240e809000701c4541403200420901006d50340c80c11460481c10401c0c6603055505030144522a06009102e64004030340140c0d60000098043e81041d4001c0850400c256180d102c0d0316000b000241141c1007043c0200e000390010442d52030801407541c0c1c8040c05030041d0301280d00500101032107450f001d009054101013401e1180d11030180707003e040300138091800c035035603090790603000c5c05020b80b041082c03844442d020314600c032441c1e5114141e2800744442e002d0b00603c500706400d61980403594550164119596518060003100ea540300004d060746c100402540320317460009020081000101d148034000d240c00e0390207504158407a1009491030259101d0b00381448000c845940545114584444418110599484e124200fa00d0010300502d0303090100340c0035030012008903000e04000c6011512559000b4528014a904000112401d80010040d950804900c04012442402c2800650710070702e5810f40e9204400c00300310805 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 51106640 1250 51105390 51105443
    0x7030b070309050c030c030c01030e10050406140705031003080918070206090106061103120c0c070b0306010801050f130f0b04060311100804150c140a02010b0a08010b0a030215090a03 80
    0x55101e5806040c51901d1b5840102c1c503070840740401d0900151790401300c0c46260401c9500086c420300306140c2401c1104100303156010749090200550302d6410380c5c1c4e4201080d1280c0c4070a4407441007080d40352404000242a950040c02043c3c0060b1000ca880c46103480411010002034801e200503800082c10000e07004000d105420092100d4900031440c038407100e480549a120750325160b050122102c1c0005d003218444421a468540310404968056a5030084110150001e4502500042a15000141c20303e4000000c0000a6009080405803400400d4100060020308450400b83c5d0b26401e03140c3d802c0e0b07120311540000b1809107044085181c503080c00c200d0750700c0c09440c14400f880b107014107010214504844040765400d24090028035060300920681d84080310844c01840813100180110781c2503419000005200305c2179038200c08640c0c4440180d800e039442d1700b01c900d0304a02042e104001516156030000321070801001158a0b0040044c041488a24540c1081d5000c00482907c2e59000e585903118 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 51107890 1250 51106640 51106663
    0xc09050903070206090613030b09030d0c080108190303111b07120c150207090204060e010e0105210a0e070305030a0e030c0a1401020f1c0201150302060301030b0907030b07030905 78
    0x654030341210b580c00034040d401407014050082c0742c0458001000f07900240042c01071070300100340100720f113401000030ba40d035030160148880c01400c00796140c401c0b60186400c90b05840c81a405403821b001c014100c81039405041e5019420551640915424009220010320507842d09044501099101d42c0607103182200c07513803000001404442102c0302003141c0400178400e441038181202200c09410104a1a0410a070442d07a8028070000d0700062180d00103d01d03c048500030f0700c5010a5610210065815000b0042001c0c9004d44041c80140981e108983e9550b2005808000040703802d034215541e0b2406129420480300c945c0300145000f038851b0808441c0c200c0c00c40850081c0b40c04c1031403501013200805c962141820b1100c0190010005a00030711000410010810444013540407941c0e4200c06046010b14140242d481c0010717008003456403076000e5081ea90064180c1d45107034030719a20079562007002030601c0d02d00d0244000200c0062060719985000300b41ca96004a111461424103504000c1600003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 51109140 1250 51107890 51107893
    0x30a0801080a0f0807030201020f0f0406080603060907060e011e080105090a060302130f0207020d050606010929031305010905010506090603010c090603050705090301090b0a0c05030108030306040b060706090c090509 94
    0x92000003609034007011060f544d01102c0e054031040c0520b800d038060f0103041035a01c400c0c600803507071111081215001d002158400d5489d0900754071100c050640724003042c4d0f2441082c0d00940d4003070202c43e001c1c0d2049144010103141002031803090700c3d4088480305001e15038200042e00071004120918040c607500341c000a45c90742c1004810b14542c00900c80141500380a01a0350b107030041e21911001c60350541d05920f03005807a4101410b6207191076920380c201126180d02213401c40390041030302c0c030002001140321042182c200071042c24650048569800050890081c408841c00b4640012070078050404001e00c02d000104441c1402c908103c00150010100d074001c1c3e260955020206034000324110131500d107030a00080640390303840100c1706e41c4240b10001e5019030a01128004119408401c28490403092800308030300ca0100008a03000e21003803040c01d41e658410300110790b0f00c0c58a80d105540d03850008044520b800800c0d40c4a03000e4502c0b44c0001c0d607040d19445802c00551f01d041c000c0550000f1585e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 51110390 1250 51109140 51109153
    0x512071409130b0c0403020613030506011a160c050a080c0306070e031507030b030714030c0303031b090307150c020a06090506040306050a0209040203011205010c180603200309030a080108 82
    0x603014001940b420805402e101004004c0340750415040102c0c0d0146401910b0b4942d20f20000840e0414050284021031700c507c1040000102c880710840c1d0f09454080481c0c2e03141c9803020700340360300c060301c0d41c007080540e40400001c00010301c1d0b640b0410460014608203010f4803100c40040c00709814254024003003c107200102c1d0582205507400315080c03032480c00d54038000441c0d45640c0c0e8100c0081000c4200c1036058481d1040120710b140c200011546040d0045003150403002c40d22003815200d010544074065007451800482d20b000d62040060804580e0203411582c840e0340d100851030380c100202c18144041102680d03907405504140b03001d900074009038200404260f1400000c01c10502c076910001e000f0301d42d82e60124100105503011248407410003007081d0b44a51310754012250b101403541c400c43d880d41c0b900724010715040c020b12241c2c201482c02e200c1c00b600c4614241096001c1d090b03000650813156107044800c0c005031076000c05140114515001583c8078505120040c1803104180c01022450380f021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 51111640 1250 51110390 51110401
    0x9080c01080c0406120b2101061217070515010e090606010309030503060409030306050a08071d0108070603020c010b090f060a0605031603020c07080307060b1f02061f0512071409 78
    0xd4111021121149005c0300345d08400622a40184001c80e10583c1c0051540c1c00c00d840f00441c074108804d0f0f41c0c1284001c20030207690714000a01001e0103200240042d440c603084951110703400340503040042c094400c1e07508071441421000d0301c12000360080001a400f880c1400019501000060342c0560282402c11800005460141043c04010689841769132907901d4401018803940212005107009082070a50340d8503081d400c0d44514141c0100381d0308602a8213007541104128005a0481e42804c4c0644152400e00300110003a41c44203e0721340040d901c411200c4550340711145030f1445000b016000940070704140c0c082140c50340389944082d0800005005002c403100580200300240703002d40c100180d5440c0484078044c01c0080c00c0d404060980808a00711082c06502e030400c000c03801c01142e1807505e60084140f1800c1c4200c51484400c0140d00c4200003e002c134500000c040e500f20f0181c00b02d40e5165070760b0380c00100d10072090107011086410010301080380c4901c14000407120141203600e40c00c0780c50407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 51112890 1250 51111640 51111661
    0x406062102090702210a030506100c0201030902012010050705070317071107060e1804030f0e0f060408011e0b010c1b1503022206230d090309080c0108 66
    0x2400c030064032a0540e01c000c01c40450007000704051007403031a11402e002010700f090b12882d42d0030801030003002c682801c00003000c03403a16074006500001162074450140056030011002413000b01012414412004c035294515250ba00201c2214520807009181c01b4926502e50416280003820500038020309000480020381c00811014101c0a055601c03c59a0354076441152944038241c01032225000b030000208040780d004020b001c45102c1503035440e9203125100e227007208604040b50f020300000c00d0040f03042d108601c02c2884812184c0e008004204030618100012400c0d0700590000e081a03550364a0202d101500c50082d0b0f54021b6043e00411409404600180c030317505110100900401c100803420644120500618010b06115006034010000000001d0000d50020188a02807070786d4076248042040e02e545c0350801d0307c90380e0f95012a0310403034070390100045a108251381c1c01d41c034080c480802500c06612402c8840c2c1d000360fa4080c2d0140c9095007641c02d04a1440d001030400456070100f2820001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 51114140 1250 51112890 51112949
    0x60509030d050702030325110a030b010509060102071505070c0902040b0304020105070f0c030c030201170108030a0c0c0e0717070c0b0708070e0306071805060301050a0302010804051501030803040606 87
    0x101c504116075101c4072480028218495070000746001d5130240f41c00c60043d0310751104c99005038030980c0d00d1404134800c1420400c1d42c400b00e1100601d0a04018014419802c08410468102c00d044c012119540c0c0c882c070701c0c070f01e205035215400701c0065004610710080c09807440c03d40004002c820001c518040c204010b4180038400100060305000c00006c841d0100a180300e042100a50800066001e140e02c9140401d0302e401548416400a0860381d072108206203c0c01780d50b412a540d100040d03141007454403054510000310b82c000d4034009150000025a1031705001c00d5031190a06654481141200c1c5001c1b02c204140980080c08000415881d200060120a5000d40204442c10314250301e65803090304852041e51491455010b000348000e02882c1c50708808901165121581810865070b100c40500085001c00d100b8182d00016000c13040001d035003d4541e80d0b400501035401c0e1102d1040a1048040360721080c0d108580c1048000200001d114852013241c0c050410b400c610740400780f03401c003c80c40062 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 51115390 1250 51114140 51114163
    0x7061107050906060d020f04090c050310050f0102030c0102040f0f21021c0f14280602030c0f07080d0b0906091b0c010e030903010515090703020a0306090207050105070906050903 78
    0x1c011000f00380c20381d49000903113500100012081d55205000c12945c040d0760058801c60001d141490243c0b0001c3c4d0081c400da0344240740e10800c00c1122443c0c0000c004070029062030f41030650008010400b0490300a00003400030304421141c251145d80340030070321183c0540b03030ba1040b1912001c264004d290740341090241d500107a0102c0d41c180b081214103006180898015000404020003140140200490a000c0b04914906602a0b81322151000300311a03e01002c000700c0307401d421903280da101c000f035007903400f55820a4550a0060900c02503203070f03456495210410a8541035000b00391060035111034002c1458480003903800c00340604142c0040303084150041d2220340e034403046000c046104500401945c003480300c140001d002501071108415225070000038100d0085d403c00c40000c070241e2800c90b01c6001c4803c094107a000c0c0341c0d905e0300202e00030340102e030200c001c01d91a075100150510607070018000c10b9004100000311341c1400f40d0b019106407441d078411001d1000c180541c1d022540c012a5405440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 51116640 1250 51115390 51115399
    0x115080406020409050108011a030d0c0b090307050604080403051b0105042603041701050f0705030c0310030f0818030d0912020307030c030506010305070b16060c110a05010e0706110705 81
    0x9844515021020f0300444d000040c1441c038000001807194015004143c0c2d00082c02c80d030300040300e05101450f4441005400101c0410700d0080d819000602ca00d03442e03544607507100e0680341458516a25103003020815101590b031640045014002d1100c103012843d8040f40c0c00e4070b01c80c0d0600b08040044d1550050748600d14400d89608510462000b11103c1341180a1101060303076656070b04d88102d141e00c0c2d61b10001c0a40315620b0040090100c0a000303020902410a58070381905640d80c21101c0e55441c0d00040803801210001580000003a0090309210300789841908040e440c2c0c5911409002404080128544254008160300c2003481d00043c1007411f0703072610305114154450070b00109140500300d0303000419074400c042c0000305020010881c039040ea4890340a56404994550101d440382c041c001c0800700e1080705402e00fa00080c2c15920020341c2c21410305001410721102c5468070b007048462001503170719035101c229009401500340a15400303801707542003500d17980c1c00703590a083e601c11030780c081e42e4081e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 51117890 1250 51116640 51116657
    0x2090f0601020a1515080a0c03060b0d05060c030708130b0105040e0c090c0703030501050105030c1801031806060303200a1509050714010206010504050c0316110102120f0a050115 78
    0x1a44248911102a6040610039000c0408540e06200401e00d00b10500306407110710760007155680b401f06402404940058210829130705640383c00008110f013100d4143e0103050840803000041c003e2014074400c0c00407000023916454140c0000e01242401030501581c11017601800001038031900c40b01c0c1c15210165000100c1d800013078691460499403411043c0c1c03110303461003003004505152000b4802d8034880d90301031000d6681c61b001591203000503210310084603400e118112030b0350703211000301c917000304145801300e041c04846900ca00300000e001e400b55070050b1115014800c0c1508180d1940c5441c08015241900414000003140c540352107000080800c1401c2c082e00600c0f40282d0800e664258101c4162034010351303142688100c1090f200c180c43c0c0580241000042c5a15041c81140c3c824200307010018615559030b0143c0f15811000c1d1250700501c4a08215142ea5400900c05003050600103203115900d814440ba8000128000070032007540b181c1040014000300345000104032100e500ca00f4010310 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 51119140 1250 51117890 51117901
    0x3060b1611060408011a0a0609060801090c02010f05040b04020a06050f0703050304050a021f020115050105220905090a060e280809030d0e01031a01020304180b030703050f061302090f 80
    0x441e210784e90016083d50b00740303100c102145d00c50801c0070280c2e00c01180e03d041007039500c00d42030314119164800da20229011000400903464180c0001c00e01925a100001d60071800d012180c04850050710155210403e0b00100300860414030640005081d650400c4d80c10701144000c0e4801d81d2141e04001420080003101003401c2103010042200da090b4010408282e00b45001e1450003c408030700c2c80c80c00151301b1310303002441c1c2e5081030b101c8070160341341a5906468060300e000307880195082030907a1941c507024081c00150000d00362180714011a00d01010b8001c5840509014003607585d0080720268039007201034001d071061400002031941130100307030b140880c0c80440c0c01c0824582c010307100e8030754150061407545441164011551000680262800c00540803e02c07000e10f000000500c405016030300c200403d06c81c1800001100b038002040c031304085003021080e0040703400d02a5030b5208480660024910906203201800407030b5000074184102500d020460300010442c10000d1f00c0b8101440c91900442c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 51120390 1250 51119140 51119149
    0xd1107030f06050402100e030d05031f0801061d01050a15120207030206180a0b07110102040302040603060203010f0e09060a0c12050411010806010c081209030415020a020103060b1611 80
    0x554000025003450721480c14201c02610301110308900c50780380345800040440c0203080000d00480c02030000c040176900990151250b5001800b41000750301001820342c0c003c62a004500b02806804002148181c0b90119280840314134658040c01c1304c15181c0144040d0320b850003400700316521000c01c40b00314164028169104031841c1010440d0b280001260802c1c550000754050103003850340000030521100282c8191661000400102403584140109001c1c1c1d1045070030002c040945000140381c10780d44d900060403034801d940201e654507004401040800c1d2101d8071500200481c601c0c500b01442c0100c200c548941c4010030f10f941d070304d55135000e86103890b1141000e00360444011104221a051500340030300001c01c618040d030700041e0f0308000200a54428105070301021350141055050962004c410200c040006103040d05510040c4400209965001c0c15002412143e4001d0300e52021103000040503689603810a40e906c6c402040104400e038140c04075119081d8011300b24000410035a000036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 51121640 1250 51120390 51120403
    0x1109061e041208030402090606040305030304020904060605030f0a060b010f1b08250b07020102160609050c21010513020d0b0403140c01060501030f06060804030f031407030606200d11 80
    0x21110010b49071a008106400000314041c900803501d01d0590303502c1904012141c42540001040c0341c0042c00810010700700300c4080303500b052062002107940398039400468900180f82d00010795591240140c182400502e1141d031404079170a2030203514103020780801400845a014070000c102a80b000d00342c0510103000c042c1c2c0c48000d142e030a01d58007080342240c41c400b034005050040e5003d401940119580d14014421143c000440000080aa603595150b0500801041c131003610703d405154003914266403003994250050a409618504007950300103e00d0131110010481107202c032070355070b44601603a40c0380d207070b80e501d25400014021195100d00d011515014051031b00024888041004d90b8456019082441600e1080e6810800a18075a609100713581c0700e4030400010070200804500070a2040900d109180003e060100e003076001881c1005c020002110000f00207640c411041c030145a0001e14903200f1540f04503143d0483e40e094103656100c81d146680d0405021600307000b48552001446076 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 51122890 1250 51121640 51121649
    0x6040212100906020a020d030b0901210501090609140a0b0115030b0301110c0d03020304020904030305250314070302070c061b080d15080708070b03060109050409151109061e04 77
    0x30b20100101c2e00e0254044d420000301180540a08644602000e2080c4155000000001c00d60f200691905d0125070f41030030107822600c4074022115074803000ca8070034094800741a12603280051084d5081c20288542d0170007002c00041a044070061074046090a24000e046d40d90019a50510f1108604154010f101641d40c01c5e81550a0007840881011108044c0c60355503021400d48100d402c041900714102d20049030000c0d80202041c02190110b0300c0380c0d03c49944a140d02c41010020340c24270a006c2e116075904068a00000d0b1507012000b583c03003081c5103413070b003080442c10150f06101145d540d0244103a65402043c00700070710071000c03490a15684003064480f54102d0a141e6039001c020400001829825030407540100c140e4000064120340001c001c82100e40d0b2201604000b0b0400f1142c3d11141d20191505c0d0420a0603600030410b43d85602c640b5100034070480c2c2c0500d00070004220311041d41c0c45502e9181c500803052095000e84d80b189021142200282d400501d541c20305c04011400074080c9412 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 51124140 1250 51122890 51122923
    0x305130510020a05010b03030703120902040b0d0f0302070509040807031409040207030206100503162c0702030c0111090109030201120e01110c100c090905100512030a0305160206040212 81
    0x11840d901c15004101c0110f964000e100900402481a051558a00c00c01c08000c000400d20003070300307041495940c803209c0c1540c8000c0001c202002820001034800c0040801641c844400c03010003c20140c0401c8000c005043c04d880203841460706440c0c0700703001d001d0420b003d0700380581c0f41250305003820690122940c40720b001348119112040ca00f802903a610b411100072800808608000c9913a15001800e40c040c3c10000e60781035289801d2500c604108101c1c080b03c0d00f400b11000c448110794007041c0c0c4285100b04140d40c000d5840fa8510318400e400c1d211607142101d080345003084940f5860740d1100c416070aa0390207003000280c0000b07071940b800c0201a82d0030000c40070351030310b000905034026110090509504010440f0914100c08404904441403081120f001c1072a9038010000001c01e5013090b070744034480301804107255030348202103501c82513a80c1030030324603400000d038502c004c0340c0500c16550400300c4100c4503035004201905c0a5070303c10001d04041c1c803654070004000c241000404c84400001524803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 51125390 1250 51124140 51124159
    0x30a020307050712020a2706060e090601140d0c020a0b040b01030c060201020c030d090f0501060923010506071b0306090506060103050f150f06070b0c040f15020a03051305 75
    0x4000946a8025030030880c0c050150440c0000d0f44e0010000c01d03804075030001d1409403184d06c0c040100d0030318000116101c1e040d8032092405441d10b000b500c100b1300100915150059100d4410080104581c0003c0c1401e0501107009020f10348010040203541e01c08a44500028644106c5d0310241d1400400050040402c04141d08200401c003140f071040d41286c0c40b03819200d485507181c0c4016800d0303000c1d808504105500a00c10001c517844d1540213a07500c1c600a203d000031502040c1c45140c00c3d11503542044a5040e00c03041c051400720010400401c120444041182d52541442c0000e40284105d0304064914503c1208003080c40303032299901401191b0002e0f04100380aa07034904075403941400c8440901191801001845000140d01c80d13138469200000d003c6001e00c101c1c0104000b010030411230582154050103a0741c000b8011040e6140603024900147d9211441c0005068058205801032400404412441000c1d07540005449208036490308025844940070352007182d07130102c654042c035413025051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 51126640 1250 51125390 51125407
    0x21c0203091f03110307050d110f030901051006030e0303010311040212040c0302011806082e080a0c0518190f05070e03010e010c171005060a0f0e01021212150303 71
    0x103a50310903a900943c40c18020702c00380003103a803440e02045440c440400c0e010040c0703010a080382d03440056260341000b001c42c00e0003c48a98820a81c10840344803d02d07a544100b031050448512a0800003000700b0301d01441f914240803280741e120f020600c002407c500000c420001a5925601564807500400308106101d28050806181c00c20f00f41c030080c0c0c00718100d42c9a00b10461240e0710701c00140d0328151582d001e507071103061800024000108043ca801d142e104042c22107c128080d040000b130002c0d8004100c2da20403400c110700b818407550300c201e00c148000c1e4030750028483d90131400c40e4000b10382e1102e8801c0c958410070340c0010f084140700101e00e5500c2c240801100503004107d0091003581138000b0810105c00f40c200c0c5023220845d18050022415810003e00400c0d1817003100c0c1d9008181d81c1d19041a40c1c2c3d80c0c40852616000920a8404a2006e00d07041030f00301e9018030001030310708091006000042141080b251244280038041103001c22502c0000c03a68146022a02980c80002d4102da0b80c07592135 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 51127890 1250 51126640 51126679
    0x5150d2607030f260114030a0c080106080c04150509040c09020307030204140405010f090207031803050304061707090308070303091205040f050402030609060409020a0f0f0314030703021c020309 85
    0x4030f111074000b08204907425005541c10400441001c40c070500c240500303900300b50075a001221001d240030b92620409011000003254401400000d0000d00000f080716402e101e0030508040001038842e02039840c10b1001e00107018094510b004440303058504030280c1d103da003010354002840750001240b0f103000009214600364581e009004039031410300d03101c211114410400c0244c0d0001c3c4240003688001301c80c01d0100400315401408110b00c2810000a031004440707856460404591060b5403a800c0800c2c1003121940002c0c44280b402c0811500100e41d140c1202c000d8031003c81da001c050000100407c0500806001f580a40c4046030030003070300c80c6d0844001c17500500c0c0e1741c060b0140031290116528002a50308190007544c1c0103180c0144504001c8d6032381814000280400700050740d20805036a000500701000002a4003c1e000d840081c0b404d803800c42c1011048035104860b4402035520412041c40400da0120b2000140310f407900c92420b00a203040381c1240345000f480580759001c0031991418605a20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 51129140 1250 51127890 51127907
    0x180106050d050108012f040e040503090f012d140c0c011d01051215090a090614072102091002030c0105070507021e010201060b0705060a05150d260703 66
    0x41034070248000d0b80c8a00e00c4a00f81c41c0016095209100590983c03401c0107214644880e4540140c210541082d640d40c01c14050420f0a0310180c44a40000400c15050305100b05058a45c1900703003407980500358584410800d9018420700c005000d00541c60046409100700d50007a45500303071002c02a2180084002070740c540716100c200f240070442003112044640c001614400301036a0503101c8070704142a1980d5000c81703040041032010807094141c0c2954066171080c056078000e440c0c1b410001580503091500b40c04965070781c45c180e0a5030600e802008840c6074007161065039041040c4407000c800d10150300c1c54002e4050740d0320156114103d6031802661650000140402c0c0850380300911554a43c800195000c1c030030b0700c001940107660280c5004c100e981001041c0aa01c0c01880001000b555a811171400380d081440200c5040d0860001d008241c4201d0040c140c00202e40781d00350318440d103100e00040c0326140d407000040440010a0a51b49070000c0404c20800b603031100401d2a644030b40500d40100b8004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 51130390 1250 51129140 51129157
    0x61b03140105010305150603040206040503060c03010303080f04150b0d02091302031e1e03040e010b09030d021b0d02010e030604032a03020703080c100603060c091205030304030e18010605 82
    0x120320600015403580f103401014001d50304c4069103c0200304101c14450203a000510603030700018208800182d54030300b002100c0c45542c02c614011340329410f52900030501003001c0c1120000b41440d501f44000300325162900005034030040c034000b41d0101000b001c81c0d40640b982001a51222079202000000200c000c00010214422015902c1b0034010005a54500d450502c1080c16a440003203c1000140b650f00c00a8000005e0742c01c40342000d83d10f0303250b43c24810090f0404c0341c05000210318051541410000465420114000f90801c0000c0303038100188001520b1074144104010b561a005590013619410280c0078060282d441918080c200907000407452030504a80302c3c6605184034030300c442e840c3d50100c030320740c180e0280c40300c94a0b5884900c40c0f40c02031000640c6600841d481c044002720184540e030700961080002046100c5201400740141b1225072201000031a0129424001103001c01102e500c02d40c5400c101d50002c243c0380216101d11030900303c83e41c036030030342a0000c1201e0342c01002400050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 51131640 1250 51130390 51130421
    0xe0d080d0e010e060c07020112020a020a0210030b03280c120c0501260c0408010c03060504060b09010e060a0203040b0703030515060c0d082206050402090a11040b07061b03 75
    0x48141c81c019a0803204655450300c11900010003040442d90890b00500c041801454582c0704401c8061215040b0380c00300e0390000241e40400c660f0021800c040040881ca95403034101042450320100101382c40303018900c070f404514200c515900d0b0b41c41000403605410305070010056521f040e02d8055104203141c000c181a640e4040e141300000b801d62140c41d1551003060300c00030031445009507144886c4400c8000e8645484034205000200d14044248100040032485640120300d0034541002d1008495076034003c8240108108080070b1140d801c03803103407030220500b940c18644c5c8048140c4100d0450049811040200f40005000001c1c5949500694040c244444404c00c5150440d01004047d215450b8550307210740017011143c22049c00f0b10002503000011440c103101c40b400440010404122050f8201c42c03c664403814481035050241240307621203903a0308100122410000c00d80c6840c002c0e4820707603001c400300103010401c121494111030003441a102114080c4004080040e019240b44686400c1c0f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 51132890 1250 51131640 51131651
    0x3050109060f0b07030e0102010b04050f07090e090a0807020414040b0915011a070f0203030a0c0b060307260a02040213050103050604090206031f03051c0207061e080402010e0d080d 79
    0x282c0c00e100000401c589008100034580071166034140c50200c40706040506655035060b40d403c1e951100d0080070701c5401c00500c070000c2464425006001400b80341c0000c40a005c5003420403480c081c000840c40e00540d0040d00d010b4070b854041c030005d8054a044440340007204000c01c117100800c501074200c84e0043d070302542550b0700030000d0307040040345210074880c807052030000300e01102d8041140303001403001c0d0340107070641c1c0d030b4103a01900440d18690000c1e0001740050104904d8600b48140900301c07603000003045000c1d02c0d40034a05565152210f80402031b84c00703221100d14510041c03d804000c80c182c9142d01400c259210300c4148403029007e0118800c050200b41409d0000701e80340f81c54812194081c0d40108030030304544034501642072141f0032046403c0444008a004030100b407080107a01400d50440102c500060799540000782008500c2e400781061007510b9072030348074000201442d03202e030f590146841c034059178076800100c0e01c02620304e0f202604194a80c50f500c0500008000610390101702c0c51043c000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 51134140 1250 51132890 51132899
    0x2010518010b010906030207050a1a07030606020a050606011107180915021e03090c06030a0903200a03080604020d0c0c120e130e0a0b1e07051c050705040807060305010906 75
    0x980382c10319509400a0f504c0041405030030b001e030b0b02a03e990341c0200102c40707449107582d850025510b01540d00880c2c0f000c00307200b00081550b03d80140400340c40d59201030040f05031a40d5441380d546002030403142c140440c0c40f0300309041e14000c11540004101d00112300c8108083c1409000042001d071409641020b400c1e4041014040107008a03240098040006a04020108108100750700f0180c0000014050801110701c940c0e544006980106000580000d807064180742c003820f03074100014a000302c040901d1410181d00d0740440d62680894040c10040c0ba02d6444400040c001c0c42011240e07120a440d10915000141e0301c8078414400ba441261390b691005100d41c000c1d10303644180095564050701042011704801407a41002c910000b100040b00c0030381c0c0d42581c072060640011110120107100541003810300c0c0e44013424054104149052151802330365084603500a01e10500d03032410030b612800031460a610130403c0350010710070f03642541c1c1e01503100c000003406020280b00d150002c2e810a8004139 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 51135390 1250 51134140 51134143
    0x20105010b0901050306010e010201020c01110c07090902210a0206211f06030f1119170709120c0e150103060807050105160c09020307090501080717130f0c0602010518 73
    0x40c0c0b11201615000d0543d0f50b16001115a525007007200e60455409200e640c0505e1401d0186841c1212440b901c1600d030501d4010750392a106031913102c248480c1c1000030030790260321140a0f04081503500800704040504000c8264074000c1003240c021f40145001a0324442909400d070b10340050b62541e45102c1c1103480f182c8500410010300c581001d411a4004020054140a50b10180720105030300c0000c0b407410301038105624a50041c5800c078141010140c0c040d411240c0c09944149212825201154a800e00c03c1c001400e4880360b028460101c4040c0103440d040c458100c44540080c0746841000c8410f19050659480e6000851030f41800700341011000305540c039000c92402c081d00c070103035541d5050881110480703e109800540544030804003840106901c005800158840c00da06c2e00d404a6651624000421460004055004000761181106100704081030701030303044544011a00030501e1541481240100c4511000f80b841c1e00303507500001c4454041d0003441c80780b503440075108041c02050074140e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 51136640 1250 51135390 51135397
    0x5160906020c01230d020a0f05130e1509190b01080402060d05070c05010c230304020907030e190c0305070602071401030f020c0a0c03060f0204050d110f091006020105010b 75
    0x2000580c02000c2c286041e0b520480e010000c440003507408028400280050004940c8a0f0000c0700146800041d8160110b0f00300244110b41259454410301c0d081801076001110401401050040d02c00345011078504070101a594400c040000c0c294143d0381011410840c0c030351039120a022441d810702c403403070740c20758040c1d0111072082c2d0700681f502d8a070610000c503000007864014804428844040c440310702140003480f0300c0301610415100c5031a0350311034801210307050020300c0c0c1e20002802c0410400005172644032403180c20040e5402c0120340721658440d100c0c00c00c0f25404c0d0300184141040055001c0c0100007003203500b200c1c0030700243c40105465030030807a140c07410b60259190f0b421080c0000c0c1002d5200790300c0001d01e03081c0a180141400b080010707840c01c26011703080a64600070700b41c00c11f0007404880c0c0300d010a407001d03840007140b81074584008980c4603014248054004050084000119250401c0c0d2031000c001c024803a4400d842c101101a5107149940a481e0041d8a00740c004608000082c0c01c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 51137890 1250 51136640 51136649
    0x40302010206060f040e06010816270506030c0607051501080303070c17040f06030b031606020c090a0f020304050d180f03151410030212071203050705030f030109051609 74
    0x203800280d0350f62042c07003140180d480c441c5401c070707560324420ba14010b0184030940c040c181d120702030075003420018078400206c1c00a40004031034081d5050755a03140d403008503401051a01c0b10002040554940d4006814003045001498000100150350001c111000c034210046154108443c299640c1703a1114583d00d000032207052020a4111903000301081722103c1103018000301c4000d03140703040c3d220070045011050075449000440d0f110428800703145000e102c200080c4c00014024411146083d80007952440103448c0680200b42e4003010400d400180e40001c400585008802d5540f4245450840c1d614840d102c444000034100c3c50600700104c15040b081c1c0c080360b9810300911030284c1141c0310010040c0ba650003210615a441e050745450440c86881c480c8a0481062995019403540c0148080440a6500c0b1a92038001400500c0654003981d16014000d815203441c64840c4070a01d005450f51048170b210000c000000b00c000102ca2480d90492885440102c0c06405070031040201550b003411240039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 51139140 1250 51137890 51137893
    0x1140c21060919020c010c08070201180507060f02030405043b0a06020f0c010e010b0a08030423010203160b070e0301020909040305031504181b0b04030204021b0102030a060f0b0403020102 82
    0xc180f441d22000038607000c1424400c001480c001c064004e2908542000800b400404c0d002c0b13040050341a020722400801c8400c0400e2805130758180e6451036200c00e49c50151006005c1415103045c072081c8201b003524040c007030150041101c8483d124640c94044180052103440006018070740f151001c01a001c0702d441040a80204904031a641d6590040d4005000c80301240f2024000110900424012111020000300000a10b00000c03014802c2c3d02131107810410080c0e000300300c01c02c02e019902d01004040b6542a03040318000c590303040103e0852140b0005000d00c000c407003003c942405038040410b1301400d40c54a8102400d9598402d06080c0c1c02013405450f0b0058032003002402080c000c0e00119440020840c00701d5a03070f8501d6000a0880c0d141d4505440c1d24184000110100711407000c83d9a807860b00000f10441c554984840e4402c50702c624040280100c0d004030340051550340301402203410f1203400d002507440b45044c0e909000100709610504c3c000712901400051254400030440b015a60180e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 51140390 1250 51139140 51139159
    0x60109030c0315020708070c0305060106030905100c0903080309071e0302090403270905180a170f040e01080604030e0405010503150415112d071401140c2106 69
    0x3c44204051502c1c500c8000f41c40c4c4c0801540c00018460001094400e209441458000d811414214a00390058018400781850020b907171011901c0040d40c00029041c401000c00c0c4020481e10880f0488903c0e40700074428207000c000d1200340d04000c555101074800480c0040624144108561142e188501c0b020750054642800b06000c02c0c843c080c04900d081484010300041c5c0e40e985842446051241c1c4185039031642c83c4240024101410004400010b000005140707141103615007851007605426024030390040024a0804500490290f800800302000d0b220203940c0c1d41d42d11141c45000c00c540c214009119002d24040d0f5152522500d4180c91016005120300c03a1010050101c0d090050f20560381c4203102280a007200000c2c1c0101d4400f58542d0781c465440b5103001c14500107407150107001c00040f15800010248401c0004162a41c09411040401d01580a0100a40100480703100c0420400c001c0040000c8403010100400702c004200c400e001c89005041c00300300551401386c4199912003110b4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 51141640 1250 51140390 51140393
    0x140a030506010e10030903090b0405030c1e030304030309080f010908180301020c070605070201090f03080d0c05070b0403200102030c0409020705030f18270a0509240f060109030c03 79
    0x254400c40d8801d0341070424500d000e01c1c403800180c0e448058804100000e89a40c101000c040c2d0280200c00100003000006051508040010b51140706156205000d56444080c0d0041c410b80a14580001c100c041c2c20359540301d80b0b07030800600c45052030048000d28801e07030120004a250512645084075002a9403030b0412410819000d058001007400c0c07070307042d03400344030340d16643c5418003000c00140303000e44a1170b5031030003144005442c0b00b038254000a01c1c5114540c08001041045007200ca008299043c00951443d1466040c1ca441c028228007600e544550740c100010140c00400040f940700021a00c000500100301c003507030907803201b1628840406000e00c001c000ca48100e402800020f4803e03000d9909020405402007959040000a00074800400034405940d04240488210034105011101d14082070f00a05540ca00d10103094050328a030340c1d00000343e09101c10312241c41c003180300507182c01243c40490600700781c0100070b41e40040039480900200c0d42c55030041d095802241d9005c456080540c0c0355 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 51142890 1250 51141640 51141647
    0xf06010c1e08030114090603070807120201050c0d0f271202040e03030c0a031d0d120e0304061806020d0c060f060b070f0605010605090f09090106051c0b0601140a 71
    0x100ea90401c410700d2425080002a640030061406014148661090030000740b040202e200b2015060fa03009400841c41440621800300d41e01003500c0c000d0780c5100302e442c40d510040320584141e20340c01e9624001d03480583d505903841000615021101d54881d0401d2020391101c01401d00d28148030f00200880341e204001e01d59020070300d44c500500042000602582542000341954021900c034400003a000402000150b01803150882524800303100b0b1007548a804221691031112014a0040c000c3d10a00c0040307204003a0030480b20b00e00701d0415a91217903074440f4040c1218041c4255031841303158003131000c50500e10000e80c0c2c000b40c004070b81c0e404402c0348064551100520950401203525a1201760103c1d482886200a281e079522840c00003041350020309201e411150181c0200040010410502001d0341c1c441d000b020700400100c80022054680c5040d150042c0b020b80d00c543d4001d04001d01e8a071521000d10480c0038083e0080d602d41006039140c0c0c0045481000906000d50700c40b0b0240200c0414510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 51144140 1250 51142890 51142913
    0x80307261b031b06180d0503060103020c0106090c0302070b0c070302030415030905071401020f1203180c0d03080402030d0309051f1d100f05010b0906030405070308070b06090f06010c 80
    0x50303070181ca1400e88240040c034000c96401c1c411440c0b03948201c082c0820400282c20211034109103038040c10411754110700081191101404c454101500403030b43d0400c1c00004e6102c44020f20402d641008058801000079000e074000c0d80381510f011030180002800f602c1400201d42304242d0550195103483d05109645101c4800036003014105603464042c0000145d003004190050701c00701c4101351002a88500091a184096100072000d800c40350112603000340c000241ea8014420f030310020048207028410514155044007840c0e40200255034140c180b60b0080581401240254242c400340d0b5066802901a60b4049034014a247e10a4440d00d0a0a405000024041c415501d01140c0c0c02c0f4040b0740385401c1072000c0d080b490b0903040030208902081c00d03440350090500c0c142d0814403036503141c401c0c1d5035110701803202d006000d03180010020b8204403081c0305d0040a140d011441d030707483e80300d14184007983c2c3c08100ca490f07004010010104625030b08442c042481141c0585d54070290364240d60312900000e6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 51145390 1250 51144140 51144187
    0x601050105070c0f03111e0a030231060f0b030108060a050430030605030106030b01030b090c030d18060c080d1512050c041104080607050306150408030726 68
    0x1200f108040743d40ca180c02d04400c0254005c02d8600c40c6070341007a08000c82c2503120707c1c070b61149400030180d82039070303490340c00e1180100c0f0b4044070b25500c00e4801d455040040c0254a244041c4000c10b05040ba1600d40c00b81e00000555041004003c4020744a00044aaa110070701400d03003960f000c0340000b003241c0740c0d58111907400b42c42040ca20b10320840c0400d0391003c82ca2607c003a00c0141a510142907070580e0700d84102001071000720024080c2e94079688034015241c0040c00f000e0201100d05000415083d000c01547c0101000a01190f41c0405800c50003400c05081000071203075011580800103030648a07060500c6440e401104107850144075500380801070404002801c55075501d4100010000011100070308024000c8014040040840042000b120915103280c100c8402c2400203100b030860004010398030180701e0600580d01c0c1c590000190031030a02011501c4610700008000c116102e006c0f0192031704920504160b42e50040b1344400c034501c1c00e4000e0a1100414051201180c1d5400b80444c008807030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 51146640 1250 51145390 51145403
    0x70e0403021903020318031c0302090f0316060f02030a05030610170c0c0715020303060d060e030f04080f120d0f02070c091401060503070c030c0201021504110a1205060105010507 78
    0x402d075041c0c2c1c114069540b031040c0c01681000c40c0d1910b007080840c102c02e41d0f54400324090000c0380ca00c085066024503803c1420380806901080c0c88806440d400452480d41c0c070010111103000c641a103030503284640a0041d40d0000d044005031140b650b0000003030700c41e12051a1103160943d580c84050180402e04d1203c07203000c1003580c500489240c4c5440303004a0042000004040e500c486d4a124075150040c0b580c8402d90074a02c2200040c412580481600c0d0060b0ac201e4081c0c480c100c035410700d04045e202802030640035000c00190403406044990060044450f039038161100411402c020b140c0b11500f0b80c4c810301800c042084a000382c012540d0088940b1026402d00500703149a540b110056541c0507008400c9803a40c8400d00d508042404240b2801840b851030858910700d02810001d0040007012030003000d116001705c0b00d004680c001c0c440002d60049600080c800c600d001c0c2805421092070150050280c040c183c03011614040084411054039040700003003615074600700045806611000003602ca0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 51147890 1250 51146640 51146653
    0x150509030307170307022107020906061201230102010b01020703060c141b01060e04030c02040506010c0614060909030a02031803070803040815070c21210501080f010608070e040302 79
    0x6400c01034501c6890146282c0b19124640030740081e19041d6586a44009102130045a10741700d49050700b20307548d00758107403401c42e982d48508001c981c050190120703014811180340b00100300707000c90441c1c0c89010009207492540110034440160300b241c1c00b450310b03503005070003650090010502c03076045030b48090003a01d849005c002c0104103000d0310342c0204001280840f0003010390401e41201740603d002a20030124045070301e0501303aa01030054416054024000d5841d0f400140e000d81c011040c1c00c0809402110034441031103a09503071594888122402d5204012000215054140020584a0300030094006501c2d000302e90354124641009118210390600c00c1001c04500c1390300520180005254000090503080311444482500030b00c02000f96082080c01d0ba84070b00420459000a40b030b040000601a04403500503100315403a0009680090080812842c05a00c04005500560480e070304031080d12240b4411050f41800e99045100d03003040d507400120705021400d80194003603046442801100d50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 51149140 1250 51147890 51147893
    0xa0b04030e1e130507020703120302040f141002070b07020609041b08010f080613021c0206040b04050906041b08090c03010903030506030f0a080a20010f05060118150509030307 77
    0x204628103908000c50450b0402a10116081c000c2d0340d05070401d40d007a07052001e464504030007541c0300c03090710010f07110b02000c4122983d010b001e07504481c094180c40f940007160b82e444035400c83e4030f480c902d40d40501038050200d418a07142d1020400314181c607405c0000780d1901a42e42c0810600740c015052103944030342e4406410b407142e0560740c4a0b0301c1107492a241c04c40590f14119011401d0052588950156008102004100c600d03241c60040f815904a4a940380b114200344400c207076141700c0a00035088800010003040a40108010b801115400c5407074810035034489043c04192504142d40c040100c220b04441d541c0c090240d500c00d81c0c80031203c4111808044c440002901792403200409031702203581c4009210f410b0506110b14449100c8407001400d42203090395404c0310901c90080020100b0001043d0382c445524040e20007128460201c009010058440300058014017083d100b041c08070780c8484031007120300d1a0384000300c12502a1580b12229229142c03042c5c1d019801000c00503818081005100c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 51150390 1250 51149140 51149149
    0x717060f0f0411040e09190b0a091a0711010c09050f04020703020a060203041a060609090a0b010203130902030a0506011803020103180204020313030e01030603050303181606031a090105030a0b04030e 87
    0x24103a84c283e148160411b998010304100204480c298003403050312040c4082416415899007203540100006400c1c0c41c1d50030120002d0103000c44243c03011020030288000350b036100040010301c21080b002080b61984282c015510700c0b2407481480c1e0850504a1600040c0c9405c1d4013400e051806401562901500781c0d454200f01ea000b00c40c1200c00d81c007510324207501c0c1003004a44d940d111509603070f03031454401c888001400065008115084941c0c80d140001d5083c0d00c2400ae44070300d500000001d054403519240190040c0d08200d912400042c0fa1000098041d803140c52842041010005004416400e54004501030070141c100600020300500034240180c07260b02c003d510031129190b042c070100340a031900a0041e11150040380c10542804024000b0070310100032250062081000c0240c0307040c0010781c1e00d04100b28042041d4170040340c900d0010f410742d0150042260103007054104d4074090038000c10018406802e0003174540692096440340300203440118042e4000d0302034201f24a24003010800034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 51151640 1250 51150390 51150397
    0x20a020325060f020307020303040f0507050d050a170703050f2203081b0c010504090902030708010903210612030f090305060a0b12060609070503130c06080717060f0f0411 75
    0x490901c007800c1418042c00361030b03c190110038480303207415451810000002541ca01010300041c10701c5e803007100140c1c10450100140c1c8001c107400703008541210f00505007907469105241c400d90b0441c680801c1c0d5000c0c40c4100d42111b81141d49901e07a2070070541201c004524a801c01b40c04083d02c190740e500380c8499a0080c0207107030011845410b030141d840300c031000c1c048101c420386801d44140d41d20282c180c00c0c15a800c00207a405880f00d070400091214410300000746003c400d640028015403808400c0e00905a000d05040004001101c010301c03100116905401150001e02c01c612581d070a0102c1280003e1052014544022152520303200c45500da481701800c7c004240c0310025040d41d181e0586210303092001070030a2809070180602281d240030350104803202c000404900401400200054001c031071007451204170b541180d200c0403400c4d241ca201a00302c04080e00c000012800d010a0500e0b080d081604891190802401c0107080c1c44004003440a21401c02c480ca59010f82c4500d075800b04007050301c018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 51152890 1250 51151640 51151687
    0x40303060b0403060209010f0e061603091509031e03020d08130c061115010f03031110020301030b0103170a020705090702031b060105090609010b03070c0201110f06090601080718020a0203 82
    0x46c4c0e039401400002d401e140c92400076406110840e414071605070b07514001e072072200c1456400401c40c1035652400715410a203c0d00445038003108810f03210304080c0c1c41001031042d28070541001c4030b03030700000321205101c0c4440703580200140e20050f964241203201ea50354640001c002105020040c55668032400f2040c1c0b80e4100b4400614291b05060b00510b00700034141902c11100720a8240e9414840c4480c07400e1400e00001d802d0155a142c0c0c4120350100308182d000c0c2142400c011903c95842e450f010104031001e11043c0c580407242124440d001c249442195030007402d98005098a80c544014842c003c4002448001940014401500405c0c06208a2038100c1801e40c082c0646604003410001c055030058607140c02800341c00014001e070501c00007225089a6142082c0000100034401260040d000390003119190080e55414002d5840000ea0385000303035510402d540c0c10707a8a5000c090b950300150300c2002c83c10001e4500c03115000038103500503c0245501d205691802c10000c0c00881c90180b540f0a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 51154140 1250 51152890 51152903
    0xe040317010b04050109030b0403090308070b04020103062301030e03130303051b010221060402130806070e0102030306030d050d090602190f020726011b020d1107150503040303060b0403 81
    0x44111015800e5001030142c28240019401e050403c00000d0407007285000c000c00510005000c2801d060051540c200213540c4041c0056407079a26240c00e00307120505440c200c0c04241449404600100000201e82d0040b1861b41725051080c80d010044000d4008952501c8160204002d00d0100300400360000c4041c6029440b202c2c2d81c0e02d0560740c00a002103c0404160203644184003a0100d910100704400c4080c0641998524940310400060028803680300307041108240302500190644000c20a94802e0900da12842503052800c3c00690703c1c0d2100711003c81d0b154119203450400d00c1d008101a101c40003c00100080390011552480c04076482038189400c514100070f1100724403a44000003680c1c1601c2c61002c1c1c18520702e440600966146180345c03130004840700201e00c5054240035842110010b40c0b0a0007911070300340604010352540c8415202000065095070900302c106030000d0703104212094900090b140e0710f00144200c2c0c054002420446c00c1680320140019403160800162010358050003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 51155390 1250 51154140 51154157
    0x30a0504030309051c0e061207080c22080d0e0a0902070807060c11060901140601031112070305010513060308040b0f0c060906010504140907051002071e1706090616090e0403 76
    0x41014180b006c404020b6071003800c0070080d0061180307603800015000b440308d0810444079268012000c005019815200284e0051a10101802c5d2031041c0401d049404040540700d0411220400300c0c1d030f00034000c8001d500300313100c2da074100884800c0ba4000c00d6924003840040307081c4a802e560b141c00307441101200360700140c0984074109404100380310380e03504a40290001c101c40300644c80c56030005400142200c0c140341e6545021031801443e08111021610070740c00035012071034580e038040c0040000380212400f0f00101e091400560b901846040191fa42000f100e0741041c2c940078408829030f00c100100c28500c03000b442503c180300740400030075005a4a55001d415a50f04000c2400101c4d0441404040306105000c00e010840c0d401064100a40b04c1c181e804070700940141c0070580c5050810f0b807200c91082c0d100c940443d100d002081c1c042c001c2e40e281da500c1c9010b42c0b8600003800d549880a44807030665070810b40209603c2010f11340c1d01da619030b8840c10001e40003a034a00c4050080c11003254180e01082088 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 51156640 1250 51155390 51155443
    0x103030305011d061005070221010509150408130e09061e070c0b06060c03160501150302030312041a0403020307030e01080907090e031204081309050606030a050403030905 75
    0x600a031405840b406401e00403d10601c010800142c40150000d401641209901000507205001310347d03840e500a803e5800300342085031510f09121901c0145e0761300703510b00408509000c00c08207007483c100304a00b0005140e5100c988444581b50f0255201482200c1100da00061500d11540418400c900c801e002e0481c80c0b409012405495501800003d201da64000410201581202040b4a81504041c821045a444c9004514580b041d4901e288103484042440c014007a41400d0800b0254400c00003880a64541c0f090540e09a1503800025819002444078040c11311040520a80c010f016000703403820884421681d41c4108030a903010f07001a00300180d41c100b41500403441c41c0451800f0b103070040d11450920300082d19403099000d402c400076141c88802c9a4104200140d541c0b104001407960441d0805292022aa44c032040e00780140d819000c100042403001d41c8900d81c4948400f0349018030310f0351181c07104001054014011002d0554407080200031030360811000f070104180401c0c1d80802c0c0440d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 51157890 1250 51156640 51156647
    0xb040e0709050a09080f0306010c050106150e180105090705090a030c03020f0307050108060411091c0215090d0303090501020c1002130f121e120206040c0803030907060807090e0a05010303 82
    0x3464410f5003810815001c1c00966420200d414044015940b507403292900e00040f2050300032018090041e41c2041408900f60040c1d184038561820b55403140440740b54240e0510003e2080b000354601035084d003500400075424200d0309142c0c4050986002403811041100081d003074405a001031340c002410280a20450411103c0b001e9080c108400510700c00340342c50002420203c0082080b4000e988440c2c2065514034504191212024010026100b049151391748500e04a0148401d0707110b120401ca85c40c0800c81000708556000304007904965440c101500c0940186c803100008488540d030801104c4070b1b0103403d21007403041f03194004001d40d450501900481034915550095610484c041208015062865084005003a40007000603800d2001d00020309180106110140100151010700c1c403005034042600ba01c01c42c4604418402c9a4803501e40a980740011904420350354020b0a00f4048135005030760b0f003540100246801c1100c5a1158000a0544e609482595030304d40c1312030052040540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 51159140 1250 51157890 51157901
    0x60501080303060109050409112101090605090610030b040f1401050a0c0e011b0b0c090d06090201120603150e07120f02180c040b0913020a080901060e070c030806040b040e0709 77
    0x6d04643c01c1c041c0c000b964a5a044500720017110381d109200560403040810307041241e204a000d40c043c02000b0130842818050302070041150810f03a2400b80b0310000e808010b4480d03008040d240c00039042011562580c1d1050001440d0780d42c00e56445a18038030590f1160000d00440707103e9412820045501d0402000c05065041e924441c036061156011078405899200440116126048007038000380d0f4494650081e0700c1c0c80303180041600028800da0090520000f5085035080502c00e0ba20140501d013500034810488580d0700000b40380659880b00c1c0d90b07070b1280381d40041d84181d0502e01521041a034a00014004003100a0111b0b00110458074803c29440c10000342014148030750820f545500e048101240544070324000e1450700c507004102e003295502e900001c04280000294111f5441c4400c1502a043c10001c4604560395824102d0210350030303080700ca1440c003548140d1100b10350034500ba9026180c03800000d040c07a410940d02d01c28800b0584d9240580a00e40800c0701c080c05c21241006080801d83c1c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 51160390 1250 51159140 51159149
    0x9040203011512022b020904020c07031103011a01050a02010b03070609050301110c0717030408101a010f0e01030e0c1003020316020c030d03020703031404050325022b060501080303060109 82
    0x5105014820545c04400c0040390010048a41c00010a040078085c40090180c0c20300c00342c200388040740b00001032000249071800d0b01c2c0100c1340495884900c00c201401e9580740c01c8110036070400b40c1034001c00f550241d00901a48085400040307078828030200440e14042a031b910010006107044020007482c01d080c820319004040d40100545420020041d99596070080e107e5401c96000320f100c00d000d522414001c3d10040c140c8039040c0d84c2840d85c0c1c0304178075024040c1c03550b04440841c0b51031142580b5600883c4555885981501d40e2603210381c1040c0194001c00301810001e40c1401000c1d0364070820340e13401501030b030402d056480058030307401c1000050302c52581500c00e40301594004400d0303c03510f981c0014240c642c0358851402503030740c003c0d5103822000b074503100c1703540d46d1a482803405010030080c2c080003030007800c2c0320003115404a145006042401c02e0020038065000b1400051400380f0704440b02c120000c000b510114004289244d60b101000c0390070903801100036400220a12061f903a200340090b0040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 51161640 1250 51160390 51160427
    0xc09040b061204020607080706020c07050a060806030d0e030f01050901020d0c0903032111070f150c120c03090203030a050304120c081b010b04060e01151106130206090402030115 78
    0x210a400940c2c1040000f800c082d100300310208224081228040843d40d0305a4451000e54039102c4030b4058070b99030450b90145074410540c0b0003010480c2c5202c5e440380e52103070760014000c02c01c4400c100c0042d2030506402a43d00d40500800440504505090094a0050091900040e900c40c00c03843c41c01c0445a10218960800c0404941040401c4d8010b51840f52007466914011044030608030a90041c00c01080d200c450711004a04542801f001034a019070082c05001c08001e6082c08080d450225814404184080741c2e09012101600d091079002030100f10244c1030000701150590000791854028041200005000204200402c65680d0f41e00c01500300c241019140c500f0a07944440281c0101807603041e048003411b8103c10b843c4002d4001302c0b030600c3c016100708045a02c9070105c0304603042c240240d403100c803005100741060038441c1540781d1508000d0005000710740c6624070a001e40d1801c041081c0e03400042032094050b6982c41d44001c50090001e40300e44480300e210700c0c0d005029440074540140c84d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 51162890 1250 51161640 51161647
    0x71703030702060106080a150e060109150c0807020a03020a0e0108070f0b1626071a0606070201080c070209150108090a020604090b19030506060306010f0302010f0507020d06050c09040b06 82
    0x1c10742c002400c03506441c401e09112a181d40c0740c01c001d07401040c02840c041e04034450003500090200c22078120500407c4280d03200c030041d6440b8106192005030305078448000130200b0f254540031600d10001b0300b403e10302c014088800181e0342e40004511843d650444072451248400411130792508118900003000c205540307038038a900c0c00345a10010301481c0485200b94001e03070240010800c85140a0040f841605851646c000c01004a6009500204401c4900603030031011600f942407201d0085202d00300090005180c080135034011101010040e003d021845818042c4100503928110030314442c598001803040324060b941e0005140038400740217103070240c00ca080ca40c40580c543c042140c0549020880108090340d909000c18500711240c03a03550706e03a0307020200100401401142441c01078408030100c4041e41d80355401046a02034901c4001d01052204031035441180c081d0018008031070005101c402030607200c1d00e4450aa400845161441c0c58001800c0b0b9440d2505200e01804044150f980c80d08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 51164140 1250 51162890 51162901
    0xf06090302040b06070605010e070e040504080d1d011b030b09130602130323010b10020604110d020607030905090c0906071424010f05062506020f0a0207170303 70
    0x82541400080e001d40e0320741d803c606141d243c4a0880340344030f034014070810242da035601401d0078070901580c012000410a0403080070038503150190500540c1c2111900c3d280000c03000c0010018074254407a48140ca00884130890001c80030303c03850b40ca80741e078202036556421400600030100c480440e000b52183d00c0c41020301c440448525540301d031a0780d1002c4016554039000002010900701940000c11205003410405c07090b0003904007010107140307540024020448e64a08020b4004200281040168080380014000ca81003c021440c520b40140c1314400740341d070f5600452503981c00050241c001c9a80031100700601e09001c2403295000001080072418440c83c2030006015100c0d0f0940580098a2002c00000f030341414041945480401d20003101d503a0700300f03101d51070703205824031a0f400f1400c800d03940041c036820444222805082003107006142e200c00501e01c001c0c8642d17500780603030b15181c1c01c0c02020303911b5414000a1043c891a43c0050428a00c1d014100c0941002d03e8100b10282c3c00510034040b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 51165390 1250 51164140 51164147
    0x2203050706260a0b04020904020f18060702010c031b0209041b08060610121d0607030606080606070209040c0314010204051e031203190516080907060e01050f0408011103060a0f06 78
    0x9800c900b0400e0046410b454010000e17002c0d000360011194000d2001880d01c18a03181c0400800060541c85400100341ca51030b800c02045016040c4003030b000c9090343d0079420019104041400031710030f0070341480090a202d500498844070741222700b1500400054825a04d88020b29814001800404010710441c98030300d0204401850025001043c8070841d40d15407950203003500300c030b80c039a04a0b03d002d00300850030240d40f6980d540c4c190b43c0100030a14100020902e01d100d4644984141710141203646464407a40c01d01017007550051040c2c52000e503c501c0440020605c01103c08000b40036000580c0715802e00b010007850307071402090011512004214162203840c0800d0100d00c02d001c0900d01a1280c2d51241c803c81002e80180c4a119600d251008000440e04610f958541003d0b4554908803aa07603201281ba0781c1c0c88050040402040c00c1c81e903030b400d00d0f601c00d000400b65a0308030490f0b10304140d6608025401d4400d01082c0c60b2920030302104110b40e0f81480d41414000307240c0344120345c0c0600c0c035222026 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 51166640 1250 51165390 51165467
    0x5060a030302030a0f0e0306040305040518040c180b040504050f0c0303030f01060810030c0807031208042001050702030f010509060603070b030c03060a050909010b090114060f2203050706 82
    0x4148560100b0485c00c680c01030045407807018014003559554941480e00a01d254800d000d8a41b16003402c43c00290004403c4a0315071040c1e034004860140d0a01300a0090440006445010780c000e0300e803000c201e0283c485000b01c90140e842000181003800309104441d00f00100c0060082c0a41d2041c4104510300c0b148078403550442d4014100301d031098540701c64501c01c9061580015080f1520700400103009400000c0c140300316405002c104050000d0328030100c64410003900c01034800c040801c0d00246a45100800140300441410201c1c80d00c4040c0e07020909112000080034620395492040007103009080c41504d0f031004c0118080c100b01c604204000039140006014801c0349030000c40000c0320b030b4450404a801407c401000380d030719454800c80300e5000e06011010580580703200b070000100d0f0002c060140c00010401410f840c2000a400852070580d0410892406041c4481d013002e20741090340c0c610300029501400207042d1617820000040e041044030350401c040e04e10400f040b40c2482d070b06038480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 51167890 1250 51166640 51166657
    0x8070204090507050607080a170112060b013e03030c070b06011b060b03010c0e0a050409061d0a0303050702193905010e09070903020105030c0d090308070305060a03030203 75
    0x1020200340c2841c034078011844d084650804400902c0b0340030320032000c014091070781070384c0e65001c030b0100c0c3e445600c8540c64080c421512507407082d00809000403801d40004034442810715054241c60075001c6045041030112205400e0f0b80e002d541007040c445114920100e02540550007180b440c01c1c0f14100e45114820548042d2255481502080d640c0e03120300300c05003c115495040320302884c0a410300e0790080c911131003824801e41c6000c2902c07121501a1040d02d41460000f44880006c0d8a000280805003034514000c44000e5a2081c07031001402100c814a035204c4013907401010b004403075242c0601141ea000e0706038030640d032000308964110700c120742140760003540c40401c540700a0500314180704000700812110010303a0821400301c07002c0c07290610480440340309a03202d00d01900d8107020b0052046c1c050380c000c0c001401200060016501a030f00464010327602040052500c0d484245040071180400f6045000501b4002400b446a506004030340c0c001104a88681701549143c4d0701950300d11840c0038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 51169140 1250 51167890 51167899
    0x90a0f02130207050d0801150c020918030702030d080f010e060a0b0703020109020901080c010207240f120606020a0309090509060105150d0911030d180b0d06050d0309090c020109080702 81
    0x800c0741c88201c0302d4041d6521076612504440d0842c01c42c0f038014280c0c0000f40203142d5021003243d1a03a4103540b240d00b0a41c40590060210411501c8590070660b011035421400041ea01c0704002060040e1410482401d0794955a075600c0e11608000c083d586007443d040c1d1141c1f690303088040074401d59076601c0c01c02408807584000800d0350354069140c240d01403c180000a54001c0700c0c000001206640072034910340b424400d80c01d80b1a0682c40b16030b41240560b14030300d01962020303510580b0001078010080c4c030081e007042d400c2c0f02410381e0318202000240d400540040005800c640581020141c00800382c002138400001c0038403c500e40101c0460369030300b051081a200d1806001600c04e030a443c801100d40740800148144182d1401d410300d42000810404561f001c0d20494501c600c02e184280e2101c50999110714001d50200e01d000124116034100044000ca1260740c0d0000140c96038401c000000701070300c01e88548448070f03c1c0000303900440315006812410369042c4036103400024442c8040307418480d411079 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 51170390 1250 51169140 51169159
    0x5150d0911061b0d050c0a0b04080f130501021204080a0f0629030c0402130b0901020726070503030a14161e210f1d09150108090a0f02 59
    0x2800d14201d10700107200780d0001c0d400944a0020120803181e10021061401201e151081c001e80c222801d109141081c18582c004040200c00901d854032466041409800054107201203800b519847e42d200c000e10001621122100708411358040c0045808969144a514100341c40d200c0107980300e03030076988003e003141d040d0400b040030003800f40e114140310102d480410741c0c0e82d03003003440c0341c0401c11420302414824812040c440150713142500071141c8560607070600c03220740c030302c0c260980d90035401c061040b9056000d180385c01304002030800250750005404041d8500c00c1920081c0d0340303081c81010b0700711500a800800c2500400c0b6005130b140d200741c14050012030341c0c0b000c040718100348985040380e0040c200214036047c100100007404440c10b645d4061141012440d18111400aa044041c0400c5010a082000c6900707101e002c0c1d01c80e00c01311001810307004030703052286e00040c0d20005c0882c3e0810848101d08060307926540d10607205503120503040d00800411500e41c03103840b581e843c8094000e00c603103c00c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 51171640 1250 51170390 51170393
    0x80a0c061a093607030320030712020a080d05040b0604060e070e1203040f03031101020c1b01032406020f010501050a090b03030d1802040b010305060d0308070c02060403051605150d09 80
    0xc6032083c03010302c0000303400c00c0c2d100c040c0c100b420344821003071100340d00280700c419884800400402450310303102054401146404001d90318010805850f80545056004084091000c2420300000300702040c80004006510b103080e1504488d138100192a59000e2490000d0070b2214905e0f40c03018507003117030352400c102e0620009040003c08150021260500300d02002ca00001c0b492480007244080d2842500d8010340300c070000895908030f00824485506580c00340c5c40384000c0600f80800e03640300040624010410f00000c00503c918004810f2641d18142406401000000d0341848044001c4035044002d1280b54944400110014400c1c00361641c8a035032203065412907035080041b40c80008400c0700174082c1403101c01c101208004000401d9004908000c81343e000e541c42031003664410607004120f490890880e0310103e842503402020031007031000110100b00940d503450302900046128500601c184a8405600d22544031540e109602404880803811401302502d025902c54000342c903070000c1e00c070300b55 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 51172890 1250 51171640 51171691
    0x5090906090c2206030606051801030f0204081501060e030a02010206180102120a0905070603060806040b09010b3a12050d1506021c0219060b0607080a0c061a09 70
    0x19580001c030714041c0d000e91100440c0b070f07500d00841120360580702080541ea6681b0b064429102da40201903640d110005070b1110f03507000e0382c0000c7d43d00c0e2001c100107080940342c8103142e181410226900f51404a01001044203550000c40140041002c0e0040c00c0c0304095640080d640b914064000b969008401c0c012400c0713200c0c01d50559410008141e021409400c258811400902041070103680900a407038000c43c886010340134510860f10440000c0905540d54ac880348441c410140c0640c081e952550384900d00c0d542d0742070b007022000c0180000c07049006005100c62a41c1c54100d12102140308510182501140b41203038031a6400e189801c095584941044603100140307074924106852010f40103010510960010325501512001960410028110034013a41d4607445070b41010108640952107000150541d041128510000b9110505004066a80c2d0744a60043d261100004010303250035002c0c00f000380900301621000001c2c604500016201060841c00b0003004440d080c80c111210230340c07000c072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 51174140 1250 51172890 51172897
    0xb0904020903030a09060f02122209110405090901060501051e1e0714070f090902010309020301020a1110020405060901110a020a03050f010e07080703020d031b08030f0705090906090c 80
    0x70010b060301eaa070444500c025121031545c0c042e20001803001c41e100211a400010303429001855003800c641801d5100b549a40c0001d0540c1030401c0754211f03440b0010319161a070007070003084000301504a890f2414a0140300c207504c4010102d89607681001420045ca0340c2020496800b90040c08035280c40c0b81700c40c41907800d80d1003400381d507044080080102c10725800d2188050200180709407403038410b0a07240b0318080ea540106001d0781202d010302c030204011469481d4030aa10981c17040c100800c10040a40010303007240c00c090b054031301041000e585c20040103414802c1103a001c2d502d140071410b09080801203032082c083c0140c01410302c44d038410b69400761403080250503c62603000f0040d540e62510b914200d82c48040c00481600c00e0360034880f039101c9807400452604203981c000801842c41314519001c2080342e02c0715800560500c50210312030342c50450098103824166000700d58071503a90500002a1040000040400c07003042001c0c0200e0b030044e42c91000d201c1e00103d0031904900c0d580c90310b044881040c171 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 51175390 1250 51174140 51174157
    0xb04022817040521070515070c050303090703030201060e04050a110a17011418120a05130b04030506010608010b0313080c010c080103020a050a0b0301062106180506040b0a0b090402 79
    0x1001c101000100080016030200c00e5140c01400c02c283c2c00c01d100b041c51640100d10004000d81c000702400c081030310340c106c1c455501244078600141100c113140c943d01e003150b106076401030668102d070106100785902405018000c1a13800009003403031030b00d51250350b02c030500c0c490003c041025200200c0500d64403107400b200501040c240c1c0140c0703c40307450f028500901c2c00400380c0c02c5481550000441c2959854512890b000c1a80d011b0409040105509045030380b0080700710051050504c1203c91030007040c0f8980000d0300398008025900c0707045041c46490084c1c16440103081104510061014250100c143c0703401012810b1045154201442c2c200d509010320507903d400b80d841d04c02055411035000710164100d0b4000d5500210698845080c030a0820507405110200c3c0401c10041003494403c2e601101c1c0c80c524100a00c881c144407060360401c2d2805607002201c1c3c0c0c0a010f64203488000705100c0d15401c154125000c02200b48001c010a0f80d03040d07584500d18820b0700c049840030140c1c0341d9404554280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 51176640 1250 51175390 51175427
    0x203040c030c0803030718050114030603011b02060405060109020f040501050904090b0a06051804020105070201120902031f0c030614040e010b0a090203070206130b2205060702010209040b040228 85
    0xe43ca0306001c075a40d0700104c40b580700081d4003c0000f040c034200c45130381109460041e9180995440c501804940c2c5500183c0101d80641d6120301030070369450640d40e0b4494a40072a8040c2985003018200f0345c1c0b5090040e001030740c1042c41086501002d90741481101c1c111042800d0081d1502400000a8000c108144005d01100c05140400a41c5942da50140c0c0035210215a07200301c001d034440c981c49c00c0d00400c480c024082841004060055800750000281c0c09410440105030f680042e40400d0030800d0214011011112010303424580c110b00c0d008800014646142c00c101c02480c02800416450013410130901640d50f0b020070300d0140401b0340080003a1100640814440c550740c500348402580308440540060041002090000001a51503003a040d00949503241946405403002c035030b825021003510b041241c085c030350b00001c0c0c0244651440303580c0e107800050f00c4060000c2484103881105020318440e41c03040121300462408e004865100480865642c9404070b484981030302da025031251004c001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 51177890 1250 51176640 51176663
    0x120a0203060d020f03101d010c170705070203030c0d02010504020a050306042105040503030708071106180603060a0806130c06020a02030616031104080102090a121101030e0115080a051204180203040c03 88
    0x62aa03421803441f000001d03c0200030707107040010f080742c2c00710001c1a203001240210011070101c0e071046002c2c0010500060a4030310384840285264a4040e041e400c410140c2d455004010942c40c101004100411382500904074524040c1e59489101031140d070200001044c039044840060f1040e42504c010700405001c5980c1c40c0e88904211000f40c1000b00b08030340a05180c486080c50707040c49400d455081e2200040704840701c81c144204180d5820040c10b04e03411402d6400d0008100100700030003802140300505502e2810928140701b95042e20b55044442590b01207803070754005031400a803241d0300502c0e810940d4401c501115040340505480501e01e2203d20380400e01140951040d03005040840e01102c000c880c0545c1d5011020f9940b00d910f0015103111042070700d0b0740083d4007940003c8000306101c400043c40c04126101d50a0041040d08a8100c65200840c0380b410468104903000301e801c200c146a0b4281490151028203050000401200c01c64022000c202040f200c10300c2400550b502c4401c8028 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 51179140 1250 51177890 51177911
    0xa1202010e0a0b061002030a0801030f061e0506120d020c090a0b030d0801080d0806010f030213170a11030318150405060307111b0f0118090504050102120a0203060d020f0310 76
    0x848000513903107103114100c50040002214000021501c81510709c3d212640242e103035489621aa0b101e8860a0782c240340c5075000e200c00701d50414800e600d6110708500c0040c0328180a400d210202a003290118030ad98011030444030111380000390380011103400c80d42d000e07403540c03807030b1101c0054400d8040040d0148180b0300a804620b030040c5006040ea070102040701c803034100c00441105d1081083c6c0d4140d001c102000c115410040c4a074008007021410800c09030001540d405003603841040c01c0000c43c000303401048100c1c0810100290b8044141000c800940c240f07201100811000720a410686100e000722032a500c4000c01c5000556000b0706005215688901c0d000002800701c4005e004000010b01524100c21007140ca00724503499020000b8003810400c00b0480019541040207000c00980140e600e0400074214005001c0c40d84564414400541c440c15005090702e0614809041c08c00e0140c01442003022903102c0b1003102c0000f40e01103600904036030341400440c0c14a144050342c42203050401100b040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 51180390 1250 51179140 51179153
    0x1107030c0201180e0402090405150405071805010308040b1c0203040303050a0506030a21050f070609050c120d0309030e04020304061a0a06051b010b09090606010810030201020a1202010e0a 82
    0x10900030307264000500b0340e44860203a0701e4280e00031314509504d81008138025041440aa0740d000c0e114004079124103110300415601c2000c1145c0480f00c0ea48120824050303810200805c0040400b5a40240104d50441d9034411483c0a00c0c01800d40c04503001c0707580581c1c8001c040c200314190039441d60466981c109410010081c182c02c0b00c1e04e544190404012500d1350030006a500134446d04100b8603079005408070b096690350701800c030109041240c24010584010340c450014807d4038411500003030792440600c0c1c801c0c01e00c040e009180d8801d0746411602019a2000b04180c07409900070300d00000c8041e00d0385030565201c0c0415201c190410b1000c4100810001e43c0d5103d00c0545803450000041b0304131850410030f144c0c00c1c50151600092080c0009402c907040300d03a4140981610030004035460840d04040f075801c4108413000b4486a0002050154550700500001e41140029130480c89440c11500085c1d5a1001c0c10030040c414a5854030241c80c0d14400e61209009403484410355225000718201817 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 51181640 1250 51180390 51180407
    0x91707021503040b130507080d030e120c032d071103010e0105090304091a061207030e34170304170a02030c09040305070b0106090306140f0606090301110703 69
    0x2240120021000c02000403044002e503442690f000e400c4030b840341d407880705d0000d030140a22022641c0e4411580d010401010601c02d1a00c0e6081a65000408102c40481036242601c0c800d00050a64001c10001803401004022200c05890580c4855541031a100403038101580c80504180708c52008102481000944600b400c80c00500320028010040e82407003c0b0f08170b803019a1607040540c01000200034008040d00540f0b00f5041c010203601a144110b00814440da0045a030310a4614002c3c1c00c1000141d014804c242910481000500e5000324030100c1e55a040300b4810001204003800d034a0080c604a40d03465440500440707201140c1c046e00340e05d0a65034a40090240b08030200d0002c180c4000380500103007002489400400400380400c1e2442070010b0f05401502c10340030090204070201c040b40365414154000d0025944076000c091550418000b00e80300d2034007180070040c0d50b20600501d00c0c2c018401d103801060894445548110b9503000a0041000b050360718100040411450141604040d28 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 51182890 1250 51181640 51181643
    0x3090608070806010801120507090507031d0304030309031709031203060a05190b070305120702060610030903080f0a090b0c040e0c0403080f09010e2808010b0105031603091707 77
    0x400000d51036419040d2041e2000300c850f603000450750b400405c4141c000e510110912805901501c4d01d65844001034019a101181e00345c0200751100c004001d00d1641c81100401c251000015604060440d500100041c24a2002615008011603245031000c0c4940441d107125000a088400d0f07408c110469460f141c0040380c0c51442507905c40c0d80020b041c00c4c400c610600c41c1c01d850000044107405c280700010542c001c0c000607801c1050a200c002d0000c0c0c04c440c0020f004034416001032410349043c5040100c510b0b01900100308040c08c0800c04000a900701b0200740d040401c000c005203a45d611401040c006040c2c0c081d0140c065000ea03000c0c017500c0d44900008206640b00031191110941e94100c5940103442070f480000c202c4001000301c03000042c50350000d40550300b8145072180300394058a0000d00da08000140389d5001d0710003c107802a0100c0c42d0800305004000c1c001c024040303101c0440010b030017400018071101040d13070036045458403140b00364040c1100a500181e410641c01c0760000414064001d00c80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 51184140 1250 51182890 51182897
    0xb0603090f010605030109210c020d0c08060604230405031c0212060d02030a030e0a0302060d1b0201061d0a090602160309090506090a0917160606050a0302030309060703020705060403030906 83
    0x400b00704ca090601541c48815080b91411a003074015403992050821400b29050410408541d0040140c3d2190b0341e0b41201402030065494071403c058046007480005400c461140c2c0c42d00304036030113281450f401c1c000401c200000c0244c283c0d40710b0900381c0c190700c180070600c1d840381130028010207040300c03981c0649902404451250510307500d407818800072034514000654150b200c0480030000030304c180406042201c1c081c10820003a030356640030030403540140c14842c2440d500c60746205102c900e0a41c9440020071540700921032546050f1860b0020300000451034401c021400c002071515070745402a1080a1740544115651200784079819582e880c0560100c000920000c2e00050040060140a0150750f0040103d00546c0351400e448004141008007201c5041126140c00c2e0712010b07590140c188100b0110310400020440d182480483e0541d80005110300040703c3c050026071400400d076814408240e038140d96600c0380c0d08061307252201a500403507010344002070210402d030b40480c1d00300442e5541d88 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 51185390 1250 51184140 51184151
    0x1120905010b13060f08070509010e09030408030d1b0903080a030b04020c0307030c0309240507030c020a0f0911070506010510090801060f0f08010c0c03030b0a0b03010e1509150d0201030b0603090f01 87
    0x4001d00c7c0c80f405644100355000c148030f401808064010481c6540120502003280d00d0a55607906040c2960040c1c040340c8000e40d039440c045004101203041d200310407011454408030b6103040d60740d444040d01920101c0c504065a4100504003038072550b040300c81180b00641101c2e280e00e01d62a0007010601110380460000d40080f00014202003100b400b0f0140f5400e0071601c02c60110700140440e076540107154103800b003001c010200e00158444044c01c8000e02265242c0585442c10161140c0603541114041410000100102e07070100300c010a0703840c19154201e8105030b01c800030300c1013110506c0481c0c00604995190000c00150502c2421500044811b20310440d400181c1c0d541d01942220f40c4101e070103021841c0c1090440000b440b1b58409850103800500c14505140ca841500135190001d03002855200145010b110030740350340c620b40e90b24034001103c2110300d40c50f03d10100481e011994013014019040d00300c280c1c045a0294000040c00000580070913164941800c0c0980e0714026194041215460304 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 51186640 1250 51185390 51185399
    0x304170304030203030112020a090516080c0705030405060d150b07050105070c0201020a23100b0310090201050d091a040f0606050103110f0d0216051b01020a0201120905010b13060f 79
    0x110160303072046030550007560840c0e1808100d601c140407002c404a910100108010034084014441d45006000c00480a0311901c0040030140450401800305100c1440a10681c80001c034004216000d99030180c40d420703100d503403030504000607000c4112100c1c0d02c0b451083c1e021412544001c0503004107400750b0b0003407006841d44901a5042e2130b031210301900503000302d405200032a050494244029144c2d40102d580f4a60080700181016403001841140f952160202c1c00c00d40740410112403040711842e41009001b0440c2e0001e4180d1050803802c1501c0c54035a614501400144140301001400c1039049107160b02d000e180004000068480031126030b8503044000c00c5a5109202d0307000c0107591035440750318083d040c0d01c850303003e80c100916085801c0d8080041380c010000341004101d040e48100d000f40054544c23100c1e0100000040f0000904641c081015000580e0b07100141c000c41f40081c12000541c3c5107a41085405880900f030000d0f00440c40403c0c00d9900c0400c4d600000c02c45050044403810365465 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 51187890 1250 51186640 51186683
    0x30f060726070c15060f0e0609010b030106140c01090c1707060801090b0f031204030201021005070e04110d06060806040b0301020903030912070f080319030509120c0106030204060b0304 81
    0x204488010407122041c00101464090303900e0b00e034102d003d82d6030212400301d9040501d0030b0b5641da410443c50783c0350344002042000701484266402c464100c42c15206581000300301c00c1d1a000500c01c200412940754110100c40c00800121040c86072940c000340b011880d2428150681d4082c0c1c440c400c01d52004000c0da1200303c90100e542d8080c1c5501d56541040d42e440c0044450182c074440186550080548130000d440b9941040710210b8001c80d205855295450340c000a810240c0f00301d070228109041c0001c0043c607075030142c110001400c04a400081c005408000c0c0d10040c00741a80d110b06c000d182420200f44150000c00152007942d0031501444400184810726003030307000307018a65070940d00c18061600700303203007618004104c484020b08039200715030748600daa508002c4541c880d40345030b0030004e041d0816084080070b42c1c1c0301c019107050a01890500050300c41d40c8110040d5040c800c1d26000c00d4900e641c203401c1d0414001075400030b1062200540712030842d052076100303480480d184100f03840c03040002c0e0b42 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 51189140 1250 51187890 51187937
    0x1008070b04050a090c0e01140d020c010603140a0507060807271e0803030a050901090b0106030f050601090b03040308151207090b0103140f040512070809030d05030c0714010b030f0607 80
    0x1d640c1c0c401c00c00c111b101005494020010314071000c070440074408440c04411610291480000071070002c00e0803490741c00c1200003201c48020b11002ca03049a01ba00e0042080040d00208842943c6080706d1030b540c456200f21011f0640304103c01b002c102207805109080c0c00080b40006445100c40139051030345001c0c05588085806119910080d0000c0c0002942c291913503108541c00541000045015140c40c2d40350400e014090b000703980070a6440f01e00418084180c4502c83e8051000e0a0140ca0780d4182580282d05002c020002001c10810b600014079406540d004201c8421014141d80f03110103007140d1668441c3c0c46401481c105078176100141d02d00350f00c41c0c0925180c402d80302d4400115519815060001c0000080040c0c605125906131101c0b10702882c401496040c0c0a0030b06144c50702c000b8020582003075048405001000014001d110440e100101111402c9034800b0000c005001884406400340a02550169050041e280c4450802c4230114001d40f10360a0350f41d40e911161114030ba410203405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 51190390 1250 51189140 51189161
    0x509011401050f090d08120f060612070306080f3910031401090f0b100806100c0c030308040309090603030e09070201090c0807051002010b0906091008070b04050a09 72
    0x2249804540390394040c40040402e0300e1001c51a5141c4024840401d10448031504111164480050f02d04190101210503c0e00700000704000030440c01d203040010400c3c010008900c40f15124100403841c01c5001c0e5028500514144054610b0a80e100c2c1885807102c003408010900d000c0c02c1c05001c040340601080c141c841d2781d4610f1a840019908800384000360039202046411300da0740d183e0300781200b001201100d00034801070780d01092800c83d640307103030b0107880d003008205024039070803580c0d080d80d15040003003191302510035a0000d4045c02d90035000c46403082d00503005080181490400b0081c19030000802e84a0f40c069103d0285c03e130b6a13800b038141224420300c07000d00054840011141c2502e801603e15800c031803e03200110f0440a10386455049550341d038403824160344802420042c5080020346d205200d1081d00080100c0c0080e800455035200c0001c002a101c0c8002c1000542d40f18007441e06400507040b107100b110040b40c1c03501d02061855000740680c40c45442440000608206540aa0107812 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 51191640 1250 51190390 51190409
    0x7060f0314061804050f0709050109060501020c0307050f040917070209010f030b070507080d24080718020307200c0405162c1923030d0e01140315030601050901 70
    0x3c0e10b2201240441e4034050021540c034013404074103186807203040041e1009460031090000f041c0d45400301e00c40446445500150542d00100ca1a020642c0e01150700402c17140e0039a03481d0355601101c0e0001e4020003410300000d140c41e8030b0b0b4150100c141890350150109a10941c0c054091340d1321b0300038264030142c01e440028411301180c0c0000e089144142c1c00303019501e01c40c52103e4100480070002c001a41c03407111008003500040c082c0740803e2424804901d00403c1c0200160a006040c100c02d40011040070281c48126500000461000c81c451101c0c2200c00300007441d0082541c8000c004562502c2c1000102d5100354240004101d50119525020000c4030386501c505121065900b000c84100c0d001d0700c403415501e00040011303142a101d524081d105401e0b0b089480e211582002d071a1528540740c25403149101c00002c00040e070a842c0024900240300c2c4900301025440d10410048421041404076101d0404012003884503041c007000c600c100d220b508030152400c41e81c8a005000c002442482080d401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 51192890 1250 51191640 51191659
    0x30706020c010b0d080901032009010e030705040c051305010207050f090702120d0e12070515040c0f03080702040b0429060c06040b0124080103020f0105070507060f031406 75
    0x140aa402840c0c100500c80000c9400c0c0482000030b5280d8040d110290f0710301c040000d00112542c0d2620804001d8080d030050700e0305c21400c1507841101800340445050601201020704902507170108100c0c0f00504000780305101e0b04801d081c0040c803640245049501707140900b0000314440d03001040d1102581c0e400780072a04410b000704100480881c01411a40c158050120794008124182c00241490b401207403010541c07500e800c1c0a18034010801509010031071091060b01c002400100300400f074007400803d030038600e0f191070601c0c0c0303488483c540c402d50340502300c902e0000800c40031101900e40c56008031001c01001303c1c41800c0c0f10955480310700503a152082d00500034840c5d814a4040104040047d107418200002001107034078124098506407110480f070001004424041403003013581c00f051000b482082d400011018140101c1030000a110707207401c000c00741413a481081500c415a070010100c40c42d06607140e0700034200052200ca0600084d00b8001c1030000c01c600e82e2001801a5009840c6200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 51194140 1250 51192890 51192893
    0xa0812030604020904090b07050318010603020a05010c1e0510110a140313050a060b030607090e070e1c0b04030212090612060f030d030b0a090501080312041112060a110304050307 78
    0xe60001951a40c082d41d20106c0c100440c007503c0001f8490034964a900ba502d050080c8130003002042c0180003d5940c1c1015030034801611340a01c0242220001c0c00c0043e49202c0c1850304100100c0c10340031180010f4030541208003801400681540c0e40780203d9801c2060003048960554148a5008810f000c0740c0605545041d5080e074500556018210060240110080c0d40c1ea0905100b03450030280d511948860a80d11207140c1442900c0c1c0082c0d0a0400f240e006103040415140f0390001003804c0184000102d0a55a80e00c030540e040c50b035204181a0010f621016280010390504180d43c141c0061145001100071244500120b40440344014030550818281510101d455500100a2a04140c178035042c49403613102081100049403041e14042803d41070035041c880c007038841d9030115580500300f03070040142400220031103000f0824020388030380982d0b46080005090b041901c4554112407840c80c001700c020f04c0490003038001e4140400512606401c8041415503000170360300500030f500208110310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 51195390 1250 51194140 51194149
    0xa03170c180a050301090b0411010507170309070b0a0210050606130b0304020d08040305030406030b03060601090311030703081803060c070308010605071103070f0305060603010903081911040602010b0a08120306 92
    0x220a80001c080301c114645443c040b0b404d6030031007030040340c0d5660000b040c0400c01640401b40030b643d8200b86003590500400340c60f04560114070000c0b404d44020000045214100203101c0038015220405101c0d1b500e00704500c00a58840741454066221454240891028070304074044445003040006031040035401c0015440c201d034009081203a009400032003942c000380e01040548001c5005a02a6845919200000c0c040e1011510f0b101d00c40c0d040881048045c1c0e80184107503080e20703005080140d00d00c032014042803404445820107040311201054822500e00d104801c01d44000003541600e2aa423600d0425038664007c1d2080200407541020047c810184211301602d252400f0707400796007100d142c1e00b02083c02c007501500120300500302c11000f8824481c0170005a0741188043d0003c2000c03103e947c030002c0c4210806828119011a03040b45481001440e400c51030410241c118205e580d90340e60032010380200350004c0030314003d000d001c40000307540c48042942c0c0140040c41c4210303071030340da035200030031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 51196640 1250 51195390 51195427
    0x6160e0f0f1018080708070603050106170705070b0405060717100b0a1404080304090506060304021e0d200f0a0308090f0d0609060c08011406041404020c0f0a03170c 72
    0x60070000c81441200c518040c00f04110020039041004d48242414201021f0918901e500080141810440100246030340246013100d140c031015000715003a06c8124045a09110b22900a402c0750300c0f201c103000a01001040b16401080540c0340c1041501100d4401685030108648800b96128800410058042c42d10020607100c803003850200e02e88040d12140d0080e40d0059000040d40780c0c03020400b8841c07042c15100b003680241040740c050b8103600d03041d40003c1c1002c00180700b8041c2a0f80c8004515819141c0c103064000c41c80d80000d05d600d01000f440310100207107654180040c4241410110701c402030808422210940703401c00700c41c0b07241140b01d034140840020440c0286400c54075508082005c942240302350400c080c41210045520341034668000e091183c107810183d21305050b001280502d585a400700d40464201c0d5400703003c0070725020300040c022300070760145185ca03000703060072107905e6440840d46615040c827030f0300c9941c0d00046100c03148060710003c640c045090ac4040020312400f00540404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 51197890 1250 51196640 51196669
    0x20405040c050d06020414010e03030a0f02160905090c0f01050403030315050607060212010902090f090a0906050711010e010207021008040f060f0c090503010203060d020d1406160e0f0f 81
    0x1c2034009550b480882e9402d9240340d4180c0e8100c1e03010500b1310500d004d0b120b02203a45442481d0658450b842200000d4891103102c3d480710074840140300c11045035000740180c00000b10320410b5034411560300c815080141c00101d0f072521383c6019125120f0070925001a40240511043c0e603810b0500e811a64143c0040005464420310000b4100e4005819500c01d4001c02203644a03070700160701c0c0c407401e1242c0192200180c0201c0c9103640107001c248901d8440c0c0d04481c0907001c04032441c1c3c4058603516007020051844070740240910381008108450316410000c0d8a54000ca010000c110024415085608038090190000e50040709401e403e18001c4c070911801d5009400f500b84070350314881d156641803c496500e1200007040c0e440b4894140501e4011851030000d0006038003e600c1c501e4800c002404540b8000d00c001e00c1024049620000e1100c032a54020417a4212000c0715554245002c031500303011840c00342c84000a0072240011401d0601c04590400c11700e025000c40980d20011041100c5040081ca4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 51199140 1250 51197890 51197903
    0x302070b0c0f0c06160b04081612020f15270703080901120216080c1c0305070e031609020304050a08040b03060405010801020a1d01050915040906061103030a110408150f07030b0d02040504 82
    0x480c241427801c01c03884441e10914900c0302d4501102d41c080c0c102503c09054200310380080c1011760900d030042e51501d0788207210501041e500c203220703042c4011030b901c1104201494400c11102200b04481c4030010040b034003007600ca41c3c40d00c0740d0f122000000d074850a440e1400100c1510030b41c400251116015010030150301382030b10000500229106a011440b000d5440001c1d25101408002600454103116014095010708502c80c140032100306a80031910850045c0c0754000006020b0000c1800004130050b4020b64a594895480d04030b080f00d0f40080c0c60041c07249282c6000001c454030144203e5090343d20351385949640000b02101960f084003514203e605010017001301880c01d645542a41004856840205d5221400c282c2c2e05030840344581c000070203001511400b02d404100000949a103c00312000c007007040000080309060f03d01070751f03111905610408441c82405c80795012014031800d9001091507260380d42103012010f5404080c0e035240c0007110301d03800d07001500303098001c2c9600502410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 51200390 1250 51199140 51199147
    0x100c0c02040e0109020a05040207050c10020a0f0309090501050a080d12020906070b0f0f2206150b0307030c0e010c020d0203010204030506090604030207090b0604060c0302070b0c0f0c06160b0408 85
    0x2008242a40c0d00380b5240810399548081403800c502e071240403e009042c0c00c1c0c80460070500f8903078900b0345e03481081041c0c81c03094100c9504004200d208000070701c40039501507540030401c1d10034a0090504d080c03d0044030b80c09410000085924204203a01d40111030040c0001c02c5881c644500075601c200d0001c00c12010160200080c02c81031312260020181607125003881d4400d442c3c10848103580910203000849400b01c0136081c4540c030904c02110300b0003204000c94050002c1036514081d0001c2941001c0400d40c010320050004101a0010207903100d03841c151418082180d040318121201030031070b446103000c1507032030700c0300070140c03e0685049082900c007600051078503880307460b4245003041c11101d030f0005500090801040680c140000e800803c03d501c020b00001c80c0c8400024201d000d980104020084140403400034503200300403d0b001405018002c650f52000010700d1615980c900804212500c04d099005001c0d00340801120145203c10111407064507050740d43c034603070340809402900c03488401d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 51201640 1250 51200390 51200393
    0x90b0f27030f0c03060f01120222060609030203060a0e0607030209060c01020f13080109030e09071e0503011d10090c050c1506040c051207050d090503030c13051002100c0c 75
    0x20008404007002d164020070003094180101031074448001d000044845a080040000c0d812420340085030641c11511416143c59a5a0449114a91654a00e0160b08181002074003580142100c0300782ca0080d415204241c0d44c00388500e00341c1313029040c030400c1540400009113110317103c3d60103845c07d0382c0002d111505d0108911a51400c4e038100380c001070410328000481803107204004400400030203079400280005101600e02400140c5895000c45c02000c4a4000800042c45402000041d152070f010146003001202402000c1d03401c24003640014178000203400e1880e0f10129440c034441c0702341c1c2681228080c2820020409000c3c0f103141802406410302c03007528900c6081c0080761b103640600742e244980b8907001c8200700c25541400c40002c103020040020f02126840c411126501004505180f5500c0c00c2404010009180c0600054020f000c0802404000d08854004002c101d2800c021070580c2500c0720200625400300e4078407000981d100308285009102e060708504904c2080d07040250880009 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 51202890 1250 51201640 51201643
    0x105040306020705030901020606031c03180812010905060607020a0b090d08032a0f07060b0316060810050306061f03020f0a03020703080907060c020f060904090c0303090b0f2703 78
    0x40f8111900c1c0c0000c95201403550381046100d9114004030020801340c400001d881140a60714046103040548a01020000b061000d140e4000260702030132840d40d40b4104e1040c0d8004070300a0080c031045500309004100141303026015180d959400070070300780d40c1c1c80c600784855026600a001c031640290030740300c445000c5640f140203544203070340700640c4404050003440d0158019030b5220140d1115036040c41403207650185203058800301d551000c4000762100078240060f10b40f0b48400011103202c80f031030b01c0100740e040d84182458000e04030b550a040100d03032154100741d160303c01100c4a64000d60102401c0c00300c0030507003420301000e80e42c0c3c0c1401071411000040c2c0c082281d12a800c81c40109070001901810184e0200d80994401140d9025103400f0f400c02c04010403800000d000a44202010035810300155900d500729801c0050080c800c200345c6100b4904840302009510059003c50180480022124007000855030130b0140c03904d5051401c02401d00d4028003411142c404224003551a1070b41005840 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 51204140 1250 51202890 51202897
    0x604090b01030516050303031902030a060503030301090b011101020a0212070c0312050c1c1209060e030d0501031a0105060702010c14060c0d0617030406030c0c061404020a08030c100b010504030602 86
    0x19002400d003a2000c03100c0105501c50a91000d1b000c0d0307008104011414011021860800c0c45100001da9039841c0d1092040c003400080d080b80c0d42c1404000b0000504807900d6100c0555160280c8035501f07010410b00c2c81030f00b00d000e078044880158001c5441d2a8008401200030715010303104031000401c0ca522600c42c0d503006200003c5040203c0c1c800502c140041800700700f10310f201441701560903404561a44011300310700c0040b0904070080d1b12203440b03500b04019500540c00c0c400006007140c1e21680d001c2d00442c0501000c1c40155072015000c2c0e1001103484800348214140c903006408540350201c03d9004503800f00b04008103440144455605103859101444150702508107402c450b501c44006c24600c02c1216607a030301a11410100758a0a81065004025101183e40d00e0800040310b1260f40c1b02a5424121040028004d900d05482e03003040e11040c103000c90196000386e03181203145458828083d034a10420240400d01c4e4814500c5800c4100c3c1da401540c4918418903015060540d41d0307942200313030380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 51205390 1250 51204140 51204143
    0x60203041403131d100506090a030b09030712050c0a0213020d020307030504031214010306050907080d02152409060f0315040b072303070c0c03030e0405100b09090604090b0103 77
    0x200d1051041107003404400320131000c2d2980400248150500c0c41d18100f038540c080c030816000f07110101e2411195035400000720025500b080400c81d107407030000d0f507a5460303601c0181304075008880f41c00c03540c0e951445582a501c020400d540100105030484d000c000c1101803010ba4071701e01d5078007040802240c8101e4005980606680e88000c652350820b442d016081900740b5040300c0c0e00d10f290046080701e4481c61214141160340008000600d0b48802140740c0c10401c1075000035010388100b0340030000c2e80d50b000400468600c001c5550340d450b034031815140c2840300c040d0f411803500500548002c802914003040b031642c105a0007041c542d9204d050001081c2882c000c04230f82d40718001c1201c1000244a070905d401c6a00c103120740fa100890020750300e0390381e003001c00889030520090808000600a14040d000e510f142580119920b03100564ec1e1030003c01c02055503040900417030810300170070080c11103000560305403804090503500b8a041c02042c012600340c01455a0352154a5504035404200040445806107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 51206640 1250 51205390 51205417
    0x210227040501050609030a06050603100c0908120a08043306090605030a0b0708070311191107050a1401030f06031103121305120c030f0105070e03010b0904060203041403 74
    0x4248540400c011518140d100c0c0e4055070003007109038101d5602041c98910541d0100000406455140100e85405100100811400c0c40c007035841c0321082d00444024200c031050741c2250b54416803140780c6011405507610134808a4110000300300095074004a46c1200c0c880c2c004600c0d45040ca210843c030381c41820785c7c10b01c00103950b202c106104904c600d000b2840642025001811016103030768500507024401000c44040103042004100040d20079041400070003080507125803640c5c0840d52140c0702c410008103d10124103c4460f00c10081d10100300b00003201c0c00245a0286a0302d0555401c2c092611003002c00d0405030f90f000720900488a0388280310140d4080d4042c2030042000205040c5050b46e284c15003400d04400384481601a80c3c1440d002040c1e810903240c0400f60901e1103d060300d07017040140e20961500030a40c030344503451015841684600880d503110440d20f1408004d2600700ea45514095030050600c10005000c90200e40003140c0103407080940001307010342a140d841c01e42c0c100302c0840205 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 51207890 1250 51206640 51206707
    0x60311090a14160f050f090603040c030510020d0501080a0201020619020d0203010f061103030f0112140f100c05070201050d0203101d010306061409190e2506020303072102 75
    0xb503404401020b51382d0540c18224178048000001074424010010030f80e2107034400000060800c14070540700801181e001040351a000c60040d2844040c3d000041a10003ca1410000203440c1c2e41c0001c581d00b000d40c045e005042d0741c5d00c804441565070200000300d401055020828588012018401076000b090900e014094290512034010481010205914603e90050080c480700c0c158002096046810101440082e64014503090115200d4075920300d18a018040c108190160045080135201031a0071082000f80c00c4568241c80303d00540c20040d0001e0030600c6009a9400b03164011178200c0f100345c2050032010b5a8a1f41210b03006c441c81c0803081091003200c01082004141d01800000d00700500c0220350809401c4042410300c44014112026030803240030070541c05000e94007007482514007006440307035280c0c9260041d9000c041c503458151034040c0300d90000f480c1031000c001e80340500c1c4507581e02d14045007900b02d810b22542c219202d176580141c1c00c00840084803640030200c1034241098190101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 51209140 1250 51207890 51207931
    0x906213d0203060a140d080a271206051302030a0302030703030b0d0f020613030b0907030308090c01050702100212030421020d05030c1b010207060209090703060311090a14 75
    0x28a8a40c5010840d8480c018814000e0964411504030190790720140342080030f84c803079400a61401c0a503600a0804000010800500c0341c0c09041d450388004201c4005501c001d8144022204001a20a4941c078905a48400c400075045401643d0804104a180000d0f85211740009003000c9038104100c1c00340e4000106d01e0200742d018081c520f100d6008480704000a14161a00e94044002d008001e10407480007078890800c0300d140100102440c0c000c110f000491030f004400076516056404180d000c213600c3c5000603010a400241301c0303003181069481905192603a420b001c1b22820b030086000950281000308050b201c0d10801962059000c2c9d0900081c00d908185050903c1104041c544115001b0740314070424550030408403078010b40395011150f502d1b099110400451070b81034000c81c1d8030f94000034034042400300540241c000c1c8041210b074803200b40c0f42c28005900310380345484000d02101808410003d1482c0161080e68440e004d074a02080c128070941c076041d403100084412207a07811140c121901e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 51210390 1250 51209140 51209233
    0x60a0309050610080a0210030f0c05040609050913260c07030317160e01020a02030f0105040c062303060d020325050123210403020303060f090621 64
    0x2a00f007a82024940d08007820701a04c2600c8007100100a4000d0080304542209035100382d1240d20050402d400c2000204483d00000305564440e10500002504018022a40b0300c0c0c0309400d2405045c00c030040c1c54015501d6540c0e41800740044050b40c4001c0981d24000c0007d0103140003c15482d035003000900181400c6281c0546606038042c1001c00c402c14060030400702c01e2694660036681e074030078201117201034900c80040346070501c0000001e401d402507601c16803000005410040c000c2d84165802065640c0b01c0034121050755110b090120403070140b030140b0260503804402560006000340c040800e400d0160042450140c842113421100004500c0540d9081c18400410f80505801d04c0c01c00b080c5840c410395101e007034001d030400b540100400039031a102c04611022200c80404980b0054500345807600b00a0b440390011a000c601070491b240c1e42c2c01480ca0480c81c000c1c450007000b0400c16000280c00842d00800c4000d01401610b4459801014410103035410403400303014090f000d0a01e810844402c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 51211640 1250 51210390 51210403
    0x30d0305011a0702030d03090501110d0f060911040311030106170307060507030b03070515040e0106020709060603090b0c0d0605031c02010b06041202121f0203010302040c0e0108130203030702060a030905 89
    0x12042d0500c14000b402c0182c0d00410000140c0300103140101d0603401d00d0421900404400c180030400880015100f9400485034009030304800c4580e00c1000080c0d52242418241d9840d6903404034001c204000900025a0484030303240502805070002643c5520307165040004129406450880c0c4c0c000b089150803c103c900507107502c001e091509202250101000c00e07501d8919005042c41003c52060324680300d9007400543d8004c0c0740252656031117503590301001c0d440d02c14501030181c0d6603007040303c04140180640551b1184552040b213000d002c0e0740e1400c07980300e29004910240c1080da2a02ca0009060b43c0411a04a001d101004211080c0e14140406800c4908410707055000300d00500c0304001e6004840d20240000e601640d000804c202c89191103420542c08510382c508409043d500340f4030511250303010b18107984c0309036020010b407141a801030f68515001041c142c00200901d000848041c100486c0a010600c09001c4130300300011a40040d034141c001c21071030780002c2ea407040300710301f44403040188 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 51212890 1250 51211640 51211679
    0x5010b07121d060c0a021f1407020d030e060706060602070501020c04061a030603030d0903080105120114010605090402040b030f0a05010b0406090e191401080f0d020a020f04060302030d030501 84
    0x80c080e07103a0307900070070301d902c0c2851502c034450100030910384003080003844110201640205040b0345101002259001c0c2c1d012088000002001c00c518803007030907e14000c441e0400e03002400400e000c0b482d0798044490415405285802c000140300c0080010701c075000c0c800160040d500a05412420b00300020316181d110307100e06100d6400c0c12402c21050720003080964a40042c40d070b1039a40c0b0740d1944007007403451142052090801e0b15050b0801c09040d07000403240e050390b6046420006000ea020f1802e8281d507285400c841160080d0700c010019140110000d04102d58040c00142c103055691044102076001100c0d0b00c0c00d548070b040b080103240e44484c490540500300c00228642040d080c490300810325a00c9010f290b41c0c070385084c40800d840610401d0140d0201d501e0403000d000132100841002c1c8102021710a5a1482c41181e001c8000c02d070020810400301078141e401820f0a18482d000c102070304031442112a04503541709004000740c1c4003800421440a0161000301d41c0e540b4000c5d1583d200d09803200c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 51214140 1250 51212890 51212897
    0x405010f1a0109090b04060b0309010203100b09060d0b0111010e03030a0c180b070614091e070617040804031a040309050f060a0c1104061401090e09030901080a0b0405010b0712 77
    0x70101101d0303030041d00c0c40098404070140051506003c0e40450300800807500810001c040200801c01191015002584178000027242c46145c03d40c0d903900c10f00070303020713564005038846024031011090300115030040c1c5590344145003101d08684004005800c44218910304445500f00000b00b2601d02242e00880b0f07518541854101d015054544090078031501c01e0083c4640b1120020b441000c2c080d45070050000240040000e449508100d04125980e039102103803440303011001701c1c64141410340806d0700b07403c640c929202e03090300390040c0818841061001348212880c2106000206c04150540e001402c1082e00885140e280c0c01c080c01c1c00360006400e94030084c892540469011016211102907521a40c45420012000722031803504103000801b01d000e650b0414070300880043c1160303100428418005003a281c41d403c4a8441d040e1045c0620202d4100c0c00a81c410481900507500c203082e61f65211048240015030701c1d0781030b030006050342c1007a403248286a102190003028044000c2610b00103840303509 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 51215390 1250 51214140 51214181
    0x605190e0307030905150406051309021303060b0409080306060a020f010e060105130203090c09090c03010912031508060c030c04081903030c0503100b0a05040302040213240804020d020a0e0405010f 86
    0x89206e032071881240070308000c101c2d010400c14005076203c0c296001401140b44150340716007440c4070512551980780310548440c2e0600502a6850900c0c1c440c4400c850b80140c04a4030f90340c0d504081c80010390140307a15404501c1003011268030b24400384282807007002801e0142c2499450b100800000794041c69115081903c10801d000c43d54800007000c846508050f40c102d201681c80e00152400c10a03101503450b0035500b04103c11081200c136006281c925006070300c04000000440f83c08003030403940e5004000844e0b101c8008180c807010008055640706c51030328005c9180c561108019800c0c142090881c00403040e0503412032080540500070400390120500d4014210300d48200c1c90701256280340b0410300400d10019504010a214034203c070f0203150003510656880c0d45000780c89041c550f091140701440340348010000040d03100c107445800300008035500d03415980c40f16003c00000d0000a00201d0384501900e00000c1c22140940010780b0581c020000002d0300c6a020705c080d410385074090b29840316908141d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 51216640 1250 51215390 51215419
    0x130b01170706030b01050d0f06080601080c010e0411071202060403021c0c030c030212040e15030303040f030302160b090c0f0f03070603020708040f03080706150b03040605190e0307030905 82
    0x745400449910345004103200e0b9541d07006036154410300c600c21000c2801c02e501408280ca40d03401903000c44089004442e1a0317030307a6071584c5445a041010035070024030030107103110161400c0d4010728800f545000e405442c2a010f6580c3d401d034007244c0142800903800ca00f080100380b40d01800380d02e100c001c0320742d20750740c12180c16100105900d5550300003c080c00700c0300c40030900340b510802102080ca584c420f101079440e52242103100c61103c0c00c85202c1da40c86c0300e400f0311440a0502000b5170340a164003042c215000d1440ba0b80640194000035107205c41c070112208003501094100d050343c0d004494404c00b52442100070710a1250003ca8100302500520300c0320307103c01440e180010360004035134a5282c0180c03504114a06000309204507481340345140c0b003404000c0203008909004248842c801c210030040210080d104e0180d44846100c1d24102003010302c00280421640c0c0c2010754800d0401c60040c8800e10480400c030210b9800c9044680c65900210b44d5404054000740d910003e040201d40002045010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 51217890 1250 51216640 51216643
    0x50c120a020a11010f090c0906080705010f02030913090605060306010506090d030521010503160b041809020310150803120703090212070305060f0105100c2603130b0117 74
    0x541400186036000440e000c0c00b5108070341243c078060542009021800302c480300d52020b4003d0240654a0400c03c4000140780c2c2040e00c145400c40700301c000500203051030030005440a0407802010301c00c6d4041000b20100135582c595403969800c078480e10009503400b40342030020440d54003c1c18240240c0c4032000500082c0c2d6418150742d030710314045640c5c00101d00c9030b280403507080c00341741c1908040e0700e40c1ca4800e0240f0002e8008090590784150221103940e003540d400103005108a100740da084078400c220500020401510803402520302c04000f14030f0641d150f004ca85050359901c41d011149a4481040070300c4060009894010003003131008505140c07810018821115000d03014406143c3e45018000031500e802010040d070007800025640c2c3c6954034184151a01070494401904100c000d0000c00c20b880e0070b044480840d16660354160701c008441e070761541709004401812001c100c0302c4200422050001c070003503205040385180d40c491010186002c0038000f01c11303040b442c00ca040c3c650a190b0083c07130 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 51219140 1250 51217890 51217927
    0x20a030f2f0102100506010309060501030b01080f06010e040209070c150509010b1228021f02100504030f08090f0109200603010e0a0207020402090d060504020127091a040e0d0201050c 80
    0xe91344000030709498907801600100800d4000414036418980000203100c0e420342d6280c100c4079101c3c20307030764034603d070303c8040340c4602d02401400507901001d404a070250a1100c643c960280440c01d0640c2240c140303031206100b044403025061170306a1204104180200d080c0510701811100307582c02207070480950005074a62507543d2031881003d5104884403042413010303034124100b9802600410403000e007001004000d402003540e150142c440d03007a14128041c407a21655105a0309503030b428040394094482110410800b03000581580311b01c40d041039140c0801e104860049108080c0c4600d01c62000d007000711584184160984135032020701c010007115240f10052684125107600050b502c040520004000707001c0c00e106150040c0f030302d03000901005040d5110600544c003d89030003e2402c210017652052804054069007514251941081403881541200036600d01212285203035010003808501180d4841c088104594086100d140480741c0a10496800c2900c15000d03902e40070301d031288100f2160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 51220390 1250 51219140 51219163
    0x2030d05060307031208220c140a050a0b0403050f1929040c080f1b0618060d02040e0f0c040b031504090501060617060f0409020a030f2f0102 62
    0x5840ea000a41203035014807030000039590081410440700d070440d800034407841c02101c04880c41c000c0c1546c03a940c107a40c02c105004e02180c0c000d81c41c0c5c0c0300741c0c180010201101202d0f042c454001540729004980ca694114040024042009200d6201c80c510b00b844d600c0c101c01c4134400c1f141d580000c21450611142c95886002d41038100201c1c1010001c2100803030028045108858200c891800510040007400e0010004452000088601c9904802a600e071900309940340050704170400c0e13038424010300f4000301821560780d10301d104a48030401070700030a4460f408048100c80301940001d00340983c1c600700d420190800340c0107201c02c1c9a80380031b090500f090b20a0380a01c100c800c0d0702100098002e803d03a40c0825007048040c205102d03848840c6081030290150740265804550070a03c2010740100301c40300f052181e1300c010309441400c01d00500b400002c000494007640c00c440ca00d400480819071a40b4800e01c00ea10500c4040c0e66a2009207100001c030f1340c2d00380c0803080b80e400c010300050540e0b4002803480181c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 51221640 1250 51220390 51220417
    0x3110607050f0f0a03030b01020303190b03190809010f02061302040f0204080313030b07030207031d01030b030604030503010f211704050a080102040320030616030209061206010f0f0203 81
    0x8080505020740303031040c4500c0202c66032240342c204001507103000c03440c049000c0c40f0382c40a100c100c0c0d0010041e0303185e001c01c80350741700e0000c0d01401c07020100c5683d0b0032041400320082c0a68020032400d004441620007501006d960081c400915070020b960720420144c000341a03480038080c5070412602ca175030000031180010340318548480e010844540d0580c101d03030007400314030101c030340d0381504421001c22107609120589611883d200041c2ca01030080c02210300c04c50785030b03440703000c880e0464050864601110115031f0406a88410174002c0b52802c00c505800b5038002d8413056103d601d00241d04801c014550410100c2c0d55042d03a1944000369080380c1102c00c5607028803422880800a0000049800307142d000550001403034800040d02441035006005990203144e100703540ca480000d001c81000c2211314100c0c0c0692058002601103a07444681ca81c00f008245005071070009541c00181940c0c000c40004506e003002c0fa0148070b213641c2c002d4188507404060b03080c20440c0c1c4000740000b80d12802910042c0641 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 51222890 1250 51221640 51221647
    0x10e09190b16110c01180905071107050d1a060312040b04030b1609051203120c0c1504031e1704120f02010e061306090203060a0f0c09031106 62
    0x2582403091401044124402124150480c2000d00340a0402d40d603851200004110540350b940c880e02d10180700100c40002050f258480300011501001c0c100c518480c020840a000b1035250041d000d485e000c0c0c00740740c0c0c03584140c5001458a60414140b40c1c40f95200718030498403e0000b810003103450650401c5613091003c9662030b400828100380d284004002034020001d00030440f80c0c504000f07082a03e014003404c0c0e60030b50302d207103070038402d034240552030b00c080740d9080c004000c1803512082c1036900c80c1300c90083c0c0e400c082c10184010480d0310705468000b5000801315203118484006c0241111070a4042200c500303500345501e01504036140310b0001c0b148e20441412580a2038001d50000074250444d003a01c12892078a810851f086540e1680d07034600007004030110052aa20501501c43d4030f04401028018a0701d0300320000509019201c4d045502c142c9524060015a42c1403000718840d4031104400f080c0481d0007110a011a10070b1306111061000c60003007480442e80040440340412300c00e607181941e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 51224140 1250 51222890 51222901
    0x90203070212031e0403031a1c0204051902161101021911030712060e0106050303070c0b0307031e090302160b07060504061b0f0207051f030519060308090909030a0503010e 75
    0x301314200b200441c02c214042c10a2108266240e486a0b00550b40001d442c3c0128090301d003088245080016964001d00c00140000e01520b4075510070341e004480901c0d1001a2502d95000f40c090360003c1d01d01d0045004408104020702c8601c00341c03050031500c24030240144180340320203225100821040034108110403c81864162420810000504518408040440c4283c03070039401400c40078202141030350030002e0010b46420008203643d14564491015803c0f28100803c810490704000c2c05030781099107400015a4074204401d8100204d10840ba0100359000c00b030401918042e00000d400034800c2c8084400c1104903150300c141d540d980c2d03001c10003040c0d5450f1810040b021300001c620942c2440d10300310344001b985411000e2a04005416020390340b01c150760b1300400ca4007600036480d84030b01e03044035095000c0c2544282c2c00709501051020b2001d2406101c0040c2e41c0c1103601c1c40d0001c50b6034000014500641d440c01c240b00c0c0383d2040c0d08000a500d00000210002d084d4003061180c00c803c0e68408002c81c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 51225390 1250 51224140 51224161
    0xb01121a0301140114090115180f032604121e06020309150c030403090302012003030903040f0b0c0a020118150503010306050907140f280f09020307021203 68
    0x1200500001c0003800b501c050f9000390f01408100380315804001100341480080360030031212160485a0b0242c8101d0541c0302c5842c10341c0c036089c01552100e9003c03d40100400c9040e005540305000d1401034165100d4001a80b80140c000035000c0c41c441c1e03c0320800e102c1044041d0208000c062040d030300c42440215070b4400c0340817092000440800420180c0040100801a20002040e140b0500a49241d07995611030740640d0095200c03c1d02c0280005041400c1880954003c0c1600320810304001c1c090011903440b12a500c0c1107030400d803100051038000007410000244200d445e04090403040700704a25000f410803045030f50322003172640217051001030504100f0b10b8034070080e03207402404d903da820034009a809000410716030090004484491800000c5450b40c1c00000d00102505c204501d1500010201000c21a500c0d00c25900144e020012170450280b800c0c07100d4048010548014007241d00e1810141c81e003031100281d80040380c0c101e01c1401042740c62940007542e1746269440110081c0c0c0d9850350000107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 51226640 1250 51225390 51225431
    0x14010f0513060e0910181e05090d030e07080d031d010606020601050109120f060b130f09170309150601030b030109050d030e0106050108010b0a030e07060e0109090b0112 74
    0x240a0080e04901c0014040e400c03605625252508075810702c0540c2c1c94449240d440000c81c014120000c49402d02c80310b40650a5028110510a00340a00007480722418000c0581d40300303c0d04c0c6411034100001e40345001d9014014030400401c400c01901c0c999003840c0d28543c0c1c40812001c800101a210406c080b40c20340c40d0681c000e1041582402480b070b83c0c1e01c07000082d694403002c5c0b01e1a400290206400600a01d00741c004e108a50341c003a61861403051541c540038040c0c401c400c00700fa07101030780d101400803054183c41402150254040c0200d605c0201c2d080c06510100c1140c0102d030308140c00c0003081494480890b0a03034040e4000038070034440d03031640d2004034014003a032036a0503007640c03a2041440034010001816001207241d0380c1e05010040e1451082400c0e0b4656104840c00300343c0060060010004241c05000c40d401213240c00500c10902d1503000740740c0710040d404900441d4512690085550384251142c01914101c031040c000e400d20300f40020706100100901200c03640c1d40d0542003148204130b840c503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 51227890 1250 51226640 51226657
    0x709050307060c110a080316020a170a05060c0306010206131109010905090d020111070f02040f020a0f0e09060d020105090111010c0203042301090302150c10140a0614010f05 76
    0x4072425a6120b02010b44111262801a80d901599124110382c034078213145d0000584409001850500003401c40e1920525000c40f01203134403032800403003ca01e800b6500d01150201100c0c20050002da500c5081413414a540503002801d155802c000300803a07079800003146038100c0c03644035a560314401241498908445004802540202504000115416030750000740c0643304604c2562158081001700381e00300c40b440d1114062031242403010a000c20300e01e01c1c18404050002c0d10100d10b4a00c240200310480e401b81030040040750080c3d4400341050380c061445688400309803019800c904004000800f05008010024104040050542617a903c01c02040f0f00d41000c190081c81140030804000e9125040f41c0a01c11103840c1441030000c0802c1103e14100003280103031542900141141c082c0501100140c1803521284010445d100c08040200f00d0409180e0801c000051801c1018860121003100641805021070914501744000080400080e107041024204903000e44034400d02035420f80101e000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 51229140 1250 51227890 51227893
    0x10e03030c0702030c01020d0206161803060c090605030108030405060703020a0c0e01080c030a08160f0803090105060f03010b0919090c0e0106031104120f0804120606030203010605030a15020307090503 88
    0x144a0001507031005000e099100b1420303140d241c800d003801207a4a8820000c0d440042e0300560106403108030b00c002610501e00d0300c0c60400c0c0e4071082e0702c0340f0241c19411640101c076420340e07800d00d43c0000d41d4814100c0380a080c00e0320b0400c0c0703194917062501d56280694080c1c18400e840c000340c0f07002058002c10281017061f0740116440040780d0b03a80420600c08500f4800c12130503000f07201407035801e4540800d55641d01d9070f1010340982451045500304119000d102411202c800e40080480c0c0445d0200018510940314900086010b151100c240211240b0108080340680e0400c0a2609140c0d5000e4195a0001804c3c01180f5620340307280a0001a00d0308810103005029020b00210f06a8040c0030b205050320345588041c402070f80303042c034072400600c141d00c1850103882c8001480f100103004501c07400e44050250300d82c641842e0b1520345108880900e4202107401c0c135038540d070800441c103080c0550301c02060200c0c0a03004038040d5448900c6155038030305402001c40d07800000105110b004601d04006000040c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 51230390 1250 51229140 51229147
    0xc04050d0c050102010e0a08070615120b070e01110a1104110a030b030d020a0b070f0302040e01080f0c03070503030a0c050102070c0806090105010905040c06050c0f030a02010204060809060601090b0705010e03 91
    0x81c5100c0754241d60182c140154200311030240c3c0c00c070002a0303407070710161300080f054500a605c0d19400c00410001c00303007003030050182c000001d020440cac8818207611402801e0000290070103180c094260b9a4a41c0c100341405108020030030304d5078006c214020b404e0380010800c1c8080d00402c0011707004104007140070041200200d201a01c840e85580408401101941102c1182002e26010f90340d0f8a94502d008200380300c8900041d505507c600001c6403900c119040140c02e00e07840d5482a4003a4100b600320790481d0f403010b07010180800b030400950a00c1c1e44240c2c040c21410b4200004a0348a11418030340d01e050101c0c0c0c0b660281000b1003541100c042e03580040145039800e845207100b9482c2c000503102154150300309400800d401313100e0300c90a40120340c0101c007100154640b180544485e080014241401d00500010700200081440180703900784c401da0005a0361420309201401c0b4007409010a100d50303101c00308000c1d450360083c0f040b02c01e4868418819403503252520b00075000d0030040240c9a014000071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 51231640 1250 51230390 51230393
    0x507060509101104080c06030603031c0e01061410170114030c0603040302060103150c020601030201030905210903100b06040504020922021207230d150e01090501050a0b0703080c04050d 81
    0x1001341c000d541440c010740d81c10312441d4007004680e01041c0c4500d98140c004100708032420241100c4a6a030006007480881e5202d0310a00d000d003140d100d50301603101c4008102c40701d4400c1c03400400701e020000190030300120007880f80b80089494101405500d4000c01c050101c0401d903581000298884c1e00f00074025580ca01d071624000b9101d05080c8411650154400215806880d19005845c001c100541c000c1a943c2c0c0780d5001140500b003801c606407520b00403804c525101120340c0403484c05500c0f03c070640030755817105402070510301010446a0901e480c68403902035015a2008204c904a4070100d03009a1105c0850001908070810344806020061198042c602c00c01c505d44c000d00304410f810010f418255035520410744039039290110321800f002c0c8040210100c2884440600a082e0740c981d4005440705401c040750341b480c40749400a0100c004200c0c010081d42010303020b800c4c0544001d072100c0742a00c0c6003240003141030041890007424000840f00182e1264104003d480041c0801400550380070b616 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 51232890 1250 51231640 51231671
    0x1180b0409050106050a0509090a09020d030305040311010911090604021b0604020a0f05131509020f031501020a03050304030503041509060b1206060a090213051801090b03060106050706050910 84
    0x684100380c42607007014000104c4030300600c242c0d01e24400701d403250ba140285000c204048040005c0c491024542d4860400b40983c0f59620010a0305101b83c80c00a201e042c01d09001c0c120117000025001168181400040013942014120b42c0044003a22196019180c05000070701a005540e1003070800d210400e22010b60040000f07955000300d0003552426802505c0d21650a44103042c0d0140c0c03a000001510a205000c0e0315a00c10700c05000d031020520f26482c0c9440c0c04109a910a5001c0c0714400c6010060045814500420104c01c2c0c4c8240020080c061311070b6009403181c040140040c040c040301100103000d0000e00f80038070780c0d050446a020000c500c11860558005d0180703480d424000c00c0740c3d00580884090019801e40501070007400c4190319890804104081c1d4000f500303084858942c80d10006081e2500240781603c1e820f440700101c090341c1802005821135000e400900d1290b4084401007001c2d54010b402c0f604016048100814903544807401540380a03e50101d6001141ca000e21000c82c0020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 51234140 1250 51232890 51232897
    0x30403080f010e0709060e010908030a1206080109030903031103090a0b0d0f0c0e04020d06051003050405061308070809121005010f05030105060f1c0c1d0601080906060f01180b 77
    0x1d81c41451400303076201c1c1c0000d40d440c002266904041452a00d00744050f500945209500c2e0381d0514201110f0b40d203e0b0680d81c10740c1c11403805a0042014001d003007550200a001b1103019000c1000200840c14907510010300320307012840083d00340040c2c480356021070401481100c6c040c00010b4a440005959011510103a500110b8100b1440b4544500450403c1343c40c05685440314a40e99404602e0452100f044000d503c19648980072550b603a1000401c0d03100c0c0c072958883c88a171074400140c1072929007403c170304104000f058066000002d404020005074900e0913140d00c640c00107402510303003805501207404100501c040d9101c03132085000c260200c1e685a00321606a03452602a140201d582e070303090500341c4100341c40490740030710304801c89400c1c3e0500703007294951014201640c241081240e2036103131903880c0035041002c00c4100700b620070a150444044d5960004028030f8844454942081c400381c96402c050280f40c403400e075562800345180c2c880d181c1c610034010080c8404803203130b0307503403403410501d41c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 51235390 1250 51234140 51234151
    0xb01060801180b01020a02090a0f11030405190b07080a020706020c0c19120602070507050d03030b041811040e01020c010c050c011401051e03160308070201021614010e04020c0303040308 81
    0x842d40518280b40229000c0d401400c075068004007500b02040c2d00f00108650010841d07402c0300d40d100141e000f0461240035030500c607040a00b84980d00c1c1001d00340746052100303a20b2203208450120011900060f650b09240b5400561840d20f524070740c44044103c40a4030880102038903460021032400115200460000307410042140d0303954942c00d008041004079080e5118402c145001c2c9c111038004210300e03030020400e1621a60980300c8807526a40002c0208078400d41c140c0000759194912421820584075444101940140c40c18188110b43e0302c403003641504188645c001c81e00c40750380c40101c440c25010f454a00003e00008d00c814408850000c00640080306141015801c0401d50040e011311140303200d0503900c01929000781d02c00c41d40700885020b002c00b030307686402d41700345400c0528041258620502031446920141e0740c401880c0002498a007131040c034900e40001010f0708104982c890010307040c2e4000c0c21b003880356007160b0950006000b402841d951445502000040004041d8030500b0984920b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 51236640 1250 51235390 51235409
    0x60f100506040605070c03060501080f100b09040f020a050603070e0306060913080a090b0a05030a0c090f0911071406180a0b0402010e190905010603110702030c0409030504030b01060801 81
    0x1961000014011004244119030304410100420b100051140004010700c030300460180202903030366a02c000444d07800b40e04c500c80340e400c5070a55688030340b0305000703502e503855220005105410304c41d4001020740c0c0c4098002050505041c1c800b4003107484d90b21150700208001810b80d9200d10300900041c20340c000381202e49110740105800a02240713000522a400b6804c0c09000911415056545c40c40700d500c440001c00900040c008000703080d9006400803c1c0040c00d558810340ca0742050b42c2d40400755030f080c04040702440920b040074064040100304000894020010124442182c101c00d0940c40c814000060b10f00d080510b00207450303090026403039000b410903070341d04594038804945054540c860040000c004d080c0280c0403070095840340d030004043c00c00c000c0c01c280003414140f215044007425984601d400f06e0b01e990042044940620441200171100703890a8a0a1529030000761162440c2000b944115600c03908002407501c1001078901a5a100c01910001e503154000546016000d20421050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 51237890 1250 51236640 51236671
    0x7060e07090c11030c0c010e19090902010801091a04050703150b0c0601080a080405150405030d0c02120703231f09051b090a0e2a120d0906030c17070206 67
    0x2844000000c441880e48250040d00000c9007000c01125081488c500c3d041e8071107100c031035a440406c1d09036011401040601c9001a0148561002400c0e20805030311000c035152403c24140d0740c03c610200e0328204500300322000620390703440c40400c0d03005080c00314103401e4804000201140002c0040e00078801b460350941298403603a070780c4040903a02c8189600050804030248000c10090078491003543c591040b11007490706241c1c03100082890045030f83c021600281c1a07041620a5043c01401604107255080243c400c80342103442d61a40020111b11b2040840c18402d14442d09203018404440810304038100d1040d004044041d603000303003c02c2202504c15016103400e05450310344600400003840c5001e0801055691450388107401000001030b162554015040070b05415a10007100c04407280b00300d170000100c01c0360340e401e10501c1d91203044101255400809403180b0160490031741012668a071401080c1d260600108491022400044505940341c410a00c0040b54004c500c2610a015001c1e00c0701c0d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 51239140 1250 51237890 51237917
    0x120e0718060510050d0f180c06030203060303091e15030a0605030303041104020c01060e010f06020106050301050609041704050a090501050f04090b0105010507030302040e040c0e09011a0607060e07090c 88
    0x32075000d40b04155100001c40c5030410a50f00a1000d0810903140b03042c0043e0303001d01e01c9403c0080d1003074800e2100300c9081008800c010844281829009043c03d89011800c0d80340c150302195a0380305140c6010703c03e901000005000710021103e01c01c0c01d800282441c14070708507410031010260800c0d580004d1150901f540810281000010340380318940046903041458880f800f80002580460f03a1150555264403000c01c0e50904000c59a008000c4145403800480c0703808402030031620190032603403090341030100b4011940d942140003500140c01c118419070300c401640a55103140f0495100303070b40000c0310b4000050801010b1740074504a40d801e4407602c07078035180c08007000700f114201400181140c448800501080d440345018040d62486030400600c0c198543d03000c00c00704807044070212101400e20405002112903440c400760040c0c00e00c4001c0c400400b012440b0341003040c0e0308910901660340030603440c052100d190011484001c0c0b070025940d29035110400100a000b0160143c0045087d5100100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 51240390 1250 51239140 51239189
    0x1020d0c050c0d05031b103209030c1b090903030717180106030b0402030c06070519080d0213080705010507030203041502030403050d0503010617070210050601120e07 73
    0x1034168010003038144092034008000c00300c85a10710a880701c0c030050040302443c55138803222004015400d0014003d04102c0101c0700d05035980310700d1440001c2d071004400302040044003002100c41601c850f641009a13a095900c91440c0103800000c501c030700c5105000e075601c451400c2c1a50320034000342c842c159a9901c00024581d607110564800e0001020907509100103c4400300d0107405c4074078a844010079501040c00903007590b10315002a01c0710b02c0c1034414002180341c10040100719641c1501c0490a0005640b0b4040c1c50b0702d1030311804002d0015696845081160102c01c80c1c4222003140d90854075008a1103240346440841d000d00000e81c41400340214136903000c1c0040d030f0b007800d5156001703610702414a0502c8500c4103401c80098103600c411310010000480c107201c0d0790400c01180e59826120340c03400741c0041000000d002c00c1d2400240d0b20703051201441d404500071061134085800441c035510f4040c0101d910041840d0b103e83d12608e0551910b95400e00810f42100700c0c0c0c0c200000142030085c40c90f050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 51241640 1250 51240390 51240407
    0x3010f050619030903030b0a0303051305010c03090b16060e03030601080108010209060421061e050109020403030e010804150f0605190f05090a02070c060f021b0306010b1b0d080601020d 81
    0x8142100c1e50907544810b02e11980095a210b480f0346000718840702940c0100d01c4800711a00202c02103180801c1100701e001c1181500d40051009103042061698680c501500c1c4410500880758a01000119500300103c2c0d920326400d1030b03600c00380c100311200300032620030344940042d030740b0a001400d04800051460814000d646034200700900c03003032900b031412800c40d04205429400c10000d6568855a0000c20f5151144004030003042c40d134000e081070524002c00445405800000c215441440140302095000c80c24500703030708080c00c0150311030311281440c00c108491650b901904070b0a041e046c402083c15500310000b11681500d580300d581d0001d00655031069098007881e14060300c1000100024a4002800c40d0400c180700d03001071500d019501d88068a046a400c0030f00403071080003481d07402540c104403a101d03140d0184204030140a07e280002e84404061141c1c5440307510100e540c0c10805806040040c904900d9800c80d100740400140140000204550b003d015002c0c40d200d420390705008520342d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 51242890 1250 51241640 51241657
    0x30f030b0108130507030501140708070807020604060b12010c030e150402180618100e0906041203020d060b0d09030e031903120209090f010f0602010c020c060a0203070b0a0203010f0506 81
    0x2800140d0780c64061900c41401c2c003da05030390a106400e0004040360342889404000c0c0b04003003421810345407031100a44030390750240141c1c08101c481b03020400307083da007c01c400350020b80c482b4010820010800005542c040c950842c0003055103004c0700c1000143c0c155111424490254040c0c40e00c001c408043e90034150001c4501130b421040c101100000c0c0072161495a0707019500810b00f0000081410740c038012520102d50040121003114418402c541c076051105030701c101200c0040c200d078074095880c1100e1809012000043c0360300403401c1504002c2907004131002d069041145a120901220040c014141e5204140c0210700b4800400302c880c00d0201d02042c9900d82d0003949079416400380da04481e1504040083d41ca116820300c4151501d03035400c1151801406000c1c6000380b02e5041011b0108510019070110040d60715003020400465008901c4032082039086402a880751f001d80000e9042d80b240c2d50303000f0040c0a03220100310442c40e40e60b0186042e2a9200c10038071100381c1b40c0051010b5445103104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 51244140 1250 51242890 51242897
    0xc170d090816050906010314040b040c050d02060d0b01050f0703020c040b010302040807060e13062c06030a02010c14070e04050d0503150613080d02010b01030f1a0d060e06070c030f030b01 82
    0x41c10b000f907041c20212590880010314000030840242050069106025541110318621140a01040c84540ca0aaa0242c1011212072001440e580e002980358850521a100780948410b140c001580c020820384030300c103c444c42c05581c0c600c02450b0080d2200c0804082c148601c1c46e101c440304055101c1e2007520709031091300c402422402d0038200103075440065904181d60102c0c1040d450344089040c0d000300170042c4a14041d04140720b0781c40c00380c0e4400341342e041d1941200c030f1031003002c21a050741c0006a8056454080c06c001504841d54104840554040480b2000720b11884200044030100915158401e41c095019182101c03150360f0200d5607448155602ca40c0d82d40385200c0e030191460420f0040440d200d0f80c8015000c0a075a80d8101070520120300b0742400980d548810f06049540c141c06000e510780d0307210200b000310f00c5000c411300c110340d030011007200c1c02a40700c46005d80c01c0080683c403a60b110001d200c1203901520f8010b07001485441548400c400068451000349842c6e802401080e403001c40584 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 51245390 1250 51244140 51244183
    0x105090303040b040803100b0412120c021e041107050f0d260604020c0d02030301090e0105161b0c140a0803030f0610050717180a0e04020105070c170d0908 68
    0xc40c0c05d11250006000c0e00016152103000042c03608280f0020401001030a0040d001003400703050136076144030302c000c6210521107032109050060361000c6990000441107001c10300c098506002160003440c061503600d80700100002e0b14402e000780068000110710070074003280c11480c19400111020800580c06440740d10300d50304c911310700280c0c0c6001141e21100c040d000500b0040c005214503d040c2c420b0300c107d009600000018402d80101e40035990191030715074000d000a08218100c075144002c00000d05080000c092030030000160011034400c0010f801c40c510010b856201c00c14010403006000c0441d00c56500420b0001d5650f00c04400c1c0ca110b80c0f41ca00440040313617109014800810b803504424000c01004001d00300000d43c00c9541100b044c0c4c50000029111551303070816500c00782c2c0d80e400c01d41c403a2200c16010030a4881400d02603030300c03944c286016070311542ea602d00350562030242c1e0040c0605480412a50300e00d2140002c01041145050b99500c0030542c0c3c03a041180c940c0300c0080c445000c0d19600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 51246640 1250 51245390 51245393
    0x22a0f030c0607030c1407030801090e030405031518070801020405090f160e04060b0f041508040206030a110403021305090105010911040905090c060c031801020d09090b03010b030607030b030105090303040b04 91
    0x9602545e85444c0714181a0350b903110101d900d909540c4000d02c03c40110701540018480c800452207445010750201d00258649420040000e03640c0300700d103050444074101c031400038030100d1100c2a10201309541038104c5004075168401035010350000e02455000d00b45510014032146d034024421809804002c0c0481d243e02d1040e2400c4940c10140a40c15400c0b944a54001511041311001014a10b0114212585440c208000008880c020922a104100c0c0c6202400050382d25103003200d07000700c034407840000d140303203520500d1b23556014640c00a035000411243c810030f010843c2e04841d2003404894000c004983c0c07201c101400b1107280c10004542e46500b803006208006441e03115540008462044404402d8000d000449640c00100c1c0c0401541011a1104588c0c4401000c0000f017102400901032010b69050010004050351007415031136520f450148225803000e52064441c4980502607804030310f820784018019000200f5268000d40c40e09001880c40840481601c2c01030ba0702010350201034485 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 51247890 1250 51246640 51246647
    0x506060409020a290412020f0d08030105060a0c05100212160f050d060e090a0c06050f090105180301150f0603020304080f0318030a0c03031d0a0204020a03022a0f030c0607 75
    0x184c0c00c84141c585200007180e88a446080280c0020248104401100000761050080d05c40d82086130354014641d10310744a00045005d401e4906480080c0d41c102c1d26801c001d982103c80e00910003000e001e90044902c0501d020a2540040c03000760004006140c290f00e400340219800310443c000b00700080d51004d0004030a500c108000d1070002c8502801040e150b403076032105503040900b500c00d140030740d0029201d14100002e04241400078101828403078200301144564120303505c501070314a030400c000024103026840180262012109000e8001c0200c14240d01c05100600058051700c0c1095080c52000940f4074420f0088a21456100a202d400c1c00b100b0070022400b0f0f000500112421503c07020901040b5000b00090311103c400ca603201c2c02e0b55540303411b0207812580e0244d204ac03540070586203c0308482c14001440b200e900d50640d0300583e1303036540d032000308c00030b02480700410261101483c42d85640d010701208030740100100415190061411246035559210f040440d0401e508403a00007000c4500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 51249140 1250 51247890 51247919
    0x703031209051009050606010f0807260a050109200904050c0f0a0c0c12020d030c0302033901061802030a06030204020706091109070504141306030c030506060409020a 73
    0x440800414100100c1c2e030381c40d081040f980604000303d0740c0c6078829000d00c0b0040046580004081c201f4810007141028010300c07500c070041c15032081c0840707100004000000e195a6920b161110781d0116103a0800840c4140904000c0c8a02035000d41018000081c4081c4c1500180e0013012046006252100d11010310015107002032007254002010b0025000940e881c000030014032907140e580743c10300005444d02c0030015860f42c001940041d009000d07540181c070380b0b02d4004000c513010304024019880501d0124034500c103ca174000507034845400c00340c00440d411503a007082c3c5070300c3d511560424401034036040d00300c845a00c9503c0c065580e40f0303807040c0b8900182d8019030300000f1281c0042641d503100d40108080e070b84031440072a80301f03640d00303681004d000b00782e9031082c600b01e0308441a05035070400384001085030250f4040d031042655016001e000d69138441800b60b99020300800144502e503583d06005050000c9444142c44600491000800e81d00d4140729107002554001c0c41c040105042c480404d02c0c0c070340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 51250390 1250 51249140 51249167
    0xc210408070507030503031b070320010b0301060b0a03050a021603050f13030b01030210090305060a0b010c0203060108060f090c100305090307020d38010e06030307080a0302040501080106050c070303 87
    0x30400020300491024081c1002541c0140003c595a081c00200300701b040402940c0909200030503c451f00000b40c2c8128901034441f2029960340d4815020103a15006150300651294103602e8104006501e083d40d070040c0c856464152010003503684d17680740000c241d100d910500300024503140880c1c0e000a0244c00607100e140c01d02d81c1e4243c20310717124081090303010401c2e40058a01c000c0c3c00004000318640842582031507a0545003920ba00787c55992040d40d80c860241070750141d1901d406170400207900c038603080b4000980050440c1d0700c80d44c1d1540700e2900c514081c0c50303e52001d03807048000760300510009250215482c01421b540750307044a28004400816003c0c0c1406c085010030037804025948030400141014022005280344540f091701540c0090740400c4806c17001060400c8454501121744038260441d4000c8606400e540c0d100b00000f07042d0720941c2801030402c880820100300f0a54540d0180c02904d9003a00c030002166203072030040c0c03030502511400408a60202c1003d00c0081e20514042480e803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 51251640 1250 51250390 51250403
    0x103031404030b070201051b120c0d02090411092409190e1807050d0c03060c0212070b150105040521030c0318041a0307030b040f02060d0b090c2104 65
    0x42e03200d940c2d610020384196002c4005030f45543c1400f150b0b1141c80d2015a000303548141443c43e02e0306031000c100480b9401001c209401d070011a0311030780d0f0070003a0116000220000d03c100024001481d900d03140f40c000900d458000da00b16250300d45051281c011001100e261011050b0505924030100072041002600a14184842d080d00066603000c140c0d144c0c0c003030300703101e001212003844c80050145801ca8551083d44100d03401e0b0700c107401081400300034000796500300002085000d0000340c20303482c01c3c1c031000f010a01c2c2d2100040502c140150a0815401640d0b841d0340030b50702d5201d00c0e004544074000e500032640d00c580c1c4a000340d502d0700e00707281041850685030b0080e82e04000c5a81d5010781141c00004032600c12820b402e40c108518505446135100c5e07542c042248135903c20071140425998982d43c0001840c684541004c1401d00000e2140c0c0d410281c2c0c001c10841e03482042c0900c0e0000b8020143c1c0081c081c0030000086008003200c0350941e0a1008510f070007000c0d94840000fa00c040302c2014109640700c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 51252890 1250 51251640 51251647
    0x105031b01020319050d0c02031e07140d0903051b101d0303030112060506030703050a02060c01140406020403030e09040b0601260103051f0204140402030a0b040603120e0402030f01030314 82
    0x13164002440340d8802216140d59403075290404819090700c0c45c108013041150030030494040078040d680031ba6002c00e544882640c1c1c64028a14013150f1403c5485024941c0b4400d00610900c2554042004410307280b0034010303503040c0c3e001c100043d00428003038101c042e8494210b64104e66524072030f410318450900c040048130440c950604c08203045034400c0e00200500508543c6c02b0091100b58083c09800100c01c1d070051204038907545549840d0000200003e100700d20001c1c5a61601100f50003099403468043c0d0040c0c02410189441d00003584280301c01c40124210301007a41d2245400e8801030b200c0c507000b4000041ca41d40d0030004403404000c071540312110810300c91081c180c1c1050620000c0c0618410300042c040c48900f51652600c40600a89050080340104000e00161076071850100d21528141d50168898858612200180c030721800c41a40240c98142c0000138803098500302c0c44030030000d0b26810740c5185c5c01d8080c042607200c110344000d0851402d0004100181c0314401c551844211000480e08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 51254140 1250 51252890 51252907
    0x1409100c02040b0d0506070207060804050703020d1b08030405130207150e010204081605011407122a0b070305010603110301050f0607020307091a0904030219080906070c031502030105031b010203 85
    0x1440c0c04c1d001091303030f40380c0c805001c10134400d4041180320702030042414078103118642070f92a655030f0281800007d0040c2100c00340482000398650b0366980c075110040c4480129511207030131035601e8229100381c5103c0c1009003100764886406200b10f9000e586c100034842c6620514540302809800803070358840196600b00000110004280482d150300c03412003404005161910700010040c42401001031344114040000a00245c04070800401400d0b160030714400180081240c0b5003107522211500c2918512070000ca010440d01100f958894020768408108a036218601101160031010120401c440104018020b92801d40d0442001d02c40060103e1718000403603012070305207040e42e0310031400c0726201d0400d03416100000407000c40000043e5403048840c54151802580c407140d010380d80d0f40d0307845455215000e2082440c1201c42000300608040c1c2e5a01c698504507000e54454402603814400aa84031020782d80c250003100e04903500240105085a004a101c40000b000b441206040d884200821030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 51255390 1250 51254140 51254149
    0x30d1127130c08011d0106020d08071b060903022803081f0b0301060201050604020a0504090519060b090102070807031a070302130e090c0901050a0b16050102030c03071409100c02040b 80
    0x31851800780d0b8444106502d0100903d407181c2d0b20782170900110400b43c0c01446029130005600803007a4803403a01090b01d03100c0040c2600c1c040d510090954004258007018400e00c052a000010114801e5080328010b0902c0001e001400040200e44040d800d480280000032900c9603800c00d8020b41800903c031a044c9200c0e150f98801105540584040040400100422502072040d10b9000c0d1040e54254075020b41c044004101d449071f03000342100a80c2ea640883e010648000c116004100501e8040144940b156012921030300003d40640c014858800003068010300450407400701d9621001007080c0d86030509015403605401040f0388100340d400d210305907401002d10304100003401e280f0800c0180d41002110507040c082880000d60145182600420541c6c0700c0c1307103041c800c503031480c4c0600362103201c0301e44519500b0028843c00741c180d60001c801d022004540c10004e6010b1802031301c81c915203991031245240e00c0d01904402c81c2d40940345a9112036560b0007880c4032050244020f00005021000d4030018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 51256640 1250 51255390 51255401
    0x201060e0718060309020604090e01020c01050a0209030708210901180303080402040501091a060318010911030601080609030406050901120203090c0f03031201030f02010201020714030d112713 84
    0x40000990861440442c9240355400328058089440c2c18007810b81745030042100e07071013148580d0f010f290742e9407150007140c1e60a60644940000c0d00000f0300041c1011110200a50444107010740302e40100c400c00501408001900078451020b052241194090032201410f030350010000c49042c80319030640c804125100c04105800385101ea2101d81d542d040a0041c07204443c0160002d2807624548640712002c032090418204510908880d4940e680e03594505000e641c06500c4000983c960030a011402049520b07613810008103c154212081a83d80d665003c0e560081a100004203030001c100c02e001251040300180405d0300181050841c0c46c4051101d01c040380c0c0110f440c140f03c0c1d0880c170300f8080c1e54640082100a03204040b4020b50600c43d003e42040e256000611004120500a00c0034904590007074047d500442d800c011702e1881d40704011707911390312903000103010201c0500d49850003d2100300441564045482c0a01c1c1c0c0d90000340c2a000d101e00d0600e2101d01551184844a45040c0c13103a20340a02e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 51257890 1250 51256640 51256651
    0x506040602030a020613081b0c0607240902131a120309010201060603020f0409021b070f1e03030e060c0f0609010204090608010603032c0303030f041103060708070309030201060e 78
    0x29035655440d03c90003420130b480a8000845031308044803250210340b54406a800100c1c01c03910045085030781a0702149002c03410003039283c00030703008180c0c5001c0c0172031502c8c1300c80003070550500004031b001d03441003210840ea00d542c0d00a51150200186200428081d405060b14010304164404400f10020000b000c482074146a8140c0e648000780084047d642800389100810842c1800d50402ea00c101d1031542c00c1c000d601800c0b55013640810071119000b028218525603014400036a05520b8032004420541d4066000300c0391403040030818820300000909810044903050f5540c26400f220810800085c1d51012441c407805102d407100c40d0b0b11314803003801880e0007190704030f0005a580d8074194800d0281c036040e0380108a036900d00182040804d400480981060b21543c4205207030f04612078103070000e030070604600b41d0540300c0802040b40381c2200255440c0140d0103002c01201c0250380e54101070362200304640760380c001500607001c12542c0c3d00070b030080e00410784070340000300d11941c41d603034034800045c001c550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 51258996 1106 51257890 51257893
    0xf1a0103200109031b0608010e100504020901020c130e0c0901150516080a0804020108090a0c09020c071703030423030702060904020c0109061b031a0402070c0506040602 74
    0xc03841d01442e40304c0f9484807070151205c004008080381d4054a1b0210359007900214010940b0700307500e4400c60280325003200c0d0070f00305014030000e900a15042030640c03103000d100e07848540d640208901400c0d62100f001503070400d125181441c11084090450003100100c00600c4008038880d501042d900090a005566200b060340401c5051904031001e44000c8bc00300b09030703c0c80341e88542d0980c00740d4000d90380c0303d41c0368035404400c0d603d8010300071005004181d443c0d81041061029001b0304811201c04054603c141c4c2c1e250030802c050040c4c90030803103442c1c00002c204010000c0c400031840d42c0b264102d607442e2000c1c090100c5250b89210b2100042d1141d200806c00f020980d4440c1c0469000810410085c8000c00c410b150040c00740200d0900600440e100600400825100b8450850403940f80801c07440c9401e03003102404000d510540d402d5644545401d00440c0c80c1c0c4862000780001c124560 = true := by decide +kernel

theorem cover : BRFrame.Cov 51079140 51258996 := by
  have h0 := BRFrame.cov_init 51079140
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51079140 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 51079140 ≤ n) (h2 : n < 51258996) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
