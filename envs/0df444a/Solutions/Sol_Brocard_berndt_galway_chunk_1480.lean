-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1480
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:10:59.762445+00:00
-- url     : https://prove2.me/submissions/04c617b4-95b7-4843-9968-3178beb145a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 266007194 ≤ n < 266187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 266008444 1250 266007194 266007199
    0xc0201020a080934030b011d100e0705090303041d01030521030c07030e121f0209150726090a0902030f041202070e04050c030c01180b1602120604020f 66
    0x211a4080d40500d4582050342079130402459043d50410191221400d01101464000c601d40380715685500f13005003449150b071200190445020700050346c80c1061006101030b54040c0c83e41055035141c6000544403138104c034081c2607040c0800e00010a11703c044400d03810580101a00d0305005500d5070030002d00301803843c1f5a500440d05070540b14882e035286441142e40202444c1001c07681c3d035605040483d004130b42040340c55402802510690b500801c0010b00b992003030200043d48510015192845040344503550019800c0b1856120307091000301154060711440d03001c0e506201d6104c20b42e05d41483c82118403041d8000d01d00b400b2620002138100441c0341d1010b4041e6036821851400c2c6903101590340500140300801008014408501007842803051400074005450460054107182c82c050381c4402031120254003d200b00ca00d0007045612032400d5000038001e10325140c021508010b05c00040d03501c10700e8040c03e50940d4143d0900107840300c0303c43d912601a00406041d080c103203481004466034615580c0c3c0e2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 266009694 1250 266008444 266008453
    0x7060e0708030f0f0f0c0f010c020a03080604090302010605090109090515220809060a2304050901030b1302060a080703060b0405060405130f02070c0e06041e090f0203010c0201020a0809 81
    0x1101071800011502100c1120340041d4a844403101e415a0610404000c04003013640401c034080c2c0d0800000345485038070036942c02400540c0d220503080b42d0f81c803900c103400f9001038558004501c942c10310f940980c3c10b0030b01910002c0366a9403250045a41e03040282d018611316a44e0f9003041003480b0f000c0c4501c41d101040a0281c03503030341c2001d0303d60010400400d0109011450112190820015280c04440480802404460301d0380c6484501404900c014081e440030a8280e06076424500c0c0b502049030b050710b01c000d01e800340c5039003103071503820070484002c240030f050043c4075009801503501e10380645041c42c495501c0a9880c1b5002c040201900e08680c08204d42800900c001e110303e540f5607040e0713003e8500503100c040074040c00d00300c4103001d03180118a08142c24070000d1003c0920820900003c1070794000030183d0310036110803060100f2181000d41d15201d0006d40c20003541c440c451f9400542d2060300035601c3c0003900c4010740009007113401e00f0f80280c0250f035000030354181c000d4001c0c20280c1d12a0030343e806072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 266010944 1250 266009694 266009699
    0x20708030f03151201050109020702040b06040b160501150b1809010503120c0102120a02070308090604081b0f0105010803130501020705060904051b030f070305090102070c03020906040e0f0307060e07 87
    0x195aa800054901000240f940b42000c415442c0e00203120780c0c2c034402ca0b000303100c1940d4030b120340030003035200c040242c1c065424800d03c50303042e0a0183c100d404a50075058140c8c54442d0070640c8440c0d92255a078100d42c00e540300e8244001008042d0f0164001c3e00c00f8002140d0303136640d421078049403100700340c103080d004e5001b01300104650b980100f08960b2003104001580d40c0c40c0280704030280244a10a842408000d4170414000300c1c505960142074014031985500703515885102e01d095440800710b400500f548010000a60004031302203840c034211850404640341c00036240c480d0390944030240c0041c40c0540c00420144d044840d81c0c0c1c0403a0081c8000c0c006850100e0506011410300e1240758000b038001c54480c00070404940d99881e02034143e10400441903100d007021b106081002f42d00b5111a030000e801c11020074009201031084a02060b4420b403000100383c40e5500384a200300d8010170141c0e00c10350f5640108002a410300141c00101081400b46aa962031443c2440c00c948903007111308440d0b84150400e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 266012194 1250 266010944 266010967
    0x30c0c03040905060a060f08040818040f0f0b0a0b090f0a09020307030504110627210a0c0905090a0210021609050103020a1505040611030403060606051b01020906161b030803040302070803 82
    0x8627034000380c0007160182c2d1106a04011300b07045074081c0311103800c61f02d441034804550746140d01c01000c4219050b010301400c100103081040004a6000320407010100300301c003007010f14043c0616805908080c054005860303403116800200d0f041114200301103030f1114104810005084100700044008580700d50500a50801c012681050740c45140c50080580c00d082203070750b8410071010441c5054903132040d8180080d5445944072100b8490440302240003400c0031600e83c8040c040e5500c45c21070035005114100d081e030204000e0215a07407205065010344076242d0030854804902c80b000d42500303080402c0c40e5256206010300e5440a83c4841c1804240307038640300d04a5445021681112941e00c1c1103020080007485841c1148036035031005001d6443e10000003802c13a000000740021410410340c000c100055070302024280d1040c94412380e4400c804100d000601080c2e40740740c2c5805402513020031a0400c422800400f801c0fa15001500c81c050040100f000305541007210501030016039010b5070815140740381 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 266013444 1250 266012194 266012207
    0x3050a2009040f060e04081902061b070221070320010903020d150203180d030605010207090f0e0105010f2d0b0930010e010b0d08030c0c03040905060a060f 68
    0x990901c580e40b983c200380c000181640220014024640e150041070174245081d02003540b0005100c07840010b1406400062800401c50621480d4220710b14410b803e14440b002c3e2aa6000043c1260f0040445d802000c000c0300308050810100420f900800c415821403c1c82c0d8840100c034011562507421000e40000300380d0b80070350703030340c01700c03641980c400147c01ca2528000c3e484043c1031400c11821480403040180c0030103280c0f01c0304481007200094444a58818030200c05030b4130180a481c2c0940d1000c20b04000c03800702036001c001c0031240600d00042021524034482d0946030203072f00070b01c5103010008080c0b20000c00c4013074103c101b0704100c145c845aa151100440c548100520500314407040100c2c0041050b100c1c0c003050780042643c14901d8400203220100c44040100000d00c20341c10b517180c034108245a200500c92285a0140282401e1400f00a035540b003078950301c000e00c1902d0315202806940c60800c001c03c003a001030843c1c0d0402181c10710303011042c8400884a07612480403ca128444408103d8200d078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 266014694 1250 266013444 266013457
    0x10603020d0e03090f2106040803100501050703210b15030411180705160515040b01080114131a0903041a04210201180e0f0106020105010b04180f05040303050a20 71
    0x403a1b8007400740c01501e0300700c0082145851034001c2e0081c3c108000030805040000c502c80d00f4028404100c4507101c00044802d8051300b28010040381154500c5140c2101864003605000c0300001d01144428462010030f50441c0c500c20030038400c5a010003800200403080341c1580e143e200a5900c10780082046280c82050701000d0718103000c1c4903000032500e640810071010203180f2500002100c1d01c0810606820f0103040c801c0300e00780c2d803414030300002050444040c020b4103041c00c9540d00c12001500c0d800983c05040d09000740403035041030074543c205599802c0c030b24990300c0355003000050340d01d81c1c2c0b0f081c1c000c0050b001c0d0030401c4e6160032000c120a00c1030381c410307181102d66042d082040c030601d00a14401130350066451400f045402c40041c00c0082c40c0146600c00314422000b100764450740342d03621181a0b003030720310030b01030340c44004800d010034010100355201303024604000039001f0640c8200d184001080340c40945050740040d0300d40c2b08104100683c2d01441004040444281c4483c2d507480a2140345400340b003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 266015944 1250 266014694 266014699
    0x3090306020c160305160905092109030601060f030509010b090106030b0a050909030403060b040207022103041a091e06030a0f0603050d1e08010509040b0a14010603020d0e03090f 78
    0x10481c9448403030100400d000000c83c00003a211907948a04180c0e03a5403e800514108140160380c002c40c002a86020303040c00b90701004010700f0900f001c284078143c08081150404480d01003132004440a90f0101300d03690007400f181e110048504a0035100505039000241041016814041c0188040d180c0042e000c2c1141c00c6072900007a80d81d07108000440304800d580c40554080001c10521052240100040c0b003100c1c8908401c1092519980610050b8003030242c02035480300d00d0305041d542c10080503441041c2c1c2041c01064038901074440210ba2002c500b680c0e01198044408070315420130741010389460318802d016104265220f80d0031800030f005440018813602d600350322104e1944145580340c1106000e9a880010354181440702d90b801031501d496041040d80440039003050000b02401134021605980c400740c030800103541d0f2603c8040103903501904ca5004c142ea81c0d001c18141c8988011003c0c0a0480b41d6405a5034848070340b0247c00b41c40762200c0c1c23822150030070804200140e0340d407032200b0782c1c04a0a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 266017194 1250 266015944 266015947
    0x9030903030d0c0e150c0d1403061c06180b072f070b0412031403150f0109050d11090a060501020a02040f15090204030203010c2609160e10120309030602 67
    0x40a04407007620411a004ea00300c054403d242ca1380700100d20140000c3c0e11010111055a459500116a160360081300450015802c00200b81941000f43d1988031001c1c006104508a11f0140d42e2881210549d114403030b1f000382540001d008011030303a6000ca07084a41450505071038005a90f10070740c1d00080165650140303843c4103110035644024000c51004060980b00b480d01c4072ba40d9007206240c45020507044000401441000c000101c4600540340649a0400d00100400201d018031500160484001e03042c48001e110000340c50341c4030701d01a4a40351040700401c241003001014490f030000040c01480d1854240784082c0260b0760b00182004e00030350100c0780800d48910529046006203002d014040170654100030124801e00710350014412284260b0003001402c2c180e104c11100508a090705400c4203042145590079110b00045c00e980203a1380c07034140d03890904040c03a1030720080c4141d030080015802d0b407406c1143c02c0c6803407400000202023041341e960190240e0750300140004506d00009118560 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 266018444 1250 266017194 266017211
    0x41e03020708030c011d01020403050a030e0d0b0702010902010f02061b0304080403080a0801150215010506030a1418010e0609030a0536040509070324020715020c0609030903030d 78
    0xc2007140d08001d003800070640c3d0340e852801164901030710003480400150400c0814001c00b0040c1403007200d040f00e803c40007501e644440c0d07503000c0391214403141c1c080e0b510090031f81101011442c486c02d0603001d400550000944528684009031010510249001c2590040360410000c061b40c0601d5a0445100c02c103c166a5a11440c003085580243e420262200001180e80b188064000e080a81600c20403a281c0c0908004c91800700ea6442d6004141e40500803408010403560a102024540094240102180c100c00c10211280c85410864409400740501c0c15508541482031003002540c0400b100582254a00702050300d81c1c1e40702d010704400c1044400192080428049004000251110300405203d80700c0f002c121884900e00001182c42903180001107410160002000780c00c03664403401024020040464103000c1106400301c8100c3e150f020002e40b80001c0060b00600210380602d240140c89846100300103161000c02400c41001c2c1d8410800810666400401e0394865007210034045400d40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 266019694 1250 266018444 266018447
    0xe01110c0d031803030806011b0c0b03190e0c27130309030501110706050718090b0409021908060612100b1f0327110906040b120307060b0405041e03 65
    0xd42c10111040c01c1840004080105603100141b00d0051009030307900b0060038007040c42d01a0f2410310500083c00c06006d0741c810040b41d0400b001445e4080c03520f41a01d2040e66110040205452040c07a1801840d04403e0350700c20b442c40c00300c042c54441c0d2400c0103030031680442d460030310b0000074000e000727248500c0c0c00880795810144903460000281d58480c00a001c200c0d02c3c58521101074000311800c881440c140000529058821208030050002c80301c2c2502846142c24018801032012080d4160000d890b002020050784a100e0900070a040408100c41c50601d44501d9504001000d8000b03440b82040d080050261a0009200b440d46403080c0000510b9074801000a2940101801240c00090320701100951842d0580e1019250030b1948666503141c460301e010b000c021a101840052000658500940250800100042c1e0014014200041807000e00d80014450004103400c5211544009000030820880c0d014820b8010b80507603040c0000e040c90340e83d50401e041070600d08498002080314640505 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 266020944 1250 266019694 266019707
    0xc040b0d05030a030c020d0509180709090c08090f01020c0703200a03060b03060a0506101d091314060601120b0a05060a0c020a050307060f050a050c120a0e01110c0d03 73
    0xd548441200d5552009607005005401011862005400b0f520316a09425000b942140d20701400105081d00d54007259024909107040078142108001508002140d01c03a030342c0c4141c40b007101c00340c1c07a410a0b03445d16451441c60b0224020058503507900600006800e080c000900009481e40811858070200014011108601241c280c481d070010b01c0e10710000070300c050f40d0b02c050400d10b402d800303075555603a6081100094031030641d40c550b00610030400401450348543c07190174036450308180c0c401070b4151050000d04188800e81c2d2081c0c00101d0901c2c440704120601d4070010403401c1c0c80300034112510300f200010780410004425045a03d480311003046c4660394480c2018050300d4018003054803a403140720010410215604102d004014001011400380740c00100041100d80566030742480107981071046030307660041805401401024051240f030341800380b081c2802c4444c807107902a200c140a10f4010408600352030524184a0f507040400b48403100841c42c14a108000c0e5418150640d903882c084412 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 266022194 1250 266020944 266020969
    0xe030a080c0f04060e090a06030506060411130e0108070f0608010506091801030b1501140d0b1c2009060a051509090115170c0304030818010906200406020c040b 70
    0x1078000020f0b021411a400040d18800c0110540307035000160b54184105080f40c05034000030b01940c0c4564002995490580c00001c100e00d00c014042d820800000f01c01c6c11242c8068002060b070104140050169040401a040080484481354101f00b80b030040c0281003190107004050155100144554542d252040e002d411100311460b079122940c1e40e030030311111140003540c00000302840710038945000c1d80300e079401a00300700c60802001c2c0740882e0601c21900501d0b29180d0a6004a40c245042da4041d14044003402e4660045c020456519644a24a024900c549180c07034030581c0c0b11010f010301501c45882e90019200180e5071800003042071101e5900c1c40c006c6800c50b80e0b2140f16035001043c0d00b102c4110060740c400298650140e210404042d41441040854000d0340c60b000600008000c01c0c856066a80c200501e200c41c40514446402003a0070b41d01c200c0385c01d4030050307203a40e288429942c1220510348250a1006410304050525500039180c88a420026100c0c6446240c2c1141a40e10003288921 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 266023444 1250 266022194 266022217
    0x60f0c2c01140c010c0201240909050c15030609060a03030f0c030212040f050a06051c27031706060f0406030b04110403050d081b09090a091401060503060108010e030a080c 75
    0xb00d5103542a8001d000c1c211417507444005500b00340030588481c11078011940d005088411450100d400d00d0052002800c1c04c443c140d0f036a225403c0b100d4410380701e0a00d100e82612614107525681d15001c0144850304a001e060980584d0b002041080429071100c21010710303031214940b24200e0422400c04030b1a160115030301000703803c00098002840e190080c1d4a60448400751401c01ca90ba0b070b25403041d81c07a805200010259140c03040c28902000b0301f1a0b02286100f0130401c0000520b9200c0c0000001904180b40100c0103e140e4102107040702154581d502da101908480051801c0c000119541c20740c05940705001c01d060b01c401400240e0380c4d480d0090000610b11600c100c2d00c031503617418529910003242c0c0040740450341900100d14071400007a180410145110045803400e03149405110341c10340700401d1071458559034a803000010741d240b69840d042e8410400003003501820300040500b0307c0c8041c1d001280507854921064140c00c004400e455070581181000d009aa42d0720800d15024410300d0030b010b6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 266024694 1250 266023444 266023447
    0x40c030b011401030509010c090b0c0a050102040b0408063301090308031026030f030415051501020f0f0a0f2907030c03150b0a0e030604060f0c2c0114 66
    0x2141000e282c14070007074403000d90b82170203140c40b21320f9054202d9034200da000001031050581070050ad010070004000c0c0364600422580f41452540f81d15003280c009404c084044800010704002c3d0b00020801c4540108500c0800b05001c80c90b441003030800c1c000340c62aa4003d80c1c450f2000391940e1f0043e01c007000150740112a150741e0b40307002414005184918050343d405805101c1022158030309480340000141109001035281100c10800e00b180c5420003401211042200785503100c140c507070b900445000d005610702d4108100800f4002a04000200480c4155980011071048007014005601e0400603006135003034016402c641050032003403081d10303640c003204450301c0c8035042208900c41d9100e10407040ca41d0108500c00304140b00700c056810244440400c5144054180420341c1660000c0c000c0000c10300b04003440000c2800481d0400800b11410b4914595032141d07102c0c0c580e01400340350040300c51403814980b640184203100b00350a04150303d4550804081d0a00036031640110200c01310304030100b0a19 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 266025944 1250 266024694 266024699
    0x706090b04021008010303050405010c1113090c05150712140703080906160815131d0115030f060504021c0f03140c030406050705150702030301031e03050a08040c030b01 74
    0x1025500181c408034060300560201e80110391003050b5140c142c2e46e240d660769180a250800446490210803419916004505c165580d10b0790b0780940c40071050f032450004145a0f07134a003000c03800080c3c40d912550180c03010300c0140e080da6184000302d0700d010b94045034006801c6503460b4120b0700d84440c600118800b040000e0704070700341a0030240103403243c0868011241d103541d6450f90320416036081c010100101c1c0020002c03412100c0003c05c03029448501801c402a008190081c55040d0307018401040041504401d10079620f40007802820340000c0894451000e061a59030351014050303100b4005400790340e8880201d011561000b02d00090000c200c0540414202a41884080960003441c200c0c04a000c1c0030700b280509141c01c00b07441c0c00303c110b000591309161802d01c06958036030003414100c64a0103040b104e156186100242030b07000d90282d0307009540300d43c114900001001009519081c0c2d13081c5540a0030002039010f001c03200b84c1c0d603c91170100d071301c0e0322145445441f003040790301300402100620002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 266027194 1250 266025944 266025953
    0x10f1806030f0f05190b06070f060c021f020a080108071203110a0807080903010e0c010516030c0c06030219020304031106070f0515190e0a0b100905090106090b031515030102070609 79
    0x8000e00317242e40101003116a0716072007088118800c0f0f5000800c0140040c3e03074180031801aa100290103540c42c0103813051030700041002d40054081c095808036141c1d010540d102000d5110078018050034447e4005d100150030076141100000c4c08a000404021000841c2c1010601c10702034124180c2e844a9582d445002d41c0c50308002640000140c0c90003986448c01e845074008000401c560300e41010b0715484d14095918071000856141c151040c2c06020f1501071080c0024a001151002090107a50058540f0020a04a00b04400030b003000001c5500030b02003440840c640c1034204802c1402101c030a42da401c550318100200c3e410344a07005c2c200c0d02400041110f030b2500d903514103102d080e401d8030002058641c5214a01100e984010008180c0c2c0211802400100440c642941000c80c0d4040110303210340da000709805440c001c641801e1140d44410040222100c140500c0070600c10032000b80c0082c1d050032880440c9804018103e100a00d03c03100c081030305803820342c1101c0005070000820702c12011907091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 266028444 1250 266027194 266027221
    0x1c09080705221b030515220b0310020304060b03120f1602210106090204080601050409110306071d06030c0d1a031b1e01120b0604170c010f1806030f0f05 67
    0x803e8800f29040100103090050f44841c080074000c0001e20880c0400700c9001481c15018841101d40c840390358494107000941d40070089032421031003e64026a4030318082c9040b0007075401d08017486020b6401a0440205d240084099811900400303c0c6a034492010480c5e01d580d0101c11180a0340106412446582e00b2500c404030000d1801400c0007030003060b54800c0404101d110300d220f00d1016030407000c0103014501d0a41c2210310803501500a076400c420015001a040c074000391540302c00718070b81d404d800c1d0900100b8048a5030b1600308503102401d6150080802c0a40d10400c42e140c032801d40d8600b0224402941d03401c0941a03120302070100c5880301c480a808551481550150f203216041036142020001100d0f910505904010707501d100307112400c8111400a88504101c0561080742803001140201c400d40004000002501c000c002c40802640050b040e81c00020400701045990301074540000400300348182161010b140c00140c1380340503041070340242240b41c0001455403c20b003c1c052203d10065 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 266029694 1250 266028444 266028491
    0x3031e09070329060a0506070209060d0b091c020d050910090305011d010b0604080d0513050303030703050105010f0801260109080d0506131a06030a09050a051c0908070522 75
    0x1c0c00040f007910399104003c100c032100d01c241a4803500030041e48005082110b00290021b401070081680c0000c2c035554154202021100e2010560280103142c00142200081082d404200c2c005804003c00ba020700412600ca0803484500800651800c41a110300c1a11075400468100000b000301a006210ba07103070220314220007c0d01076081c10035800c0d40785020300448003100d0741c24001b050600310b608419038044c1c100d004a43c120b00c1400200083325142413008505c00e07445540c00040302c0d8100000134094140661280d0104240c0740014090b5895000c001da018906008961549140606003030780581400c2da0700a2801c0004109070300d1410b4290003650041004941800740c0c5c00480d4030102c21581c4405c0c903900010419000f1040074101a0011500051203900100b40d03c407054441d5440c000520000715865400f188040d4410500f40030040282c00300303858089a030380e24107022141e0b500c000f4003906210b800340d40100203960000c2c060700b101c40c545010003804a6100205910340100040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 266030944 1250 266029694 266029763
    0xe1e0d0f140c09060303030703150306060902040e0c090d03080c131e120b070c03170f100f0b0403080c0319020c01080f09030304141f0b030f03031e090703 68
    0x12040000d907251543d4440c0c401c1601800441c00d40d0750b1f0f558200d02410038054038400c5541e150001001180380c900a00300680380340321015954034600950900c0e1000c1c000c100c0c1c1102c00b81030000310021744d212440c0090a54040c5880380983d1101051025103105003c031409416076604800503624400d008010f6116104400b82214150703540d00c1c10840408070800100050700000015490710301448000034014020b01d4421120703d210304107445540d000f6542490142822300400000948000b0050007038844110881c001c2c0d4600300015600b80203601000b40549004609a070600c00204113950342c00c0c0050110ba00b440000840280d21505805078043c00240a40001403a03602407880c258080d0036028002c1d0b10f150303201d4540d0a082c242c1f64405043c01d02941c071000404112032911548100c640441c00144481c840b820146800c11014640c1c609800610810428450740403249031558060541319401d6691100014209112a04014180702000c022070380c8012003507140c400c0b00c400c1d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 266032194 1250 266030944 266030953
    0x80a150b0a090902211c140a080a06050f060706021804020412061b080402010e0406030c09230907030b0a060515070201020f01090507050103020a02010b0d030309020901060e1e0d0f14 80
    0xc14003106170513254201d0f0040158454440115090031020300d0a208000b6441d10500f02c50b40c000d61110154403081000d00080c640205115050030716106801c001c060071221095240c1520340412840c1c014010081c01a0790f001c24090304518001c0610100c58a001780f045503201c2e100c00000f00e03421001002510f2070703031505800c4600b180d9690030301050015607440e0014155542d6004407030004001143da9000307074644000100151a035419031002c1c0c0000c510100c2c90311080c0d00b42e2031004242c503400790321201580c001c3c0310f108a400709140040d290804001c52850b520031080001400f01d503800a50000300d443e1030300300e03410240c001424403a4400d03801c1d66009458030081c203080c1d60140f0380c0940160880c07a8100070540c0240e008001200d41c900000c600d480b04100014010b20625000b40d0100e40c0f00c030041011443d00c00d150601421440c01c01c840610003c030045403912440010f410040303207003200c180f401507460555080581d036003e1209444448640741520007211445040c1005208 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 266033444 1250 266032194 266032219
    0x106030302060916030c12050307231908040b0307170106020a020f180a02090f0411031b0301080303040201030b01050c0105040c0503070807030305030c030402240a1206080a150b0a090902 82
    0x640c0780b00500300c0307410145140016003440c8030104541e081d801f0844051204004d5240022840200b85200602d9051908041040b814201c1d08010804100d00d030700c0e10581e415200051181c070103803026100d001288a480340c2e01c0c17040640311006450300c6200c0d0100c40308000030b052a40003c00b0702c0c400340b080c0c41d80205942c600040c001d0039003c40303203034182c0014142c0010302c418506901421652400402520798421034501082c01c54100002c03402203d6400010002c004d00c003003080340c3d464035880b21407034507561400300c00d0790b00c90001500090405490748031500041e841503046e100c905006a00812203800c151600031003962072442150b00074083c014002a03501008150700e02107a4050721620324590f2543c0c0107445036071008000702e80c0010b1928403010000080381841d401b0700c03e1660150b5503550300c00000760185030000d000d8241c060802d8402d000c3c0440200c0c0c2c02e11015403105c1e0015240c3c8810040381c01500094600740d0300550020000074044034117030812200d05000f1f8030848074014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 266034694 1250 266033444 266033473
    0x9060503010f11120402040b06040f210b04082d18030708030708030a02040f06020a0506090601050120100e010c0e0303031308131503091e05100b030f01060303020609 73
    0x30002e120380640f6120a00141100815221003c0d500a200800015400d08400c00080c015001074010b910b044020b41014041c520745681c0000d81610490003000d000c0b004e41c1c0da4207404a00c0204001c004120114a2080d01070b8044030011072440d2081f100302c140c5507040c8080304035410400303c2d042801c40380c1c0454501810042030020030385590101a501c8e00300f96840c0c0f80d810740d00145c4040c40e119400c1200140c11601001402d0242c01d10f0703801f41c0003044490411924285002c1c02c09211508030b00c0040029070f800c03030b0f2070f12000307040010030001550900028a00b0040707000c80400c6201c1c00e100f819416034a040d44210140100c41e220350ba403602c2e140e001d1554030b02088981a0281d112100880c012900d00c0000d48004011000f48040b03181e180c54141280c2c070390b8901c100d0042900c42c070044040064000c003000c000a10361a150211041a840d401e60b505441c04401c06e40c035542d800011600c0e1001d01079031400000f08070083c420646d803850020350b81c8004682c410f00c10302444600c4085803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 266035944 1250 266034694 266034701
    0x715020c0a03060c081b3108071a1306080c0d050403050a0906031b03110f0d06090c02031c0213030c0b1305030d120506040f243206040305030409060503010f 69
    0x408008a1034103061a010b44400b050401eaa11000c0d84640e1f111508040b0400d450102c002e048c8081c05003050902d800110309041c10740901600340c0460a002c0070840e62003e640700340c01c1351002d00c3c08060030385414004807901c0c410642d9114049041c10f00704014141c0101c0140758407446a5600201a035840034124100c620340c17407103070b0791855520710100c0400c1c1c480d41200d0610813102100902d003e0308040d0800f0564000503452940d10340b9582e0400c0b000e46988200040340d5414006140b51611015114505100035001c00c07616a5000c9420003007140c0c41001e0101941e8004080202c10340c44602c5009990060381c090303800d00c041d40c900403603d82030110784008100d401d5100d440181101580f884050b2400070400c80c0c010b80c1d0750012a503006d01c58001c141c0d0f15401c00400071310301d404c00700c440311403440203801208044030000140211409000704400103040d050340034040d0380c086580003072041d125039800030f8260b201c00b1402048411072a440f100c11602d0442c001c200c2c0c0320340c445681054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 266037194 1250 266035944 266035981
    0x140708060c040806061005040816030201030b01030e101515020a0b010f1d070203120c090909070b09040f0b060c07150e0d11030106050301020a032306030715020c0a03060c08 76
    0x3c5070000004100c050801c80f4001100500700e08240382010307124075080389040c59429000031500f03e0b1200070000c2d07582510401c211710000b0b107001e00000c41c0d444010356680025410040b80c250b501c4e00101071000315102c2c030001401a55000d604400104c0c04000d6660708212805d540b00b038140070000445c129404280301c1128130100300c207140104110644054803130700070484000d45c0000c100d1120008124103225201784100001d40352240010814002060030040000401d58081d010501980c040e0074140c0d10360b1401260007040b030750180700c014400360025150312030300000c01045c049801c62020441c44192070416000381c2030403055510071200c103d0520083c9411448410340b1b440800d86081981c801d828014001140217903942003c6800c9030700c481001000a0755035485010440a800d002044900301511582214208030300042e46984591160190407c0b0000c44055928000c0c481c070904500000d0012500507070742d00700300c409000200c40036000140280c0005119105a8101d100c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 266038444 1250 266037194 266037209
    0xa02040515070302030c060c0c0d090810090c15030b0907081302060705160608070e09010305031b150a1a1e0906010507020a090b041b0c030302090607140708060c04 72
    0x581c1180300c00300916901c00c50702034045000401000c62a182d00708121030240318042c0000d503a4024403070381941002003c0d0100da00708070313040e40100100500061103001c80f207a04c000c002a0031207545405c1d0040c0803103038840250030b1300c4a607100c1c600030f8059000e140c0c600300541e5620301036a1022402c482181c012030f0074204600075100e1180c0175041c41e070080d28049129008032910b41040800c0a885807449502c1000011142410080c2440d889074003038452000a988444055066a8400761030380101e4401007144480322848804440d004c01c51411000421070030000e46060448092000d0211004021050301d51546805001d04025901c030761812800701041410346c04030001c0003990704029081504001c018040040540c1c1d404000a00800c00490006821007841c41480161103104c2140841501c26200d2035191036084070210300f040d54103180050343d60070b000300018040d0044801c007400c119000d0400c0400c41c0c4002031220244ca40300b82c00c85080f982c0b103031a10b54061049009000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 266039694 1250 266038444 266038459
    0xc0c022215061b171b010207050c01020d09081009110d1b05011d130e0f060f0f0402090a0b031e03071104050606180f0306070c12020105010e010521061006080a020405 73
    0xc41000110301a021a4200c0205d0003080c000841401e03007680c003c1340c41592203404c08500b0030115a010030007242c480030030f824a0988549484103254a5229060446a60301d0302c642ea0441007100da20901842407200800302c82c0c0c6040141422155081e4613038003003580f6182d9080101d610340c0216120050f458105000901c40d0814009004221101401c0081d81d0758603150031141550060012a24181e00c10005000380e2400c031400c1000740b07601910291f01e4824100030f10015031a0800301c607500801140c1c0c0032446e04000004a8a00001540d4407c60303946107205c2e0100c103c001000600c1082c1c054001904000c6102c8208421a4000d0f1009907201a080001500585419a008020381c0300100048548442e0002007800e002085801000140c40c440e03c50b800c000320f50034044294280752001300025070500c03130b204d5806101030140c28480c0361200b0f01f5003040884910a001002039440649000c0d09180c0b80203600b20f00c1c140644004544c2c0c41c0006814460180b003a6403c42c0e00050801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 266040944 1250 266039694 266039723
    0xb07020709152105031b0c06040b0a0c29150109080309120a1a0610030c08060f120d05031005010c0206030f04020604081207150c0c022215061b 63
    0xc0180c60440340c122001c3e400601c0000c0801c1c010320107800c000c400c10b10040341580101c03010904001051400300d03c200414030052100e282e801003903640384003007801d021045901e04d09007140b001d020044040592415003a203010880f513042c2c0c0d61401110718440010030079610b10015950816070f40200840c0768824860162246068449412081e0750b02054400c203840316213958001d003840300d84a5103400c043c14140501d9003454071412550340382914040000001d203c000912200d0040d0513030740b0500c00010814800d90b10190300b1240300c0707064411203910002086002d0540d4004031501801003442e00e80c00141940240103201803030390b0060880d4590794520640d07501340c140c0500180d030000c00501c0007246051042207000030a2840300303021a212034852812a810503a602e206000c1e0504122041e9030b80c0d0782111300e54060f244d0443c0c0000078051034900746441c0c02d8030700f0011130034241010500006c88808100e94000e031466642c0da41c040c6a00708021010b06410104000c20344418034954 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 266042194 1250 266040944 266040959
    0xa0308090105060d030f1709030a0f02070b0d021804051302030607050c15090a140a11040912030c0e0d0309051306030510022b1401170c0603041e0b0702070915 70
    0x468004106c0d5080104005003410b005000441c03080b00c0c2da07140c50f400000c0d4405950341016014640041c28401045e2050400b01482c8084c0602410025071503004240c00700e415581c1d0381c80a00c03850002c0c004010528220354019480e10f07000c8400d03030007800b0383c1d00400d03180c0b4441d008490b03e03c201c820040807881c950640360381c44990002e104180074003ca440d01000a0300703100000b0220124680205100e10881c10605100c4810b0010140f049203400d80e04000542c82e5840840390000f6400c0c005449451684203403140410011113078bc0c0001506410010140c20114080c00c2c5c40066412404960038240050100c5046005c00760990b0700c402ca031a00d038000b107a00103020b944140b103001e1413181101c00380c4040b6590480050152603444059860300801000c0c410b44c0181654061100c007005003410361900c44c4200c0407c50b0068030004001000d001c0d13a545e40740c0305820060a20140b05c0e4045c10807040042095809000500651740700044d1100b4a0140000d07a1040c50009039003589003c21 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 266043444 1250 266042194 266042207
    0xe0316050a080c1609020702010e010503060120030c07090203310c031131090c0e01060e180402030615220c0e0d05030304081e0c0a0308090105060d03 66
    0x504a4140c826218081d001820020103000f01c09102001402c44550b48414044400c10301d400014501c0d1042c090400541e07404840c00c000451f0a00f0610755a44070703500100c508403e500035440c6c902c440c4c10901560070500000908107800309074242c030302442c0c0720040b0006920064400024007500c03400d5001c0703100742d2074060111565402c100400f91070042c0c0e81c0e4070301800d41c691040c1e81c4e40700300c046043d0060800401a01581c24401c5000c8002c21100220b45200c0054071856003610741d6030342c070480030007020202400c09401401881c2d161582d50703000003000300c46045402401040350038803030b0342810050144c050085034000d0103410030f41d40e00001090400c4206e08810340c40898036a490010710101800a4080c000c0d601c0f0202d554421f104c4003030010b40e04151428000e40d0420301800c00f180b03020054940160780324030101e42d2105071241e22000e40f030a480c815184400b0010b203141c1002e90003d29984100d12070344481c4210ba540d1a005803c8480c1104ea00380c005011450140020f40f0809 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 266044694 1250 266043444 266043487
    0x60813060209060706050903040515130e0a020c03070605010f0b030f0601030203070507150b150a0207120507030b0a0501091505012f120405030708010510060e18070c0210030e03 78
    0x3c0c40b082c2000e1081d02c46000340d500c01d40d002c1d402034000003003d00c43c3e070425140040101c000f502c9081d1502c441c1c072a46c01110f007030034441c6810100a88002c03924003903141d011600d00151200459403200c0c00c1d800d20a00805017845041580c0d40d03130b400b001a200c045141070302d00c508007001c0048081d80e200b00041d40a0340c8000c00301c50810004010243c0010603609651031000c45844001480d00b00e880c0500038050000c46101e681c0721010300c44c070312210f80e0004840d020f544100f01506110145890204c1c60558030703400040c0b05009c0c40c1c00b0403106d6001075000d0303030403222201010301400b54280c0d4010f00c0f0030223034010b007400188000e50032026091010329010f0400c4030f0550759034105164811050611300f1408500c2d0158000107010000c9113070030001d8101400090000300010700385021000703205041741c80b600050004040700090716646010442c0030091425404c0c1c0305a1070403801c010003030070301004100d200b1401e0003100d51149220380305030413403100c0d00d400030752030000c0b090790000c4400d0001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 266045944 1250 266044694 266044699
    0x18041b03090f1703150910051c0203150f0109020f0406030203060a050405090a0317070206040b07020106081905011a100c05010b030a03080613050709030237050109060813060209 78
    0x81100001400412002c280c4001c00e91103140c4906101017030f28844031500d070300ea070b108603c3c0405220721003006125035070803240200d40d01c407000c07554420343c88213400c000d00740603505002c3d04000410042000c800148607500c00540f400c2541e0300c88040704200c2c0182400b403003400e1010b1205002080c042c2d40207540241d4014010032900c0c1e603c400007015203c04803042e210a800000c1c89600f0141c00c00190544051400e03100100b51512550080d80c9070801803024215a0040004c9681c0034000c0d0301c0300011340480e00c1030703400c03288440582e455802000700045803207601c0c2c030300c8860900c0c54011070000300714030081020f800d54102040803502c07812940b105660307035562290070409030707502001400180c07031098642007542d00d001000c0101800d00b5a0b40c05408900f030100300024103a01c00014010b480c1c0c11548078501291748001070343c0200903510340022401d000400e0600d840c000310807036021140260307112501d5a171070380402c4900900944048481d801d41e928010000307000c0c1d80143c032004e80302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 266047194 1250 266045944 266045963
    0x120a110a080d0c050d1a19050f2e021c0f021e01110c0a0209010e10091d0a030909060614030a021b03070f0507050a030209060904060e0304090218041b0309 68
    0x880c45507006c0b01c1d04105821a00d103516501e080007030600e03070f2a40b00100c00404480015901d488041041240102a030741e100c0c030303119040901c02020b440345c201c02448410110a64807043d501010350390f0121f0b103104101036101d0002051600344692111150980d0644c00391800c680350b001101d80340921a500b4241654a0348040c90701c1072006005840b44051a030020020020a40103000e071031603040e00010007802c454001c00c4103c903140c80c00c090449000c03540005801d00d902d040300c41d244040245421842c0120000c007030925a004803a407083c1c601c000340400105544c2c69050300c401c0c008640e031030500b100510008205d00d0300344c2d0107070035541c00c0001c00030f50580c8000b41d2141507500c1884c00300c0307822126101503020302c0130400c280c03000350a007901c070346907aa8150740002d00320796801400c0301e118030700d43c44c009130421599800c0180c3d084002800c4985884d00d4455202c080e401425403028111809801c401c21031411780260006401c103031340c412070984d2000c9800c81c054a0303e90f10607030700b1031034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 266048444 1250 266047194 266047207
    0x6030a12090914100f03020109061202070807030503040506060f1005030c0712090311060403080301230a06020a050613020a18140a020c010f060e0117070305120a110a080d0c05 77
    0x7628000d6400c3d040111040781020b00e00041080d034441c1964012484c010070b130f14070034001070741c0045071141543d51030305040740148001d8524001912030014000c200380c00c0440c0100801d0742201c0514000c81c45002903407926503401d014400c1c1704ca00702c4401c42e80800341d0381c0014005d90103403000b950000401076200d454080c00741c444191520b840400440040c40414040040c0700c111461500040c10464800d49094030f9034580a18a001c18050305900083c05288218682051440803004910190030703441300c11b40d10000692144440b10007580d4074050200000e03035620012401c2e0840550003080f681d41681488400c85000c08680810258140d849550001c6400e0019145110707848411015940e040c501848900352a04c10706044100703804d02000f805107030300b80810207040d104040c0c05070f46498490b80c2035506e131110300d6002511743d00502044810200d602e070000d000c2c43d84207846401000507011205961036a80e08400f0748924001e0120403210030407600255040c0c219403904504110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 266049694 1250 266048444 266048459
    0x708160e0325030b01060206010305100f0e0f010f110c190305070f1b17060402010e060706020414030c0303030f07030209041e0e0606010c0201050714250f0b0306030a1209 75
    0x1d0b1401c040d62031498a9000f0401c01802c801a0340c013600181c40600420351455481940d01d14402031942d0409899640403072900000b5071100e221907584204441e800c24880c860140284400710080b8011270408100c661f074000c10b90b00b01d41c0340011040080c1102814031721211b5810312045411001c200c0104220000b10314042c0c509072007140200001d06c04d000c24000705241e492a01e074400c902c88170361140d1443c02100701003051540560203081181c513141000001442070700c00c00341d000340003030f1000c680850291010304400c0c407002801e0b000c90307000040742c40803d9540d00044403000c00c1c40a00300c2c0000c0420340300360080d02c0004c00c05800407a060002100d11900031039507060502c2c0300742d5120344040007100200075440e003000c0d0a08241c9003104098000030414407072648080d01d800001c081c0d1405c4103104110940000c40018441805000c4403160b00e10b034009148500580310503040404180e041b5000304990003003000a008224a04240d5a2481d46c0310180c0c0040c0f061180c0c0c1c040000340e50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 266050944 1250 266049694 266049733
    0x11070306060e070c1a04080c030c0705150702131e0f02090109060f0c02010809120c1c0305010b03010e0403121a03070f0302010503071803020d1a0708160e03 69
    0x562003800082100c60508195100010307004002504010390b41000c0710104200c0300d494060000e00e111030701c010384d0b203505003a00c4503c40d6a0031400544400240040d2070f4401062020030f54204461900303085c00300c058901000d00071010043d60207242e400000652100d250b0140424035105001030010140c81c03010340044813540c4081810f010340000c0c1d0030307246690201c003c030050950341c20020144124001b00502c102240d000c024184059000450300318101004520400043e41e034005035550816810640c84005201007a0340028020748000c582a000f801510706803070300004030310306581c68803001101407503000c0c10540c240840e100000080c941c2c2c1e8080c2041910000e1082c0120b00f50f050b00b0706140c0580d0740e0001301c0300f05a000d01803005070f80c003408607a0081c8ac0c0d45814070100961041e410182d500341d90000354000640b01601c2c0401581e0649081c180010206160903541c5d400000d442580003181d00b10346845d44d800b114803440d40500342900c030500700074088075801d0444102d0150038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 266052194 1250 266050944 266050949
    0x1080607140703020a0209040309050103050901111603050909090a02010207080d140a030e010903090828020d02011e08040b0112030c122105010e06010c030503130206091003050709140603060f011107 87
    0x4400ac2814000f6503010300419801401c404003c02078440b90241d074001a010f1000c41001e50a000915001450700c01c82c10740d2581c450040c0842e081e410100d41041d9912403080e003c90140c050300c07100240041010542040305021174581e2400c0e02002010008290301c00b044003010f1694403e0000d8410909105140310f15100791910000d890801103c1440c02521500f00c0324001c2c03400801e0841541000e01203202c90750305030f40000c20b1706140d00c010384211a0f038401030320391b0103030542076452041c0d8050701d40e9000700d000b20100382203640c03140701c0c044601c0181c1d500600450a8654004001303404d0030b00d0002d14481d1480c001540881d59610701821412030b1990b05e441548440060004249a00d03100360449800d007071106c0e06441c550b0300540a400020807a9251900c0390124105540f114000c0792620400240115070a1420040283c004d200940b840d800149142c0300108401894110f02d0081c000010020790540d41c80c40100082a030034064401d04100c1c0ca05070700250800108241000f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 266053444 1250 266052194 266052197
    0x23030f041b0302210111120717060d0f081909080c062104050a0b1602011401080304032a12060b010302040b0739080601080607140703020a02090403 65
    0x29414a81030441852607900000d50030005005010030042c3c0c0e03440c4070280312400e00c440038414103198252290050100803100000308070300103890040010704c40c02d440e220307001d07a48800f800c1c01220f004000d003030803003214070742e8001c1d10580111010845c110900902c031442004407501d04074502c10045a0380d032403001d15002098180c03a052081a02c24040088081ca0584d0910700b07200d040203001e0301800001400e600d200031000041801c1c0501409910221900500700400600b01140481700c2d0000300302100c00107519000708c05190036201c8483ca03040314050300007141010b096440d1040484403038600e10b204414000e0790f400d10b03002511903d400402c0104040b2002c13003618140a0300b515070b500841410036104000c2400340092407016034001c503410000800d40081c0d54101c0741500003007840d031460002481c1d1100c48a0b6041d400c01207041d80e0003041511407a1740e86403801a503401040d1814008100c1e40e0b5000f216665410001d441424028812502850001e4001c200180c0081d5026030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 266054694 1250 266053444 266053471
    0x705150702030f010b01020705010f050f040303170601030b010e1201060e040302060412081015032c1b030307031107030c03030305070f050c0a0809130f061d15012303 73
    0x207601c0e050058400060310840203201010000e00002e440e203560340030310707418040d8491022050300c2c40b038000d4a080b03030007101c109a9620f46905020780f0707a6048006d101e02c100806400a05d60354032038000d01c0c54410040e10ba034852000500c0070841a24003c80358603034159a1078000241c801108618107000e14043d4014107440d040c80d0030416000c0e4510929801440180d8050008590050350352004461442e0505549103001c190120b0103058044030480010080510303c0c86030702400c0301380102405540080700e20045617100c0c0b008902124081c1103070301d90030911445e400b2902825886113032801a505480c0c5141d12680c621060340c10300d0300300758002503031401002180c83d04403502c403610480904009051082c078020055949115140003803030908040307281c0100d40c41ea0268207500f05500b0400303100004c00e1004100042c1000c0c8120110b10103101e2034100031800f2003040e5402501c0c4041d160155a20380310040d101280c008800241101c14518006184041000a9030240c1103507080d60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 266055944 1250 266054694 266054707
    0x303140c03181c11041d01020d0f06080c06070f021206040309030501060b0301030203060a0c02010b0301092a030b0705030627070809030a0926010504080307180f030b09070515 77
    0x200e1034031080e801d0b2411001e142e40e0003c0c08214044548100700000319408203450020510055005090144900e9190b00120704083c90580c0b0340c2000040450044d4100607260340c540300340340e0b1451003001054001d00100600c4010910f00c0780341c6211140003800c15242114003034042898094111002e8000810303103481401042028000c5070020584503880764210f5065030002a182e42c8094201d01c00d07595a0710024400900039084401c2d41040100200902110360604052001040c4464600c1d42007820310200002b4244481f581644c0d007018520240f551155002d036410b40c00070789041d52141c01007001d5690b0000d2160200c041c404003140c00c41c3c103400e068a000d022078602900c840f0340380e0018000200c0540d4001048011600c079200a40320500100c18015a03140510081000a500340001c0001f480304580003540103001c4c0d940c91003c0500140c02c0004070b420030f4040c102c50007600740020000b0602c2110015003040016095070f240c2e581e40d000052505004007200b801c80c0d000407400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 266057194 1250 266055944 266055949
    0x6070f0b07180506030403080a05070e032a040204140105070f08070f0b070e01080a0b060408010507051308010c0206010302040b04021c29031207050f01021303140312010303140c0318 80
    0x1c0b0020300c42501c215045041c00c0c0d81c042c040b110300509045070980c0c0c0c0c200140740c0d24494000d0100803c00541900c10040d108482103415a040c42c03921112034420004080040c1480d100302c501b00c50780103000303100c00460344004499550104400b95110320000e200140802c00220040600d280309107260316802006192102400c0703401043d0401b884a108030041c200e9811844250740607017400c0b40083d030300c507480700001c2c403a00690700421513540c40c000410054039081401408150740e001802d40200c0e40d19822542620030320102c5a00581050f0f00400c014103280d000b40ca90101e0043c03015042840605a041941c481c1e108038a0009840f0070f07103070b59606140c0483e03403a00e1403240d903812140400d800c0070968a0600d040801094480020710006100060207040060800c550007903507030f1044602e14900d1000540010390740c100c4085d17002c4404200c000206d407001602814460690303840c40e00c09a40c048074203a20014106000c0081c005070100a000401d0000542d000c2c82c41c005580d40706 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 266058444 1250 266057194 266057237
    0xa110718093e01230327010207020307120503220801150303080105040605030c101e110705041a0904020f030102210a0504032007150206041a010b0906070f0b07 70
    0x2e0390600c01800c0c41654031180c04644004051201150190360b40c5803c05d203000584403c0e24000c41000325070400862641c07064004040725402103041313907000340d155a5154003101c0404002803c0d5441008188a0021840c100c0440481d1400d450380005540382c42130341c00c1d41c14840f4001045001c010081c0201608444900d000d000183c800304801402d2001095452000c3da0320107200ba0404c80414801d01e12580011411203070a800285002d03c2408000d004103450146105040c05417000118142c20175100b4403c140010800c0032171440b50890922100300340c0940700380e0b000720884081c0d1515840c24001440403480580c2001010203005045030b03514600034080d010303032909150510000ca80c0c0700c3d01107094041480e0290000845460620b4580903543d88008140d80d09400207050b8a81c011039641d2140340100040307140459894803502c0040c10900400d4022001440711510758280740001d4145140701d0214a000039800e41c69440405104481b00340c0010540c0e6200c2d02540c40052 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 266059694 1250 266058444 266058563
    0xb0a090c030c0503074d0601060302030f0609092b02071403030a05030c040f09020d0e070302011409060f0c0f10140411030102070c0303050a11071809 66
    0x35080b804c2d07041900004221020300310301c0700022041c400100684031603005180003503c18040c83c1030b07400300c404400144039200e0b5500b80c07a9503014020000828502034000c0b80d21540818a1511041c0d980340c007000014080504a040b444c070418802103005030750071100c1d406031158130801c503a5002040200a1503c0066044480102039901c1d0914039a24000160350a00c0c204d81003480e01c0e55074140b4520b640740904c1d4003861160140c0400001d0b56910750b40107095110714100d050111002c6501d00550329145844002c0c0018958a0504403003d061400707030031402c0c4020b1000340380003100020081d07a900911000c041b140c106c01001583c040d01006541e0080100510a010841c00162007100880b001440078107042d04121040d0311a0b07600303604a515596220042ca0100740c0c0728100140700342c20400200e000301d0035000e00f24030f800f070380001c0500483d03541e0060900c10100c881c4000004d071000103030481c1d040d80318286c01c16a950360320389500c41c4180e0b680d20800810501c0c0c4d22101c0b9000162 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 266060944 1250 266059694 266059697
    0xf060405031519021201060318020a090c11250501020f03180a03021306091a03060406020a031407050304030201061a16030203040503010c0c0606051206040f060b0a090c030c 76
    0x1044108480d46000c58025020321916030b02016590301c60039400740c00707040300c83c02d900720310301c0011304090118501d00b00d43e06031a080c0e079040004000001c900b55103180410710181d40446a100304016803141c540050324200028a46505651441e030b031540e1400100b1549032140102d60101d2821003034240100000604092009080840280380181d45901c0380d86a640e40c1160802c0380d0b0102038481000030001158041e108614a480312541e48000b410329008440744103062040b0820144e034440c2614052410041c040d00c0b2a454654441d0700a5000c40400001d05865030b40b000590360350284424403410950301d41a5807450546402030031503269422031041c0302c88110608c130070108443c003a41c0a010103201e03565041d0f03c20f400c080e0f145014640c0916415803c22010031207155210b808148039502c58407060048903154800c020301e11130f136a4000c4096074030400016010502c80500c488101e4010007000410060010219041c10035582081ca400c075180c0309140d8500b94503118110411030503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 266062194 1250 266060944 266060947
    0xc0f1b0b12060d0b04122606041d0d050d0b040e070810020a0f051c050a0b190501020a0201050d0906062301110601050d080f04031a010b0a081923060f06 67
    0xf0350f90102c00701382c00b400c081c0a0074a42c582611903e0301624603049a8400e2042c0162840e5100440c2e504904c1c003110924015414441000c0303e40459000200020b0501c0029081e805445101250f1a030400100c126402e40c5036038500f070fa15103562144100d280703401005003801504140c410342c0303805810500c080708a4410420068165401020300c00a0300541c60322a036504610940885240c40c0303210b40c520740034500028451061650740c480c5034150300944806604c00800c42c00c51a4061031440b441c0d01503040f140b8500c00661241c401007a071403001d1704002a0301052901d030740080b280790350050342a85404894885075501d00f01040094100300b417038400050b09102c080a52281c40c10322030640075030000301c1c4c90b2081003620803c1d192030001c1d00d01c920f501c41c1c0c0c1d6400c1c00340c245070344c600b0701a40b4040400004640711242d40103c484541294070744d17082c0364450011603059108085105050156034144101c415040c07a283d0b61a43c40b039042c414001400d0910801c08660f00140065106680 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 266063444 1250 266062194 266062219
    0x9080d05090d030503040311011d0c1f03111303030c03091e03030e060904051611160b090f04050a0603060b0102030703021b010e03030c010207060f0b010c0f1b0b1206 73
    0x1a0ba4000300c4495906140094603522180303420344660701c0e052200919035003000b02c0f40c5414010310a040140000050850b281d49040300184501190500450400c0341c0829000d800503d0003500821500002c0302e8507a40f510141c0390500c40b211000d60000c50010f80030412940034541d11a12240c09042508a9182c840496010b0341c074250780544002400d005130880200c0c0940e8505d4280e407240340d4042c0c0140401d00c0d2040380307003203c160b401e072003076000c1000641c1041240702c0000e030210070150005480c121082c10420b5600b91034024241c0107904c10000300a05030251600d000d0b6502a904110004c104031b411458441c007a02d100c00354940c11903100f8000329000c40d44c0080d4803c051003903009007044895884d0700480e005600c140da070b29098407000819040c1014158010031829000d44010055912195004410f480008803020300040c1c2c070140840206520303c0182199910603c494041c80320002c01d1006102a168820042c0c4180480c803542100302c81d49a00c1e900ca07070111500d002200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 266064694 1250 266063444 266063449
    0x304171e031e091e040e0d02030702090702030324150f031009050702100221040f03030b040b090f101e1805070c0807080408010f0e010b03060f1504020d020a09080d0509 74
    0x30319049680c80311107030b03005038001c25240c82d4022001b0741c804200f0f54946040082c0041e40c2c0341c0c003142d4124007a82410002921642c40801034038062101d42030000c0f019801041c1865080c01101190b1f603021803180000031500715150000c00c090000c0074403458492801c3c5102002569480d07014864860811040214096000c0361200d9000703c0b214006032178900a001c0e1800040c5402c0c0f607100c00c2e02c2014140024408060441c61485100c4c0c0c0d0300b4004110701c08140010f85005506440c2c101d0407000104940c0c500d01907042d03602c10301e100c0181000c42d40d10b1840a116200311130689146240d1301800380f2180140100b5114284182c850a0000d4109490002c0c544c55584002a14002c40410a4410001007030308440040034080000e0011308000030401004042e5240c141059600e0495000b9245c10045a45440f03842580e00015517541d81070620840588030210f480d0b4000d60030015024001d04510207440e40301d845175501091182440f40b030f50310b000503032010038013404030500800d180b95 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 266065944 1250 266064694 266064709
    0x12c0609010c300f0501031401090b0c090f09011403100519020f13061e0e030a060203100f030c03050c0a0b041401051606090c060e030304171e031e09 66
    0x20300d04110f149100c41c1c0c08107550000d8480080409200c604140314100104010381105050700d0150354494045c80010301a2402c884803190020000d0322130000055001c200c800140003842c4010706198988100310000480c00c1a00340c1001c0302540b07080c910103030203040c208010b01d10403505540400c010b0408002c40891040f81e550040e601c0ca07000140000200460000e075030591f203101607110641ca0f100c18015000030000b524040c03d60800081120209104080c500f040c0c2c0c402802130b20101c0d9440d1030341d1010b944010000a00d800b4070803c00103406045000c9200218010211800020309501d0100e0400b06202040e91250089072414015402840c044808480a092030714036200c001100580d07ca0180601203074203416460009070038080650440385469105602004c0c22a48480080d5111181c180415800d54000c2c0414404560070840200c040f110010440e000f20780310b020340680700c401c100c090990390780010445030118500c4110340200307014042d0010781080c40701000b04170382 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 266067194 1250 266065944 266065967
    0x4140708130533070522120b06041b050702030c030d05220f080a0b01150504230603070c0b070813060f0e030a02070e130b010314012c0609010c 63
    0x916400c2040303d00703a11503080c40342e89100f0009207003030391301e4079110240107900100e118400303e92104984071001c4401c1d403a4041591150200800704078441e44640c0302d000d00080030507401a42d40c004051603e400140340c007031145615550b9503600c1b81c40d4814541000041a07510340a54030155030302403601e4000c0140c0b02540400c05100814142e81c2c0a100b261051a900c40400896200d40c00f088650011510750a0280125000340d03135641d9588480d8042c01107400c0920014805100600c84004c0400b225000502e0b00d100c2c008400c400c00300001c0c05c0342e0040e03c0c8100031940c41030545003084410512903034092098103100e0362601c1d00c42c5440d50312581e4a400141500e50300c0d20340b4041d41030164048030b440d403100000c0326122890494040c1d81c6807014020b6030403c902c2da200081c40310380c00b03407000113465500020740045640303155188480d613401d001d0311013120b54a5400180040b507079400018240014a0001c9401d50000540c1d20704154002d0a07130210b99042c0a041d0101d0354010318407050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 266068444 1250 266067194 266067223
    0xa0b0306010c1b0302100503090d020f0c0d0f06050f090f032118150108070f0302030309040e2803030501051c021e04050906011e03171602041407081305 67
    0x60301e100e0011494a90b584c2000794454603070b8a000e1400c1ea4440003452083c031030304044503500108107106aa584400b00c0c00d0030301941c00f205449000e410821403c9a055100d802a01105030b1603170341c0d11040e550111000c00701c5c400802c003000000032041085541601c010f10241d03240081400740c46801c031800c0c2c44141384124403c40461181c4a1041c0481550848502502c041d009500800d20500b0420f1140e8026481001c0012070400070b03000204046030f500030700452814585206200c00b9041ea40198003250081c5a01c041c000500302c410004128400c1c0003103401c0c07034014a0050101c40c0187c0249014070225450241c0707074031540203d011550b804a5403c1402041118844170140403841d21641040c1083c3c2408001e010018445043c0d4005a4205a12000d00000c9183c403508a1102819200c0344200121008038161300400ca120600c980104a040703242e000300f010758000d622400241761041c1c08020b100c03275101c8d159075046006541080d030040c03d00d464141e40c0d8807005880c02e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 266069694 1250 266068444 266068463
    0x71a010320060f18040b03010605130c050c030408010b090c04031a090c040f1d0a0201050a030515060f03191503112e0807080106050a0810090213050a0b0306010c 71
    0x1e541ea03203030558101d10400c65015585019110140c05840444100c99004a060050b801040c0c9410301603d0181d400c0030f030448103a078401d01c1000b00544120780d098000d000c400c011196080700f00344020310140084900105443c9141c0c803c0c0040c3c11801400c61820200a10003031000035503105038040394a80f01c160b10707070068582c1011507040c09600c24182d5802490008820091625904540400d00800f40c80704102c02d02c100c09203454249400c0b0090014004200386903080d030180d400030703400130070001240d04400e07110300120312158014011109880d4001c0108000d022105481503040702c0c40328024060b43c044018010807888003400300800400513038451500707944682800961808585074224900c114411b07886190080160360480000c007032000154100e405049828100c95481e43c50a142c404101c20031542d0350006840480e10078825000000c1007210b900141081941d18820054640d18141c200841121603900c40840000180f08000040c4e0b00030700d00d085015000107079078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 266070944 1250 266069694 266069753
    0x70c020103110a0c0b090d05090d060608030a1725122009100206101716061101060801090f12091d160e15090402040e0a02071a0103 58
    0x40c1c01414070700a110501e600089071441d18198060000c5201e94001d40c1042c246440e44018541c80b0310f20302c2e600c5004030300c0070005051641020760b16010341ca1700409001904a4440d0310b0181140c1c06003510600089141459800a1800035141034001d05061400e00480e4484124003610560003075400c01805800841c101d80000560803010b03075010300f0305104010707801a441c13600d5583c1002030000c0c01448030421600c0b06070300000b141c0b0f02a03000c488086207010b00e400c0c581200c0092000300b40c4807600402d14030700d00480c903001f100c4001e440181c40c0e085441719481406801c50300300b41e10154444c0e04100884011904241703d480d2802c1d0000300401034150390306000c0c0e4a40760241c2c004510018845943c9164081c5071440700d0041e02c09030303e1926100b03801c400c02c458802442031110391010881012807501d954500007040d2240024101608150342ca50004800380c1c1c0071a10b251700103400068000401c400c104800804020030514030420354115201e115032042c0007481c4440403480b11290 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 266072194 1250 266070944 266070947
    0x180f06160201020f1b07120803150a0b0d0e01051012140f0a030822080306131b09050307080708070b03070201090c120b09010b0f011b0203010924060b03070c0201 71
    0x4542c070641c10306408030b651748842c00c240100140c0f641d055079000d0060040c08207514000145110240303800c09032050440e01d80d05001c941a251040720130303912007010310300022114480006404107039000032001480400000c502030135108001c000081100b0741e10700503c9000300f0380c2400c200c50740d04100d011a80c079040c110760038644407808214045600c0b810640c101010382c0700340d1092080100d0700c803c000500e94071075041d05540200304000c01da100c05000081c91400c00c50039420b42410740c001c01003440c2e10340a010f0050301040e00c0300380c0005a1421801e1065050401c410300007840f00030018000c062034000d032280c86120301c0c01408042600000811a503510035003094054a07040103880c0c1b0180d988880f0142c1c0100c2c0a9011a9807031070290009030070790410301c103d020103103000e01107620303002e08440111031401030b00c46076a07103d070344054007080941c030240300320048140314003041d01304000783c10240c0d45000c0445002d5a40141001c00074008040d1000580790001454244010b041005100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 266073444 1250 266072194 266072197
    0x20102070b0a0f05012115110726040f0e06011709030a020613030504050904030e1302090f030f0615010c05060a060812041a0304080d0c02030a1409060426070905180f0616020102 78
    0x2823803204d01d03070701090f0181400140115144680030381202241c4150006101c641c0b00c0c09075124004070b00c4089a4100300440c038119506a10610501d0000d03503a04000360b52400200c016601c0f8103450744081601d05420340c040100c00d400c240803030801d00e521699a98011f2031442113010f43d81c0a42e0b904008542050b008135070a04603100c0c0280052600c03051401e01000039041080c03014403568500381c5001c00d27800c02050008a0740140c0014082994403074130048241c2c802001d1480c100841214030402040e0144007107402220318080100720180782644a524000f80c3c180b00202002c0200400c00ca61a00300200070403001040350841c0e03e030f03038907820320f10164001e03245010101400e04c04128030842e4080000c1c840488561208444241249060701d1140516804103030000e80800051000380c0c1c099204202d8a0481c2c0c3c407022440251440007414400c10b9400095003176280e40030301920f40c0d42e006500704503202c0340c001440d40786021b52600b83d50362005000d681c03006280c0402400310307520070340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 266074694 1250 266073444 266073461
    0x1b0f020613080109050c040b0603070c031110020c01020a090e0c040504051314011b0201021c05090c0303040603020d060510020a03080603280b3301020102070b0a0f05012115 76
    0x2c001c00400d00541400f40c0c40f1814003000b18070591a04000c44410310346401030364021a00c40e0303569030021a0f59a820703104180792040c24541e500c0340301c3c1c090110240c0d9000803c5d80310140c4002503107526800070003801c00e40340c3d0b1f00214501c0b01c4400030800c4d000421400d80b0202c1d0f1007103e010a058417003006114074800094005040382c000d21002c10030b2810150400c1c20320101001c0b02081d44011b080e801c134202d02a8058030300c07000c040016007004402c07842d0005034001c00740700151043d43c0494030002c0c0c510751041c0e00000200c2d0300407900c0d0344502c002e0f2003200010311054565540d04007804000075240c88402c01c00505011600b001700d196501d041210a5940f009568511a8034494000d500b07503850350070101311980d0616000040040116101110b003c1c0c60703500e859140e0320107103900c040c0c409140120980c1113660134048207000c50003031400c60303006800c0001e00260f005425002d40081d42c1c0141c0018403014540c168107280d00d806010701072005604145003c0c14911407510b400040d10208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 266075944 1250 266074694 266074709
    0xa050706050709030b0a0c08010509091b060c03031008010501060309120305070309051002090915090f13052b0e06090f0d02030604050f070603090b06010503090118050d1b0f020613 79
    0x7009480c6e0074591190007a26180d4032500810703a41e0380300b001a0712008442401540d013000225000655648d0000d61411100410407420642000300e8103203181c104451034005a044030a042286071400e11031280540305528050140f807a03a6201d9641a61441a0400c01c05645100007000355101e80c1c0502d0f520350740a000e0301d5800e602500007401940190254a10500e80390001c1049070800c0c0501c3c02ca1140040c004203666542d130186c0c462055001000260700c0f464035000040010010710000008108040036800c08038411040d07240300211990005042c410003401c20851565640241e030808007040368003409410800c00401d4508010100c025010b20074a01400100500802d9030718107101100101e031007084c1d07280c0084050307414682d0090260241440490b0305540728400440c0d005d40c1c0c800002c81c0500b800600007000752140d131005d5234290043d82120100c99030000c00381c2203002048905200290f010f455940b0f203099140c00003881108000340c08049202c25450100080a10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 266077194 1250 266075944 266075963
    0x901020d0c090f2103080721150e07090e06130e01060e130c0b070c1e03031211030a020a020a05071d061c030c0204180804080c060a05070605070903 65
    0x9400041d1010800703015074110100307a04004650b26130801d1818a60401d11a8503144080260320159000c20015100d8010003e4940c0c1c101030701ca4441d4003d01202441d0032000a5a00484101d094080d0f19500002d9403900c1403010300c00340550040030002500c99101c4c8407102d0303407203803400140301d40012090f02005038100f05c400320710507506620090858040042020310755447c03070b642180080798000010026100400306028089040d80603041d028414144440074948500f94500d121352405081014403101c01d50620030164002c40300e07030272484505001d1114400900c0f411100d8000101801032650340481d8407020030340f080100c200301e43e4102d810364a15a4855003d514a0854a11103400a6104001041060a105410b400c02110011420348004041e54040f82d804580840680c0d01540301e400050883e90108466100c00344246c4455598a1401303840a052110940409200768014001d9401303454100044031065a4410310024255840390001e4484060030341025007003241 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 266078444 1250 266077194 266077211
    0x702090f18121b011404060c0509060d05040303150f030305071a01060507050c18070c020307180f050615030105060a050d05070314060a0528050303070f031b080406080901020d 77
    0x410700080c200404030b0103541070090081c1c01d4003400c1c0d40c045c1d403840129514410002d008200143e120011940d007a1400c24a002d40000018016801040e84080309954410921003010f07014468030340c0801105541205103851329580280d100d54922000d001d1000020741901088024000c0c6600c001d2071680c510002e58423418002e1032608507000031512403280701f9500d41d0302e00e030007040071400702c1d04a0b4521410703640302c41c4102c2e00d00c507080d002240c16114405020070745108142c030155010300c10100028a8842245000b419140301800b83d5008043c104601983c4070f15402c01c4a0540f841038581554404681c1c408231194030032103003080c41281c030308410711a80e00d0341a04201103411b91030310507d003d40c0b40c000800032524154458030340c1c0100d0501c03148a064201d001000e4101c48454210702c5440c0d035980100b400c503442900c0494601c1041c2c0ca480c2c0401d03030001403070030881244c17914160345a05d042d034a201c0c6c030384118043c090500c074103400007410f00c200035011500042241d860500c00c880 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 266079694 1250 266078444 266078473
    0x9070201060509070309050c010e060c0d05032202090a020705070e0c09041a010210180b0408031806070e1c02060d0c020c0d0203070515070c0f0602120702090f18 71
    0x1e0340e000c0e09203d030082d24046200f0074071901030a1a40c84d0454060828007a07160010744840c4a98035099422281c28008422002c809124100c4020482e44078190b40346001d2211072007400141c10040d00d11400004080d02507180c6484031036000f1a500b0006a4074010350030918980690f5a2061307480c4200300d030801540410310300140c80c01c648207450502c0140c8605101d51850b00c1d9410700755005900c00013004594a0054003c40030f040a041e040030082c0c1c86640340e049200314220b0b0159030b0580008148105080d11103008464100c10720082c00c582c1c10003d06c000c00030084159420700ca11550503a11100b190703842c0848440550003021940c0e1009041e0000700600b44143e02d00000d406160500090790806960f0488031a5005010301000c07070401c9c003040480f41d034400c5403105072407080c0601e100050440c0300480c05880301c0c11540c81881c0c80d1a100071700e030510005039280300740707000d0280d80f0058850f5441ca035001020320710600402e0340e07500d0f1026003002810b088c0c09141e1086801002c40d10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 266080944 1250 266079694 266079701
    0xe1906020a0504051c2f0904030908030a0914011806030902041104030b090f0712020d0501020915040f3302010902030d050711120a08030c0903070605090301050f22060b09070201 78
    0x40d01c42c544550b902d042103021103420380d1446c000e8515600d92000561041c5c5012107120342c1c080c2c4282414904c642d150711a01e841d603009414807401049448a003444511844100040b149000340b81241d202c6680f40541007214100344201000c0c5501e075249142159560f8000042c0685200650b588840d543c0c20707c000c00c108140d48011782c500490703084500ccd12030042542c3e01510302c1084040c078040681c1e0309026850103e43c2054480755400e00101200d603a4001c0410700d041ca0010440d030300c890404c4000300b03003440180d02c00110f104400501c40000c0c03040c80f4100c600019400100419407100d0407050b80500000b1000135070501600c0c101c1004a500100074148803070003202000b0042140d1001e0200c0041903103000c095550000940c0c0c4005280c070002964840000e0030075504040da00404071307203405110303000030b00466408512980f040c00c09100e034540c0000003644044ca1410000e4a4202c04200c90042c0d0390f2891041c2c3e512800d0020a030801e941c64000504000114034140714003c0c002e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 266082194 1250 266080944 266080999
    0x6210f01031b050906010f02010207050105070908070602010507140c0a06090b16020f06041209080610090509061006030b012105180625090b0714010e1906020a050405 73
    0x2000c908042c2105290a40e0040281c91025054200b152140700055891440105aa808540d000c00038000003810070f02465008410355102c1d5000203051032883d50410345d10350001011685041c04001d181540101c8180008074807038401d958580080381c8a03420220413860140c207460801c1100c1b410040e00c401017034407917006085840c040c5000c04d08126101d034015410811241c1c040004900403803450b01e85101c2081c0c0506018038503d0703803542d0481c10403038111040000c41201c590100300041084c052554402c4855020700120b19103a0400c0712206c40e6070003844101951091044042e07401403841040710740300b007408002e1000801440c503026004c1260b040d42120b980703112030104d01d5800a4014080c060301e20001c11424401010700e49402c004281100411a40400001c0c0f40211403004000490081c42c5421086e410f480d111401d440c0c91484083c101e41c0964440c1424800e11f1440c0d0102e180d124002581e01c1c48840780480d118091500410b5200c40500030f10840e60505030500d860 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 266083444 1250 266082194 266082203
    0x507020c0112061a03061903050a0b070c21022811030a0803010306090609060507051306080601051806040f06090e13020a17010f05070201090b09010203100506210f0103 74
    0x40305203001c640b10003a18200e22603040560714411241072459590006140c0c0650301500e0107440061040d01c3c481002e246030700c15201a04142010b40038032081c9201141d003d07801d1300f4102420f02d22903030b60294880e2400103846d03410004000a495043c801d004c0c81940182280801c0c0000a802091070340c60b40640c401200c0054480001c43c40301c7c11301081201810f60800c404a096a107140c580c5409400e050000b100c3c0305983e4041080014641e02c1614014811a9110703a00d03040031041340212130103141c001070113005041c020400241c1c0d11004031058011501c80342a002501c00c0b001ca84070b401a80c0200c5030f1607000c00004540a90b01c024014121550034001d11219100c1d0358030840707100804c01020b5004802031005000608003083c490540070702071400014204249505c2408841c000e030760ada40181d450713044540511600c8107a0b00d402c810000000c40c6103003004103042c0c5030740025220701c50241e0301c041140340382001022140c080e00b94020806c0c20591900b030401d0882414240800c54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 266084694 1250 266083444 266083457
    0x40507050c1608070611190b0115110c0d020d0c0b0316110a1403091504090e030c060f1b0a0509120102122703070b040614090a02010804020a03060507020c01 69
    0x40c00e142034260102c1150610000340822509204007154400350140d00640144100d5060407480440e603d903400c00a8040c0001c19141e50500d4009580c0c2a178140704001040790034000c2040901c80880e800341700c194102c1d1141c5d2601e0552021948510302044044c0000d0303005c403000610484520000c40c840c40103240003409142240300301b41c132100c0210169850642c840c00668000490b00000100d50030103100480b4103181004002403500e80345031410310200c40012030200140d5a00e13000d11312940c515a8040c60230f0140c0085000d03031743e540052850740d03d11441804600c200409070210f07001d448000400035070b035401d400030240542d1b00c140d00c010300a68015080d20141c005c1032085e10090003a00c150088903131215415501540010f525445403441d8015095000403000c1000f842d64510600c681e1103e4a094284001107810300b80e600c020b240f2403101003004a40700458148841582400c0c0a001c680321400032680803821904000c0c4118a000144103100da00095080f003040400d0b42e400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 266085944 1250 266084694 266084713
    0x209090711060609070e040c020a060606091d04110d05030c070b070f110111010906140a0b0a06110c0402030906090706050a0e04050a0908161a0f04030503060f040507050c 75
    0x3100e20160819034031000b6045880420381c14a800c1000c16007016141c41e18a00400c1c2080004044816900701800541c0c4069048420807200c0c0c01003074000c203080e0410215003807500800c1c1c1d196151605601c0f021044100000e001c0040081414810b2000500790600c0842246802640c80d404609540c9041c4503620300017447d204d00c0411a01c4190344070381030150000d6590b94415890041c0c10b041418000880c5080040032001d208040220b80984400305048401120166651a002e42100485410f1200048054464a100e04116134151814081d03140304101000d04007651016940e60282c00081405052500028858000c1c0110401d450fa8140c0e0741c001130b00c2610860b422240820144d00c0d00102d18a4644d1041e0b5200882c0c0c0b00105184c5590369a415040e40030002080c1d02c403461341e462005004107450300c14401c49200300c261160741055140c80c031414500600040411500100180b00c644450980da6240f40014005202c60f05012402601c5600901c80c0d00025100c0c0003203c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 266087194 1250 266085944 266085947
    0xc030c090c0e040203040c150302070308090307082508040312020c03010902010206010521030d0204060207061809050a1401060909150311091806090309040e030c0c09090f07080102090907 82
    0x500d41407101680b41c5200888100052101035000240152501c0740d00c031100040410444548000c6510299001652080107140161080c0c1e00034280e807401e91b00500c0010000360682003100c8080172050707203008201c84030903800c000c14060250700802034200030900008006e140c54a022000229400351520b042d40e0380f081c10f00302c40c1d651901a005903c0000104024105145285110001500303040880d02e07135000410316603446030201d89511680000c08205460341071144002600f41c42c581301d02c50004007040714042c00360602034400c0c0c1c1a035401c003080d012801980030034002403040300703148015a56480050102d25043c0b0855000d141040d181e80d10242030207441c0c03010380350b214100c0b484018055007032004021000b02000088500b443e1603600d00344003004101e100700d011034000d42d83d07400b0160502c01900c0031a034501006500c14030400291020200301d9010102e03041d600d00e1181d9403803822251a114004142d52403d0291020104c0c0c0980190002c0288a10a5500a40944620780d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 266088444 1250 266087194 266087201
    0xb0906040b16050f0c15010b0a080f07091509090507030902090a0506030a0203100b01021603030e10050d09060203061e012307020909030a1101060515071e0c030c09 72
    0x40082185800d040051200c482900e4206000c0546142c5181480c6003842d81110702d5004008a0f045d40c1d0019020302c40e0381490b54615405801480400b9007440c0354644007070481c00e009400030300c0700b02a003c0010b46403417050602100804e20707a0500d602c2c030040c440001d480182e0500a0300011418140003844990080c090340b01c1c80e55010b00707d800c1c02d0707031f800d400709005100c00b8102a0745401040c3c00c1a0150b0380801c0650558541d001002034501ca03644006454009202c08020303442d0b000d5181040070940014941d1040030701501c503829400d050120894143c0300329160103080c01e240184c1941031000517170195108150685d08244c1400d041200c0b58002049035800b280040e40c5d80105110f800e103100e00d10507150a01c040d8860900d5000c0c0e0001d00c24490413601405594008900d004500390b20404070814101124001c020715800c1c280865405112004800c0304946c00240210820141c5524051045041c049800c5a4001c1b071806c070050402c940b1013071f00e20701d41c4000082641c001511 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 266089694 1250 266088444 266088451
    0x150902190807050f07021507080d14040f110d0804143a060603020306010e0403030b0901150c020d060509060402010906050a05041202041b030e0106060c0f021908030708070b0906 78
    0x844040c1130501e0000ca668840d441580100e030000303206984600781d103003601c0143c802103100c0c003542a190202401f00d01c0407a640780441800100340b25007032001084640381650441034000381c1012001e40f0100c08200305403042e0740002c061803000200040c02c1942c0741c2c809035031018115030840500610142901d11030781c880030202c0d801890441c14007910300c2c40300204005584240e03404203006940390002410310500340c1c424402d42c5031550400c0101035140c440c0c0300301081d08a07004003440d4109841520121184065001032000c1102004290354810102070502d80c0d2104042c080d92500e800c22035101c0000303540803408107460348030214100d80a5403d6a140c0c40d82552841d041034502032070711541c01c40c401010398005958008130302600825520303140490a054401280400c0c0c01d500c1d0750b00712407055100e0800c03c40c0c4c0280e4200064000b00f422f500582d012901c0c1c0011007014004118030f1096540012413a220004108040111a4016041090044180b0101d650341c00d031b04192901d0086 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 266090944 1250 266089694 266089697
    0x70b04060b1c12230706051006030905070515070f0c03051203070f031a09040b07110a05100f0e0708070806010e13120207051804020f010903021302030604150902190807 74
    0x20000018124032442d04041d5101c020341c3c801c01350303002d0300b0090a2190b0000d01c09a800c2c5485000300030308000b83c5c0b0140c1c8000c021625040004010700d45902e6104e200302e0241c00d208403504074640e94140b03003a2080d220b0082d000b1903050a60082490b00b01d410344054401118180078121004024034105401d5038070801e040d8a900c2000300405030118000e0520150251031a050450345136240d4446004e40f910403480f9491000c998280850040c0034501740d0034044500da405101c1d2900062804a803554204d00000300200c2c010180380c1050028200c4240391b03115600c5002d000244400b00091032000b10b851050a4610b07998071030303160302941d400c121081d1541203c1c0e0a40480000c80c055401c10310312004e4410750703081644a8000600c554041e11000f036852051405000951400030400340503480c00742040070485c1d246034085258284903a081c000c0480d1301000007901511560001c2e038581d0030115031424080c3d12120054000c0d0000a10313205a01820f0301e00709400c5000d07614560254229 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 266092194 1250 266090944 266090963
    0x203060d060902030a080f18040213030308250f110601150507031106070e011106070f050d1517060702071404020a0201020d1a190e150402070b04060b1c 67
    0x16261803010b0000150100d80500c685500c0d0030210300e510000d003030450419000340f81d51f0b4020580d580500f249100420303102d940304006120355003061080030302c11654075043c10032040d5148644a00201c03c807481c210401e12008000c078903215030100a00c00c410540340caa8034001c02c1d01408e010380e0303000c1c02d0044502c01840c03031500040303441c0590081c2a1251003440c10120888111704000e0a041f002d44a00c8041022200f15840e103680005040120800c072070010282c91500190081c5451820541001031040001c0c0c900c101600542110041c81c40d24010004a00c2e626899003540c3c100e061041019800303210041002c546c80440c00204035080c145d00b03001e440006408100c003c0d4041c4440300f081d2366081207912080c1c081405000c0e0701101e002d070b08581d60200c80c1c0900089a18041e10a000e940c40c001c418081030061179540343d00190200c50401540320000c010400074443c46070050800e401e13101c2001700b08142c9400060500c101680c0c0003680c49812482c006034144100d1006103007980 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 266093444 1250 266092194 266092219
    0x9020f0702040f1d06060111061b1b1507140306030c0402090f0a0e070207080303010605160c030506190c0504080303060427080d0c0c050c040b0103020405040627020306 74
    0x20b241d08031480007550341e82e0014010101d925042c994146400040c00c0640007642009110b60300810501d500e482c003640030700114540130070b858450b80c007411030300100c005000c1000c90703080c01407510190221645400f220000712800c2d10100c1119011148040095940506020191103400a41e4000c3c031001d002080c811004004001c0a0340004c884190402d40c03c4240d140244e80d10482d03540104a0392070207140c64202007100030f0510410360840c180ea68020001003002e0f81d840821070700100d189620048000c00149000c1c2c180e5800340e880580548207050901022000508034240d4903202000108a0480101e00584407401903200c0e28805400510000f5480d00745600305500401d2484072012410300000603006005640c1d00003038542400119841c02441c449104400c80b64516052642c22042960380d06691542c803144210b00850703d4040a8005034003e07016a0b0142c64001e009100c80341c0c0b644007403903072001001803842600c46220303e450060020791003100c2c01110040e006002c40740 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 266094694 1250 266093444 266093449
    0x51509031b0f030a0606081603020a0611010207080a08160801060e01030905070e010602060f15150c071809030305060a0303050708032806050f1206070e010201060906030b09060109020f0702 83
    0x1030703141c80840d411030b2030605105082c0da000d114088080340306800005400d4203044e441840c1c80030144c05590300044013801030000daa2003410340d10490381d1602d040c098100e800100180a4040ca9000614215000c00d01c14469038210b51071038810400b9401c0c00d07000c0a441041228030510a00c6003101017048504100400e502c6900f0a59600e4000d03003c5950140c1d8645001403005000d030300003801600b004081c0804c0103154424150088110101c1120f04500301c0005404d020419000002d0350a00058001c0f0301c150500c680d000405042e003030011045248036034203001d040c0610048000034030780000141c0c40e02d01512001c0617039403d680c07110708106880d9941003559001520301a921012a24261700c03144a00807040e600b071044805c042070345440e01060000c141c5002090794401c142080501c490420b0000e50070b035104906207841e0640e5404a070050b401010140c01159885081c00350220502c00c554070910b009844040880700b0580c2e030343c1c2c0c5920403401643e081501548081040c41c0c00751 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 266095944 1250 266094694 266094733
    0xb041704150e041e02071a010803130e010f0909060e011103061503090c010c170f0d06060f020a0305030a0e030403060606110318010315180e0d030c051902030405030f0705150903 78
    0x43c0b15520b4500034440d0004070304000d950989c086c44c1e45600009030200030010210340000207040d035001e44180ca50402c2501c0c00b40d4000c81c001c81d0358403a80d80b00800288074940d0001608810341000030401e0b2040c007000190590700c1120302c513000395441000050717984e5020701101d1080403c80c01402d440000700c0c00450b06400100c0c8251107003003500b0b4202d41c9601d1024010800010102803042e0341d00511100f24044e101c0980c003c0d014030900484030ba01c000d4001c500c02d0259945450000d036a41e440c1a00003004140d00e02c15005244404100030040245603813100301a241c0d640c0302d819400132408599603a9212307641c0e074509807103491222004154003e402c098803030b50030009052949134654036049516240a680500c0c0d0031344400c0c03003034441c0c501407140300c00d20505c40c81e043c050801d0982018081c1c0c0f0850002c8400106c05940100b889403003401510081c040c0202503540b2080c650410710b40c0d40c41c03240182485020b010540040f26000801155031100014001d03006d40d00100c0c81e0324556 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 266097194 1250 266095944 266095957
    0x12080a0207030b0f16080609060d020301110a11070812040e19020c0d090e01050a21050609060a1a130c02010f0e030c01050c03090a0b041704150e041e02 67
    0x9610800202000140310350750704512610401040304907524000617002c070b000040c0d41c0400c05000144050040546a403180554488800d54002034007111a20201e401000f40302e013600500700011a0300200180e105942d015030081f62012140f03041d4071000f40544980403400e1074500040100010401030f5610f00d20641c0c0140c001c90201c0d4006038040401c81a64070010100e010b03500282e030860005900054102d0140c500c1420343e176074560420b40803a84001c0305002c0c0f0609400c00140403040c000d200e6591303072003160b0b000c0e09507851070a10004080d600c120588520001c07a00b040b044000c680aa103088404005006046071088003444144000420300c044c0601e0855484181ca408082800e004125800ca41e8400071030780c8100d10610a0300310351000d040360741062410002c1c0500c809000074082c1c80395410003113012076600c0d5440c0084040121414032301099002240020742d103054040c4000313000e0300645510b0010407a040811086030110b00c568800c190444400703101f90344850340546803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 266098444 1250 266097194 266097197
    0x3020907050904180605361c03022d030f090f150907050406120326040f03080c1201032015030108120412031803060207060b010e0a12080a 61
    0xc0c0401c660080341c01d51312a500c0f8102c0316803619148400b007144900c6007992003940440040c20344900c081d49100800200500b041880b0a000d400015444090081c0345409241d08991801e01c0b10f02c60014002c0d4110f00721040c002c018030750f0b42d906811041038094600044061034a032035030341c48607086000c040c1c01400260311403045044110b02c0b0032040020508500303009600d036005191203085a8500740700c50308058000c2c0d081000801c1103501024840705102e602d07052455009500c0e00d02030040e4210818602e603100c14680a1006004080300c7e1202c26900994070070041c1d654640d000000c620450440d01101c0b41e204c00104040750840b0b0250554520050221311145801e400144988801c608800e0400400000400038034204010041d01a00071400550506184c04a01c887d040a00e04c0043e0500c42c1d054500300001e5101c0e643c210103958000d108540b03950903400c044c0000c11540c8055404140d091003070300503078607051184400312591443e0503120340e82c565844012030b0b00202c01680 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 266099694 1250 266098444 266098447
    0x1509080c01020d092d02040f020f030a06030c0608010509240d11030105090705090c0f090406080a0201080a060b0d0e0111030708070915080a15030203070f050a050a0f0302090705 78
    0x2154a000380000c109920032a10041121120303070814250005e600b6140700e0306100701480039415041e180071030b20001501106e000901e2030301c10401300d020344180392411003c1c120020410104c485984d0002c004e40c1c1c01040a440c03025128442079809103403e005541d44049014005104480d400d000c2c1001c404c0d401c4541c060441001c0007143c40c499030680211401e001c41840310b001400d091150503806490078000709200d51400380071816148010701918411807001550042c50b4585001b158144100038204001161307403407140a44910700c05000300d002030010000f248102c3c6180c0203420603200c081c980c1c0e5140c600710208110090800b0000303400305540300c01d490403031040d00b8005984112542d0b201c85221b03281c200401410000b4a8104d42d0207900e44080b8480301640c454540e50f4040d54100001440c4150b0210344d000c10a5140d0000794140300d11302e4080389150032240003900711003041d1100140035860f0010440040d5032030180c4002904150310400c05860080e0606400410b42e00303165 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 266100944 1250 266099694 266099707
    0x2090d12030207020f0301110f070f0b0f01080d08090715030906090b01080d05031005120f0a0303020d0e01180b0612030a050417030702100f02101508120304150908 72
    0x41010100801a20042907003c26200150300744115100e0580c0c00440080040c4039640e0703505c031818091541c0e903690307031b0501244803000c025094010f010980d422604215181c989407441d84010b0000740035402160060b640c00012040c05074281c0d600031410000074180c40350400349504104814440301c1c10426407503079149404610144aa44111340c02800356900e198113100c080d070303c1e240c2030300c0001c03082110400811014004080c8008207540c01260401400300401410b1868031808103150402030155103030680c1055019401403296100200b41845014841503855088401070b10007480c0700090302400ca00007544089079131381c0c404002400c1c030350f00d54840e030035440c6036402903589580402c0001030203100801d00641c01c0c04034280030100440c5000c4041c0e02080c404041070f0030398001d005030311160b00042c500900c40440002410081001018902202c0881041c1c85104085103030040c500316101c00d20041044a01c15508403a0041c440b00c4c41c3c44600b401002840c009482c0900c1c107005d807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 266102194 1250 266100944 266100953
    0x2101407080403020102010b01211d030309060603070501020f100b04020f0a02010b011202040b120703020c030a0818010501061d0f090a0f0e16050913020a060c030f0e090a02090d 78
    0x150400c103014950aa440394214400a4210307140d12403c00d06000380305c04640300b20f001c5031565040940d200d40300030410075489030404035808441205007000c1d000110030850000310001e1124072030070088086619007650ba20040e03880e0f00000742488160703081101e00300f10f103070446d800015031800081e01c0145051461000141190008803040740140d4691001c011f2a41c0c2c03140c064002d0003548141185418900000141c00f40f14426140c02020f15072400105c1c131038001c0d030585400008410a4a90b01c02d00c0410081c001c520440744035601c5040c440c41c031401003505220f1030741640c000307071030b0603080d80071201c0c1944a680d003803400740380e20419140b135120039500c500c59554043c00104001064000d1038038021000c3e5440b0790080d0140d41e1110080100c03000390303030881c24125501a078808085441d0b068400c00b01000c80304000e5008020514000b41880c1c4c00500410614000d96861030050b000302c02c00c07900142811002980258030801080400089500400c0031003001083d06501c103425035103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 266103444 1250 266102194 266102197
    0xa1109060f25030207090e3d0510030606170303061507060c1707020a021f05070b04030c030f0c0b010b0937050a0e01090e030c0312041202010e0703021014 68
    0x2400c60060300b01c0441000b444500e4050703000c8440d04080500000f01c643d1235000c0030005001c0919403a4591941c2c1107080b403100040d55082200b07009810700c014545131441c490608503503c42114218a030400c0000e001e2011040c000d2000c000d14040c514680f02d4600700702500440d410300c40d2034030504112550005060740700d00e030070fa40169107a6010540102d00300220780b50300181902d003035400000700c203130041c1d50b0b41407080c0e044c00b40f07400c1170192481401c504980b0b034090580024000c080e400c0a0000713154010000d019020300c00e6560004003404010120303001303c04008002c1c0190498001400314800c500060001c1a03c0601043c20302103014000c0d45800e01006801c1c15004203140c1500612130780b4031840c0c405003500740d0320a01c010b40fa011080b000078805204583c031296607449441e000590900c100e514107150b050859480c0e1004548800c680c1200341d401b00c03051014031184449460041c021010366a1100002d0701d0243d245800b40072a11181506090030032440c5242d61418041d13140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 266104694 1250 266103444 266103517
    0x2090f01212a020606040b10020a030f09170a0506100e04080d020c030711090109200d02041e240f0804020118031104140105030703112202030a1109060f 67
    0x3e0050415003842030601080350380d60f8400a01848c8540d00e10011180c0001d030040070a82d00d8600f48012020440003150801d0050701b041d0400c0c0301d401c0707028290941c0024007501c0c2601400540c2c0c15511380c09403821032210130b442031400d280031030307000a80131070081030181642484428004d482e04014500c868216070107420b089404c4d950101e040d0106051078041c0b907014080407003003040b1184525188010401c110501ca1002240014503469800c14a4064070010300c601c6ca41c803403148841c007a280417065010b0044a02803a00f43d86855112407811040340010440c41c2c507040707007004ee05503046495070300080c01a8144101002c18840d5060f130200003c00540c0510b0040440f00309000802c8251058103600d40c8000d40d8420040c010b9a4020130140c00316a4414200344184140d403010881c00c07000701000c03002c06060b0f01107001c0d01400940003540f0440100400700484111807d0441c128050010340b0740d04080700b8407111024140c9040140380041411383c118160071002c0020030084040354 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 266105944 1250 266104694 266104697
    0x50f04030c15030506030609030d05100e0f070206061f0509010923090c0403020a0512120a030902120105100b1c090f0c0614030a23010902090f01212a 66
    0x2030b61241055142c03081d40c0c2c02120860150209041000c1710954074001c590041c0025591880891914500c8001d094010f10362030000c030752130b860040140c02c2007400480301200540a50000a00580340a00d41e000604c15a461006004140000c0440f0b99170003003c0b5250510a041e41c001c01c1c588204100310403400007002e0404c050907404824401c5a8201034807450b140c00042c0010310040e0741d95070445003035480c2520a0b911503103629070500c1c6048940c2c403100345440d4000034100d44c0c01c2d46c16000f00e800180207641a448103021004054201c8204561802980b2181d6005015a0f00d2103030060408080401120307111542c0b592481c0b0403184060707000c407200948007213490100443e1641d080300600e030500304140500a1503042c040e07140b000034560100d85664136601e50b51020442c10440c1b42d0408002a6a03003503840d10009002940100c0c50f152052403449056a42984240c50042049030300445a81030080c1b40c101c000c016001c0184030b020362400f00c080300c190010344407141180000d0503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 266107194 1250 266105944 266105969
    0x2070c090501060e01050705061b1b15160e0609030c06031f080604050604030e0a03051c03050c090102031905070b07080a0f0b0f280603060f0e0610050f04030c 70
    0x43c030718060185005407035894140802440391101054020541e05d80c410404241ca2000d4126080608900c0c418840541011101c101440301030f0800083d07081102810200400b05940751800e4900030290400c2916001814600821445092500c00b5202460000e0304a80200400d00001105a08120f80c613841c6000010040ba031500c01d514015001408003101500701402d01d5201c0381e499540042c03024091000d040814481074580d080000004e640080c1951070005c286450714022003810348024000a061601050020b11070004a4441c3c20058004516000404801c0d80c1103294201074202803107000d0141001107204103264070300c00d08203592541004d150044050040711840111068000e280c407405e1021510b03007084060349540102c13890a800038200503c4209824100fa003e0148a204c1c0000500503401d80c210358191490006641481074440b086402e0908040b01c207543c2c0700d1aa42000e140c0340b40110014248290082099454551246c03201a814040c0f90300040c02e0058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 266108444 1250 266107194 266107199
    0x50606040c09030f0b150a150225050f0a0b040608181603061805120909060907090501050a05121819021e0f13020901080f0705030a020d02070c090501 66
    0x5081c4a000c00c1d650301824502c11541c2181ca90351900424004001c0111401c840403d10038140030300c06030390b040c000074004043c40d44c4072040f0000814881c0307800303000f5200300003566111400070b402e8000c2c00b0600381e0396078003524074000401520a041500080c0c1000001d003010422004810080c000340909444040c2182400308112806a825000750103951308a0380c080c50f0400100104241200c3d0080c0703010444000d41b149001d1601c09441740200144038903007104c509104020050046140c0444081215a90740c03001c0c8104040200c0d80c3c4070008001c0007060103503601075005004d0500e01860400c0c18400002d41040c1c84000c00c0e40c04ca00d04a1309506101c141c2d45d0100040c0902d401d158400c0c5200c404030b580400e1a52044840030070b80081c2103564a4079030348614031419000d00340100407142c11000802e00c00f00a42c001d00d01c01d40001c0c2c40c000062202106821064014031440d40d0f9945190b03110910340000f5004003c060305010b80800c08200070172a62584c1070003502c003c080010f050351 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 266109694 1250 266108444 266108449
    0x207020d11190b031305010e250b070503090402031306060f05040c0516080a0e0d06050109050c04080604060f1107060509100b010504140406031406090613080910021603050606 77
    0x1940070081d0702d00d4016000511a048200341030304d070003c074540ba49001c1c803170b40307481e000d4058410a034040d14070740300d0700c20f0364410b0010101c0c0524107a10165180340035140c48410a04c418410740c98003400f5907008000d10070880c20658000d60307121141c0540800c203000c096444105403500c03a4094441803400100c10701841c43c1a2180c1090881e460410300c1c42c0104810141059140d039403030203404000d0109070404014002c01c8040d40c8007000814081641d4001d10f4207800801081c010307000314030723304000102c06203004000c031402e0300c022000420890783d4682c0c40034051704c03422510765426501c549548043c1d2044602800f0294070960000c1041e140050740c2c01d00e012074030045461001d051401411169801508a4003a40e071044140d480b02040580450060b02955000070490386d49481190034080780442c3c401e000700501c40a03900191070392552030b4078110780364201604000041013103603802e1810903001800e000c42070050b01d165440800c5850500d0040342c1c8160782e6138109004110007031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 266110944 1250 266109694 266109709
    0x11106010909050c310608030c0a050708030309070b1c0231120f2a0608060301060302090a0903030b150a0212030412211109030c0909030d0f0207020d11 67
    0x54203484404031100203203030902c00c41c0d43c8080d0400031255003845c0c5034400c8265800440c0501080001c45ea03035400e0f51100b190f07844c895180141c07041d004182020412410101c03c4900440040c001403010310b04000040d5241d0740701818812030118103600d50400b1803018000751a400e10591441c120400310b625030441741e038917039003ca41540300341040c0501c521503080442c1c911081d00030050410712560b41c601a41a48403030805207406940c40c40900541c0503c202080050390225540c002c007540340c030070900d1b0980306c8a010003503100303070751100148070041035034444400d15001745808509241800041001e20118802540f41043c00254419069804002d041c4a100410100c0c40c6146010703207855105101d03d0031020104424417015807400c05405452094078041c0440800a4014a0110907444e50044000d070340a801003407134001451500701e441e10310a542e164081c0d460014450502002440703206800b580c419802e21015002d078071250145e884841c80b446244100c40c07400c50070094403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 266112194 1250 266110944 266110963
    0x3030e1915081504061a07020105040906170d02060f0112051501090204050f0a051f170108060f0703090201090905100909050a052506080403050702040f06090606050901020309090601110601090905 86
    0x242d400c005e000c1000080841d030181c1c1305111104016201c84c424801201d0360302c83d070703400314000c01c1c100000405c00310f0407d001000700301440000c5034a41c14000c030040e81c4441c411141c24260440440042000110a10180c00b07201e200300f041e241d404845400303070441039600b80c00085031664045024440c6007400710b030b48000958216070040e0b8507031800000501500e40710b690a5601d50001d88512140390040340c00500002d0300d60121841d946c2c480d6407140e034601080b11442d20400c0e448022516060103881000030766a0180e48080d242814900c00c03801801024028400050b440d010000c1c0030f244501c2441c0b000d61094000d0500345101c0c1c24518900140c1c040c2c1707200c1142c820034118021403141d5400d04119002c1c0c0c2029040c580e21030809550305e00400070040d4215060455425000030743d0780c40070040d10340030b50b0700700035280d2164411108c500494002902681c01000b03034404a281c2156407d9003c40145080c1511090340c5801c241004030070b07031040d00c1c00d030745800050003040700034451043c0d0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 266113444 1250 266112194 266112199
    0x501050a081b150405130b010e0406061b03020f030403051b0105090d060e0709021612050a091e0801021b0d0503060a030f020d0803070c0b0c030103030e19150815 71
    0x451001c03003102e04070076180740b0364280c0c03280d00b024000304040c842140c1030702d000f03003801802ca221014016220101400c0e262403200c0c00104200000201490984290b6003601d0f6540d995080c00c0c0a01040481c0040802034243c003544220301e02c1c03905051080004001440c0320714051701c0310034052340845999070708030340080741440300500205100b0b032614041610f205801c0000403904104040b195400c149081e04002c40d000e000181041808c2c401c60440e104440c803d181641c0c86034202901201e80d405803466080005241080030810801c00740700b507140801107080d180809980c0d0300c1c101400ca81c041030f40c03c90322141900c4100c1581409000000d0790400b0340c00c01d58918030304000010f2170511140001000c034a407802260302951140b190310740c4425400034003195070b4240254003510030400640c0c01c80f403030300400703001800c100461015039041b2641502c038680b0400d1400d04000001c4210410106803200d1080c00085d4008502c0c0c8190f10b20703049403540e045608103c951550410f4003804210b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 266114694 1250 266113444 266113453
    0x1803110c040c02160819150b030d031b031e200a09060f03020406050f07030219150b03010e0604060504080f0d0516030b0102100b0f09090303011401020613170417010501050a08 77
    0x1040880c1014040341c00340d07c08800700111004c0140e81005080b60507450350544556802070650341c2e007550100e500280c50241d480804580050100c1c182d0b41006011003100301011940c132140b42154000d1520799940100920f0a11140000f201d0581c21480d01100000d4a00c0c804000c40ca0b0003440c0c41200046501d0107500d00750800d0400b5065120f0a00d11401e900e4001419106062003484400d13560703102240c406000c0314140c01c022641246c503e404c40c020f41d142c003521141c681b5051007031801c840040c2001e0311030b550341c5884c0d1100070305006100303031030f400420850001082a440001c0c003018800400010752810302c140e08008125200140800741031905140b48021b80c0c0005220403039503c0000046103e02c10f0901080d4030080a003101c8d80c210301440240181c4040200281d81a07840d5408828400800e00c0012a5035210a03a0401d04d41c007500b605904c0401d241c40700c110f551194095400d46481e40d00c2c544440100040c446403a03590750340344014403051404104030780060040c00003c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 266115944 1250 266114694 266114713
    0x7051902090f1003120908010c02010c080105030a0f0602070c05120615011b110a0b07030306030519020d08030c07081801020c0a15030518120711041803110c040c021608 74
    0x40b1244a0702c4c0c0000341c80c044442c664401500d02c03841d004400303007201d81d00070b01118600300000390180c103000d1030120204070044004505818001451424a034100000120603009502e494000303512031503090340c02070341e40c441c0818940c0300e8560701c40c01719400718020150761504400c45da00d1000b080454904108a07098985003800703482c124200038540000c0400c0001100c0300015541c4060b66015800030380000c0380020615070550701960840c0e010340140c0301c1c24004040c00d2a21041e01100013980301c000d00c0340081c08201c00501840e8403401c40441203141c4030098481805035000158242142c4000501d08500b80d42d0604c44001000000e903040900e20303042010654800300c0001402041590b6080001d68102c54103e200720540c081e8010380c0d8540307807006242c0301c1c00e1340400300030340d0141116802c21005041c58800d01410220110f000510505203640071946c003045d0307160f07111161203009502009544d0303a118144203407030302e0307001055900c91005001985519aa003e082030f40c001c0c10301c0313 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 266117194 1250 266115944 266115961
    0xc1c0801080610031208090c280806092a210d08090d1b150b091305070306110c1c122037031b022107051902090f 50
    0x20702645c11068180b8062a5903200205031a1010551711036034010700304c030700900d04405025000384a880031250302c480b041d40c4900c03010360741d282e050700d044010382c2c0300d4050380c0d444425040003132994040c0d070720081045a00c003000080c4100040c80b110200720301706a00c2c0e00442c20003004100108941da0915172002e00d840004180c8410b1500244002d01c81c500980301030007803070b054003600025030000802c1c16905010700090000c207841d2104a010b0800400800c111620890781e241b80030742c1c00001040c40d5800c568400002c0d1080103a58130270018140f0407000244000d203c4100ca44144141c1c2d010300c40180c110060a14031a00340a1460500d04001804a00a08224586003c1d2a211241d43d203204c0c18514850049502c0d00450008402e01480e240202000c90010704c44a401d641c24080c1c00001d00c040740442d00007810301c10259000c8982e1107042103a01441c01c01c0d11154207281428047d85440703803401c1400d0208001d007a21078000c806011403a0050005406c00c2041042c5209460f01d4100e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 266118444 1250 266117194 266117213
    0x140a0b090a0507050f0c0312010609030b04230d080703050601090f05090601050c150106091d06120705060f0d0f06060518060d0603210e060d020c1c080108061003 71
    0x42008141e0701da00000340442c0c000c0c3e046450080003002006c2d030712421002200d0f165040039800d80e038400415030000a140c2c0c400c80c21102501d07000000008903031155602e21045103d0741c09100842d41d525680170803118001c0c05441540c4400c4d482c1c54126140c0074800504455004000c20f0510105060078072004250f44024020b07514290f412010980780d004c0162168011031810440d984640c0340102402503c20820070304035259515260882601d608200c1c0c0440030260301c1d415032101442c0061200d00e46285440020480f46045c0d038045610341001c514180e20001d4140400c10001540602190051007400401810040c08004590810200402c580f06004019600c3e105c2409400207a545100444841c4038043c41d0402c5803540c0c80c60241c1c1c0201500f030b55010b800400744a50641d2502600000309111030041a452410304604400d200a402206d00d015091060600402003000818001d4039a68070f586c864034442c0d07140101151170408020040d03030b80c42c07a0f00001040020040c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 266119694 1250 266118444 266118451
    0x7080703060f0b0604030507090b030312060405060a1a091c1205180301090c0e06120601060c15050703050402120304030224070501060b130e060f0603100f0603140a0b09 74
    0x8801080608491400301c003d001403800c1a83d2140000030000300f000b0001500c082240ca6504003400092290800c054403409680f04035140c0c1c1205034001882460b0030f501c8645d01110040c001403460303071248208080050341c410103100003c400100200e06107062429600d035040b92100720190650f455661414040d1480004000d000c0045600c1800408110140c00c3e00740300038008110059035820481100b001a11030f4540001d00c0c680400ca150403c00c2401661410040041c21070343d180076030031a0b041c018200c1c10380b00408a4000054050007600605000b00c001d0b58011419042a00411800480710b8214120031b901c100010030041e01d605080c00d1000e0040c0344001540000c20351648401c0c45640e030300031305070f52800f01d000c03541440302d00181030a40e101122803503009482c3e03040b030003130304e00247e9000340c1c00178000c402d040e124900300b001103503c21503042c407410b80c5039600d80c48a211480e458001e80c0c0800d03207a100c0103440c100300005c01640842e08e01418080564070a021072421400074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 266120944 1250 266119694 266119703
    0xa090e101401021219090b0921010906020c060105030606090405150c040b0703091415030a09030201020c0f0609010c1d010c050c0a030c170c03030a1d12150907080703 73
    0x700d011403541c0c000e000b659084203034000d25a50781d41c0ca002c81c241054280c4503860001c14a41c5202003840e551100a441035854050801000100d070381006d240040880c0d03a1481c1c0640d00ca40c0301c800007619500142070382c442c1d602c000b0101541000b042605040f0700910745402130b00010300f004046600010000c0002841c4101d0091507180c0f080700521078401c64010040c1340c42c0010b00a8101903021380c40e44119034085090101110001c0c0420140004280400410220510200380c840415501903007180c1d201c5d000051030f10b94500c208a04005500c100089241c1004080117030010302070240e0003403030200380340203080e02e010f1548440c49280d980d940f9504000c611100c1e201040f00800c8014407410b0002c0c0a00703440c42d56498050048e884600605c1c1000840302041c0d290103000007822070b20040000c01443c24110300100460719000002008200010710f0802c071841c03602c4442c0009800c10f0b00d03001a216070400d82391071038402c0d038010740000320503032281c0d4040258060218030141500c2d4071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 266122194 1250 266120944 266120969
    0x230c0403061a06040303020313050f0d060b130606081e06090f040c0b030c09030f0106030803040f06140403030b120604080a1d041a13060e0402100507050a06020a090e10 74
    0x30500b80100311021414240e0410740000340401890380000c0913200301d50310140360220440d103481c2445100c59001e09500d400210f515006030000b46250015400404040c114080c030460312184d96007901c1155001c080803c61940501c6200107042c0c15007a5022040c0f0340000c21420610081040c050004003a40c102c40307000004a01041909803140380100b0105c20b05544a0070840c24800d065401410401e00c01e10444181005155060081e0b2080301d810059642c00e5030f503a0744465010f0406403034100e441650341d580751580700ca070b00002180914000c0e80e0010b0342c0483c03036080c401441400607925481d41e00000412000444100c202c034034030865450490040c2011500c45c040341082c1d07a0b526079016080c01800c0e00401401007080014410407a6212010003000d031131003080759028028981702c4183d403c000340140c2044400c04424031424501186040ca076516980d0410800d514120340301d40e000600790f54840e510211040160018054040c0c0500b00354010602e4002c1d80c1c49403400b541f0a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 266123444 1250 266122194 266122211
    0x71b020603180709050105010f0207030b0115020a060219030506061c0c03060504090b04020306010b04060e0d08041e08061501021b030c09010906030303110406020a020909030d0e01230c040306 84
    0x84071010582c20306048441d42038440074031401a205c2400390300d001460901012000702c0c8001140030850f5005000c040d0b959003070006240d5804043c1d1001c000b54402e27900804c002840601c000c0c00d409404200a03a01d20088010040940e18042d0200344903003800d0005a00c0019542d2054031034040103200022108130020098000e80310701d83c0001c3d4014600a030141c00c2c02469801148150b100f1030035240c2d02d80e00c41079081c0c080d028070300a180000b5078011074011941452850780c50000d02800c400e03802d003680c031500c22a5164104880158100c07040c102046041810046c80707420684901d40c1c0381c011541500002d540c2ea105241ca1418800e10400d05603464a01780884286a040a0108412585c55500020107000304d40300450010b0b1a00d540307140952203170419078049d6013407030380981070141c003a03000c05c0000700c000f0b0a4941140010080551105254414000150004800031a14140d8264000d42d455000310400005038092010011424800400c0754162a80700e6000900d108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 266124694 1250 266123444 266123461
    0x406120b1203070803040b07030606080103030f050403120f09080105010b1e04120516060c0f020409050c04150f050306010e160509090f060913080a031a180609071b020603 75
    0x1016041140c045000006400080c000c0d040011440b1798090300a03410035403a002340c02c40450384284111030001d26507070014000071380b00d22442d803072a04142c54154182030f00c9071603080030301607041d400801003002c0b4914035880d6900010350754020304402d40200110340c54142aa01140300b451f00101b040003000c0c08104070800c008040e6005400c3c0390044041403c550b291455440703800c0c1ea5041442c106010780054406c0c4600c403100c060680c4441410790250351542804003508003000210f441380950284000107484510030040581c00031f4030109111483c00b010420344500c030742c111a009401c1200144502c90026042a400450503403580070441c40180b4100e415024003c0050b034440060b809100b148103009040c140224003c4810000684801e042c245444821440050031008c0a01080480902980c4101c40d1800c0b00310198031280d059800080c8040c95400150354403e81d48010701c0078500305045059400000c82c2400e01c125014040001c43c40c41e11030200a01c1014000001801344 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 266125944 1250 266124694 266124709
    0x21219090b040603020403030815010f05070f02150316030e0304120203120a030203010905010e1b03060d0203060f07030c020d0c0206090a0e040609030f0c0309090e031e030a110406120b 81
    0x80441d000c2107a01c1d1a00d4100050207940140b0003235000074041000f28241d1200e0506007010306105071505241c1a403c040c040c0d8103030300155029200c0c0d031101c207000c10242c0c45901030200e01d00181c17003140380d60f8941400309480701d044090541040514240c4034041940c0000201d030140d40d03081504401030f610a10000f03103080120300010344c40107401b08045001940580282d0306075404044140000d03a200e0b10007100c0ba210032980b0300e42500c6c2e440e00c444010010070005540140e8003610107090244203030003103403400c0d40c103a0b00e40303c0b40c0100308100440f1691521a880e114040b520103080c41c0d600d80300300203007469040100030348503880001b84850907984444050000700000c3c0191039031450181420710081440b1103060f0702190000381c105003003070710584540c03070501d40c541c1342d0807041402d003000030004181400c0c08072082d00c010040c8140c9a2100c441070845035070b0a000c066034910f8641c0456054603a0810710700254042030000703000060300b00b09000765031000d9100020b00c07042c9940016060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 266127194 1250 266125944 266125949
    0xa05040b1e0408070c03150c090501030c020c01030e011d0309030606010c03140c0312160806090606070b10030204150801060b070f141608010b01140301080d08150901060c1202121909 80
    0x20b00382c02d03021000707951445802c008c000c40034070348805244a584000540c25500e10b000c10600580003511804003640c000c0c1e0005001e61911390001070710200c44514144400e03030102034450030350310209040085207810410503501a03800c0c0391a148801c255503002d8082032010070005002040466030044100d010400d45105111100c0f03180628282548004012041c0a00c40c900140401d0300060003401d00300304003402254080c1c1940d141400c3c40d1601e000205002e401c0c0c1e0325541e0b0b01c120000c00b5903120f00850044078051a540c800c414a403d27001c5007142c0c41503000c000315203070a1002c1004101d480807180e51454005215070340d91000003101c0c509040d0301c1c075140034032500702000100c0c000e50150f015403a042030a803510419243e2442400f41c0301e0009100d00f95280d4455080700500c10721400f41c09421141e190000346e00225203078000364000209802110009052000d55401c2c4004001c900c814000e050003c1e00d041011042610954421449240c59107000c0480303203c1154415000d5800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 266128444 1250 266127194 266127203
    0x5160312061202190513020d1112011806150e0d05070e1602060105060d110d1b1d03100c05040503030301090c0f05130e04020f06030a05040b1e0408070c03 68
    0x1652503564000203600000c600364041d0786040e10800c00801c1c0c0854400950703170010000c03043c01084012400181d44001d000b01c464a49070082422000c0700180501002e4800104140b41c540c1003e142404421800c41d52a403001c1c1043d10803c0b10380c056040003013541c2c44c545406410a0f03000e0010895040d07103000e00502c10301c21003100250a9640291207070141c0041291017144140c2804200c0c2d440201b80a50740d800081000031a00d615859400400040e02c2c1c0c1d18600e081c00713a4103502c242240c95020305850440c4880044801c1554808103070625010240145100440b1920100341d88000c01800d03980c80341d6a901525524900640c2070703400402000f000c49a80b980c51b10545000341904c00320501c08650034004070070b41d0a000b5421303210120700b0785110403840361a1040d648a1508054400e0b0780118000f419203840380c4404004600c181e00b00c0d2400300d1141402e00c2c2041d1a448001d01d51401625425401192104401d5403d0380043c0c020080315242c18690400600301c002c0d5910041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 266129694 1250 266128444 266128451
    0x708090d0605090705040606082e08071e03031d0301061e051804080a08060a0302060a170705160b270f0c09100b07111c0c09020a05160312 61
    0x10070075a5001903100d0f281e0310042d81d030401e9541c0c0502040c0c0b20107000300c40101301c000c8002104c042202c1c0d203509003890741ca82d0700107421002411003080154160040700309900721480c14409940c28810740d03080c0203407072558004514070710749000308031380703400740c00a00a8031103c100102c10795425000740d8090b192a100c000841c0605030360b982010681c5203d4240900744c0ae112400d250215120000c1c0f1a80e00205070700d25000c3c20101c200c603818001450140d02c419820004000358a415003d0b205194070f54494040c0c59101d04000300fa800d2005040a0820000f086095002d407450b91540482650140f9807072116141c4004072030301c1c904c1e41c4410003c0c8200c003040e01020000001403d90100d42e5540984800e500300d5801d00020707200071529441c010340040c03010081c3c000381c00700401c0007501401a599690b401c0c6000640782491094400386074103d0068910103100e1040280002000403200440c80e00704c00380c0c2e004d00a406115403030300101c0746026410b01450700820030410780704144401003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 266130944 1250 266129694 266129719
    0x909070302090f1c1104050c0304080313050703080408150702101e02030901021b030c06040201080402010c02040e1b0a14010305070c08120114030a0c05090601020f12070311060103030804030302070809 88
    0x6900780b004e490300690f030342c1c081e403140c044150401d4420310307006007455511185503507601c0d10f40c0c981c9070384081c04405010380300c0c800240c081003042c4001000745100c1c1040907500c500c0c000e00c1d18501101d1030010070800d0303148424800c81d681c00240071a4840d00500002c6140d20b034410324035441044d099042ea0b0b0782400001044400d01c0194010041c011151028014034100c1000c081e17540c0c0030381c0700388821540c810404034000d50700032a42d41d903009105240c000c1e007003d45540410156856001d1080041e0301001d040540d1000e003800d400d941c6103040d078406080b14078010261005800c000b0312103047c1546c641c00700d0354031403280c070b602450250022012541d030400700555002c01d031000d12403421483e14060803104140782c041200382d40d86070083c003050f0a16017090108600585c010704030605510524000f4102c0030814064010601c480a07850b42d2104054200a01540440b00b8658503d81140e40148006504106076941164142c600145c4442142c60000031501c100c2d83c119a200801d440c90 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 266132194 1250 266130944 266130979
    0x12150a020c120d0c050301030c05060f04030602550207170303010603060b0711280e09070603090c150903200109140d030c0c050409050706080c0909070302090f 70
    0x3800100c14900e020130190f04c00c03c4003150315000a010051007910495410065480c258000d401d48241049109240c96981d0f40d410b01280d100300c1e001705c000651904008580785013000c0c1525502c0c084030200018205c445141c101c00240c0b01c00582c0c18811501868410520030885500503010100003800c00b5954802c4c5507a494200744035590009040400105082c200c41c4151404c86500c00350301d050488008003003040c100e11040703515140c0111200400b004072400c95003d40141506101007102307040c0071407090b040000542010042c54141621400041d401c414034800b00c1e1101140703004001100b0034100d07600200c03584054029004404840ca0203200c0c1180068188800d890790b050311a0359a0305640d10298292800c0d0380f0103048a40c00000c40c0c003540010301c0c1c003403040903040282515400040c1c100c7e5030214054030540e11004e424459150040c07038160300041c0000100342810808400240b851b031008081804042e0049503030802030b118141d00c0401054000d06692411340513001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 266133444 1250 266132194 266132197
    0x7111002030c0c030309060405091f0f06140f0703110709290a0b04121e0b1b27030f060c250c030803040213060303020c0103050612150a020c12 63
    0x300b0a650301900780c0c14440e51030b001084813682ea4014052504042c0752004010801000070500025101c00304003032034280c0030820f0010050325051306003030b25650400c28001c00414032190104140c600801c0000c00f003607440070943d001c0307076458a000d00d400300d008090715007007d9031903018035a040d0a0500c00d03c007001360580104076051812140703040101c040401c01804403854810309680190400c401c1c003840103c100b900800c80c0c0254036030711800c070401c0c40169280c50782403000d54003c0418020701c04111030b681d170103200d01c9003400350890410049584141c4d0740718440b18184940451240c02c0d0030f00d81c0301441000321904250007600c20038a803080c2a842e6035440640b80980f115400f01010a1000400c00f441034020340200c0c13400e140c2415075454181c27030381c405842a40d100c01086441e00752100940951320140d403282c2d01800080440348005800e9a0010f00307683c2c410140d080542c0302e89000060140c0600b45002c680301c0d1070340caa20100303500a01c40c11845040e94000d004c511002c007640e150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 266134694 1250 266133444 266133457
    0x60d0b040f11060306090106030510030f0507090b0118060f0e0d0c030213020703140c01060f0305150f04050606100509030f03130905070f03020a03020d0c030509010b03010c050901050711100203 85
    0x2c01d580461190100025440300b26403050340042c02c480107000e107910a50145e94014400b050302c106081e141d8803405170f07403c001b09040300d40358480c40050200707490901449010f64001c1c04c2c40641d0010450a42045421900a44007003180b11020004aa03110322404d040350310f0090030512200c032003420515130407101800240e00a40b021041f988640040703100b00d5102a4055440b021010802100089250b1080740640c40039074943e50007142113034640c2d5040006512940007440c4241d000307103c0b2681103d000f085807400c3d1540ca810040860004214140e001078101c03046c2900c50704021040c2e5041c01940340042c0c162065140680c03a920000005000f000803505440c1c461315640c910314010b0310012650000000c218003400801c1c24000d4000c2e00f0307042954103001d400e120000c0c00d803804031004802000c00190321801407004000c800c1c0300d00189010b0a070000e020403140340038041c15600c50000d03080d0400000003035003820310071141c0d1010701c407000081c102002d00c0440f88000799a0b80189 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 266135944 1250 266134694 266134703
    0x509010c0f050d110405031614040b010905060a03060b0c070806091c1206030519200922020405010b19030903020c0405040501020d050c19140d05060d0b040f 69
    0x808003184041c0500c90406015038a50381d158a0081c80594400c041e040c2040c840c0c00c902418000414142d81c01e024035a408140500c101c0d4140d40342c40b840300f6126540c40802e6001743d1401c410101c407a43d0000e41e4100f42c81d000c2d02d015aa0707110000045000300115400b03030700d82200c01700d00e000000c0008140102124000320450309640c5510715641d85407051109101145c10402c8801c01c040390103000080c2440408401c001200da550f81c940c1c0f41000c41c5200c01d0211020a0b041d44030402c00800640180300e15001c7c01130308a0b4450070301150302618081c203c01e80c1c07050300c04010a495400c0e0080000102e0f80503206100c0c65071744040860f030710b070040a508400c180351705c02d10034500c0b84a0f129403820250154000d08040c4410820701004141c0070300169a295001c100301442030605004281c0100c842c003010035680c50400c0114910103039120041c00030022610041c1e00968080d40980d40303400b4901e9000510341c1c80d10b00004045103424171008280c1043c80c4108800c1c41452880e200341c09024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 266137194 1250 266135944 266135951
    0x30a1202010c021e210d0c0c120f120510090f020304060615050406050901090914012405180103230402090601030903051801031805012403021503060109050402030a050901 75
    0x810b102a1a11110044d0751042903100404283c00280c030b0b10002c0001c02c4240c1032140c035040c480c00c08030042d01c820f6102c00d00800c443e031526000700b00e1541c0c5041c15174a4140307000b1800c61403000d00142028006c0b600c502102c0d0b103e40c04075a0741c0c1104400c40340144800001040b14500c2c0700c481a020350001c58003550024a00b1000064603035078054070f4030904000d991041d00d070a05021003550560440c2c0c62450410100081c0840e0b00b9003148180b4000700700e0242c020b500d0f50724104101c00172202d10811204290311200c0c00c10b034115001000e03200c51041c01e42d0a014211458001200107040c1b02c40510f04009038000b0100c101c040d45d010003030180e40203482d4541079a60700700054003607074404200240000c100f0018140384400c061400d940581c0145404102c0c00065a80695030b0351401000346c0701655228504001a080515000d08070f00c40d1072a2034100030b1035500007031341401d5002c2c02083c2071311002000406680c481d140003000780c08010030440d204c1c10541483c5005000c111b03902e188a42c40e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 266138444 1250 266137194 266137213
    0x10091e060b040e070b0316051c09060b040204050a0e04172b180f0501060302030d03020d0509010c0507080c0102040b0d020d1521110301050711150601120b030a1202010c02 75
    0x1004c1180001d8a100b03035001440c40c1c4806846200302110b000355142004024011070070704410701403064154480410300420445401e0500780100e8140e02900d070b1040c1d1041108110540f2204c0e4040c1c1250702c01200300c0300507695030070300001203c0a4280d124400c40f00103485411003c0340303203800c0c0c107003111603c0d00e1074800400c06e411821101030781441501800c0d10342e00300c400504003040d032400d03843c4035a0010401d01c2c0d40e5408079180400074520312010030303004110024020707000e10607507070f014500f500288a0942d940304050018030034031070042c200300400210301c0c009000035011180103020040ca0140d8544402420100940010b0b01e1186001d0070060105c04003d1f0458468054486031441d141070465039078020350344802650f1085030740341138403240e910b400d0b502840f0b8188501c1d40c50705c640d1494258404290708081c148540c02c0035000f501003d118003070745d205603a460508030000000500200d40d4000a140800000c0c000300040b5101c0790109440d541074021818101d4140c00701c1c0c0f01c1d1103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 266139694 1250 266138444 266138471
    0xc01022101090603210e0405040605060f0301050f1308040e01030c050a06050a020d180f0e0a0b0a0602030307030507030902030a0f030807030b01140a1809091e0510091e060b04 77
    0x1900340c0710140060481e000b00c0340341c9402001c03a4014601740c0b401c0c807004000402020509030343c0121400e4650b26170310310403c012802e00c1108804104000c800802181c80c20703040741c071f15860001c0c02803440e0101140404040140c11012074024000d900e114440c1580d50b4508900103c0103402001e00a04c10050700240d0321b40160705403000108a40c0207400354003c06441200c0a040c55800039201c141000b4000038141c42040d4483c020b828400100091850800008015181c003006801e000e091460b01c02c0181590200549030400e58074030300803a0039160107608901901c50307008081d505001f00118942000321001231520f007648691500240750b564968181e0484802205050118400d004039403c42e998010040c0070280b10303820001e072284031910f1081805101a040211440e5a5201803c24004040b07400c01041c1c0504008022840390307a5250f6803615580003000488589800c006800c002c0507810004040c40741c40c04842202c2413a042c4000548503101545000c0d6141c61251440d08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 266140944 1250 266139694 266139701
    0x60403140403020d02090a15080a050c0303040e0435070b07030501181e020c0318030106051e040e010c03060509060a0501021c050903100504060b04050910110c0102210109 75
    0x1250003d1138110148100d40912092882c018240402d0a076260300c0c0c62190041480604041e00d1400001c0049030410704e030052420100d071401e28483d070b005100400109a0b02078106510561003000004481030821700c00110841c100c41210f0b0707855414142c00031000d823403005011001c0c00b4988040c165103031558150300722a001e010300100c003086104100c0d45400030390003000003883e0401e00241c50411040b10309040b42c02c000102d84064200040c03102000c1480607000800440440080000628050015150360039602d54901d07620b00a2101d030145aa83ea880700300a0100c4500910071030071800e900034002c1c4014007850f8442c00c807400c0401e056040c1205104c054a02c1a0010700400307081c04849021002c2001448080041c20480036496850a0121a2018840d548089200c1c00d01d031a221081d40c54540c2841e0055242c1020031400490000f5030824040c02e500002507580728030490403026100b90004c88a241d0b000107004444908240c1040890301c114000700042640c0b5a509082603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 266142194 1250 266140944 266140949
    0x2040c08070e0901140d050703020312070b070305090c0d0312051801060905130803041b08160915170a0f08070c0e1e190c1101050705041d04061104080604031404 71
    0x6412a0f84d0704800c6c03e2001d0700480c6c50b4010030450303110581c0d0f030780042e18010030030b96128a071807008900c030010171882c981204e400080c0c0d41410300885c500142d4866403194034815003481504020010814180030395120540c10455107405e101600d0000988840d81d460840c041d51300350300e4011b0000b441141842014040d590741d4646880f084456107078500503410150040d100302c0d460200c0400c88107001c1c058a8000d010b1400502080c0400f00b2511030b8000c2103034000da00032810b0264105002c0c0020b8240000d070f80b00c004031030780171a8500340f4036443c1c04290305008040240b201620000d0000410191026a100d90b505905440d1141d00307041c4290010780d0300404184904410382450034190b24110b9022401801049003a140745583c0021ba40d070016082000c61500e18040c81000000c0c0100c03a0b00481c2410140c0c98145044550b80c40c0415240c144e00b0740c42802000302e001c0051640150388401350030480c1e284c40d562501da120b91180c0f002c0e501280840c01001e000f054901c010001e0340c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 266143444 1250 266142194 266142209
    0x31d01150b0c060406150e011401031407020a020108040c090e28031209060b150d0b061e0c010f0905060106020c04060b0927010f0303090f08030a1b02040c08070e0901 73
    0x3a81303503541c2c0e00c0040c09103c04001c490340320f100000706000c00401000b5000300854109104010344000014086034541a00f11900c81103004c10800e03619000502d00d185035070b080c60080980e503100d00700f491400c0c805400200141307007450440c09a2680028a45801d019004806640100e40000742c800c22000100010301140607000b0b03010b540c035070940c8000150b501820000ca040688400003e4103104e008549411400000c640450a0071203841660b44e009015611076141030380002c13a00311581c42100100c0800c02d40020102c0d6444000c0d00000449035811009000405161400648458003409021b0040c0f01d40308983d00039140900505040790070342495540f60041010900221226032011038101c005034070341701640380403124070040c000c1620403a2030440e2070851800404810342070b402244001904d450903c102000401107941145042c03d00088200e041142c0004000301c070b04010b580580340400c44080c440d00000311510816890742c403071a00710f4414082210a64081c0603100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 266144694 1250 266143444 266143453
    0x7090b07210e011707021c14070b0415050106050d0902120f0304080d08070512090316060b041a130e0a080a050d0608010e0703080306060408030c0705030c121b01031d01150b0c 77
    0x40107003900381f201610f5010340c90015001c00081d00341c1c0b0072070360010300c08460307040d1500c08200074003071407011125a202500106000b9540741c104010b24501032361211b900c0c8143e44440b004110b50744e078101030920b0340d941c00550345111a04540c00391641c02a128080650007070a000402107480751809034441c0030f6540b80ca40c14080d10f1014804d00c5a0001e20b10390541c8020410410326130210001039807010312540000c074070031801d4810702c0187c0781d10021114a03101201c610800f141d0f241d200b40b000c4502c00c0c800015030001203030407551400c140700c00068404400010504c0c0c40350703030010040c5001da0312003000b8412103585640c0c040c02c850601801d0303581d0350404801400007805400c010b5400c924000c00300b078201501c0da20507900303550203044d00c8803155008107410021410144405c0b001d082c0d00725050068502201015916a82e4010800158550055150001d68043d03800241e900d250305842240c0700d072011044500804043c002850220300e4202d0001e008110f140869281109210250 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 266145944 1250 266144694 266144713
    0x30e0f0607140909180d02070509060d020f0907020d030b01110607110f030d020415050c030d020a03110c010507020f120412060902030a080304140607090b07210e01170702 75
    0x4881409041491440882c0c0c100f01605059542035450703030060441c0c0c0c111a48000148400f2440e05070008410000d641003800c040009556030884140d221a0980e60308000c41c019100007a20702c5002c1800903031020301c07081400404c83d0300058440305540140c8003045224044801980e0340100c04503507a8255104600107590395105800501d1015200720849501499107440381c0d04503080120804c01c810381c00f040402040440c0c03030290300442c0803824003a203050081d031003a584138840e402c3c0741d180031900000d034103109920a034480c00501d904080866121040c07c00002d0292009a50340401889140c281403038031000801d00100d22506900c08a15003464094050b5880221401c00d0324150768506004025843c10711551022502c0ba24406aa038074041c6064003e0240d1400c003d45551b12003010030030031940101005041e6810140040d8507001246461400344e0003e108441d03030390010703240d400b45288d08820350070b58801090b2600000346e8410005291004004c82d00e103070040e400411316 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 266147194 1250 266145944 266145947
    0x305042f0303030a02070c0f03020609061602040501091415090105010c111002010b010f09050105070b0c070615051e18180d08061203070302120d02090d060b01030e0f0607 75
    0x20345850240c11611a012200e4034000074119041103c09414454000800740304100d03d030025100504903180000c4510760854020030f143d4003640540328001c0400090300354a05141c05d80100104d940208240041d40c0c44007a80c0014044206d00d505a0212600c0800c90120040740040500072015258003050380c03070480115801e00500d10251071100d6224500300c411b4840e04004409110a900003203800c20549000500440c0f0400010b020800c0c89172040c80103a03400f104540483e9040b40f01c462040d1599422100c003031040110050106103400420855141140750602c00c807002202d102c59111141e590300f01485084c00722113a8001c0a0072561040344580c02070030354003c0303d00420f21622042101031940f414444040d07100c04185104200091450300d0340415640c46c101d10007860034040345907006036403003000d81001c0703001c1c2c40d0104110b03c1090f0141d059a50748100180301d44503410340e40c18030000034000c0546c42400603090a1004c481711100144c04203030041a900100007a136185c3c5070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 266148444 1250 266147194 266147243
    0x13060302090d170f07110109050108040b0a020306011b0c0801180b01090507140a030b0306060132090a030b0103020415052d1017011403031c020c01050408030f07030504 74
    0xd000e030024814014003450b5104d11018109641c4201c11903904038408800240000304e0561000b410080a0010000010141020713150420040c00d000b41e1030352600401650b41c81c8003400104030300c0910752030800900207105003010171110b01800820088607002c043d200750861101002c0d120185000041201028070361005501c8507003403034101d0440801c2e150f40882d95014601440c0042e03114402e10149103401c2c0300c1180c1090b03090030015186e91202400e04056400c4500512a9000380001c1d41e892849107000c46039800700003840c0c51000f80e220319041c0c032070107030a000a0380220b1030041e841100c80d080b08134100c1964070090009c07110140e0f045090202c40c0f07040e0105560350700398454803081520341e8641c0308561001078030780e20080d8070b403854041000e42c0140d01281134031032111099805e9072804002c0b100a08810b2100b01452261520300c0e5010b48201c02d95040b056103401d0410007032001c1440514003a80b5800e140e2009500d88200481c242e41702a2805003100540b61808c40b0102500074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 266149694 1250 266148444 266148473
    0x2101050f0312090f090c04031515050d0f08030109150803040303210216030e0f01030b24040b040602010606090f1a030a140103050f0705040e060f1801020f13060302090d 74
    0x91203544c01c004043e0114189950a682000701d402e000701c0d0910802404c83c07000703815031b1a1034000b00810550003a50650304006031203040c6c003900f1004644d2082c03020a0300b410b10f10340d070010010f030307a607580d981c1e40302c030003008030b40340e0620001060320005c100c0c0c3c5000710803101201d400d552944c9000c0403d0040c040300402c002c0510301c00076401c0181b84210007103102c0d0b0440d90341c040d4691013150320000301442aa501c0c8441000d040504d0303d0400c161950302e4a0200c4002d183c40400b1034140d400054010329030740704640008a882e000841c0000b0030b6a4150480c9080d6419660352501441c2e071064002407114036800f40f02840c91062214180b05540c04014541c0099440700109001d13403100240001e00b100bc0e081175070761b038100c84a4000300050822601c4010441500c0400010010807802a00c0350780180107107240b8001107011900c008552481980030543c804000c40d40c03000c25000c43c000b2a0b1006500403120b26940a0025450340203100b50340301c542000c1c292500c411101d9585060070b11862 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 266150944 1250 266149694 266149699
    0xe0a02032d07060309110f0d0602030612100e0c060a08010e041a1e180316020301150b070c14060d150b13051e100518062101050f031209 60
    0x244400001420401a02c8000d1003a41c400103200c0005007001c5901800460081e4045c02000080c8811030311000c4a005107180c020308010380700c2e220440066924058203000c060307103104901c1c00c62542252035015501d144861021207056195400601186001d1034038290b011959400040003105101840158404d00c1121040d100488100c122034441c102520440a028103241e503c4004d42c0b00309400c1c4c1e41108904000e1000d802846400560342d100d54200b090001c0017402080045450941000111442180b1444031140c0c841e207111410b038101030010340321403141600c0091300c004002104020741c1c00c0580f480b85012203074007001024001071200c0e000992074403540024420042c0b03000c1c08441d4811032181c7e8480b490a0108002c5c0291155040013600300103d858910f07a48041c52202c0000060401d11340350180c001d03100c415840891003068000000007550150084410301c02842110304071f0b800707520350340c9610a100807030801000140c0c041d031011003100c4034500d039640a01101e9400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 266152194 1250 266150944 266151013
    0x813030c060c031a0a12030309110301050112050105060609011407020310020310030c0b190c051c0f031b121a10020102070203121e0c01090b09060a0e0a0203 69
    0x9540ea648112a2403141c0503000035910841d07118611000c5208000c44803048417881c0c04181070a0304480c003510038500c010141562228080100300442003841c100d9440100204010340c0e407540c0d18070303c0302c144140403a002d501c0c02c00060310030710b48407003600c22982040e5030b40140e4600c0b085481c03c1030740c405501070343e05220303480c0d40c01d45800340c9000640c400d18680c0d040c3c40d420f03451131a0000f07a41c2243c0c1c010181c4080700344006403030041d0f40c00060084644a11f4a46020882400d01c0c0303040c841e4100401e5075043c2003001c084056900304c02e40c0e01e00c034052941d04204c0c15a81c040822129004654400000723070004500d440588000c1d0420841e00300003c0d81c0f2001d041000d4001038501e80100b0411025075000300c0e60400703502c0c062041c03040c0c1c000c0d01580da41c503000d0582c07104090f6104000451003091000704180d05480425400f98206a5120104107241e0800300829940e81c0e10442e0a0030075141000800780007040c3c003048580b2582d9000d00244100c1c0c00e0306829030044203c0e100c5d030044c1ca07000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 266153444 1250 266152194 266152217
    0x1a0a02010213062f030a0e121b010e040b010e010e13060807061808030910090302030109032f0a0204050403230a09090e0307030305060103020f130504050a0903081303 73
    0x1682a404000d1403603884580d51840c01101c45856203900003007400c282000c03a11100f12a1300044202d605102442c500046200301d450300191004d030015070f054140f40314000036081d10b40040f402c40b000341c8609890b2944030701c48100812056900c0c00f49083d000a41d0902805503650050041100500780203013400c40070142c09110200316000c0303620003807141c1c2c03100e0810002e41e60414cd1001c107031001c02c03070070400c1c40342403148017540d170300c94100c210380900009000c0c0c101241c480e0900401443d8000d0090105242c2d60900802420758800303521040049016a11400000d60403070060075054100076000900d5550200001000c0c000d209606102c0d01c0030b0052502000000790301d01c0e080075010380644030f1440000041c1080880e400650400e46080100000024004243d0f14015818a004507161783e44000480181c000d6414402c1250030100342403403e1484140d40e0002d485083d40c04125660b0b07040c00c8002501c821060180110340c3c504046020400e022f02ca41c0700840c001c0c1800880e414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 266154694 1250 266153444 266153467
    0x130609020d060e09010603050d08100e010b07020f040c0c17070b0928030903020d05010e070b0405011205040807150b060d09030816020318010c021906020d0503011a0a020102 76
    0x1d000001c006066030b50b42c0700c18880c503c0c290302c0143d00000040b0007002441d003517644490b0f50310b000c2240c2e0800e00c5622800220399080c04299500a46580501020ba035650707008002c42c07580181f50b04a1013070344540d2642080341080d1180300e030481c2c0c2581c0c0d002240307200c43d100c032030080004203c0400e0900040100002088a2a4090703029502c3d580003010030328026500101468010300c2c80c040c00100f42c0c0203040c04603500c0a004030969404580d00b543c2d4000d50f150403401449034260b0702040d40225440011500070440285c011500280c075408204044d0200d0b48003115021540207040c4003052100c00041f8101044098103c1c1c0082c8002135400104800141c2d00d4015004d8440702ea80c40f1034069040580c0954519085030b9a440380402c001c000c484081d499005d049014507444a030f025440401e81c0c03040d554424040c1e005032a14942003800200c40c21900d40b24002d034005407160480c410905407103441144d0480e0203427007011140411084984032182d0103000b0540442d90240700303603509e00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 266155944 1250 266154694 266154697
    0x31b0f08070c140303040b040c0b09011409060d090b01050102070e16030b011701140f06030412030203060409080309060703061505040b070206070624120c0905100e04060b03010b0f0f13060902 84
    0x114081c180d041c07010300d46440c0c030f00d00c0300303c45410800e1542000d125124bd1640c012190034507002d019040c19880b0740301240810500c1c007408607090700a909285255060040000c4510b050311400e03030039240d820740c03240e81940c04454141d0f600038410100701e040120b814460b90144242c02c405140c00803c0d2107010300035a80340315081e0003960b40042c0c00e124803032852800402d591256130080d0b501504501e02501d84960054450400720189a0004001145690369038003109000f940040e803941c4904000b04010343d2101d0032100000442e01d402008034000700c1340148484800380740d9803440d140504285035013070309810414089810103000e000b20800121540500c5122103a4064601107500c400e111010040580d83c0c4802c1d81020103910000100d20b40882440070b49017202070120340c68440101c100ca1002040e4040060034482c3c030700344070401440360090420080100c000303020002000d0304010402d520011010b50103160700c038122100303003418000b10321422491400054501d0751146000142d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 266157194 1250 266155944 266155951
    0x80f04080303240904080a180b041805060a0521030d020309010b01030b1e22050c030106030c08010501090315091e031b0c030f051c031b0f08070c140303 67
    0x94450350f4040c1210000320301c074400b45a02e0116032400329400d0030340794800103200d4a4000010130030507150104400d20f000446500400901544036602c503500c80c182c040d85103840c00151040f88c10b060110b48945005604d980a80344c0091890360390701c1d0001d81b4a19040350000303080d00360340000d02c81109030b02205d00c05141324030301c860700204500700d580d80010700b1101d91a581610902181641c1c01e044020700c030b8020720b02c02d0140d800b40c088947c2201c0461281403134030196030140381030600b041482420600070310304941450320b0a100100c400b410540300302d0424052540002c4801c5802c00101e2a03040e090044480e440e42c000803c294551034546003090f1390421034001116100d240400c15038066221141d209400c0d6a200590b15503070b88201010710341e440064204c1602d440d111051203c14031034180403410958507c104125034100207000b810000500d011075036520002c464100b4002c1401440303a8006540b0301d0419a0b45d0345068600c0041c00d44c2c00c0d101c0000700e0b10021400b90b01000250b00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 266158444 1250 266157194 266157211
    0x1061b05160e100b04061101020f2d0405182508070905090103020a120503042d0608090a03140906030a020904180f02010804020f09070c02030c010c050a080f04080303 73
    0x1041c1d4201007000d8080c84000d0700400c048520900704004a421990a407002e50321285400241d000d007801c51140a401840810b00100c00002415502c0110424050075400c01941e039101c000c03214440c0d4160580114442c081d0000403100d601480f07810141e0000c1d03072100461403400d1304800e40c980140001c402e03035a55640413413460400e2141c08c68110300441c0060104070b0f0300109035030455002c80c0d09480c42e0711401801102030400a01004018410b40e00500300c00801410400880e130304500c001c10000b01c1148400800b0344011a08911450656204990724030083c94044501e940440c0c3c1605401e400700c3c404002805500342aa88610045010340c2100e000541c446100d00100f01c121100101a0008400c122000100003611900d18400840d02400c002486540310f0011800d604003028800e07a02c030345003c080060f80d581195015844500940841d19040c034000d00541e44148031b01409485039010682c110300003a480d000419034483c0140e00c55003041d56444081d481c44e002542c9255 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 266159694 1250 266158444 266158483
    0x30f060b0d140f063d0506070303060510030212040b04030e040f06081203010302030727060b0c0c0a08100f020702030d0f02060609040b1911190905040903050301061b05 74
    0x81030721500700b2019800c0204a0402c03541c5d100160205550358550455203d80501c00c04907603000140601071140042030050b25055607014941b40060060100340100351081201c0c45403080720b2031291080d0b03034101401407404042600d890f00c2d158000540144114108040080c118100d038840d4043c4c1c00c03610400da6000b0800c64100b28001c1d0900c103030354007040440201440100096030f00000c01004a81c0800000f120507048203403041c500700c2c0c500020300002c9003802c4002406000c0b80d0018018259524165881180424100100700e10944192001a840307140d4a8884192940c400c400c00fa5070084010700d44550740d03000c0b90400310f00340d489a001c649401051100d4580501402c0e0340808100c0300c3c5092450b1036070307404e018100040c03e854038100000f080842d00c2443d0368408100c0001e985000b584581c1d15041800a05640e41d82207400a40d40c0b00b0001134500341402100c045e55810f0300c0d820b040d40c1c02c0800454410480461100100c0911003d01c00442c00c24494076104804801140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 266160944 1250 266159694 266159713
    0xc14040308220b12180a0f06090206030403050403050d0e060415020c09040f0302070b071a130c1e081b040c050409020d02030a0e151b04081203040615030f060b0d14 72
    0x5200c1c01e8014240178412100844261004402181e80070641c2d83c400f92100e8001040d0501d00010143c40d200213420900c00810b20050580100140033140e01c40c03400c55030071170b114400480303449003541100b41d0058401c1c001406101c01c4900c441c022455140f0456042200d0540062a0280152400d44000800361b10806c140340d4148560805402e2048829150900e15504c0c00409d0b2044640304c100d880e089008200b041e40f10001d44ca115503003040001140c141c6550444000c28020b00c13480000d10041ca00006117124007203031a50880c4070300f0319230103c4031a01c0b600b807001800c40e07d400042004020440402c0c81e108a101800c0401d02c6884010384078600340c0f11150880d440380c0301ca500d40e6805548a00000900c0101c40c81c1d110100c0024070040c0b01030030354001054041d0b80c21420301405013012540b03103411f2040140d403060303009050500c0341c40c0c0c54000000498809000140610b0450280c91011440640081b0040540584981d080300041c0e00c0b200303216031011a1084150b0001d5840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 266162194 1250 266160944 266160967
    0x4060e01021c0204060f0507080f0315090702060711070821042d240f02030d14040506072c0a090203071d0609060a1d04050106020607030c14040308220b 67
    0x7006c0101c605410500d25216158803410b8030b40c01524101041c070100000010700390b08090070200c3c450440500307000000e0900180180d01c8010480700303070000031036180b800000c41500041c410101d030178880181c681c1c5003820740c442e8104101100e070705110200421001891507942c0485403c000003850090528215a40503115510883d80c4178140070481070f0241504601c0d654845900e80d041410a04901e000441c001e84c2103004551a00c00c02c1490510306103288500249218425449842175490755038941c14162411124420084842c03404807690501c1d010b01901c42000411000b8071410300707169150b1000060744d00c100c0d21301c4005820390704100b11540280c0100380c03102000b04c45482c100414400854000d01800b0040000c10440425001d484840748440c6000080b018100340b00c1d641c4c54120203555030806568074800030f4034040104d200700f40306003c4140300921513511289024070703603103070b009164100c940c654044082d50120802c1c1001f001c038090002f0080d650300586c86a62400b107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 266163444 1250 266162194 266162207
    0xa020d0905010e10032409020901020708010c0503040f0309030209041a09150a15210213060f0e0c0d0608011d16030204051b030a0f050108010b0904060e01021c020406 73
    0x11039410701461006500c1c01e60344910a88042d102c040c07170000f40f4403e10320414901d40c031200c0c10688403a600500701190108054005081d00302c802e800325082c1da40d0701c500c100e08a807081c070704000004505002150021340070302450080d5502924000b910740b61240c0004a03010015035040f00c0040c4181c01d803183c4007904502d0140c1c00b84130040984000c011481d074550b012400104024403855643d0100001c2e03c142540140280c14002d2540c1c01c0450765140c060141d04041d4003da10038000305420394030300ca096000320002d0322110894041020300d450505500031a018140e07200001c0148002507000065104820061420b00000b242c51980b0500b60749034141c24800801c2d064110100180400c90071006130f41c22a581034600142599504450383c030740001d000c0c044100c2100c0001800b030f40f40c41e02d810505940e1a01d000810159a032421518200c50301d00451a4000100718009030206010341e1150300d40600f110000344c41c03c02c0351001c0703500c0300b0030222801002541c049400d0101d2903121a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 266164694 1250 266163444 266163449
    0xd0f03060803031b09040e0a0b06240412030c062a030603030e06182d040e06060d0204020d2406050c03031b0403120309050c030319030b030705060a020d09 68
    0xc0614998205184d41c01d00c200800d01d06002030310070028850340a034580c0d91101600031151001d8800d208550320700030102c00002c0d04d06900c901010400c1140c84d814009685400c0d0f0800100e03140742a240c20044030074070001d030505405104807101c101011078003501800810003000c0000320444810540481d00c01030700000c0600c101486c1c0b1405000198010080d0040c4100440c1c0c85070b1500503810301096240d00001c3c459421011200c40c0061071241007119140400c51101c0c940d103915035103024041204c642c2418010306500c164041800c40c00c0240b00b0440c000e0000d00050300c0c1001c01d1a0600580b00c040103036440d408044034100b1181c14107840384d03a0181c40c1501d403151503c2c0c002813481d41d4038000035003101c541c01c65180405081c2e1804400b00d0740150707888040750110825401c4007400070f107100d00099999010716010f03024140745c04000c031402d03008403c81e020b00040b92100d0880050201000003605440740d0100491540e1750701e0040e01c0140c4095005113929410624010b20b5521690f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 266165944 1250 266164694 266164709
    0x318060902030f28020d0203070608072604020103150e0c1206060a0206011a0403170702040b0118060e0301110301081c0c0c03080708090d050f010b060f0301090207140d0f0306 77
    0x1180d502d00d071300019000c5070090300d20000038060349800041c48507017060350300943c0351150700350000d5440d030002101486461346440310385c60403944080c0142c20140c0c0009180d0809051000a401580a84e01507c00c50100c624203031a8070b81c0390760108401900035940f0030000c0c500803420b820b01c000c94403401c40d40620142c0701c040c10030401d000080d696060601508040f400031200d4601540781c52002c0d50000c1d030700000080e0750118400b4001581ea40b1000c0e041c1e000b242414010100c03035000e4041d0043c034240d080440e92880d407400f007040720390281030015150301d5500c40c3d44484100781900e001e140038103032800c09020084403046005000003802009481809403042503440412032824003d402c49421811482c0c2c3c41e4a40e180400491103111507256011600075802004d0140008003001e240c1c5900000700f00d586900c4080001600802414011900040005020b508c8464014102e028496a21401c0c860305000582d41001c800322084400034400710407141515615004040003807903075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 266167194 1250 266165944 266165953
    0x70812090901090e100906090b010803071104050a09170a0e1507030e01030912080f070302090d021306050603041505010b04080a020d0221010f0e2404030318060902030f 74
    0xa40d408190492014401c3d1030340e03641d4a51403000e003048140141d40001d041d020080080708001e02d0320310001e002080056522078034010003ca85024000116103a0541100c003240d0410b01c640108000b0340801000043c0d41c0d0345a0103960001125a04d00c42100c2e000c0201441e2101c491080052003881c88212880c8100082d0004804041d004401c84040a030189403040e1402881e9005801929032910000c03e01800e5000c10f5100c00d034804000e6004803688020511181c895900850990082c2a174a42d1b001d02600200c0005182140501a20f0351070302c00c000c1401c0740c1d00c00000d40c143d00101c41c245c4601020704148060b4440600c20f0758058400c00c20a076041a04100f5034035030780c100b403807002170003400c0c4201281c0a41d40c812602035222050711941a004850103a001800b80130404a84105107023040301e100c00e0004041822a01c10b8142d0040744e06040e49069080c1c51441c01420903801c0c140d480c4c4201005904110303504006a00480000c1025440b6105240c5003a406400040c801d402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 266168444 1250 266167194 266167207
    0x80c01030c09121b0b0316030e070b070c0f0806090c0307030b0606031305010c03020703110c0907200d1d0405010e0612011404290402030a170d0e070812 67
    0x4014602000752030003880f9038880700019203441400460040c120181008101c000050082802c03001507100b030110000c003410b8909a480306405071513850ba41c0300100d40210313505102600004000d00b2106010399020909a65104180d008148054103c500160041410020348074010070000c051103e080d802001a10b01d540c580d03041c01040a4000c81c0720344000004900c00550024215088907000b40c020444844101005070095114100c1140403c10a6030f074061001c00c08610075000b1100901208196581c0392400c03140c036111003d200003124180d08440100c1d0800300000120340300991a18001c0f00c20b040f6a40010044401c184c3d48190704160050040220ac14042d541002041e1148c1558541c210409400740540d0314001102202e200c0030081807225070800607071070301c214100000100034890412140300d41d007103601170340580c010680300c00042d009200490340301c80000c180c0d0b400c107c0c0f0300420805448400c246420190300c000300078461003e051103c0150020741241d01c42c50202d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 266169694 1250 266168444 266168447
    0xa170a0507200c04020d0b100e0a050a0b0a050306010207080d020c04141302010e0d020414040b07020f06222102011508120d020714010c0f0e01020c040e07090207050601080c01030c 79
    0xc802043c20301031500481c00c0c514003081d0780c100401c9080001c0c05440c000004540080040411040041c440d069446001030039041156084c0c040d100344c40c1071a0310303044a442042d030b00c0c0d81c8046d00303090461080400000345103a00380010800406c160703001d4410348401008000c1912201405200f80c810010107010b5020111001000d48560a0818030000c6c440d100005400342c00642029401500340640208801c04501229104a1040e1000300c40c80d1a40345040342d648442170240300d00343e03201070089071030b02084402a0034041c210080c000121001ea0f6101d00300080c08000c0b903c031046c246103030507440a80a00502c2e4843c08002c0d1400c03522850914450b5550350084d1088460b50000039102344d100e00700760100c810303040e0440034441044000d805414000c1100c2c0e40b2a90000c0c0c0fa9030045100e42d072040c0c8106800b200160700800003440c8140c00c100c001e00c14940700c8003c1d0300ca103010008051510f80084d04101d4001c4020780465890704075494280b001c416085c43c10586440d41c00210305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 266170944 1250 266169694 266169703
    0x1505030606010f030e0d022b08040f0c0504020d0507020709051303050d060806090a03090605040b19031d071406070c0312050f040311030c0405090309060a170a050720 73
    0x90000d10300358001c122603c105500500c020150880c0d079008517443c2c02d003400c1c0c0008032450b41c03c01403801d0f8020044ca82c0720769410742445001c940c00180445002c20089400c0003034070001710b40079030540003207150307039100240403603000041c110025a240c03c00c00c002c02e40c0601504009000f502000c1c009481c0100788030100036030781c1c00d008050100c049005201a09542e00441c040c0a03c0011121141070250307910750340720000c007400c400040c141e0f04003003026449901607030b00302c0c0d980300425401d00070582045021406101036810030141c1d504007585036660f48402c04000e41000b40003402590f414040d1017521049a051054024807040002100160003a048901206c0d007004131404000e81c061800c0f5070303034454440c07a00f00c041000b01d801720078405411155081c0c1c0008034100e403035060301c0606010035030750b040342c8440d400d80082c0002c40d1a800d04400030070900d0b4041c80d2244001da40140c101132501025119100e485584070108000150400083c07000030050a4610740c003c02c10400c00c0e5942d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 266172194 1250 266170944 266170951
    0x21201030b010e370930050a020601030303090f020307090b04151d04050a0b1f051903110109090608010e01180506070f170403110706230f04030c030c0302010315050306 74
    0x1003880b209001c4d403000b400c9a112050240d807101d80d0405443c0e8280c0610070368110000300d004d4940c140f000c1c3c1500c082c000c10456445c0c10441c3c000e005c4903071035030310260001d06420342c05a552130f049201140052303405120082c0508000100000c00310782000900c07040314102840410354849a03642440501000c4801c0040111700329446001075030b8500d496030510200344001402d090b0302a051190f05a095003000e6039506008070340640e0941e681080244651425240704580a403540c800c0c40407841c0b5203005084088181008079144d5941c600c140d0840d8803591048559954494601284070000c1c059500c00d0400d40c010f09a60040f2074507055101c1c071010300301d0418003500c0320b80c0d40c05c0b081c058030300f0b03c100e41e01658005000d4900340c10301900044100c4002d003501c2c0102c2802086140c058803d55203061414200100d0b078800e84107c020580d03100b2000545c0c40c11042c480000002c0504203198050742c400d03000d070400240b03988000f506480d00d5116102070a40800820310407900d001810590 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 266173444 1250 266172194 266172271
    0x210020403080927040f110904030c06050a110a030e1c05030a02031306110a030c080108070608090c03010612170f030a020304060f0e010b15210a021201030b010e 71
    0x1004c0c01d4154608106000400c2d04040c0280e07040104401e2020345241c1062150080140100792080f03074007002400c1008440040106000004500118456a2095900009441c03000034240b0b401102d040441d000310070b5034000a40c45070311500d0600000d01c130a0041440e20035625950344241c500281060100500307840401307501000080f03080410107504110a5000b1100300604403c0d0300b1100c1007544580c07840300c042401c1141000820340702c5c24507a030403a003242d0040c00a4600b0f200c0120381c4140701a100030070b0f9210391310b54100255001c1c0b003010010030104a100e003d00c031082c6010703600704068039040340360a60188880d82c08491040202c0e41d00c4400c1000050340ea40d00da00d4484010036440110100b01450024042e25443c4154043c025441044030306124601e080d41c19103119102d440709407646450021158480c80041c0070b9515009400180c0c05401d19481d003401800c0440c09a200b614803403201d0004205142480072480c1c0c00c0140c090300c00c4844150102000d8500c2954940550b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 266174694 1250 266173444 266173459
    0xc120203120301260a0b0c072f0607021809070303090e07020c040506220203071b150c0c050303091c030b0a03120903140609010c08161412070c0302100204030809 71
    0x40030714403e0007804482541b01c07500c3e0000781800d0f1019002c54020743e000f2504403c24020701030880c030841d159040816007103000012006802c105004c020303001004c1c100d0b0480505100e03460003030720003484148101c000500401c0d18900e9070134001d15a1032907034080c00c2455a6142403114643d40410b80d40b600650030b07180820580c542102040200c1c0a1a108544c2881d40c69101500b04806400031801420140e890a1510349650703460403189420b5000241507210035803204024042c03642296a2300b0000f41055200e10702c060316150304540c02210b4426032a042080a40007544502083c92107414491404120312030b481e01c0824021b00300d41c00003501101344640e208028510801d082c070f0295074040c0e08100300e404407410256503100c0954114015500b0700c00103000c81846080070500c141c04030301e85001911028042542d1225001b401110141010811055100700c100c0c1c10341e002d031405580340070b64900603080090414500010715803a03140100000c00200309107000760740362414111142d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 266175944 1250 266174694 266174759
    0x816061106040b1806040f05060105030c09010e15060a0203072d1119060210050c070c03080702011407030f080c03070207270e1609021903180c120203120301 69
    0x1c400111210042c180b03201711020001040112511000c016124401f29691641c0361402c040e00c0c0e5941580268024100390010041c08440c4440c960b048115002400c161b01c01d50341c0801c0580d444201c1400141e07000007401003c015400f06068400c0c0c4174404c001411001c100703010182948c04100240c88005421900c2c4025902c2c03803042018114422051040345603180b6019441d03082d0200b248100c0c41c94800040c00016405086440d041d5204901c60003560840c0d17030340e0840c0d802c500003d0341003109504103001146440300081070790728080d89422458807a0030000500200006000414040003441440f01040c0c0004031102075a034040740e40300c0000e81d04105040300c0c0710340400d14496607041c0070440303005800108035030101020554021300400d40b1800b0b00300c164480c00c9034107210047c1c4a010200c2080c400d80c090640483c00d640740b440082c0103603c038415030003010340066003080c1b03004000204500d0b04000006281c6070b004540c0d410741d0b01d00300c0103848401904440088091541010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 266177194 1250 266175944 266175961
    0x7020f03011407111b06070b040c0f090603061b1b050f06010603020406020708070509010303050a110111180d11090c04030501060e0402130b0f0f030c0402040816061106040b 76
    0xd1a9280b001d4071031141c540b8250900400f151070603404070030303d801850519800030000d070706010145480a407005203011020381d61358009100007403003070712019034810300881d0043c03681d01007030000e0800f014045941400c5051500c101e45542032407502c510000580250040c2e0040721840c842d03203240c80d03c0f039201c1a41707041880c140f0f0404040108940604800030400940640c058800d0711255404c80d42e450351106945075440d40356000b001d5215404000400010348504003c03c08101c980c0f0b04101000203585d410f03400e40b2400441c23803030700c0407020a0200e440f185042c1c0d50140000e046030230f01000d903220f4980c42191072142d0400c1d03014503690b000064091030312404032402590300800800a00717645100c0f030924114191000c0703200d44050201314902070b1041c0110240b00300020321404020f4a00004c02c01905440d2000c190940100d02c0c1001c40c1c0d03522131010f000108000409401d036000496103001000c8203c2e0004070070701040c1401030b4400003000500c02d6105a10199100f01d5171070f014039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 266178444 1250 266177194 266177201
    0xe0304080f03070302011409100f0207050312010509130b010918020306010920040806070309020f12010501030b13050a0b061801060e1002120a270303091403030f07020f0301 76
    0x1a0244078221603040d40c108004000c0503221300036402005600ca06204000500302c042c1c03010303211940f001500380760244241e88003c24903644402c00500e040241c1e5503441c21500008070700d5440310100d00c010002800c0500805030b01801060f008580c540c0d981d9a00b1042d03c1d01070041d1000a5a00c842c1641e400260b201d4658007290002c04407010785da5264004005405003a040e4204450899208003020040c44292420741e00010702408040c1d40d0310000303d004009070001a87d004401441c450f1035500c40c02c03004500c00c104100040b601d5070442c146405004800303029030790039010440c000c0e400708601150040380550700a030514000e446500c00580344010000d02c01070040a050300024800f034005c00c0a001d42c078130503249488030110b0041e05a842d405810210351895404220f6400d480d803183c1c2920b00094944c400110203605c00210031072805201d500101c000c1888103c0910190b0f030701654984c2c1840085008500c1c0800310788040301d142c000c90800038054240c0b110b00c0460b6580a42 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 266179694 1250 266178444 266178449
    0x3061e0608030a02010609020703052b02040602011d0f06070f0908060a09021801150509060408120301081006060f0c020f150319090809061c05100f08010b0109090e0304 74
    0x9905200181d25006a55140d07800409500c001d9031a1640001d0700c2e04280c0243c800454140d11078909001c40700c5118552541c3e030000340d8005018440325070302e1a0354680f000d800508419800011480c00c40502c0407490381380d401005003907a0240804d100c0d06000001c50660003101803400321030009910310140c80718091a00460440d001e0b60741003000b0b81841c0d0b8003281400b03000310346c06103d1070104009854100400e020f00b209007601c000800015134041c1005110042000d8500d900d00365542c00d002c0d04182c40210b04502c0143e0000040005507001c000c0c00c25180080300b030400c0100d01d040700181299040d0f85075030702400b4100c000030003555991141c00503240f40c050081542144a40b0324802c0700e81c402c4a0111800784d003c802111140340c18410b012105a0120360149032001e004100500f54000340300540c038840440c0f4001c1c0c06500d242c000d590003400c82c0135a81000d24280400c070100d44005820001da180c0c03409402c0c6a040e80c0c408100022117a074050002850a010202c5604510858 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 266180944 1250 266179694 266179751
    0x11401020307080a031a0108060307030b09031303111908031204060e1006030611070b0a0f0917030103030201050c091c050f01061e051f0f2105091203100306 69
    0x225030000c030300d501500b01b030312502100e07455041121185001543d541c0400c2d122950598010442800003902e005a1a600004620300b01e9041c094421520040e040b50f0350011a4803c65010703000c9407900b0f010150325040452410700502c040d0510f01c8107540c0780030300c005486048401c100440d090200c01d178442404000418142c0d89200e94080622014008910044580c00e00d007180542c060006401070700d4080794068070503921034a905c580e59000c0c1681d540303104a025502d10744a00003c0380314030040504115018034a0b141c1d8034604000c0d007110383c01418100094800c12212038541d441203517480700d04c02035070a028030215180c14424505103441e50b2541c1107610348403020401c00080f04002c101810008a6011615190800d01003007212101c04580b002134540c080c140900e01078410040415641c2c9429481c1100f00003603103940c91110100c9202196544061040c100018001650300c82d440071003091860508442510030f400c0c491101912065642c010050700881d058480130342d24001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 266182194 1250 266180944 266180947
    0x615070803100803040b0f0d140403080f13110d1502030c1308010908030601051e030f091e03030117031c02040503060a060f0b0c032a0d020309030601140102030708 72
    0x1403800309481d50040e500458007031a6031000250381d00b8000204d80c15625901007540c2800410803283c0e00c43c1d00400c410290311a00c0c0d00c404c0c1c050a941d0f644d028072850103556289800d00780003c6019254034041c00d5108234065903102c0d08040f4140394000c0c860800107031941c005441ca00e0400c0030303003090b41003035041680d40004280300e1103101e04400307092110a03100001c4581ea07a1000c4542c00c8a01c0c184000300621000e000045a644c001c0026204841d41004242e03001044440d12080b168008c0701c2d00b400d2055001e0501001c0d080c100a20143e2009503861804500c9004107a1542c2c2d02051041100c0322503883c9405901c08000d2095604280f05038800320201455100070001a410902515010340700320b20014070340091500480c4101e84a5101c4802c80724205140e01d1140c1c1d000001e0381d841480100040c001e482c0408180d10040d1411704a05042c464554a02c0c0303090490780b030707038110455009022515280e64041009411a1201020890b906820b440140d085024091018180890 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 266183444 1250 266182194 266182207
    0xa02030910110c0d17160609080301030311010212010b03270601080f160902070201090e28290301181b0911090d060609020418060506030903070b0615 66
    0x410041e0307125141c403420b055510b150707070442c103110220014000280c029032200407a2503a200303a00006240d101006d01c6405045a159100c00d0280c4071040c3d8119802e0030008010001d1507031040ba50b5240b11303030900c02546440d140d1043e2404003c418018030b40444000004611000d801c0780366100102a812180c0c80181b640303104003a225002445001600e004980b00c41c40c02450100e0801796241804980c84100d6007008100f500a41051400702e0502c40c0c0c51401166403003000d00520320804c0d01d050100c2c260801c104041112480d11710400c01e100b030400c00c9985101180c91540c031001d403034000900c0c1c2c0546005001901405202c0007200c00343e04624407110601080c10003105034004035103015401a640e03901504100c1d8108411108030100601850446152400c0100c0d0120301684012030350030b171170307140c0d5404990080d44076400d00c40ac0160003000d060014042c6c1001408203c07800f5040d0b140a200083d100d01c03c940000f08507000f40b0f40000d165a64070051004950300a51082d81c9812 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 266184694 1250 266183444 266183447
    0x3140904090606080f030c07030b0405070b18030d21180606120b1003110402030a060503070b1809040b010308030406020c0109030c0b1030050318091e010b0a02030910 73
    0x1030301d0b003d54204d90103a030310201a14080081110002078691004101c0c69146444480720342001a004685d140960f1500050b4440650042c0883c05411200c2203038041e000c4040500c1c00040001c130005215085189031440c0031150440c5485414180300031401d5104c5070300e406620103507110b000784481d151007000f0440780144031011003c0d42c480e02d1100900e0320303202c4805421a941d444001c00c40c100001c5501c0f80ca0820ba0081d581100d0202804529280c4400c0007034200190390b0012801e00340081001026080703c030708100004401543d00080074281344c0c0740e011070347c04140800380010000101103002c2020b03d50450f0700c410386030704c02000440924500140b5008002c60140c1e103880c20345000c00d002d0320361140e1843c2203420440e1100f400305041e290380b04c0c5085d84213120704000003041d01803d010a00600040c41c640e6440d06035a02c078103071800104494041c010f000c4240c5031007a4407560b003013111082081410746104000c21600c480612404a00d14420010950340005145100c0f00c90507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 266185944 1250 266184694 266184701
    0xc0804140a080f06060f04291320130f030308191a010f0c0213050a0c050f2502130906050604090507030b0907080f0d0806061204031409040906 63
    0x11002260794081840d079801c95180d0303d0030000e030f544a42c2d03007080303002c10290f1420000f42c41c0c407054040c101003080b030b20030040014502c100044010b401203444640c0006403800200b48800f1584e9080304108000e83c0110b015a9070080c9200f10441d0304001940c0c0d511110740400080081a48000160840d81c40e8500185514002e813000c0d820014201141403441030386020b07030310100348680c0944518001c80d00c0112610084c00300f0031414018614919000f6855070041c404007450f14000108490802c106207008403002481482c08103c000c1c0800c41c505141703481100d2004c060301c50000c002065071513800410100c40030000390310076251200c06600d04002d4006088480c05428100980c3d507540052005803401908010210307000b503c020b000041c0300c40c018170f801a110004079a0600c0d02c50f4801443c040c0d03c070300c3d960400d606c920108403080e40c0c8080ca2079803000d03058039060300700b0100d00d800ca01c0004002c2c0004003846110390341120b056402000f0341d25020001481444403901c1410010001d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 266187050 1106 266185944 266185979
    0xc02060a0b190e0402030607090602072705180607020706050d050a06032a06020a020d0b0603010f020a0e0301062301110c09010e1602060907050607030c0804 69
    0x1c4503490304001018003e040a160401d05180c0101031074035800a00c0c100822003c04400d00c00300380e011807850708585c09103410781c1100910702540004900824400400c25283c8020080d00b414144803042d0003100000548143d40c890343c50403030301d88a50b03000f1000850808c010826043ca41680519405030042000151440d00d9544480128140268170445880c02c0d060000c40d918107002d00304c005100303500003824850380c039130301141070b404d050000502000c9030200003c0068400b0b410069488000040440d0360b206030000c068510440701080038020745c0380c0700e00480c1d208414243c003500509001c4000c0658540704c001154440e0440003224428001c01c001c2c10165181c03030007024068101c2c0052051140380100415107520901d03443c807801c40d8010003c0c840c585002240c1034058540c1a19160b59070074a90400350380d49074100302e0042880c07500040c00203000003603400e41400f = true := by decide +kernel

theorem cover : BRFrame.Cov 266007194 266187050 := by
  have h0 := BRFrame.cov_init 266007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 266007194 ≤ n) (h2 : n < 266187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
