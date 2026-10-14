-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0515
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:12:08.211772+00:00
-- url     : https://prove2.me/submissions/94643624-0804-46b5-95bf-0e1dab5da236

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 92446043 ≤ n < 92625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 92447293 1250 92446043 92446069
    0xd0f02031923070206030a090f080c0d0905040606020a03180e0115233a090203011107050304030b150607080306012607050c0f0a05060601020613030e1e 67
    0x1c0b5070761680049000c418584000402c03044078401c0510014015031101421241d1201ca0081c001030001e03c02e1030910603400601d00041c0c9070034000300d8a081d200c100019045041035454039143c6403140c0d80d8042006071a210b004030030068000c48100400a4080d20341c200444000307040c0006ea054071807080c0c21491500b64401d108040516074420017040d00400304104101c00c401c03c0042e070100710000f00403e4400c001200c00980020044845000e00d1a0090480c45003002c10030310081200b441e24402501808200342c1c4a5440d0504144c00003c0c2001200d200550140241d0304040c6191a03081201768018003109413820170642d40c00c0c02e070b80c804008058146c0b08662098403030030124001031000d6524003400300e500b15200c815080795460001200d03440192450b00070390303952001980d103081142c190303130080041c482e05a01c68200310380401c85510504c000c0c1d0803a46942c4c0c40480d0088866204100a00410961144201035040101441700a04070f4002c3c0310b210201050041010034400390 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 92448543 1250 92447293 92447297
    0xc020a120207050108070f080103020616020d0803150126040309150207140102060603300f04031a0708040204050601200601050a05040207030e130b0303040602070602120301080d0f020319 82
    0x442c091000e5a04107540c0c6800411624003d240c120045901a00e0004180406403148002140c3c011a04080f011206401a030181160503009128608400103400540711000b190000614801d01544210030002c2509a800c1c3c40791401c0700c0610000019400190040d002c1202040d000315405464140c6496450601d600a04040c0d1500c800c0c41c0a040404500741e0440d00018103004680c0d40002c0d0000c50191028050044941e00942d0b080c0e4018600107041c605040105080760300c03103101405401100d0144400f0150039040c0d080003d07402c1c0003261401f000c6898407000c00d0160920fa400a64004018100ba81000d0103101022071042008580c50480b644030400501260174448070620084c00159825811310344944e6000d48141c103072954490185200d804d1480c01d10440c0c0c0c001522965024003580c0d551910b0303100094588a0500481d0050310a040300ca0f040c606200046a04a03010040507003070329429008100ca41d0700b00360003000210320041c4060000c000c1031081e0b80401400707503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 92449793 1250 92448543 92448553
    0x50f0d0f03050c06060d03120f0f1505090c03010e16051b0309010e0f10050903070b160c0f0b0318011103100501080a0501030503041701020d020403030c060b09090705040c020a1202 79
    0x403c0c070140c82c010004000500443c403c00c0c40d0300000c1e80041c482c10085603424030100d0040460442d007402000d000702d0484c2e00c541440c441000e40c1c0c4000c80b50000340c43c2e0596151084c0e650b550611000c610081c800c491fa48600c1b403001032070951610540c6c03519240c90745080d0785801c05a0401203540d80440c50014201d4000241c204125a00001d10460f10b0b502960b0108484429600140c242d028840d0301d0024000c0000703140e16140e8007802540064480300d00700b580c544e1510480208101ca4201007200c5202c4002d1011445140100c5004102c800013150945196a801003801108940d1401100190349906d0b1190b840b665240c00345215031a44030030800302c50329040c001450103002801c4114240e18040042c8041030010003206c0c2514018002d1100c40c1e140102c02e02d0081c40f40c4004811174510210300842010f0740013150010040c002c1c0c1d002c3c8254800310003008508030058030f0004155024403010401404c1c180c0284620503680c1c0140c400c03a120f0380d01d80044030002107011100507000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 92451043 1250 92449793 92449807
    0x501090506090403051611030a0605010f080a020609040209010c15020a0207060e0d0f030903080403120e04020a080a050a0906090f020103052202091008150103050f0a0309050f0d0f0305 81
    0x500d1245650252044850003694141501c01901c0e62144400045212000000341c0f8248010001da0a20348880a0100c600e219107a040440040c00d080c003560044107844200003c000c1000180c0c82c04480e0001c00c101c0c54010305000300402940a182030f079050082040c0d030704011070b00c0c030481030b403c280d040000581c0d6030300c900a00a0800302c3d40d03007281007407000c02c14025029459683c115201c2941c04241e0241d26500390a040c0c3e00d0307652680c4001d2007410005004020410401180e0415a1641d01c0b00d0b0105800b03101007106a0284c6800000029140b80c00100096a1a00045e41081c1d04000c00620484191507600a95030b0481090f40e54079801a20300003103591500c100781c2c0c0580a00c1c041601d001c1028500300d0105e210f006e0282c858031011021498009101140c080100340041c01c81d030801080004a10b4000d200340300c1501e403070107901901080703072201280000d085941a5541200d1508000c00c02540340041c10f0540e030040003030230740d010010302d50583c40c4080c01c4c00b9840785034880702c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 92452293 1250 92451043 92451059
    0x70f031e09060507050414060306010201090b0c1e040518220305030f060d0b0c030c0d0c1e05030702070509130f0c1802071e03230a1d100c03090b0d0501 67
    0x1034054540810031004000030050302c120140c8a2188071f504440c1256a626440d0040740502050340d07014020740248001d01c42500380260003805184bd04c2c43c1419000c207104000300c21a40514401d46811a03130009280d641c0310404080c295100301d4074100f4030391a480700b40704880f1a03150320b03004601048000081c41020031400c04126848401195142c0c459121991f48007940c3d0805000310b04a5040031000c0784a81140c40141c816942e54484200403c0302c009200400019440c00d60810700d6a0100c0707200d5117035104004a84c0300309400d800500c6102c0c82c000c20310011490003485281002500b018001c0050703000ca01175440103001e007100c2440c0c4c1d810441c0d0b0701985441ba404200c0803038030411800000542c0751003d010320615440c00d40c0012000f80c18240c03000165100105030b82007580c10070400c01420349018118480e0181d48a103000703c0031000c1010154052400340d94400140036025503014818696811030a1181c03034100f01c01650350300011529046254100100c070344800c01442954 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 92453543 1250 92452293 92452301
    0x70207091a01020d0c030201090206340b150a0305010e06062704060908090a0f150c171303061401050f0303130306021308100902030c010215070f031e0906 68
    0x21092a00d245416800000084d40d82d05030140c040c014441c0e5182d200d4180f500070751020190300d0b0054070490752005c1c144090382c0070030002400c03d5803041c101a4581010180c0302a42d0052035400a0010010b89880041d40c5c02c041c942e01031264003500a4102000286080c003500c055804042c0082000f403e00700100510309414506041660340d88212030300919200c1c20300990804e810002c009142e4029080088884c840c6515158000c2c039a4480028610704800308207085441c6a0301c00074003400b090720300302c6000c00c6482c1e01415400c0e4160048915500c00c800400b41c0c01031035140e140c196aa81d9a034001a40c85612100c20310302d040000401441c00c00c0e2103400ea085c0d800301c02443c5800c0700810841051686400003500017a4045410516641035042000107046644120741b20340715815202030141038176140407030107402400e0b5088980d500010300103500c842a00310300c403416a24050308a504c0700380a1410300c10140c960003150340e900320103171682ca10441224400700f8001985d0508405076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 92454793 1250 92453543 92453561
    0x4090e030a021f060312090306110903070509070c020306040506040203070b120f07050421020f030118080904020909160f02030903030a03020903070801060b0c0601080a031209060e0607020709 84
    0x6030020031520404650104038000c2d050809404241c180403089010b0b0018065600014061300b019124507280d0703900044031400f180d1007000c040c050800d42801c200b10301c0c061100855019400844140000e00c3c00d510510380c81000c5140507a100d1805400280c81c0200581d025505c94101105020550070140b000e030703004e0320b5855600784c509104a80070820743d4100a09402e1400b00907004600c5032440b440888000380522203a407400402c0b0f8022581284500410881c45038000e8141c1c1489401d0602802044410a40040e6041450703034403a0040d552052100301e0740580d082104a109a8070a031416000b1014010040380b503c100d000007604402c403090100066500c188409101641c00000b1226007141c50700d070241c1c8070400704011910740b410300d411000c00795081c084040b85d001d04003005811284e480c0c03021030f08566179502e106038403068044000f42c0050417407240007040303000703903000903119502c298000220088504441414048282c52502c016004110200801ca0031400f8140b40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 92456043 1250 92454793 92454821
    0x210403032115030c09050601050912070e07030204140d02060306090703020f18010210051005130608070602010c0f08040201170606070b0f0604061a0d05071101021305010801080604150f020c0109080409 88
    0xc541001c0001809c01e00484500c2e0344506040c6203c1c0e55140300c2840100020200e000e020700e56410010350150294005000300d50354a44180c81051a07480c0100390006031130380240c9410320316240c0c40244080210001c2107070084c5a020031200105480d58001005090080c581101400c6030320400241000c00423019151840d003020144101101e1021905045410843d882c4544085a4400b800544010790009409025613403000500702c0e010b40181071000a159100c41495410f00340036220980282d030040e00041d00d2401c8902c4401c0d00001003a04984020209800d1440b6a44c510801d8001260703c01880c40c000c4040c400c09080030700031140507100a40b1101802043c0401c3c004441c0204413007549080d4865010450b52030080c54121604c8101c1e00003590386d0402607108600c00210f40c8a102d00240c0c226000180e569408149180a0f640c0302c0e2201800b891905d01d400054a115500d403400301e40c0c01c20007001181c1e424030030b49110b980700d20012034a8a2504e20154111344c07070011401c107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 92457293 1250 92456043 92456051
    0x30e03220f06080412030c020f030c010b010f0906080f06060910120e032701090f12020a06050a02030703030c02100f09020312031905040c0b04080f210403032115030c09 74
    0xc0001c00b1240d0175104140103260004c0d02c0074035908100c0c030740010448020218040000d603060034217010b4219168145003030300c500c3d91040b144542119021040d00c03400000801c0000400e2a0a800e41200c0c0d0308903400805d0a818503585000160b58111a5000f5101091140e60710040060160040c41031030502200603600f00811244001450708001c42c1c19881031000c18800361950b801007100202404105105503222921100c1220740141d800c0d1007a403140c0f000000004106104100310f40414241e58084c5051240c00e03582900035241c240300007429030180c0c000580500d0418490700c1d00c00c46603960007080c0b89400e4014141840c40011010448041c20410001e0001c000c03426250203030310f102b02c00902596181003555038003a80342c000c0034003070a0024001034503210015071000031122140c00e40314818001140840703580039200c0380e20302001c418041000401d008900a90780484441030007469540c12210250450f5030b4424864461100f8072002d00c00d114201d0440c502610054000300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 92458543 1250 92457293 92457301
    0x9051e09150907061706060403050a080a0315030c120201030e0d0c061103220c030b0403050304020f0406050906120f01020c01020c0609010612060e0309130605010f0804020a0303030e03220f0608 85
    0x14400c0000c040c05c00c208100c0344010941603140c0e40102d800868214082d509144050b15050880740e014001c1880000c2c1052000d801130500c000710300c0300722a4002c44143c0701a00c0e14002e00b00e0034407041d501340d0503d03070f58030f00103100c510b020300008440000c9543c3d80c2c0506401494210100c42c41041d48684032030042c4100480c0d02140c2c0344141a042000c0840c00e810200f501d401c000030006034100418003940d080601c8109078004010f0340c0186c0c402c0304c41989040402040c04100e840c6885040e0348030700d00704080340d03003800e240490002050000091750003250301400c01c1070a980c0038000b00d00e06a07500082c0162a41c005001c0341d81c008144e0402800a81d16140501180d06502d800150006503540e210713026a05c010000c49180b804050319000001060100300c6d0f0061000f44507450100d0001c200f404140b510440382e00b40300e1603006280f9181c45065403401c40081050328403400c0c2c9440108505808002100920002c2c40002400401801d00b0321140c251500b0656100750144241c0000344 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 92459793 1250 92458543 92458547
    0xc0307090e0607030b0627090604140a020c0a0c0314160e01031203020909040b01080f0102070803040b070c0b01080f07230f01050412080301090617060109051e0915090706 75
    0x180c00c11042d00e4081902054100010004d100b011001d0503a60300d20041c18034650341c00003550f400e0000c112520230780e0f56030b01814441030303a10840903124102900e4000400410080d4003a081b44100e1004441c40c000e045d90f03c0030071040d031236042503440946180d01d01034144410080809204000030b0b241080070300d8210528185441804010f04521401c030640c81181e01c0381d4160345560400602c144441e007890304250080210a010350b03281c0d402030900020381068140200c0701d0055004a800f481d507640c0b40c98103480c05c1805028041001800001040401d01140845000c0d01d04140505a203a191601d5680381040f50f07403040422261010307854080740f41002c00b840344074405a400803100075101d00100d4940c4669049041680c00903a00801800303041006941601d00004007004515214205c0b59070103106681c80c03140307030345c4010700600000a0542080360402c01c42400281e5403203c44000540b4510700719003840d555480b10703c2482c8042001403101d50007002d90f001070052a4100000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 92461043 1250 92459793 92459803
    0x902120d020a030e0d06180507090204080d120e0102030c0315010903171b0706020c120303100b0a050c03120406051006051b030c10021c05010e010626090c0307090e 72
    0x303001d2020050030b44c003068488246040486034080010050007400c60406050720028503c1601c45104038003004c01c8941ea903100315010340365884014000241c0c0e4a00403200c2d03008a0160321101d41d19045428a401000d002540c01a00041111a164a060190784a54840da2500c881c104111504200003103610341d19520b00a0300005052a607600c5452422210120010100103180c424100001401940414199120401160a0898a028a803800f99213000a403141451122038040c204030a0514a001300034007a241c1c28880e06140400c0344a07800c42c1c04c40f0440f000040030074010070013000600c1c411942e100301003242101c0c1a42c02c00310018028000d500c015810030b4403000003030583c00810000c0d5402d6154640840d0418111807060307001a41058580c80010502201c80140740d002d2805828140c3d45040e107004ea850780f9150007260320000540020807000c000c0d01007000c008040310b100c80c3c8900000030080c00804400f02c01d01d4030b80b03c116401040c001d807406105603079010b80414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 92462293 1250 92461043 92461063
    0x30403150b0609040504140a050303070909060e0a0b0d0606030606150f08040212070305030c0102180a03080909071709010603030906020109020a0e0403112e1b08070315090902120d02 80
    0xc1c0c0003170140d0311850611860b20361001004005d11410101c042041000402980300d0041c940e070b001003803aa03a080710025295240507208245505c3c1c000210320088136800b031480d4180082c4901450b182c9a1a03100407a46986c000752070503900c46009201081080c52680c84004480c80e00c4500104801d0005004802c041c2000b88034003800741001100c428201300b4032004e560403005503546c0b0300303685200a000b544503c02c00c08000c100d850002d8503d183c00e0b82044101c035000b0703400c00d2510302407904001001e00014628024440c1e400c4d00074411180c002c09284c4180b80f210000940c003410360401408030ba1083c0c0c0601c4c11603060241c9000140c803400c600c442203030001c40b14030140c2d440f285810f0701c0002d0003414201c0e4920071a694a6400c48403450844400954070700c494100120810706207040d91042550b81c60100c10f82051000040e1154040d61713441070304c0c0d142c0042c0d07050140d003800d080902c6580c0074004d090b80700d041c06801c0d4907006030000c1025030418001d0201c2c50141c00041c0d00c81c51040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 92463543 1250 92462293 92462299
    0x160b0c030124020a11040204051203130f0303081801060b03010308070b0105040b130504050a050102120406050c0a050a050c0c0a060203090a1707050d1410240612020706020702090405030403150b0609 87
    0x1000b0200c00f46c4882d0145c0f00502401811030444441d0803d03031a81c2d94100318103084030080742c3c2c4000501d8001140400702542e401d507884403626511480b000b11803010300411250190768868000440e003100d580171314041e61091031401d0b0340c0c071041d0038425219041030300100d10441ca0300e40b01030310a030780d00e03c141031a800072000c003c2519600d500b015402d014000c00301806550000036102050b011402e1458400e03803091204110310303203594113005024010304514002186040007111056802607001d0400260840210f901e0480c003003005c20402c80d5035911840259201040c00300712883d06601070303000f81c2600c001e400d01c46038100350fa6555940c0544a590301401140ca455014024903031820b100c1c4510b503004650f035019512a00034000c04030001642ca03030f010040c2c0301c0da10300c454020542003155955540d008141d140001400000d60000300100d4806600b0040000162114100302d48568003460145480f0352841c24242d0320464042d000541d400e28048544005079500c2040d680744500507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 92464793 1250 92463543 92463563
    0x705040602010f15151b061b0c0201020309040b1915030e03070503120c0d05040503070606050f0102070311180a0b0f100503150d05030c01091712010b160b0c030124020a 74
    0x2402c0a40c1e404006c0c140c030410581241c0424014410785400002601c0c010101141c0403141c0c08000316060840458001d0050300200042400e81c075054109500f06140140030960900100d03400342e06c80541c0b0f5014101100521559503582c54051203904210601c10024500d00703000e96640340c0d224401d0fa080d100c100950000401d06240151059405100302c0080c10070290402d414595603d0304540c400311075490a041c40401c0a0074210a0009000410f800510b2032a0460f40c604410302c03100c2d488144c01034507d80366040006903200d02580984072080d40081e0900c4020240814100b0140e80c2602641c00005402480c6a0101c00c5903031015056441482a4540000207184981050b0010301280320101d00b42191072410352021031101c0c401c07040c4441c009940c0c0e9115659000c0d03101c0c84045414403034010003119000100600d15429004803070140440c0e1a0b075007a07003543c800da03001e1048100c040010302540741107071080290008000400c0f4a5100c0e503410003940d8007100c010041c020441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 92466043 1250 92464793 92464829
    0x201150e0118150b090a0b040b0d1a0402130801050c04120605090307020d0b06040b1219140d0804030212120610090b0307020a0209010f031e080702090705040602010f15 74
    0x41644400e010400f841c4030840c0c1141c0ea084074a94039000380d030714288560007002d0700041c02040d1004407001c440c01b0016141c2005a00c83d9000010109140c10310640c0780042c8150140d0b503a40e200030941040c140ea10030107242c0c14242c1450848000030402c44515900304014840c4044031003016102e03541c0035501203104c0e584d4200d06800c5009400000b500280019850002c0005281900c2e2144d0002da400300f041d147d0b6407003004174034150119411665084078848081100340c0d07a00046046014500303002c040011008000d02d003203040954500041c035540140003c141c0d050054500540c0c08a0185003010341000e2500d403883c2014010510550f03200d0011514140201e852400074036950406917202c2c07918820181d250b40c0c02d14006c920585e00340c00003081d1000d901c3c03020f20949402c81c0e0400101d850904041c0300c0303c000d03032005464547e0103101000c0140c0e181103a007441131036941d40d001d88030391030a0006429038501c1d490480c0003500b032008004c08a45041c0701d020444000c0209014103041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 92467293 1250 92466043 92466089
    0x3050a021e090421023009061306020f0102070818011b0c050120060402040c090e040503041a0a0f14040b030a050108070b0c07050607141b010201150e01 67
    0x10040c0030740341c2011109040105100c80d01d0641d441d040004020301040d1250400100e80301d84220801c00d6440076055441000482980c0c1030820b045030910780a0f18007000040094065009408440005400b080040c002c0c20ba041c8040307807169004800960030101c1c41d030f40d6191103020340c00c0440081d82c42c0102180307141c0c0c0708a2140c25107030030200c02c40904403250f0504004036912401000e000c218048051107519102c030400382c00c1790304560040c10300c0d41c0310b5908100240415210301810081c91000110350fa454203100240038501c214019070f5580e18001d0500f8481908003c802c0a102090101000e05a00a504505900b80615101c2c0550903148901440f034004c640100c0c0c41d18001100300b158449459101606a41e5940103d07084542d403a06454568404d0311400f05194014110401c403600342503018144042c811761404100c2000f10b080c8a1910301321b4007050a201541c42041c40040d6020711882044844c81941080180e01301a0300800b00b11040c0300b00100c0852070320b07031070403920 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 92468543 1250 92467293 92467339
    0x10030b060d020603070e0103270b060a030c0f03030221070201120f060603150e090d050c07051203120f090a03080a020c0d050c1501050a0312030608160f080703050a02 73
    0x6500a10058803400c017803500030301300402c440400c1e022074585221034401481e0b4800d8107001107000d40c00c90b1102e008959500d0041e9601501554201200c5580800041e0345120110044c089a1790301400c0382d891400c2c000d140c1040c0302d20080084014140d52800c80d51030310119000d007902801e10599944034060400c0003400c0040009140510b00800031400c207616805c41d04402814035030021000b40c031404150354841d0156060081540480c21000c5a070780650050044000301e0b20543e10b569959034089a4003c21101c003016541c0c00c001401002106004515500011000d500c00280d2a08170b40c000c2d0f444610800c0030781446000c1001a80c109a190121500c1000354019a1003070b42f0002405800354015164082d100d015084560034110308250720341d0304803a00181100d034050700c0c0d51240d809069203030251000701502e40c440811120010402c20010400d9031150301450303881c05510101c03c4059401000aa0304403030000c0000c28800103c0c0a080c0b90100c0d03c400c203000319089401548 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 92469793 1250 92468543 92468569
    0x90b070209150405090a060f0c020a021005070b04061d010b01020303010623070305030103030f02010522021801080313060305010305030a03020c0304270b010f0f121e06050a05060310030b06 83
    0x494113000801401c0320340424800c220324403d800138407103445081489001c1c1e880364504500140d00481070310025113040d20560a80d514141002c2e4582542600ca0840d0348100700e03000c1ea204c2e610388070410503054215040074030740102a0003c00040300ba020000317403640300600c10380041100c03101d4011800351041990741c0030300e070044010320740d100020711b800f5156800901c400d8002c5502441c0c0d5840c000c0c0103005440c40b800310003001e000c2307640e00100300c408210701d0000140d0700b08041c0008070005840355081180038102e10801182c840c0c0300360082d100080c4c00380c0c002d01e0400d0709000041000400c00810784002905a041c0541c44008842c013151450169900581540086103000207030342e104c1c4108404444ca2140c0c061015149160055500841a0000d00000344200c5a81c240c01d81c4600c810001140d40c0030404211400403910795113107039100008100020703a80e04001c100c20300d45080c01e80d00500043c0c44840c10740c40d1030607440141446c1d40c0b001030464110000003a4503603450304010290 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 92471043 1250 92469793 92469799
    0xf021906050103020103050105060c030406032a03090506070512010e0604020f12040c090e060a0b03011d1c020c01050a050903070509041103010f05010b1b12030106021606090b07020915 81
    0xa080458100391000d00020700c000d03800300c3e10305030000c121420b24404880c401d400c6140110701d0107190210441c018403a0648030b8010903140407001e034105211a504065003007076681c0120303900d030f07441c02c18034101103010b000352003802410006640c1c005010101c1c207044038140086111165500b40c00306029110318100950341d4440094140c6d170705001411814020750040c00013840154540040d00211922000440341590112001860300303402030b0407070a6844000340001c1912140c0c81020a04858085070910707042e00085c0060000252000090000022910090800e41443c00010302103101c4c410100c0200170000640084503141013000100403c0060180b60030391809080c225140000e128442e072080d400c181039140c0360070060103003034140c034408607280385810b61102070346240002d21180400a40100604000c80a0b00348002e1030007031800e500680000204e844100050310015089136007480b11589082c020540500d0a0b01c44050381a9010986522144d03582c01e0b440513184040c0d030b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 92472293 1250 92471043 92471083
    0x1103010510063504060e06010b09040e01020a0804030f030e06070e031902030316022e090608040510050c0910050a0201150e041101050c2a030a0f030f02 67
    0x1079414400e2404085440559495201400d80c0d5041140d40b0322601c91100d01000c0800b25540102e0351000240d0428030031040006e139802040716480c00c2c00000d0340300400c00354000c40c44540a090502441ea07072452900001c528008441c0030144c40100007030005000c0007030300d12801601c28065800920361840e90f80c11a84285040b450091852202448150183c09103105e13240c18444a01c182c0f05c6880d9000b0301860400e260080281305104110328166032122440740000306d41d0742c10503034698200400e52a10305c002014a207014040d8122a8852010049104200400b01d0804207604a012080d003402054075121540150014040c0702e90550b0311403254080b074a003064000c4000c09180100d034000344100b2a10800e0896100c0f03552203401179540403500050b000a80c0340840c0c0894400505100b0b09000c00c0620340b500e403400201e0310b9800706011450544020b90300c510702c8042900111b00828418510781d40c7ca1125848001c1d0080131300c0115000e950a4038002c0c0040c007201c2005640c0d1031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 92473543 1250 92472293 92472301
    0xd0b0d08030901051b070c06180e0411090c070c0e04020f030f0d0f02072105070b040e01031106040b090d06060b0c0102071406010812090102070905190e030315040911030105 76
    0xb60080c0002c5d2020355802d000c081d10b08061554110030303a55500c0d0001c105864851900c03005807100344545140456041c1c0e42c0b034011500540d45007800b8021b60148841500103103050051003c0b00001605041c0e00403018032801c2e0008480c19000d0055440b000c03001231183d1698400304205070104201c0c1c7e82d06000307003012031b07080d0f4000081e809804905507480b01032450005605a81710340803409801d9214110117441c00e03600ca000c41d501c10354140300e141101d502070b07a94040082140c2150308285801c0c041040104180b04c004008800540c02c00c88a40e464140782c130f034101b40d01d40300702014139004500c0b115040050000715072080c0c00500100301c13015900d40c14039184074002c0d4031581c4103c0340310613001001c83c2021000107400f41138070700940040041a500b10302004442e000000c00d80d045100388000440c2c0d400180c0143c50213401078130f18a03030f4651a00001c0c003040d40d80c0108903c10b2a4014010048140070071903054103848410b46000862014a04001c04000340d0444090741640c00c04c4284 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 92474793 1250 92473543 92473561
    0x18040501030809010206160e060f0c030f070c0603110702091302040e0d11010c08011a13060c0605090c01080c0f0c06040c0806010e07050406080c0702030d0e03100605060d0b0d0803 79
    0x1803840302c1c001d83c20f454980c7e6070211068101c079040d6088500160486c4454800340c00d0200060202511200c90b49003052403d4803094a15800509034065000c00418120104009041c5820190405c4d05052081c0308003028402160b000386c1070007170b201f649150007086403050098007189009030040c00500450000c0761a84d0398551010010400154010407018413078031041c4101200c08140b81e407101026482d20036a0801c005040255503000003042043c4a010504031060000510703860f1078603c0c002c22541402000c80d03200500d10034075504008845050307070b0390055106502503005286030740c030b034199021101011301404600305010303c50101440180118012884100c07100078089400c6a80c07280d41e9010090015a0b00a010034010b1000344500b5005140607540300c030780080b607107007003030061340001e440d0601d503440c0900440c910384600e090a05061054820180041d00c0074000c991070b0202258061043c01d0500382119a039103810403881da20b0301c000350f041c0303a0400044e03503c900b088464 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 92476043 1250 92474793 92474797
    0x140106080106090b0306030c0f011209030e0108280e0712081201050a0b070609170a080a0506030c010c020402070602090a03060f0c030912080903040f0303080f060d0c0b180405010308 80
    0x2c60011907030788080050711114440c00c03248500401b40c0501461000c0700709120645400aa00f941400903401d15024104043d200b0074800502907611614400a240e0000d002034102610034041075000c03403200352550224a2a00ca00c0f000113050006800c10040307a0030b4103002480c1c000c9104505d84060f15003c1c0003c10018103600000c006418140d640e907202003101340000c52040c925101c1044c4184004030380c03a40c4c4030510a500a01100840a811180e80000c0d548540030000103d07072150144284514944115903100d801a03009210603500080041c1c905021144000d10458001400904000b025015180c5281c0042c0c0031100d010703141d150104c0640440c072030008401d45480051007249220f40a40014546c0000c0d24a2803008012011030310b416000302142041d200401c03000400b01120400400107600941d181141800c001d490f080d509000030384900c1c86503190881000100766019040c40840c2e54100066035500c0e14424041450f281151003282e11500d0a0000014841b40c500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 92477293 1250 92476043 92476049
    0xb100f2301030203091203090313080607021005062d040203010626010308190c02061602030705030c031c0e0409030e01030f05090c0d14100603030807090e060d02041401060801 77
    0x20240300e128122004504a00003107490a100c2d0340b00083e0a01c2c501c044000a41e000b0001c2c6060324600340050407035442d15103269005c481c01c3d50282c010403150b250b05002d0701c40d580003128004d2140381000000181905d140c2c07500d00440041841200b43e02043c0c0740c2c013030b01102d40c0c0039105640381c0d03948410261940307038004090b00301d441750b80009000448902903194140c0b0741c807205c0c0a040c03071000302c01d185628807102008414060a0341401e00941e072000e01810305111214084c010f6007080d80706060a00082e51700a034045c1d0711204514005030b40218003030100e42c800c001031034209405c011080310304104c442c8410390058074112102c028180d10144401004c5020f1f241403204529418202c4100c40d41261000c0d142e0700301e200d41110314940701600010b010301a0801c4038200441407085410044005048140c1554400003081016003007918240d1000c02824034450311803403e440d840103e0002000b4600c505100c04102046654a900c088030441180001034003540c2c542002034060395081c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 92478543 1250 92477293 92477339
    0x90910170d0c03030b03010e06040804050f03120931090c0e070e0114090a23151e041e050901080a02010e090705070f0302010c1d0d0b100f 61
    0x548400da10440051000c9505801e41d65040102806407411001481e030600040c1e455500c5165a60100f902000f505004d00d0007450f209039542e1078082004000400021103e0182d08940d410030004042c51040e034484e241e082c3e5045007411840c0c00303103107190740c51140c40741c043c00840b0a412032488010382c00800200e200c0c502142c2c5243c0c480c03c181e1031100084489100158100e091004694400c02c12199140f5520f858030703051210020000d40c900c4440c1d04a46a2004440d0b41d000030b4414500d0300700061741c0241d4150507104900380d41900c03503114a2050350155a078100c0700c1d0038040b05c4207080703070000e00403514004400c1100d6002c56000c54440d11405101d0b0b114640080703220704022540d0071011740d058484c202d1440716201405a00b580062001c03043c418280300f503d02081e009580130101621a600020395911309600182180e10701c200b0210f040340c00b028142a050b12518014030106410210810055840c03130700803010120284c000c1031003014016000078264130000c80320881e0003266 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 92479793 1250 92478543 92478569
    0x11030c1207080103080712300c0305070c060504030912030314070e030d080603070302060f0a120204121e0206220e090309010c030504080303040b011d040809010f05090910 75
    0x9040c00b11103900c000c0c00041c10f068401c00c090000103030a51248005500c440c1800f000004803614840180001400c840320320004440c8004482500c0c0c0c4241020070b06541400c01c2581400389000b0403424001800500c4103a494002c07405140c001e1340800010030040040b0015426280360090262054440580a07041102e01213024a4090b03040720780840070180052904224060044580e040d0141c1580d8060141600c00300c0035031580702c028002e4081000200d5070760b01c0c0b180002007154003074404a055807881440280102d850400300341e01d80903003140c0b000c46c1d040c48421054501c4900084000d50001e80001c0c9400f02c0d540102008440a03d1110b0440d071250303640348400002c00c1c04803891160b40d0400c008105d019030040c80445c3c5407034013038a802030525464101ea0703403641d4402d803015100c00010800400407644095501511008400e545002509003552103044c10701524025905100101c504114104d11500a65400d142c0042000005041140d211400c1c0c10f0170740078414100e00300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 92481043 1250 92479793 92479801
    0x30c030105040302060613090b01030302060f161e03020d2a0806062a03030103051c020d020601031e05010504060504050f071401050a03091b05030106060f0806040f11030c12 76
    0x184190382c42660550060f00c119510582040414404541c40c1c0071503e646840725008201c41022081c00380d1320940003400c0505003031401e1036200000802c41040b0101807041c3c0c3c80115403000840080704c00010600c0b404440a41040c3d001c1d00500707601101c0203250003040c90114003c03000181c61602c1600744a80c0510701ca11003229803820450348280c000c00300300f200c02c4513550015104001264403621006c42907901700c06150642d402070b40140d40caa4032150085151542c805003941d00341c0c400d80014020b003041000045e48581051101401030b140310301e2080e0307035600700d10212210554440d0080015281500c0c0820007030a081c4e5040d00d82d4800e45800d1518250001000d5041c1d90019080203000700d29200110303901c1c0d001d9896001016100c40010000038080380801c01814500c0303104410003401c0c08141400c503000c0f81e2091040184c1800441600da81000c0000e070000806d84007c5080410301c10594040c1202c0c114103944440f000042141100800002e0301407580403030440c10312074a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 92482293 1250 92481043 92481049
    0x13120f020f0f0a0b070302011d01020c0d08010e16030f0f06030b0a05100e04050111180f1504050d02060705060108030403150203040c0b0d0603020a0602070305071a030c0c070b040b0702030c 83
    0xa554031440340c0140d00f01034140710280040c0040d041c007920074800812442c80440e1045144548041c9107143c50390003080d041707107064081c0f0820805518518010b00c4c2585865110301c0700d00001f070030143c1601101c0c10801440d0340f082e004090b811110250a012541e84203503040e009160a100c2560303403200d0b900210703600c844a40a241d0007007810380300703a440f020b040140f07102424401500032035866588040d4019503030380100281078141ca5a031891400e40c4d03070900900c10101c00046010b845018002d016900001070641940d058880039152070340354190701e1011030b49134450f587c0e014000f032244800000e95201e0000c020701c181c130300c5245071244821060411380300781d0100b51740080114001c10070030300c404401103003d4500039104200116034580e40e9004241c82100e190400c20042c1c100380d0041c0280a010071440303005000900e000341c1454024034103100c1d1400050405c8172051000584017000e10300801c0500d018000b245820341e5104e59603c140640c950059400301c1c040d01801070f48a490b45 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 92483543 1250 92482293 92482309
    0x501180206070b090109062d0b0901120f0803010b030702070801060b0301060804030c0b0702010b030115050d03050702031029011704080d06080601090c0915021213120f020f 76
    0xa601030809402c106041d600c1019200000708002c2e079540da5801402c01003105030064a1811400c981c00140404500003101001654030640480c4a424045050100d489540000341159048200141c0e0000306240c1550322384880b8401070032558001c0004240c40702c0140c0118002ca80c43d800b21258581d541030090309841c400e10840c101c9080030f100403c00d80d0b0141705000ea2180c440d20b05400c2d9500c040d5910a01208103030358046c0180c0d59140700d0750040c1401d02c541d0142154098000c002d8610f030200113030f00c1580300c0360001d00300100844c1c40740c21514100324207002162641c000b481411315940746a0840e517150410b0940a00310790705a0f400a50203248194800496204803e141d55520303250b0b1003030355200001c1011070a035030703100000307030181c040c0030050203080840d50100d410340491070018200680c030b41044071400c01c214005c1800c540c0001c0c08485d1850168100340d100c02400d000d00302c0c8401d640e072296070400c1c0603460700400c0040a0380600b003118402c4807001200040c01c010701181b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 92484793 1250 92483543 92483591
    0x2070503030a06080d0c08031b2b0608120a033c06081b030f01090c090608060709060f030605090f040204060f120f0f0f03080a0f0203040b0f0a0e030c0a0501 69
    0x1082d841c01154007c01c0a01e80119802000d800b00012403503915186140203074840c2c1000f0b15525020300b07081401c44003406604120b50003804080c00312900300100d80e41c1fa4010199248400d50002070070150f418000c3d08500034070700700c400b040c03025007401008081042c5240805002c402d4402142544c5a40f1745228100548032800300414034140c0c140b128284071030354441e909502d403040c902a1182520700340580c540e00f92141159180300b41c030703142c1a141a11400e40000d005508000f0800074100d900803083c0081303900500c0c005140201201d020740081440d0340140d03070004400c2c401c02c41e21035000069a4000c5100755010400d0565807450030001010b0741c0500900a2044845500030842410742c0b42030384c0380102803407200a001c9960f0449103116814045020800080800c948604207100b00304500f010680306600d1031030240d5811005201c010b1810f480e050f40c21001c9280d05c1800d520440305085844202c030790719148124500d40d5146400001c40b03070b41d0f00b000c0224000e00c264100f61402c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 92486043 1250 92484793 92484797
    0x1206050f070c03030b0109090f1e060522020903030424020601030b0613140a061707030305091315031110090308040303030203090f160302041a0f0f0303040902070503030a06080d 78
    0x80c00c4203680c00c44c003030b04140c400700c0c0c100b2004810105802c0218814481c0406001c00c000800030f04652411a240b6000d41480322400d00d0081c00b08016181d0405040e40620040c98002203020f511040c10000d01916120a40500c00032401044005e04040c0c840546c440c1000d10b0380c01d0100424040b80d803042c0c01d00009000340d0000b40840c807a0300b045841280022420300022035400409805486262421240c284140b501c543c02005210800031003d031285002602030700440d400d41e01d0150080c400c1c02034030b038054184a11060030340011a8460301c448150392403d2136101341d41c3d080000710f48401c410010301c15100c11441191460103400d00070100d942c0300d81200e04241c035546060b070003034100510103441e80c01950007605480f642400030b03141c0383c02a0050100300300e055005000407900d44200300324031421740b851030b811190b0b52000c014484000032104808804d109c580400d08500640d80b1a0080e03500209680040140c040050f51042c0c404c0542002020350701d40b510307070351201c1003061080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 92487293 1250 92486043 92486057
    0x6030617070e0705070812060f010f0503070c08040506070b0403081003020a03150605030d1106010b03090a150f0903030e010e0102040506180f062d0405010212090a0f1206050f07 78
    0x40b203450040700c1d29600a00718108a0300384900c545030200141d00200600b02a00091420807001c1e1a001401c403040881c20710700061481d001860241140c880903201c9001c1c450f1038807540c03041284000c00c95001d0140945010b807100468600484026025603003240801c000600045e0b4000c0d0411080f400c0380e4000f04819505c515544602c0d807403a0b0703418440740105450301408140c2c2e89040103800b000603840e9580c0c4d0b500400c01d140080c102441a0820800c0070400c00520101090004120031450340104500380081d1800305c4400040042200071020241040350302c0051580580c04107106101100092001a1b9800d80a500300c3c4a03e02a5540c40300e0180700701c010f1a00303545014580d104000d840c402d80144c0c2d500001c0d25079044032503d03003e4020300404d1083d03100d420b91850072505016084d45410541003e0004c2c0d00c43c90301840c003140712440801c81e600e00d55683c42150b030080c1060b5030102540c03508d5401d09070b24110a02c4055038000d003000c0200e41444440440c3c18421840c9560b0701c1c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 92488543 1250 92487293 92487299
    0x120c020313060509130c09080609010603020d11040e07091a030d0c0f060e060406090210030c0912061d030903070617040b25021b0108040503040b1e0d060603061707 72
    0x30b1000d1304640032060700281c802c4514006041c0c1441031002002117516214402864000c0c554541480104408a103905051003040107803103044e821500181d002c441040a2545100400d00602c03114a418401e841141c030001805035056001064401e4410a1400e0221a44062558076445030a1200005407803005003004907c0d00c1c1d1440d03504500c50a00422041c0801b590a458484183d030f0607202c155443c0c1c42d034000c52500c6141c00100016600f401c0c00180300b800c01c080c15428080c07154105c0c4543e5568100708224031039200b2202c2d01460109000310b10303d0851204d580e500700c12141da000b0300c02e00e940400c8460103001202a00501c0e844040055600d5a0715038001040160240f00b000151003205498001c00720703254010b2201d687c0c010006146c060740d1121070070805118a5051082c0c20040c000401c0b00401201d0540d108103c450b9550300c0c045d00140d16101240c2007046407004080b0702d64010340c81a411220846040b60380500009849184154803034075a0462513416a010b00d00030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 92489793 1250 92488543 92488547
    0x2070f09020c030705060412090909020a090c050702030106030c09200703050d02042102040510080624030601080a051b0607030c050309040216021f020d0e0a090606120c02031306 78
    0xa020700c0c00d181043e20b041050980c0c1d2545000d001761800c4030034411058042d041c01e58811320490007016800c00500a00030150081030380d040e00d5005d4560000c1c0c99030b16001c15540a80101c6048903401b600800c007099a03802d0803a40b02d4001c0c02074000c001e08048148114543c2c01d0004030038803400566451400320203550544d0b40307070700003801d04800540038800056140201c074210340e00c2e4418603d1040c01c0619510402045a0300100b0b01e2140300c1409409110510000820980c81802c8900301101e404082c84035580c1442d14071032080d4184140c80011900880200d10b1114007440340d07044501e400342616055204207051045503400150510aa2001c68400c0028901d46805501644e01d40700070f03100410240e83c00880804da440c1d07140b0385000b04504014100f000042d508501c1c54003080348c0f03c08001c2d1180d103102c09406c00c00032603c2031101140d8809800400030714a09404014150390744201801d10614102c42c801c4861501c03402d4118907001004442a2814100e000f12206080c00f0003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 92491043 1250 92489793 92489797
    0x30b0f0f0402091315020a08040501060e2206060504110703020c030c06070305030703140a0b09130b010302130204051305070e0d050607030f0902120c030709150b09040207051c0f02070f0902 83
    0x100759090209854100d171850903a00c014007205007a607071b5100e0640f40500b405070940f0f44a900407107401250808020388241148005c80130ba050708400c0d41301c8004c2c182012070203000d80b50441544185880082505141a00005c0059903c40d17000e546242c02035404068a80c0d620640d540d4000a042020030300083c1b0443c000c55200c14030303060024100d685101450303c549011a200c411031961a203000060345482d0905540c48071200546181a601540da038000546040c40000d0180180c0880450f880c02e40f03130190b5024080240c400c0046000d8616814043d00080d5000e0021480c004400d61f107038100302d450790011b0b58102c5c004040507110358104030700030200d103089250b40390355880031b4000681c1d900b10107602c2e4442c034200410140c0810010103040c08090341c010080d1500d8010040605490340700e1340b400729845040070030307151113011020034060312440310000c100e40584c2640d0503580c10f90382c1c50680900c01554410200b40311030001682c0e189094041c0308219003255108020300040e41d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 92492293 1250 92491043 92491081
    0x607050a051b0a0506091216060b060d02070813090b010e010809011e020307020d09031a040c0e10091805060103020405060a051302120703091208060a0807030b0f0f040209 75
    0x2003401460394895482c0c9050001c1c0340001c030b032141c200c0000c0c455002002c002c0e032400d04d492005c1d054980140d8480b64004000340810007005a502d0741c24410050742e603181641c01c10349120300c080d50f48030f030030340340030b1002d98058403903800c001e4058840468014510721a80050810623101c09829154900c019103040c0e03c0100010380540d2075907010703158a00b8090025848000c4103902503181d0038040f1000c0d04080c003d2821504104030070004002107040001c6035200540c1402c135001607504d460402c04103510154205421809070b03002440311910030b450000c001c64088040c00c024001d00760010340e01307001905d48042c18550020340180054a8240d20450300003100400701048969a0804208c0f420303105041039400c568082070a00015a45d5441c4691014a40c80e040042c03414695035001c0410403d0b980c03804019074440024866120400354401600e1503908480000e07540c0e10342010148000c5800000840c0140041a00400c01841050090380d000700f01d050690f44041540e034444110721 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 92493543 1250 92492293 92492317
    0x3070308180109051f0c0203030a11090607030e120c061c0f0c05070c06080105011707091a04091d0705060304032a11030604030e011409120601170607050a05 69
    0x9401c0840d544800d11400034010b1241d0064a084c0150080c0742c4000700c4118000c0d02031509109400000c00e5010044940c0150924000590004000d40030315040c06043d015030b42101c4005075031700c203243d0010340070b195206085580b403804c42c1c645803009440300d83d49030485070051801e000e10300310040e210300f00884c440356103500011503d0703600c85100150340f103021250011a200042410a01001a50b41000ba000b00d00b800852540341200003800c050b9030465003100c00c44250302190301c19101c0d5070b6200c001e0034144140c054842c0b04048004065001d84200b2494a02e0720b1a2545058851203031400c07403859031006040c2030751074202401000e500083c011001c1000040c051103002d07107014a0f940c407010114422402e41d029070f1401445820b208080700e84a03034041030400000a6004000807402d0000786000c110716082e00440e1107241c003950310a01c4c0e10074003d603d80911080f00242e41e5040301e8010b440360101500e00b81d0b0382da031181003d40324100051802c100607134260740603d0050250760180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 92494793 1250 92493543 92493571
    0xe030f180405010603021c020a02060f040f150203010f14150304050a080301030b040b01050f090601030b030a02041e111306030c050405041d0d090509060909010905030307020a0c0b090303070308 85
    0x5000240494a00360440000305e980030a60500845005058128070594844c0c00c5260248844002c0e54541c4000c03e840b0141001cac0000804000301c03a60308001d041d600915200a0011012210001e034109000b05002c600c210880018100c4030002c501e0a031040141c070780849181d64804980041e40003c2c000e8550b8441c0400400004100c800114020b60158200c3d40c0d60f4141484d01100206040e070003244100801403590302c0035907444091603001202400d0009011102c2004241808103042e0069030140c680990300c928082049412030303400140d034a042003209201407000c030080c06005500c54040243c5075080c4078142c0298400c5c2240c000b182011030030240d0f00d40c000740c1954100810800c00080c512655804000200407103800d040813800c000d0806400c10004c100d4601c8000e000740c0c4902e407a0300201d0704180003035108100c1c1c143c120040d03d54914001c1c1010350f54003960042211400304982000519540905c2514032550000300518a0f1000310385085809681c080d06ca01401642c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 92496043 1250 92494793 92494837
    0x90503090a080d030609060e060f0a1206050615030c0304060213090e0a0303050c04050f091b0a020601080624040e070503030d06050405011e0b0a020a0209070e130e030f 74
    0x992a0007800520300703100182001c1128000040c1698682ea100b0295941001c40910403008440b0b079140d4000b10584011659890510004030400300310780c0915400c9000052100c280012600402d02c20071054441c546040c0100c25903034060300c821541c40c511401c0900100300081e40ea9001840d1a40d110400c0b401c080d92a40c189204a480c141c3c0700402c2c50b80b000014404268140c0a010b50140c2c52003803203401e151610340072a40700d03000d000500c0d10807070b03070755000800b400c042154000e154190380411a489061003c2d01030764466080c00340070041c0c82840009200c4000380201c2e2075107144c2420055010190400502000d8241c0a0000c090b80c0542400410b007901c00704003612042d0807040c0d0105003d4903140a00c0304680060300f1448000c0c684400705242044061090300444076001c1c8250b030340748e0072550100d041a060b100300030b610000220502c41c0c25030b4032200010310b400048030900c1181180369500d000300c0320016402c4059410501840c10511b1668024100324403582c0c9255070040b01c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 92497293 1250 92496043 92496049
    0x2041e120b06010f110d09031208010b0a050906070c0f0305100c0c0308150907020105180307080403022106150f01080915060301020c01060e090c01020303070e0d1401090303090b060a1809050309 85
    0x454900300800080c5070020400c02c9c02450380f81c032513007401c66003040743c030550400305140c030383c2c0c46941443c01c00e2010015a940954071484100c82140703070040230b01201103840302e08a0941604a03c01a20305129030718035140c1143c0f6030b2081083c10310321515410044841d56a0560780c504004011b240e41d60801c8040010640b41d02e00d105100f01c0c0c040c1c0c00000e680c6421030410800c00042960030540c0e0780700b030041c040054900e4003100c044d2070301141d00c0585816050038420801c0d0f036004003900030b4042c0c01e040c0b0061a505000072001e4410486110b2100300800c40115500401240c4960a592055000f488002c2c6441d40313941e00580c0140026290030040c0e074895080d11215030103840b61850310710401c200d91606101e10141d10000344040c41c51401c11010050511400c050b02c2446101c01c0b81d0080c4c1040208100c11040b041c44400901042c0b400d0305000d4020140c03928259112040e80f00000c81e1450181c501d541500e0120150703202d0201c80c2c0041000800c06c4a0048485101c100710f010392a40d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 92498543 1250 92497293 92497303
    0x1903050604030f020d020a02010c080c0f070b032413050c130e040c0909030f080a06170a14030f1c0b0a08071d06060d09050a020402041e120b06010f11 66
    0x41e010f03032160502c0e1100740c0b20007440c2075030382c80003001150008001d0800507039101d0000300c0f009030024001d58480545e4514281082c202c5180010540300351280000c50010b410091440745003202c0740d1070708490813400c1034040e02000c5001c1c0c9912000c196100003640e03040f944515000521510014100481c80e41d00041c000490341203040d4600071035082100300981e108000c4003802d5610000d00c1426a04c1e038002d01150000e8150506209240000603181c00055105000524003140039a0084000c98101da48800040d6010303110b64648600032200c1010010841d003180d080e489a0300e1404425030b0100e686818084001d00f1116100c0c418950a5034507900100090501c94024096452030254802d015109882710701451404500400c60a0796a10f0150740840850120108000d035007840c0540c1410b0400400940c024400700380032844000910b0840c2034050300c0200586060b4558001c0d0141c6008146c00915040c400d400003446e035449680c505001200ca8202821140d80c4000e08034109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 92499793 1250 92498543 92498551
    0x90903020c0603090106090614010f080c071a06010f03060b030a02130f0308030702060a0504030804020607020d060501090c0e01050403051209060c0f1b0f09010b0a02030f0c01091205030c040519030506 88
    0x3586d101e0b030b014405503800b40b03d000010000020081c01a1b0030034000600600c2d11904820b05100078200003401c0d004600f030490700c1c901d0344112001d4400610401000c0404802d683c5680040c0b0400d034030660190107481410191a0006c048509607a11800707501d0203940170060b4070035580340388100094805400d080c1c14010f54070070b1a0240d124a01058004d20301113004188001d61070604c0140000b0a400492054000d030301a500030342e8541c203d002040c0e1018510000030041fa1410000007602e044e540c1c0894030200c240e90f10b00c075001203440d004441a01071400083c1c640e403c900150b0b5041c0201d45d004100354000030f81140c2c102912a64200d04002c000c441c10016504520ba02e0000c5000659003012070290481d42003020b1482117020900140c014002c0c8454680005400c081c1c860080060304e00880030440350a0340c40d402078912502030039140c10100c030000710701d802054000b405413095a1041d42d145082c103003403518000402101260150700c080c5040807601011000c9103003031000500c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 92501043 1250 92499793 92499811
    0x301060801020d0e190818011b0c0302010210060305251a120604021614030c0d0c02100203030f04030516060221090706050f1e04030b040c05010216090903020c0603 72
    0x1010444c20840c0341080380340268021101420070700704000074100c2c0b058451000780e00d46020807000c40c3e0001a1083d004c070304450600050010400020017034140c0842c82900e20030390a84091002c0da82084090305c07200d0100424a812010303100d008514901510103020380c8604a08010a58611100c1d13950700f0a69001c030000200040c1c02c180140240392015000741003a42e0440c64070401c0c545002c02c07a5501000180214904011056010420000e80d00c90202003401c0c1c9500b0400140003410395040f81408038056404200284543c60000c410f40b4423485001c1444003e9a40e6503404880179888020180782c04c01c1d90b00c81c1071011850320b101425048038659000c814411105400440c6200000d1014655600a060500040345d100b810b0318036404c08402c100e520741c0085201200200d01c884c1c085030125102060010500c1980d0408502950107004040c048588078001261141401c2c210010b220440800c01c008072a400c4d40311f09031060080c415601041f001c1000214194401d80300034074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 92502293 1250 92501043 92501051
    0x1103090f0f180109050c0a05160606090c020c040e0309010801030803040501060306020d05071e050d0b0f0607210306030201050a0f020c1f0e03010203011206020309120c010f14040507140301060801020d 88
    0x204c105441e1003910b0f000030700c00a0090600000d004000c1c242e21580c44260107038440103148808020240d000394000d0300c43d01100703001203403004000a50340d600154805120300d090030440d03907180101000315410201c040c1d50b803229036800e50711002c1d00da5101400480b80c0399a111400008994984080e2003408140b08001c2803a0914120041c0802007856a02512120302078060040310303081800c807060754003001c101180074020701c030002c0c18599450f550140c20a100103880030402811403104500b11009050401494820f154128111203a900000780826420030041c0031140c082d03400c3d020a00c6040c81201c45902c01000071401110174100d020318440c0c0c11300b280c2410550002080c5511030810740007113085600d401c0080319244824440509916400008103403000703c240b01c58001450441c801680c4d54924683d924000c0c40c0d06130f20710340c0c2240381283c0301680000d805640da004a80040060088034240390910b08001030082d0415410f6507198400100d8000a001401c51358101080001b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 92503543 1250 92502293 92502299
    0x7120e0601060e1905100c0203120d05090a0b07080a0605030d090e011508131115030a0b0f0904020424080703051903023f0901020d1103090f0f1801 65
    0x5064220189146407142d207800c882c2a0f130003118806900111441102c0d10520548600d0301a80d40040381034020b50107000b0803142d1001e079a00c0d580100154044407008101e107940f040582030f1120000c400050044031041d02082c41203101c0c080740303908240b500030700188490350f410019280560440080000c1344a050042140c900500000d50042000f0341e0700d00c080c08804080140207a20081c2400195080085402c041c403240454484c0620800761100030700c400320545481c116042140d00c81d1026041401000741420410224119a074014114540b50344895003000050411004810f40198200696040c5400c40080c000000c00f10940030b04400340c19420f295003088003090384580711408099421000990000b1112181c044011001d0710030302900c80b044060700c2156104610041841d00b5001c91541c8440c0140315028007602150b045030310414040d07444004810008180341c10034081480181491603054aa1140050600d4072441e4400700007608031080e10394160b141d8901e54018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 92504793 1250 92503543 92503547
    0x30501140709060c140102041505030a1b0c020405061201020307030f050a1b111203011508100e011703121f08120d0c1110051509040807020907120e060106 68
    0x86a0072140c0c5280c0840414240500542208020680100100300503880a400b2260a41c151400b800e8041e8001401d001c1c00100182540c0040da113403030909141507030307244a460156600c00420400c03520b030440c54a2080c0c081000912000301402c0c0c0082202d8020404001c0a01c021441068036460006508203080448000c8501c0144040c1c4164a42113080e40e01081c0482013111413503440c0b405900140b5107524282c20042c1c0e01c40013021844000c000401d80d1014000c002c0388401c034542d07600201c1ea40310840182c400045128020030480c0400060141052280c0314910b0f5161017801c40349000103841445400003070032070316000c90f0029094501110b6100d11280b034020003204c4020700490f2040c003a074080e10301c501d00c0007200c015070340c1030181c40079806000c0c00d04884090030b0a8030b4044108035180c001a002c2112101c012120b040700507891842d00450450281c2c0c0c10100d0141000c0c0c02d60700b40302c0c802c070000d4244030600c4000b202441c4420b089009110500b61901c0160407554541040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 92506043 1250 92504793 92504831
    0x10507090e01030f0215040e0c03061503070c02060c01020403050303100509130803060d061e14010909030212160c09020408100207210e030d0e03060106090803030714090604030501 79
    0x1807403004814004101055106039102e5281d501140d001c0004004142d81040b54030455100303d078400c55140422800c4030084c0040c6104003015030311102000da00c5d040030201c81c4412a910004650002c0c101005070402c400607000d540080000103291035202d403a05851034100303d440c0340080291800900c9a4180300e00f100341c000031002c000740304103040c079900c0341454040141032034011110201000706101c515002690305034642d04120268141000f4200b018003081c1d20380c44050580c410000541104504c2425245a056800fa290316115511549a01e511000c2658415900399541c43d0104400c20190030050640d1074005036500c0c5040400f6040c103071418860306ca004d1040c040c400115442c00745502907160401d50181300100000829900404411700058043c4501014031032440c3c2c00c1000d41702d21610490480305660380c0d0300c034110740301e10141c09403400c20703042800403440490041c00f003541c40b01e19842c1400d062000e42804a1190341169000b51102ea4460314540d03015160946 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 92507293 1250 92506043 92506049
    0x3110d0b0a05010c02030d030b0301060e04080c070501020f07061d030715080f010302010e0607020109080d0c061103090307080310090903050901120b030303150301021201080f0607030c020c04180f030201050709 92
    0x345510b000149400190702d58a8030030007d403c0c141c60301d0034000350b80e4003940107402412003032540d03240f641000c1c00c22581c01e4114001da0f0415100307480006c07502e9800060042c04192542c402405428100441110741000302ca0019194a42c42c0d02034241554003070200390003070110782408032401c00031070600a1018401406540d02001c80c58018070260368000150311550805444d40c1c0d5494940d40300489081c2080e80c0002264007a01c800d00ba101c1d6442031002000502414090005000c000b00d240158801511078090941c02003100302c0000c0d41c0075029541c4500783c050012401d6594500b200e0075907124010803400110000f5200200e980c1007204000074905c80c050400a000300080825070320300c000703040b40c000c07500c0c240380c1240c2a5900750101da01c00002c1c500002d5881d41e44504c8140e944603070030b8444c0418010030000424581c07091280408180c02d40d8020810301081c40107004c001d20f4050450040b14031429500004110302030a4a055180b00b503000051600e40341340006c2103a05030390 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 92508543 1250 92507293 92507297
    0x303091501050d0204020f090405040c050f030606031c0c08190f020606010c17160602030403090803030c09041a030105040312050604020a02122511040b0402070b0f040303110d0b0a0501 81
    0x30014001d544445035941d203495419180180d86041c00b40c81c2e0b0480d405082d030000c1d40a42040104002c00201b00c4402040340e0081e10000c409414a00405480340c1c01140d055402d03a215079418866091010010724200d507050030801440e0889032503900b040d510001d8000843d40c40d401804400396440317282d940c1d02c1c440c5440605040e04006000810b0000c42c4c1201a0460030170920710500b054107942100c3d0721440c002c0b03806c0400c0c8100e00d0500082e4104650135008990042000a00100c012040381c3c410030411041914103680e9004210040054007150480f001081d00c035200d2070384091090502940c0290c46400505480c44a841c041e40c0e40105141e000d14014031902400a80000f0148105833044c0c8885440310541420010320801e002c1c5021400f01000b0b40b01ea040c0302408240180300c160944051003400b000e08180b00680c0b19a40006060b00014000202085402e000207a00b00f8030030b25000c070340320b6061581040d450b0010f807000072129a6509a4030034929109921034018072080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 92509793 1250 92508543 92508583
    0x30306030601050406060507031112040f050a0602010507050d05040303090b07030209040c14040e090a020a0f0e0f13020d02150a1815140703030207152c06011203020304090905030309 80
    0x4071b40b0040550044950040921100031045207050388180100403030443c3d042080c0c1c2d00c4039611fa00e0810640d070f41d441654003901c5c594102050b0984180911441040d40d078550714640a8005c2000d0001d0070000d0040c0e04160b540d55181001402c017807203042c00741c00305950151700e82915208100423170703034024605410301500d010100b280c1d250b0442030b40c1c05c5901b24046907083d555002001030820412910080d8400d01c90480400d00100c042c0480003521041022078802e540e55070021900c400d01903601d541c410240c806244010700d418445458060b03c081c1c490342c1039511001c060102500405040c40c00300c0e49250740c90b01180b0054540d50000c0401a040004e00c03240c2c800080d02903110f601e08007601e4000081c450090600a4044070000c0740d1203207025400c0300301168680c00500c6410322b0a42e0801880c010f214412540103000040e0710362250140500d0303480d0100b44d00c0b041c200031004800b0b41c0401d000004102c0b09610840c414980282c02540e038910f000700c1a64207100c8642050b030308204403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 92511043 1250 92509793 92509799
    0x13170307020a035a0c170f010e030f09012d020123130f05030406021f0207020a140d0f06020703020c19050f060720040f2702060906070302030306030601050406 70
    0x41907000010044d200885180c60004412070241e40704010000340060348040f2001406a41210f0800d0a0601e146e06403800030186001c02d5003a998450b14066680d803080c0607010100e101c1c00000c240d8584141000c41542a0b9115849503521000101511504541c20804607458080c0038200c0d47ca242800b000314900030801182c0507602016010b048002004454a0204600388411510564000b402c03a07454a50b241c400a5403801c3c0f1520a05c00500e0810713101703442148a0003501c42e80ca60061041403410b00f4444526101030001040b00d9009940c41c0140000c84d2000528400043c0562005640c603621400d000e440c1c8629100080d004503054070550f4001442158288190750003107a102041e07258081c00030300d403801804e501401c140c40000c10080352481c3d500c981010b00b0419103061200742c0302028801c00315180c494a40c2c1c5080c290248c980d07001e10402c418a01400d03c014001410400e83c2000b007080e5030001c074000c40259000105003d840c0c541044005d0050508031414407182d41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 92512293 1250 92511043 92511143
    0x30f090b04120f0b1006090e010b07110a0f030501051609050a0b1810020604030e0405070f0c06060305060c1b0613060207060902040e1f0213170307020a03 68
    0x3040b0310a50010001c09003509003044405100180000d41201c88220386003020251075003810783da840b401001c61441000010302c42000700c44079040b15682c030f85032424502107407200307128402000406940b104c100310011603030030000c0b09014041d60003140005001d182000e14505810f4000007036105202c804c000800440ea204802c81081c3d4484410550329140c2d1240c59580700942000380da0f034001014860100c80030780c0011007c0c46a0300030796034003170800b8088040c00300710b4000391401c0000652113203803021058050501c0c5881c6903c69400065010350301d4481f039050403c02e07035280f10340080000b4103000740d20300444001164000c0e0030140c000342c18035807001994480e024034010504c94004c915002440116840b00382d20031780181060100550400f102030b240d5402c00240b049125542010442d502c07002e109588a8881c1e940d1040303106401d09294282c00c0620b11003903001c1d880104170000060701c0c1c0030340c85002980b14903545907840c00c0f580041c0034258081516402d0289010b155041210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 92513543 1250 92512293 92512297
    0x513020f010c060f2306010e030d1103040e04030302030f01060216030b0705070611040918021008130606060302030105040c02011503230105130c050a0f1806091503030f090b 76
    0x40908065019845030701e42200a840382c0300b000c1103802d02d8485820303c641e07000caa005c032040c110007184090780e90f560310040d180784095515035501648a040a40241da000703219050424a080c4116810150350b980b9000d0600000c0b102140000d4000c82440300c00b200850f18540500402e0003d0407030b00e1b08080c01e0320f12500c002d04c4054000c5003103c0124044038024000c07980780c2d03500b001d004d0154281101c500c1e012540184100325a443c64000e410340240c480c100c140034050382c0107140c4c8210384112002128044070203812102c107010324500d0040010442d01c83c640c0204880e44000d0307141d614240c03c01045a88081d045000d59052011001c003480a03100c0e48020f4a5201c00ca156401c503041501c100340c0f1f081c401201d0a19807070081404540a01540380300c0b01d6030b2098920f503000c1500d601c140b0014502c00d100754400000d040100f407040040c0d4960300100049590300c0055107e03030b03c08004068444025a91542104500b0107009059100c001c101030304155007020f000c11031405042c00142c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 92514793 1250 92513543 92513569
    0x30507050306090a030e220903020c041505060706140f1909240f060f05090108030408070603020306030309150304050723011206050d0b091c053712051302 68
    0x36441d100840c16651f021034851001c400400213440904502d46110300511110409038090f10500d8040441443e01d4003560115080241c0320708c0c101450207040c0722460300418821101240c54040c0d510300e08a03840242e510448820f905a61a03080c80d450070050745a07552002240306041c94244070110b01d81840b520043c80d20404928004054658490700800c2c80c100c07480c0c0c210f0f042400003c1c0d020340c150140c0d401d403181202c400c3c0559983d0801c8070f5807407240c0e104104482e04558403c21149020342d01071684690040c1c103803407604624200298100168036691402803c01001384010701000300a100090589902c81c000054031489a00258600000c0303840e040000b400c152105a4459401c014010500500325020384003c41c5402903500380100c4140a0321701c10403c06040c02c1c9442070000d4036070802a15041e1038800700e0401e00c0407a20071a6031108804100d40011000c110310b188041605184c2540c403a0300d10612500c5242c140d8001030080c43c2c0c050a050160f40250b84e07461152424 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 92516043 1250 92514793 92514797
    0x6040309080c01171008030d0e010e03040f05060711030102070b0702150402012a0b10030218040201051e072a06020601180903020708011514061c0c17040507030507050306090a03 78
    0x55641c4001388000505c005800c0407141d80030102e542e4664a50541140034030320803040082c8600180354215036582d000700d118960007180350a00400c46030074000e0003850141d009010481e1003500e540013082c2681c1c0001c0088400c4481c034020031008560510190b041c908410050000c2820980c00080c0f410041d4a1620030022180d2060039100030540d4038107100542c80b6000100b1841c01210031200940f0900c4281d00070038a2090150f21440c040e40304138807556058450303a06019070a00a092800c0020030903030742d0072a080109101190405c0c054080d40c01070902c910303083c0700251040001411081d84100b041d9404000180254620701803c610301650360400050070f844941022454603d00380e1200300c10b941b0b010448030707407031003183c0101043c0c6500308822110300d00c0b07035000e211192103011401aa0703100c2da80d218000c080440e40008492461030725001c171140c0b440110740310a9031b50540342122243d000007010010004284080002420200e01a108920303101c1c00e00d03500c1c1c040e0b18a006003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 92517293 1250 92516043 92516087
    0x105011107030209070c02030601080a02090c19030b0402120f0103060e0c03030f03070302040f06050307021606020c130204050a0e040b0c090117060d08040e07022506080a0f0e06040309080c01 84
    0x807a44030310300516440d87c00800710303881035944100c00e44d01d8410240080e40a03002d620001200ba4a0002c125552240c1089804d101c201d4441011401062801c0305e0590050b02041994200b5600300c02c1e103400340101d11480d2401e54554540b0800326070360321800c201c0782e0304818411003003568044141c49071030482d00c243c556a55294602140240301c0c2d0381100e540340010010105e880380d809806140700704403c0e001c80711184600c1d0054280384034140304003801640022170380e01140c00d201c0c2000c00d111043c200b01504046c0ca944c0000c5040b401d68220b80102c0000104000a008000908640181d01c2e20840703854801128002445030104d6901d1040003201540411010f803070304070b1594289500000781c191a1078880703034a0860040203403174440042c881d6004a200310809101c020558804408840c00c85900c0c007401502c0c2488000c1400001c0d40c1d41e0078500755240c007a80210038010640300040d0840c0d252074680030b44039003416040841d103540000303020300c60351344c10880051040c0c021608400c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 92518543 1250 92517293 92517301
    0x1f0801110a0507150213080f0304050a060e1909290a0501050f040f0308090103050702060105060a031d072903010e0f040f050a0303020903070506090a090c020f010e060f0105011107030209 82
    0x2210404c1e90310100365500d100040c80c0c014001030081002c00c1d2850031041d074005543c1c004000f50b990041c0d0052641c48850b0020811030580940d842c8400003c0180150360104a102c1e07400a16560540c40080c400c0d0700c1352200c0902040d80074101c09119506140741c02881c1001021a220107011f001d0700c0c1c107011002502c0c481e01080a025540140300140381c410340e0b07544914200c20355401801201e4086400e207004034140b41d0022034000c0c141e0780c02070300c01414220309010840c0508000c1c030000485480000003030b0040c0c075080c403442c0040c1025082c244d0b035408003071f800070034104140c41542100c0081030005010120714024095040340441c0d108000304e0322a070900c0b59110181000041851041c440c401c4209501074000d098000780440544000c0d907501c9060000d2403045004007076010502180501031500c0c294441c2100b5113052040300c0b07650040c10206805c4604110303001049600071340030400d6076040d481c8039a002d03200a18101040d44d5190641c250750701c02501000344039100700310000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 92519793 1250 92518543 92518553
    0x50d05100c030f06091817040f080a0c0b04060203031303050f180909010c020a0609050a08070606151b170d021c050a0b060d0e10051f0801110a0507 65
    0x20300203030a0000010000e2a80592014000340304844461401c2414030000007070700034452080b20000071400045c2c000b840140e5844c100e441462036034054920310107100128840c1c03007800d400b4018015100042c4410100c5040900b41036a95030302c5140001c030100800e000c5c5035808020390b45c00500b4000641c51b1800c1c1803805941c0ba02032030b5070f254605240411100700c03a07044034081c8002440203652031600c6440d0175000c1350130303508042540000b40c1d00c203000c0e0100084695000e82822070203102654215981551503c409038000c0c14103680081d202c0ea000d000c00c107568a5000814100350404481d5180b0001c41e00e20f81c040c66190103802d01500c1403e0a41c0d444080e03003240c0703045070030303407002c5684040100550501d11602e005805d400382ca00000916004c0040c40350000a0800800003030404660301d55074406400d42c1031443d100c3d8050710000700e00d00000c50044502510030088400c160480e0b0303040745a1000400d074803500d0584e0418485403030400c12030007168207503111490b000d40e4450081c203103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 92521043 1250 92519793 92519803
    0x60c02030307060c05130e130206180d0302030304030f090e010509100b0a05120109020405180a02070602070b011d040206030a18020303070807200f06030402030c131b03060f050d05 79
    0x2014001908000e1200307036042c1c1c8540188000301b82c0706079850006486650035801103d045584043c8030b5030560400d0090b2800c5006040e00700b14480c0c0d8251414190408128500505001100540d0021081c07004260304218071065900341c2d031900d0308000785004440d001802c410b115090240003074130082071100403154220805406000e2a0680c4d41c0e0b00980000c00075403101c0c03d0a0725080c0075800100f010007080c02141c0c11282d0080214800e007407050040b2000c00c401800d007100d040d60030464140040c0c0140050040240a10044066980340c8410420034075401642d038000401424104401a2744850640e030300580ca101c8002036400904000d4a1040c010004c00fa515110109481003044406002081c031a4801d9464040300e00607402a4940740d01200e6200342c0c0b0501880c922415424032101840d4024002030407100400704a4001c61b800d43c0031a10304150395501d07601c29142c80020307c14100004202450108661450401e000840c1e04040c05100e116141100f81c0c0e40030b00004104d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 92522293 1250 92521043 92521057
    0x5040209070c14010e03030a0f2f041206090215031b030901060305150103050d02120a0c0c030204020d09110d020105070f05120d0204140d0b0a050711030c0102070203010b030303060a060c020303 85
    0x20081c10a80c1c08269640e5001254801203072030800c4400e0591100501072120313081c01980803c2d022b84480d00d0503040c090454003a40b812041c041c403002424900405040640c07a005203c00220300510f80180310185c140c9a9102c41450b90400c1400b002c01080b0502170701e11600c800c40c2e00d859480303140d8824050012031744060315502c1200725041d40324404521007412207104101303c69040039401800d0782c07940c0d0b400540803030b1800107105142d030213401040000c54080c442d5544c240e0460b01c179400074080f40c003c4461700412981e0f95828000f045080c0441440c00710040794009040000313580024014410760f00c0081505080742c020000300241009259105c200c00c0b40001c3c2c0716080c20a05500a42091150012140c03180880501c18200b14031070600031a0080400c805681d0744100f9840601800350284d400c10542c4149200111000d2020b042c0c03000c0072000160713442d81980101800c2d0360865002e184a5042041409030f90b590f0103502004a5105081000e0020300900019086005100b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 92523543 1250 92522293 92522333
    0x712140c0f0f01050106030b0a03150626010c08010f030f020f03060f1519090c0207170a150b031f11030f071b32030f0a110105040209070c 61
    0x4036005070184404110b800d00194003500070402caa03686c000441c10f64407010002e03500052005001c1c1b01084070701c1a14442004544008100e071607035030010840d944d01c400d04a2110307403682c205241c0814001c2c020036003200034610708440c0c15410524a40d1040720b80788001491004120380722400c540321a480200090780080a44030340e031800300f040d180741e400c0440347c801d407050149440c55024034200b803074104540703408044800050305008420004040c10018002584900000011032561102d4101001203841018007200b420a01e003101c111044030280d942d58038201a851300603030300c0c001480442c2d894925410005001d0f00031640000f01800c090040c4100400020403810300740108003140601e40a07030741c1e40104c040b0070591900000100030300902074400e8045c0680c2519031040718810300d2140680c02c40da075060401e21680743d64032a004051107604041070001510b600846a40212207000c0000c0c421490541d002881c40301c0001c0600d424403106812043c1445409060941050008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 92524793 1250 92523543 92523553
    0x204110d050117070e060603090a0213060815090a06111b0a030807030902011d060f0403060c080106020a0c030303270c0512151503150a020702040605060712140c 71
    0x4080c000e030180009009202196840c00300300040d6800029180084990000210107180c036110308020702d603031019006080910075202c002d80960745480e05101800c0c400c0e0400120b00d480d1862080c00d05511404580c14500000100140742c000425420185a400840041c00b168008030300340345409004500c500340c0c801000100f9907000005000c44085010317488100c07150b07035621800c80603126040d4000740001d60121414100d89070010419200c82e40c0103110a050600034a07410700c1c01d4100354070642d0350b00e440e40b28a1000c2034124010501400e00b03440031340b114200c151111020b824061200030201590f410710200081894101c0850b1900c6111702e00003901c407603003840c0304608a940202403184500c13464545910b2800030321091000c014440c28030043e6600c101c454250b02c81c2030102501409881c40180030912019031081c407812030180c0c0182c40e00b00500500080f5400e60300800d010701c60402c28000420b01d5460000102403051810240f8180380320313522121070040d01040302c07461144c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 92526043 1250 92524793 92524807
    0x1a040806090a05190305090d02030102160609120e10080c1306020a110a050315151f08010603021e1602091005040b030303010b09010c050c09180610180207020411 71
    0xc0840c4103002d440c00f0b041221040c00300a551800c8107020304000a010801c01c000c5003050b400c00c4a642c0d401140010300040c10320119000d540d24119881c0e02c119680c0f55a4035003102044503611080d8500040380c0341041070202074501141d031103031030500100203100b4030900040b4002d60080848000c14406d2081da501d5a94601000e5a0740c2600d80013116000d00c0007414105900b00020b00c0c108998000700141444000c07000c85448206001d0441440d20001c05030159a030348a150071486401a40c0d101c0030710384070004000810b10303001078110700d041500400c81d0281481130200507940781103030780420f41da4a0207400d0408203001203a4200030740041d00c2ca0704011000c02050044000c85500351420312090b0701010815807280300900903c0c02005040c414100154402e107115160325100c0c00440d464060080300107048020111403c04007121403040140c0e100f031007072140329041800c5100d011029410714500c03000c402038082d410b44100f5804250312065503580d801c824543c01c4620350640e42c43d01c0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 92527293 1250 92526043 92526061
    0x80c1c0504081c0905040e15040c0e0c03070503040308090c0306040605090705040e06010b070309090e01020406030f020910081e1006021501060518040f05150a05010201090302071a040806 82
    0x1074442c034442400303501201450034150408009100710a50740d4025460f060000b08001015509000130152007098501c01d0101607105501d03021b1401007086c212614645114010141310042800c00041d4007401800389285c0c003c2c09803604554035042140d81a590f1058851404621480d080d9140c0304200a0105100c0140c0c499400390b103144058400d81c5031240103000941c0c4070fa210a4149a000000400080c04007002510319907100f032402c4d220040e5074191420a560030203015003690b0354001800c204c0c05406109a0f0750644c0048400d608080e030400c0011155103100d10714000340411040013a10445484840003007415058040503500c0c201248025100c04141c05003802520500d0362200300d10180406250403140360380d030740f946010a0034100c040c482c90840744140e005619400c1c3d0388400c0d080c500509e44036800382000b002d000c68400e400c024030b44640741c0c401d5040d64580041100881e50103d0721009075094030000004c14980403130742d0207076813040b64040440342c010b0205200b2165 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 92528543 1250 92527293 92527297
    0x50c1504050c030304180e16030b19140402010f031104032d05030a0f0203040518070e0a060c14070306090803041b0b090f01030905061503190b04080c1c05 68
    0x107405a4100d40010620030706040c0d403440740d80034148800c2e40f5141c041d10310404a404c5034004a1030007090344c064000030b0111900c00781043d041141c0c9034414004000000510080c0001b4003160038600740410300200342180c030140f201610107410450450300005c01c03030b4005d4100243d25607040b901142d4440e500d0601c04480c0f0840403c07040306040540c41e4028081074a410981040c1d041000b851400b03407490800d4402c1c0401031454019804180701c0000c1560380d24100c1c29000e10142214034841c6043c4400070800400c3d012040d109600b042001d000042d030001080c1072055200c0d80c071415003004e03010f4240c51720320564070003840c40e41046050010481c000d0040c5000718480c43c030501080360340c8c041e904201d10150094207070180e020322112406141603801c0c2c0b0b01200c418100000c0411945e00c0311800c010003103c20b1048a0a96007002c840b500341004101c410820107030000da0400c0c019612140050350141019000480c081060b5040300c0080c040c100c1c4015991454081080b55646c0c0a0055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 92529793 1250 92528543 92528551
    0x203070b0d09020a0b03061020060a060e0601030c0e04110d09030c2009520206060603040b0c0c06090a020103050a0b090a021e03041a0601090f030b0403050c15 70
    0x50301101d500040c072141c00c441a2030052030000c100c8d03aa034424a483c200c4004898001e0000305018803801801c00c03020a001c2c4900409414102003005130a0809501c501c03840544100d040601d0a40802d41542c2c1c0102034000c4141e04527408101000004c820f040c49000d0350b60003034030080c42e140029082642101d0744140c1c2c03034454040c6070f4655511030012495112032211468000e60380d600042e02446482d14010850462010f80b840074010b0758410310100c1c0944003a00c0100f011409144250b200c9250140c44140d0310392006050304d02d000c401107006404007904c000c20b01074890000ca01400d240006031070800c404c01c2c046503440c1c0b4101c91042d80d11841000140d010910b0000443e0151442d80144e810040d0082c180c4d078059141c10785502d00a602004503400a008280c03940c0c503103101c40100541c001e174081d06154860000d1004941d1840d036000c0d16490500c01140c10030803080c103801500300122900440081c41a80d51800c0c150784031310503c088061140604d0743c2e03c00040700482083c0d401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 92531043 1250 92529793 92529799
    0x1201050a0e01030b13151409100606020717070e070503070311070f030e0a0510050702090901181502130b130501051e1b070602030705010f1a0108040203070b0d0902 72
    0x3040303564100c0c06154107001c0c00007809040b01600000c0d14030610964200083e840307200c05617540c4201500d408110380c81442211040311800b414085401400c01c2454800f42c41e070344c82080703038516050004c0c0da00c510520507590031010b2001070a481c0801400600c004140208181245107044213005103540d004450b28404203181812035000712040c0b07815138903400c0d030100090400c0d22079510b0617079071004500790040d80000e0180c408203482e180c5001072035840e01c60b600e41e503842d20418410400441001040c18000307a1420110842c214030b0100c26002650300549150201d92008044130082d01c11000d21481001c1444800656428504000d1030b071480460651101203444100445041c40f881042e800d010f0f0a00100c0340c2c40310b2425006084070807855202030100011070b40d80505003c0564440e601582010a9500900100307010701c111403400c00004102070340c00c00c0c41b003071680e50040501702d04102d540ba00040464404000000c003601c1c0803a5150f4407040b1a80182c80503050104040740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 92532293 1250 92531043 92531059
    0xb0d03140c06042301060605040302040b120708010f050c070b0103021507060c05030106020f1225060c0503060910060c03030e1504050f0d050403021806060f070b220c06030203060a030602120105 85
    0xf11a2810301c900c00641f2103e95400c3d1415140d070302000013400c55407024541c84032a920300c607400710303808000647c02410144004078503100003845660407103100912056030f89100b040560001118440071505591741207031051071400b100070000702c00c1d02800000030441c07441d104401c440300341c1000155040f2507080e8200d88002c4004081c02342c452900140040e82c041091002c46a00d0300c3c00b040070483c8005000d0f00081e105000d4880d01e083d50880c41c55a4041500003003401868101890340d194041401ca030500881441c1004c001c10750041404064209981c510a1143d078000a00c101d102000306848210a60306260900e00e4568003c031009140d24440c00100a4404d4080e00c1501c085a80003059102d0180d411507000d651880014a0b40da0301450811900318241d9012003e050003074043c4100c3d14051500713402030a450002000205003100300350312800001008001c5c5041554407074030300540c40e0780b07501011a0300206282c000500d0701d0b0011401c6190390441e400da550490347e0842e2242 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 92533543 1250 92532293 92532353
    0xc0e0703020a080610030b031603140a12120207020910080601061b171908010305070f0b03072a0602070501270b060a0506031f08010b0d03140c0604 65
    0x240072480b641c246807010030310b00070000740c4901d01010707507058405550602242500c62200000c0c18900240c81084868000701800d00611080d5500035194805c2000107014000306620b452a445c441d6024910411950051044d54400560142d8050b0740d40580f210f6690700f860103101c5c080f072100d40611034a1b44210000050076034400c803901013100c0b40d01e1020b8204658161503012408512070485070214a040048180d03d0410040807030021076a940c2c2c410b107550451400c641003001e9940402814a0100c0042c440c0c2c000b0711081325004082401c08042e008042060b9601c021168082c05d04240381c0c040805044c419250001c0402c07a1080c002040155a50071910080c00d61526034110900d00102e901d00c00a50700e203844c0d0b604443c004003401c2d0519034800004840ba4803c032000b4001020100c850807407018602c9483c8c000d085140001c0c800e603800400840da000070001c202030100244510584141c50101003141ca1180c1e440d41910250b140504140d000500090175070204494085042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 92534793 1250 92533543 92533547
    0x9010b030f060a051e0301020f1201031401090305030a02130b0c01090209100303080403050307030b1504060f0f210603020d0303020909070c030512060f040f060f0605041a03090a0f0c0e07 82
    0x2a81c04d03500010710000900b43d42d50300040040006a034155090740d801c210303c40343c200314030000d00919268020040c00542c1180380800c20244140c52620b4203a04004204002079005030950350b202404003c0103884801840720707600000603a5116030b55040c0d0014442d03694401c1900006207050099480b601941c46414100207a400584409800941d00402050001c0c0c8540c000f1a0032060754034000c901210345030001190807c240700c4602d800040000c1c10461507400240750500c0c0030603820107242103141e0010103002c107042e040200b001003107141b0000700e04003243e0740000c0c0a190040c0c01418845298a8050000d43c01040c445104a80d00d000040f96030b4459805030300d000394980e851030f0a101d90325010004449006e091170740d101510101346c03811500c1310303c121980e208807614041031141c5444034a84650000b070b0088810030608110501000000709514040c0180341140581d403603031141c070682c1c00e0031062040140b40407008000b0b101482507017030103901518000c4402e00b80b243c5400e641 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 92536043 1250 92534793 92534809
    0x4050610081209010c021201060b0901200c120f10020706110a170a0905160306180807171b0102030709050904030804030f020708010c030f0c091a071109010b030f06 72
    0x18840c5810700f040b40125651041c0e841e01034040c805411805450307003015840382034034402e40000003440d0010508040703a60f403141629070360f4010204201d642e400d4200c8401e8440d01c90400f164001c5c00285121030300401c0400000400440b1001034988140c000d5035200080c1d400b10340c050b252541400900284090a0310466070680c019445189500002e100c0e41c6001c0c0c08011711400f101c990351842c10300480e100b800300c0081d0641c641000444c10741980750020486a501d001d500440c007151440b007000174401d000f10782210b50803088141340d60350040f07100c0111b442580310003510401c0d0420300d2090b000054024601070091500c84a8203035072540e00307104940c101100d020f4006120075012601007405540b108174680c8403032050342c1d0202d80389c0b40002d0a56180b1074020000075621260821850704c3c620601809038030616107040445e01d000420b10144510030308100701d8810000c1c0c207404110702111f09000c060800b41c011801584e4980050f901078100706c80900c513414403803001443c24034081039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 92537293 1250 92536043 92536063
    0x1050405030d03090515070e04060e0613020706060b041805150d0f020a051203070302060603060108031c0b132c070b0a1107030c060f110709090809090405061008 71
    0x4100c9444148011805084501e4094070b542c0548102250b1b5040b42c001c0d030a104100326156070442d0070540052000720340140e84040401032010045c40718942d58205c1e0045e8035001d0480260719401a802c21100500d0310364014081040000b4000880800d25a420174602d08401420410b0360f55504480d654441c030b890007107a1106100102c600003840c4080b2038000d89001400341e41405448401040b40700300d0702c08126030b0070b50011403560200b5504001d100d5115030140d0150016501d40303c0c440d6a280546040000c0b02c8403a840b0609048070603500000940c01d00030000741981c0b844004031001408041c0400c035804008451140c0c0c1030381d190009000c244825401006001c0c50401f910115821900c0450304010b100c80903011071220800000c0d0186018480b8000014074204000d4080007803401d4035018804194004a50140d0101c0d007101141e4605001040d444100d01e010304440c851015241e5005d4086014441444400070341c09102e43c0c0340201d6440e50603103c1c4001c42c0d85001103d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 92538543 1250 92537293 92537299
    0x60303040501031e0c050d060b040503030d05090a0c0e040c12050c0f04021209010b030c090f01210501090501140702010b060313020406121505070f0806090c0d0e0102090f01050405 79
    0x4200442c2d440307130380032150f150000000c064403820090441420b0f100c2d101c14290004201045802040c0180e224000080000020091a051400d80403e407070340600c6001c02c1006a8038000034001d00d00034030421500c164499207060f0060f480b110301101c030507400e842c250761032038141350023060b980e0500c220b08604907048802050141b508500b08100c1c2c400c200b1603190010340078030101c10101840c810042c0500c1d48040007040c480303800402c7c14580003400300b007240314180000510010400704040d00b8150350400a00c076031401e441c20343c015000f50040a000302958078004c1030ba0103100040d400401d040d5011110102c00703840b41d0130700728241c40c2400f0500303920803010800314240a0305051168200761026201180103940c1f5280310b24000c0d4010815203a076003401c071108461401c01e00c40e8035440b52150404034004003020000a04240e40149031a025082e1200407405100e8040d042d50b0019034924024001c0d640c4050125010b074100707180085c003849615000004a41c01502036506855020f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 92539793 1250 92538543 92538547
    0x90e070608091e010605031b04050a0504080f0306150f0306010216180509120406050408070b13030303092a030302060c04150c0c050604030602040e06040c0906030c050c060115120203060303 83
    0x1a0300c0807103c0d001508031000e80d640c0c03034800041d5130302c0501041903808005190308110b441014180401e0302c000400d000d000720301d824208000034031507034103813102c206440c020701ea286e90b60400400c1e800d80800021510034030010440f5459685040001d51094000ba801e0b20110307508400481c407280c142e80031781c80c624601900c0c010100541d590156902c001c01104039250280003c2101c415a841307500810002100050b0900103017104120300c4009104c0010001d150001280c0701ca06541010b0200404140e104c08a01041c4611700e030036034008248a40b601c2c0111409040c1707800d100c0304144000c41c00b40c09480009040e018001007039804840c2c00f180680103c80656404540d0300c2d1010310110740e0b03043d01d202e0101b0300303844510103840614400c51005a4603400c0c00c05000b1990310081c0114440c40c02d0066582000340d0160118007107810030f00f004141d00c60074003420360321070082101c08200c80c852000000740d01d490352000200340c90181e8403050264142c844040c0160700c0100e034607503090303401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 92541043 1250 92539793 92539813
    0x30a020702010c0b0a05090708060c0904050a240f05060f0702120304170102040f14010e0103020d0609020c060106080f1302010c02060d021204030306050d020306040b1302030304090e07060809 84
    0x94005059a500c14540f0302c0031041c0c681d80c0c401c01c81d5001c0d500c00d280c2a9441c820055100410820386d006800154001c0000740381c0a0f0852109110302e00d40103004913100d00100d80e4080450f0031042c01400b100c070303804095002024445007090382c280f0801901c40028200011141004400c83c1c04844104280c1c6180050607001d11140c02513502228100b0f1004000c000781c003498030340c206548040031a00142c3d0b294604208551035607400d07040300b5070307100d603440c034a281e240e801441d01d442c090001c5c03c000d6113500c5000c440784014a030310b5100110b01400003808400010340402e000741610039070340794000075132240c1503c841020011110752503180c41442c8000050760081c55020b4035144020402407802007090180003d0340c2025140a9414203e80e040c001095090300403c03000e40416a03030140702c01c0a54002035074a03013014201504643c4214089805015402c2c0c0c0079080d95000780450f540c560b0b0314000c0704000c00400b8842d0310320f07006050010880310720440105008020b190002d20198070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 92542293 1250 92541043 92541061
    0x1506120207050a02030f0a02031204080d03111309020d230114030a06020d050618091002030901090602040f03150501030807030806030c0405090d110613030f2a021201060b03 76
    0x409800d0a40d20b03071182000c1ea00050390208840380c44005508082e298058052040c03502d80603859500b00c040d05000c0c0010320005200003103110990b4850f140104850300c8416800c00300d489007228030700c40700920480100b00003450360002c02045617000410020f4180501d20140c450019581d80a0030801101c01000031081a4200303100070f120050550b850b0742c03110b5480030101c0c0c1c41401d00c020845d4807a0104290351420108220145800f03241c0030000d850100e40c0141c90f400b1411260034484d901001151001c1025400351400c960702000c1196640d8480501a4524040b0702c4211071602c030b803464000540700f45006260490f9880030885007404d150b603500b03903800107000744042d07050711036401c010640d80c2e1940203c5000724a0100a029400d080407402071013058121a00710307281e8000304c244018440040340c00700300940c15280c04901c40040400072652015400c81c81d00d20200c00d4203640d41c00802e80401c1c1c0801620840b091090801c00401d198265800f500ca0103207851000d10002e04954 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 92543543 1250 92542293 92542297
    0x806040204050a05011115041401050711032505030d1e09170a05130e0a0b010315031b15031a030a2609030604060b0405010e0f01230d050109030315061202 68
    0x804441b01f610030700b2040d8161001d401704103d5060703941628209100030581406c1c031030b1035001000d510301210006058022940c1d0f030710800017032024041d00b851200041d1190b268903106440d0b400300030380707664014080843c006072900e062410100449a221109482d4a074400c401105a0002302c0f000d184825240a60180e04400140400d0080420013508201618100b12014008442480c140c0d1304201c24250201c3d41604940d074103041c40c00c0641e00302d00c0c036446084030840764490701755140c84810702d00c510344e1100c40d5030082d5490a814440341d20603503015003002004a00c41c1e2010948030b2030082c10107590750680d101c06410010861b00e01e08003041c4010020b400010260012482c140103c00824a000e000315010380700296a5840c600280ca09400340c0d5004001d24010b0b80b44a04045155240c0002c040c0314200c855200a003449002c488401d61034070f1011001402420760518508189000c0c0c900c1641c1100040d00e0002802d000f0844000c11000355103055807803114405c81c00c00200025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 92544793 1250 92543543 92543567
    0x30a06080d140a03180b0a05130f0206070807020603091b011d1002070b04030f0b1008060705030907030204060806070f02062205070807120501152409050603070c030806040204050a0501 81
    0x40d00c41c03100840130525800c5c010196440f88600b101d10746411803141c0203d80002d841111800c2e01e00d001c0d1804102491003103816a034040b560f0694034030140c54820220700c61040001d4005502004201800801040910780149040c124484402041004403181005502030780c4000c2080094201d8506100c030744100740c5610b50045403034264503003040d03803519041030f441120400070400800c400c100f0905440d540048031b03612201f020350700300302c2103580b82c0c0070082108007040000b1001813501c0c2010000c0400445e00500100140d5448507502d40d06d0340002c0711170801044948d030009072441c0c80001c0443c030070800719240c4003c44c41c4034607500ea4001380802065031706205091000c511003006000700002400b240030400c0c070f001003914190b801d507544126581081200f002e02000f08500c00560010000c1542c40b82c2019150300b51010b0312008060381080c0d403c080040300300841550000c0034090564041d840b582d88596840c030400c8142c0c40f481c040d1903000807000404001c5940140700c64211 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 92546043 1250 92544793 92544797
    0x1c0f030902030a170c16060c030c1e060506030c0108070f0e0402040b03090307020307060302090906040506120601090c1d0d140f061302040515280305060c030a06080d140a 75
    0x10404141c603030341d0042c0e0307200400380140c130f9000a030742003d00700c2001a440014401c110304a480382c6805c80240c0b60080c540d10290603c00c118080d0710812026941f405160781910102c2000041d0504101d0000e08048900c01e000e0712508500d00c030103601139111507228810590301c0405010100f181203e01340103250600703802a800344004208400314201a40c0f041c0c5030303031000303544884940c0105442d04506600c07000a061040201003080d0322980d48081d070002c0b0540b00480c00303031940804524000140d0800121702e005000c00811001540d800910580302c8581e40c031003a00351652001c40000368141034031ba911428000345031001501000e071000c001c510f0002501c4031100740400c1582040c40c1107816501d41d101c513140d21000c5140c6803081d5a00941d22148036035070b070030ba50700110300450340d49803032800e0040345d460034100884515040c08005c1c59201050326000e082200c48400c1300d0b001917031005c40320781c182100410268400503105c00307689842c0d5100711500540900381c00c450391040c204102 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 92547293 1250 92546043 92546053
    0xb0103020f040b0d1101080708250507080703030902040e0312040b04140d020703020a0b0a0507020d0204020405061209071a070f03090b04060c0b07020c030703060b031e0307051c0f03090203 83
    0x4041d51224600f58441d4019440166040d81405c001082c1030401030401d410300c0000001e1194201c4550240064100c1e0050784400030b40c8c40a0054815004800000348203290000c0e00c2410107a158000703091149c400ea400b03201142039194044c2c1c4902440100c0d400001400380080d000c41d42070810560041d006060f000b400b0020b0103142400e02c041000148092307230040c07034100214140540510020a0300c803590074100416070400500e14401c1d04000b0344100c20b500150307800d45d035076039040310000c01c801442c0b2581d880301c90406004c44c101c11114554140a007020002c0c18014903112b40c0e24480384810b601e442c120b1039039200d039408030300c1242c29000c0003451503020440050001c02800070705545c0c0c484c1c00340395003180b034518009400103000000b19082540d1031b211540b40001c043c000c2c0d039070001c0c010075080c070301c400428500440c1000d10070740c01c3c03010a80c0004c1000088020a0407502400640d40082900b83e007005020741c8d0303502e00d00d0006031503522a10303001e803199011041442c4001e090b0b034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 92548543 1250 92547293 92547311
    0x405010f0b0717070503030f0f090313051207090204060f030b0d050606060f070206040b030406290d05150705070302120405090604020304050c0d08030718080604060209360a05040b0103020f04 84
    0x3610b1a00101c230850220350704242884041c40f00008040d40c40121403008510f081100c14134010020060301c0358601a01080f400304c0031404081c8030b074201601e6058421900c50b90f980800038440010841c000e4003007460031020303440c5801e084036420801504040141180e4a4039000d120043d480a050345100b000144103803801652244014001840e00946080d00c90516040c0003044500798110a81c3c0c010b4603094646d42041038a0180705100b0089807007015443c0c0f241411402c2c00b41540700400081da0b580200310415030400041c06d05580240d0840d1054007054920482603c2640107155102d890078000440b21f10f0950002c5910900c210151a00707813508001140d10100ca00f00c00729200c0c100441000100e030342c44036880c15640010541212142e103840700c0c1030345528018002a00f1a0b40001c0d0014554981c101358014030003031514003c0c0b54914454540309c14282c1c1c841011030544001d00499000403460003a81e000741e801820801181e461982001280c2686003480b5400684600d416 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 92549793 1250 92548543 92548553
    0x5030705070605040b040c14010e0108060a0306090c0603050705030c030a0b01050904050703060314070605070f0c0e0103050303091b061804060f0b070506060d0312050403020703060509010b0405010f0b071707 91
    0x2050045224179507540c2141402e1501805184180d040080622008990840c6680c0c9c891141407060b07101782000c11b80f648400300272601082d03941c0c01c003a05407410a090401081b0382e0040120840d10306035000c01c00364503200d500725068481503499003d444021b102240c05000c0c0c5510010b001441414294608002c000103e81943d400303d030340c1070100ea91801d040060080040c03104003032944d07a0000d000c4060078188082c00c41c1c0180b4501400307101e020741d1940c0c01c000150325807501404000001010382d6a603403030015981d6108640481c0a4081c402c081070464800788a0a40480001000300e41002c032422144440034140e103856030340c440e8444400003100c005014209020300042d2000903a0f075451170030700b075142020203800c080c0102d081d0461200441e40c40300c41d241000c51400804603a0307440b50705089191007201d4001900180c503103811701c1044030056012000300042602d083c40355070390314503514291400c0d0307104a08020f4010040f400024021006041c080c2ca5500e0021341403150588035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 92551043 1250 92549793 92549801
    0x1020a110607060609091401020f07030e030307050f240423010b06030a021308060f1902040302090f09010c111e01290108010f030c06030905010b03011a011b12050307050706 76
    0x70443c41151b90703d0f444030a2080b40c2d0a840f5103016004000e6240000148284c4000d100c0c1c1d200c05010003024038090707515a41c0c103208036036074070741c00c01d081315000329100c0802a105d104801c144101107016603000c0000e0821902c0c80f5101e55004218506038292414080c9100e0030b01641c107691a55035030544031803555580c4007941c0141d03400d980040e25600c45e00804540c91a06400041c1554800e2040002d04448034805541c040c1e20851102c4804d101c08948201038005c9801c0250b002100408000a8055408045115001e20b0b0f000307119061449a00741c440a4030102403040135001040c6032a11741103480207140421103036200010b40c854020034803114592444c403012844156001200800350b81c00748030310340134100c200c102405107031555440035050301c1c0a1041c02e040c1503c412105090203070a41c8290001d40014009000b403180244174204240703213039070030780340402c03080f11401c5829941213070030081099010014400d910610741c815a80c2d03170002800c01e001c1010402c100ca0014401d409 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 92552293 1250 92551043 92551049
    0x4020f0d06241b0602070f0503040b1e090d0201110717060901060b0a05040909020f06030f0402101805091b070503040510050c0c130b040905070519030201020a1106070606 75
    0x2428404601030309428002081c4602c014504018041c1100758402440054800301e10380d0110005980f010103103401c18180c2d8818101030440d010110300003903801c00d000c008041d0200228411350780040040001c04940c01076240e069000340460f04201c2c019405201240a02d04402044a081c6175a406d00c03e000c003d00c00c070240032a9005a030912004460074080c0102030506800c0042c10031161000080490240d40b00d6140b00b15111250340c015921a0304010030281d4020301569900d142880c003414800070140e900f00e0084459221980b1001e1280c2c4181d410a071500d4031010740c40d85014200a51441c0c003400058000389120102600700d926440140071251050000c1d5880303d203000304118485400440d22800d0110800900c5407a090101d240d20041c041168103241d4504203409010040c200050343e160428986200b000c2800030010301c2c01d007140e100700d40d03c0c130f08201909040c4400b442e00303200081c0968099403403140005c0b5949552407669130050440c0b800c08400ea2a030700306603152a8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 92553543 1250 92552293 92552309
    0xf0d030203070605070908060f0703020906030406090c0e13060f0e0a150605011404061b0c270603020f0607050c040203040c030b090a03080106050a03060f1e1202030c04020f0d06 78
    0x1041c50420405000b04c982c082c9040c1040040c4510f820034444d00c5100040c002c01540b034801c4002013626000b0f5041c0c507800c130009000d450312480c180c84c10400030000601d05698104482c500028103840006189200c0c60f03e0314510801d400351642e6110103020030700c50070b08055481c2c03100c1454110040000b0740c0164050110000156030b410640d008440090300401d040045518088490340c0c0707228101c60440d0524900002c0e0351000050740807141c240003130020014000214001b860b0310000c9141c0b20010035115a05007040002c0c0d0140f0101d6845210007500a40002340c200703c07510380400505030040c0900c081d1020340700000c000230220f82c0101c40854200c040840c00348140000700c0151584008842e00520560300c580c1c5003d02025070501c02c2c0400c108001500019040c42600f01c5030041400130180321f865925429140c2c103031003a0004020444401600c0000d9400030751081000150300a40030700134500c418001d0001035400442c41d81d40c8080704014044c0da444071445038000903d900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 92554793 1250 92553543 92553547
    0xc0302132403030509060c1c0216050102010902100c020d0b0c070b010e060a14010903020409120201111213061b0f02120a1d0103060e1003030e09070e010c020f0d030203 74
    0x1000d2040000c031600140e1030405501101c0900000390814102ca9200004590a81d11110b442c2e60711440c048181000300300400d288203041710003070703000509010759076104070360b070840c254840004900b00e1b200510301a40c0001d4001001141d54000d00440514500140641d84a19659140e82442e0101944c502c5107408000913130100740104007a105000d00001d80e040c81c2e050030400300241041401d405065400c045901051250780e0245003844000c5501070800d001c4404c80c2c2c00c2c42c9022074036454100e0095400c1c1032100c2149802d1108a0300e0388070050080411689a1000c007011300500d60b0021610240e483d00b440300d200c000100f490144034001d5484160103418503400030300b0b01174091017503800c45909005413072081d60040c0c030340e411401940c48031a185842d0b00d00100c020381216800a10004149002d06c0303060a112610081504d0107520350101070100c40c0144050754a0480740d00c000510b06800b100700c030350b204e11103503030046000500020000f419040014140300c3c0542040b805a840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 92556043 1250 92554793 92554811
    0x1b070f0609140609040506040b030d0e150903060703050910110901020d030501051e031c0c0b09030301060e090712020a02100605040c23040305010c0c06050f011a070c030213 76
    0xc0024000c02414100c0c5020100c03a4000c4042000f0b8062078508078441c0e515080000d544c0d4031140d218003400318005088130340c0d0300136041c40036046015081e070650254000b100c840c03e8410070340c011900c20032400350040c0282e0b80c60860072401444058080c800c2c0d4012110706120b4524203000d1f00099a0600c0c210554a640341e4001a01e860540829001454144001001a82ea40c1c419080c3d07015424081401d840c824000020b0811f089041034090800707444180e03c5445920202c50709200e44140c40004190301c88000e03141ea00c1c0002d20400f0005541c0300710300011030409484094104c1400d0a0407010210380345001c401703a82103180d42e5001a4003100840c003007802c0d503014010040034241e03800c1100010014009020540d100c42e1102c1c06403d0140700325002d0141e40407100119044402000800100200102403a407220b00650348982030030007003601c0c45107207001c0d14100e401407441101d1030003e02ca400101c5412401042e01d0f08039120f40f0006c0540c85001c4d0441c0741c07442030b440004001e1a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 92557293 1250 92556043 92556047
    0x3070e07030c0206010f120c05130b0102060f060a0603230f150a03020906152b0f0c08010e06030717010b03010c090803070b1003021002010902120c090604021b070f06 73
    0x810242c4950840d40407a004001c001050045201600d481c10394540b0a4141c500701031a40300704a40c042d580026004000b000000210380c004801403500b6070964125403500100b1084007501502c030540e0190100c40100005400ba500a44841c03100c0d145280e0b482d0140c00e00c4100e018401c41344031260308840010400301600316051101d1a0b041116000380c0c041c1990045407108a00a00380ca0054030051840442500d1003c00c1d84c804054568286240c8809081190b81a4004812032941181080044034400c02c46015190b010034060741c1c6d000b0580c0ca000b20302800080c0242640750940a145d00100d44005002d6241000391100c00000c500d038001107013810b00716000030f010710301080800c3c1c0091040410110490b4041c40e04402e41d40703083e40743c0c003500c0401c8422070b9000035070105102a01a55683d0190400090b00c0c1c001c441401e20080300c5005541c5038801a820f00303030300400500002e4658581903000d003400c8448030392048403c1d43c5100b4403600d060700c2d640140c0311406141404010440e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 92558543 1250 92557293 92557301
    0x30e1f02010c1704060c03061205010209090f041101030b0f0a0e10050a0308030a0e07090c0e041113090e070306240b0901080703020d090803100810020f03040b040f0203070e0703 78
    0x4606032500d0314881c0d00303581c0c3d075a0030002e000d0030051405440302880b00415100f900200003600c030076600d10400700c00c50320b0701034000d51119500502690b601d000065003294801e1300c1d51300c150740041d607401001412000450003880d042a450754003505220341049030751621180705000d413845200140d40350416080c0c0c00e9090200c0d07407009202d038101640c10700c00103c940050300c0c0c01864071031021444a05285c0c940d4203140064120010462a101d0301d002020b40c8030101d01c0280605440400c070544040300750046911134025246044070103020100580c6030150f21260850a0050175184215200d544d200e00327a503154200c8103400c2041d1030f100244d11408007065802441e44280c89854407000b0300029181e040005c100d04103050307020925800392200740d040062656800b178131841e903901d02203292464022090081c0c0350b82d0302c11946200c4074107200340308a030300003c6484c103880e05540e1180d40d40d03200904010000c0f107842e0070601401c80103170ad0400100018050300100c2e0740d41403610072b02c02801c407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 92559793 1250 92558543 92558561
    0xc1703090a0510020f0406111504080a0e0109050108010b130305010501030c0e0a020a080c03040302210406030f0b0d140703050303011401120b01090924030602040816061b030e1f0201 80
    0x301e1040040c5e01406503624200d404694080c00e01c0c140d41e16071540824240044404207070200300300d4604200c10880c1d1200102076100603900c89401c0d01d03440400450b4625605e00945000c50a258018041c804400020301480703207020101c0d20001c4c0d200e9071b9240c00d54000380c1c03046901900881c402d002c029000d005950740050359130011070404d0145500280308400141c80380842e14030010101c0d0a1610900c0001e82e1030500e0200ba41c1503042d02030340d0a005500c80d22a500020389800c02c60000d8a4180c001c0100002001700141141d00907030716440554958011104d4092140b0300000000560a201440c001d2002003a5010740090150024040d14507030181c07000d02c20700e01000804513a03001507490090b01c3d82018001104e801d00e800000303002d0b103580c100524810981c2030010410481d60010002d0b54a180c058504451901500304a8603400d80100e50210311450b41400c2c00c0407a0b01c1c8035021442c000c0c688049503034503100114904503081c14029031a90b69209002031036603024080d004d01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 92561043 1250 92559793 92559823
    0x80318040c0c0f0602030703020c0105100807091a04050c19020706090b0c060f2a03010305160609180f06030b150108090a0609020a03020306070203040e07080103020d030c1703090a05 80
    0x2076181140e81e503608990b11802c0c000c11307150b030101c0801c404c24800d074184c3d145141100000c1043d8204050303150800d50092041c0b2699101d2050b0228000c01180102c11a41c0440e40b6446400040c01e010480601130003410000003002c280804505a6041045109030130701d1038001c0d141c1c0034100040104081440d4001c1c1d120140204450004644001035469010001c0300e45000940c0391446102a050003454003034610500c0266485000e51308040118100c0c0d1003401107401601e2030902c04a010b079824410000800c4401004000040461480400a1580240006040001d45ca6210464245410036185d030f4070060204904088202d04441c80c062003420b00352400c0c681107134026507540f020000200925121802c83c02103407100d940d050090340c0c0c0281640c01c41e2400300e00080d5a0707000791007030440111482000c03c3c080341c042c0f00440c0c140e90b0058950340042c0d0f1b0301d460075241d0211540c400c582900032090400c0340200150042d41c019407289028019415a07400c01d180f4000c3c0807003103268 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 92562293 1250 92561043 92561057
    0x6080307080a0309110a14010305090c031e0a05010f0c0e0307030809040b15040e07020613051005041401090c0501110712060c0c0506090102070317090a03050f04080318040c 76
    0x41803424041c2c8211103450724010034408600c3c607203105d8480290603400e801a00140c004aa01c1810513056020b188007030741c04118030f40d24100d02d15a179200d44020990035401c00700c5000e0007803941e11112000045554119200020381e991140d08580c401e8002058040d52001054205a40b100d01d20350b994004078024024035007581c550000b24070662994502c60b6a80e45080380b01d50301e640704e03800030841c030003071089894a0340e5403d200412a0112008401130003000000303448042c82220107083e0903004001070403417040c2d180d00c0768011314018206860640307110700d1050003040709020380d0608501c25007e80049c1c615142c0098660f80710810b0380e10580d000440284002d01c15880c4e902900ca801684c0410141c8a5180070360788052001000341482c01041c04020b04041c054005002c418402d507140002d007107822081002032541079480b40400c3e00084d0890700030038400c01c040c04024a61050062915599030090b41c50359001018508154000811494240c54544201480010399041184c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 92563543 1250 92562293 92562307
    0x140304030206060126010e1f14040c050403050a120206100509040f0f0b070503010f091404030e1f080a060801020301050a121e0b15030115050915090106080901060803 73
    0x382d100d98000340000c0c10805e032005007064100600c0c000c0340075800c50340e50021540d6118405400c8094080b110000400781040d040445c000308002c403c002c40d40030400702000b0000f40c0c0e0130000904000d0b008081041410701020005c10300034000304074403500c24445900280e04408000c6e051010040111154802025013000307607860340e80d506503003d40c2c4840240c040103d03501c0c0905c42c800d84d80c440905860030399400c0100c2140c0010045044c0d8098031003a0744910b80e07400341d0708291080e503a801401c80c2a01000300c2c0020740112219601440000d082c0804120300c03c0b504000c0100a0020400040c041414000c442100f031040d80c0c0031b00203000007586951305041c04560086164400c40141882140411042c00f1061101c940130054002c041080581039062104502c102510441420b6a0600f6403070001e140522508501080c0807000341806450002007203490a8001c1074481c800390030303e0041e40e01d66070b800344003406445152074280b985e080003520349003110540e400602107948100045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 92564793 1250 92563543 92563547
    0x3110106211703010807031103010c14031801020a120e070303020703150b030a0c06030b03160512010209030114010e0c0a0512060609040c020601140603010f0905040201020a05060a0c14030403 84
    0x10603400c1c0500c054a1406140a2a001000246405909a295501000120342e449000c20428210790061130244000342030079080600325881c00c80500045041207540c0740c03034031140038065a40083c0e64a445039181c0030201310b103800eaa000e0320082c1c002808914440302c1445451003070101c090160070003402924110ba4000c2d503541814040034041d01e90486800310f07070307102c0c58110a122850180c280e500181246c0f50014184c9a00e0181e000400d044c10055412804c0c0014811407184141517010100e6280c8018080c80081e80448030314195001c01143d003003038070300b4045d218802c88500310302202989491581401c445000d45000d48000b810030000020982c0034082d580c04048108068002e5203500c80010341511070132410703a030072900307105c26800055000305034141285c541420880d00f1943c407100704401072109018416406003400c0c000d114100305079000301d030300a1040c01141c81031071044d11143e14191040701e152110580714600850f00c0f50b4040144850480d40b0740d101c5003036003003a50380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 92566043 1250 92564793 92564819
    0x9011404031707020a080a050309010f051801050a1101050c0c07080a030c110a031b060906020109032a0804230d05061f050d050303060a060507021e012a03110106 71
    0x24000a0600200d541000d541c0c03940c0c2c103035005011b610120740a090302441c2498403500b000c80d230306000c55901e4100c801c003075001d04200c40204200a00040042da00c40006440541026134030301d0030808256415001a0800d1213a5801084071051050300c030302504000d1072030285190410341e0980c01075005040000d41040c00450740c03551003400f4010002e54480840c0b0540c010342c1c0080c1c4001c0786042c10741402c1c1d00d00e0107403905843c92030382c1c5c0c102060303101d007002e90036108202c0e0014006a036200ba060610980351400c541030381c3c2c885030050801c00094035000440c0c1c02603000006000424000340c0d1420400c4042a02080c405484031030403c021a2103050b19000010600101008520080c00c1080c407445040f0001d07050080001d03284004070304087c1d0340d035041225582e00400c0e13010000300b103450054055800499004110440c4603407050868403030046c10320400c905208901504107182d18159040991141b5000100c15a0128900340100039030085011416136034505801405510395402d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 92567293 1250 92566043 92566073
    0x304080c030f060c030c070606030b06040b030606030703240507050a0219020603040803061f020106031b030803010b13080d1106060405040c09020901110102030a200a0807110c150901140403 83
    0x43c00c05d4a0b03503113445924006108111001f00070b140b4009020040003210500e0390b01408003524204600320081050554800301502c00980c142d010134001c0002601c02c440d400d44038151041c540ca192071500c2c2122040d208152500b2010500209560605945c10804c056118043c18103040320850250041078251202070310180c00340f40004001203064440c00c40591120410000c91000710104881c02402000503000459041ea10608071305034010790002d4140c1500d82041c1c03024510703480d0203804200384d403160741c18250340c803407228002451030410f0040300d41051a07500c600b008a54403010f55401c1c5980240150700c00c0b85000207000120f515440404180d41500d600140c0c3c440d502c1e40140e0703031031700d0300342003034910358000000c0110345d48054114800d91850500268102e1901941c014103500130004040001003031140000e032150311030b90400903141180401d40c2c070301c29202408155100350004418419483c0000c0190036940e00840400204203ea80f2503410181140d64501c200c2207c84 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 92568543 1250 92567293 92567311
    0x60c0c03020d1b081602130b0f030105010b190215010602010f0b010206040f150902090a0c0e0105180d021309030e0a08070e010b0928061404210303060807080304080c030f06 76
    0x428004100c40041445c8400a5001042005a10000903d02c406840f428103218001c2180680c109603d0074140561410703600c1d0703070300914100101c40d0548010ba15401c4002811449080045e5101003012001c6038003805059002041903442103485400741e419a0340124110f61000302040041810b0b8429100c84a078860341420708040a0540329001e0001e004000c2e5200c10900700340301c0b884219901614803510582c80b070040b00e0744a440191f546010361910004174a541b00e403000c0031854044140306029200401e6100c4041c840001c0c0011961030740c00c1100400d0030321451981514004106100824000c002045642d017080c024004054040c0714030042402d02155034056a07803001c141d03034400440014044055070351580c4010004681c0e101e07000201c0c801d000c610081e82c01a80482c0c041d1f4005170b0035030702103c0585030f1a218541880c0c0d4203900b01a034902001c43e841c4001d10002c4010011003009584603400c0c00f0f080d5060030b0b501d040343d034880c0e4801c007224404508007040c002d5020f01c440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 92569793 1250 92568543 92568547
    0x5090f09011506030e1b1806040219050c01060f08030406080a0e1504060b0d0209071209082d0c0d0f050405030102031003060b0f010509040c03020403060c0c03020d1b08 74
    0x1118446014200300c480c0b10b16100310000e030200300f0300d40c03660240b654543c0810849501c0000d084440002c0f12070300903155000764144980f1600c41292961070341d00544003810041c50103000131032004014208420180c0080d80000b20001c05c60070074028070001d048604150307040d06203482d020f19600c0c41030b441200d01b8411403900140401c111f0380d01448001968070140c4076164031110000c0168070341203504071442032504c003c1d2a21818207681c0752098035400703081d59403207483d800d400342c4440080460740f500ae40e03100d00701240000c2c2603c1c0600900703411610400d00310302c00d007000d098407800582040090b9141c00d101c6200e080000041504604030181440225150022411034251140e81c1005801d5030000081c02241c144c9c21040c01c0840303002c0d0408104012001c0c0c10414000120351040e4006401840003e08514003076004211048042c200186055070340c0d501e100a840580d401c56001c682d400c0510424150140030042003400180b0b041c0d810000045034294401002e580d001d8910400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 92571043 1250 92569793 92569801
    0xf100201090c030605041509030504090506030c120105060103180c05040e190b010608010602011e021606060308030105090907060c1214030907083309010221070f080105090f 76
    0x1e60118008030340140c950000d07180c0702d0a054001e494140c2d011901030307a0048855200300304612680960b10783c9607407514500f914240c0007601405002e014590325004210a5003200e5440020340802d1a80c600d00100b490701c0c01e5400541155058106074844c000007110080c00280c00d95110800d440007210b0000f517035600d5103121850030b600014018120306030b00202006000c113180ca101d04a43c00c954521782c160b030300e85100701d00740c9500d551000100e0890750440e82604880d0b0f00500700c028480f03aa141c0049100d5203c800c181c0b5001d50050710005030010062065041c032006903640050380c10010003000385401c20052440b1001c10340900801103000d0800d01403481580c402206006981440cad440b4100404015150340082c4640e074082c0c45024014500c0b4403c14130304010b1128010300c10030b00c001500340301c0b03200e4520082c4031104555081040395250390889114103000052002a08450b28220201800f0940c12464071130034020700c400104102e5950744c0a4070f921040c000044005526 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 92572293 1250 92571043 92571047
    0x1021c11040b0703020a20031507050f071b0501090b03010303030905011401061d0910090f0f1404060501090603080912100c0c02210a020d050c03070905090c09060f10 73
    0x542c2d0403110201000180a40616500180341c80301380d4015800031044400715081c1d820285003000082d82c140c0c204030030b2101c0301511080311661042d03c508040345804c40701074201d000350313120160842d503170a80080928081c100c40b0b501c401c054102801c0160300a828804464441d01051000904150710384090404000d020f401c8404903000485d02d40303c181d41c43d000c002d8000818815036806004402a0b40b4010340303005074a140c01007240000450030b65050814400160040007842400591940400c48141d003481c4a124000303264210402d200d401d1520f0404142c0d841039000f00d18181c01d0170303814004201c54100319024100d0848000100c441003081e403504000c2501562104140f800c5402d0030455002442c071040343e8070854045c051101c00d07100c03240110380100740604861f800448400010b0501c0d0b0580301c0c120f030150044030b9852030340c02d00007890180aa007110582d152034000b071110a0108000301d0081400840d01e44483d0300d4084045a224049440001d00c20001000c450030524 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 92573543 1250 92572293 92572297
    0xa08030408121608070215130f080c010219030603020a0902210a0203220b06090907080303090705040e0118020f0f04091a070c240b04020c0106030506060301021c11 72
    0x40e811102c41c216924003030355000114040c580444010030301110002e10314520119811022101c00c0711400096101e507000782c1c0c01030040e03101c11a480d036401c05006001c51a11805804161561800580e48003001d0009010030760003181c070a000d05040001c2400142da40c112028180d505040300103031200881c1c0007101d02c011031030181a030380400900a00c81045450b4000310b101d200700e82010f99420403801d40d42c060311480b6503005400c00d5141d001190403813502c05e1030542c025044100300c07607445423540a0075086a00540718405103074040300003007005007047e0082101c01c00e1007a00820103442200440e00b85030051a01c000c1c49001500708205080c4c1c3c401000c0d0881c00c00262080041218600e84041c400e82c4080c100b0940000c40800551000d1099000ca4182a80111b0307846410080c0008404d21011003003549241940761240441030723898902c040c0c1184c1070b800780041461490360070001d003402e601904090180e40100320311040fa0050351340c812441001e03640e000a081080244080c054 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 92574793 1250 92573543 92573557
    0x106050f0f120105090c04271d01090b010b07151104080a030314130305040b030a06030f0b040201110c010e150c0a03050304050d020d0f18031e230a08030408 69
    0xd0390109603803400c4808407403414142c80c030a840c104416110403446c0707400e40c042c034802c00d40044503caaa80074884488400c60081a8056101203919515102546030b080300400c90002e10742e555618020510091b05401401014124503035840d140c12603d03003e00c0c143c1740d506001e2450391141d143e8045025080100e50081c00c0e280c06560511801d8a0010007403d203000d1343c1400400c1000224080c81c810644503e412a0f264640b5450319141041c0e070081600024200c42003184e40f040008049180f40c0c054016591050f4550006850644000342c01080642d0b4400202d602180130015240d8111804110000c42160070b4201001d0484000440703110750a105803550080c40420b80030141c10102950080b4803910546010131a440c04c02c03661500022000e000107100040e810b40b9040c05022000b1151040342c44000c02c030b40d16503d41c041e4142001d160310300003150001e0070720184800d03400401a18103407411840c00c103402044202d44c0c0d070000b86c0c1000d803030b51900102141c10042d90408846903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 92576043 1250 92574793 92574817
    0x103090c1203020709020c01200a09060807030b0402030403030c031409190c08011805070905090a03030b0402161b08061306151208120a050601140a050f030f090d0807080106050f 78
    0x145a0703100c800709010744001004603945250440005154180880580d40c00ac142d6039151902c2c2868140c0480d841380c000342c0400145940c1c1c02c01c1c40680d448a0008522843c00b0341c4021810701d0444000030115079003440310305030f00c060400034440c030403d010908840400c039038020301c1c06600032400c0c05010361805a00820b031a42ca0f001008074003c8428102c003840c03a000ba030a48603c6950748020318160ba204403019099030300001c2c070103030009010758001d5580880c05400181014202007001168091500c0260b84200c031140807140824030302541c040141c000cac0781c090003590401500a03460340610b407030001c01d00307a01d907022003030402c85114042d0028449030b607a900025030710342054019980071448210560240c080042c1c0480c2c0346000b02409801c040e900c12520000613046811a500704000843c00c000041040320071609103100607601410410a02e2001810710203031051900610f42608014041503400700b000460708141d41c94115829400c00c1660b4106620081306a44038030f03d19016 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 92577293 1250 92576043 92576047
    0xb06030c090915060105040f090c09080f280f08090f0a0b09011d0303031b0906070606090c020708030319060f0b03040c0806130303180c0e0a0b0103090c120302070902 73
    0x750300b800000c3da280403802c08892010040e11540011a1140301d10f000304040c058071940e0400019502d80d01840580314980b41000c072494882100c2404c1107c610000005030384071110b44004080c0202c510014160508103030940140c242e40c3d04800c4000842001e04105030125002c4016142d10010021a010050003814500e4490302d02e03052030b13085400c2050000740e03a41c0b40d060319400d14a0406840366401002141580d880c00e06880180309400310b50b4101502c24042106e00b9281e840103801e01a100302e401141903404d00c440c00c811a01030352928001c640c00b50300304001480001c400c40b504078041e0162106403904010324200a00140d40c031103d203100e4640b100180515450000d075004a201da05500c0c0002c0d80c40c11400da0307680c000d035142182c00340d5110704500028000e500080c113207056281d07490103602c5030f45c54681003a01198403440100200408001040da1184541c1b82002c00900301023041640e941c0703030111042280d002d81095150151210390505000b0000900104100c007001d41d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 92578543 1250 92577293 92577301
    0xd1202090621010e060108061528050c100203040b071b0812040b060d03050415120c0302070b13170c0307140115050a12030818010c0c0c0e04050601030b06030c09 71
    0x1142d058000d1041581040c510004508035600c11030401c0c0c012100244110010066011043c1181c1d000c0380c0c884c109041c960108110046801400d41c4140360991503484d102e00f2040000d5040080c03c0780c2d1035011910410800c07001841011880c0d400c0940d038900444840022181c0845080b00000050401040400c9010f00206c1e004003082c407c92140c00c0440d26a01c0e00e9042c405e080f00c040d6001008a8006c2c0020b01403c20404004101d25246281074102940621035087c101c4410f5041000001d4001422100b0b01c0b02c5220556001140740c030190210000944502400c003503181c40315440c012000400f00881c440400c00d88a0f15030700100e50146204440503041d008044000b481c1582c00314000c1c002400307240040d40c180860f81c030610300182c2c0c00c2140d9411138482c6801480c040746ea185030200da000c0c0310380900c1000308080c242e80790030f0000da902d400e001b403c0581e140c1c42861030342d2008080000040740481c0041c1120350000f468403180d00c45174002810501004075044d0000d040c24100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 92579793 1250 92578543 92578597
    0x9060308041404020c060414010f1d010c0f0c060c030f1401031103010e0c04050603070b070317160f112a04060503030c030417030403020d1a090d12020906 68
    0x1403045401e805036580248005030b062100740d0040003901c8825401040000b408070700c0703d90582d110340c0000c0d0000034074a00c08541d004102c6010480e500e412000c10890541000000d1060320b100245a040010707a000d4103000c014070455800340300910954848082c031407000e010b5005541d0b10342c001e11040c0180401c80c0f245101540c82480300b42c134101c010369460402800c06100c1c904640c0440c0020303140360548402404007405019101036018070442d000010803410640241c01020701c039644004ca00030b07400d07a054003451400390000b0390007030b0400c10400820b6001a016090300c1410f041001c0003400c000c00e1345060200c000d031140a614807416030180c06941448031403410403021101000101d4540b014107130740717000f0071200000c04d0380104800d20010300e940c0c0343c052403c010f036411245410385170303404181c0100c2c896404907031161000080341500304041500961122041008000c0c904041c1c000600c159500c1e546100c00b00c3c1c0c0041c6020b4503440d044100d030145903d004900c0e03a00d101d00185 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 92581043 1250 92579793 92579797
    0x2030402010207060912020405090304030203011d010b0901060503040209100e01080705030106090603110d0c0302031504050d180b0904060f14011404030c09020d02090d0c0815010e07050702010909060308 89
    0xc034018081e407080400c069000b00c001c8000c0d03810310260510f5150030740c0d080c007000300b1014050070040d12080c031000005036024021581c2c2d0b030f0315540d0040e10502c1c0c01c021440c299440815401e114003110720050140d55401001c0c0c070761150b0104d66070512625440801051010250080881495080008201c0c818002400d90031503031b040c3d008020403991030728030804498040c00010b0600000164410703c030b00c0d03e83c1c9009022801341c0444c1c0110781c1ea0740d00081c94440308048110009250340c0c104814000c042c4102e80380100b240c10521514a08242950800141030144c04010900410800001d454a600c080040d01d000c40c98000250b07102c408550320340304039508981c0003802c8450f5901c2030034402c0c42520101c81d404440e111220742019041c1c0c019411010540f03030081ea007841f00c40d00d542d4800d406145c6490184481012441c00c100c9120b061402da000b0449102060500402582c112205501d5100c042d41c0f40c032a495591301c0c0700481d10f80c1c549a010210b00d0341007070408800d1003c4440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 92582293 1250 92581043 92581051
    0x2070203011505120106140d021503100911120a051e010b070b060a1202010c030e2d01020a030905041a150a1e1b020f060c0304050f03071a0d11030a0203 67
    0x2e0345040580710740703100074265a074902887d00001480d26404d00c45040c0400d1140f10140300426031211046850200c10b59a04101c03040300e078100f0303000307002c0043c02180e1003400054502c4417081480d000d442100d9044e0204058461541e030756803800012200f00400149a00c201d4181c0c400516550390744055400e83c1d0000faa050342c84900201c0800c006181064011044400070040d60740c101c1217540040d107004400000075030601000d528048039660381c03250051144d0a042c6c0080c84a80101d0707514400651018079902e0555010a20010106c1d4014040318201d84e011240444d00da01d48400059100504104854001c3e12004c440c034118422800580940310b419a41d14130380080d81c0b9000c803880c100184481020075042101902842030380309255042c24000351048689041101c003080b41a4003d4406000c40d0b000800c2c24002480e100b801c03104207000840051440c2c90604819541181100f114000c1040d00011250811141500104c41040ba0012401d0710707847e005002e04007a41c0b04403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 92583543 1250 92582293 92582299
    0x1e0709090f020301390302040b04030f12050f0d020c010e01020c03030109051f090f0b13020903010605060c0601060f0e0a030c1805070206070507030207210c150503060405040602070203011505 84
    0x61443d41c0d245d106091208554a0041d031030b080d02c02111180e1100c040403015400c200343e020800858181e0035403004000451007400141c0d4040c81da814110204440c0e200c0701c408100e803c01501036900c4a0a05039840140b8002c80182d0328540200900d00401d0450000c40c0700307500201d403090054801001450480301c03a0350081c096030307690320369013541e00b840701009a9807040c1e100d401b404024504e034007042c450f4180360703030000b880020180021443e10200d0340713685d40250001041c0342942801e000e218003e00041c0c03070050410040b50489078842005004600030000e07540c1940d08054030803c00c24543e00000340180c0c1100b522414038172083c407c68010340c6051101c000c10500a84d95030311802d403150301c1c2940900803588880b0380403606540303c0354098085100b0003d021a041c00c00c04081880801d04186a0160311024640060821003a0f80300101508a42c250098069041030482e82e01c018111000031303459540c0e20b8450000d001d102e402940540c079210340360041c440e180700e091003960011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 92584793 1250 92583543 92583551
    0x706060b07300e370806090a031103040e0108070f050603040201090501030c0507051507020613050c010806220c110d0212030c07080309010b150405031e0709090f020301 74
    0x940e4450b07a5100c1c060352a00c014003815250401107a11500c02e42c45490002005034012030302d010714281c80c1c003042104040f01001440e1401031016030203110b00c402410400058040c0f85007040680746c03903002003003016080c020a60700548003c80c1c107000b280c000d4000444c4855103941c540740d0080d0748981600ad040c0c446000d00c80e010800d4503112065a1242c1c2d07050352207803401d6040c44011000f4003034400d88002880b009110380e400081042c01802c010103030040d00a1218a8aa200245090b0000d40540b0030300004401c0040841da000c42d20512040c802c0c20250400d8440d0004518041d1010021030340c00020000c1e80b48615800d50096001d0b20003a03900c03c00c0110f180306005403156241036164015a11070b10030b6100002d092400f0b1340d440740034005c445090807416214080d455204403000c0b180359541d101505040d290450050742030b586220006c60800307080c90041781e0b45207400c94034180c18000c042c41e01c0064180402002c0f016001038001445580394a1820700030120725480128032950030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 92586043 1250 92584793 92584823
    0x3050607030908031f1505130f060c2402040b12011424070c12030210051009090f080c0d030b09041e14060c040302010f020708030a0e060706060b07 65
    0x82800741142e0260050029440e40d110403554a41c0303a80400c2c65020701c2258441c00082c0c00701c000c500010102200e0f182c0c140e9400b00c14083c0e40250780b590300240040c0214103024080381743e01c600745241c8964004001c580740c0030b1072076600c1411500f190216018500008000ca0a20318220260841880380e1100c60000c0c0d885070010302400140361091504401c202410240080c0c204807100c051401c6541003e10b0216107894280000300d198211005400b40d501d01d1500f0594100011801d80440d10810041c034180040c902821000c24402d229074280c035001c0200c180a288211440500d41c4013061640d00d04c80d00c1105511440991030361000300b13142000c12061824400300140c801d0368000d800c400c02141c0040009480e40348040e0070b46402142210055001c042004114014600800e01740e88551840c4001407004042d80310050441d08071400c20460500c00100b5928441300c5410006404144500400c4d258040c5142c09026182032820024402d10303400005e10707455010b061080b5100c41c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 92587293 1250 92586043 92586047
    0x3050303270f0c040c03060504090528020102060708072d11010e0a08210703020301140d0b0613021c0615020303040b150a1814010f050d06021b0604060603050607 71
    0x1410008045030807191a000f00c1d440c0c0f541c001540000345040002d4003079255008030f011030304800003c448551200400100103014440707190444d100010004c8003080044c1d0000352220400340101007881100c0002c0741c050b0340100d862040139640d5031090b00d13901d081c6c80b41d01075880d011507100e075000c9000d40d080504108818002c226000c1c101c400102514001a81c0301141680021464862901451b030b6451655a411001c240a600503590158603541005034100020001c182ea03284a82450030600e4000b1300680d141e0b55214004407400d94240c035540e00c4c0d03080607100d2100785288140143d90040c02c002120750141041d80c11880402c4009007507000242c0e920710060390050540b00304040041c100b1001c0c80040d0040102c043c02105c0440c0e0740304c45c000e0000c20200020b54030162100140c4c030a4401510843d80102588061101814501804180d507085c854401515840e00001e45400c40024840c4080700d120207a41140c045281c142408801050240003c940e18029003001c12a264 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 92588543 1250 92587293 92587303
    0x30218040314040b03041b030c170c0126180106080a15050103030203030114031005040317060604060e0105070c05150307110616050d06150e040b040207030c1b0305030327 75
    0xc120003001c2d8a541ca69403104092170700001c2c87c04c0c05100786500040001000464800010b001e0700c88040d4a841ca010030040c1400c102809039410403018008040140440e00d803280f504c0ca070f0b540c1c0009501e4460045025815400d200110f06643c2000030004001000191480c0098001c6a544550700a01c240b03441c2943e60030302c006030043e4001e1005000050034140392904c0c5041c014120341c0c41d0350040718940156070048400b60f000c210f120b0707018914146502c0d6050b40c03044040f600c0501c0d2a0600c80054202c5044005090400071301154240410800300c0c1764501901004000c00340182540e0003040d015841141d0f10b030005000a08442c00d54280002d20350700480101c2e0b00c5100c06150070004131696040301100000d40d40c0c070707804000f80c642407a100c58003490b52241d0340e064034541c00310141300c00c0c0c0c0c0c42464454000c5104000c040c0c04071303030702042601445900070800800b02d202c4581c4072641100c40d80000e049400000240a485e07400404200c5110788107a455101d80c030001110f107900c032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 92589793 1250 92588543 92588549
    0x90405191803080f0705270d110909010c020d03090809030102040306021b190f02370e01050f06210c03100909170a1808070302010206090a2a03021804031404 69
    0x868018805a0568000c00801f810045440780741c240301000c0800029860040c444802c3d2006030355205100ca5a00b0181107099002d84540020711050002c894020f54070320910b00c840040641e2070104104220310a0210361814000400a64859413641021002940410f2601a2216966004008400010030251516072915804581d13101c1140c03240c0030030030300d0144102e0340301e0095000d12002400012800707032124504420000e0991140164800007822600581d14010031030004000654a00c4e841c1c40540406489464072681d48015503129440120710842a8203200c204200c918100840034520508220200380410350340d031145082100e1059030042e2034039006042203454040810001c101c08582407070034184424006418100c2040c940d082010070340c02c103480c01c03c11f40d0303410000107370030039200005458107280684d9136026803a0781900714032901024004445038481c5440f58080150307006400301c0c03017080a45c24600c8500344103c4084003c100c0c14110b0102c20507500c400e640503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 92591043 1250 92589793 92589797
    0x501050a0e04060b0d02031504120309051e030702030d020a020103060b0f0d0b03071a030f0108010203250e0603071e030209030a0201120b06070b04030f14090405191803080f07 77
    0xd94690343c440101400030011480d402040c88010b42c80140c170108030365140070003070034054501d504007450016a075070302c40c002c00c204041c1040410004030341e0101c0c0303405480040e034080c0c12403114150300c001d05602414001079070500850785040c0b48150041b40124006100b41d03420001a52200c080400c0d601500810641d0340006000303102c40c90500e98044030704d1801c01803c60303450030b5541200314020b4032a500307201401000402808402905110518094100c2c84000c2d4114900a11910020280c808920203510036201303204240034000c100306a84104054401c654074684440007030b00d4034411204c2150204120904440c0c2035200340700781c0310b001c40c0c0240503001001503034004503940064480c41e80000b070ba903002e4800c8155500070090650340c1c420710a911051610303040c050035454600103104280440800c1b18104d2090f210100d40e800e1070f0880340010161150385031300c03030241c0c0c405101000d0070b490544001541040c01601080061080d540c3c0016561011664550f54809481e6400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 92592293 1250 92591043 92591069
    0x60309030c060221090a020906040605091b130e01031b06020304051314040f02031c05030105040c031e062d03060207020d0818040507020f060c0901140712030501050a 73
    0x200e040d0014120003800604039038100e0081d00f1310304840b460507503214640307034030000c102d5045040203c4040d40c001c0c400c80c3d04000c11841c020101e1007240c001404007001d45028501d548402d030051050341c5050000c1101e451200351100d40600140600b03010580e900940d018806c00b1021580e0104000d484495002d58109817611050050034942c0018070000c15031075140c46e00e020508420390740e11a50180b480b00e40c17040c0c0107006141c2402041010341241c0101114002e00198200b070440381100e80c151000a032640204600b10700410b80844101050114109c0150340e01c40c9640002046d5900d4079030b00c04c83d0010104800b03c204a110a2840d140301070340504101250850b40585241400600b00c7c94044c030711075941c0c1d4540e0b031201c0c40f02103030031440060001c400c0c01e080c401c040c1d020b800ca000404031210b01000c1c1a0756807400808401540c000010a80c0300c592041400c0d10f810822003400d55191065407412810651583d840000001c2ca002c000145a10300042c0b00c00480d441c0b031030081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 92593543 1250 92592293 92592317
    0x50406090311210903030c0a05030a03150602030750030a0909020705031c05090705040207021c0c051914010206060d06020d021e0901030e03390304030510050106030903 74
    0x3200c0c4d04080c948640c5408203000c80c0c5080c0d54240003602c3d00d140300d0300107107aa41da00340ea406000c8400f40181c074680a04642c00038408030ba0004201c0e0820f07500080443e2402072085014034424050030084028001c9810481d5401d8500c0c1181403030411031400154842c0a140b003c1e9543d034040c1c80e0b00200068104407003044443c0c42a40103014081c05072080e24508064900340c4c1a800150062501c1180d5031001004900c1405107c01c101500049505504c2c2c0b030415000151404c0180300340b00115a100d844400c10851260204801442e000d044405000000044490704c11803034441c81d0980c0002e02da83d00310380e41c070100d08240f08450091510351019055260b28000b0740081c442030700c445608219900786c4800c103c940d40c3e5100215800141c0c0e418861000505aa035a5038480f13038580d005000c140035484001d003130002c20005d800d0550a98a4036803051511a04407c03100c603401d400005004414010302141134804a04200c034140020390381d030a421000c940ca00c00025000801c0342e8441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 92594793 1250 92593543 92593603
    0x60a050c012f0c240a1802090a15080d110c090702030f180306280b01080a021602060313030807020d0504090c050c07150207050103110307030b1201050406090311 71
    0x36101c44140c1400700c510f0740c10840031001441120203040b8a00202e514104561405c507401101d03042014125002c4004c003082c0d02080c0d520802030b00c1010903076110b0501a41040c040742c0050010001c440c102d54070510310b110081d219100c50518114a4062100c1014141c00d1503000d9602482d2181d00461501c1c0c0f6a0b10180d040b50882c1c802c0801d840c0d1845032200c82d03a0740810045019200812020396032500d0140c0c0303c0841482c0341d504a64143c04d24140e0b100700c0e03812203120ba500000213840580d864400ba0110341c0864020b40340254000808003d00c603611400581c5110301500c02d0722a8005611030900c00e0b07036034101740c0748254006030f0100b2007403010741c0c43da811902500728282429810003444010342400c0c0101500303c0990342000307107075510640c1e038100510300c0241020309042000c1d90b09100c00e2085031100030415401d141d1070340c2000f109611a03075400d11081c10824003c100f907080901d48040640000d040a9000400c000e110010341340c404552140a03600e0300b580221803154801030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 92596043 1250 92594793 92594797
    0x60409020a0516050706110d080604020906130b0903010c08130f17070f0507090603080702060309070e04080705070e0601200c060a080a050c04120b0a0605060a050c012f 74
    0x440108101840030480d00351020f10400c65951060f00a0a00c244c10550010000c107504100070000da07018914030b5407081d82092003150040070648001d6039408101c004200a8404c00d8410303180710f588402c00003806011361000d000c500e5011802400042c004503c1111340c0c134410343d1070b20184170300c01d006480003c40b4800384030602072141801d4241c00980344281000754010003801c0e51541c00070b0038210100711b018490f613030240441c0c1408000090a548546000b0b0082882c002d014440002c049001071104004c404c0050618822045c0d8a00d4640351a540c0e50300040800c0b19a803040c4403011489604000c03030703e071080b60103a48076003105040719950750512400c0804290640144400ea6032647c507108003c04402c2856114402c0030b05010701c149003240c200904802101c8000c0c4400c0c841000c91508641c103c9400681500046c0c58040c280002400103601080d8428000210300310190b4002010f44000c00111008001c114015451076000a4044001d9210034440e07894000c0e4034500500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 92597293 1250 92596043 92596057
    0x6030c06030b030c060309010b0f09130201030518030a02071508280603120e011706030604030f0207050a0909030305060405012103050d020711030d090303090902090f03060a06090b0301050606040902 87
    0x4201e03041369800c0804680705510545420034640d45500c4040c0315420700e4480c0d856003c0d019201d540c070b540f03402c144508040941da00001c0c101034447c804500c41300401c51044c00349070700724020b60790313200788590000e56102d5007881401c85900220b4503100d503070340c0210107140c880e41103007562024498480300c03210030000351300b40c400200555484020001c968400348003220380d1140c1c0c0358104107910701c05c009408510307034600c0e9055482a6074100b10103501c0204800b600540d16080c03503110000c182c42c042c0e0a0215582001d90001da004500251030003aa401c441120390280e2001c003c4c6031144014082992001d0045050340c0300003100d80405603e2021410034034a0107460001d0900b607140d11980c0c2aa802040c00752911120780784010700500e4140100710303103d40c15041c81c0044601d9660083c2170b03141c851090007686903020a00f07107a00d4445844d03040c000b50005041d100185003201c5180300070002405445421460189040c80c0307418140b05560080400401103400d1915111150010350f005003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 92598543 1250 92597293 92597299
    0x1050a050c0a03050c010e0c031510170102070606080d02070506031b040f2d09110403140f06060f060306040917070b07080c2d0f040902040306060501020106030c06030b 74
    0x110000e140010b01104001034840c0c0c0e03640d0307503488543d4903650030745001090540c030301c5d0001d50b541c0340150b0700000c25881450851011500e00e03514042030f0401c0509680c04041000340c5140c03088074a00c0194024000c2500c203090401c0030301c2c0c60b62860780e030350b4071540d4030400580d01c40e0806001c00d02e0088042c1d030f400710001c0380d501d010700703410170300810f07070340c0041d44a40203c0c3c91281c01409081000540c204103540da40560360198144200d5019901078280315207402e0b69030700d140c45030080c2940d004480265811942d41c07d2040c9640040f0b0303540e14100300000030030303010b00c1c4042012840c0c07234030103903d0210b0024070aa082da1540001c02000700300c9400c0484580f601c040e503412101600c0400741402c18090840380c20185400c150240030004018010060700d0400c120144010b488642e0a5000000e039000d0101c881812541c901e142c0e1049020301c21040030040381c0002c01d6440c0e60001d00541c0d129200074018195071700016820b0b10750600004084542c00c020a202842c429882950000b00c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 92599793 1250 92598543 92598547
    0x210051b0703090801060e06010503010e0907090903020c01090f0f0b0c0a050d020f0120030112060f02270301090b010605030901060902040311014d06090a0c0b0301120201050a05 78
    0x1106000e085035000030012808900a4581002003803000c0c81924000d14080da100031240c982000000c00501c014000c0d03028651107c804203400040421948001d81001c54080240c1540303424080c4d0380d001c0c01c0e10001c0c00211200004140329140d202c8100840b04203428800140c0d017000c07101207040d0020b40321540300d445008030140114808200110410032150003428102032810740190070b540c08200d107404181540921005241c3c0020126411202407d0305820311491600d4210003902401c000070304054008100c0b040a014103902c0c061200c4040c421908440c4003900030b044c00c1c0d407101103014000100742c0e001006910301880055511500c0c0d0000045d031a610740c0110404c903003142c0c000399401580c400c4520490350304050001441030f081c10840c00301d40e80340c8821203914030039203841e058056070105a9001070804505965500d0744054241e84062a000300000d036100e420400590340409040c500060f40c400038800c0724140c0740d40030007511090180342c005540d603a0050342d80c0e030108101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 92601043 1250 92599793 92599831
    0x50a0309020312071b0305070e0405010f0e030a02010b03120a0305040201090b030c1b0118030f050702060c0f06060d0f0308071101022712030d050405010b0901060c0b07090501021005 80
    0x41800041001901c100f00b040d01c812a40c103200a4640b0000380002100d180b0351002d0003c83c000040c0a8101e0702c2c008224200c964072407802c103014002d402e144549a5051020b40c40002d44044084e01c405a180e9000b0003055030311604140d941e1465000001070b04070201310220080d03100381c00550384507006040c158100c0755a20014215035100b140c07904080030b001300e220300c0840300c0001e1484403048010000e021150194107280f04840204270007d0500c092206004003803030142003910340c06a001800b640c0c40e83d203200701742505e803c0034040a1032240140c000141c3c442c82c12002c03011103190842c003010401c42c0d4964095808034000780206003800010201145d209000740010410605102090350410351800d0300b1910201708103482c24495022a02c1d0308070340c1c03140001959401d08072000c0c0451291030300e050640c0100080b55007660007030740780300c004a41c0d15042402c914207036200d4020b0084075540e13550102c802e0390043c0103040c0140c100c0d10030070201c2103081c0c0013140c025855924074400b401c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 92602293 1250 92601043 92601049
    0x90603040b0108160302090a0f18060b10050f03160315090b01300f090c06080712020405090703023402040509060c07020d03020c0a1409090f0c01050a030902 69
    0x1200d046440c402510014810320106002d2405200403070464004198115400210840001002c042c802d45d5074800c00410000c807600b2100e03983da0720b40600002080349040010240c5031004605010310004c0d80d403910341c14400d60031120b121041e180001e0440c0c807161007003c0c1020191100200f05a190b007080002910322469031030081035101000201c4c500c641d000542400f4400340c0b000402d0071200c420a4400301001c041c040b50351318020300000c1c000208803580c402450384060141000c4410803000c2043d540140c1d489001780a15214480f00c000c0c1e40030303100164440e5020346a00480b210300859003560003a0042c0c0301c00350340158400c00b024503141c24500044820074049201088180410b800d40c1094880c2640104105000d4200c6140100e0810300c107100d0080e0090040650314603120600d4400c3c40041400c2000a012049592750f69641c400222a00380382d042c852410307c404907001400000d0902034180e4210098100003112000556681d049416400213050311349103c41e005035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 92603543 1250 92602293 92602297
    0x90603070e130e010c0e0310090807050a0318080118080d0b03010c030515120705010f02070810050412030e07170a02060706020a02070f1404110c03070c030b0a090b0402090403050906 80
    0x80d01400c00091043c0e0441d50b12403c1d10440c0440e4018410360b00c420b11034a80300420300d613616603501d003004100c204107850075000610a451020305180038810001d01015441100c80c2c0700004980410484180c60740c03051401ca905103884500689142c6050320300141084018081d01c0d051031b40e00140c1d5045000219003902d642503039140c00a51f4650402015012030003082c00d9031041959415007101180ca12103a030b07685a07000b6241404000289401214400c005880c050f0002c0000d5414948104180d0005481e040e241120307101220511031040a20920629642d0040780000305116464404003404440d0240321540b842e001b0544100d015071581e200900c01d09206034401a9a41d400d00b100a05048150b0420359059000540c2000804049240e100682d1011100003030800c1d101d4111003010720440c10210028040410110140000b01d582c00d4100e038095102c0b60b42503a40c0c6403c00040304e243c144010701125001002ca00541080b260450b0b00c1442405d15525112299000076015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 92604793 1250 92603543 92603569
    0xa0c0306080f100c0c02031e011d0d120c0e010e040204080a05060105040506040203010f0b34020103050c0405060d090204061e0812090d0803130c0603020406020f0f03090603070e 78
    0x290384007031040320f850341007446005040701c0305203000e030040b841c142d00007a2584402c049800d032020241381c0e0154401c800394070019199421074021041d0002002855481d1240c4003003140c08509001c980780541895801203400c05801ea540e01036105101c2001902c81070a0888800d42050303092002140c149420008141780340c0c09a0001c101644c905405c00c010384a004100502460052004100c404584803000c401d541d20401160386406029104142054250202c0d54504104500c5246802401d0b6907120701c0c2c9000703a0b4240110358807034210030b41621851161070382054003004810250901e503400020700502c0140041555a82d404c2c04410303040441d41c60221040f47c86004009256007006800078403011405c81c40d040020380000104208080c01003c9c10103840080040d802c0382c0f40203400c4002980c00100d404400352902e400400941090194001510802d482c0c446c01d080c00141c201c0304403000d40011440c0c282c0d10400d00c540c0c2c0e0005020f940910050608165290361144054035903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 92606043 1250 92604793 92604823
    0xe09130b0108280302060c070303140403030902030114010f061101020c0114160306060903020d051507020c03070603060b070f080f0c1b061218031b06010609050312030a0c030608 78
    0x8010843c600020010403d140310034901503035480300c40d000079004201103500400c80c0180030341b107600302d040542c05001104c207070740c0d141c00b054010041015010ba0000d070005001381c1c002c0003101107100d00642440b20030702a0400000451004020f00b92080c25840d15854002001508043d0000a200e0030345c0c22182a01503498070060420042c0c5412071a42020031010740b5061103c203107458005480104140400380c0940300605150090007400c000d900c48801c0c844013126102d01d00304100079100c415800c0d2161107401000c0c07000030202c1c441c0c010300c0d06071140c0d00744551800e10706079202801c50012650440e0f04590511078500168071400280c840c100d400005400b1a00001034004d08460510320792903c00d49013444035030041e12401842c164031502030b00021000340850050149940150200b4084a05114420380341044000c10414121007140c2c03200c0d101d50781c6440800d41c031000b0800c00710400c100180b0003e0356403049500100114109400d001503981d803191a11f0b070520040c4440164 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 92607293 1250 92606043 92606053
    0x2040b0303130e091204061202030c0408030706050a0e0a031409010e0a060504081c1b0804260f0109050307080a090e09060403121109060919031202060c0a0e09130b0108 74
    0x4007100c0c0074170183c103101c00101542413400741004009820000c00c00910210a540400091454020441200c000d0700d9108222a1504c035585801000b03400212050b5041504288040d0400d00002900f00940c07981601d40e100304e0f50340e0700d01508140e00030301d00d20781c1044010094102c4585800320850301134101c1d6502c140c0d1f0349040c040000d16014401e84000042089a80c4203005194451800540c0e00792030324400c1d038000d00130706108a032130046410a1040403000300d0900d10300007a200124a16907401000d9075111040c0c00b403014200daa00381e5010f401500100060070018520000500d02149941001c141060701c1c0d540c11036010310101c840036403680c031000030301080c99040b031800c5680e110900d60500c540194007854280d42d010301084c00d4050a0040340d50001655448624000c3c400702c006881001c42d92801e00c003a6400c20f85240401601503540400c03803410304203041704d400300c2e6107444040c2000410b0040c020706003001800c1d000d05043d140f580100040391002e1560007006804024a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 92608543 1250 92607293 92607301
    0x40606020d0f050403030e0906010c080412200a06051605011b02010f05010b090118081014010605120f07050d0c02010e15010f090c02070305032b02070f02040b0303130e 74
    0x9000c20002c50b400105200782480100000307580a10000442e2209840e40147c42e1a0400140c85240307403004000c0c00044049004a08a6003c05011000c10300031448961000160b850300ca0300d00c650000d0707160300030740200070501c81503005000038040b032000000034400c0c40000791186421280740d03100b10f211407448080c00d40461982402020080620340b80c04122952409141400724482c0d1440c3c00c0c1400f082003607040f061006800d11070010f01d0b030001038440c11841d000d0140b0007010781d0540f41000e16003c1c000450058414026a042c00c0c2c0d410903400070a03215100b01e8524040d00500320801c101c810411030389480b08601030794010060f2034002040440c2a110003504040014901890104070b240041040099403114a400c84202100c0002d20310140c0808074100525900040d1142c4400218690b21520219114140100c00c407034090070803072701c151180160b2081c2a4094010185c00c1885005071034194042c1e0b00310900181142e180c041d4000804d503c40070240d0201c0c0019008070100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 92609793 1250 92608543 92608547
    0x40201081f0e060d050a1a010e010e0103020112020403020316140f0f09040f050706080109050a0203070e01080919060504060501080a020303071e140606040c031b120b040606020d 78
    0x96000070700a601488a40e14031484100c480c0064841c4003021142e00b0081402c070340f940c07035181d2002d07500903094450300510740c24004408940c0ba040c4401002c40e000c00020079030b18203151103040e6407150000c071000e6441c5800442c3d00c03c054062094980d030b8200000401617404000302c140f0050508503040c50781345002c40c00c0d111a00300c00e03401401812410610480d07603031108820f00140d1030803a040c00c4103403902c4c18228072030460a44011b10760701c942d10006c180150002150703170486a200d00280300a03900d205161003079000a40d040c40101c0c0c41701209894660080302160383c042c0b1f0110449003450482c8200402004901c90152000d43e41c3d502480140b207060701485001d40740a800824000c2d00301d501080e034a1044a50183c070300048651003808900c0d401225400075500b02221002d18002c0344803164a0b080141d0303003248101c1c40c0a40844182d4000c1c062144c81c1c2403c44030540d000c20b240d54042c0d8141000001801200c0c3e540d00078443c0f40d548a104800141003150f00a24280b6101800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 92611043 1250 92609793 92609807
    0x408010b1302190309080c010603032705010c061a03240108030a080412030209090a0605010e09060105040b0f071502090108070305011211060c0703051f0608031e070b04050303040201 80
    0x40d22500e8010407106103202d02c42c50580c040e80c0194600080c00032582c6c00d19002d9030180301c6030390b4115402c00340c1c00001e05500203522541e501003600c02030f0080c20300c02da103210b01989921078540400c40c44440c03280410100e61049620110b9140d201c03240211f03240010307041c40580703c0c040d418807141050100c1000800b040c807501410f100c0b80203500c4e00050160103008031b00008d01c0102a485500700b11003095200e901520070307540b0040e2102d006401d0104006010708a240076050000340030610101d42880c0c415159401034006031511440c1500b0a210382c98035500400d200d40035600c0c100035020006000601100d2a04100c100050721244803000050941a014182004040c1840c0060140c0d40316042e003a01c0c501d5018170b501a5010943c0c0c0030900c0b83c0218841a21325014210000007804404504205020b4026022080d40002e22110900301e405900503103246038001d2013802e41c815640702d451003032510349089103801c00e000759030b070400910802c940840d080d8102000b480210751b04054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 92612293 1250 92611043 92611069
    0x5041b080303060a150c1a01210201210612060203010306140417090f04140702011d0a0b1003050d020c0f0103090506040b0604020d020412020f180f0702070b0408010b 73
    0x914903609007900064105055070140300c6007800c511615105c40c0340203000600c0400d50011442c015200c0000c101031005074244250801b02807000f003401000e00a0504030090390b41c0c140c40305412002140c005c101254105c0302c0c80c001c02c69a508001c2554100345020080c0c4a105070405130f5039604620740102602d441d024141703000c1d495501400001a1104809081c585a8540460f281c86500c00001c03001c151042060307400501d0315403c490801311740c00305c980c0302e0380440d0000e018031200c2c0d0501030b010b82c15032001540140c116502d03580000d8116280c2581003202d0840c894002c980300e40310f84d41801e05006505d00940c0c40301141d0085030030406108041c0f407100b42010481c41c5025203030340b5100c070780c010301c02094a00380d68000790b21aa215815108180907401d803c644490300e07a2006c05c503516007540300b40c0c4100e003046015075940c54008050b1030170401c4080d0b88615625011210460030300003500030400d5025510011074405148000340c4002c00ea004004241446058144540680d1004c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 92613543 1250 92612293 92612309
    0xc020a081b1804031b080405100203090f0f0d060f020c010e160509010303051c060b0a0c06050606041202060c0f0102030a0b2106060607050109080a030c08010f080a020607030e0405041b 81
    0xc100004240c001c0946020981c103141e0405c660956460000c210b0311481d009582d1210f440d0700d45061039540007029001c400f0041c1c44040c138101100c01048400035405c158258003044030819000044e04940100188118038003001d820b201d2078610050035102d01440390a21603006540d00d0001050b0101030800030441900c0b1a1030355411030314010701c1442164071041c0e041c243d26041c02c1c07441012343e01079401003065000d8503440b1781c103081e4004d00c81003004100792009030034100803a00c41d15141d0210740032540c0d140181c08407100980e0902010ba00405800600c80c0180001c910b40c9010a0000358401c10303407002c0026544400108010001c0e9030742066002807503049090008000700091000d403c180202d403120784580c0030f45001809042d0303455006241c50008a6031401d4250503400a520b03200ca56241c0c1d4001e681c99402040220f105849402e440780c1c08021020050306184005209090083c94052000c04d4120085004e03903000b81e9049070b00c40c0450100c08440c0b00103040380302c050480c00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 92614793 1250 92613543 92613589
    0x6090b0114010f0302090315071101060506090d02040b01091206020a0f0513140a0909081b0a030206070c020103020f030f0417120105130213060216091b0c020a081b 72
    0x41d03000034002d0211058081c00d041e400200500c1541e800c1100ca004501107804410700d0b4030300024010302c0d40010000801c85503080590202c0c1c1490614140d0340e04c8200a06541100341058003008007a00803603a80c18188007405001240c0100c1c0d20345080c440b58001c50300565111950200242401d020072031aa040003c01e02103024801d07070321a14101150f801c0716840100307003003400c002141c408a6a01c2a06d1b2189000d003540204207a4402400500c240f03c841440c1000024503003035150104240020016001000010f100718000c07050100018010315005040c070040d50301000c0c02c0c1e88155101d00c52004080c04110410145201010600b00e4105285041c00f03407074070b2000100303113042c011107104090002d0425512401075058070011014814503254040e624030340a0344440c0c0d41006d0142c4a8440200402da132101406160100410825102c001b4014880700325610550107400b02e03801400c4510002d40c80c00c04000100f00310b1001c11005400000c000c0400c40c0d10105c80c55010100864 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 92616043 1250 92614793 92614829
    0x1602150c030a0c090503010903021e0f030409020a030b041406031e0a020603090a05150f0a05040305030a0b030708030c10050907030201021c020a02040c090503060a0b090a0906020d060306090b01 85
    0x624000d40b900121116008110750400103410b0f2040c000903000140c1640c64240e420060503400101c3c0d8a50714500307590090301d1284100ca86841d40c2101d110000213900400041110100640c01404200380314900010168440c800180c00d0316070342c7d4090b50801d910801407040c10b00d070500054029081c480c4045074402ca5034a40c0e292509481c034070107441624080000b0340301f1002403025403941035120065504c0d0607150721894450b800f0603251010b40361a124001402500b4900c9124061501a1038413030a40e03880c0c0134040c01070031408402c69014010b40c540040c1c514802c00c040c03e242d03014400982010307e143d800230000c4480060a04100b40d002c07441c10070252343c01040d884864104443c0080e8400107659043e403803c01c03c00b0300290004d05d08002c0c0100680d110030601d0688004505507883c9885d4450401300b03a034142800607a0149489000c2503145026a0140c24010b2081c04054100a94aa40102110040d6200383c070041d44a40c8500104640e00014601404031482118078040c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 92617293 1250 92616043 92616061
    0x61b0338100c0605010305030318010203040206030f0411100908010b0301110702010e060c030a08071b20010201090b130203070e010b03010308090a0302030a0317221514160215 77
    0x1144190150040340a081d0407080301d4840e208a90b0326030341285060000b07594a1030126604d50040b24140c80300031442c001c0103602d90060007141d0183d13070010701031820360300c0342c50710003411440c050400c660051120749120f00359201d040011411810321386919010914100b5801e003502c2404402601c01d9142100218a07080f00d48160741001d602860904403610718080070030484c1c0706620803280c00303110200e840c0c001142c1c0100324600c5a00356039900040100c8d40d00844404580404004180341d07080582e500c3d0340d242c1404220301d103150510003c100da0720303030303407034900707207440151040388050710144d01007000d6040130002c450040c10404034496403580740141c2d500880c04180001001414001007040c2d0f20b07540c41c4c6441d4040e41d001401c0d03809070740561070040c000745440e81c1d00000880726100040e0701506c042c002e18104889200c800c0ca01801181d444030314601c00c8928100400d80c0e10342c0c0701c0003840c100302d035481d10800030882d03c9100e18138042c0000c1c2c5092840c4901c100050940020003078108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 92618543 1250 92617293 92617391
    0x702060105010801171e010b1e040b090903070314090a080109170309031206041415040e01060602030a05070c09241e090905010e0607030b0a08030301030b060607061b03 74
    0x24030102411b06640e030251006c14003421090140c158403a00c1e200c0d050710126840d104610040c202101c041010f021401c3c180400e0141c100c1c0d00c0001c5400c14031024000c00c0c0240c081902e4400362624681c07909020b100014034000c091303005a950fa0b035684030300074108002c05500c03126408100c0d40c9a420b43c901409419624490a5000362031568150b005c03580350b454942101c078101c000744410f0200c500e89940d4145200030711201e100e208600704000300c5404c2d181032046005844040d4040d40c03803d24a4031080e112540201800c95195614940015580b28188110959842400c008030360140e0045c404201c00102e81c1c010b00000301588008800080d07403400713400219100f244000c5114032850510a004291420103a059802140200181c0700d03415400769001d01c404590ba94a1107484120a640c5d90100340401400185100f010420314500440500f55161043c00e000c243c041104c401300709074040348000a00481e0311448031011010407050398ad0390303030803d40303605044c5c004115034510406 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 92619793 1250 92618543 92618563
    0xd020609060408030402011b02130f0c0905030303270a0507060f0801050f090702010e0106080f0708030c0604060506130f14130209070f030e03160515010605040911040806070206010501080117 84
    0x3005a001030245200d02341400e00700580e40042c01e1000c08500c0c02c0300f51000d0404a60032046075031410006013400c60141102c0c405a500140081d030440c0c1c0c8400707c01d00004c1c401d03030021a0007545010414915001081151002c80c4614060841d05181450140513164184040000d0107003400c01440381d170f120010342e10020070080b00d00c1c403140d4442c690203070700510036500310700815420f00501151942c80022a00c44121400003100c0c01c2c955102c183c103403240603000841000e0740003103004c2000300da0315400c026009440104111000380070036280108903a000c01011400c103032108075102601564807240e40c1e101074040d11103042d1410350380c00245520740040c01e400500017401d000b048581d200368810340000c025202200d40c2e483d07035001c00101285101e0303070484007880b03506000d942a81181c11030038101c990b01d4580900389400e181c40080070345060500084495402c0c070001800c0201005200e00840705500070300841e5040c103000518042058200482074520a80c9070921a035002500c0006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 92621043 1250 92619793 92619797
    0x9091707080304020d0609080a080f010503070305100203070225061b0b040308090106050406031b090c0206010314010917030f0106020606010c030503091e0f01050f01030c090c090e090d02060906040803040201 91
    0x450aa06d2a1040c000c3c01031130350241040c1c1c0b01294000507241c008c030100d4001d000d0b4203051861a0781c0c48003003690f544498040100325801511003d04c81e40d60303680281d40c1140190041da481c800018031081c3c42c040d02d4000d61b42540d0890b1004201c0107412000032000003105c0d0413262905101a2195814031102500060810200d000025030292007903000e4806400000c00520030241e5900b08001000030802c0f40004501001340000390000b02031180300458441742e0050402a844d5458481c02008162a42231895488040d2100040d41000007140c0349940070140c1d0362a403c000050050848058200ca802d540c4011309000c09aa04590414440d0390300d8a01150390b90394420000781026242e510301910b04050503990400d408000c984814032004102c0200000d503200f503600000700100380300180c160f0840c01c4080c018008182c10103480070360b41c6d081080200b0340d03900441601c801d0031070790441640c00803400720340110b070705001d0b0382d0300000c42000038800c500b41600e40102d50b110250000741 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 92622293 1250 92621043 92621059
    0x503030f0301060809033901020a0207050103150f030f0309031b14030c0312070606050d030c02031b1c03030e06040606140312090f0a0b030403030b090c030702100b011202040909170708030402 84
    0x80b81f0203404c0b50140000e51008025900c50b10701c070002075542c03411401014003003818014048040019081c1d41c0088440310741d034444603c0d10f50f454244054100300d0040e001c21040a8006c0b0209060115049000c0e1301450303440d403131030700d402d00700b00d01c080d4024026882500800005c020b2030390000345402040e4181c05525645020f50300d021402403806034002c5c0d401a030040c2511052582104001c240c140c003d40c1991900d51300000c03111902c01161a905911021f509407e0000c03010f56880703421304503c603080c0080d8032000d024510b80b420008450407203409458038418030050f00825403000c2d81000580081001c940500381e02081c81c06080f590b240145010300c0c1084083d0303074124164004200804c11b00741d6074285400d0050160007114096401628104045122003c24608a92040e1074982c0601290b5000c6041d41c005400002c007490304100d10a0313446501162248000c000030107019000082d140060b15040c80782c2410309809813500c0b0424080480410381c0c910880b64016030440e1801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 92623543 1250 92622293 92622367
    0x16050103020a09180603290f01031a04021305190c02010605030307120513090b03010c170f07180e040c09060302031c02030403060216030905100905010c0c0503030f030106080903 78
    0x8001000c8690018142c41d4595888401d51218010803504000547d1262030403079407010b2004110041c00e210081011840300082817041c604450150303000f5100822200800001d03441000aa070b03070170b460121070b0b034441700d204191102031882a07000b5400c0d140000d100b03051401d00001d889002d44903000e820020300c410040e19a910403000c0340c00d01211034000b801c0c0c5c5501c4102000c020045065264000d41c40c044010350428081c4d81461071903e040c40352904c980e9076141c10300421680103401c000034018401c002846000354503400401400ca040380c64040b500d003c0c03d0000d0480344030303401104110701d0b18205001680b0045090f04d050b040d0300c0200d84018910403022451446035a00c09130000d0301c041081288618640103410340d1174003035503072000b201d030b00c9004108076802480c1005011440a03c402c02403540140402420f550007807c90780300550f91100400c1c2190b1281c0c8582c81e60043c00801804030542001006812410460045040202c08188401d0104004400d22107140f0494050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 92624793 1250 92623543 92623589
    0xe061f03020d15020c030a1205010b0901110a170a021005010605040b0703050408060103030306050306070f121a04050403080f1506030403210e030415230a11030a0216050103020a09 79
    0xb6601c0d20803d88003150399001804000e900c075000300e140f2000040c00c0d02d4000e105039030503002d040d040e2114142800e05c5c0c12450801500c041c007a2502e002c07410300034138003d980804c0164501c0014540c0e15030700795a4440785100000d00704400d6440c01c00b14640f410340103000312607010094606441407400400c0d41c4070154241643c0d94011355014021070300c58103002104041d0b142d0080011118260103d0380d032512072180c01e440c05801165181e0009405181c02e42059420b13401c07003080300310503a00b241000416900441c054940841d0241c022490407010310048100881400354000f40054244004100b400700048462001800103000c028503099002042001d01c4542d0301e58070904101049080b0046580d20340ba900035105584000361489000c144080c02805030300541e0940c9207204c1c0d0034142c80794260b0702030f40080700c0c041c0c10050360051442404100700024401c48a40386c00030036031303100c0c07483c820065500d00d0741140d4105401840300c1c920035500600c0d940c003600c010400d5450310601d50480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 92625899 1106 92624793 92624813
    0x7120e0108150a030236150405060a05060a031a0109060203120405010b1201060302030105011203081501020f0a0c091b0210050703020f03010303030e061f03020d 71
    0x6071903041684030350200050000d14220b901900c98000c00d2a000d1026131034200103d001c1d000c6c070094600d080d1640100c1841089001e01032503c02c076100f05000540c00d00e24000d98480f40031a00780e0f07441d01c0000c4084e084c040c00341615002c002030001c1c00340c003076610051140e4030050b01d410039552042c030401c0282d5120307400a500d03090006503481d80a4000600c2504c5556848440c401a681d907101c02110859178203002003001401d6004260866106034003402e007074080000c88400098100e4a09079001c031501d0211200f5011800040c0c3c140040004115002c0c0100c410103010401c0aca292501500ea80038000c00003041c2c10b03039126501c081c1c8041c501000d0b078041c00b501d005401031900b005034844541d1801504180d40c00c1c0805010390000c2c1c00440c007090300e600da8042242000c0082d03d60198002200d882041c1c541843c0a01c224030798000a40a0141050700000740300340c07015 = true := by decide +kernel

theorem cover : BRFrame.Cov 92446043 92625899 := by
  have h0 := BRFrame.cov_init 92446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 92446043 ≤ n) (h2 : n < 92625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
