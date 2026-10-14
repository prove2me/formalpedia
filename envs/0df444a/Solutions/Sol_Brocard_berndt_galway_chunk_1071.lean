-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:06:37.510371+00:00
-- url     : https://prove2.me/submissions/8308f626-be9e-4990-a032-5b08b4c5fda3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 192446043 ≤ n < 192625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 192447293 1250 192446043 192446063
    0x2120301080c0904060e01020a1806080402010c0308091005250905011407050c150403110406050603040605040f02030d0201020a0201060e1605180409151508120c030903070e040c0e04 80
    0x1e0781d030900d18480f0740c000e03109482c08903007000305000340342c02c82c0c1040900c500040c003065082038480e4070040040d405040c0c5032038a1030240c542a000a005070200180c000c00b0000900e002441421062111020024200c042031010b400d0810f82c121078603070861090440400402e080040b0180250400c0003100d6040c1c41d02203074082c440002145540140000707484600800c030440045603203010081a8070080590842c0d00c4500b5410030b1542c1c203910a00141c0110700e010014070480d07680d08280d03948950700c130078041207235500e0785000c0c010a179121900a400d07104507103100483e03540640240500c091640d0003003243c81d95644100c0d00890342900c01030048422100d04181880c800ca00608040041ea89924ad258547e00082000c603900407100b983c440e20322180e5103841f00094018000c0e107081c2c3e0750030f40d005c1e00c2c02c002c01c481e11101d81141d1440b45100000c1c0700786003902d00f402a60100ca20003415510002e07599210f5041d090303022141158503004048011600d03175003003a0320501a54000124a03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 192448543 1250 192447293 192447313
    0x5040b121b0f09010303020d021002090d081b01111c1802040209150a05040e15011710180c0305010824180604050d0206090109170a0c050601030606060212030108 71
    0x101a03062075019964001e9210011a02c2d2a01c8440c0c42e140294820341c024a0250803440d80203040030509003402d01c500e40108000d9010f5510500c00008807030f0400f03e5945d48403422004d035182d081440590229550803d9440d4218080d40c0d005090841200210340b03071201214100d440440740003d1144061003519018a8050b04066001d060305800145c10745058982e85140040150042014080080d40000702440488021441143c001d00004500030181703500c00700103004c04803a07003102682e0340a0400082c0c07803810140c0005004203800b449407c1c1a44c2c0001425015140e84038040b000b00742420f00000d810000002d06001c140555582141c14602d2011809000c0c00040c1000414000105500c041040c0c01d204850007503100c2c02c018160b8035070002010342003040040a88000d03915000100c00464503c41100c81c1c0f01080104003545d4404901c130554060360400b00c040c0c00ca00c65040080300300522039102c0c0064172155004c60340aa0600750483e4240d220900540ca1070b504045140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 192449793 1250 192448543 192448573
    0x2040e0a0207020d1a07020d1b0f060204150e0301151a07030e18041a070c030e040e0109080715060308160201030e03130513051b16020d030905040b12 66
    0x2e000301038070003807103030005840c0d40d12044048500c540e00049500c541005109165404001e44101d0200c1424082c0522903c5000c840d151045d00324007a0040f01c0c400d40320401c11003d0340c11a07014120445a008814015000080c242e40303802c503046000b580303420118203207404071048001c2281c580d40ca0705c41d002440e4100f41407040d08010402c40502104080b0500190b6420309c040003810300032001b6060070314085c1041c1102045140104d10340711103190034031200c02d5008065064482d0141030800718441c0b8034000c03d0051032a02c3d644845546400c2d18502007201480040c840d080c02078841203d0b00d0002c102a4044600a21009140030800c00c040220a0310070720300d10441e1030050400017883d000c45110141164858640d220580ca6002014020351a14540d040040340c044142040607181a120103c142c8130800e00d940003403070021440c0040f41003a121340032581759000c0d00c144400320b00740c98040c20b0446a805954840d40c100b02030003035181070030980c40f418619540c00074a042c411510305 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 192451043 1250 192449793 192449797
    0xe010e03042306070303050411090105090a0905070509040c18050c09010c1b08070611060c09220c030606080a0218010e0d020301050f0906061e0f0604170a050c0402040e0a02 76
    0x40100350b00d0b01c080210540c0d100405061014065100401c0760300c0c10340313030a0001000b890079851103a20008014461901d40341e03003523580405d841c08001540c80711401d0a81c505007040d4029940b10120800f000100b040f040d0f0b0900c00c07a00354160784040c400d046a40002a100c04a40c0d985080301d0500501089610807000c02c00300074000c0b055421070000b0b40a080500c0c04450f0006071060740000b1041017032036482000b0701d0500c0020707005406a414804100101403240030728480c8521024005410080d944500c03940404000490421039140d04500c01381c0901110310940c1e010414044c0096010f500380d000312826240500000c210280c244e0380151000c0c00703402140341c3c109004ce0113500068600b4440c3e02c0c020042115114142d113020703500700f45802c0c0000d00f414000c031200030320b13081c0424007640c0c0d0b2203a8601c11984018486080404140d0030700a03a400380c850603412683d081d51601c404508440320501400130340307002e010078105010503403085100340039000c540c0c07400180d030b040e9007540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 192452293 1250 192451043 192451079
    0xd050a02041a0405041109130b010b07021f020106150c05030304060509030d090606150c020315040303270c05100f030518060c30010e06040e1b03010e010e0304 70
    0xb06203803010340c18012a084034004c40f02107400300e000f00d6444c0002e01e00342c44569031222880d4551140c04000e665072001c94030040c41010310074107002c5000c00440d0780f002d02e10181007076032540c0342d030240300c144000902900544c4030b01514224444150b40545110f00b030b030f45505030b80080055103152141c1c1d80701c1c0d000700402006441907010620207a41c03d000e2600882c58201e0090030003052550820315100400101000c0c0e500500404448100060300c01150740200c1808001c6000329030b40c1c0e20305054029214501a0300c0c600282d491b4440040d044803490740c507200d40a40d49400c80c803510f61f4240554034840a010f140401d061707400d284d00c018401d40182e40e0018078031141e8040310307072410755642c070b40f200a541c0d403c2203940214009019044400c0f1104d1500c80f541e43d00d1180e940c030591144140c15040c011003034580c07552070012300d0948498028800e203815032021140d540d040480f0154644c3e07038841c2218402d5080092a020405050040700d42c00340a1030b0107540b806180c20715455920465170 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 192453543 1250 192452293 192452321
    0x1802101806051602010f2021030108070303080a1e0504120f050d1104090908030f1513050c1b01020a02010c0c0b010e1b0a0e011205070801060e0a0810020a0306050d050a0204 76
    0x81c18140c0702081011f00361032004003c000f4050544004040c080c880c2000004616400c01440104000d800010b9a801201c0d0541400c250755210106800040d003408501c54125a4082200108203900799114510ce1401800c1141b1000e1013201c4c00c44643c102c030f9a000303000402c113000c404c030300f0004c591040b85801d80d0b060706c841c5441d503201850b0003911559807051724030490200400c80281c0d1140d224662040c140070011006c0d00c5d0280018846084007803542d04015900c00c002100310301c039901240c03d449880f079800e45418203084070681c081e40c40b4a445500650911110141c014050108512940e51000f00e00c011607003082901d04e0f484100500300c00c0e0071307030021201c1c1049070500802040319069a6031403440711403d40c4009820000d000e401e41071440d1070041003040140d800303c04c09054030345a03c0c0c45403034414000002000c20085030060030207800390146101c01076410b0350007010055404d172402d0ac5402d580e00304200c0a090203080103050780c2c02038807030280180341590140200c14107079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 192454793 1250 192453543 192453557
    0x7020d0b0a141311061c050a020f1303110d05030910021e0601030506070906021519020f12010509040305040312121d01050a02090609041802101806051602010f 70
    0x14049a44900010394030000c01140c41c90b848000d0000d84410315000800031782e20a454450a4400402902084641601c089644602140707511047d90100c84680e814818429100c050f0542201c3c8030128074071046841001207a070500160402e1843c19070703540c1c1c100c805581000e000c0002c1c403000c0c0304a4403800d4110b0040f0041c2204401024504018240492006000a40c1580740452400d2000b8001c0828424501d1003000f409038005041c1180c0450305440074501d4407045009082da1301c001e08041c5145001082c1682c0490080d805443c803440001140ea040d640c0e503030240f10310020251400340c0010010401400820304140070800d15000714034101d0040380c80440704a0446101030101d00ba60341d06205040900c1909008031500b100c030fa000110302d80100341d0002841481210000fa0046446800310200006000c0181c03d20640241506411002d000e000a2010440e56448440000300c83c2d0041845403007182503800410b4552522500f610264005603000c03000010000104900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 192456043 1250 192454793 192454811
    0x60812040504020d0b040e0d02060705030f010603090507051e011404060203090613150528090501120e010e0303160305060303070201031d1f0b01080f01050d080c030705030d050106030207020d0b0a 86
    0x250780302e0708408007c50f03c05810f5070f0a00741c00c000d0405d00301800300000c205040c8240000e040d45141001d0440f152410000703441440c03441e1490809800e54070a03a03010403214541e100c45a281c00c600d50705540240c1e6034280c00810004061118010350290b40700680c401d00500703000b41451300003840e0300702e48807120f5805c8540c1c0d8032103440902d403441032910000b071010800701e9901400d00e1600c1001071240c400d100d4850048a801400082039218a40c1000368411000152850030381c00f00090650000083c00860742c0c11600075a0780d803095444045d4030105400030079115101703100300c0b0300441005003c1d61804101e6001100503244131300761410101d25840c500491a0010801c8140844070003402c0b50910040903a82411a20300480e41c1d41480b203c14100500c940b604081c10b419900c0c01c541001048031103051600c2e840c00380410040b050f200001e01d400601000001400b28112440400d00c016030322001d04030305900541400035005015100e0307000010304288800395125031850030008030000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 192457293 1250 192456043 192456049
    0xf07110708030d14010504140609060d20030706170c0901051c050a050603031201030210030b0d0f170415030c120603060504110d05060403051e03011701060812040504020d0b 76
    0x112030800c3c14240c40c1c0d11907869128800c40e8500034010003088504000e141070340030308000c5081000340028880c4400c600002e203240e6680304081c400c40d822007101d1100042c0e03000104000d9100c1e01c641d61203485504400912107110703008403d102d1301c82002c800c480da01d54503179114054001260b5a81409818410080c0c0345052002c04003521004040c08500350501c00e20503402c980c00900342a0080c1c004001420050045d032041c0e80c1140d6059850f00481b60001100320000c1045035201c1e070b0302c680880b1111061001d007d080c546c006014141c41c200039866031441c0180c62255101d075401500e402140780b80f88600a40c0041d41e4443c15040c0100300712f082c0411035040340c0d030030307041100d91a0740c40f004e110602102e002c24043c3c0d40b5050300c0952184040c0e4884507990716001300000d00300000020350f000c0c080343c45841c988142e001640700741e80b01c1d44c640c03d80e00d4010361413103028a1150b1a0200020b24042d000490303440c80d030b403c00300c8240352900f0322041c08069400800c02c0b20203191148070186941d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 192458543 1250 192457293 192457297
    0xd02100f020c060a020d1d0303090d060b1c060b0102060417070218010609081002030403090b0c030706020403030e030607030c050f070c051201061a04030b0112020f1011070503060f0711070803 84
    0x10013170303070180810445a040c05458480c0c40e200864034400b085041d0303501038600208032140500100c0d111801641a840c0c8840030348510103503d40c1140500041134105030ba2400350355007940c46a0780a009440d104001246c7d110400c540140c040310710038080303400c0c401e02c2d04001d00b0710a002420002c00440034100300c000201080e4011400924075080070400303071034140080304078111042025807940c11700e0f44008080f40d909020301c0740d801100042184403100304000b00c070341181c0e011106549407a9603040c040c00070102146c2850080c06104001151544688140e60041030b140c5c44203800c011842242c000d00d50860b0710102c4050180103404076107651a2026140061002c00012801c68207002e280380c4220014500b89958800620041c0001010340c2a60b6065a0107641d0f6006002098000034071500c440c400000d0308480380074400300c03080358408418a20202c0510845817000c1d540c1080c183d466208640d0000324440546c04140942e224600303d80d40048801c3c1161141764880d15081d080d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 192459793 1250 192458543 192458557
    0x3090501090c060e0402040312080603030705070602011d0a030c06050903070501050103080403170a090603110909040f05010612021f17010902040f060c021807030612080301030b060d02100f020c06 86
    0x1110b0b5001d04000d5294407003540800700f6000e9074150704040c51542c0d050451390341c200200044c024071100184250301d0400550310015000070032694216900d00d0060300030904010b03103140d02c0c0681d040a01c640e1800003400d20400750f041e030320907041c2c203200e0300c0c1e400040101070b04030b01d8107000800607040803440034002c3c50302031070250352419a07079441c40c50400c9030b0f8408003140200700700051003032914030390300300000344100e54503802e002c510020f41140d403000502c5421303100d0b580441c034002888240300315906100403091094008010585c1c44051948000c40505030088d03000c132402c442e14541203152482042460414207000610014200d00c809106c0c02c00d0f0040300c00c0c15400304d010426481c1036800440104a50b0512000c011102d0f004200e4070300c00c1c4148144120701f44004545001d11a0b40000010b00110342203410480c0340d03140a1f82c207540284001d0302e2a00329080410a10325140c010000c603907a004000055042980707400b41d4414030724100750705c1903000c1d88103445065164031000700b0304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 192461043 1250 192459793 192459803
    0x1104150602030d09211d010e03070e090709020d020c010605010306050f040b03120a050a0801141f1413050103061508040f060e15160804031409040213080f06130c06030506010309050109 81
    0x101d802164246c1814010701066541008464031494640780c40120f007840549040840da04825920081020b240560036808040207902c0011140b44407080b42d80680714140d02640248800c0d6238031001141920a280200d40c0d000c040c2a642d04020310b01540010590b40024040e14110300d91031400f036070590000c03951140800c900184030002c4680c840f45150250003c1d146080c00c44142c500030a00c1307142d8190481c071240600c10b00c2c9001e8280070705d080d500021110100d5998584e22042d03040c0c0030012a1181502090a14030089160440c00105000981481e0750f84021542e598a91044020103408142d940655880941460103824400c0511054034030300c0110185c1021581c0c40300c00d0315000c84e59070800c4408824070000a0344a403e4202c1000404003440c0c0303400b20400001c0080c03049000d15802281c0d000c1c0001015203000c520303540741030800740c02e403915130f0703202d101c0b1502c0d0840300340000b41620503901c818030105029902c06900010185400903801c20250348850841d007072008180e030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 192462293 1250 192461043 192461057
    0xf0204060309020a09020c060609150a080c03070b09030a0320030307031b0206040201021f180507060e10090605070f0614090c060f09040c020f06041104150602030d0921 74
    0x1c19401c0043c4c04800410101108510b010701c0130400d10380303c00c000707822140b082c2c00382c0000c6181c07c0890303121103c0c0407500501c00903c8603941d840341542c1d810032214480c0030b8040d10000182d5848c0e00e0701038401074400680034103000c1c011650b048035800d011400c1040480e07012200c005241c0c50030405035100d10b0150320005071629500c8948848a4464410741c011948840200b10040c1d9002c1862600c1910510f1a0000c0780d1081500d000039003000740300da94440444c0082241403000002d0f5417030483d000307600e40c001801e000406120049080604150128441c61010010700d8490302c01810594000c07071118074800c0d41175442c001a5180e400303080340d001039170a05201c03083d00705100705883c03040d045500619281039484221810301884089611a99031400c1c00c01e0041d00a2050600354405070f800d55806180c40e2414584800322a110980907a103008241220741048400074001e441c0340340c00542c07d12404d102c00f032001e041c0c1110120dc8865501282110f007070621519521441c0690b00e81007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 192463543 1250 192462293 192462311
    0x4150503061801031e06290a081c050304050309220b0a060c110d06090317060f0105040e13120c0501050c07020d12020109080a170702010e1c030f02040603 68
    0x4044055902640074940d4140e0004100068505005d0b560102c1c84540914000d0050708140006007000304d414801900700309541c1c0b5031051b800320110041c2400312404000107494040055075407072880ca802c0c62095845650586981c010030182d50b01a1003a421030f8030700039401c0041400e4410302107000d01d0056001d500d40098055901401c2000740f0301f564104851840d00304014003c1b8404034010300384044141d41c409243c0c9601a0b100746098000405010ba103200e80b5004241100c86039050b0244048900800c0c00ca06e407882d007461001d40305030759403030070301c0c1c1050600801079101500a40034102503000c0389c2c00283c400c4003810280360319034841e0030050025042440c2941c4004103069000b45081040d040169a802000d05580d60001d80d94003280c80e1304201a40100b00d02e0b00081e01c1400080f5280c800075034001c4814803410107003040c01c3c0894941d0b420503801e84d03444008482090304840d00100c95086e1740704520361050514500810001c1854000d038049920a40001c00003c0d2120f80907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 192464793 1250 192463543 192463549
    0x60f1404050f09060a09050a021503010e0c090904060c0c050a060e010e03030c0a11030409020f0d0b060a080a0b0d0c090f06080a030f0f0509130603031b020307050904080415050306 79
    0x9650b210a11120051451821940e06070f10b5140c000c0c1903142c440e607144c090000744007003009100800303540645881c1c1081200395607010a80c000b407048103200308520b00043d942c280c0d0501610300718035001d4080c04040e00d90ba40d03200c001d041c4500c01a01004401f2001401117502040311212090044000058401e4214051400d482c1b0b0703680130340c1d0340d98401c01c1400030034a10301c8211a400e00707a5181c129040c840402159043d842580d00401034280080b516903031188495000700500c03174030b96070704100c848803d0040c4695402000019000305038120700185072080340c3d400c40e00f404400140103c258680c00da803400d82848444c0c02c091441d0f5610403010b07001086030320031103024003070b9a00144000a80d40c1d400618920303100190b5010480010103004200c0d0140c000d5641400c0000c0543d604196a801c1d1399008180911003580080c00800c100c0007800704840416076070640150250035850b00b0041484403014001c1c000b1241c0403130030000004c2280000e43c0b00401507403155a4142d580c1422010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 192466043 1250 192464793 192464801
    0x9210a060e060a151502031c061805040f0f061e02030a0e0c210a080406110d0311090d0f05012d05010e070f090e011d0109020405090613060f1404 64
    0x2914015484e00a80e0380c5001e0012600300d08444100303200c0380605083c03c03030880c150300401c608041c0d8151401005d0000300c3c8540c11500a41c0c00307419507424110030070060751007501c0003518041d100b245891a00404949041c00b0428601d005001c00b082041003408261102954030f0004040719074080203010b080240e9004d100c41802e10381004010310300c84c0b840080c01c0c5140e9440341c0403502c4001800b02c2180c0d1802e214216280da0000d0303040b901c4541d031703200c06010300c101c0c030500101c1801080100e81c0198000c1c4500d084c850700100704941004031800034004500a021000d071940010344200c1c100241d4240101c2001c050218810650215080000300c1940201d00342c20209509100052109929203524168485090b240c4661503003522070301540ca00b07096030889864400c10380004103401e50600c40003103040c001e10b201141560f9803101440200e009500030158002070240101d102450104c02c464003500c2d4280c0000344940da1210030199804e0154000b240c4079a81d0540011389180c5486 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 192467293 1250 192466043 192466051
    0xf050901080105010311210709140907270209130c0801120305120727051201020c07030201030b21061e0714031323011506020309210a060e06 62
    0x700a005a504681d22410040e24059001d0f024154000b6200b00641d00c035030310b00140d210507400b43d5031040d84507a0304c60050844d000200000b10305440c040340742020005110412501d00c0500c00c2401c01150008681d400717001041c4d019015001e001c007402c8d070b81da04402071007005507246c0b000030035680c0050003078580401680004110401070742200b001c6078214040303070500c810211902071203075a45941628120701c04062040007443c04810781800100350a611000d88400321400b500e000280e0703004609030300c9118800c94550304045c90810055001c0d4204200002005040c20080c60411204521840102d0440c0e00980d0200d005e001c0d402d481c02e5019625814505034247c1c0c3c034504040060801e000f99108003000100c0000091120040c51019401066001c191519142459441c1c49102c941008154800e5440c214048070004070a145c00c0c0b0880f40a40c0242d800c00744031f1000c000450829500e030540f140d9050206050510003409603e10a03440360000080742100051300c2468108014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 192468543 1250 192467293 192467309
    0xc0601120308162304240e030703020303040308181002070e1302030a1101050c240a020403150b030102040306020f0706060b0a020304091508071203020607020c0a05010e030a0209010f050901 83
    0x311102c15405005005058840300400311098500b03440444d83d0b104d65031014108054801d1441c40c244000d035200c1c21114060b9035a0700500d05640704058443e0302600c0020741c50f5104010800001d103070301c2d001d00300c4000034140c41c107131032411880400d02c000b0f6594948801600140b4050104528142000f03070407442c020b501c0b00225010340e0100c2d64400002d007001d411203c00140f641c0c200c1c0c0c032900072541c2c0c0e01d0b40700055440c1c8410565903034050510180303000d0314203c0c0c40d80005801807180d1091300c0840f074000002d0002e8040521868005003401901e9a8043d5000c101c0400403400c43c2c002000c1807052144000d940302210f041500445016400903200700300f0801c01e801b40e03a44d000080c1c034191610072a0014a2802110158a5540c0310358010308440c0200d200024414490b24400e400190180d0281ca0035903441d820b00300e88034020b0030016a40020701d00c0090125520611116142d5000581160124509500011401c0d403099200741c80600070351a0501c1141003008080e0b004210b12 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 192469793 1250 192468543 192468571
    0xc0602060906091c030b04200a0207080d022a04060f080c15030a020a110a060204060f090302010813052a010f020303010b04050f06131410020f100509030c0601120308 73
    0x44011149803240341c5200c07a042503198455121a940c495005d0f007403581448d880358651100b078604903103441c0c000b85543e00c0076010340740380040d902d078001c1031015800c506940640f0004500c1041c522a09801c070340e42105404017159030043c0c9031500d10813007002e090007041d0b1101041c6030140d8185040d244410143c001d0020b5402c4410088000b41980c3c1c000f003a20070090703103500400408880701c0c40c0d0410072010910421801e002803010590080c02628101e54414054520403401600c0b0782580d03110007400556403500180b200c0342500806090302d44200252951600d80c603100c80200420b44411510a0170300b140500c7e425070700200070081940c010b0000e9401e641c503244d11081140250b10426010300141240442e00b0341c1c1d00700840b6442c584070440080081d071240c2070026114100c84906010f41864006512281d00020310f920147c00240014825440c0d030b44000000f500014103000710354881805004007c01e0203121701406001c0c00c0c801c4428540c01c9060003440c06c2009000070b44036840c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 192471043 1250 192469793 192469813
    0x3042f0906030c0108040618020411070c0501090b0403030320030f06030d092102060c0601080303060405012102010c03121e060905010b07030f180303120c0503010b070b0a090c060206090609 83
    0x224617095807242e0000b0001854440c051a0703140e0991150758020740c007524101000c01041c0303071007025060040c0240c02e0f650740307140c48400649001c0058010b140c1e00e107405110070070000c1d119401c00c405808012040d0f540544e80d581114415030010b13200002001802401c0100302d080403c1000802c0c4280d1a10300071f410314020100d420740c0c0c8900c2516100c180c2a602c14000e5480c4c40048600c410083c0e011600d00d503959492503500ca40003a04c083d03206a0401c0c000045800007140200c4103009400d10349400f81c4155401036800c0c0808540c110103100200d020070300e54101c07900c2420035036403100024041c0d0307038880c1c0c17945012660340c2c1c0c2000c6115854140180403039820f00c001e50703130f6003580b60420b02c0454040c003400b41c034010404010b0032078460003010040205a0300602c04100700c003c100081c01881d40403a0706441d14003090103112640c12040c040540401c1c1003c00c1242c0040001c1ca00240000403511400420a150742003800541e110300148400d1140803c001c650080d400000b03400c0c0180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 192472293 1250 192471043 192471047
    0x50c04050c09040e070b040f0f09021905030a09060609021c06030f020d1a0c0a030b0301090308130609050a060c0f09050919240518190203042f0906030c01 68
    0x30416880e000395035404031358a030042c00304442c0b4003174a10b8100c8503407210303036400130041280d0b41e50140d48651610240009115520741c002d44e024a80c0180e84001600040a41103447c0c3d080200310b000c013141c0300c1c215040401c0d401d21a507005070800b4030000d030761340c1404044d20303403900c8043ca62124414940802040032550000001c80101d0b8105ca010710040e10b1800c01009640da442c007194590340880007440469080f1030700820f451481e90300c3c00c0c000403850100701805c0f52840c0c20043d0200d484400002c01000012660200c241d10404002807041c045444003850041800c904581080c0d0380c0851140d07890304269075040070f2285161030401141031001040b40070f100540701c0940c40340f0382d054003008c8102d82c3d000300c585140e0030490601903800e40e01c00c1010869480c89928000d40c03a0742005100d002a022415100719800c090040d001c2e60070540d0b6100070340c401401518801004001c21410b0040c2081c0d40540c03480364241240510526002c1050715607028103030070700c207174001e600c8072101d40d0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 192473543 1250 192472293 192472297
    0xe1b0f0d020127080106031202010c080a0e0118060204051921020604031b030b0c04230103110a030605040c1d120c0312190207060228080f07050c04050c 67
    0x1030390a2800f40200348000c9250707004040c01c800c180c0c62a4507020000704000d841540000f0413640110440c11017540c0c16a416402c07500c040c481007000506000000710a0102f54014501e480000000000c02d4038583c02001c000c0c00807050b01712480382c0c002900300498507200c820340c045c08000500000c1a00d01d000d14a440b00e9013120500c0f80a041034983c602c06655801054800a43d00881c0c00c101d44a48540d02195203040e9000480c0e90402910204003051880003e0b01c05076151420110707201e14078002a8100d0115010100d81090f0301c4141c002c26030501400540304450031500c0100d50541480208400d0300d8007150301c50304000741403440802160130148000380808041d5510041901003413030013400c01110101c100c0c1c040c861250841000307003281c402461030000720382d5014404071003610100c0e1140f1a512405005911801484400c2031440c64421809102403905000c5290705179107006d4540c1140c04a03404500300403030800c084c81401d218155030120226400c21461800e21040c812034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 192474793 1250 192473543 192473569
    0x1020409150e0403080c0403022139030f0106060c03020c0301090f0204021c050108030c060f040c06050a050c0109081c0501180f0e0a05060601020d050307021e100e1b0f 74
    0x80688000301b02e4100d642c00480d8051a00a0500803541549011000b0010140700d12903006110b11600b2855100c81c0202d000301d400790039603010491a1072035041d441003002c1450a40c0e0706018801c1c4243e034088003446404014507031a2202c0c0b0310444242400f0b0b090802508003540286d040a94010000354202c44199000b54101c40041c2c07509200341c5000d0100c5010841c0000440c40c2200104070800b0010280c20421000d80456074203613584600c550142505035001030000044c460f003400100c0c0a80080c041f0504140751540c2080d8151000e0b40c03d45140d00d4090700e10010002c0c007140909a800c02600d45020074100c24001540341c05240c0320041c43d40c01815130b00a03550281c0845201d429009101000b046408503403200d100c5061040d00c442c029140b4501511440d2104068540103000b0f4034400d84198020b4840c40ca2004102c1d444600c001d044250140200f080d000800300041c4608545001c1e044000c3c0350280704000d611400354240e410007882844108503184d441c1d03544128074510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 192476043 1250 192474793 192474797
    0x109090507090c120606200102040302030304050103240b030f01081507030b0301020c010f050a150b0702010309021809010608071707030f0515130c060c020904030e190801020409150e0403 82
    0x20220f01100211070003002034401d601403e044c2080007135615400a10340b445990f203400c0c1e100404104861040c03c0384590f00c0029010303007003800b041102e507000740d00c0368100c0031503408481c285d052514503142d80c01c41c058003d2400c910780442031040002c4075800060142c03400701300400114000e003415000790031004091b4801c054494075060410b49003901a162141030ba40000c0c40000109101040602401c582d030f880b4051903c2600760242d032207203160b03d048950660b01c8030304e8a402c503001140900201882a0303048403140c1c0e034524040b030200000a200751001c000014405040001c4142440e807141c1c800c40520291010843e80d8502c041214001c84c3e0344221039540304441c0e0b280260610303074286102084100880704104181585211035158a807160781611800707900c4440c16150800918006034015204000060000380a50481c141002000304000c40032007240d40c06001e11500b5801004d03c40c0d40101d4100040d81c10350095418141e1040443d48016040030003204a0f99401000901 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 192477293 1250 192476043 192476051
    0x18130c031202100e1b120d0309020f010305010501090b1e0a0c0c05010e01171b22060f09050904020a0803030c0c16241e030507020610080c1e0a08010b0306010909050709 74
    0x1480381e9501944481b41c186207400e807081200c5480c009401000700e440c0070f0340216046110b82c0231a6210344210b506a400503112020090300b00340c401240d640152004540300c8000d50a400078280e41003010304220b504a682d0204044454a032034045c412441d4001410b11840e500d013901983e070800340043c001140409030080540ea00d00c140c6544c00c0307446036040507a902c00101003040713007071414a19900c042001c05824503c0e07583c200494241000d0710b0707482c002a0850301d09120b03601c0e290080a4200b0b000034036100d022511804084c0c1542e000361000c81c003000d0001100000954284101d0b48020001070020918610f030100b5403541860014110380d451001e040d0441410313024000100800c08103100050558440d9100136005007030650310075000d0311590000400188107903400e0000d40ea4144082c0c4120810141809112040342e2401d000041209250404588803c2d411200404008001090103180300040c1802d012068102e000b0940c1444240b2000c101c00007001400c641300884005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 192478543 1250 192477293 192477343
    0x30a20040609061205160501080c0c010209091f050108040503030708090f0303040f060e0a020d02060307030f1b0f1106040b070507020306040c170304030218130c031202100e 76
    0x40050610342c2007006514901100418041040c40d114030f0200d1164086890903070401128428019240c42840d002449420010b5007a0600034058840103146c2c90002d0f00709003000000030b002480c2140e072400f8441c07800136490245070800142c440245002e0a1422260416445564403444001c141c02c051020345008500494400c0202d01c200b01d07a000140d07522420702d8503200e2680c011440b8242d52040c1003649456840c18041501c9103c690300800311007982c6910ba00f4882203410090a220515941d5844807040140740d004819104a03c5121400c06070250318001c1c2020000d403035514100190302d100342c540248000703915a00a5086103825042e5070b41c80c00100c5841c070907020003c0d05405900c042c44200003a10340c860003550003032180181c0400d109070311300c2c0e034900071403002960124031011400441400010041d420000400520344401c289445000599225074000c48810b810008888111a8103210b5030b4040c031000c100501c50781020080e030903543c62604034030164040c2500008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 192479793 1250 192478543 192478549
    0x121b030d0c1d0303042102090103050a0b06010e130906061502011d0705090f04060603120203180609030a0b06210312061801091a040608010c080c0f031303020a081c0b030a20 76
    0x6e50180d402444407003d03607103d1070056140c0359010b400f19141d0300118040380c9158014034211404c00f4001d444001542d0803d0303143d03006000c20b040142c0c0c07c2c2c1c0d03440d107020038a45006500500000c1540d00003140000c283c0044404058141800301d00030782150906020560340c0c004401e4110f113050602c1c0c50607440d2800c20030001c0015500041c002e200c0b0b41c20b0083c00c0ca03000720290100320440040074500304500000d118042c8111304002d075040e0418111800010720b086941c580005d0003401180c1748280d00e01e518507010080f404d01410541c404130ba40400c000d401088240d1065055505042445501021904400041c01000110364990521403840810140198224030b001001480040d40d50b221030380c02400585e07104c0300002c4400000840c030810000c116154142035900d500d00d03554600c032411071180003c0d0811003c5000725150000031960b40790241032240315039240000303030000380b8540d881102e4030050350304c0c02508646040c3c40400c03103400030070016a9806044c418244414000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 192481043 1250 192479793 192479849
    0x50c010612030801050301050601140f28021c0c0201020d030504060b041e060801020903100e0a150209210d0f0525020f12121b030d0c1d030304 63
    0x110101000701005284285a4001150790484c3d00c00c3c0d008114603120100116124481d1054481c0d206204100078844090003100405260a01aa403111401314401d0521400c2100e03084e00e60059211070a6240f0000d083d014681d01d0003140d052095260803d83e00113912450303001ca0782d0b024150f42e05d0004060094542012103001c60041003040030b144105003419440d100380c500c805001e468200c012411280510803100e651400030024000300c00e1080c17500019101e28004407903140a41826240002d14104404010701d09490002da281c46410080c0700e00f01e072000760a00303104c03050721021080f040000300b42a010302400d850250082c805c03030001030750707240b149501140c41c11401c3c7e0f1fa0300041c5601110301d448101d1003102e044a191060740c0070440d14440060f800303450b9402c21541c4016081e0f054005051031289421190042000551254115080b0800d1500110703101c8030540314140d0700c501d0f000002c52400d00c065105180b0003020071b580b4000c90240040c0c808403d5000301c0002c4040c51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 192482293 1250 192481043 192481049
    0x40b16031103090d0801050303070b010b0c03121306050708250e060a08010302041805030409230412020c0105030c09010509040e060712151a071505100302240307050c0106 75
    0x7109a80f0f04110301ca06607070303d0440c00100c00045107540003080a00e00441200c2001d9000420f9500c6a420810800310341e52040c60310342c0e65413004000102e81c08551743c0b10700c0c2c031805181900380d40e070000900b00300341a10001040b84040040110070400110459000007150f5280c9042c50008041d0a541c192204021240803a5000c580415036011503548600802d050303901c29107003440b4004950440c062000120300004010303030010b010078045540c10741e001c54040307503100300042c202c01d49144180b00f00f50380640c1c05a03110380080c000a01c0940d010801100812003e01e090b500d5490000140141030103042006030410070009090f8900340e946820100c076214440d0705482da5400e20703400180400030f210b122a0350f80742c2000c0030140311803e10400d502c200d50344407988008200000506410301c1e88080402c44403600c0702e81d000c03039040d0301501c6014070034030f051101e003049507045004029901082000d6183e04070012104111210143ea080e40e81240390790602c0c81d00d51820401850160640390 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 192483543 1250 192482293 192482321
    0x30605090109021b0102042117030f0f0702060606091908100204061103040815040f0f0c05040e0c0d0201050a02030403081c060b030f01170a020612090c09040b1603 72
    0x1000402d1800456004042240b280640309010b01c50a001a43c02d034002c500c580c6981040380d1040045040355246e082d11594402d842044c4860b40009a140440d001500c400c4183c400344010049072000140d020354010741d950004081c00d180070000200710307100c0c41042500032a1544041d200000c880509170010b03181d2a010784540000020116009402910400002502d01344100011641c040210b50507204040050020b0300b01030502e8105103000900b0890701e80c40c04102c040041048809a04100d41c4203000c0c10003240e00e008208020360b404040d8841503a00900c1c4030704403c0e03071040200316107180d0a003041601c41458500070b0f411801141c0c000780070720b0000103026a40000e10440c013406006018004c1007526118a170780a0346000450303464a000d09540018400d40da52401710b42400c100d071404842001c0c81590218213103130400301580002201c0381090010041c030611420ba843d80341511140861f10b00741e01d98030390480e0060308100c2e50b11041c048520841c0c2c820307001809181d2040e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 192484793 1250 192483543 192483559
    0xa050f0d06090501020a020705100f0818010c11210d09030e130501031a011815050d060504140c01080708060103021306050c0706020601050d0201030b0402070515090706140f0901030605 81
    0x5420f01d00c0c041d6221104800050141020100e200d182c103404862030030005544080d4010318071031003614401c01c00391084041014000c43d465032a607090203400c5040e0500c0c0d603241200700c2c8070b4070030b0f41ca0b00c4c0c1c2140c40390b00c00c2500c098800072074100d154103640c600c0c00c0040c404100c990207030400fa251221990b548941001881c0c4c100003440703ca03600020b040f60b01c20500046122201e44420381c1c2200d081c003a198440b04c050030122a1b100640c2c200440726080104003004580e56039000581c20b00400d10100da540d1b80740e1007044280001d07500d11b0054030070740c20090301c000000000001d001550040600041c01001700100d8a030f039101e581520588107501c0e24218600d42c0303900b0702601d1500854000650341c841e2000202e0520f102040e09412640040d01c3c50059955580c010740150500e007948a400960070f01210380800c1042100c441c9142c22516211702d541045004642005680c1e000002409503180700c07031280030310305000c480d039505021f0350b129140c4030364200480181c4550b42c0040e03484018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 192486043 1250 192484793 192484811
    0x123060f161524050405150910080d0906030b030a02060702100509031f0c0f0207121b0e16020d0e04091a0c09010f030615180801051003020a06020307020a050f0d06 72
    0x100e00700c0443c0400c0d81508084a607036008003c1540c804441c528840d00c1101417003051800c01c81c180941104050312100c095070b40300d8a1081c80d21000114500000e000003104100b0190944107148501300298040c009038807140c4c01040641c030912900034000c107903424030041143d2140c03007500c000c4100201500c252124168140803c1351802d10007002c80303454501c0101321341d030003404140407403805600909109440e000c01140d03410195202995a025800f01000c0c10f0070301d20345a9400380c13940704a0441c00c1c2c18220580005115001501025175110415007a00380b600001c00007282201160081003051003494001014016000e80900548810041c80b04100340c1a0140c031284400780e27100080f0450a07042101034518070710035442e481c6840420303129010310500c10303050310000d00c4807a103103140e0b074400300b45007103410845102085160489042c0704500c3c002c5030000051205100460824442ea00042d01e208002c0c42103621503030b00f03c0c6200000361988049001c000c0e070048020492204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 192487293 1250 192486043 192486071
    0x20a030809031e01051501030b09070e040b06040f060f0503010b0405090403140d05151c080a0c0c031212020906091e04020f03010503060f090a0b06030705090123060f1615 75
    0x8010b8030b080418078140c01c003031070b06d9511a1142c00d0103100c0c000d2035070940341c40c1d9103400d4414a20218010f50001d0b241c001601c3c2c00d848841c00cc0005002000b02c11130703c2454444000c2104596190901c100f0004000401070404040280c81c2074460448a501c0c0035100c902e020740c1c907002e103000d4211040102140d00480b01c144e07a40f20601c82c5225000300079400d000e2a040010401ca0501c0861280a00500b842d0214200c040500804402c6091000054010f51503140181400f035100315508443c18803003d4001d9840f2003405880454807409500340808400018075a00a0300380c018060702c01d2490f82c4001c50480c0c00704118110015204555440c14000010301940c000d01805001c1e00c9221301050345a441006030910a07503217503000e09850300c440d6541c050289006440c4035414825110007040596689118a000707104854807003600340d0b45140002d0b40005640c0b00903105d140b00b40b11800860395240110343c00c0e601c4090140085034502d00e4410507070340520344032010b02031030319a680308251 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 192488543 1250 192487293 192487301
    0x1120c05030901062408060609060712030e03040f03020d0c0f060306080712080a051308060c27010f050705120304060c020f0a02010e060d1e020910020a020a030809031e01 75
    0x106902c0000d00103541c960111345040c42c244254800303400c488140312010180b02c1c5c03000d5a00480018a036030b02d081ca64500158480d00401001d442d014914065049426011322507100800e0100014508052501600d4001d204280c400a40101071250011041001c02102000504070b101c49824900ea25040010b0040079940580d003194420441c02048e03180710344500403211544142c40b64540408550101c51517003041c10a02c2c40320903c4440030400580501031248200c00044240340c4032561031500c00c90180301e0382140101503040c08900c018590f030084000c1481d1155040866644000d8900145098a072031040324850002206000070024160060603150755a6821545040b005088964503120710160080c046010301641801d242009005000300700035003040011111881d401c54820102c02440c0c250451707600203006003103440c042045802038106440180140525540420402c0d0020301000d085d401d0040f52208039030381c04005910050303041724480309114a0031946113010b4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 192489793 1250 192488543 192488551
    0x17090a091e05040b01150c0503030a020333041a03010908040f060822030c0222050a020a0503040b101205060709141c02130207080306040f02031006030b01120c0503 72
    0x4116424030071400c5090080394052508021811030991a0101c8042000981e644290078014001c100801051091010b0361041c1da01c01405070340c038600080ca900c070404142101d824030003070f0200303010301c590f417203056035024a034040e24001858074814003a5000400b5a0310b100f03603d5820820603508210522000e08200d502c0c0b40802c04051741c44040075510204110b900c5584410051040704440003188500541e25019040011802d030700d0b60041040c6a582c0070080c0810045126110102c042c244106544511729050031800d040315903e000b01107103c081e1000e030802c45450b01040388594110701d60070003070501131141c00000e01c00c0d103800740c0c407207030700312402c03008200c0100000500000c0c10140c0700a44800501d400b0154500c0c8149800070400220f00341c1c2c1201c011501c1381d0320080701d88000c020041c0900d00c1c950b103030302c0c040301088280c0300441e4100d0b40b110300600901459680d03d0010506850031070501003074804805004070b503140036031030043c0041c4d0b0900c4001541c05400000a41c02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 192491043 1250 192489793 192489821
    0x1510180212130f0f020d0c06031b1107030327060f03060f050a03080705070b04060c0b15150a05070b0a06150804050d0f020313030503270d17090a09 65
    0x1507a550884210080c001d21038007a2041e54040f100e600001c402984c1d489110784010007024030701600c0d4a40005281c402d82258000c603903240d94409504407051043d194400f6581707001c6a4440c03044080380c0d00d0325410f100003420700c03545a03618081c0114104940140740ba50180300d52140e07a58800080412505007a10300200349411000301d0520303100a034500c241c03000500340103115807a60380c41880b0760703001d03020950701c0d03000d04540460400c40d150000e1000300601d544a020715282030822083d0464040c20f4503014448000210605440711a03405000c40007200700161518400342054409104002004044840e94820824000300784e611003000d46259640d111180041c40c80c0668180b542070300e01410aa000d1802c0c081440e01c0ba41c0f038070040040ea403040d6414181b49100132080c90420b500121a60340000c00c907054840418120001c0c07403215020070203042c03503040001c1110b0840188001e0b10b00c40300450304518501c0d03e0000c64030700d94400780451240300d568400c0003004190391081c03190 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 192492293 1250 192491043 192491077
    0x1b0e030c03030a08042a12062306040c02060f011a07080d05040b0a0b1305090c3a1a04022106041401090b1f0e0403020d0f0504060215101802 62
    0x1d255005246042c0e00c6049021b80200c1d07803401c140b9107211042d014482214880d0f2600300d01265580411080c40c12106480903010441c18410100400d503002c614102d811584844c0821000a002c0d0301c3d02c904640d42c0c2201006000c00c40c001e046401e00c02d050f406005140c00141407880d0700701580c8003600c103038003440280340309890f0017081e1400c3c1c5518840315a44211003501d5071420303210540c003054018841c40c00300c40004244001242020281070b089107000c4000200004d2003044000904450f01100001551108906e03600c060303a4013503801843d204081400b0019085444010342d42808a40c031240810219104160940d66a036045408546141001d000d510316a08140950b00c40242e1110381c03060b0650362910030071a00074640c18107401c160000940013032050700c02d0040b2070040b40280e014243c0c0b10926080076010950310700710b604c20810104030400c1076030303404288403607585400d401a81194607074203400034021095801200b500c0b0800b842c010201c01c010388c0104444140c0d501004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 192493543 1250 192492293 192492323
    0x5060916050603090606090a0608012c0d1407050c09161805060d200a02030301030c06021207060b0f03030408010b01080c0c19030212031501121b0e030c03030a0804 72
    0xc02d40c0000c1e6001042d69001d44040344851905081183d4050100d40d000506180e0b601079190a4805010308e101c44540c0700d1600d1a40005a03004103212400c0600081226601c240802002c2806260b500c2101b0140800d2040c2000024400d4400145004106000070f0034008601250003451519101c041840d040448910782001d09481007124001032055045c40c4400390030300050b00c041340d0301d5100c0c444501c240050204a400c0505008105a0700540d03d1b9030445c601054600d009070045015584030300503820072030194101b00c9070207503803003800402d109211002050400d00310307003080c40d41030001080c080380d641c005500c04088464241c0c0da134445500c66840c0240c9500c0b942c0c21080032070700290003040c141481810451001482441140d038481504054084203400c10748660a151180d142d14040c03543e8000365801e00d5a01d20310007000072458400110404c0d01550202c40c061001031100e05c1300396601404041440316000d000d0381d03a52003005e00d0042444404980480f4110101d54100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 192494793 1250 192493543 192493549
    0x30f05010b0a06090e0a0c0207060311131215090807020609040e0d0216050409050c040b01091701020a030524010f0e0d2a0612020d020409020a080114030f1c0c0506091605 75
    0x100365045c7c01900030700242802c2442c1180504804002d03440c04500030407a0f09101851f00741100020540c03440542c0c105208d81c07038031781105c01c164005030b841c481c18202d0300004144160210740100d07030b04030b03445a550300220011030007078036807401a80c071725018601091a0203030300443d03038220802003074481c010340503115010002100d80c40140600360380d0080c40f80d07180500b440d034062900003005052508040340c0d2000303641980380c040a00003000341d4000c01c150100c1074240c016103420883d403881e51540900d0044030506103460403800380b810007204040c200d220314050710140600c90f0300030307100c1d40c2c4400503814070214a20007286003031105d40644c8540507500c62010340c0301e02618200c1e55000800a0840300100103504210008402d030350b03081000140c0e124462000302380c0e0514544031242a90300d0071403034040a040341e28400d4002c1e080203800f082814004501c140d0390b100c2c0031030325070001d101c540e004a4501045039002031980c456641886150000001d41e941002045850000c0c01c2d6101e40038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 192496043 1250 192494793 192494801
    0x5150d0503030402100302090a03031107090b0d060b01030b0316080f0312010902090609040e0c010207090513030c1704030f0b0c0403080a05070212060a0204050f0a080601030f05010b0a06090e0a 85
    0x40608107800900105005203440464000124030794507000d810100003800141180300709501c2207022448840c1c4001f1b0b00402800084010b0414600400c00c01c03001c80d0203d01c2e00c2c40801c400604080d61044094480c0c2c5c041d40c895400ca95002e01101d03a80d0300140e01007202e646560060150511800d82543d907000800000c84030740000100c403c0300c569107004c52031340183d00480c1da10f41d8044002e000d1034415480c0c42c420b281c07460300d103c0c0c0100800441a400682044100e810400c40e85040400304441010725682a08040b40d252510100d9103a0301d09001c045c41c1400d24001c0360b100000240001480f811900c2d04041034000d46003410340d5102c44c040c2078141d110702d100040c1458428005c02c80c9881c0180060501240042c1003281c00b801c0d0210070508290045850b0342150798003017400d0107682060a510750070303c801900d43c405814102103200e82e43c0d84051000400c12203015070310b40b003041000e41001034044409008041055100c0b00058260041801800c1c0c4524104001620303100d41405 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 192497293 1250 192496043 192496069
    0x8250e01060203090108071116090b0f010f050c0111030c030f0f0907090c05070203010c080106090609031a060a0801090f06050702191101020304030b0c0a111c050d0e0a03030515 78
    0xc3d03140040d004010741c0c2003000100036406200141944650200c0288400708020072064801c409085c10110190100c41c40350840d6406048090a6006c2a9070000901d00c10340c0220300300340d62111841c000f0070340500301951403400e0b200380120502c19900004400785000d000d00315020840303569a40c1030342c02086021a0803445586c000401005202c40c03c0d030084861540510707025291080a4020a00392003640380f604000034284401040303019445081c80c0d015040c4c81c42d000c0034903813942e2203241c03a2043c89000c4c4898510a01e000c80d0040c0e0354090039200412444000384104490707802c12072107403161685d0564040e41130000080d1418808112050100c5903c800720466040070744840d00d4096209820034150312080101001145814013490721840d113100c0c0c2e69035140d409110007040402c86008100b00359008504a000c07800000e103040c40d43d01964178100d40c03110329400020000d03050031000604640504810302c0241030307051700a04e102e01490050300f010340300c0c01c00a0110b0815204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 192498543 1250 192497293 192497297
    0x25080a060204090c17060409290103020109080706050f0d090f030906021e06040f03030b1806031c020714031009060b191a030603011409030d050c030105060301051908250e0106 77
    0x300001c0301b42c81c16901c60340c9010301900e40d0f0302584080c1011004140340c00f51071400d4418484004004541c5d0200007032002d04050b50280c00701314900003002c0c03c0c80c041ca41f103540c12200046004004a81254800301c0759a070062030007007a0064904002d0010300403806280010300039114481e070300507052500ca000d0f0341d0080d4020551a91141c40b047c0c200300326102c0c200c082580fa21401d1410742e443c2403044440082e5640c0300410303070409204051a041807050708103607640384025402c0c0c0700303134010a0031b604548200d407440c0c5000b048100028100700000c1c059206051500410505001044d841301c80403003416960422060072040011441401900c80c510100c0c11203020390300d24140a201454010700c010b4008110040700c3e003081c03500d0100072909202c01c0c0d4030108540341c401d1214002d294018504100151840d41401d010641c2444140559070150b40800c003040c14030b0508205800003024040e05030b904041188007011151032051046a00066148001188851721951060304840f03140d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 192499793 1250 192498543 192498587
    0x11a060403060e011103100501021c090510020703050105071106090a020f1909020406020a021903050a030c080d050a0e1209060a080402030a15051603090525080a060204090c 76
    0x10355811020303140c0f00c0414901c3d5500c507508003884450321409540103400201c1418081e43c2840002490004147d0702032101421682001490540000c409000d42e5000d03998141c00300e142c804164a0500f865000070480c0d0700c3c02d810003c0701075003c022131040c0084001618181d40314148140e40e2041e00d0303100039601404809201c145440d11300f024100f2040500c030f2055026996980c02001c90f0026840f000140c0c00c40d9419100b140381003080e10241103010303585039240d00d007140c840a5880d00521401000e10001480442c2844100300039a03030881c20158040c4010f2404030a00740241c2941c4481e65078610400d400d2040616080c400e0303411403480600242c0c2400e912910407200b0301400350042ea058000c41c086031000ca05006424408240d40010128041c10b0410311221043c2c1c4040c81c84003014642400e40300080c002268007400c103500380c1e00c0c2120402d2242013284064500d40c2c4880d480d0710886480000300400f0350003420171030707910b41400c102c04920044180c9441c3c9104044031038411311 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 192501043 1250 192499793 192499799
    0x30a06060503040317060d0813151d060f0d0c0207081e1b0402070203030d06050108060f0d03030b120106180e0102030c031b0d02030705030f0105030c0303160f081902011a0604 77
    0x19200100b46e1100c00202601c60050342a1540fa000d41c1c42400e00004e20203065009202514845440480c111264500f8580b01c07411503034107041101c610448240304800002d156502d00003d64256039803404a0b60080145103001a00603686000d584507080380350040914400e04020110080d0942421201c094140d182c00c640d15038602c1402660000d900c19400e10002015032002c0003d404a9006640002801402d140002d800034200030401391003070004640c000d070300b516454680700041e03506040209648201c04c00203000002c20507001042586089800250420704000c85098400030890401c280700b11007069074281c0c0302c1203e111086400c10404240c49503480b0501610985100039028140720741d40f2800c1d0113991042d1a0540002d9012081c8214040c10ba0021401803008400800350314038144046622805551588080316125600b45d10034891104d80d45401d4030b900010b40c1341e0702e40150415071194041402000010340c60b0a1103244400180481c0c3c0320101c4e07005011900b803a203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 192502293 1250 192501043 192501077
    0x2010c051206060415050a03050c0406090608130803090309090c07030c02090702070806010e010305100e0606010e0a051c0c060903020a09020706180c06030c0212031305070e040503030a060605030403 87
    0x1c0007420140d080341c0208400103c5000030b41c504a0110f585c0d59074642d884280c084c0003425101c015251010211003004200b102541010303400048031220b081c83c620660f250420740940d1000345001504840c00007080002048010000744125482100c1c801145e89131548104034500a807480200800c500c0c0b04210301528003100283c5e8090440e10466010944580c01c3c10300b001801ea0000c0d10082c8008014410460300b0712007180400c40b20b540810082c1881500c113a6128009003000b0f051240d90407030407074542c49800507603024160250030740380740103034814966480601d02e032030a076201c0546100c0806c00911898400040b25001800c000c00710707040a1303556000754410f01c821130705265200d030807600b1020b000240743d860b607011320b003108d0300140307041d0001c2c05840181d5011001c64000c01400f0388522000c405880c2c006048084c64000d00e10503192a62801c041a005050441a100208010081c0c0000114400c42c019401840126a114015035060000381d8004001c1520410900d0801d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 192503543 1250 192502293 192502327
    0x714060115091505033102010806010206160f0504050a14011b0803043f030609021c0b0f09150a0f060e04050a0b10020a142a03121c0c02010c05 63
    0x31407201c04603050300241d02c01611104410003901605001d0540185003503680054030f892b0b10140070b0000d80031505d40640395410000c040d40416007800340e40d2500c80c0c4c0c800d10400982d805071501500c1021a940c981d602c280d0b03964403071842c0500007000324074011240c0c042020b0108480390300c0341d0b1250440d12241d031171901c4d030009268010411075900078114003500c100c10000a00307203408040018809803250300182681c0d00358020805080c01017202200b1045810302c91031403000c485100083c101e00380c0d0300180e417640c95158071691140002c000c3c00328422407041126468102265001c0525544d100800a001d01ea8031514001c06c803601c10084540c1015005150300c61002c1c0381c00161440031130300055401c01207600d000e0059201c503192108201a02d4403507002614888001c02d404d00f0360010a01002040582c40c840c044021070240e603043c0c604001007644545407000c502e454400c0c9a4811a401d400940c10441840c01c0c41c0c5414203007030040c464502014440d0359940c1c80c043c0f024500100314 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 192504793 1250 192503543 192503551
    0x7060e150a0c0f03030516030c090b090d080f04080f0a1716080315010e04062403020c03030406020d0b010810090b060d050c1908130611071406011509150503 69
    0x84048203002e0750005011440302280c03244241c03400103803070424034004604d00384280b0700c8500781440c0c101c0071240e95070001d03001b40443d2005c3e0342e404ea03100b9105012a80c102c89080e00182a600d0110b4003082e075140c018040d1040d540e884c002c03078250b400780d02c1e140e55503903226101c040c02c42c7d1040b03420304c02101d454000400b0400c8081e4a240c01140c4642d0b2080710940c4105d1b20094120b91001c06405d0a42e4001a6880598006c80f401d1002c00e081503594401038143c90a6544040d030130b5550340ea640ca009405440c10300c8258004d41c0e840b8642402c0080c0650310041c0280341c0d403450301c60300007101d60041044074003410401c02000c03105800c114161000b060041030a03544400f052002c011811102d00400d8414000d0952140d03c80a115040c4041c1510030400b0800703118611040100600e0301c92102103c1c1e5030003500c04192495100304815062241001c0900543d45a00b07002100c401d001074120704851610700080c0301c07501d81101c12500041c05004003003500300e02c842d140410f0b6102c0c002039600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 192506043 1250 192504793 192504797
    0x1b03071709010e0d0203040f0f03051519091101030e0f0606120c0d060e060106050408060f070c080d06030320030706091109090c030624010807140c0c0307060e150a 72
    0xa0711210240407881d200c5130424030310040e4000039060014440b1400014006c103203c3c440d10308014215584c0640b42c02d4100b14401d10408140001202100039a902c90145040340345c0c00c000c402c0300e41c2000b001541030003c90740c1c08282401d090402018000441124481021020701840d88a05041000d02954420860590301c00c0f80580c01c0c0c250303520500d00c000c0c18070032100050740c103020030601800c0220582c054030900800303200c00c110310380020407566800a6801c4141041d40d44103102680c090b400203001505001005c02d081e407254038940c0c020403e5074007980315400ca1040d00b402100311114000c0d07070412260803d0110f100041c1032600300e03070140c51146040f004160050070104455150484440c3da40b40c2c050038988980e400c0600c00c0e16040081d001c10000d411300d000c4280c6002d440e50b0840c07141000350007030005441e148a01c90040c100400083c0e00d07582c0700e4000e16025610100e81120520038040e03500c0008003180a118800c07242c013400f0b081a19100034016607070800d90403200584003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 192507293 1250 192506043 192506051
    0x50108130204061e03050706020c060301140402070b130204061a0d0914030307020a1214120406090b18010b0901050307061202042103021905120a03180b1b0307170901 73
    0x29040240a080b0302d1444d0002c0d41407030440d4a0350402070300d484590350110081d0f41003411a07000395110b01301207a0542e20b080d44401414032007540810024817419401600c01c0f0111018054040140e11000744031341d0003110144480c64031941902201107417420142660704040140014882c5142c0100714410b000d03a9603a0701c940d03010103e05045510896454005030170040717064040010481060315603407214508070070041d40400400d4018452041d5410316011038200107010020203030400c48034958021039400c03e50409007108060968207180c24081b5508004481851742000d40b1030340c0c100c4900500070211145002030030394550b440011500340c0b40707408000202c0d0502503410f104c1401c42841b4000b05c100d11040c180241446100c4020103d040e82960b00100030030000200900d0302121106925a1400303401c20582c001c1c845c55412500031212401c1090034044c0505085205032400c800344805030300100c403050540c0c4412544500411414510643d05484e180340d035503844611007000103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 192508543 1250 192507293 192507299
    0x32405060102100b0a031b0f0918081b0d18050d0503030a20030405160510090603050a1d06010305060106020604030c23010f050a1a1c030903020a0803031e0105010813020406 76
    0x2a24003a41402074a40c1c4002a010810140b08c92181d50f000805a0143c200001c3c40c0d400c003d9485400c44c0d201c06080c480c004175600d900c01c01c8042c000740c0c050900500700c401e000b08114000d01503140a02c84402c107216010000140350400142900302c030790303010300510314541e10610000001d24943c51503d0b050f800100e1a404800c07400c0d0001c5000300c3c0920f0092000300d0b01d40c03005114641e0b1681005004440524800c0c0715550040d11030019100a81800b00315075a56140c000014000303030300c828070102e078a049000043c01d804907180d810780e80681e0542d1050307030300c603101030f81d86510964005000400011070300c0b006c643c00c4003200c0300d400d011301d02881000500d900e455080d43d40b040e0f42d149103950380b001880500d21181c4100301c62450340040d68400c3c500d9801c009012100b01c078140c1c0c0481e40c0709040440400d0b00c0381510b20061030303000303000702481620713610f080d503881e0011260306043c2c1030901d0510310700389011a103640c12100c05944500c2142d950424045500150309401c0343c1154544070f000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 192509793 1250 192508543 192508553
    0xf2a0a0f150902180f22030804050c03010903090305011b0504090b032b0e010809030d0b030705040c020d030f0209090411030a0606060e01170c040e04051204032405060102100b0a03 79
    0x10400c2d0a40030030b50b00141094042a1a000c401a003441100900114540440d035051b81a0000c041c7c0c150801810540d12410110306000c1074450540d03041d40380002900030590003048910903a4041c038002c10223095002c00c0c00b08110300d440000d8010900910081001114507004203090710710240031f442c04030f680344518006400420004909002e2051610086140c0c4071501c3c221a00302413810000c02d0400380c280d1038403480b80b903001c10800c03074465408240c162801c1001c00000c0002501c10808014800d40003501d0388240080c0c1d0700040d0502800120076401e60090300c4000d440182000c425489541d01d440019005000032905401400807c1000c0f8500d0320900c002407209450f0340200c580d1580006100e50b08104041058081d0582032244488d110003d0302d06680c00705201540d151100e00f0b0183c81d1840c00d00d810466180001004001c001e191003c19011210004894840c3d110000c07180b401d0781e808580c1d80d4010382c00840f1f10003404100b03070000040500040c09020b01d054603600c075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 192511043 1250 192509793 192509809
    0xf1707050405010b12091c0f0201090803040503070c08010209060d02071b090e010e01140a0905120d0b0108070f020c0f04020d06030606050f090709050603040204020f2a0a0f150902 79
    0x1300001d031404101784082e05c0700711000c60351003012100a4022602e0300c0402c080c5402d81070341e50b8010051000c3c1c05140890003540405c02141d00413058686a107440e03d04682e8a90015108461000001d0000180d40c2c00500070744420b200002c0000c1d040c59034814800c002500850b00941e02c00b10f1400301164074103400e08406d006000c01c0500030070180401e000b16400c1d61a11403044409a01d411070760074500d40c50182503600151001000b1a000001d400c6c058546442d02e00d84090040001481c0e43e01d4a00943c0546540c0fa02030700c0c0e00b9102e80c1c404c0016103582c0501070360782000d6007080207102114680403240d80214080200010304102d81c4240c0390f07040380c07540c1d04103c91542e03440000380b105140030b8206200d02c0d002142e2443c0315250444006064400610902d4040c0d10080003080c21135640c4c0c3c05a526560340c8030480c83d1130707010201c2c41c4180f40c95152202d03640044170380307845e0304600c00201d101001c0c41c0d081803041c0840501591444804621240c9071110565140849001a0703641c1103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 192512293 1250 192511043 192511049
    0x507050f071b0b0901050301031106040e07020706020105010b0a02060415060909050a020310090f080d0f0f0507090602122502090405031c05010e0402010f090305061f0f0f170705040501 81
    0x150030b200d052882d00000001490b6004440f854030300f4811a2100d0b82c0c8501220b042d00d0b48902203005005694012400c1030203590001c060445900080191072a4001120412248540e00900641c0d980d10b500e0002c610900350342c1c07001a0030810002e004551042e05104c00c5061600300020300540ea103200801f1542c98410407120307a080400500c00790318041004a48100036a00704001400d080d658410728034044c408024240c000100c1c1c810a544034640c007426010822a4050200c100d001008800514040b18a00040341e000e00000c81d8240c80050151450100f0710340c043d150400c00b00100d20441212a006410070340031440720320050b100d2560281c0940d02c520015a2141500c501c8010310b0714031102130b8107515252100402840c18405c1803a03800c5502801c00c0e4441c0800120111481003164002800e2442a8010301100310b90304041a86018405080c0913012070f10307520581681e1000e4410410f00d42c160310002d200004040030b0003c200c00c450411144100d55880c04541a520300368 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 192513543 1250 192512293 192512303
    0x50a031d071715090712050a060510030537020a0302060703050309190b0402010c020612090d030b092421010f0b0303070512130f172104090507050f07 66
    0x116110341d0740b004100001c0c0c48404039030f103032181e407601c0340356540d441d00715100e55250403800203562800e004061290314030064016505105910f4008500d03070401545204c11030350351151924500c0441e84024508100c00c5114501d8984101c811020007034120b1842e070140e9215100384400001a41d8100c002d2406074440e0322400e84a10300750700070350700301495180c4030100741422025801c00103400d152690744c06642400c068100341181c0c00032030f416006440711004619685014040c0d8240b001603600701c070110366503092207183c20140900807204400c3e61403041030a500b803070f210004820308032848801c04000e06440c1070b5801c0c8060014074549841d88008040e5901d4140d080302070850300405c5c40302030007503000318a802072a503a41c5560346c1c0106c00800061402081c001000c404810b2201c0082059100c1a4000c41c0c07504100000c608075510845100d00c40c01c07459080e032041d00303041040078a40840c60719080030b00d0654000050103008103210304020301005901d4046020030064041c640c012 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 192514793 1250 192513543 192513569
    0x111130306060501020d0c03050a030603080a08150a03050a0b0a2301030b010617070c1506030812060405070512040203160e0a0606020111090111070902033301050a031d07 75
    0x40c2490070442ea140e41000e41150800162001c00030b81040002652681c5442c000380d039074040640841c01050140c10081c4540360004010780c0349a0310021a038081c06494001084000034070040000c0050b07148030040c09504450100c1011030555541c0c01d60180c030300320b000310b411401c00b9440b81e00042800d05180039504003100504c140603010031460702406503402d0003003202c0c64080d084007030711000500960402c0a00b001a43c100030608a40f250030940400d4144189600d925002c102d0340c005015041e0030f00c1d00c0c400042c641c1e140c035010b010301429180e1942440c2011a81000d09043c5d801081a43c040c03180812110411800b03807640b0008125070181401c19007851340200c001e581040e8815011a070600c5080a0101110344c00c0302c0b000e4509082003002d051034040041e040ca251a8851980c3e544080104481c4030703007103c1131902001511900f00d200e64803d8100c0219400d103800803038002481400030700f04d00360103903101e400707448030003020b081036031290070700407032422502e03402c0113143c6944 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 192516043 1250 192514793 192514799
    0x6150f150c01061e0303021005041a04020d0203060709180b0a0e0c0c070905011502010605010e1210110705070602120f0f07060507020c0a080714190b0c031305090621011113 76
    0x10500503806234020b041c105000358245522103545082e030707640c1e0345040316400c540440c0c11941da03562180c1507070764040c064890615000c14040c0400302c0502c80c41c0c03850301c50f98400a040b03110078491060141c9004025600c1d850402821001c4800001c103000345020081103240110070302000f0700c0740241600c290104841d07040c00a0354621141041c0c0700e2066a0401a050040b0780e003204020030074107003d440d004014014031705503c1c64200000d0399400100d1074504007013003911034a4010000300f4000c100b160880713a5111000c81c1d9074140e9040241ea0410103000241000078021300070001910080768540c10000180c44a100300c4d1016101c0c203015034003402d401a45414104000c0000f402d03444054102681b40c03082104545a0741c030102c070301c0342c40515903400e22101d500c1c0c5007a020f03019510066841d0b0806410181d07403613000010003a41d2280c62440085c16103440c0010314481c900203801084e050060004402d600c100000c42d5002a5407202d00710003070040800058605000d02d095509403e510b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 192517293 1250 192516043 192516047
    0xc10090f150506180721090506010f030b2716030204060506040e060616050d080601090b1602040c0915080f07090b03070c0c0b030906150f150c01061e0303 68
    0x304048007040054140b60420480c0c0d42e6481d29413040c1561204502d18541d0b403940d08442a000d0002c41d11003051110148011400259002104181c8180211070459886000380014590144001000c4040c080005140d90045181c03d103c445550003c101c40194150b120a05208411240c5004410711350320400c10340c6824051000141001d84415103032906080e0400d03244c0000070300f054003422000401d0b030107036402512501400c5400205860061090744401001c3c90b80580e003682c00240c20100120708402504200e4503c042080c03001000c5a241c0e501b8800a00445c044032401c0c40027280e0000350070141c6038410807450035143c0d1007012600c0c1041094580070300242c041c0e810041d160000384040002002141e07005162400e0552541c111032034484c59000c5a41c2091241500c08014005183c000003403140c040e03008410075050740c1c840c01d014401070003803681e002c583c001036400d80c00d140c02560b58001c04800d0000800461310750380303c148800048241407151031400040c6034080041c16 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 192518543 1250 192517293 192517313
    0x70f11090a0209030a030c0c0b0408031c05131506090f0c021014070828020304020f0d020307061202040b0a090602100612080c0a0b0403030e0d05090303040b0c10090f 73
    0xe8241c0408500740540780c00441d40c0d80455080060030710aa9202200034003240f140040000d00900c16005c1e070342c079115003841d900c94010100f0610405450040620003141d540101e07403040b050350b4480700c1d109405844d04e804494094007084281d9503a00b60208041d11a07004440800048840c0400c440f42d0441d030080c42c0507038150621748081d00d40b0701c0b158420001021102d410004c1442e03c446c1e151602c0517003405a102c0440e100b0642d0283c203440522849458029500c20f42c021940100100312141c1400440c40100c00020b40c1a0000d420078000c050061011584e8807200342001810140c40d541c03480910340c440c05110703000c81c065890400c001541001a503205607400c100600c10f10b4130388034011000c10103040d001444820081440e51110320704208000195400c14032a00301b03401c041c00c000e00100000d030313254642030103404605510f160007981254a4643c016009618161810b00360811641241c040c0540b240900850f0000b40c42482c0901a14039010704100c00c3d401d8900c1c07410a880b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 192519793 1250 192518543 192518551
    0x40203191401051311031611010204030b060f03011a040c1205011403010606050f040501030209040e060a140c120609060a05060a0201020a0201060e060f13021b01020d0606140a1103070f1109 83
    0xc0c0d0400d000b404200310301001b52a0000c40c03242400c0c3c1d4180011000fa280d950308000d542d21950300c0460f0020511801a001500030703181580c502025214240a15007618081e0244d80701c0200880b00f0910785040540c89020f40c0c0c0340e546403d4420340307840e9080b5020382d88283e2003021005910081c100390382c80c0038403c1000a2070303c3d05000b498650744d03a0900181d4007071403040314103056001c9041381c07460301c0b182c01c00d41211844c46d065809510741400000018001402c00d49841860100000c1c85000e0030b80459031841140d80449031075544d40b904001248900404c80c98115811800c0019580c8800b805031250f4800c40e000035884241519009003166015440100319105010501030355882d10603a01300c1c0d0035400e6528ad03803580e000c00048000380c4a440c080702010b40c1c0c0d8040c01545210113502074100c000b440d89090100076980c00c2d0442c0c101113a81d0b2243e84000040120584d9203016210740e01c3c0060007031041d24105090f6444035070389603900e200d060710500d4045903201e05515240c0a03490f40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 192521043 1250 192519793 192519829
    0x1d01030605220b0103140f0703020d050c031005040204120803090705030f0d0201050610140304060e1903030b090c03180c03010c090302090615180609030709020c10090f0204020319140105 82
    0x198011442082d210351b80a460710302c4000422002c40e805c07500c00d804031391904030401402c1c4150b081820007001c031980700301c490000409242c0004105460140201c40880380380340c0400c42e0440042e2180c001a038005070083d403540c841e40000040c0d944050018010f503841c0320019000e400300e075010190a440c00203100900c215880301c03201c00d150b50400300459040201c50215622940c4070710342003006050b10b140340c68651040700001042070100880404807248241e07018400d008000007449000c94054820302d012080500025a074840003030001c1c42c801d1042c008454612240b007011070700b12003a24801c500001c040000c14025801c0c20800c03690002d60680380103201044406002c080303401030a8070382c5020414410716048580c1c03103405640c61030030010309407450b041e5030b22120030003540081003c82c250b0161912002089060f8890010f400b40c1144500d0102c190940c2008000c1d071000700140941d00100c0800814222103200d0900c5406641cbe0300f078a1a9410b040410506034400203403650 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 192522293 1250 192521043 192521051
    0x4290a031220120a0c08070606080c0a08060903030726010e040b060f0d0312061d0a150b040501140f0d0608060105060c0a06090203070b07060605010905101d01030605220b0103 77
    0x8842c40c1214200ea081d02005c0c9482c80301030082c0d03c0d00890300d20400f24080c01c0c1500740320b00841c50030070225402c140c0910854050b00a43d6460000e0b6480d42403c907010b50142d00f06000150010f0f000d607110840e20784000c1e40e00d042c1c0720710b8030740b02918144003a044000300d10031503000c02080020b020320b0607410610807200c1d80d0b8502480c00009034003040c090700040401582003440d034800011a0003442c05850980c40d4a407101c200322907603400c045401c03aa44107a0906210402006810283c0c100059502143d8064503044c2000019076034103010000c81b01c1ea0200400524828804820292400703a61590000c11180c1c5409221413900b21b046c0c00181c0729003001c02025608500019552540c00e600140100d400c0420340002410556958864648114001002d00402025a20410540b07000362914641e883e110410302c6071004202c520300300494420f40e1200a6907000c0f2400d5100c0d4081403601003076054807800400d80014804070a01c4142524a012155505050145810b88042864108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 192523543 1250 192522293 192522313
    0xa0b04060b03070c06020904060b0904060f0f0603020c030d0c02011a010e1c060b06032a04230d0602040f0620031207020a0506010608041104290a031220 67
    0x6407040c8800b030481002c2c06810045081048480c0d016900003400003403080040907681c1d1200c0c9240d500071a13078188220316042c40890115254103240b010b80b90b21255400040d030519900390025441108560b500d0b1100344007908140026010b8412083e0030365002181100c1411050b0704400c0160769818140400c0741c80613803250700c41f90080000548454181d02c0702d03041e10b044c0840180842c1c140190090f90000130040b5240760108040710f0640e111180c5039150b02c8550030504140514042c09062a0301c00790410012100b9074010010040010194100f80d0312070b60b10038007241c2c0298004001860550000c00c03c05810121540701c200302502e1019010407e010916228441e03d402e5035018084039000c260043e108011a644079980202150200d584624000d002000220b40c00c40703449000d81686440d82c01c150041c0580505d0450807c103c2c200c0e80d604982c224041e4440080e003200d001d4000002240c01c00d6605118a8001e8480c45d840c615440c4200e4801840c048488134941d1042c9805 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 192524793 1250 192523543 192523559
    0xf1406090606130b010e030a030810120b040b150a090e0106080601050307151b1524052103070c0807150915030902030a0605060103050a200901051b01050a0b0406 71
    0xf0561070b00c08180000c0c0503881c03200580c0c42180b42007a031505441285030a008140c3c101a819000d1810341001030740d0f6581c0c41110441c43e01d103054000780281007950124000844882d0392039005a03030401c1040c2c0150604000c98502c045551051104545408111040c07074070a100328405440a08050b0030258146000300b5038030091481800b241c03190303100100c2101c03840350106682e1803400f0803540d232160000e0b040c0307000e01400c0d084d10451250300d07014001035400342092401c80c07100d0b269034141096524050400064080440344940c540c49400c5009800400030700041800a00c034081e0103008a0a04040c01c0c5010030540082018261000e5440d86a5400440307000454034482890625811405812000303807940c5c0c0c0000b50148503170081c400c00c00c80160442d2740300e0142030340c08100036615601d01000b50b686806610a1181d16003414900e6001c00e43c0041c4030701303074040c10681d01d0f0070829101d0103150208100498060707591201441040140340c09a14504601281c007440003500307003000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 192526043 1250 192524793 192524809
    0x305010609270605090403030b030c0a061e050d022106060702010c060b0a05042f030c09040216050d0c1202010203070905090703140a0b010306050a080303070c0305070f1406090606 79
    0xc84a8058801c405a8600c1c4a50308548042d04015145c91038a040c079180240c058407004030010300c00c0c02492806041ca0906a0369041110340c0c82c0d5038601c0030440a004401701365425021181000001c01151b41202200e00041a00b8194004413031145940644100ca40d0740b0b0282100388a400100600c9001d42e030f210300c1d10307404280c0140e0005003140540002500e64401ca0340b015401900340324401000300000058902a00320700b5110701c030103044000310345409101c2100c164041c01d4042c0003640d9130b07041c43d9001c2c1c50b44501000030356240448a4903201c0c50308881e0162200001c4400340210300304142e031506260009020f0001354218242107002030b051300c00a0007010300441c04040003544c0340b0310940005120300702c50919445142401c0d1100405082545502400b0134280840000c0905280341100c00321070120003d142162241d580032030f001078a03441c1c194100a01400520b021a081c8682090300510a00c40d568a514504244505001008141d10590340020003040915140c05070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 192527293 1250 192526043 192526079
    0x100c020f091521070308030103030e0405073203010306090c09020909070e061e1b0a02091b0f040810050601051305010809010603050708010b0315130b040f081206010305010609 77
    0x1908084010156072500d002001c850141c0d6038911130010004203005051000714141ca00a1f038500e00e01014000500007030b20b90580b201d600156103500ea2071a80c610110070219400070340542d20381c00148154986807203410a0304165510340d0340303503650b0040084d0040100c00400362040150b0030203502000107a055000100f01c00d061150f03441000340541d0300c81003182c0310311101108404d6007030f40d1108034030350a400440c00031007050704603015031382d102c00d001554410182d0b000b03011210581d140c220602c4000d5254010000c030070018024100d24020f0f0501400c0640b0240c1d004040c003e400501c1801943c0c80508100d041c8a02017103c0c5150940e041086010342d80c0a01301800d0540329030381542e004000d81c1d8030140140c0100140403c1c04a41034202400b05981202120400c6126a803042c040740320903513000512142030203d0000181c600001203900501036950f001c00c40c0c046454100071648100d1948038030700341c584200580c944c2c15101e8540500401e207068082d0a04000e02d0280f4410800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 192528543 1250 192527293 192527299
    0x111b0c011b0204090804030b13060c050c030409020c0309120a050c1c110105090a0603050103150c02030d1e05161d150c19080307030615050307030c020c100c020f0915 73
    0x2c401c090901217900708079001940e10034540400ca140c0000b650149102c800c104035020b43c00c06c00034001043c4524142c0d90700c080f00d400510700e02441c0c034428000079032005081e441140024000307484107545001f00c20184408400c081c1804401034517040d07086c00320303258446103da111403424003200004400041c40c0a030348801002c00d46295900140c0c2c141c024040020b40c0b001003038101260595064005034100c91042c58101074100c0811408000c0d200500380d81c2c4010390040c0403c41c3c805c507058000810f1030002c80c6076140b14900c0212040b007552411030380c1240c3c0460b560780000c00c480d40842010041e80c00c110700341605076903030000582c6190b00012011a1040d010410b034000c03803810310000b518042024812071103045603141c6154246c04c03c80c1c178000402e180800010f0188841e00d402a0140c01c00e41c5d1310351442c5d4039003c05030000c00001c1400003c51007005568811a1a00c0294010b0007400c0d803621035400402d441003010030081403a8490040039440d06010000c004e62410700400103080f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 192529793 1250 192528543 192528551
    0x15060f1a0a200a020411030609040209041e14160806010b0a140c0604030f0e0d0807260306130915090f0b130303060503062503111b0c011b0204 63
    0x181c44100c1d002450098031505100201221181421001601001d410300c259818010221a0640030301c03580011210283c1000000000500510b442e000d100ea00c40e20511305c00c0401d10900c422079590000081003210b4000007000c0c3c2c00302e044802c124054524450781c0301a00d6141c2000340700f50b201c00d81849401c007007810100d01e4014003400740d2014041d2505468009480d00e0007000d0041d40c0710401d0700e043d4007050040c0701d00c1000e6841021489110240070b0088014402140c0d11500154013030f103429185403880005140b2041c400085101e2400d0328490401d807030741881e8003000390000c5184c150040003403800c4070840006060300c060036100351050b0000502e41d5003074100102c002e120783c5d42c020501c100d42810024a2104050810310787c40c001e5030100002604c5000b407542c0d904003030301c40e100c04220400f1407400c0848400600c0031599010300d0302107101d1009559004080d0480408449a0700410003221070303501e4100151440b0800920f011300021039442c802078001c200800d0301074016510303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 192531043 1250 192529793 192529807
    0x20309031222060513050102070602070c0b07083004050601050f0a030b01122103060f09020f221e080f070b0315010c02060304060e01110f0901080405070e0415060f1a 73
    0x85d00d07182010340000c003c0d9a80c0f5843d14024000398030404044410002408000c90805400001d84c0c00740340d03104e88090f15011100d00707481034903241c0d00c050f8400360301c41c2202c040b50f2281c2840081e000f075110388000c000e55414982008150b104980c0164061402d00340204041140702c01d45504540c100003801000070094280920b035400c60003450b10007083c2441c0b038140c00c640d040e44400101d41150340d410032030301e0711100d1f1032084c0d110365120f40504142c01d01c406503454000001c8920142c1044181100041d92908155000d58000e5540c81c0e040a003002c0421503031900780f0004850b08210702c003601d040c0f410202406400d00010b000a2545006082071001a034010320185001030f40003000b981d100e140510b415405045038611400455080004031020007040500f5520700b02c0401800605154440d4011038035040001d00c141c410344550394000a000d108030b0f180381e01031400f03084011150304003406448191a4070b40d018541c42e01c65004208007080407160300c1d09200c400b0041d000c0c0c0d2042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 192532293 1250 192531043 192531061
    0x1409060d0b0f0405040b01080f01110403080d0f0507030606020f011401030b040318090519090305220b030f040507060e030705010528020f0c180c16060203090312220605 74
    0xc88820b116081850321060105000b4580f1845d8101e03400340702266620804005a130b030aa8161074021b0981c614188000e01c0050841c0d00a00761f103082c0d006000803101042c0b50040251102540c0410100f40d5070300c014401264140001c14003004018005d00c1a100e00c910305000d1424148000b40ca61300101c0c000c2010980700c2d005480e14880f110881d01512a181e594400040030709484038204151001070200007100e4034003032180c1796070f05512001d0610b0f29602d4441302c0b4605d1884100384103075403000d0104d05541000d02a6002d602550400c010910b0a40340c224602400c641155040c0000704c00004041e540c0000c0c0b0105540080c64941d45500400803010701c149200518000342d0b0160100d082c1c806940010725104500c42203046462400c0a101489460021014450724031990b800000b80b048108200801c2035601000746c920340e001154407a04200c3c0c00554402c03595800010b0b058018084070820240c2065440c44031198040d0b640088003112110410002c24040d290740003e0082a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 192533543 1250 192532293 192532309
    0xd1e05160503100501050c03070b091c0809060601121508030a0306170a11010c050f0d0f030e030d320604050601030605091f0b0f03010e0f07020a0f0602070c0b0a1409060d0b 76
    0x25038000600c007041d0030708100bd02d407102c91002200c03011700c0b1100d101000d06441052624003407036244000d040c440c1ca8400044610000120100100300d44818074200d0031032502030301d0300050028030051520b502000d040241a9805a0b102001804295444003001da07404182c0c3c1401d80d0340001c0d1031007865008001030301d0b10324000341c014005008100f10155000740c04290b1004000c41c913920350340c2103410101c054088504001000020758410f100356142e5013140e5005401c41d26110714900c48540c80d454038103a200452509050a111044c02401800e0400c0d00641d03410690908051215500340004140703041300003001101d9000200800c10745521280b20588060032202059030350751540c0503400381a9900c01e09c1500e0719201c488000071800030300c07403902c18001d140680c041c0a90880c075403542c8050140603541074030410780c00c208020000341e4540d403000013448884411a19400d40700b60207803018001e914004805c038810403400d005580c4007000c5030f42850341c181c8001507846003100407039001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 192534793 1250 192533543 192533557
    0x6010e061503150906272a0a0f0203071524090c020606030d0203030601111203040606090b010906080105061c050705090901060f12020d1e05160503100501050c03 71
    0x1921001051012144410088982255050300c01000b9515801d05001003c4d2140c10300d1b030107003a0540350394a940b28540007026045907001e0040841c0340c101c400c1001820b8405413950034403c5001480d0b542d05030300421840e407081080c1c00918105092901c48240c00380107009503080103540d0b001c0060310323546c041507100da1981c80a00d84e036882c81e440d9003618000b030150080d260003621402002a18620300000c241040c41e586034051810b40e00c8280c015294050760b000b490000340204501d410140442c3c101540c4110302800c0081081841d081481080355442c110080c100491180244501c42d0480b0340c0d1411510300b982c0c00c030b6588103100c01d807840c01c0344062981c0d02c01905000910007883e501c4001f030f01031074908640080701660b03240c81c1070302c02c9094400c01e40081b4190800110b000889a0302406640300b00360030100e090b1340e0710741d2510180d5124030946141d207540c40d8148500b20950010b8180c0c40703100750030b1003480c0d03061174480c02c03c42d1203542c0f040c24100000040c010807081001d00a275115 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 192536043 1250 192534793 192534829
    0x506070501410c12060a03120903020406090b0a0b0c010e0303010308090406300c170a05010513081204050c0607110f0d02010e0d02030f0706091e0806010e06 69
    0x14007004001e882d0910802040440710a040c10038014442007460321180d02402805024524245844180164842c8000c0005a00c00ea89000020116801000c103200a481a81e0f481c601d1500f18810070088420036002107080707a00c3e1074800e0007503880b55404a010b1340c14105000d501c0703003640103032107000d4004110703024003900010000008220020000d0100d000c4212400c2c07015079154138540c012440e1004064030200311030070380810320320b10309070302695030360700400c054030712145c40324074000d16003642541c6664194000e00f05d038002d00c40c0038868143c002d9414050b00c0e07207004503600d0340d010070300030000308111044a00001c0703000c100b410082c034415808040c0c0768589902c254107025418900041d0094002c1441442059051610301700454440b68140c44144030424640140443d210b4020800c81e014842c0c07103564000300c44100f080b80b0040c01284da4843d85c10b4105642d0420b40542c00301e0140b6607150400c0c080c0124100800d0303070f030305407141c10302c8510725030380d0b40360010360181904403000740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 192537293 1250 192536043 192536081
    0x308041b080f03070203010b0616080d0b0918012913060905011e05010203071a060409051e0c0a0302030d0f0309210e0d080f070311010e0705011e02070506070501 71
    0xb6800440506000741c000c90007004040c50036000d006d0303141b050121200d1160980d4460b10005640d56014110359441010001824070901c400325505c140241d52200301c1075100302e000d40d50318100f4001c80d003d0055a82c6440810045074001e03042c00404045818414104001d502510030415807148004191404041c01203580d10f40d4002140f14022403c0100c03d01c0156021580d5400041290b201e07075845034490071000b491407441c0042c0ca001420003070344251180b48120116900300803400342800e54250043c040344800f83c280d890b000b03500ca801401209200820800b50b640458a1403000103142040c9100c1a00038034110003c0401d143c0c01410024a41903048030203924040e1074090300d02e01d854080403091802c0c20403148140c6414001c102d804104104080a003240010703107509486410800030590501d4038580c25249070180c400306540c0403a60400866070f003c1081c100140540c05114000d5064000094a0350324900a90740940c0d800a02e10040000075444100300001c0e49003c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 192538543 1250 192537293 192537313
    0x3140d051b010e061609060801050d11030a0b0109060504150302100c03091d0403080624090a0f0801021801050309070504051504050403030501051005040e04062705030301080610030308041b08 84
    0xb040c400402c84034000503130300086c0403a50900074951181031b240c00415501d990a029550304020b1014103c0c3c040c0c160090304a90360010b01b1780c210b503901030500c103503012078030504001c10b11040790072621400c0c6031071010810400241e200d2030041603011031181f03082841481241015280c50075590322000512642c100302c22850841031480c28006e510950b620107164503410200202c2c120310720184040304429180c85441070b1086001884a180d015000600440d80e84a05a008041541c80002d0507500004c000303441075008220410600300909010703041d4100a48101d83d185001d00a00340203903960000724044503002d003454070b0b00100c001c2041c4a00e01c2c2034034004014050a200c3c2d54003941c0a0101c122089000c4c1085d1000d5a44140c0c4501e8166603070346803c400380c407406014840300a4140e54940f000140c100325100b07080d000340000c60b40c2c1c3d4500240c15151010040001c0c10f01c04503c501030002a0740840302c02c1d0426001488007070103d07254421031401400b260304c0000c00c1e2091490308 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 192539793 1250 192538543 192538561
    0xa020919080c27061e030106090608010b03070f140102030409091104050708132307121a1303120b0603010609060e040e150406020c1603140d051b010e06 67
    0x219031008007541c810300210705414440d070507040310000e0b6202c4010f0103c0001e0043c10302204411289003114102c03065a0403400200382103800c2034100281d515168842030021103403d0117403500070707401500280809460090b0302d0700e221a2a00a11311803625651855240d40c1c800c206540140c1150002000900124a002c0741c1c1c0c4a021080c15004504000016503607900941040344038442040319840f4150060f03031802207841005041d07580e90f0951043c003698050003044041c01924220300e0100404c9018108804d017030421a0070100c11191100803c444c0010781c50525040d1549401e10300010014021404042d24034262440d41005000c00002a000c1d80100c03148101e94058490110f00901642480700382e40281c003010040782e0248130040d4404052000c1d4582c058011240182400c1c400c140c468102100030b0501c403240b0f843e2140900501c060300c1d061450360082c40c0c1c021b10104100a9000d001c81c00381419981d0f60000d03080d580320000c5403e4000320408a050004d68455150140314 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 192541043 1250 192539793 192539803
    0x11161502241504060303120905070b03040b090709060501090302060906072013151202120303010e060a061b1122230f190222030501110906030a02091908 67
    0x10b40e80e603400000b108402e10b04091080f5802d0b00e0301a5240403c0102c010100c1d00075000144040300e15100308480007452000c1d050145000f50710600c9140490f003001e100d114074100c081d801c100401031802600b00400d07a0040051011203034142c40341c035201c541d018005905401084400350402e40c00070303d00100c140070307a0140b90f0b0302e510403540c1c50641128843d20400300d075558036142d4142020154240002110059840c03c128401000008244590385903182150009c2e4040c014440e07410007446903a2908104001c0546110300d4000c0340042000300c901c0341d83c40640170150101c001c0f00304000c0c03181c8a40c410101c600a46246019592540895205c02080c1c101c41324401002030f6810f5850360709060001c14050080340348104410b458482e0a140f060381d820001100b19a400c001e104084c1180e0018a4907041c00b0034424800c592071030034428203407802412102520310b010400071140d680c500707007580d40001315040c0068580d001000030507072205140c86c603640d19401040e0b0019881c140012 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 192542293 1250 192541043 192541051
    0x30512100609060f1b06020f120f250807021603080304020406090605150a0c0c0303030e0c2209050a020306090307030e03030405060304060902040b12030a1116150224 73
    0x1a0302e0110303e42d60507044a071340011081000002d00d451210480140f50b0a5900f20a103001c0e03040180f401202080445d07069210400c101c031101001c0c0104010356141e0f05007545e100008030342000320900381017246da038815100744141c407d10503203002280700700384208985184001c6900c25401c840344c03a030078110301e1900100c074201d10503818040f02040741d134014052070003144e00280514805284082100300990012603036042004207405000020503510541180214001c1c0c6000610003541a0354178140320369540d1040c044c4114001d2503ca070080201c810103d99a18400000c1040d050b240407401c11032000c5c806540341c480c00043c0300080c0320104c000e1840c00d111341c84101d030a640c1441410389074090340c4100c5601900c14400180801c00d1a08260302183c402400001c001900d00001240c00c541210140d825034000718640310030a40200400581001260040100144030105842200f10700c0c006c240d15600c1604801075014020881107030b0300e881414106100d070030740301407006038000115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 192543543 1250 192542293 192542297
    0x40803040311060c0c0111031c0524010e0409020f04020310170118061e1e0c0503040b0105010f050c0d02031c0b0904030503090c0a09050601030506011106070305040305121006 77
    0x80c807002d6901c0e0801c111034100f401c4030040c04405001748010b6402801d191810754141c0030422041113010245900510800b91203a4005118100b500706c5002c5aa0003000e035880812401034410b103181c0c2c00c4050800901e0049801044103c0c0c54408074142881a0584640290011081c0300c0c0c404690000403040e2034883d4000420800501d410900340d500440c0d0348407100c1c0440801e0004188582c01030307000000b001d010a400450041c0c0c2d58812104900c0d9400e10031200e0450128064440e80940160444989800d034118249500c0c1c202c9002d00c10b1140d24140104217041e030306502c0c0102e080c0d40c2620140300c161240c1e00d001c0c0b240a51641c1c0580c0b50081880c44680310210340b441184202426001c014040d618141d80301e54094072603038000742000040e8802c403010301010750b681c00320806c01741002d9040070805080040025040d140c01505d2241400a651003500c01e0b660002482e80d8006070620307001c40c507030300c1d1410291500e200701c03c600f00400900008000313030303620110b40e00381c00c6038003075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 192544793 1250 192543543 192543563
    0x2090a050a110c061605040609090b01030e0d1d0117060906030f072409080d030c05040b070302010f05010f030206030408070c2310020c06043309080d0206040b061c080408030403 78
    0x218030851b46440b840c0100301c08039003040e1091048003015448221300d00c0c0181070001e045001c0044e242d160031030050345a00018191003002c0750302010110480042c5c40700f03007403041146040c1049030b00207000040c400c5004046610005180766020043e00e80d41c48518015191010f4591540d00a609a100d140c450108400304100c040c180c4564402e07011280307004040c04a62806c03041c00c401500418002804000381804003003a041c070590020840588207030000104002103299440c02d85e407050f8030041340301c1940341080016031a11411030750301640c0f00e4170341d60b503c0341b0502c2c03c1d0340c0011290b08045120f100a00360580d00011200c0049500442101d903103014000042041707070340300750820481d5003004003403000300148090801d900700c8110082a10311800031002c040040d070290314070f5045c800140c2c680c50404c116003040c0f02d0145100c009101400151a2a480341c20070f011000e40458012440d90903090418407901d1000c075100ca600000f40c6503126611901d644d960707045800140c07010220 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 192546043 1250 192544793 192544831
    0x10806010e0618011710020406090911160201120221040201030b03060106020c130207140a0c0b0f041419030b1f0e06062505030a080f0402090a050a110c06 68
    0x2c001c0081240703c00b08041995a03a080041c80003254002040c0c6100c0d41c4541d030102541c030145400644094950f030342d103a0240a01d085d0140082d00c0051101c42c4400000300001c07440203607040301c81030b90f460f02800c120020b03908541d0038800910502c0c4003d40702d800c02c4484a1000c0c004011124003407030003607800b44101036801c0c041644803902072080c81c001d68488030311507089041c0b021004003800c002c0d03080103090116603200c000d800b69003000001500e80111400e43c081090443c00000a441e0900c005418200c8030f0014110901c604d01030300e10140c070740700c8801c079565541315003200c0382c174680010444c0c96540c2e074a000422003105031071000c0482d000c0c21114000f001610b01207400c0b18541c00c0ca00b0010703110281800f1030340d44150076542c44464400b6140a01895960110800383d105000031aa103144100d401810080c018004c07000300c030081402d01002d82e58030115203410090a84000840740c40394403503100140b100664040400d500030800c4602e02c14003090130f910540724407480c9845081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 192547293 1250 192546043 192546049
    0x12070305061618061425031403040b0f10090e0a0204050c18130e1204300312061a07020f1c060209010e0604090f0e010506031504050a0b010806010e06 66
    0x70b482c1c1c50001610042070401c1012078400c5c4183c3d41d41c041403d407441d02e0031940c4010b040207400888826100f00207080006420568041850340303400720640001400c1d0f0405580340038036031074060031103100c1625050102c1d2000c0c06450041005100c1c0d902d080100040ca000a11b450b408181e0303059214514000c0026100c1210707074110342011902210710340300d0000d8001000f1103441005460754810f552524501900c810402c4881c54110200f1181034840d40b400e8012072412500e80c0d0004145040c03421307044294400e0080c1840c4c2c0c4d69143c18802ca5043e04280c000004101c42d034840b44401508449014000d1f07440d00003031845238000e0303801010800100c03003804004800040b0403a03423018001410408141103a014240304001450851561b91000c00000ca1980140e0004000540d0359a0040a1103444d03105031082c0014043c001d0204e13281920010b40c0380c0c139014400341402c40c502d40c0020704000080c032034910241c0e0f11200040c0107507180c200ea5076580d03409000748005902c5000110ba841d01e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 192548543 1250 192547293 192547307
    0x1d0105060406060f0305040c091503060c03061a0c0a05031602130b03030901050d060905040623061005072105091c020603130f0f06050601020d0e03030d0b120703050616 74
    0x18004d440c0c0c4038030b640034a44110000c00c0014401d6910040c0e0400c081903120003030149072902e071038540200103440c3c10350620f0000c075041c0c03c6108061600d0124100302810903040081002480601c2c11a1a80c040018081c01e01c005802c00400a020001e465541c001c031407800c00d09014003e80d0001080402c00c1300140440340700446e039079890345c4140049403240d84100c0081417074030341c035520200c0e015a89036041000d80c1d10680d02240c0c0d080d1030b0704030f9810048240c4110703c1c0c00d24005e44c0c0c02e021400c0040100d83e0f0000a0504e4108101c40018610140060540410340300300441110020799519601d000f022a000003520a21480840c01800000116200960303241a0024010703407030350329448441c075000642e03403070115031501c0c07901e00b45000316210405ca44185d074014400401d0602e800350009041c80c0c0e0700501103050041c1100302d840c10b91400429614a030402d00000a40000d000340001c90402034109152454805d900b4040200b05e80400c00c14040c440c4028114120a9055403c0c1ca441c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 192549793 1250 192548543 192548549
    0x809030409020f0c0a050106211203020306030a1a01060305091c050702011e09050a06051c050618090f150411010f1202160c0b0304082b1d0105060406 66
    0x15801840188080c4030345900504804190a812500d000711105029080c02c0d040079060b91030342d56401c002c0009041c200031480742070b40c2c40004c041d04004140d0b5064442190a141c00c42099404000552113460070401c0e00c0507907401191914034045030040c48014400c09005180000307040101003540480005049034480c03012414003038680554050440d02900812000c0c4d04101c805080381007641460194841944100c0d515022281c1c100402c0c46200c103c903500c01d4003082000c01940080140c0005040c42451103540013203215114000008c003042d4000d03404841800c0e180c014021600d1001a0303a500c0f00c0d85600950341602000c0e0103130050600b040b00e001c1c040100c0e9000c0d945040d0300c0303261a038420642c0d5003000081c0c0e012039103201c0200d8100a8051000340a0f980d178a400f0300000810f018000c203103d0034440c0c9545483d030381c1c0111038043c44030000069089919100d68040300c020b5805800050f8017800c004143d010031002d1010140e8840324000c070f5207010003003007072820603014180503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 192551043 1250 192549793 192549811
    0x30203060c070204020f0c0307060b06130512010e010203010e1602011b030c021e0d080a02030c040308071a07030203040b0f091f0204120f030801061106012102030f160608 75
    0x1140d07181900c1505036840900100c0c0c0c05a800c00c03104030303030210f20406082e4441404008544a10003403038120b00f11083c8003401d9202794001d001f54407400080c110743c07105a5005907403d90301004d07920643c0340509a4100402c1155002100208012091041040c42941000c413216448030801c00c09038201c0350f20032050010b002940100110a901a030443c080249082c411203065856040e880e00070407013500e210f00076540066030000c1840c0c1c0d21000640c1c101526100841c1f96041c04483c503220f8cc030503444010090703540480c41c0c20901145820342c03028200542010302d030318074140b04010000d501c01c49080311300d001d80002007021408000e540764482e80045d0001d091280e051468562070102035186450200d030200000300b10f0706180c6107060030192142c0021000c1701400d2401400c1240140c01c01c0d0100b0100e001445883d00c1d00040e074504698517414141100030641c0a021009402c0c65406501840b4810005040c00c2c0009854049092070b4240856140c0c4c603180200e070380d4241580e015074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 192552293 1250 192551043 192551053
    0x5070209160203070b0408120103080a030e0f07062303010e0a2d0f110d06060807020d02070905060112020714011802030303150303040503070308120121120315091a0307030203 77
    0x41703a95068507081809804503a040c040580c4d2842c0c852071098004403103540b80450451170713490700343c043c8006034501d02000e0013018071032000081d6160b480e0700c502c00c100b01e464088158615550344c0000b2080c042e84412694a603140c81200c00704c213200395031074800d06181005509000003500510180c80a03040d9211012010000c441c01c00781907804200c4100c1c1e43e4031848010104000c0000f01083c40103d0341c0031038206d140c214007401c044801817480003903400480b8403190300c80d4081a89025112406400070b480d03154100100c07a24048519030074021840010036005210b40704031031034175036030700d0030000d01490144031070542d4140300c102c0300250141e0051010950541816910241d20030380602164180303a900c40000f460005168810b4811503000206500c01590301019980074198110300541e00c0010000301c10701e940c1e2914030103442e900342d01900c0101c0a10030707042180d1800844500030401038484052078000e001f041c825822400d10020203036900e0901291003002c40307400402402c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 192553543 1250 192552293 192552307
    0x7021c0e06030420062814031f0b041205010609020a09030f0f050109030f0201050c042301110f0c01021b0d02090403020f0102120f0603150c0d090804030305070209160203 75
    0x158494100c1e1240d0700002e256044c1e1008181c5841d8050081901c00025a000218a04284011200e44200a5800c200c1074005011407180c1c400112a005a1a0024150901c7c01b0f0034803240380303d0094110b0075007440d00040009820200306043c912003801480200030699440e00f05204922404150070041a0031400030004500c03050030415015005030f0502ca074000081d03070f4250841d588164110301240341c4c1e20300300043c168248125540b01d060f00882c1c600d13003070a0420344228212001040c024828107444204550792113201081301100200c421201c1c0c107094a16519192000000418014400c090b044040120041120801d014024005051310b4441d40c0034030220010040090703055103c2c041035941d001100b44014040a00d04c1c0e802043c00d82845a04251280300150282d40700354044800d13051502100760798981c105d108641c60a544262429449d000791440c0341000e030042c54041000014150020018103683c1d2086030721440070350b5800641c48001166400c0038005030300a00c922 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 192554793 1250 192553543 192553553
    0x16110106080d321b010603170a0c1506090c080105130c2006010501030e0d171e040503041514030103031206170703050c0301020a1d0a0e07021c0e060304 67
    0x2d1028084019004218031000d503500300e01c00000c0f80745000440d803002600303642c51020081090858107101c4001c1c80840d25544078645001c00e61200000621000250700c03000c0781c000c506030200c0301e070302001c2c01d002c588035035a00c20001d01d454402da496050038119601c0001c0d10901809040c2c070f0000f4504034401418072908e2008081800381d035070a0180d01042c01000140020f070440a00c4802d0006210310360500000605580001c4600d0040d503000304403200460f40c0020101c105010301900c0014190b0f985141c4152505880c550700850000d440309210a10502000400955903505c11200304122918412170300c1703140309014540120b2040c801030000a1244842d00112020700c90003194164440891404501c0e003441c0b4110a503021403010410002c0130b20260440050440085080502c0710744068407440c0c1118000300c03901244c41c00441c2c155030300c0f14000701808003031014811600d1b000f036000c0c2d030302c0d021030350100012a400e0500008552103000c10882c52a03001d407110341540c0326540c076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 192556043 1250 192554793 192554807
    0x5090d0204180507080114010306090c05190f0e0403080f22060504021002060903030c0c0a060e0606210c04051305060115080112031413081207020906040c050304020108150916110106080d 82
    0x700f15407072a4401d00000c0c041d17440410710109040140002090703f8540404401d41c40710740e500082c1ca052100c0100404a5009010340c0e90110303140502501c259034144807002e400c040500c28004858030701240d2014400b90f503000c0c1d44200c2c400d692140000c03441c09020313a921b000803035101d45540d004100040501407044054035100c0c20340f40450384c06d056a951980265104040c0440d05640404102f000c40d207041d071041c44030790008002140c3d105107040710458451078107042150003103865001140c41040240398005c101c0e60000241c0f482c1e5615030303940441c800ca03000407560004802c00300204e40c109803001c44a20403036250701c03030211404401c0c007180004e802440c00b29904c3e5244800c005281d240c1030101920480001d50752030b548207214070400907030300d60103015540990b01d000110469160000200c80d0095024245001566201205e083d0b400442803c3d40c1d8001c4412745c188054003220700c80303204c4030a920340c440007881038088a03003908881c510b108880d41503000311281c01c4c1c600d0003440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 192557293 1250 192556043 192556061
    0x507050f0304030803072303040602030a0c030b030c100207090e0705090c0a0504170313030302073006050408070f300917030c0105010e0105030c03070806010605090d0204180507080114010306 84
    0x20800220400300003440ca05800c01c2750f0982e209500001000610181071190380c0d00050141410098070300180f02103030b81d40c02900e100c54003940034120301c400b0646c000c00500b801409003110510081e105200e249480d419240314443c050f0032400082001038070300c002941e140c42c2c00da95503030341000c0c40c1905d040187d08003120048580d0008204004490503102d100101a40c000c2d00140240c51901c0c0304200c0f200c1820724400944441c14184240580c5070b05801c064580c1c015001261544480c18085402d10420b04010100d040b4540c200c42000a26401032000c000324500100c500304090b9078107558202030888000001d01e205105004800f00c003917008250081c010102d07810314813850f001d14210303042a04040e00400c100c10040101c3c0c41d040001d140c2286c0700ba0301800f0440d180958440e600c1d0010b0180d141030080c0400c0d43c87c1d290719402c03003003440560000e1051041e155100308c6209039412804050b0b130b080c00340e00d402081000050182e09150040203407891035503860340c0c565200400e8004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 192558543 1250 192557293 192557327
    0x90402041211010f050d0504030c210f0c050a111f080603010f06081c050f0403030206040203120f041701020904090f110303030114060c07030507081c0f08061306150507050f030403080307 82
    0x100c20030001c680d103001c00e040940d88100c00310440c11080300010301480d4140c00f8110370804c640036803000059011500301c080c0c6500c004000429040a40040c504c0c1e0240c5100d02c10300c12a1106102116a10818441c000c0200345d000f0031034403190050b810242c8541c1c4c0581d0a090380403131140c4078028804ca041040c0e500c0f2070b2801500f450002150311010303505c103500940060340080180f04c15480c0a01c4841c41c1500744d10051031808450040c1045640607611a0741e4a015400c41c042104003000e404462500c08018000c20540c0c16901e00b210082a000e40295020584a43d003c80300d420004110bd05950441e0104284c42c54a8010002c00754400c0c80300da43d01c0e000750b0760b0001c0042c82c1001210301034180900603201038840c50885131048410f103480c2c0c008014852020000702c50f0407084c0c894001d10160b031200300c10700ea0301541c100a44225070291034000f00c8120080200e59010b4080c000b468814000d8a84282c201098260381c1d009601002e0704120040000c1103001d40070f820082c510011301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 192559793 1250 192558543 192558557
    0x11010509040b04050c1c09120804030207081e0f0106061407080706050114131802090c1c05070207090b060307080603100501240c0f0b0c090402041211010f050d050403 73
    0x62404181602ca0990342280800390105000c002449810340343e542a1b05013240c10400c1303150b640c0f034280e043e12050030450705010340f40c800304027403610a10800d0040e0911008403007100025046890341060710847c40140d0f40640380340b80c400c19030113010380021a0201c1c0c1c1c41c001002c0c2d20702048070325940503000480c0c038071908008401c005983ea000b068000e22810010175801400107040c40a8198180d1040c242140341c22120350b589140782c02c50680054049e100c00f5120742c0d880c40282a10700c2041d1000294803405014000240f03170710f0300190f01c20a080d9080d103a140d5944c00c8030038280c94800d141c0c2030340080240b0003d90120b10640c101075000382c0041c100c1e447d40e80071910039422030740e082e0000c81180580701603d4228080800d49420400c11a25016585452540b203404280414131002060050030348013241018608900743c850001c40200304556550f520314039400c03a88039145003111070702c922030030340030507580207101c40345030345000f512458504800510503000618004100710203110071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 192561043 1250 192559793 192559811
    0x1c12060306110705010b09010b0301090903050d05240301020f090603060a03140c0a0e0601120509070503160504060b0a0807210507050d0b03061b070606080d090609050d1101050904 79
    0x726000d0005a0a140031405a032054a400e2850030b540c0c0c583e081e54083c02080d8010461400d2400880c4e04590207000c000801070480c0c50126528401e819501c2d03003c1d4282000c1c0120520420440d20380364000b81e4012088040d00000d240c01c0c0d0250f03400744003e481003401510590300704031005685c0603900403c0006a181c032607484840340c9894102814166100f5001c00880f17040042c1c000d00580003402030410b1525001000170715031444105401c007a81e0321a00828588481040f0f044086d004c01820741d103170100360f046080c00c03d080a106113440385060000c0040c0003a2158100c41d0101c00a0350340010703d596a603401d481039a20400c524004138409445003016458903c02e550252000355107156403030002c080d442c01940c042c4c0240034401d41200d0140b20b03403490050150403084001e401c0f40c5807a403c031401c0c0b00000f8049980310041500503041e4004805d68401080015644a03455071b0231465184d105020400c060410010403102404211070650760040010780350f1040002c0c0042080c00c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 192562293 1250 192561043 192561053
    0x1204090506030c1005123d030c0602150c130b160510020702040e121c0e0706031e050103080301050d051c12060e0f060613030f0f0c06021c120603 64
    0x2480f110400051707001c640e2030031840e210340300e5680120124100c14141162901300f9100c040603601c0c05650310803d20100c200166294241100650704080d0201c2160b41e50310f40030b911800d0302d00403109071003010700010b1420b04404041c1da0840501c40c0354469407038100005404142c1c0f0024064503409803142414000910401103490003c07000840503884a20318414001078504411101075a900030000f050042c01ca0503041e41d564248a80e1a03550417110110400c0081a90868400c550b00540c103010900c56010b400c14107807200351000c9100b1014035407003600d080301d000703003c01080460f00304010000c91428080d0000701502400a4640560345010b002c14003500c9000f01b240030035010010898000020b2145100800c100340c0b0040040c5000c0300c20710301030400100aa0310a00b0082101c40d03038204010004005190b109400c04074a80d06410584490485100100d0b100780b000800401e400e84046490480348a40302682c11500814034001d80f44011200107a0303040940d1018000f010030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 192563543 1250 192562293 192562309
    0xf061b0204020f0c030705010c0905060c10051f09051807030b0a0b011215030c09020a081f030c030305070213060608060f1504030b040c080102070c0303180e01030602130501021204090506030c 84
    0x601c50f900009271003200510141c800000d0b0350095204440078070211807411804500990603800075140016541d031004d201108040e40b407001144038401208010440f00309a900042c0110103040d24020a60100320b00ca0355141c849000082000ba00d0201058000403650041000c885050600c5206004102075040456a40d9075015040505d03203d020800c0c4486441d0301000f51131200010340c6002c68820001c0d00550015001c0d20101c000100409035107030600c0000f41c05198420051402c440c0d0704e04008000350003510099200c0c403407006504800032910300c50b0004540e1940c50751811552040708216050000100d400d8100050502e11104c1004038001040610b02c11700411649041a0401441d440d0f01074000c050b46a20400142c000318142c802044110395152900030a42c10034011308280064083d8888803000d0042000803041100540141c91076a000000b00d080c0725a46000480e5590701c00c0c0311203181190208014001e10745d15403c401e40c044400341c00c403403c0442c40008941c041d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 192564793 1250 192563543 192563557
    0x152203050a0e13050c121f030809032407031103011206090501060522060503070518091f0603020909010b0109090c030b030d02010608120a080705030a09051203010f061b0204020f0c03 80
    0x4e05006c1e400c4070380c00001d40044d410140b00b8208411150603400d104080d000142406030301080320a80c0f1303a410804503d000310010200400703020706a00001d503030001a60840080f1b400d1000070704c0104c4489054038100e07044c1e0202d210b0b0001043d03c540700140054407058895540f18180401c1c1916a60350005c0e03440e0901c802c1450000351780d41200219a8650800c511a4003c071804002d1561020000301240a0760700c0446a95211180003618103010300000c2700c041059107840041407001d43c2d0165013124000d0700c016503d565aa15068200e510460300580415000b800c207111840c50340d07005021103030907418000346603510400000d10705516944444010703034442c1014000d168013071000c003c8550768000030f0b6084c410007602c0901102001485035041200100000e2400c01c2d0701d4001106041d044819500801c1c40968052610743c4240158078001c000141d0008009204075902d000d401d18064462800c030301990b00b0000a540701542c0401000014030144880e1002070000b4014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 192566043 1250 192564793 192564811
    0x6060a020115030818030114180a0b1504060b0901140906040b0d0506040c02070602030306010c0c12060509010501080c0a0918080309030304030e100806010818152203050a0e1305 78
    0x21046945c240f8010b02c03d104484074007d904041146141600a00da5241c1050300c003407522001d249082146807610010b000080c2c074090510091018505c01c00c010600350080c240c07010300c00707503031286001c420744d20407040070500250224074039413100c280a00240028210041450345090f03541d09545e842d40d04100e10750309403643d4071014010307545068403440c07090100358005040d1007480c1950207910780c000100724505001710f00341004d040090000d00e03c8040d01101003400710a540c10f0402100801c0d08542d170388904d6207800b0010a12020005482074105030091400703c5083c14410b1010107080c484903240014100c0030010400a80c0c0803000d103110300d441c0d0307005540300d01d13050500070305500c512400940124200e5100040c0a6031268401d940040c080c00c0580c940c1e100c07a5105d041e1211440f000d29402c0c003c103210010980340f80d0441074003a400154100b050020f408010741c0150a0b1800024007043c0300300060040c03203019140e0049201802012080302400c00848030307040d03038021240600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 192567293 1250 192566043 192566047
    0x5180d020109080706030f0b0d02060a030207020a0e070507032007030807060b03030c0d1d010507021002120d0b01090b0c0303040b09071509051309080a0507061508010506011b050606060a0201150308 87
    0x50380c7e9425105004071000e0880d488840d840098002c14034600c11004000205600050b0a000703544034168a20f00401043c881d0700340929007580000c286801820045000a0100d060100c080c1c4274082c0c100b42402c6018060702d2800e02c0c555448034245e0041c50212000c80e2a02d000c80455a81071019140700842000686141402c40030b00820025840ad03480f080d007003007032041c02d010703980c02402e48108540c1030314541a080e0310404141d00c0c058103c1407040c1d00000000720710f02d201540341c2000891000a0302c403030320115104c1520044a025084002d501940180300240200c0c40c02040d058200541009513030000da194040d00c000c0741035001c9140003082642d101003040741464010609464041c4004000d00310099540a440c1d1207000c500b04100607000c203940c414407110398080b800170b160b040c80c08490143c0d2505914060003040340c1e081d01007a201100124190a00401d010504d0f40c0704015000968680c020082c041c0c0100d94508110342d80c0e194040c60461040107024082d600036100c640d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 192568543 1250 192567293 192567311
    0xb0307090e090604110d05011109040b03070305100b150301060305010611060402010e040e0c0402032508041104200d151703071101140301170d05180d02010908070603 73
    0x5000094154003540c0040150010815010350100d5041d030130503400309034a00d002160200003080314982d668090040d5180101100381007005400804500c0410344041c40f00c1503202042503102c2145200c050255003004815484c800c64a90000b1921903000341850742c070b2042020440b030766030801d1700000081f0340d40d00c005000151308403002e910b0703080f1910001c0017586810b41c002400002601a100d0140e502c0b0029001c0c60786051110002e030441c00b810071900c1e8585100d0b41062001e05100c690001c8180303052401e103051107002103911580e08004003e148070340c401c0a01c0024000b084d00c10000806100095006000c550700402035642d85620104140000360315a2055100a50200c00d60300349a0141d40c50505001c0309031902d1a400c4401203052055010050f140f2044071802003c02c071200100128801d81391401013034007001602c00b142c03000b05010701c0c155003070f11480507403441130190b1000f542c40c1407500a080b0200e152062500d0070ba002d5898a10510701500c2c0e030403040102e03480c1c0b5155 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 192569793 1250 192568543 192568547
    0x3070c12021306030321020c01090f140703020d12030f0e030c3c01150e07020d09050618130c030903080c040b0412030908070e180c03030415030e01060b0307 69
    0x2150141110b000100502840c5580161030903e200d03030b202d00c107141481842103000011364103070340319581e00c03078002c2c000c80806140c00850004016000c44000d550303d450202c030020006041015658042c0101c001815191901c3c3c040405070507183d4100741d11601000351035086400303070f000e050381014011500c1700c09a002c8503051040300030740300e81c5100c240700c3d02c00c00c41008821041891111304100c80c2d4405c07880800a03015080d04002c0d42d003814030700b05000510011940c40740c1d00c01d240d145d00b618580c841400040364079146900c542c82e8805c00600c40101c81c444030300140015071030001c040c8080200e9001111041d2024540000e0110b907940e00c4141c1455009a41c1c00d81c80805400c002d03180038104640b026480c012170040420a440030b00c8441c040502408641c80501402e808495402e5a68110074026080032680c800d902d030340b042c02d41c1030b221400140b4040ca00710000c0186080900341492045a05200e1600700101519400d80c81c43c840b03828401c0740301a10030030000b580c2d00c3c0340010300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 192571043 1250 192569793 192569809
    0x20705100b120604081c06030b07050406080906090c04050702010b0a0e01050a170d110307052d0102091003050c04031506091407080714071e050f0304061b020303070c1202 75
    0x21005190441c4007008006941c200846e14240e4062040203003082500e5101c0c401800365030001070406400d9014130000d5078000f00940121001560703001d0442e51041d20058503010240d074000416488004c0350500352030700340c001d0382d0711581038400002d0b88014180000c0203030002d030b44142100e82c10700c0014402401e04034591030140c0310a0200c505401c0230600c2140e40c4014103141c44003003000a0050090850040c021140550307041700440f80412400c4405c0345200c030040c5580d04114070400c10100c0f1140b81030080d00e07031401004140e491b1070b00403180c042d8050500100110403aa408000200000e0140506507415101c4084002681803d114a070300c12503136031030740008c19002240108120607501c030800030344c4010b00307240603107000720024808400c501070800d00401051055418000c8406e9041080942c940948100c601c40e511102c0a1601ca01c5540182c4000aa80302d0000c482030f1b8074090602c1405202604aa00d03008650b1205103503543c0303075008807031014100c98010040d8582058 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 192572293 1250 192571043 192571069
    0x40f0c020d0201150e040f051c0e0907020d1206081b0f010c0206071104020f031608010f23060c0604080a0e0a050a0504050402030a0618020103050c040e0403050d020705100b 76
    0x8011003d28240203078643c130114416040f401044c0c40018081001e800c1d200e118035503200d4115001500ca40c034140010340c41c007050300c00010381d01140c01d1a2510b84641c44034011289500500210303010490203e4003038030031500c800c0d900342c0c4450000904a000b040140310b1942602d540c1e111800503078080128184842503481e0410000e842070b00050394600c41141d9031141d00142d040d0044241c0000729000c0c1c090f03207231050481c00010040200c00d01c4600c3e8416030b040c0c00c03a82c8038005a81c03500001d0845907401e002d0a11400810b0b0b0244415500a0301d001c40c2a040051100341040d5040e10b610f4900030303003110200d42c884000b089401406411043c24004590215070411441d414000410a4000940b007111310a5480b0004241036480603c240a90240c1200e0103202c0d105c8191200030700c0d0f01341741c201280041d140000081d44030718014143c40a035540442440e034103840320740b0b003103c080d0400403105852940c00c000d160006801040315800080c1d0060012030036403110130400c421403680341 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 192573543 1250 192572293 192572297
    0x130b01080a170a090605070c030219030b061806010f0507053406050f030a18030203310e0405100e0c0109090c0206190603060608061510090b18040f0c020d 68
    0x1c0300124805400c02c02c1c4c3d10030340d00103291007a2500d1182c02c25030407109060344060340000c025407070038418260b220100c00986c3e024070f0101910352256000c1c0140c440100001185440c280310100300d01c1c4d03204084044c00240c81c0d02d0b0041c10000940c84150904450700803000c01e0078a185112801c10131402c2d90740c10f40d18008103488080b1480c21074094507501c11041035141011f4000006001145294003082c0308410071480c3e0440c42030103140c06503483c0c0c0135071000c40401ca1000c0d10f00c1c0b101c0300c601c80e0602c44981000f46500351070b807034031001004400300a80100c90724002da5030b841b003000c4800c1c480c00da0328400000c0240b881084040009d00a84402e420141201c0d0808282130a0107400147c041d4018818000e4903481e02c883c0244203004110f160001407001c0e08198000521200008070380d4014034030000380c00c0142c2c11810802403130b400518841d80c00316040391800c118030038031040a403c90004500081803410024000182107a1700e1840702c07203016540d00c054180b2a64100500240301c44e542c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 192574793 1250 192573543 192573547
    0x903070623040b07050c0a120e0409170c1212040b0105010908150402040e120d0612050d03020307170429010f050d0501020408010c080a0b1c0b130b01080a17 69
    0x1a065181c08024002d0014160364564070109080382d22901c00c80304800601c2094030301c260218541120001d0402c80c520300040c00c07003107001143d49450300c500010786a100c6000c40c141d40c102402c120568028850305402405040904280e00048000505031034041010301301c0319142070300d800c05d2403440c1a0407450410407416414002054000f60483c810200010b58400c541e03160300c00075010b80f00840d0340340314600400440c01c0341c4200d40000307480c5d43c1c19074140520945841c0c80000c3c3e80118032580240543c0d10011440003058025401547c00030170700d2802c0c05060f000320300d528008200a807002c03030310240586070300d50545003095040e800d4400491944451549803c0c0042d00c10066402240e01c00d41c44510074200b01305003581120014160340c3c0090040300340420010709200e100300e404070201818004058400c0c80c00c1c7c41c0c8000c150340d0080c43d6000b415110344130071200090042401c405a164200304001040c6d02d090500c0c020603614000700100446468542c0d465040724203014118181 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 192576043 1250 192574793 192574841
    0x50108010b1e0a0801110405041d03030105010c0807080a0504090507020f06061216140a080705030316080c2505090f13080d0227091005190e09030706 66
    0x21481800e0409840c0010201c410040d00c0c0003c00d14292a44103040341e42c80d0000b20f1500701d001901600407144111010840380a407171070340c51501c524034441c000b640c1e0003c1005108660046040c0a0310340e0103001c3e560305085003655450480d5224a41c800081000490200075241c014000c899000c046071016040c0803c0300015195205400341c4464441c00140c0341298078041c0c02c000c000142c01d141080f10302c00356903440031010100c03590740e40c0c00d00440c026080882c0380500060514122540503008515148100317007102da40c0250a42d045134080320030080c01e0002c4c1720030402d55000c04425a501c04400c1c1d035651500010b020551300040c007507802d2008122002c00e19000b2607a00c101e410f144580300c401c003131804205510413507080549031440424900c03180d102c552550b00c9140d1309003100d000065508030400c14101c2040f00c241a09001c0c40000344110700b862110040032101100800c0c024544502150030306031400c9801803042c0c3c2c00890300c0c000740990f034004c0d41c45101c4040018408112 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 192577293 1250 192576043 192576049
    0x2030406051e070f020a051603020f010518011209080a0f1206030b06040f061212080f09031c02090d0b0f13051002130b03010603021902010c020a0f0507030209010b0c01050108010b 79
    0x700080854082c00141500c00082a00920582c203546d86d106068410340d104240403056542c180740400e0b80901d0046040e20301c1d6502420491b091a125040c442c19401c50900046602e100300b0314030a680240c948140c6400560008040c101031003c5440e107a00c02c50104100800401c00129152015030030300c0d000704082200d0034180d070340003141910007050714070a8a50342c3c8068403180d80000f501110f0490f10205100300d000354195111003550b100e0f41c407500d030380b405041042800d031107966039a0020001c111341844080c008038401080d00341e015003130a601e40009920707080220707030076107518a5074401c2154001e42d06900681c040140300703074200c2451580d01c490381c2e605000160300003401e40c0054010b01600a81c00340300d00604c84207200aa0b80c0d82c446000070040e40200545440d850384440c1c14107007490042c081c0159001c2607500416540e2019103991150740c0305448190340714080d0715008030158072407881c594083e0280060595981c80000341d09803c40314160300c9400f15034034081088203603503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 192578543 1250 192577293 192577351
    0xf0f02040b070206070602130602031b06062b0b010f030326130510020d020702090603010606140f09030a080c0601060c0f12050c06151203030c030117100e010203040605 74
    0x60340565020740c84085e2880e141c0000e220781507443c0d403003261000e0b000407102d50010040107100c00329039800c26000c0300411007070703503c041c107542081e44440240c02e030a0020b81074811440c540d00c8484070f510b040340c0c52a00d850201e0007003a000b051200020500600500d07030040381d006411000c03003200700704215590b4411400f840001d040039580184906070301c402d105080100e941010101c100456441c40b40c0e10000c0025800392038120300235440400007414516061050750b00b15200350319840d0043c0e995641440c001d034850001c21004200901a440240e1001c0003200d80a9100d105080e40c3d809111013407a192000507881002000b1b81d000c030203400106c1c144801926140d2208620343c1c40401081c050f14280144180c0030b400384191020083c0d05210003900f80c3c0074420aa8500c06800080c114aa441c0e00c01103860102d040010401040003010014074048841321070030556041c07114074812641540c801e8941088180e4000c41400140841c500c9a95001920020a0b500300005003030a17803841 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 192579793 1250 192578543 192578557
    0x803030411061c05070201150b16020906040213080705030106080d02030a05070609060c0e130b090f060102010b06040e10050a030f030c050309060d060f0816030b040201020c0d05010f0f02040b 84
    0x82d07000424004000102c1c14000500e5020714881440303185402d07140207000f0030f680c4140f42c140c07050402303001171010110b0003119081c220115444c1002c1001d5001c0c0301d402d2402805003a0441e41c2004811915841c040540d00589804406860f2080c5003804050075110180c10a10180d00f01500c0601d51680000884a00f050b00d4208581c580685007008401848040c40107170400e03060204040d502c0e503005400b00d070680e80842e0500d03640a1901d25000842e03084c000403681002484000c5809401180901544060148004202c14503144082801074100758041818900300401b80102101c14001d4400548015503408491a107541c60b9480d40001886000e820321003100407410038000305104903041010060600c8e0380e078480300c0301914000c00840c031559002c99400d43c400310b1000300c0850a11456201000c0720100607045441d40400600b020300304a0540c4244d00c0d40310010707102d640300500500c0c018400010640d603410b000d841900d40c1d0040414106204110034060303403944405581c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 192581043 1250 192579793 192579799
    0x20306091302210d181a030c040807060c03020d030b060f03190c05130923090106031203061409060303030c0c0a06020d061e120f0203010b1e0a0803030411 68
    0x307504814004114540080f620711003000890007030f8081003800000305030500102035521096800040e140700e1103000014080c1c4004110345001e03606105446002540d013017003000c03000303900d8280c1e103030481450210603620100c0461034808224040c56014800e444e084e03241d909051155507280c0000039040d21403014503050b220008408102c08132801051030301c42d28140241009400f000c0c00703010b0402d0700329a6601014170100c00c404500e41005000301c0081490b9582072903600c240d84c2c0c603002280c507001407010b4141e40da1203400002191a03030110018031013103510000303900b0b0b082c5225100b40213188208c190084a449042c059140c600004884d4400000c2c5001901c03603800d4a00c43d404c05800c2500030b041d460011821110b00c661a0703001c02c003291280b11107000021082008007905403090f20405c1d0710b8048504401010807445940000340502c01400010b030626240c0025500a0400c8403007110319600c4e000301c104500700740b4a010050605040254210310b425540c00c801c4804107000580 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 192582293 1250 192581043 192581071
    0x61b03040b160302070203060903191b0215120103080d05010b0c0a0305090f030f010e06011707030303150506030421020c241216020c01050901020628020c030304140102030609 77
    0xb00b15119a065a42e91070f4024203440160900280840d42c0f0b40001039903c400c01604103110803400c0c0581d6003412101c6146240080c01d80f626001c2210019200d03074410f001d14010441414070400300c6007001d029512441009131504442c0780d0f84001c0718016000303041103020801c036068010350001001610a84e040c0b0380710340e580d1022000304200c045200440e40d018450000d03008101030040d00010345424a41c011150261f03640c10340e400c0d8081100301000d200b40c120300740c2440481e1290f0000042c1c0000c00c8004010b9a0356400803c0d40c1e23500440c1d054030394500c0424690350504100c540c02070703004128801040700c000c070324000035070208551220803020421030340d20b20810210941a24012408444494030528028041d000c583e40f48810b210014054070340b08001c5036005106643c291001a4024485950303040741e0822a50003100da1071010b00400300801f0000c10840c0010516003602c100034544904142c54045140040703c0807a614076401401007160036119013614a038444812a2000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 192583543 1250 192582293 192582331
    0x120906020318060c070b030f0915010b03040303061a0a030e0c06090405040f020d0b01030c050102070317031308040f0e060f1c06090204090b180f0d050a031d061b03040b 74
    0xd1403e01c03814900349018040d582c1c00241c520721a070047e62040364101c1d0010925135400ea100350f11075801c02e00086000c0c0301440148882c01e0302402540e807051103401c001035401c0d2a102040242d00c0200c5031900810000500d100c5d500703034035024100705c1009140003041d50b1900040000c2e4103001b60103001b801965644001401d00c421041c00ca50141c0d005492081c9802c0d070750809041c441d000340015903650388141c2001403103510005035641140e0b001a6a041c581030041d032042015800642500d00d40d240c0d40f007408010032402030081c8010402d06400b6144540341c140d1035002d0800041c1a24401c0c07000000d402d403146c4411000c0030102004000c0d144000b80c00b8a041c200501e181c0602035006032424001c1810811800c1901340907000d80030200b01a040b0800795107503511381155402c00b850700600341c040d039113600410183c0414425800c000c1000d203451401140765014201e5204100e0344600b040c03160303456010035810301000b2803001051940c80c243d01c84a0908902405050005507040300b90 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 192584793 1250 192583543 192583549
    0x20423060f0409060204031a09031204150b0a06030f1103040c1a1c050609060301050709031103030d090809040615021b010306150c0308160804020d02060c03120103120906020318 78
    0x840040d42c81344086441e5a101d050182c8040907000008030000102d41c08148454000015605200c82c040c0b155142a65642ea400f03075034031202914410b05540720440141c0e66914101c011020701070940e40062111050580301050f031b840220740c64a8a4010418880450351107a00807040d41c4d0300c04640d10b460440340600d81c840b842160100c030704602c8100144903084200f80c00503400346004072015400e581b00c01d03040508030303070040d940200410b056007030404c0002c2010711140303a540c1000302543d040800017040380b019201c8240088400c401d0000c0c27800c0c0c0d24601845118090041c00e02a240000c00f10300c40070303550309940c00594000409403198910706030710075004800a4901030ba95010503035411140500b04c103103120000c07800b01d8a20000200b6487c8419030860810030640e9a000a07601d464003800102d0481c401c050b0b8202e1070400020f04d00800c02c000610582801c040609031030341c91400c0000000c410002503070304000c00c10504201e1702ea07000080e2614440c03000650700c0c10003400400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 192586043 1250 192584793 192584801
    0x50a12020c0a06021606050f03061516050109051b060708030c090a03111305091906090b07090807050907050a03020d060305061512010b0604060807030621020423060f04 74
    0x14407a40840510b20214a1076401310b9070104415180c0d21450865403a00020f4516024050001c040d0410500004082d46090380084140c581d00d001218680b0600c20450640381d10301c2c81054070260b4441e01150200101044107241408050041c60340c03070780c40000080c0c0740d40f29640001d040c480000c0081003040031034400312000302070001c26041501341e591412684418242b0030032803250900d0810440344280f5806010320030955040600440190501c4070042e00c601080e080c2c9505945030f00c0000055848001c4500454483d1035211102c0c1c078003029507280003080d40219005240c01014803a680d60404140c1c3c2e90606a4140540c94a0308010300c1e500820741580003500b03e104000c144050b0401445c034a407151102074031030314450118603e02c42d00303a43c80901002d400000030001040840d1041c4c20320f0382c0003200c0707107004945640e403200f5054910458101e40d01e100120a6809021480d140c40780d10520101d2403800064452100032071a506107005141c00c0c09480c08000c3d401c3d65580310380c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 192587293 1250 192586043 192586063
    0x1e05030a0c05010b130516030c0e01050a0c0209040c0f1401050301060c02030f0a030302220e0406051306020c010507200606061303170903011103011206020d020702180a0501060c050a1202 82
    0x1001119440c1d494179040070300f01c01d846604a01c50110b00b405842c80c464054028140c0305600c07440e50900701903004560941c048002070040051000000c40183d58400881c0c0c000d602a1800c00c0031f03d82001d010800c0040680d1200c0c07128000b4150303003074081e40c010b02924110f800d1803c18654481190000c28144002004d01c1e00c03c500030707402484101509030b8054403200b150b85002c5580c2c6a4072810840e10071005006a160303080c00c2c60000340003d5441c0d0041c2360b1018402d81414003142c044d541342c3c0c081ea00404124130050b512003040109896101038983e00c2004220560a41124054109030b140e29000d083c840c0500000035201c0c860b001800b40316402554030051020211602041107030300c1341c1010000d00d11950814680c90802c05540f800e40707042e0741030b4120000b4000301c0f0395240002544011010b004080c0c080c050036016a4414040b40b4100054050800e014980014103804444c0c050304081c09200c4500000d2021400c0007a18000c6261320050b0340342a400e02800a0345022070041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 192588543 1250 192587293 192587299
    0x40201021e07260d0c0c090f060518090d050c0604060e1c0f021009020907030908130611070b03041e030207090e010f0b1002101a150a080a02120703150801050a0204031e05030a0c05010b 81
    0x452245482f010621154846c000140c1600c2000309840e00c100d40d40d11813032038005403e511034004603010800c65404903800c0c0c04520102d505406940500f102c201c1c403d0148170000c03038018003c64400c1501400403040310804503204001424141d4005409044003906072820103607070340151000c00551208440914401d07012003035240c0d82e2880002c4c041c07940254051402d0160760030001d084d003d008242c1c0c2c0519400340c040c0ca4207210f001c402c0d2100c0621072400390110301c102c060001c3c4502444c4140040c840f1484004541244490420000e58000d58210703800381100c02d40c006000c079030200e40c0c016265107007070000c14150403940d02594552a01d4480961000e10885c0b40c41c4d11007222001000440e15544840d5a20f945000700c6004034040c40c0b160007100455900007580e6030b846a40300007050154260007690780c81d00d034040da07821254111411011035900103014014044502071907224001d6403d903060380d4645940c1c546440340204010390041c040702c0e615107003c100d000c0d044a8000f850203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 192589793 1250 192588543 192588559
    0x1050a05160c0b0426060403091e0f180c18060309022202071e050d0e06130915050a05130209031504050a110405040201021e07260d0c0c090f0605 64
    0xb503004e0b903001201945c50303403c80d0481964601c907280c1011450500c51a090340726604104e10301320b50105014015182850480d07070700381c8003140410305124041e000c0e0195010741d00d1089005001d040c1201e1104000100340510403042100404a001340042038451620700072880000500c0400c85451818210480041643c2e16001841c070342980900340050217800611003140b0381072426030b080704d218080a4070b503800a0151404150190f800504c64100c0034102e01e2070f0030080c481c03102642d050760f000031281e113403607160f01c2810518a624000240004503500481c481c41d1800182004041038a04400f064010540740b0a654040c0038000885c0c0c200d0003103100506e018a00380381c071041d9040c412151030f05030000e06d20301030800d4820b4900c07450f41a00105940d5080c0407040e4001d171003600f840d420521403600041000e51a190070024084401d04810000d0f80d05000020300300100c00101c2c4081101c1c03440098041518503503035508480724050002865244440c622000e4201c81c0c104a03007180c05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 192591043 1250 192589793 192589799
    0xc230a05120a0905090903040e130f061506030c0203030105090c070c08060106080a050606030f0901061205100606080c0403170d05070e10030b030d11160f06030b01050a05160c0b04 79
    0x4040c01003602c0c0380a40d80c0e00014540315010010024402c0d10341c694158010300c8148012402602040c1c3c01556440b40b424a80d42180d803000300800001204a640a4480c99120203004c600030205000d4842810203012414480000039540e000500c03402c1d20900c440030110361007810800c11144281e421440c000300d00e079110203081ea03a400c030038030841002440c4280000d00081c0144211805103200401c501e155032103903010080d1040340039096203c19582d454001400f1107603004150441c40c490340c090702d078007080c1c006090111213140d4014814051240100100c520318203084400b901c2c1e1040c03040d140203040c0090304072039002c0c126600640e1440c1c01d080c001b00b81d81000b0540c25008084802e00c00444e00110304506840c5401d1005805600002e41505214082d803020b902042240c41211803145500c0c910905400040d441900680014441440560b5150203540e24000003070030001c0c07514154400c01480c034403962104a01ca00420f10203c01048480320504005296084030540c40c3e9031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 192592293 1250 192591043 192591073
    0x21060a0801020f03160c030c030c02181005121b0d060e0105010906050f040b0603070516020d08030907060908030a0305041b26070e0a05040206190e0a05010c230a05 72
    0xf10a8541d41080c031500c01e4400517041c402d406400c10305a0541d030300301705416150b07401e40e0714111804080380c0c00041400e441c00c1900c45125454070404092180d1180c0c5480c00041c42026051215400c2894100d5104c186007860b40e10100d011211082c2d80e40c80d1002c420741016030003003100c0e61010700e00d942403200015001c810350f0030860a81d0011900243c40704506800c01c01140ca17030180d41600725074148009a50207000c1c2c0701a01c03442e0b6148030070718007102c0e0700d41c0028480b1845490031a18443e0100902c030040004000480c003600035400c040300243d0400384a195640a40340700c00c0c0405848400040130840d414020320214612580c0c0700011a860b41e04c209801d0744059a0081c5d202c2803220b5210042c2000514601140c05040c82c480003034550640c1600503000040c020b03078100f201041385508000c01220a0740c442c0c001a55105110382580f0308010184280307520281c1001160002003021a544038000914503103803e00c0403138031102401b05182444240309c0e000d050341c02240c2010500074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 192593543 1250 192592293 192592297
    0x2105010f05090a0c21021201030812090d09050d060207060e070317040b04090906180c090507080103050d032f0c010605010801080a0605150d11041121060a0801020f 72
    0x504121000001c503559901e07a401203480c1c44c0408000070380c1c803100764004510400c0801c030054014203005482c0901d82a40032004100c20ba000700c0c1c603001c0005181c1140610082c60a030030500780c9002d0074880c2d11200d401402d0100a006691003021070140e003400b0021207a0440e600c40d6807000c41071004051210740340da114045480b058070101589910007820006060499041d181200845800c05041000140003400c018000b00d03200d40c3c2d5280202e402c3d01110348550f044034820804602c1d024144131510064500280440f014070900c40f0040c0001400850701c000340c00c44074a0000760200145505281c403030540c810f89203000c01c500c01801300c0000c0d0303400240050728110303000348051641c80703004440e1100c0911807401e840d00300440785000282241c001c981c03c41201c1c03410000c1e40000d903002420542504004030713041401400b100d090790820780a03424020b002011018104001913a41180c0800c00a1145020f800301000081c21555441d482e5405861140000c41d100c8142c107910740400c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 192594793 1250 192593543 192593549
    0x80309040509070f0608430804080334020a020a0e04022805030303070509010305070f140702030a0f060c090f0b0403081c140a0b060414012105010f 65
    0xa038207000010b091104006825401c84110661104440f8540314040340d0014000d4180d424001107503580138800d048070320001c0f2203000d460300824200c0501007034aa0224401c1426941440f2260b82048007080031003080c0e990100b400e8031443d041c0e800c1c104002010705562100120b224a5040c1002d02d81540095007203107041c400c0d00c10750442500d8071a080b481c1502154001c1d40032000d0316074218062403440500000101e104030268841d905d840c00a81950001c9032800c000a00100ba02c00f000d680c140aa960418220f00f01650031401030340c802030860030200d5144448145c0000d0300411901c00300b11403040582c1001008605050518113032001e8038008244000182c1605000302d4043c00341c000290480c0d0701155140c2c6418919a0b4558481c0c000d407503203400040c170304002400c081d01c950080c0b41c1d42c250400c60f070080a00c1c20b00e901d941103940701c1101c1c0d0700a1174144000d21148140001c4510304010901b060001602648508800101250b0123101400e0914000207400d801140c1c109050b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 192596043 1250 192594793 192594799
    0x109091a0a0510080109050304050d1a0c1306030c02100b0a0b070c0305010e030a0c02011b0213061703040b04120203030421050105060103140f1005100905100905090c03060604030b01080309 83
    0x10742135903100c40600360750240c40040c0140c0c0041004024030304e4051244400944a00700000311528584400380004030101d800c1411000d0005400001c070b4144000b610140c1514201003100e0754118070000d545294010726143e40303907503900c0b80d49066980d003500200100b400018070380e510320407403600b001408981d10045500b0740c00c04112184150001c4242c0344401c4a603a20b511061096400440f82a01940c2c05035410141c004103aa015860340818002e8040403540e0101c0c9103423401c0702c00c4850003002080c2480c030750400c0c1301c1804601e0044040320201c89121185002d00c0b034207400040d04610555110b40c186151782c400d068a0890621004012280903500802c0940d0b186c400550a07210715504003841c0c120a0000503000c2c1e584407007442d8100e0303080358503411220707200c40109054600c0080d0440110300080c0d410002d41c640f00d80550302d030300314910700381340f103949042e011600c0e03400d015013113205000002c000942152a25001c0e50025078006040440c25607607540c403141c40b070f40f1141140340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 192597293 1250 192596043 192596071
    0x60c0b041b0b180603040302060a020f0412030c0201020d0f050d09060605190306050c07020904080d0641060301230409110f09060306070c05030f0406180f0605030109091a0a05 77
    0x183da4900201504c0c443c5030103030041e120b5646d920100600950021362804280d220500001c1800710b46500358080c0c5601c284c84850340c541460001a1800b00d41d40e045c103007080b800c41c0f9040003503940001500c8501c2d40301c28000c0f420340e01900e0814040c103404e0304659000000c00ca14541c868070a4040041200c1c0261410021601c52070b6045a1600c2540c0001e50401031100128001640e002c009225000e011200060b0598a94a29060110850f000d1520317640408201d95042c081c4a0f000030707141c1c0001d00d140003001d42c000022891600052281800030016401d2034844d8020050203013030402d600030070800c014082843c10340f100030130380313031081c0c1c046c41c00d191603220a42000c0c0d0b0168020321000380200b560b81d642e142c040340c82d0a11100122010301042c0121104000300c0405413014001070f446103004005881071010b4450155030208002e0351100e8001c0002075009402c49041d980b100501045640c2182007451801042c9035803241544400410802a100380d5803140b0b0140c0c02024081c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 192598543 1250 192597293 192597337
    0x507060c0f1b1e0608060607051606090f09020c060a0b0a030b0108061909020f090703020d0e1c050304030c0b0402011704030207050901090e031c0b130c02010f020301060c0b041b0b 79
    0x108074503000c1e0013940e01117000324000c2655032600f2809080120b01c0303441114214180c1c40354458040000394090b40106420304014822100a20101c10140107012400c50400b100356903029602c06000d001a4046130307541421904c180c032412020000355401c2913800d511560740d1410581c0d036903021102d10076a200c0e0940d072a035403843c013805540001d0383c00400c4050744694040c10004140303009080e080030b056081045480f417601c0b81c0120f502481780c44000c0c040400d001d041240ca40010a8001c40412404104100000c0d401041c41c518541d00300300c03510202d0703940b8401a6135140c103030b14601003401102c104000c01c0540c002441c2040d190190390441050340d89032001e20940d0452443c8a001c0d800502803207419020043d080b254401d0040004500200c55202007501c14552140e403000d4607442e8422200c52507024018940d0304150b0032000c614640c0f5210b80242035009400380282044203480208003802200d400e901029140409519006555161214a254005078041d441045601c3c092 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 192599793 1250 192598543 192598589
    0x105040b0303030f0a023c0306010507060504030c0209150a0b09130b04020d0e1006060801030210080601030f0203100e06032103180304090204030312090507060c0f1b 73
    0x411054000c0d00940c01d5407038201e030641e130501000b050b00c0d482c16400e00400309940c0184d00160006285041d51000ca40352181c90f0446100a03002095003607802003081c441143da001040390202c51f007001d0006000d032124075048440030946200a0740c4844410180aa0540048602c44030f900b021a905030072981e4444000c2194001e003001c4aa00c03583d4529055160091604000368082c0000c00052070180c3c10f00041003150b6480e00001c04c2640b110041c041e8640503441107202810395406d080745107602d55400148500c007140c07003480c100200751001c1091039000f60000004111148030039520ba01d04000c10020007041032040d10303401c081800100c0c255040208e00821003610240301c1c44080070a9150b0007020b50700140018030004030f940703d0310000d05414000341c80500300071100565036516500700185a40040d44488000b1844d04819000081000402c202114841d0421140e0200642454514201e1880300a4544054503683d14100c0a202c180301080c0e5121160080d0701113403031224 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 192601043 1250 192599793 192599801
    0x1c032406020c0d02120d0507051509030f220b03090106050d021c05030d110a09080c030a020114070206040e0403020d0c260d020c16090b0f060f041205030c06010504 72
    0x1490300941c2181c40e040000d07040070300b0015500341c00a0b00074800a40b080d02c0c0e2606e409035000e4428000b6001081520030007100b80308810080a039002040b0b030310300305603502584910601c88000400d0340c0025141c10810000341050320703065030b0205120006aa00c80388000305034005c0311a000b495280c8540850140350041c500700300c5a0300600428813400703e8100d2815085800300041d00c1d00d20050080400b040740c54002d258618035002c00143d01c070f4440500183c0b2541e116045440150007070b078dc0c404026280081c0780b807209502441e008440c845403961803981489183c41c00703500018000342c0400e044280c01305480c051880380e402c41e50f85003c122411a24000780d59002001204002c4903041540311000d002000e09594101080c03130070080703041e4103040343c3c401c1804036602e40200c0c41310300050006012500050407002001d10444061000240da038411041d6413911444000c1072007501110070b902910050003080783d0359201260303181000c558039041407004840501c40c1100100e101c0c05e250007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 192602293 1250 192601043 192601049
    0xa06050604061802071a0a020a021903020318060d06030f23120d15060206190e0c010305090f03030f0109051f06030903020a05010507050c0f06010501140c1c0324 71
    0x4110007402500e103c0500103544142c03019601010f000310000c0391034000040103400760009600041c1d44d001c4058000c4d09000c030380450050766484075019800841d40100443d2608000c10400a43d10034411000403085d0280c02c004da00301e585090008000c00001c1550590294018000e000039512a5a0b4280c405807001c0541106508011101003691341c04c00c0190440c01d42d2103070003064103620801141c80c050201d620407c0146d1101003400415040c0c110720003d50b8108100030300c400303c520043c05940c0c07556011810704140e030320000158144014041c40001110603400e4039500e051130940100c0b40343c4207000f1038040c50300d000041088181d482e0505c3c02c0d1a5907000c03042c2c04031840c0c08000d138004c1c4040384080e0258040c401100000030001e20a20784142c1003500c480791036140918070725140000c26401c1c06580ea022400505c000d030707045203103800c1d543e00e181c001903550540741c2820f6040c202e0104509004075558800c102809406800c11511016a02c0581084c085416041c3e9200003040c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 192603543 1250 192602293 192602309
    0x80c0607080a05070204021c0c02280203030405130c091e121e030305090c04020304020d080f0d05011401030b09280b060f130807030c050607030912050a0605060406 72
    0x36110000d1108806000180d09504003141424043e80201c5c09030ba0103003072440700c0280e0320f040680386030072039101390400401d180c03004021100941e40e9502e4018421803407041d48900b08000d180071036808000b00c50141201400390030010048000ca40081d1807400140004903010b03450229001400012061000418102c012030b402c2c03911100344440c0001c0f042c01d4620b0000441107400020008108182c118402e0f030340012a842c009282e14204a040800140719a004100b400003690314004441c80d140d8200b009a50b48110703080840c841c41c803c2c0a44904410305000001401501d04103c2510101c000c0c3c0b01402400e04500803c4400841140c8000a00354084104205071840341c0713603803448185d807110004006600c3d1002440d141c1183c1d28400000400081c010a800d04035840304d4010181c0e180213200382420f50f680c810b145d00d03560240600609020550b903007813510883c0441c00030054074402014074605411b00c2da885000c1c1003400d8404608090214145042500c5000c00f02c40d450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 192604793 1250 192603543 192603547
    0x60c030906200f0a0201080105061303020603180a03020c1003050708073902040605090c0d0c0215090c041103070509010e03010f11040f0503060606090f0d05160f080c06 74
    0x30000d485050054080b500312030b82c450311041d08502c04108000400201c403004000c9241d840c8001008071105800c8035018400c18003103020030ba55900d4000f02602da046905075120755480441024901465044040342d210700d5110009041e00402c41d400c403a0b9003a206070390314912960040d41038034001d0b5219030000d1210f4000810f070b1841200302000d00c10844698608d14a1100c5400e889401c24107c1003a229810419040440c47c0c21321a84000f0f0006582e4290145014003c00c28203020b500204901c0c503407101d0718807c00c03910038844c0300c0180400300060045402e00c241d42076651000060310a01a61821800340c51042d59582603d02c100300c03544c0d07003d1400010b040110f50368520203046581641d00c0301603540140c5214000c0c0340141c20039045c1c4540b01d0b46402402035050b5203650100b4000c2d04800140041340e261030007190000d00c4140d914120130318010b070108007010105080984180a5142c3c204001610074202004842000d6045c201c280c5d02c070031405455050b2080744603444041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 192606043 1250 192604793 192604799
    0x207171b1203060f0d02060a09050102071a0304081303050a110f0406030c0501120f0c0e10090308040b0c0a06090b090d080f01060c0510020301030302011b03020a12050901060b0706020c07060c0309 86
    0x4038004840008000d84407902c0e550b9550302042d0b558008d0324030500480d50341c040604c01541c0c104030f608000e10700040c00326a038104100565029100290001d003500c8000641c0380700b141401d04913071004561200c119a104100d50500b4081002207030b816501c070f0400e5183d1103105107000c0c01480d0590f504500004070395803a1070015180c903900d100f5800403080d101c55400020005070321070b000c0e0110f5191034036030700b801255040100c54403c1d40d04110900c154014184003084c0c1d84000d55043e501911002669013098450045c0b60101401000f4166800c0540010402a00080309402140c0300380c110348001e507803040c0544840508803210801c4007600001040042c7c880c17010003214901078015075801d482400e400606a03442608285c2c0542e4541d9005410b2503020120441038021501c0c0850801c240390340008d042c050b042001100342501c1c1c1300030549400003980a034000709402c20081e55281494900040a5049080b92481c14040c0e4200005c8660140b1010055160700d99201c0031500c0c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 192607293 1250 192606043 192606049
    0x2031515030604050a030e030a17130e150f030f03031f030c06180e15040c05091e04050105030105010503100507030b09070503150a080c01030b040207171b120306 71
    0x1800500e440c0e1018540c164400c9161401d001450149018001505c0b0490490402609000f0001ea8817070007a0701c18000700011a15064622419a032074000c1d05641e0502d800e02c00140c45526048045036181d1001401505442c0d01e0004079a6581611040e040c1c0f410302c020103031a4046803041d281280c104100003400212190110600203111500c10b00c40039440b0307280c0f200011103a8105802207401c2440c001d100b500646803041c0280180351081c00d042c500043d900203036030700c1c42149a0040d6224140204080c1c080c00540e40e482a01030080c51401c0c00d1110842039004101003024011443c04c000402c030380c00e060080c1c5050ba10050001c01c124075181c401c10000300350040541c001c2641d41c0c803010301c090307440048480c0900c4d01c642c0d0b82d603101d08016000c01e4451a403019000d100c0d981c1d1800c01c10081001040c030f04016102400e000401101b082e020130081c1c40340c04402098041e4440601c0c5c1c02d443c98801070244061800c90030440450640703c80d65880308480106036000c50300b0b00004160789 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 192608543 1250 192607293 192607333
    0x3100506130e041b0308120c13060e150a030906110c15100306020403080304210219080d0504050a1a0c0304020402070201030b030a150c210c051b0303010603180203 72
    0xf911522400a00b03001409204840000b240c00032110400d00142c2d842c055880e9003031aa03008444260920b1030522040d40c0c041e0304004a1041c0414000803182c1c9800650341c010022294003490f03902956100c407000c000a00500e00380004030341c8245011044101c12a40388280c4100c160031300300800b4500d94035205500c101c01c2c02842024188006100800020858005040290300c0744041e603440b41003d1810400d0041001d10f1125698040c0803612940c81e80019100404010454014540c19107400c00b14180c0c030038217509401440c2802c0c180010810b0014444040720f0051010880090740c1e40907400503018261648080050140045005842c19500600c600c074414180040c44600910100f82001042c1d181500c0d080c041071405002c0d10058080c1e81310040703003403030f060688450240070fa058080d550006c2c04d154a0365441c40d41c0710140213070b08503024103c1030071a040c800c1c0c41402d5400ea07242d00900800c00080d00f072078042003d00c84142d40c8000340c958003c0140a60614907010404c400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 192609793 1250 192608543 192608551
    0xf1c0b1f032012010608010b13020310090209030a1a07020607020706090603150e0f01090c05040302010206040807110a090507091505070b06031e070e0117100e120307020303100506130e 81
    0xd0321040220100030f00740308140041c080c11001080f50034141d0200075210f18141143e0300d20340d004004001c400c404100c2c1c030703800b5100002d10058840c5501c1d00840c0c40c102d0a80d81c000d01c11b41182c40c109000045c41c0c45030030b2060040ea0b003103500950b5072440803600d440240c030440c4081060394006004240c02a00606008c2d01c0002030145a1542d0b10b440c103078144c005484140d10001c03102c005110079680da011703103982603400f800d2040c6410b2442d40001c0da070702802440a0100c2c50081011020001c172540201c42c0c100700200852420340d103844061000700700607603501c40030030f0010a0015421041d100d00103021110303900e6450900740180c40320154071500421059050227245c118042608400501f01c00c060030100050408908140f43c1c2034260700181c106140044041151980c4124001489900c074200c00c5404101d52a0043c0060315003401c283c480c8800d80004420030120550001c09140304841c0b4181c1410241d55540900040380b0030056074400c06030035004140030781b0500008171070708 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 192611043 1250 192609793 192609799
    0x12070e0301090c09090c0806061804020a03052b021501150e0402030106031a03010510031e051504121103030a0209030309100e01080709080c0f1c0b1f0320 68
    0x1800d4850341d203030003080f0543d0304494540d0365503410950600c402054841e000d42280340042105041c16000a210300355103901d00d03802d989405001078115287c1c034030320000440c0d115088075000749101813080070701d1240058041c4140d003038000c03102c00c03540700042c0c40b003517010300c002689420790a10b42c0e041205035017100307143c2c1803001c001806420307a100d9100a5000740340076600040c8458800c1b080310120310042c1c1c140c034860b0381031400340107600760032031130420440c1da000203142501e020486903070030307000000d17000506140540b000741142ea400e9010b40f1407042e4031072004803601c210082001d0380d2480e503100000c3c05903232081c0000364441043d90b0042400b000f000301183e0030401030300000b5840d03100040034000050740440d4011540d5801c403034059040412810841100381c00c1511031036903072152802e214812091090701400da1b84910051260881c1d0050300b0700c05c0c0c80040d081c10324100d902640e02e20701c4143c072070ba4012086d08e45074100e0415039a22032020003071448110140d140c10348280550543c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 192612293 1250 192611043 192611051
    0x60f090903031b11070b0306211005010e0604050a0203270c06071202060c031e0a0b0405040c051f0801090e0f0307110108280c030f0e010504110612070e0301 69
    0x1001c03000d0a42003000042c8540c0d070f413140445400382e4070790620120364400300e003141c0d0500500400b43d0f0fa0700d9030502c011007090598012558801c0317507940350050000e254a80319250500104424002c020070300d21400302500d084c23000391a140f400324201d21048910031700072010706040a14208200e030201c00d000205804660000c040c002c0054800d03803040900321169140321074001030803601446500d82c404824160301e420b42c81d0100c9441c14201d101c039820406c50011200081441d90198407554140340040c10410103842d241c6401c1c440a40300d406280d102c7c0c1c0d11402e2003241460110300e5000e0547d0b40e552490386a9207404e00d4003026040100c49071049004140407640310322803c00251001c580201c4900b0b03000080f00300054001074000c0c01080c80e00c8c1d1810041c0e480c4146001180b000c004204400242d89a0444412402001368594000b000e60500446e0081c02005400c03490189000b444440000c040031400c0107e00c0c420a00c244090340945000591311501404104824010140c0041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 192613543 1250 192612293 192612311
    0x5010c0815190504020d140601080412050f1303060f06150e0d170f03040303060b1215032503030201050606090d020126070801260c040b0a080f031c060f09090303 71
    0x70706a1b000320400340192a9501c1c03a02e00400e0120180580102c02820441e1581c10309482c0c441d04200d600e2281c00900c03800080006032a21003408841000341074003540002d40d626031402202a00040318030302010307420600049030420030b040101165070340300d482c1c404d00c810020b418400c21008a64080d40c41c500f0088002810000d4140180024100e6649407550703460a0314010b0100d0300701d1780202d40c05120500c003030750b81608003406c0c0e140c0007035103640c0202427a803803000040d24110090480b034a00b1f2400a02d42401508020703c0c0310150788c481d4009201c1965584140583ea0152051059110401c45080000740d400f540e9000902a888082030301a0a44c00e21410318101d01a1610750009403207038010001c2602c42c9008004c00840403c010f1900b0414010079642c3c2c2c2ea8213035015119070ba846a00e024540e6a0a114000030881a0141c0328403064410b405504c0742c114440c200b800c1403c0c0d001c55075002419115510548030b01d83d1101031841d0070009208000d00c4004001c80505589001003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 192614793 1250 192613543 192613549
    0x8030a140d020304060207231e010b03121b0c031005100e090a03030605010503040b0610051317010e0706080f0a110309060601020c031513020103060308130305010c08151905 76
    0x103500c00c1d07010340001b6a44040524007075402c40381102183c0507900010b4810796031580041800c0c0880c55072145a194442134080c0302d50300500c00a00e401398580300b40196005280d0040f00501645207103591492880000c1e0101c0717a0b150300769001400d9140e001421102da02c025a60310058001701004907000000380ca8a425843c01841036540450356809440c9900401d64140106e01c003410083c80c040e400c50920380d0b5191011000501300318800c9800d05a22003089120742c4c2a03400115004208000b001c0e5a2100c00415240c9100001041d508020361110400380003d907a1701122000c0d0f48400003075548042010011201414070300d0141e032101d038509000070300c403400b95010340c0c486009440c55007003010002e4a4400c48a8400303009400010703040301030136940f6080c40d901c8456010088002034907440100c004081d5500b00801d543c00220b00f00a080c0b400d10a91425684604020041110003440c01c0d112030000701d030806064902c02000c0001d9042000455584c42081c601c2c0d01aa141ca401c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 192616043 1250 192614793 192614797
    0x2010c0c0c031220010608190803041211120301050f0f0312030a090609060507021b0607080702040e0303042003010614040c03060306050109090204110702061605030d090309150201050108030a140d02 87
    0x40c4444c03070380d100c00040c805241c00344015141303600158400c8400301d09076030700d9551900000700301604003002145900308080c0103641813070b02c95110324243e403800e03901554801c40c10340084c000c042c000e4a982038000e11605050baa0755001c680c2c01001041c2110100d000c02c9111342c0010290031a5a840321030b00b0307000500900a0400301c52080030086018034103090300a14114035000d1100c40400f1180243c0803c2e11668112000c41e0713004402c041e075070500c50010501030000c00e10824205c2c4000401c1106100b040c50b8a0070000c0d0f0742c0c1030300306070190080741010300743d03507450088607901e403001c82d2540c07070714a49035102d5400861203050120700782c0d030340c0d03110f460486200b6400900760a81319400b5000f1031410b84203e0400403441c003c25130a00300c040d000b02d5858011070040f110803001ca418007a0905c01d0070010703a4800040b445044c400030312240350007003000240b0702c1041380c80a1003110680045006000c0c80e41a81c4180d070040d0304110600d102101c58400900c0004a000d008000c01e03803103210a400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 192617293 1250 192616043 192616097
    0x803040318060f08150a05040c09051207050a0806090705010309050f060405010203010f05060708030c0f0706020a2a051b060714030301061b12050304060f1a0102010c0c0c0312 77
    0x150f1010954610502030040e000c02022030020400c05001d550080d40c49192460640380c05a50004a2414074007040d50714444641100764481c20501603414400310001c1c00310242c50042c2c82d0782c1161a666507130141c0da0402600c00000c0b42e0041c48052185502c20350100305418020310031110300070b90200d681400c00b40166001d54143c4d40001c0140041c0f20241c1d120b02c0280070a5664600e400010b8440382c030940406812410551400614010807640020540d4030040c0c001100715951805244080c5c52110120648005003500b820074000c88a41049101156a003001c00b81c080c003a8031a1404402842074030103a94054018403000001c07840c012440b00080711018000e6540307504040307001d08480001d940300d40c40307910031310f008900044d0070303480c4401000c8043c28426107a45407450301c3d0000d0701402c660038040e1861b000d20541400300358005500800381c280c0081010840c013110032512180b02c0711000d030005014050820000e40c040300141e2207240c0518008030510707035400f50120341030309440d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 192618543 1250 192617293 192617297
    0x9010e0f0a1d100615140c0102070c09060f051e1201110409050f0f071d0a090c052a150a0b030d1e05030112060209181e0c0c0604080304031806 63
    0x10500c0064954504c40c04010381508011140c241405040007012a40c00c22502a040070001c58414020714007501501c40665020109001b004d8851030010300800c0070344254404030051000024090805200313a081c1a14031300002e20f14413003640c1c18011016500e4245142039075892146404640c02007000d08082d001441000c80d0a00300543c0700e660028004e00310b294603204080900c29840d400c00e041101d2334080c0740080300b05c08070810004202ca4070302d034462081982003139865440940d0200083c180c01da9403035009440003411600d11180c021410240382c21690000d030390740c1c0705203003542c0e50303c0d501403020030001c1a02e80724900464100040c1c04244804a42460000c05250f5a0b881146a01180a141050440d850941000d0542d104690003034103440d4006400c0c1025210218404001449d0b200c21141a08108060030020340e9040a81c400038000600401c1c040300e400700c21920151840e000030065a103841e04c4121031540f028004400703100080031011344010140703440300c008007115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 192619793 1250 192618543 192618553
    0x20903210c0c1002030a20030a0906120e0304061b080c01200702010806010507050a0b0108031e09060306220504060b010e0f0901181805010f0b09010e0f0a1d 69
    0x460200c900c2c04840c108450320501032038101c9800c0c03a9000082d100f00f00c5982c985108000403500194440c5111500268054000000c0070102c280d040700510003203034107650328180022003041540080340c3c1450b02110701d6400c104420040d248c42810ba4400c3c0351421001d41007000070316a00d4015642c04426162000d03512048002010039103901100c04050301e03100c0003407030095aa4002000c1d4440185000d05102c17002c600d210510201704400c141e003541c452695051541c40e01c1d0020703580d80103a80103009100409200a1004030190300780c85004001410041c01c540302c210030001012680113010a2100d40001c8400300440701e4040c3c1d60185010725030005107100c8150004000d540701e02c0382c6074010003c0b540c88011646640007511704407580042c0c41150141c050f1040d00281480e081980341c0c1e4050a1018000d000c07042d40025100d030240700e402c12400e011b00e000c1c010a0582445165103105400c0c00083c1504100921150b01c00343c4100002503c4885110035904a0780c1c5a10120160b404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 192621043 1250 192619793 192619807
    0xb0d0603020f12030304031b06090f0506060105040303090e09030c06010e0402010315030f110f0a060216080c0d030c21050c010f0204180923030c0c0405070f0302090321 74
    0xd040241a40c4243c03003c0148840c1034150958078440030b4030042c00c10415030001580701d16240302d0107502c0c40e8840c00070302070310485080029015a03103080580d0b0707500803200441c0242d0f00600448044941c1034640690992500140e070584000c010545e0900b800200074886843c80d00b40f058a028002d1401307201c0f49400d2074000102254801c001d281d4100201e50400c2c80801e0019000741c01c000e074070200c07689441c04108042040445490315403500020884070215a1640114074015110b400d070600c5043c40b41d6070441d01d6036170b21036420710315000902510541c0c08a8813440380d007030003207020b50001d4110403044011003001040d818110b0300001e0010400c07249680081c000c4c8070049800c2c1c44250704207030416202080303001140b01034254560342c0d1140d500412014654000c1549081c2d1154400c0e002c8111210b83c90b54481d5018102c1c0d03003e51300c1c0c500d065251030f21415018250310340e526015071443c035005600a51019500035410303c40c668038410700e154100b000c4050b000c0e070700c1d091a4803202 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 192622293 1250 192621043 192621049
    0x10303090614130b0a030f060f03150b0904080d020403171803061b07061508030310080a030906080c091306090b01030b09130c03140a110f0a06180b0d060302 69
    0x884901c1840340360004200d4844008085104081511850302251780d4a490700b210030b80080c40308000c408442401c01100103084142404d081040b203000e90000780c02c4044601f5810100c84503000c010b41d010701030b03a0204012803044000ba148515680c000145019160f0b00c9007a5051f540500450400400041c25240d007540400241e1f54004160010500c03400c091681100d202040d041181245601260b10300900c10b0580103000c50690b000c044800003501c5410ac00c1d200c0d803086a010f420341c0200280000d83d81000600507150707a4041c1d42c1d03c080c0707a0401da021a070181c00940440304556061015403910f68582848440010080b00d000440b18689030400041d502800c100e02e05041c60302811203180d40b038605103075a00c420200720701d0480c1511864041c40540340b41e00044d004490008125207030500000d01103030b0590140312800f10500312103040100c0d01241301031864119152400c100416070180d0181c080401d0700d107001640040d00c801c20602150810020101556120003040013541 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 192623543 1250 192622293 192622307
    0x4060506131a18041106030a150909060516020c01050a030e150610020d090306020703030608070b040509010b04060e040b1c0c1a040303050406080402010c02040e1b010e010e1c0206030103030906 85
    0x54580d030703c0d450043c5042e464a031910321151107410b0146000100044200c0102d5100c03400052580301c6004180f03465001c080024600510101c84482c074103800306802c41c5142402210f03407070030b079402040150030444c011200b6400840d4060103040d2a9015a80301c00d07410301c9410b1700010724400d2106140341c030f07004025817000500002025074001d0020041c0981d07214001c42d003640c0e0403020150f5200d2091900720010318166000c40010b0240240200716610380e20000c000b11101242c0020481c0d80324092645540700b5072081001080d000c900c001c51030b003480cad00418103054008001d2003462801410003508082d80360380441e4224800c01c024059002103604100910703190541c04da04050840d0b4024100d84100d01492081c405103100107400c681c4a4001d1000855015000f0711a07118160705950703840c01c041005040c0e00ca60302010096035481000b2421080505a490074280d2048800707005441c62044c0100a00584c0d4803155005625150000c500031442035441c1e107030840c80c00000134481 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 192624793 1250 192623543 192623569
    0xb09210a1a060a0b0c030426071406030406051807090c030f0c0e090c0f0f04060f0f0815010c050a030504050306010e01030201050703031e0c02030a0e0103021204060506131a 76
    0x2540742006100c81c5807100c0305241c054031100910780e552503107600d005074558011035020482901035500d0300360010040c0c43d90072401c10100411170313000544441904c030203a5603c4d000190042802d00000300403891036044990840e00b183c0407004035031a90307580c01c1d080c005107030030120900707031980c0f284582d02c6d03414400c00002c507403181c00401401407850001822034641c1d801c483e01c10325003100070034903212500007260f00b108101125103645011400440c40c260700140f03d1600880d0340c0c4c800d180303200b074007032107040015155a0369540040d0340c860a041100e02d1107403805070304001081900500242c4108260f4640b140240c40d400d0329140780c0404c252608005810450310252090010001071b60450280c81d98030364075040c041159016540c5025241d040741d807101c1e40c19070a023100807543c581c000c4000d2110200b141da4010041c0403100c0190306910405000c08004c413207038000500465299802207802c075034018018800d00c0c00c000e0b0508292150040b0500074030080a40d110854601408414a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 192625899 1106 192624793 192624833
    0x1b0e070801030213020a02120f0d052712070201120b03030d05070e010c030905061806030a0501060305011403031b0c0d15060512070b09210a 62
    0x20000d080c48143c0c0205400400103640e01024021034490030102e1b0014030728180340660102081d4070011a59044450a000c01d00142d80703103002c3c2c1c0b0300800c0522806201e130403818088002c0b082c0101c6488405070b0107002c205048607540d01c161001c185d02420070b82c036200c51180e0030802030490941c0060b450f020000c1d4148000303209900c050300030802d035034a07080c4102000c00190b50300b10b40c0350310144c0840c14002c070810040c03030b2603802002158242e0607070392440451000421000d42040c0d88030482261940d0040c00f039035074140314050041c40301d01000c11030703043d2000121340c5a12403410720350343c0001d00810081801c2c404000c03c8041000182020720748a001d800d00715044a81551090359090070075100041c3c40c07810060080403800c2c140c015101c201d280c88030f2601c1d00da1005400b01d802c41141c2116038503c00b29100e08c043c0c00b03c0c003800988056030040c40c2c070b030014121140307641c50 = true := by decide +kernel

theorem cover : BRFrame.Cov 192446043 192625899 := by
  have h0 := BRFrame.cov_init 192446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 192446043 ≤ n) (h2 : n < 192625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
