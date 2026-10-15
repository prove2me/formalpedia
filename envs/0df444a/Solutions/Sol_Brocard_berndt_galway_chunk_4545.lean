-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4545
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:58:16.458316+00:00
-- url     : https://prove2.me/submissions/deb1bd2c-37d1-4286-b00a-643027845a07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 817266187 ≤ n < 817446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 817267437 1250 817266187 817266217
    0xc0c08060610030e19150c0e060708030a1409030d061d01381305061201030b040f020d060615140f090a0503070e01170f060601052503050a14 62
    0x400100030780c080d02800740c0107a03150050116480c5c01c948035001540c0c4c458407803114150b421140315502011100d002d0318407410820317170625030000c3e6283c40040303801c0c1a0700096101c0d140c3d5100728071035020b42000602c42019900040501030701d0040000508060b1880c01000d002054451000c0c282c2202d2003e08604c0c1d81e01000010807100c010080240e8080010911407941601c003850382c04404031b400d1240d03000c00c4200003580740420f443d1341c0e1010054a81140c0d41450030041e80701c2c0a0200f03d0601001e0703e0850310f000460300b00200c014180c1403066001d0040d95404403a4107041c0e0080c5a00c1c440c400103203036810284000e1500c148008500e012808a0450800703c0d0034404010540200e8242d5402c81031409001c102c40e94104520030003807892680781d024a40c100900c042d00c4030140041c030501030b071040f903900c41c5c2d113200845c609074459000c0c0390803a10b806000e0804030280d54155250005045c401d0312043c1456400b800421007589161529403696172990141700d00f91103800003c0c0b11540c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 817268687 1250 817267437 817267459
    0x40314100504020f060a030b0a0b043012051608030106080606030f04030e0310020d1b020d02151017010f05100f03080d0e100213060801060512180703030c0c080606 72
    0x5c43d00700098541c20150f4a4002002d85d002d80109045000c29040400c0c400c4011408125004001d8800100020003058421946104600801d081d100e441c40040c80f100c1c194008070b500e41d115005550444440001c4484401307114204070005600a010341030024841c100064a282000800c9901510460700d401d551a80c83d40c0307003201c81c00d80da180103035494007034a01504208041400905500506008009150260604034000f440c01454294080d90040900c110400c0d070003280782c0c10302103000c05e004800c940d00c00b075003440f034040180c02c4940b0a20035454a640c8600d01544001045040400100b129803200d241000d8001d000344500c40c0e1041d02c0007028030008420001910f03c003038940901040c1c4000030041907040050800c0360001e480d6001c04c004842d841501c2444005000b182003400d01355040c414014518421155145e88100c414000300d25a800346644d0160700180000680f90482d4407451700505480c0381c401c05032001142034901082c1003201207003035070190b0f000a003a402c0341c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 817269937 1250 817268687 817268689
    0x228030609061526030412080415090e01061202130b030708010e10031103010b030d020a0506010b070b1f0e07031415100c210509090a0605060904020d0908040314100504020f 76
    0x72004d0160b0514503000900002a2001d100d000c10783c0c00e14420003215131564100000b000d5000ba460f60f032181000035080b000c002212400c0021419240f007490610305800044030901d0192003590522801c0e03001c02c05000990000307160145000e0813072a40d4580c46640d1702c20784101c030800165007014506550b150100001864030208070360408001c1c0010828000400c0060304000c00b06110070096002444000304128040c400f4074094040100c0090502e411502c03040001c807402048081c103080d0409803865425017011610b0010584000001d80d2071400544c002c000e00103415900729400c03000c1c000304100340381c180d81c400c80e41c03a8054041c80350404010401c80e10062502000d4a05a0407401c2c0b00070080c03010054508a40156100c090f580d01000003401001c82c00242094080c4d46444010700041d80d8010448080040c111000740e162500c2007041f00041800c10700040603980700040000c02c00c050789442c0c0e0b02409801c820b0b19036440049600c0801d640c0101c80c020360142c41c0c0300a8040b2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 817271187 1250 817269937 817269989
    0x60612040303110f1c0b031e120414010807050a170601020c041d07050f0d0201141c060e0c03060d0b0619230904030918021c0f0e010c050702280306090615 68
    0x440079076100f1929999150278000400b42e020f500300380f41b203490902004c0129608041c24070703040110740c0741180c909291008020010b00d54a503081462150070004184180e200304200341ea8004001d000300000c58102c1280c00c1d1041140415840c1c1d8040c0c0e0600044d00c0c50500f614900c001d501406542141c805680111740f018010b01c200700009409022030b105000c261030304d1020403000c11130f00203a042d003400c4400d80107072401421154200070401c1084800c2d150400c80041140d40156048415269240003c10310328203040448851041c84000040403904100034500745154024002c7c85104214140808260200c4028011600544041045540e5400c0741c048026010b040181032510701c4101035841024041b001071000c0d111015007a10392440c0c410368000d6104240200100007402c10050280d002d010701c017901c598060911281142c0640e11070801030001c3e004450074440c0c491800b0f900400070454107481481c6400e140c1854820b0888ad035005641c1ca0345403050a510030381c1d000880b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 817272437 1250 817271187 817271233
    0xf0d05070809150c010204062d2001020a0206010e010906080318030c0603010914060f0a1e03020a240e0904021011121c0203060612040303110f1c0b03 66
    0x1401c840b040071415600c2000f2409045661480740004d82e681d458010020100188040e01415052590090034400c0c004a04400041901e80c1000003100c820505081101c8107a01c0c4001940c0d40001180400b03994003251703080c1a250f0b4050b140644c0d0340c0300d840310812201140101100ba0344108034082c0e1088c0d842803902d83c4080028202c90000c500000032034001c0d0400c3c1d004001e00303900d543c085001c2c0c0030315210460b440f80040d956002e19100f030400060960140c3c0c8911000e0302c0007020900c0b10380c04580340044c040c6401503c103040c0351380c0d14401d24840700c00701c00c0e14000c9a2114190040301074170606408441e407030000c03d5236070380e92144d0302041410f00c651107480b070030301c040c4007042407041034140f00c80d0485540c281501902e07207464604010303800d49150581c840303441c4100100442ca990f00d2095039100300c81d1040c2e00d40d4680d15460160300900300d155042044940c0829000307400ea031607000800d030709080c00703503140848074000c040712095480103a429130303264102030030301440028012000a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 817273687 1250 817272437 817272439
    0xb0a17040f15020d0b01020c060f130f0e09160303020a170d0c0e0310050105030601120f0b091f0c211d21161b0b1b0f0d05070809 57
    0x61075244540d5540403a59025089150542d00800c024068100901c50801407100070300240410744c0302080000d01ea0b00c24611130706d00c42c3c0804a80c0d809004040d101074070103884003644030482c6c1c54646601e80551001112031018a10842200b1681c0c03960410416080f00d506800818600031980d41d001402c8642c66a003034003050047c00403400801c014069905150400e442e4403180e65415030505050180460198980d98144401049140c1340081d080741168401904030482c0d03615441e002080f540c85031400b400ba034510030b082c0128100e000c980710780030340b482580c41c2d10b45a000b1001201a070b41c01c02c01c00400324100708440c0341c00c40301180321607a2100c6816000203411b5448020000000d1648444e894298007140d801d030301c1c003440c140303040c01c1d08907906c0f1034079007807081c044007c030446032124074004d1003d400888032b4040302100300110b0003d8840a84526190003c02c00720405480d0030710100181c1d0b12400c00000310b80e00c004244421070600c01e0340c4081c905010741e282c080140c2d011a4581d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 817274937 1250 817273687 817273703
    0x5061e0f070530040819020102030c0615011b03020604060504050f0706050310080115090b01030f0c2d0e0621010b030a05010f060903151d0a05070b0a1704 68
    0x55400503400388042034095a000480d40301c00050381d51507014a0740259400f0203280d00400040c00000000102c0760a01440d450b03500848000d980300403030850091070214805803159005122055001d8050585c1c662130aaaa034000100c9243c0c0501c10005c4111001d40980c1014000c100451926007100340d10502131400c0b107000d116640c0742d0360f00e80b40c103a43c00503001900c04024810310500c001208001040c9000080c4200700791041c00b801d038070125205041c00c86a80d5200903205134001d40140c618980c20031410002d881c0c0c103c00c048c02c9003584080c000d0078200c0d1032010201030b031400c81c40c041c00c00d48155034403248001d25000780104e60740401c0c1d901c41141c8aa9048500b00c41000c5034842c040c00c16030103055228100007242c1821b80d0b0041c0c10400a46040d110103102c2183d000880c2340c201d0741c000f250128808204660b101c020661070038103c87c0402c01ca15180300c041d80000700e601941d2700c10801c40302003954515028415010b05034000b000200400d8010500301d40d0001c40c25002381c05007000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 817276187 1250 817274937 817274947
    0x702162108210c040f0e071e0c05010f0510180e03040b121302090f0c13090c0e03070e0c070c0b030a061d0613200f120105061e0f 57
    0x101c0305950400150640000540184010841401c1d00302d2900043c41038101d81c1001c0c101440003110b41554081d80c400d210f012400612854850540c6e811407132002d081513505a02c900e04000d0110300d0441080d1801e60908800501d410024400c581c41100f03150403590705a4180100c0040d502280e0031090246030f00d0b0b561480d12024280f009100500c0400c01c1d00e40d0f9901c81500580103054014061031074440d520000201580f2030f1803415a00020b6002c0c1c01034140c0d10032012030018000d800c00f0007811300001c034000c44ea4020325071046a55503903030307101e18850482a0041541d10402409030944442c55200401c841c0710428028200e290310912100c180c0329160208042d90342c00840c0c0d03940059440341001c0210204660f0002c0310185241c640790b09500e0140c01040b6807400301e020080c1820b564181000c400100e004010060041d0b041d5143e50350062180d4120580d00560750048800c0460400003800d4909541103442c0103030035003c101c82880e6011030750041740c0c220081518005401300030b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 817277437 1250 817276187 817276193
    0x905130915060e01081203010e13051f0f020c031806070803040305031504061d1f2301020a0510111b011b030c120b24030f07021621 58
    0x1034203803007803051000000e070149881240d00310028181d10801c0310360401c40543c1d0608440104485c1950162000f00005840305c10b8144c859480d140405804c1303014031655488069056481c035410010000c030300f0700c501048410208124070400c1c4828110703510820490607106200e007013407084810300504181c105401601c541d00c80d0b6208443c11800100004100114011040302d100d00603c4240e50030011681810040c03c41d10315104000481c280425000400c0100c162481a8190030860300404469945e2410f101002d44524200c01040c507420751501c5055200154019150341c0060040c20a20030316800303034004103071301c40480d03082c003400308501704515000d40e0070582003041d01070000603000d4524046c2d0107080c0345040590304041c113181c0d0354074220f0390000c0c0000300018000c0f00060f2541c4174400241285180301455125030251040f50007a05030110040c42c410400c0d500400000d036503940040740c03942000411014205001d0900380701c0341640c114200c40c040b00c6056401a128842d403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 817278687 1250 817277437 817277453
    0x12030c0f05030a350403050309070510050d061d011703040f1d090604080405040b1f03050603060121030f03230105030c06070c060309031b0303050403090e0709051309 73
    0x40c12a5001c141c000c07044d403a007241c01a4061504464200d038505070914070041280381e610010300058200400030012945160060160700010200200000001440000e001d07003190000d5104d0001c842c42d25500144105444501d01c9902c8500f00c0000e072103038200410804804500d1089036443e10040c07102141e045c483c004200c02030034580c05114004555054035070000b0b1402031225642e5001901804000740d400c00c203039400c0d03a00484001c03030450942c0b0045074500246501040340c00000326884544075070144d000600a000071390544074540e0b00e40e03064004e49450b281302d180070791266041c1140403a10032011030110700c001e8a80407421840360581c2c1e80d030700e20038100785202030100300c40100002d01d005c00046020520655610381029503c2e20f0390340d034800c014400c1c0c000345034541a10000f05031280556a1005514440000c1c0b60880d600f03000f0010001214100c0100390504000320b4454082c9610501c01c543da566082d510600b0303d024044034003284003401c405551038590b54400a0648 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 817279937 1250 817278687 817278697
    0x40507260105040e0d0c08160f14060c0a02030f03060409020d03090f050a08190c0e040b0a0f0506060316120908090406050d030c110a0314010e010c03050112030c0f0503 74
    0xc011000503541420104001c4882040032041540c0c05600c4014100781c0001d160f000b12600b0240c60783c0c94000c20250380b2400c41d9803510043c00e00a540e41408204411703013002e0200c40ba41e040c212000da503601e6006617a58481c410175100036900500c0000381c0d42c201c0c0801198050006030001c00c0d0b441041d40401c0003005c2498040300402d8440c50b050000b9001e0045010051004030742c401c401c20314001c3d050fa1601011000d15280d10b03c08201c000501c0b00700d02490004112100038640903240074107010804050981e01803080600b4000c030451080c14078010340f40074440c01099a8903603151101c0403201440ca01c0580400e100580300c6607000d060803032043e0300d0b4050040c1c5000b44d65800c0d02041004039000da401c2207200f100e207000c640c0e006c40d074014803020b0450f521503020208400306030300148a8196542c8000c194010003540d507015400190817402428000c8030013480003c3c0d6000d070075400c0c0d410901641c1610040980c40b400460b20038400b040c1d02e180102380814060060b52030701815079000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 817281187 1250 817279937 817279997
    0x11070602070b0a050709050904050f07120311070e0c0304030e10020304080c0303040e010b13090609060e070c05061501120203010f050117040302060601080603030d090606050429040507 81
    0x2001c15201c040c815a803440940c0700040150400a83c500740802030010b100501403540210288000502008010401c5a40c0100030300f046807441550781245980c400584001100020300350003034030701d070014002912402d40d200c00185c0c90250350380c940c1c40842500014010350401012001d10600ca80f01c00e44131007040030a41d0301641da258181400706150041503107400e030007a0302c100020030240404581c02c9054a5001c0d810613903c461502080070781c2030464100c1141c042c0b0304680051858a640e00c001c04407421100032007003d543d18030003503030078080321080517185070041000030345064564401000c50007414184540c114240d51240b0301260400d0308000001c150036034051000e0b60b003140326a40070074011a0400400e1170507039002512400c0150105c0d041c4580c110110b01103070b40520a03104a00381090040100a2250134004098100da108441c029450990110b401001c60000407001420091030500b0004495040c0401460700030802010884404c41900300080c0d4040c00e2000214 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 817282437 1250 817281187 817281191
    0x409022d030a06050d05061815102d06030209040603140309031219030903051606051501020109021e18070e011e170402040f0c020703051207020121110706 68
    0x10b0714500740e2040b02e40c1c1da00480d128204205046001880020340541c3c02200d0640f103102081b8804e40152a2010b11103040d0000c0ca000da040041340c0909003140f204599450070800d60700c03121400800f6004145807441400100c00e10010300c0280c2c002e40052500c500c01a1000503c0d03a5251140c0303001d1021003808030082c0e040021407501e00d01d82042220f115025950400e031809440c11004140419501e404d60289622004910140350154013a5044600c800c0400d401c46400792134100000d1200711078000c40d030b201065030502c5651051044000c400d6018041c42c034100ca000310112140300686144a030b00c079240d040c81c42c0c440404050060b00480c115192030b01d00400304400586040362600c003048003562003050040e030b007540c04a045640d80466403403804143d1038600104e4050081038686140303030340c24010422415a40002c00400701c1c0e01980640d0403c1c00c810380185c130148500d40780030340016414100900400b81d603e401c454103000140d0002000c81c6000c0740989903401c840800c6d68816 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 817283687 1250 817282437 817282441
    0xe100204120c141c02030304030803070203190e0d320a05210f0a1e0f12090302121312030503060108130b0c0d060302030a240203010b0409022d03 64
    0x2c0401c408070b8024100c918003080c0da248000022841200e0742004850042260b9450003095480c18412038002d1500010010382c0da240c80c580c00ba560390700c0790856145010324050f101c54018458042502c183c4030007045210511041c0c1c07500701c56030034142c40d000409549a6541b4030310f400071400006440018030003610044d05a030502c24280303c2118081e01103002401e0700388020441007411110762aa00015403a16620201822102c291001c0603066001c00c00302020348040740c01075000c8040317650ba51b60341c8011342c580050000507500440802000360380402a68000d080c0640003070f10071400090950440c051b91115598440e4803010f005802080001050000a59114801c03a82c1300300b0003011035040c2c100c0350f511140903410040600d1040b4501240707140090301d058124000458008007159501410b0b810a1110012511500d810a02c01503040114aa010b4001d42c2c0c1201c0b120a001401d02d0700d4440050040e60002da030f0100d0014a08074110700d0701c1c10801004045140c5030000545034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 817284937 1250 817283687 817283693
    0xc02120a020d1707020a150b0d060e0106090b060711031c0810240302130914091903020a11040615020105040219080726060412080f010503060a0e10020412 68
    0x2032030403c007090240c07245642000b441580000312540082d0f40040022009545040031400514005030340d20f03400021b480c0810709204080e0080400030580a0081028507510540d40040f50a1642c565822100034841c401c0031070303152103e00341d00ca500038003030b04e05522245422844444400f06014007180041003440807076204000000050100d80062800031040560004007011000014000301500040d45c02740303d2007480701c900000c04803481c090101e40450501003032380342e9046540740164850b13640b41c80c940b603030400c42e141e10458154002d0614904a030310758051700303070440551642081c0c450304c00103100070900c1108000104103a00002c1e283c01d1038070400681ca00310038070031820503a07040d0301405440400f1038554215440824014440e40c00750b007000c60042071410345001c2e64001d900410042c89114075210742084001c2e80c98018558491080004090080c060550554000790010b007003420198440c1d03292000040c11560503c0b144660b400c20fa1f400358210303644181209140c0010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 817286187 1250 817284937 817284947
    0x50f0402094513061a030114041b0e0a0e0a0209160917030405060702040b0306040510050a06061209022b02090f0f22120e0f01020f100c02120a020d 65
    0x103241581d030202c06450070400c8000342030042d0001d02500c120f070344040c03000010514610391740c01c00002900074008032405031943e224240342100d0a480d03401000056036010000f6803050400c0c0c0d070315212001c0003038a954038100d0050001c03607441c0005204e40030100016030340781e0710744500c9000354281e603120b0380d001208001c20403006a400050300411030940d4807403144001c41941d0941e5402d985c035903228803590002801a080c5502e043d5010300545007070109201c0c0c0400d00e201d1210840d103040c09191981b02001007120380c18420280010154610050144480c2d003003021142c2c00103101180e230035a520304172080c40700f0203140c007241003048030303070500460510b1554140d00041c81d00000a5034908940c0400c5000d03001012071030000c5080d107040d034442c0c90700150700b04203c0d0400e00c580507002c20385201400c3e46014001c11403041c41020b210f414950b100003000408603078100c02a18410400c1c000340c001070321104ca0300006500034120940614005c0e013014124070b40a5600804401e081c3c480d02801c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 817287437 1250 817286187 817286299
    0x41203110105060303030106261e070507020d030305190509060a15120206070201090b0c160806070c0605060d020303070f0201030c0f09060507141605010e0a050f040209 74
    0x3503a4140420810325035000b100781d17411128a401d001d00c207202105441c1405103c002c4040003e0910f41c41489190b042c400080166900c002242c582e00341c4400b80243d90f64003070000001c0d4040e0004400000092183e040780342c00c45443e0030541078606500f1a0681a40c00440d44035219600c40d90821201c41d903070f801004176541ca4403040300002030401b00c40c0c582828174040b0180c01008009030601c110b92052a608004007804480c046d210908402d140f9201d0070b614a001c2001c2c000c0c1e1901144400012800d103008518a407210ad070740e40e0242d55010081e1200407c511b074885800320f440c40250314140000c01050340305020240100300c00d84000340441d0295515202004a0340f12a06145a00618554291005c60400e103403240344900e00b188140364036240c0440240542042c01c1c2114421600007000c0d0386c1c2c00d8880000c04012a001d0041d20395042c450540e10440c2c0048001381d508003540102440c0801800c200480c8100f408001f1000343c43c001614075440ba861000020300b00405d801c06 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 817288687 1250 817287437 817287467
    0x6190e1c030b010e060d0b190906051f08060f040216030302030f0903070b0f0405010f0606080402040c081b0f040f030c030b090309180603010914152d0a02040308041203 74
    0x344c0341c800004040b0300c003405a81c0e004008150ba0703458100c0b40d0b90341d282d02d49884503225800d14a80c03d80316035080300075011034400c443c0242624202c840c281003a031141001c2c20712081d5580100c0340c2da9501002140074070900c8003034105a00b0043d1054034420707c112444914040d40380035a0303e041c170080c98003545400518407890b9810a01c0144002284003202541204080707504200342c2c0c60f14100140182080da40414206107402d0300010503030342214131a8403031070003110100040341c086502664900700845010040542a0f041d21007001000c4014044110b241d200d903500300b07600c0e07005409501c13030300e80c0050710381c0e90140e10101b081011200001e50700c01282e40c080d60034a104080490942c4440e6024118102c103440006a41a102544403c440603044800500c5901a00c0c1c4551f850390422180540c62203030b850300182c08000ca1001203a191410f0880d0340d01d0060800340a00050040036004240c40391702004008045402e8001030405800e00e10481c15000103549400303820f0240e480005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 817289937 1250 817288687 817288697
    0x41406280603080702090c040806010905161d2833120f02070f03030b0f011112071511040f08060723090d050703031b0506190e1c030b01 60
    0x1400083c0c512415940c0c040e030b0599440010761102c16600c40315004507040131080b40f1a810000400c42c0c2c03540c002034016844160019503c4003d183c00b155034400082031001418200c400090a90902c0d40c1d00010038a4180d0b800c01308031b01400d4807500010308650217441034080180400b1000e52610341048140e44020444401810007090042e0100c1c2000b201c041100b65100c121040300c1d40c55404540b03010342d11840001c0754a1507454003400526021030301030b02400200050215650007200103440324865000100724402d100c2880305490ba1000000301c401d002c480d4682245052035000b48092070050706545500c46090000d5420080c845a11800c400e5018509200030203400200740d920207004014001d441d030078a03100d80b4441d44141c0031000c0e00422031942c210144400803400e41d09a0b032081e03030303080054080d2204580c1d444004076805400358001202040e598002031180b01d80200c0c14034004039018055a0489013426040c21260280352042d41c00c5a001c940c0c0352140110140d0b0034209 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 817291187 1250 817289937 817289939
    0x306010b070c09020d060e0f010f0906050a262b080105010f0c0302120d05060901060801030215031b030703020309011d0c04020f25031101230414062806 67
    0x480020b00c1d603d11526000b55400548039144002036003145019002202c0c0401142c181001004030101091007550f00381c038004c00c400b040001130b0340101d00440384000c24480b03155040080a8010300000c41c12420707606c2c84462042181582404410940e004144015592100d00240d0307900c0e410a001e1407600304615000103200a80e00203d81c11100e0030503241850348529540b5081e03240480301500107040000110b81041d81c1c40346900700c14420041a01c01304502d9036550706c10340d01c0a00a0000035840880d0018101189610320b02959100e80c040451040c1c6c01103000c11805c0300d50003544e003100001d0b000020400211424007801c400d20b201240d86c6140c01008420307064588018004481c071036500022101003d200000c156400708806000c2d04c4029651060442c254a605020031800304021000d02e10704240107106441c40c4da1800404020407003a0307002404204280204211610816100d02194200003045201e102e4074507003070084212442d100c50107480003051a1008042414148 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 817292437 1250 817291187 817291193
    0x6090a11010804021c151a031e0706111f0f240b0f190201240609030b07021e0d09080a0c090203060d061107061a09420306010b07 57
    0x741170748040d0620010480c00d82c8a4030305a24400c0412000c0003009040543e80d00c01d034440e80b0703004d8500d04001c404035010020741310051003402c82e10100411407a04581800c018050040800ea0001c0700c00800399080560f4515120002c0300140c6441030415540d00d2046030301620902c259184012184042c818a810b030135200e1001101c140104185000049040c03880652240103484114440b25419031000ca20100001e0003007001981c201100560020f006006503034484926054405540d00c0362106803c540740c5001c1c1d110302928030320031072207100c081400070100105541c6110f203640380980100c9400e013800801048050b003240140f90441c004110020b00c0b1200e01070100c921048000d600d9541e683c0c0004c0f03800445980c040c007194103100140e00350b2001c078001400310500c2a441049240c0010410540703800c0340748001500141c607040440d0940c0c00c0c2494424000b0047c0540721004441c401400a0503100f1a11a0440c078031041c0c2000700030310b801e00c06280580380d682046804c0c412030391 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 817293687 1250 817292437 817292449
    0x20130204090c09090218280305030703020105070815101403152b0f02030a080c0d0f090501020a060509120f0304020f040b0a0905041b0314160510030f0b0306090a1101080402 76
    0x403101e02c102c00c1060752000c45c009100c7c100c0741c03034107007840c1e031440007541ca040064a03070303008800c210019440c002c00540d0190040501c207014290704402d11a80c106501d0600082420102104091003910300010b2040b00c020002503100700c0354810295840d483d01010f000c0d5556844030f041380c0c14120000d642103844055403049007255007011007034425040900101e4204040d200c400351043e000050000c290700000a030306954440d5503590b0804000001200f22800811409400c0c0142c0200820b40007041c02900f1894100680c8030036079441c002031999601c81c0c0d03440740300202c03200c0c2e00200800095103031003004070040c1c00c0140c5041c0422003094000900318440750003804401607440011900340140108844003c0340e124201740310440d140c0c20018541940c502c0f250f1014803036460a50005040c0295000c12590003800394007000c80c80440c140e0243c0700c0c1c20201005e0a9941d400c103c2e1a035820052507018140402c0500070f022410300302103201d16003070100301d41801020302c01c0c070005803602 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 817294937 1250 817293687 817293727
    0xa030e0606061606060302060705150a140609180d030e07080a0c15020703122c01080106030f0f380607110120010c17010320130204090c090902 63
    0x7442c14021210f0407407900100030320035078001940102c404030b40310080000005807804000100407658206956002c00c41c000d442c076841400d825118000e02050090800d0022036070490f043c0489600c414810314405440c11240038041c0e0002a16480c0702d0f40d508001307200ca1006040c150001e02241c2c0015120142e81d003006200d8003140f2032040c2201c0d44024800e0080070b014541c040210400140d4444004119031042050301740c130112400c00365030103c01810140c1483c0803044c0c4600d485a860000c0580003021022860075a40c0d440788000f103544c40040c4180351600d01e003040003156800c110301032502407403010030044014400b14180000d495403450255603555620001d41e001c00c0382c3d03030300c0129448584802590303002214509001c00c0008103402144007000e03503585183c40404180c110000c02080ac1c4009007020340c010400e0004145044158151184082d103840c06081d98034600d4822a4419405a02d000d80c0c0c4260541daa168022200002844201d034150709004001e071010300c4015107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 817296187 1250 817294937 817294957
    0x11010f02210f0c160512010c0c0b060d020d12020105070804050a080703200d030509031c050411060705030301081006050f010e0103060914040203011b0903030f170c0a030e060606 78
    0x10124411031111450b0089030f50350070701001a5072009000404020002c10f1038000c039031007500301120701c40801c0c00511500261140c140d030b50843c110801c2c0c0300c0180c2d41201a040540160342d004c49800540c07030f00686c220006d0710401ca62b644c60b61000000908559020b020642040040303020b02020900006602d00d030690002a066030b5202c2d07a150584980204a20540ea00e032148158002d540e803020500344031454143d1010320a0b6951040c8441d101d02c6211780502262048112140d642c40c0c3c2c950145a205220300c66811050001000140194021081c00c80c0c0c2d6a10000041c05081018440b036032035800303042c07020310040f03003404005036071206d031182180c0c100407000000d80d0682e03200c0d400c40c0005110030078042003a1004446c140c03080800444050b402907003406014100c0c880ca003c0a0500e0301001e81c3c1e4907098605696044030441d0f810f0607414100413410401d41508000710705210300904868080711790300e10b080c86000d0244e6601d141910400d81100082213801c0e00c80300100e840d4025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 817297437 1250 817296187 817296253
    0x60a03080d060909050c130522080c03070f030306060c150b030c061801090f050604060f0c0804090507021608100c030e010203070c02120a080d0e010f0911010f02 71
    0x105032072100041840307501801083d81000d040c1070900402080103000c080040c0e802d0310f04840884030080a4603400d5581d07581d00c0380e411001110310012180ca51540038464004985455028603180f4915044440705407201e0501d80c0403d8101500361042000403c001e040604442d6240e841c0c606100150102c9280c1441d02c81101d07901541d800d00004401e0000104019207a080881400441265142c00340303000c10180da40205926054018100032560024083d07846c1c141011021507172000b54110740780074012680070b80c1c000104064040e0014004010000881d454000300c02840e03c0d0340d034482b406955001e80001c0c00003c0f400305407070790700400920b000300d260135031218120020314008140990951010042c4411258010b8010300b50714000c0b507401c044180d440d02034a03251072901b88001d250310020852082c4140b803982100b00755a14034000001e88656a104850503070b800040d08844009008001521079a00100719084910541c4000c2202404026001c1246481c0c02c0051881d80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 817298687 1250 817297437 817297447
    0xc03040203150c04090b0d2319050109060f020a090512030c07090e0d0f020c04050c0904150806070302090102071707030c090e0d030c0f080613090f0605060306060a0308 74
    0x1d1070030054207a034420a2180342107280740044035203400350414011104000e08107040c069151505100102440d5000b051904560384480d00c40c0d000031040c0e00d09000540684400d0001c2040c440c0060301590303003e2800802e80104501e0700c4011a50607140107658680706001030795034107910040402c1540c5007624020f004415840240707103103020310004500030348140d08001c61000b0054100131002d0150000310f60541d01400c0c0c00b43d0703640014401c03190059000e000e20321a6031501d50003003030b00302c9001000d880c684910300c008141614a41ccc1310b0f0048080c500d000c100400c1c042004900d034006814a400c50604001c000000e48510302e03442604440d000c2c1e14044080c00c00280650300086504c459440300090391500300c003015042052100e2070901520080c0c480d44e9000c1c1c0110036050500c3c1e030301d201c802c0401700c1040d242268040d1600380c01481c441026001202c242c403c0109a0740501c041c44118034076890110269800141954080d4020405205403a11017049075026030344c0c08500c0726103807 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 817299937 1250 817298687 817298689
    0x1e0a0624050c032a03090114130315050f0c030903040302010e040209031926040504020a031e060f3302010e0106030c0303020609060f1b0904152103080c030402 70
    0xb8041d58102d41c266000003e203400e0350340024134500314000c465003290b85000c4280440251a0f0050140e200e020903c44054210f081a001c0010203100400405141181d512515050181c1020100507000c1564480178040d0005000c8509036006000101c0ca51035494000c0d240c1e43c60b8011480000e052001c0366401007450ba40c1c9806941000e20042e046a200c0122070302003166594081d00117850070313007010440390001513a1441001c68048003a81c0685081c0c500b0701400000d51040500604141d0b84102048220300a4110001c0d140b00d60980421078508108034401c029545521401040c403c041c840c2041054403c00161100380510b801c1c031b4142007055069014025280b9a802194079054011080002004d403082c03c0d64020703802c844281d134690320341650718031094501111013108440041c0c009028242564a000c00d03850880c1d080c158401d01290039100c0602d00d000d480196030005002031b045900d40f0300240c12180340b2210101c400c1d070f01c020f402000080c04016031107100100040c25 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 817301187 1250 817299937 817299947
    0x140105070f1502070b0711031602190902030a0c020a050c040504230d0809030c1c0c050708030a0f2a061b08040c06090b19171e0a0624 59
    0xd1908140b060441070000c80d0b0307202c0294400c01007258044004000724100501c03a502c0c0c6104400700500640c43c007200000c18910701c4020b00760880e48802d240801c02c2001ea14a0708040081100c1c040141c2c5908094902c402600c4152049408660040d54007001107239000800b0305685070251400981c6803180e062507960340085005000340c024802a60b01c000480001d5456190030081d52040c0c190b840b030040aa4491044a0140c00300758000460720b1914020b12182e480002d0b800c1c10300c0040041d5070342d1454200034031343c0d0140200b904007003407415419810012124407000305160100c41c00114503404605c004603a01c203c805020f4003e064001c11115500a043c07141603800350503d04c100b441d2005015400488084880e80c0c8a0344001880a02034034141094449d071158541c101404044004404004482035000300518140c0ca6244089001c2d003ca0013083c0e81c80340a045a030003801140d04400010341034800b2546824010000107140c5003284640001418180304c0c0000ea415080b00c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 817302437 1250 817301187 817301213
    0x17060607020303072004020c0606101b05060610050307090902071a2e050109050f030a0f050f0f16140a03020a06170604020703141b060a051f14010507 66
    0x50107210001d115403d0084174100034813103840b81e002801c001d0708220103000a0340600703245000c082d401400403c0d068981404c1c540710545442c500a412010f10f2b460030440c08030808015140e90300f0100a1145600f801c014480346580079003011827940c144205d000f8904255441843c284a0b03020410204005a29500491101041d901c1c0304039820706000307040d0b41c0203041060312600b01c0704d6620345507440d04540034503044a1058440840d00d40c80e1200707200a100304030740115032501450220741c0001d03040c90040e40303130b050142d001083c2c0030b510045024030707265140c9001c5400340c0c4841030008100211100d248260341c0040c51001e11509031102141d450340050b08002e600c1030143c1c1d80800c2060707018079030303500d04d080c0c2150504d21a1648000d10080f07100d1203001a0014411129000458085c0d02c02418a1f04078800704881c211a141410342c181502554100f14158444017408a080740006102686020590070308080e540703852078030005c0c00b000341d12080c10301c80c02007415800c1c010f584400b04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 817303687 1250 817302437 817302439
    0x3050c040902011b410703020616170f090312091e18090c0102150f0103060b030304030c12030305010602010510030b1f030501060509010b041d04140a0320030702011706060702 77
    0x800d55030004805d8481544580c00c44154041d40d00e20720a07950000031824200c80d0043c121a28080b801d42c40c91011078403482041d03805c03110300c2a6400e21061180000d00001001c4005d0680302c5220504160524000014400000b0001c0c010075503150780b80400303180101d6814210202a0b0095400302e4a140ca00d48050b503409240501004201900442c58445000c0d0980c266154518082c1c1c0022000030195025407207002501c005000080f600d903c10000b180004040b64100ac0e6695a143c0d90701c00e46820100031200e580b0b400c1010941c040c0181805408940020301c4549400380c81c0c105071200600c0050650118080400c44802075007004400221078803501504c200e45a00f0070501070321184c0f05060050080c03600010309002490156015a8540030312000560b1000c1c03091804d0714070140c029242c203d00b005440580c00e40410113040c13184d21949803620920854011600d800c412070510f6895038200304003100042c1ea100d90b60344540604101041c00c16120751001c07440c103004801c002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 817304937 1250 817303687 817303733
    0x80a080a0e0f06010e0106050a0206010b0a02070302060a050904050f04150c05040512030408150705030c07060209061204110a120b0a14010305150115090302043303050c040902011b 79
    0x44808002c0216045060b110846415246a6a16003040b03480f13220341215000160050310050000c008000c1c0101308a01240c41124070007522034000800d103500001c06940440e00000e60360031282018080c250b4071207428249281c00e4505a10b480d00010441500721300030079078542c100c550f080d009205403005041d0103000c2280042c807071140c15a076640309000c0c021480c4600310741c07494030f445607400719403240c031040c0d0311700e41143c4845902c41000d4018000442e0744d00d80900030140d1580b02d981c090078030038807170001005907800e050909141001038003150901030f49400314240200160501510742c4158001e88a0b1003d550f0401c50200800321926080c0400440a0001060010000b0000000c11b41d18001200907665030520807400f41c59941c5090105038191001c101600c1c00307602c0480d84e19112050b00e1118650130a850203d427625010f110802016010f00344203004082040b00d172a200c042d42c0821141d00c2c9500043c054045009500500d20006801c000810a0b018981062621354440e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 817306187 1250 817304937 817304953
    0x50f22020a030e1b0a1a0d020f0403061b1d0f0405091c0207080d0804060f050103030302190201090b0103061d0102030c0307110a0c090f0213080106150903080a080a0e 73
    0x1c010003a00f600301d0340e100603214801d5950801d4454403606403031090000c21010b8500c6ca401c582c00008002014000601340040c003581c42401c0030380c0000c048881100c52040e540f58103524040049032202d00000e901c440315011640505500010259511503007014243c0c41c038014100042c01c0f82140740c200c1c581141c182803d11554410014407c1d114000403542c4c0c000c0c02003105002c80c0c3d5140300c3c1c41407040b540d2200309000045400f4030a5180c00c0b6002d043c0100309042007203424402d44000307034400ca00190b40000d4980854016211345490107059100a01800585851340d00380d5070410702001d402259200444c0410700f501d6807031007144880c0030009540328900041518041e4008032516008103890000c02c0c03000e80d00114003000c40c2680550300c2010541812685c00041a641e902440707030030b034204000e9000340f01d0038000c80010402000046102401d181ca1b01e0304070007481c0c0380a424001042e600744000b8440900b1744600344108d00d0031448a50b104000710700038090081c4496464010150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 817307437 1250 817306187 817306207
    0x11103130e0103060b1c1506051206060a06140702060904020c07060908010c14160212030d0f1103060d0f03171f05030606180613020a180b04050f2202 66
    0x2014100c9000b1541046481c0145c414480102e540340c8140844107503544811000841003c10100e180e40980000140075840b94003084100c0c80d5003c860006030b008808020f0746161081114000e003010b0f1410403050040c00b0450456800361034402442214081956443c0b5219070703054880120801c41103174842c0c0da40707040c0600116070714043d040347c5509040f0203401c01401207034816094401d42c4104c1e0302d07185507845079103801e521010040b41d02100345e040c04455620200301412600305840d0000501581400015080b1990341070071084050703003401044401d507035091a49440503001500314407181c80e28581183c4192080030424a4841241b00348030664880c40d00380c015081803651020041c0e9100d0f0105a03640104070b0354541d0104541200c609012003050140f90802c8024000b101d115030302076140300c240e0304034098500004114200d1f182c07407588900c083e80020049003000034507141c07c26000ca80c0b41369801400c00c1c00307103003105510340038151403032041c0913601e00301c12045485034a586 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 817308687 1250 817307437 817307459
    0x10e1813081c0605010c120c060b0a090f0f090201020d050a02120301031401050907140f0105090603071806050301030c0b03130501090c090f02040509060906120601091b1d01110313 79
    0x200100b9901450100049440e5002d220001c03000303604007240d052004070f901001c48074070f00c01d804102e440f640c840c54a0001c0d900e40201d9800034010b410030215660700e0251002c2c2c101c0e592602005065401c003100540581d03004580101c03241e007107140007a0b6600e6454411b0b8541700d615180507d81c00000800001448002d03034103190311808101c001e0090781c0703030301107419a59031542c06181000900038880907000c2c507000307103400e038030b0041814140e0400100000040e000d800c220b030042c01180c580010075841000d540c03d8a0060601400c001e400c55045440ba200300e9106402014031041001000c2400c50384030750400c0b00220350001c000d124a111a2800b298012503520500819a041c10400949100c4a000380d07020b44401611142c92540c0f80300400c092184040d004681002da817076440c0340d0800090206502804003410003142d10407600c6c18018102201d031a48404201d000c1e0002c9880080b51a10040f0071402440c240c540b06000b40c050074118810096507803005407001e800018003c80c80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 817309937 1250 817308687 817308727
    0x607050901080f060901150c020603010e0a061d240d0516091112070e090f0403020c010807080f09101e1b02030a1b0b0a0b0906010e181308 61
    0xba620400aa1600c0c81c01c0042540161001036003c450b00005000b2001c0c801c0c2c010341a400c1615080480c8034040e008030740d4a520a030803403a03415150030f080105025040c0100c030000d0044c650500703580c1400e00c40401d500074024201000d020391026801d500c00e203a803056100340714001404500c44c46800d19015643c2c0596454900000f0401c10b0005141603941c41030b26801520120b1a500d030404010400307203035030340007001c0c4804d10840740300c042030741d172982e081c0248182008502d80031542072608000e0310f40460002e42c2410444510708100742c0aa00c42032494010045560304100c0d51540e0750018101101410209c1e6990703d0482c040400c4c07405284010544100e1650402c5019030103181c0350020310002c090b00d13015900400604000c548901c4480141c28a000048603021010359140b1081c2c59003900c02190858944090040524242030a036402031000d0a045500765540c0300481e09507045005081e0f954a45040003408003a0400b03249252a80c0c80407889603560200c12451201c1100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 817311187 1250 817309937 817309939
    0x6030c0d1d0102091801080307061113060207080c0411160204060504151a030912032503060302090f010e0a0c050702180103031205091b0f030703060209150708090d021206070509 78
    0x500041420b48105c002450503038030a0000b541c45d04000340c80c2d0401038a00c040d0942240c04042201c5c408103850910802c015111a50203400b40c0c9241c141c15501d0310030407410103841946010004146118610102c400031821041c000d45401c009000103002040140d2102c1d4025081c800e55195000740340c1056020340d60880d001d82200c1e441e03c1c1150105010864120346258083c2a149119803000ca000d5640a01d0001d00948a000110600c0c50700d40c095006081c00b09803114018800c61910f1a20f895021501b01401e088542c5000fa0044000e880500104240780c0c0c2c843c4842040351081c02182e0b0342c603401400ca5400503040030140b41c94004244401d800007100300c1000012241d40b805518022841c000c0280b201440300b4010103151b04440d60040d50180f840aa801110b4500740114002903004201c01a15a20a041032200400380000d5002c5907000410402c00010194025264051420740e8040d43d01c0f009480400c404503030005081c441c500c0b42c8003c200460341d02c10010312038408 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 817312437 1250 817311187 817311199
    0x30a03200d05091c0b18070f08031c1b050307090306060f0f06080c091905030a05010f0f0204030317060609090f07020d08041a191805010c0e06030c0d1d010209 70
    0x1518841d44c0030449002c8002050b0765015000b040f14003450b5100d8003480c45050054964481c0e03210040c524101c8158800c3c183d6030070203c8c524803849003036100e080b280d40030703c0e00900518280c601207000c1c1c1030401400c14140180840401c64140c41164480065a0300600400c140d54460a05502004070ba01c00d980c94a0a118004102d25216100c200c1c0110881c0b6112810220944104104240741ca080c041a005000b0800500780e80c0812100003010701810000078010034400b001d00603648588442a4102d004010401c0001c4e4841ca842140d600440c070011a26100d070310008002340326142e10607078003600e00000d108003890300100c00303802080c894003110b130000750008050742d42c408101d90203003001c0010700400c840352a00b18891036000b01e01101e08070200301300d81403c0045811406010308140c10311104241040024403903110715401504203003030401d00038000102c152000a101c12400b80c404600c0c2c0d1030700c1940e81c02100d42e00c2203011904182c0690905005d00035044044003a11600b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 817313687 1250 817312437 817312459
    0x606010c060b030a060f051501053717150a0314191208010e010308041412010c02010b0906090906180f0a0807030e100806010c1a0702030306090114030a03200d0509 72
    0x823107500c8150004100c1078440e1410805145440711180602d440d442c0b1140e07000141c01c100c1d0414001a0315040ae030191662a0303000d0302d8495002d10300c00003c4c840004000c0e842250031840c0d0725490306600b2070b94001103080c0e0040342c5034250f9081184240c6d0075008000ca2000e1481000100d01480c0c18250503561202803da1b644d000c0840007e8083c84054180b8004020a00482032054124004028013900c1c012403144141c080da401c6401c1401c3c03110050f55100140e01040c9403041c803458100b00b00310717061540c1d810320103601503d900002d00b015103411282141513100700e1081c45211000d40742034080e02c2e0b1000c40f904003d1402d42c00030381d0444c0025141d540348020b900c1d0200000f040c07400242c1e070b21000c0c0da548030010f44810548140540e064540040c0101d510b50010300d40c2c0e03207d03036030640c040d5860b401d01e03400b8010a8081a004654042c0060f00400001e0303d0008141c400c56401d8501962442d400c0003c00c4622015401365602900510580b14072407500400100b01010042d0740d01d040f01c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 817314937 1250 817313687 817313701
    0x21010b0c0f0303040f06090501230601141c090309080706050a0f03020c06070305060d020d0c030605091b0d0c35031c0222090903020616020606010c060b030a060f05 72
    0x83d20040310010002200805c0e12404074200b82d01c1005139034440c4000103114800003201e561304441115107107000786032042c00c00401e560320040c44250b0007070404006060200c010320003809030040f240341402203591040440281845014984001d0401c0d1081d9905d068440c117004140ea4031004c5414049280580c851b00854480d108035002046044081c200715164144110050300028004691000c00d50303151001682e03421034201c0480b0f11a402d44d264051541c602101600d1008110f20343c103411400c02000c0c8030f8030300300c2445039200d005c50300c004401c0c166240c4494103510940060b4039403103400344901c0c0f003010005211014404510101702028040109180c0c0e41d11a03440b624401601091512141c04841e030080c0c200e082503401080122021411410303114000d9900040001d07840381c4548003815014408180c00401803007114034417000b4218040d42d01e03c0c020348014100000f0038001001d01c0301c44e5101040c103403030040c29521184080d00307040001e00380c02550310450529240120f045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 817316187 1250 817314937 817314943
    0x108010b2703010f061d01050901081216081611060c12090d08070804090e0303070503010303110106080f031b060702121b10061e06021221010b0c0f 65
    0x20044508103480480c0e5020a40d411140722504031498056490710031012000150b0301603000039000744900b0440c988010090f680c10890306030301c00da0240da80540184541c1401154042c000e80010081a907078040380c112515800100500c090400725021030010450703070444040903071060250001224907012402080081d02c07520305c5443c001d5002080f4070510707691800141c241090024140300824407107440380c2c0b82c2c55208010459417020002424845110140320303403000041c40000440c250310b091000545144010b000144c1484121130380c804100e43c09401c6034001e0300301c4c00e06441c25642c14a234240e549401c02850740d0380302001303610211000440005e42c98400c4580d64000e0008040c40c1c0e1101d00c03154020150701024940c40303296001d600c54200280d954412821400146443c0b800d44081245941038103000f041030780705c030f900700845540043d03031080c0412041c00b6180d80c0d8020075800710f203c080000f01c00090522a2000003141c00069010300444001082522221124a181f041c0c0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 817317437 1250 817316187 817316197
    0x110304050904060c080a0c09062d0509130605240c070605180d0c0e06130c02100605060304030c03110118080909060d080403170c0f0a0311070b0304021c150b0108010b 73
    0x14030258000c0040a104005603440c5010001d155054080380c0d10b40c41480001e50ac0620012940008508403c0d04108007074034503000341021f01300516400d20b000607801d802841c010806080411521213154441e010071192225181400c88581d195940c0c1d02800581180c2c8070141c41c480c0c07680c4c5440460a01c13807456070f092175220404c0915542440401c8000b000701400c52a0006610795220501d20541d201b49440407545070018103045a010341d0440903208540c1100b40140c0c814400d02c000650070450505010380d141c14480080c6661044c001d00510044e000f007684403581c5800041404a02c000801944200350b528040030740d41c000c1030013181c1d02c58a1005100d40010003041002c541d046d4204a181070003103020502e001c00e918100351501c420502d11010580054046004154002c070381181011513000141c04403514040e030400a6000003000a405420100940320f0800031f665039024000303900c021a400041040d28481d00100710040c61540070903200800482e0128541040c2c80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 817318687 1250 817317437 817317461
    0x61701150f1a030a0905061810020a1d120a08130f030f06020903010b090115081b07030309020d060203040b040611030103230703020307120b0109060f06110304050904060c080a 77
    0x5005040c185911954541c401007480c101c040e60b4140c100001b503c00d00401d4010046040ca040014540d021140e00b4511b2211220115510410061a510713070421800c010001054500c400400d40c410081112101080c101414a001d00f500390760402282d070300030701a442283c52040c40c00c1c0341c60f000505032400150101420b002c0c8a122460001540d54000308140710001e00007240390f40d4484003045071400280c00500c203400224040c200244e81c042e5045034014026551003240b400c0b400e0780003055100e01440a0100340c0c56281d45004d548a407055031102e103601510455407031429003018642144251400c0304c24504045154000403140c0701030700d050300d800101e14100d10003a0390b9640780d000d03092002000d40d030045220000240c0d809000c1000104070b5104034604080f0304d85490550320b2816080031a41c580340c010144088500c41841c04107403a45810300d454020400e004c010300d1400342d41d0201d0b41c000f0401e0100010048030340c0000801d030025464024650701d170100040c2c1914003c01c160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 817319937 1250 817318687 817318709
    0x5040308030a020405060301030609020f01030c1e170702030a090e0f0a090f020306042009090604080c1509101b0806060307260411030a0309090f061701150f 69
    0x520115034560300554000d01c840d000140f41c1940c40d0049005a0402d034000c1d1440c0360796440c91400d60401c0d440441001c4000d10301000103207490000501100700f0309070b44014609002d142c610015015182d2900c0f00e07034000c2044040e0345054a0300960300d50007030440705c00141c041500000ca008500502c0d502901c60540ca038049541c0d041c02c3e420041c080c0604c2550614050025100541c40034070059018500030f003a41451001d03841020150160501800b5001c4d15003507042002605000c14400e0700039610030f078240d65074000d4111180c6026040415060f03412a51418040060000146101e8003054020b05101408150480300b105105c0e01405001054035800000d08501e000f400556000001303041103040140580d4101801120000e904004415808148003d0020310301c0400d480c424110000d01c0840c4583da00209821420311407040529103a00d114491204143c100501415184207480071450180090a000e05411031f1100c07043d0328011000705020181030240002c0d11051900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 817321187 1250 817319937 817319939
    0x10f1d030406050f070f02100e0405090a080405090405010b10050a0f030203060f010c05030408120705190f0b06041b05070c050a050f0d0224070302070806070c0f0c091d06160504 78
    0x20180c4c564010003086803080801100b06005952380700031030703956680b290381b07115074195400c0a0000301c82d07010b80b01e0703080ca82c40544e041002417658011030782924010b80350451251030314540180541282c2c0310407640305800c07070780c216a0503a0110103070007000e0240d541c4603048400900240d00320320080d02c500742c201d00010301c00242d550003009080882c43c403c070110303450103503030380000350070014100300900d155a000a0041c050001c2004504020407024018280502082c1d541e007024040080f0001e08030380c1e0303001c0003403050307070380c55100c0c503013030810303070101e015000b4040400505d0399000307072000c89171001d6074a00800d4500f8500e0040081c0c5c0e030007810034070000c20a0000c0051404900d14100e07400581d0440081d12000e12410a10000410b59005030700d0b03d2452401908240064100034031542c811400c00c4511a4800302c4108000e420400d8040315408600381b24a10100d1504004080c908001c404c1540600d2403146e10240c8015106940c40390301c0b1304200c41d243e2010b1203602c0c0002082400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 817322437 1250 817321187 817321207
    0x90609010e04031e030c090f05030d140c011b0807022e061a0909010909031e0e04110d0e07080d2d05090103112703030705010f1d03040605 61
    0x341c540c1183c020304020f0b41600510300c01c100d600010316144000a500d6400380e0300c0d000d030440c6516014203813a101505006051901103583c0c0d01014841804104425015101c85004201140c0b0265011002403101c201441d220401c080c1c941258900001d43e40c20001e504a440414070f51000300c00c0c1c900b8101100903c6103000c0390450180807030711920703030341c0c1100052690550f0390207546001c01e040082e0700c07031440030200625604140e0020301d40c0f902f000581c600181d813100550540741c0e41c2042200446072804030440321101c00e8110a07030010300e404442e020030507144014203140d580709002445484c8100d02c0d002d8803a10603100b01c00e110341c05040b4201c5541d002e8209564211f056413401900e00800341030621203000305050a8011400c0015920b006503414000c040151440c84d00c0180381c42d03561140c1c1c0031001010b2150700300f440360f00500425144e40500c2180d4003290408000d11140350544209001480c9148411041c21040d00c4018860f800110680341110500e0711140e0800c01400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 817323687 1250 817322437 817322459
    0xf06010f050d090b0405011d0a022e120b01031806052d010303121107030305040516170601060f0815010c080a051207051e070c050907081509060901 65
    0x51446081c00002c1c00480482c0d40b491245210f5103016240f00d074182c1c04e003420003508580c2014a1404066840205c410030740b07a0004c0d40c03d00c00b960686005c810380e456007a010110500b09282142031a207551000303401d0641c0034035144403140050404011000e4120015000c41e400400e0440000c3c4c0b11118040101d0354903840190300030032110030107480070140c0f8400314070340086451282201d0030040041c02410b601484441c030011245804020161003040c0703402e41d50040302d01c000c04050321540010200002407040d0302c0400c01005841d8141e544a400c08803002c0c01440d501a51482942c00010300d142c030404001c4c01094464403611030545484141c4105443d09a02090602c00401070b224000742c066002400da840d12a030b500360b156080100c0342d200b4071001400300002c0040c2404043c031080c54940300060482484c1e140540d50740c140345804040c03141240d10203640720b50010104140b2036041011540b098284040c60900c0004450070408503510581e41941c00c441103400502c8008105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 817324937 1250 817323687 817323707
    0x5010309050f0102161b05090a0c020115060207030204051308040513110a090806070e210120040e01121a060d02030601080c0a0e1603110409020a20060f0601 69
    0x180207440d01019440b500e2400d99008020b0b0b07942d510b460000c2d0006102015641c0408903501094241141d4a0840001d8100300041c05c04080603680707861701e424182c002d60003150104030008410300c0c100c3d6901806500c40c0090710059000c0c0341000005100207000e4009840240c2e401341d19181024200000c0c44000b100e070f007a808803000d80d41c0810360800c1c40001c1c045d0506041036074842d248070781880341407410328074042d02d25000c1c003110907088415660f03490780818001c3c00ca0b08100500035032541e2800d0241c03040301250410b000212010010b4200034000500039680f25244860300750740c3c1e031260710651b440302e040d003e0842d030042c002d0100d0100b142c0c2941a04010000c1410f4201541a00007a04104c03080e03120040c1c030740c002080c1c0e050340d0034110110401440705008039500c910701a0200e206102a0003041d404140d81e541100000c80300c3c102c2a24050000400119110303019560040e0080e400d42080e11800762110100425084000038440c0c03003141c1c0518040744075200d4000565140d186 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 817326187 1250 817324937 817324943
    0x901060b042102150d02090406060206070c021003060b0d021908070203090112020d050f06030106062606011b1208462310030b0118060b0a0c02040b0306090705010309 73
    0x10503130100e8500d515009001007020405005a82d0100310b820802200d9041c1c0c002001d42d000401000103070b0f604590003040c10340e016680744100780801d4108500400807504420625040403801d52110001c5030301a00780001c0b5412003110303900184200b501c00c400100c84400040e882084090125445a0318035100003078220009410704680034504403e0713890031190b174040850401d081050502d02406440010030050801304070000c0c5140d4a0b6800140f1554607442e00b283c05004030309141d200d1071040120070303400c01c091040c000e0140352031000341d0400020305c4002005800884c296020b80507140c16800700e1a19696021080d07005020f144200c201441d41c800c0345d44821041509006001d5000342040311060903511148004000146207400b625070305030080f100000340002400f2041060655420040c103103a41c2c010310300700c2000380c01c054103e412000c40104045855640100c95855118802c940601500389008181a52180111190407441c0d005800400c242d5010b81e1101480e540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 817327437 1250 817326187 817326199
    0x604090c0e04060305100f02040f030f05070302041803020c0a05090f0a090606060e2b021c06020a0807120905070506070503071a010f0906080628060303080901060b042102 75
    0xa04440000d04540c0244d0040d9515000403480700c5d02e0300003c1c8283d800b0014031940450a160629a40640143c00c50100070400c42c55005845c080c44810000340005540c010800d00001400401d105082080c0c03120840251150070701510351407401e0074a09080d00c00182c80780c0c40b1a6690281c060211102403c100241c980d200c84d0800820701034044c0c0400f5060355251950110a100107110011107180468816603615160b40200c00032404854040d44d50122181c4041c00103102c041207051b50190f40040443c0c1c40010003001142d00804c005d481a172041d155207440d080100c0d0440144c070035800e0000c00c90b070028942480140b070000301a044280c000c00443e41800400d9a80c0b0007141c440b482240b52224184004009000220540402400ca00c0c1414481c062605441554640002d0640300703010311012480182604035203001080d0034070144007800a2541d0f810083c20007041642c40e12165420558045160640d1300111400c40303441440350034669481564684000203480400c03680701c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 817328687 1250 817327437 817327457
    0x1403030106050a2d02030a0e0103050124120e010605040509190303110927011d13030e030a060501170304030201091502011d2b120e030f0f18030c0604090c 68
    0x1c64480d21118003000e04d80c0046940d480030070b102821600344491032604140c20300c1d0060100301c4d6810b055055a01d000c42d003240c0480c4405d5030658400340b0702c0ea060b00c005894201c002a0b41c4205400180807100300390780070050780d01d0f55032041f40ca0b01c140b140c0505120f80c2c58410600000c0c4240d01031302452800340d04c00f90a080703400d00000c007525903240f20322400382050680f141104290017005401800041c20201b0b1001c001c401c81c1e5600840100103044200000441c40b00341801083c1c100c01000e0010700761446030fa92450b14400503c0203000701c6120030940e46041e180e800000046030b090702d405031101c84410740f5044441e40c0c000340b0002407101319520703026415428138081030345151b507040da03101800743c04581010b40041c8003060f0711528441c0d20451030611149821041c0081c031200c46090208d4004030103180c06285108482100c036000c94005a0442880030304005403800200c0e41c01d4613401a80f42104040d502c0700442c2a550b0311002c01c01c010810341c2e06a81c080803060b403003030610f840e0350 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 817329937 1250 817328687 817328747
    0x801020a02061b030420030a020604031a0a0b060414040b03011b0e06030705030606030703060b0a2c0f0d110a12020924010e0607120c1403030106050a 66
    0x298000481903000350340180203120306803420b44121203c01c40307681d00030b509602d40398403950301c1390f406030142c0da40614441a900d400c0351414425000b01a401400107a540e65680c64455001000410004410003003a4081030ba010424010b0000020f03004140a080c1810b14400e2141086021181d5a119607101207405454400b8010510760030f000e0070410042e60760032031003e46881c7c0e0320525244240d404000f00462150071100345d81d0000d00640b12143c403540c03410301c1038000340582d8002500500000c561402c5241c0e00512560080c01401076101000d003000d0140c4080000c00807a1760f0b0300c060302c2c0902d2602c3d41829050309506a0080e0401c0c01520700900118210400d00d410000e26001c0310f48404080d820203503034050300030341c01c1c250041d6501021035000c10300044110049042203c0c1e05180fa141d9036940051b10380b0382e038100c0a030518510003030070702811080000c04201c0e01690700ea84400703550707080407050701c1c1262026203900340350500c00f00c000c5820422004002003007482c02c10700d122032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 817331187 1250 817329937 817329941
    0x20d09060f1b050a1e0c0909020d0f110319051c0507060905030307081509070e0a0906170f1903030213030b07080f2404020a0302041a1905210601090801 67
    0x2c15000d1006001c3c0041d560500b0000d4005002094a4000800f462180025648001c1100300c4440450016529500d0302c002049005034801c0502202010f004410074032410a01e800e849840031006c541520014442d41d049080018a01500a800102a0004c0e054080c66980d442448901e0a90b00c0d000b219680c40007101d034003a50641c1d8036032010080080c16600601140e0f00300490900342c0240601c1c0c080010a1008000c16038420854003207011000c1d601d4009420740541048001480125207440c91041d0a8059a24850a5115042080070521000309250a072403034501c0b03c0100344512030314260040e5010f01c48440f80c81c0900350001010441c860f10b50b60040340c0907aa2030340581844180c00d403400320044d00104485403038041c4c400c10401c8502036050130540030344002d603ea04e84d18501750004d001d603506c907580c4d840c0090320755040c800a550060244a540c6540308002d07002009044902d0f004440388000340d59440600f80c4806850162210780c002070500d0580f18554a902405003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 817332437 1250 817331187 817331237
    0xb1209280c031416050d4b060c080408180102120a02240c040e0705040b07051e070807350607020d0806010503010501031503020a0b13050f15182d01020d09060f 70
    0x602c3c440941e030350003005114020500002274901c1c000c03003181004d0725000c205114000800101c642c2440450035664000d22074500c07000412030449844402692019488195000301c440218820b00b1400e000d05d0b211070040c0f4001c00c03104800c00c0c18141046d42a001126010384081309108061000056103003519005041d0325224101802d140c1b007000b10240d01001d090000d0040380d801102c014007206000182030300c21a520110314410b0f0a0351500041c3c440b40343c842d00090328000c0740b43c2850180b9800201240584215400c40e03990014400b81203075102c0082e0b40315400264200300400407584280c109104466580622070341c083e0340c07079000030600f44c40d40d4840d4080080118510b0050004009a0401884c041e91264076504003072002810300d442c006042d0441c01e5000c03c4d0708641d40d16a150690b904440500324444241c50903282c412200314080303529800f00b45407401030b055944042015803c1440640b980ca508904210341940c203854442102800c00081c148490340c48104080200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 817333687 1250 817332437 817332563
    0xb13061b0c0326030a0f1b05030c07080c060403031d0a0209040803041a070f090f080a020402030c1209011a042f09030303010b1209280c031416050d 65
    0x1c407411b481c00040140c0700003d020000c140c403100d1100c41c0054020048991005443c40c0642e0344920350f260903080b5001d6600d00302e5081c8540c01c05c01c800c040c2c050340140e040181c0e4909555144202d680d51950ba24a1104000c2d0003d280b903011400180f030709000f540d001880394042c140034003180e034403c142c480703000c9031039000145040f604225100e812400c054003416040114070383c004c1c1420502130b640c000541d0005c1c000c5600000090703201415106032400120000d40306100c034140035000d24040d21101c000c1ca0245d4041c010062200e103458400c44244135001410290f079810b480b24400c62120344e040183d40190820448100b080d501400214060109204210780b40c0c2c8080c08221a1040d00428400d09070703006041c2e0303102c0c501350103d034945a12410401d13200301c1c007410701d000700d81c02c8510b5000401c803240200000400c2080410070841c1503144450341c400c459501c608010010088050107813111b0b010045104003001c2200e1a0720725410303604c01d400040c07001c100040e0307140507001e8a09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 817334937 1250 817333687 817333691
    0x1503160c03030f022701020708150411150a120515010c0228170f0a0f051603030e040e0714060d1103040f0308010b09060d0c03060b13061b0c0326030a 66
    0x50a4442c1c2c0400e000e04072860301f84018803042e0704100a0507502c480700160280d2202003440000c0401084040356504844041c00d41d0010400c41e064120164004801042c00b19003006408202c1c1c8070390380700c4d0511480c070078181c4050090450005540c86801000c060360401441c2e10041e50240c28103078039440500d01c4480f036051092801025100645402400c032007990851803403481c0d00342000a4039450182c00040c481507522951600f246842c0c00803520300790a604500c000403d041d0020a401d41200080c1d80500100d6030700c0c601141c80b01400d002d11403001d051100000e000b0300307150010f0240400c12080c005501182490950306c03981084074212003100c40b4007250070405501c803a07081d00400907155000c0c2400d4100c1e0000ba124041d074104540c0c803907074031203100b010706200c0d402410080c20000c0115580b4081046d050000e102c071405403001040002000c0e407403c448000d1000002508001c6c0d100446095a40d0104041d041c1c2c01e071042081001c00c00c580141c0d10342e10007103000d10118500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 817336187 1250 817334937 817334977
    0x40e0304060e03030406020a0312090506012706050109060e030a05010513021309050712051e1606053c0a0806010f1e050a03060305011a1503160c03030f02 68
    0x1c0031034002c2a00380b4000e41042c041001440c0d000518049420b51508020741c05440c42c8407180014840c01d04040c240e44240000003c2d130000c0d211040e4401d00b41d0b40d4000c0c0b0301c11165882d81d0151f0b100703841081e0004040150810142e44298004550701200505944000090b070321010b01b9623a05440f0403454030815403040c811440c0c000089114400117100520010340e45446443d22043d203031207000070b00c014101111003001018007030142001440749107840441041101655140280e000c04c4001904801c1c000c90814054000e6440a00f000c80f120070591846418090b150020b12610744032000d500301000500706000405001101201c1d85c0d070a0140c80c0140c00100308810084460301480003840c07840341d19145c0f541c991800c01102c1d05180e65280600c0e8400c9004100c02e03032000d0415413820303410700000c83c0e009210000010040396202c40c1d1900142ca080340341d100a40c0c5000e0054550420803004a018862241c5214000c0c01c00084156002c0c0114044c0c1e40302c140b07a27100400c180c100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 817337437 1250 817336187 817336199
    0x1a120102300129030a020405034303020d02120615041805060f070e0303120f0606040602190f150f061a0904150302120f0d0314070f0e040e0304 63
    0x440b40144040002d1403d0b41c07202152042c9444112400720006410000000303001086a404840c020072000c0e007201c0c044201030405003041610024104004086004801528003520743c170103940a251800242105d03145600300052400c2145040340c0241c02200707410111f0390180542482440c284064607500307034151042200b124a03805007144640d6001710b1040c0400d100140c8641e005244002d2144540c6884d881034a8017140761006661501c0000b40e000600c4900c0308050780901c44c001090340c1a600d8000401a0600560260100581c0185d250940440b0050000c024003401941c0c269216450303600c80c034401c00c4c90a84020302c043c0d1544804040185a4070900006104c0c1d0740410381044401d4019981034803071801c105119640f0b4a00c188071002e1895561f0006590060180000c42c0030400265101d100e500241151030181e040c0b00b081d200e01a000e00001c80c0761005c049402d903514030405891040d001d0310003c0810042e00c6141180351124444ca41c0194050001151a146001d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 817338687 1250 817337437 817337527
    0x1b06060915060e06041503020714100212010f0614250c0509090d050d0b030c1905090702210a0c020301090c082b03020c19120906031a120102 62
    0x1040e114080d901c05c0004020b120681100d09807440d081d4940582c0d01d110301d04001e803254003480d02e81c1d16280500510321015010644c020441c00c100c0441141d405da90721260001102240e22503180480c001ca03402e9529501e1060080504081e204181124560b82c807000650100e100310701115400c1c1c0d801c0c814403051801c00c4803142e1003d103a0009000c070450382d100003026402040202c51195071212407500e01550240212200807074054802c01c3e0316441d15420540ea81c089100f49030140c042400400d00d224402321b0310000d80f01113074440601481c01a000800c07a41d210b58419402c11002e02f120000683d000c0c000e0a503514091041d400540e42002491401c0140d0750201d0310400821406038044040240c0d0303200d00301a200d040060308d0b02d8010300c429050101c0006000c603000760f40302c541000c00000d80c8840c1c1c481303001e543c5c444c0350954440b8419011140103440c8415051140526030741907103010f03624401c40700124800541007600400c00c2141c00d0580d03541c0284c811b4100b21018884101034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 817339937 1250 817338687 817338707
    0x70305031b010b0d11030c060d0902100c03050702010c1a09060106080606070201021e03120c0c070605092d060705031216120f02040b07050a060b060a1b0606091506 72
    0x9240200214146500041c907444c2d50740800500b86001100340d240b42c0e83d818071028400034009011256074191180c103c100070107400b101248520ba141c035a8a8600d84240744c1400711a40c161030b1180340000e550015200b14465400403150b03020052030080304029082e0401d409200300500904c0254100400a010248002c3c0100e00428041c05040d0260b0b07400580ca40c0c803c2902c028011020b103229500b14110b01c03800b09445485c5843c8800d000c105601407000300442080720b0309660190742c80d504111403500c81d082e10365038080f02c10b22052003148cd0074020304152030140c075502c040a0030301e00301240b000d811480d02500c0a4201091806101c1441c140070795111072501200d421201d804030f0050401d05020b40723404c00c00c90b40c0e07080c1c1c07401200140c5e04482c0588549140d890300c0d1001c0b40b0b01709640381344402d0101c40040c1000c1d408410303810301c5001e030b4890101d00e032514130351810f40b010741990341c00500b0780179995542c941d540054094a00d101c0d40c84045007030100794190a04120028010843e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 817341187 1250 817339937 817339987
    0x3140c22050c0f04031b0e040309151e03020d05130b010608090109020d060606020d08060a05060a021c110706081b0a0509220b241b07030503 62
    0x30010403003610240d184120300e450000002a02c1c0c840c441600440d01401c0840d6070820310010f00882400740107950307249001c488200100d0007a8551000004405040d140140410744101041c04603016003180d01004001918100c541003400100302c0c0c02401c0301006110100b03600144210980d0303c240922a17110740e1402100c010060161703680c6103034420510428003000621008030307803002429080350003840d80060080c03c200e1400d00740000100720600c5000054400c06a82c0030516000e441b10b140705a80060000c5005850403051140c15440b1802c000d046004102c030340405413007020000b50941c0304964481c8420804d40c541c2e189407080c07036000f01080c0700d0b4882c10441400313000b415003a1100a903900158070b44401e00c2007560203000d80e103003150340800c4801c4030140c0035002c045a084030f44940c210501078840e440040c888e0346490b4521184072405145041c8001c803150304000c114014169004840e406159001c0b94180b0742590801c503a960000501c07003060507000c125017001c0c402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 817342437 1250 817341187 817341199
    0x605090105271008060310020903070f0603020d140411040b150f03040308060108220201050714060703060b120a0908040b040f090507032c101406040f020f1605010b0a03140c 76
    0x4018000941d01c40b10346147c9002c2540029060784130b81c405001030001400450350040c0801d03205d000250194105000740c1d2100d5261080400310030030728040c4a8041c0e80c2000d070680b8420386100500c400340051054040e049034000c020780c68011f86000051022401c042c0b5299102e00341403074001c05400c4050042d6040041c2c0509000414008282c80904e00803100d0720184499004d01c01030340c0c0d42c0a08800508580000f2400034480b0001003143d80c07080c0c280b682d00b04134150b203074200300300d140c01a416490041c50000f80000c07041d0890b680090104c40c0603900c1d15040903554a070141e903650060304808400e00b204642004101c040e03003d03035500010303281001e1003007000c5405000382c905031764840c2c3d1000d404008011303140032801b407010b02c420004009051000d00e594521281c4d1120064404a00643c40c02c14800700100082c402da0f05400c0302030303422502d003400440310000c86440c120f0040d80c05560f40c0caa150003555416121400440c41450001c1340001401541410a4098650140990 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 817343687 1250 817342437 817342441
    0x1424070f0215130b0706061511010b33040801090539040f140a14060d0b01051908150a0b090c0d091104060602070806010f050102070605090105271008 66
    0x2c0030150f0702015241c04105664803981ca5051040141900341c2c41030340b01c61200f032800c0395140c6d44821b64010580b5044024080741c5a0002400300c20070200c10641e52041c04071000707401020080741c82682c4540b03500c02150515481d100d000b0308485500c082251240d101048002d110000c4e080c80b0006212a11703181c110700301d0b105207001184038502021038030907030355003002e9078003520161f021000015080d005c42d03040b80b60114074030303004028400c407201e0301d03a01160004081e45002400d900304a40e200b4614220f036482c0c030040c40340c1220416040424413400c54804030b282d000801c203408824810840c2c4102070b0408024030b0b0200c9920441080c010003070034040240c05800c81c412201c000c00c0d01c550004201500341009c044801308270500303070350141c18084000b540355400a4014240c0702c0c170303506440035641c6e10310500e095818148241809a040800c0401a00e402280034042050060400c0343c0f0304203c200c1030328a259441d5841d41212403207103003000c40d0340c00c096090b440d04150606186241d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 817344937 1250 817343687 817343707
    0x90a030504051c0b160905120a02040c090810020a092102061605060c03062b0803040305120708070f0203070c05061b0303070c05010b0a1424070f0215 66
    0x25104034020140940003010000c180300304a803403d5001d035600415120300c10305107080c05500080e94004054001510310502048034640440c0d020f4581e07508100500e2030306010fa082c000582140711120003804034480000079150814005207450b84c0d9002d03001a550610041e019010201c81d8100e110b00ca400001c04000001e80c0101080085404503003e90711411080e1026401c0c0d034400d0030040140c0161400e10480810301c0780614020030040755200101880c109840b000800200301041052580300980404202084019a04175000e45000361801c51540c104124410701135a010000841c1c1070104181c0faa8000381c002c4c10035620b48003452504160b511815041441d0740156481590006003424800c558088030046403005a802c0e25164a000342019018401c0d60005988035401c2c0030011000d031a24181c0001500c02d1308880d40c044008440034004c50030503000b40da4225048820ba01c0340303c5110603002e0034802d445003000e04000506071040c42541684841d80b400214000d2204a0074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 817346187 1250 817344937 817344947
    0xb0c0309060a0b0f0a08010e011404020901060c1106070b0412020607051b0304080106032a0f1202040906060b0703030e06010b0712090504020706020712090803030a0b030f060106020d08090a03 84
    0x21418000441c0c0f04140c18000b5019500e0402825800240404001901394043d00441c1c6421080c10080200316081100d107178250204440c005c0d48886120014480e0710f000c0d03205540c80343c0c010121140b00b11880404560603034404202514001e101c40200405c100d08032a21011110f10780c4007400d840c0c10004e0019005002d400c4552442c2c0f240700c46190b00343c185c1001603400401d030743c0c1700030320803030303540b03091481070458481070503003c0a5500c00c5584581c40e0445241e000c81c0c05420745407034800d01d0220a01743c522000d12080340e105071503491040104541c0d00840000d006168110340e9a0652460080c003200c07940303110100d840c2c000b1401084520030300740c15940e11a401601c0641000b078585811110f02c19581c00043d0311901c045520340a0000315806843d03010322807224030741c40220084007a41c02c07441510501c0f0075079000300009601c02d070254000200b07640028044690083d16a5500750074000c0980022005a20002540705a40d0f4801e03c5250402c0040e000fa1050550503140209 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 817347437 1250 817346187 817346191
    0x9010b063f060d17041403160f0603050a0b030105090c030d1706010c020111010501081609020c120d090203120d0b0a060e0d210e09010923060a080d03090b0c030906 72
    0x840341840807520410321441c3d007500d42c4100c01409138945d603151159103002c40d03048092501030183c400c0b60002c58080002400d182e098909a40d00fa14849140c80b000f03e019000c0100030301061f6481b06a010102e481c240201d40c02040080c010b00796480c2a00c0c24103142c074040045002c01c006181640544d0201a604407540240c0700786080d00301c030195800103075440700603080844000d40c82e000000485440104800f0382002e03442043d640c580b50b80d040d100c001e0340603007035080c0010b07080781a4003041e1242440c001d19640003500750101e88d10046400203410025030480311001c3c2c030b6000914114506580c400c00b88500c82c1101d0881c030030f50030f000d4000c107840410b60400d405803011244810034054000b03512180400c1c0d2aa000f07030801c90300427005200300d9050351510301a101140002c44e64244502a0b060494555101c900c0303402d00b081e01219500700050000d03500711070703214408100710801380b20045150306603440200e44c400031440c0000c070440c00281100c5c0e0251081c02030104131a00451095 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 817348687 1250 817347437 817347439
    0x6150f030b250206190501081e10060909110406230a1502030913050c07080702040b03150919020d032f010c110d090e09010b063f06 58
    0x200d4603a0312025410520300034900001c2c1031000340003184000660005000d889190900c2080c13003418143d02d00c039000e5980a0060440303d801503449690021029515604144a00720031618542c942c02c40c81011580141c01040202c0e45802848092003034000c060084401d050300c041020780e2034003104003081c0c00d00e64444e00300c00c00c0c015200b414170364607c11504003800d440e104095040895140c060f649502044817103002c2c9803040103002040e00c072842007520a5008204c423501c0d120150b41c594006034021b450490340280ea4050000164404004032920b99803087c03164546810800b146a242001c0548240712054441d003050300103071189039140341103a80c0360a00481541c50500c40e030a040a01150301d8181540c180c3c404d1035003040541195901110035140d242d402e440442409454881280e041c1c4041100c2090822103110b150001641c445901d000005141c075203100020b007140d02000f4486405242c02031280000e401000c0b25a12584150201c030080e9100b000c190010404014442c0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 817349937 1250 817348687 817348703
    0x10c02010309020f10032c07030312060503100903031a0a29040806060a0902090f0d081920280302150907030b0705031302040509120c161a19030e160306150f03 70
    0x411043c4403600880c00de42001402c1d202030b45149002d405c003c0c000002c054001904144141030180103040b0074140680029040000c9641001c03156510b18000c03910200800c031441c0c12981c00540c51401400260810401500c01030030301d442000b45403104e58000300401d81c81040b0303148195980002681d6003800c1a20728818005480c105403400d40100524038850100d000840c2500c0c0754004136485180e808001400c4d1400b102d1406a0340d034010610146003001c922150580098220781c44405081b4032074411610242c130140c61240c0c42c40011745620350b0580c441c0500744100704400800c0342d0b1122580c68507504500c1d1a4140c07442a07800c00788041c3c06035036240049111160140f041c8403900400c10f4030a40d841c1c80304000ca9039240001c100780c0800c06040361000c80c20400c0d00811030300c1460324114850500e01620060030500707480c90780d08018075a548440c00032014052120f10041203000804d0340b1440e1841c10160165040e40c2c180d94503010044c141030003003031062108070f42583d0b089244 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 817351187 1250 817349937 817349957
    0x31e1b0111030705010506041a0616060e0f030703090e0603030328090b01050906030d021e24040c0b0405030a26040f180b010c02010309020f10032c070303 68
    0x41c0c0341880342805080711400001203040901905411680c003440069400f0401d10420200b0130014000c40c102c0d85034400410444d054919040010554030240500d00000d26090070303c9080d840c0500041c08814203130800b046000905400c02414802001c40f2400c109061800d40300194403880000d048010081d0010301c100c030010980381d5045081889401d04100c1152107050820380400e092140c684151090f40005015080104509904078030070340080c2007403040d02c0691010301c0c940180c1e00140f803040100036204118403c0401902c4005105001c0c1c05080a040519041071160807050f2004004c000800060f100011912071250f00840c18500c1d071511000740c260300070307070891010740800c030702180110f5a9440b644008046860341403d800903155034950100c1920040c0070200c1c007241c10392001c540554001d80100d102c1900c02403414511001260010b41072044003c1c441c4c0c00240d581010301c0461404079407d50003150f818120100d01c2d0040310500d9650760960200800300003460503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 817352437 1250 817351187 817351189
    0x80c1e07060f0f06080c03071d09030904050f0a0b03010504080406050c01060b2208070303120b0102010f0e0c0f0a0b1e040315020d060b030412030e030f030411031e1b 73
    0x4010790354242d1082c0c081c01208221881c40b8013030002c50081c0d4200d80198a032244081c90002150070446420100c10030343c12240c0da61a00d022080204081e842d408204141111680c652113042d104a000d410581105c0c20300103100c0040728010f002c69806603161005220200320700c001170b070f07003180c00d245416aa6a582c80506a002d0892540820200e10740454000c0d2200450b803c40388404a840429140d002d540d910303a659142c2c00d40c4006400f044524034001d05e0003e17650044074002404cc0004142d0314199502c000880da10140001c2e02504660188011450041100120b000c41290f00c684180d0610054a400b8400d4010010b441030400c2940c0f06140780e1041a9402035030014084101200c3c804e103400082c0d848000341c2502c0c649481d00205500311101c062328002c1740c000c2014060b10382d90110130740060200f40341c00200c1e407109100707003091415008010b40c82244075000400710883c040061502d414440c042d0b0800c0c0703190b01a084103e100c000190202c050350007005040300500c40350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 817353687 1250 817352437 817352441
    0x212010b2b090605091906110c120304030f021b1c02090703090506280b01030608070f080c060304050a0f06021e0d0c03020702011b0312020304061d0c01020a030507060228080c1e0706 80
    0xe512409240200008080e8ae00c1d814800f440c8118043e44408202034240c500407600d80520404842e81d1249000c8103410300e0900420740502445000b0741e140f02e500e4039400280c440764048440100090700c50041804101d0140080c0ba0049006002070b03c0080c00951104202d144000e0000103003955070380041881e078803a400450085c80320000b1303504050340b80c40210a0b01d1060340529040c9100f84405c0c0c8a1904040044920982d00040540031500c869500e2000c000440181950b205ea000d115201030f510990711041c4090303160b501080e40c0c03858550042010b035050540070201340742c410b01003840983d03000714007c4030448603104404c6a100e064901610b030000e0014004951500c00f100f00000c001c483e51010955280c414051640310040c0904903940e14070402c0b0031401a04000761201c0080d0068010303100c058031501c005070a00485c04803034661001b40c000040900a042000f6404081d0011441600500300d150401d240c0811199a000309004814050000c0100060000d0034040d00d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 817354937 1250 817353687 817353697
    0xd0c0306060806090f06040b19061a0a02100b010e06030c0403060906020315030c01122007050601030201080c0f030411030102160b06130212010b2b09060509190611 72
    0x4040103201d440d5002e455880400700c580c01c0507480380301d85010980a0000d5418420369014140401e140d5a070003002814050010444e550542c42d4000450880111440c1602107003450312901c6c3c9900103023400030310f0300b00104403c0c846189003c030043d00f5642d00440d1071a8100c000d0312101c1e41e03511015020b0320300f4825548043c1669151000140400800d074000318041c1415400705440010248101500d078507003000d801c1d01107020f04441e843c180307a094001ca200003260303000d494007484030002c6024460303001101c21919a00b01c58014800c41d0703044803109400501902032503042c6100b40050200700d10000d000906280c804881060a40d0307400d40480d42c908040c05041c003c0b8004524008850000951748640320309014150008003c000d40f0a842c00d1042c3c287d56010181d1070300883d802150701142e0035030320110310080c81d4400c1141107a060710000cac04145000032200d4682c213007541113a1010700403890641005076015004a64030011100d40382c0c208600040340007690b50030880b1481a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 817356187 1250 817354937 817354943
    0x23f0c03070f080304020a0503060708040b1b0c0303011703030403050d0b1c0c0509090109030e0f0303120403050a020625030b0109090e0a1b0e180106091103060a050105040f050d0c03 80
    0x182482a0b4200b240c0c0401540c020392003545c1190340d05449400f050f8507100c04031200c100080c0182c00040208100708000e40e0400841700c440d0400c64442c1092402036408030789001c5095000000400907040e107040910000340074680a1800c41c100b80d54010242d2040c140180e00207034885800200540d1090348042106a0b10a4a04001001441c011601550314031441e48584407010019009030010300800d079070f1951568a1094211a02e0100301d48200c07001a51a0540710501601026800100006019a0007034032899200e091a00d002442d06100401e1900030102004001c4000403400c00300d002d080800d42004140400c114004030703040b55060f400380140b07508110801d080381002280300d141303040c010464602138912b00060045038400c03d03c074007000d182c0041700040c1c09811095500010902c1d000c00861455514030010083e109a0b511010710810700000f07001161a201e02040300070300007802e1603410280b0345008040111614819940101349940e600000c000340402e00c0409503034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 817357437 1250 817356187 817356203
    0x1104091e30020d090605070615050621070c150b0f03071503061a03040b04081204030914040e030d0f020c1002070b0a1104050f0102010f0c023f0c0307 66
    0x501d03810354900545509004054020441880460741c4645594000d89556846642c03801c1c0844e601c4800401c51148c0009103a240440c02007071030340d500002803008100001054650183c205030034240c450024101c03609100400c2c0502c000180b8480c40707421030044880000814034280000b2a50b02e102d000c100071b40c940540f0a0110301c0030804084075802c0003181d6010403001ea25188140703000101407802c09080c510503c00900040c22803007001d0f60040c4252452410103542c0081e1001004d001c1e9001c03008180406024001c02d21a07900c0201d9824080b101031086100600c4c2d081d46038800c2460303030b2040689500c11014049129011236048507040310807103403c3d91201d4050300003034001c0b4a007115a803140d40045106018140200c6213921203051410340791074504001c10140c8080b00503503d042d55204d0f51080000206803080790301e42802c0d0f4024001c001e082d10084049049010488115401480c03859600030094180020800c070000c00c4183d59512234001461030740c080c203240104944 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 817358687 1250 817357437 817357493
    0xc0f0f0c09020d0b0906030a0b040f0f150e0c1f020c030a050114180712020f0409030903140d0905060d09080a0c02031605090622090f1104091e 63
    0x1581c1507000300103401c0b42c4001081900405802c2006071082030b100280d055010050000125443c40340d07182d00184505001c00c0031015981e144034018600040503600484c03101d000c40c248038281d00a00d00c06040c404090400d80c61b081c2c0011781c00005080d18108007841a4007031583d002d00801c24800d0584000f811104105070740e29003207001e07041c2d400e1501d1002e0303410404200d0504140500800042d4060040c25001e41016821080b070116840186c2e403150340d107405441c103030300c451040d00b66840c026901c0b20803050450904068981641000c0505584075201070b400300c59000d22201e00b969411180b00355181c0c41d4600c09005000c88400140c1000d2001400140454010340031051480c07082e810358080c081c24420b0310301e900c01d40d07214440e04800c411000908601d410a401c2c00520640420b0941c00302070f0356018411030f0202c50b0200d41c0c030071103100000c05101c182e030300528061000319014460407080d03030380d0740414544605841e0040c2ea60315007000100400c40035000758940f8202c0c007902c82c0f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 817359937 1250 817358687 817358699
    0x317151201050a2a0f020c040903030509120405150c2d0d090e0a0b01112d010203070203121302090f010509180d05090d081303050708010603030c0f0f0c 67
    0x8042c280c542850742c030310380052000420110904c040d041c164120704500e8460303006906507110080345034000c2c11070203503c01c0440d0503612445000c41d000c0c00b966000400e8a407404010b840c01c401440a903101c0c0009000412050352003d10021900c2002c070440c0d80c0302c0c16400441071800c252400d003444d900400ca6407101d50308200030348104464800c0002c45032040b11241c8261900300709030103285c03d0903104000003000c4140c1c64025002e14003042c0342401115222442c047d0030000d141d0b02107a212030350381c0d1500c00c3c5a9101c60710b10380d200c01e00c03030002c62450401c00701c00f82d620300c60604040e114940380c40002c1c115000400f00517208580141c81440203103820300c0325040d00b200c00d0040e184903150400129000d80010241e9860102c4004001c3c20355200300c0400380d405400036450560b100129a104100080c800406814826040c00541929505500c0c25074140070580c0c02a84550389007500070000300f944041e4070450941c100c80300b590f0300c1403142440b003882c2610480203890004490030010386 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 817361187 1250 817359937 817359941
    0x3090f0308072a090902060705100f06060201020c070e070c0b04050a021e090c0d0204170a1439120d020c0f010e040e03041a040e070c0317151201 64
    0x42032040b80321103c0c00000c0d440100003600380d084041102882d503403013800344612541c861041c95000a103010f0400d03240d580c0d45c51404aa4070300751a0300e961612200e03640380455002c0d0b0380180c00303180025410700d0014144199144064820f01c81000d4204010440550140c91444c8500350801288281c0d840e007401c049a940f49200022030051880c1018005504059803010182c401c00803c400407640710308210008a0304100c1007066a030b41d0801c40001c1400900050310714440c0c00b10084e0522031103c3c04c001405010881c070b0b0000c030745c2083c0080043c0000051582c80d00c440d8084a680491054245010741541c04005060b009812410034140a200018540c0a8411b9981c02c944112201c03030244014101c070b2001840c04582101c0580c0c04500c0c00d81c00080c01641b103001101d0a06503100440b0f0301554884007100030a0000083c20f01c005003051071b24550002d01400d001d0383d80452964003d101da0300000303400c0007408140b0302098080c940c00c0221100700700c000300b0245c25081207000e100c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 817362437 1250 817361187 817361197
    0x180307030c05060a060803070b06060d060306090c05040509030f070320030318010c02150604090f0803100b09060315010c06020d0b0f03150c07030c0f0308040506131e03090f0308 78
    0xd683d214040005580345064091302040e00d030317140c0c0658106205543c880b041154050b1400350b00031800d000340a02e1203698400c540086018a0000c1540c9200c8e06100b10ba10215401039405076050104100c09900004101c039805206850015510803d03410200e0312010320702d0800c0900211901c440e010590000b0180d805074044255005000c07a03a00f076224202e66021403c00c0250f0009203407000148101c074400c0d91301400161001c55200700c0c136a50b4072800d050120045600700d0002c020301c500451340c00030700000f500840f22518034007100d040014209000c01050081c40c2c44003075015007000d92042840d28182c65005006549819412991801409140305014000c08104407408980c2c600003174041c10034a0020504121500c400555002c1c907404604254140001d0314040400180d020747e520700c40710300942d111001400c052410509103c009084a640400c4003041d401c086180c0309043c8000460071020ba028010240c07a09859a542c1a03028504550000c600001407000d4080140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 817363687 1250 817362437 817362443
    0x90a030b0919171803010204120b0c09010e060703020102120f06040f0b0604030b040203071502010c03050601171f0f0f061713060519021c05070224180307030c 70
    0x203101e00c401100d400740410802e51002d0200c0b2491005540b411900c40001c00084800c2c40807200b071001224086400c3e0307480f41c0d1115024030f19080600c0144011a10482e40010f00417107031900e841c041d000020a103c04ac0d2000a00c1503400281000806000354111401c030340310482403030341501c1d03c0c1c070010500140032103110b80201d052410222783c8418910441009071001071059003850705685900ba040000188204d0301840b078008081b81c4000d07600a03a500e420040d41c00410f0f41040300c40010151600a000340c1d050140c3c1d41050030480f5040c05c2920350001d40170380d90803610600b0317071381c20042884203601074654041a4007002c100d000302c049030603060390007944862180c03608059018200f1034044417118030b40042d400030040001d04541004c1e4006090414181c4003441448502d0100e074806800c031603003070010301505080701450703000e5143d0003440d03030019042e01e00103640f40008505a00910184101c1c107100061070181030000c005192103134080031a910351440386005450482803100130707 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 817364937 1250 817363687 817363693
    0x90d020d020708100f0b090a09030e040b0d1205040f0807080f030c06011404020706051f060219030c020d0b0412022107081305091e06040209030d14090a030b09 70
    0x5000000d000003402d0b0100e46004009120062a4600110080100228000100b9164002620140e84d00d52915000b488002c0001074044082d2030058915000d41200c40d00850a240099045544a14841c101d06400aa1415440108003800c0301e151090b500500e40c001403010340850400c030002281020303144171404407902017050b2855070b40d42c0e01843c06010080c0e4007800050040c25020581d246180c5405040581805490f80d14113080d070b00e003280d00307140300c0e040414407500030594000880020062030014100305040050158061407880f00058280503e040c481c00840d200e11a50502180d004040000641040c0c50300f01b0150050091020040c45903882c614000e0b0440b05032800341a0701440640d103012150b5aa6000941008070b4042c0c0d0688410310008003a02d540d10050702c0dd0903082c1000040d00442d062101207220040c001038042c501c18003042c0b001d51000100c0c0070340070342d190508840c06448003072070300d00d58412404840d800400c10f107000000c00c140c507654180550070040036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 817366187 1250 817364937 817364953
    0x30f020a180c03272418200901060309080702040c05030603060a0c081303110f010b030712170702130f020910051c0c050409151511100203150405090d02 67
    0x800340c0c003811071101380c4103d00c46296900c0042d400402e4410315107181c2c0d20540c818240291034500b00d4607158486600c04032601c9449041040c40c0100302c00300504401c01803191010300c408198520740500560b01403594914184050045c013074181c40d0380a50081c001d0041c0300307010500605641060326101d00910418000c11190207260148900309041569580c080f540d40401185c050030025000758203002e0001c0303500303801407070038040c810b6490900d00003c90001d031000300380340c540052035204085c3d215088841800003909110002c00280c40c1740b020300d49500c406c4c00050b184c4004002c0740081700785400401064494981c02600111134100c0309071403072140c500c8094500388500072950940b2400491140c4103203000342d000c0030421202c1c0ca000e500b0b281e25904024211060035800d241e070341134505c408002c0502e15400b210621a518034111243c1c103a034030645a81c0d90042242034016640200000303142185626003072400c41002441030019080c101401c0740c0f610820003002c0014000c0b002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 817367437 1250 817366187 817366211
    0x6030d021209150c0d032f0d0e06040b0105130c120f1803090801050c0403030c03080714070b1b04060c060b0118030818011d010305090304031a09160b04030f020a180c03 74
    0x241c40f410009101f1289102034580016286641d07102c07640d03400245a40301a10740c42c0400420445101c0c920810950805505004c00c20004018100c00c48100c9800c200d030481d072795a1b1002201038480c03481e0700c0200fa5805103020230009821a45a858a543c061508407030515503c112000100c8017030800070400d81d00d550544c6103440c0305900001e0b01161b0101d40c03c0c1c00080c40340790065404036140c80c200100000f0107000ca01d0702e600030305080d00c40040a506019007032803c03c916003036118009003d10b240926000d005881c0201c1c01001900c050364807264100720f42d00801540356005000028021856100e18041500d504400541592810003c200900a501a96003803120100c10000040c0303411082c3c00440186c100286103a0759408280310000c0001c04621002c000300c101c0d201803c07083d1030000445450100170518880020284003810044c04810300121010703a60446d88004550742d150000c21400c8500c4e603c00360300d0303c54003082012800311960041420045980e000d02800c0b6241e2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 817368687 1250 817367437 817367471
    0xa060e01050609061b1b0f2e020c0306191808160203031902030a080f071d0d050d21020403080d24081506030d021209150c0d03 56
    0x1005042e04160300f08140c810501c2c180c40a00038000500b8040c070242503d8040007401d020410101c000120f0f0508556443c5140a0304600880c003c140c0d0074841c0280c5000d010382d407480d840c00d0b2030807403407207210070140506109001c14141c05001600316445030401c01199410081002d00401c965440e011014240102c1041c0207030019421169081c20010082c03003064096244500485e031600c800c000c170f00c070123120003d40c1030b0400c40300b80c01441d02c540020b64060b0441ca401050460400c50480401020940103c210b201021080c07124120502d0410041654800b241d0006420b510540c0851b112155000150a1311100c081500341e0300c011800404506900460100501001090040a099a5196010307040030705118240400aa503240d500100010301c0b504081d007103401013441d06a46050540f40c89070080010303801130110741c149000c0203468000c00e907036501110900080d03940031603803102d1810f00c0300781383e10002ca66a1102212090f80c1c828816402d03901203420084211401140e0b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 817369937 1250 817368687 817368689
    0x2040c03020a020703030e1c0c0918082a0f0d0e0420070201020c0a0311040615080414070b0d051812030f040213051e0f2a0c030309060a060e01 63
    0x383c1c000b48426400c550303090b1202111203484035001000d200d9400c00c004000c07446140b6150058980001c00d40c149030301401664464000c13007100c1600a02c507840080d42e864200c43d0f011801009040484d6000302c040d0700c0100d07981c0c6460000d40300340b00d500640f070000420314515200040c3c4485220202c140180b000b500c000e10100c1d404840d0740f50600190568141c002c003aa0341c0b052041d10410340c9807800180b94800540c006a4000c40b0001c9446a6824588102c1000c3d040c0ba0501280604222800030180d1000400c001c28a009551003844222809c210a0024100c40b100d40c61301c81142900f20401404201c80d101598a241d482520b15080c02184503042c0000070340342c451a550f10410940980c0201400407a04208860580400c00307409215050041480d500c0819a850074981001c12801002e0140308880055805101841e07035000c6a0311000c00c241c810520f00010401007041e1a4001c03000340101070b01002081014201002c58603503c03130030703000c08208403050b01d80d15002402582 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 817371187 1250 817369937 817369957
    0x150d0f0b0607150e060712111c0213091a0901150926030d02040914010806160201021911060f0103030504092c011d06090c0d0503040806011202040c0302 67
    0x10000390300450458180454190703400f400c0402d210403031550081c034010701107a02c1c400003081624040000300707250048030502d01085174050f040100007080c602048000100380c900c0c9550020f42a40b0200714445420020102400c04000908114840d850007201c2545102d1007070079044008941c0760000000d0300700d03100d038607650b081e240c44c1071000254060b002c00d1204c0c00c0c2400107003410601c0c1e00e420002031512603524900541c6403880e006018050314161105012040d4180006214020001a405600014401010310b0000c1e04050585c0240b0803071250030f401018507221901816008030148400c24030200407205150366003602d5206d0b641c800c0c080140015001c1008005040305d6400c01c0d0244500c521f4a0038003150f0b1070084005002e401e014454181e5103940c1c1e0700400040b0740c40040031811400c405840986048800c85031100460602c1a01c82d91400030583d003400010030030703075016108a1007240e00710f51311403004c09040440440100c0c801c0d0b00709142049010f2090080e40d0f00d00312 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 817372437 1250 817371187 817371199
    0x305100605030c0d0203061909230925091406120319080402010504080a060f050a18120e0303030a050f101203080702120a031a030627010209150d0f0b 66
    0x400e109508010f90b03c01f41c2504e5000c0c00c000e000c0c0707070713018480c0c840b02004210280d070000320340c1c0840707400101800e816410300702c5000d00d210401000c0381d00400d200034500101d40000841c00110300d0031451480b0030f904001d02441c500a085a900060182c80354040c010413100383c4100301140240c0341d560306c2615000c0080c000c04542001c40c07940101d1805811a1050412604081d01d40c0600f03031a180100f0400d50f18a0f44070180c90300502c1c6144143ca8000103001d0083c00944400b901c0046003956240000300b2240c4811400c111403481400800081c09000781500e94a051512003080901410350366001c00207210300104041c900c850452000b264003034544100103508503181600d904100030103450035802161142400500240b00500765132041d0b072000550a0380142078049511103030080c2c075000340e00640a0142d044a142000f0a0003038030030505542001007104c20901a00800401d10317080100c0d83c1204100c1034004d0050013a20040303c900f00044400c2400c0c2c10242c1d5207801e03540e0b4102d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 817373687 1250 817372437 817372447
    0xd0507210b13091502090a03151b020c030718020403060903020307030206130c0e270a0b01080a170c0f0703151a10030b03010221060a06020309060a1b050a030305100605030c 76
    0x48945c0107462040303c01424106001da0704c0c0c50b0505461b846074180c0c01e6960740da510751000c0040da50402010311282d071008048803180790000c80da5a1059006560b01120a020108a40e446680448000d1a845501403056100030b00d40a07580c1e41007140100c0150203441c0c000342e410501d400d84141354a070000ca50482080c81c0603a400c1c404200a0035524550b035185040c0408402d400d440b0066600c4a007004000401403410301c00140a010b8008402c141c01040c01c00c404152441e0440c03105a030000f0710b06d55509004943c00d4542901c804818189014400000090080454011680c0038540f42d050082d030040e05e0b881d010220306855942d90001c040d500c20001c19200ba802030700d020b40042d00040c90462010062040c003d0b5101c40c007500071030240d04010346400e00301500d20051041740020b6040019804c001441d500500c2036a8081056000303180e8062390403443c060074025042800d54031290300b182001806045c08484414071120a5400050a10300c2682280c0c131985405481500744 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 817374937 1250 817373687 817373723
    0x1e090228061b200613080705010f020606030303160c1407050f01020f1f0e0304030c06110703030207060c08040b1812030405012f06010b030603010f0902060d0507210b1309 75
    0x14940060f820380002043c0131510044410040d804007800c0040000c040f01450030000410304201c00b204001150400c40601c0a1b644001003966000905800307590682c0c059458221041a0080c0000d44440254940640810004120f40c4251002904e06290a80000f0010380e606e050181c0d007031007a54850250300c2021400303000850456032103c1d00c0400c00728190140315103160880d41040d0341c125034100b000c0000b030744c00c00c91803001c40d600c680103000c00c03c0ca1510080c0d100c0301a485054113014140a00004100c445000c40b000380880c40f80807900c814880b002100001034080d045400396515040c882640c03e000400e0700c0444505030364440300c0c2c10680701c50b50300c1c5100b10403420f00f00d40d01c40d0b124500e1030502400107501801c4500500d6841c0d1400380304042c01e6490491303024865030303d80f5aa00d0301684070302c4101e55003c0007110000c00c054803480000c850702d000c1d00b10000704171100148940d0440c50960001244080200d906440340440d000103c0200c07020064001c00160158a0411003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 817376187 1250 817374937 817374983
    0x30c031a01021b01090f061d1206010b07110904050c1008010b0901110f1504170a0503040b100911340210090504020f0d0e011e090228061b 61
    0x943c61042c90300c1402030340d4802a03103902004d01d030403030130119a06c041c0c0c9400f00355448010701038400003141c5102140146551260711a1010300500341d201400180b030106011440f0203100b001c403800740c44050b49180a05005881e00c20000c4203c0c0b240300201b00140000d48203822907810703100442005440e04007400010f42c2c00300c01d42401108180100315031030241c298103002c0441440b9000d107803200b0b40d181626081c1d07442c0e06001e201c442d0003d424401c0220155004083c1c1c2c1e40140d2005078039031710392a914850610982540e010280b018203200f10480b4010600c0068004c9900c00306a0b850000040203080e9020888002c1e45c88540b0040008040586410580a440d0741003a007494002d06841c1c401080c180e9000744000380c080d41d00007a82110858152040268810604000f08504c103205680d0b007170445503480b0a440d451780c60301c24450071f40d907844482c00f59000c1090041800d0a0030900c102c9444500d500c17507440072a08404100c19020b4132034609208059000d00c000c24000418015503c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 817377437 1250 817376187 817376233
    0x90a08180a150519020102040f030b0717070905030c0d0b040f0f120327020d0b0c0d0207050c010809120d090c120c140105090901052e030c031a0102 65
    0x5071040c01d480000810701108071004103605034541e0342990394205444180008040c0f0010340c000c41e88100000c00500c10703560003c1043d290301281c1001551141c082c00c9660361900406844280c03070040c02d00c007047d5004036424044842c20b50540d40021901e60410806943c00b140290185500c80000380016056602c55800c5512800c2240c80070100768503440380b000c001064000200303561780c1114807000941e03c02c1c03d0741403900350440c2c0801c2e0800c0d80450b5001118500082000c414900800c642c03802e41d9096901300103544078115194080350a186a48600d40360441d80410780000226070101c201107198003004c4150305e525441d011984a20394004c15244100380d0351080c07024008601002250340c2c1480c22800f82c10085000c90070803d841d00001c0701c0002c030606000b02001030089030303200d21040d60304441c01103601c9500f420440c44c40c40c506d040080400c840c4011034020a210181c1c269002a41c0000740c0c9d6006c000504801c1800c5482e4411082002d001d6404000c0c10b40408001c550b20b02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 817378687 1250 817377437 817377439
    0xf12140a0b032a031002190f120f020409061d0403050703090f060c0b010905160c020f280602030304110402030615040b0409110a0c03050c0102270306090a0818 70
    0x40c00f03041c680c50258000140060101c0510041000c000d0552404004c0c000d600450301108602e400da410445c1c0102031400302c5405c1c148a00b080051007000d0013807030114125640c040041c440c05103403004442c001d51160190640340361920700f001c60706034801c0f08807170003184021203042c0c1c090320385440c03d41e11381e00540000c604118541c0008a01312540400303c2c001058242c403902800e0100385811524044141c000004641c80c001c1001107165500000010409580c1001c42900b229400450003810301c0d03c035040e4024200c481002c5601041644c80c2d14103100c81181215815202c100490b2030b40310585000e480b180f00f07480741010760b141550007103400440090040d11000388542c0030810680041e885465009030209040050b1034040c00391045203507005404030724200c0c0c4480007400e540120f808c0070302040808200b4240440096040354121440410303507a006c000026250503a80718076808450090003002c002c07070700000c0006071000d0441d90003215a82400701c5111102ca05443e580852 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 817379937 1250 817378687 817378693
    0xa210b061809180c0f0d05011b1b0203071404090507080610050a0305030d110409060b07030f08060f04020c0a140d08160507170d020a0f12140a0b03 65
    0x52011651940001c00352080108001a121100c0c1000c012059400034800340240114106000342081c0104002d400d1350300844444004c01412008105402c012000061441d0b207000e0350020102c0035680c5900344940603948045420300c1c0804403969506040c0e400075090740c0454401e110415440180c611191805800060a44400d0300c4403403404840b50f00001450304400e0502a40762040000480a040d0944041c02460719558600356248114180701101c0c17660388001441c60b03402d072401c650042c48101010b00465448107050195607101d4042140820b2220051005d1a4011002c031407046c00006c281044803035001d010300000c1d62029102c054940100c101a0700003d000f81c21034800b09003448000d002214001c04090803015010b03010f40c0c102c17810114140c02d880c1d4400100d4011a601004101441c0b41c41d080c18480390140c1d0702c2141c2c1580c000305600c00c0c3c0303030380c48a8205110f03490380c0d50b034a0110f10303204d000204503825001f0240c01c109003d80060b00798035280d04440340c8100040d080b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 817381187 1250 817379937 817379951
    0x50f041707170717120403080c04050603010b13080d18150804030c02030c130609050709050d03030f09080a050c060109180605131b0608010e060117130c0f0504110a21 73
    0xf1290f2140e208480d00d6032441d02c00000e0205041e0701a234a0b9a22840c406d10182c54241002e0005505010511440c580903100141104540100c2c034041c0c0010158042102d040003050140903022052120041c40307450218000090001c00d40382c1d410343c8640c1c10340c07200b03162921607840031100d80400d031106903010311599079001d001d51260310b0009224a2030180014803903041031304001c2940c0d4040c041c0350410450700014403d80e9100510041059414100014010005a01b01c1c0c09000d08001c06800309801140c820301c1c51340c0040c01030500328910070030340d440c980c5c03112015801c803039a07490410400000070202a0005542d544010307088412903c880c018440c05545105046a5030003040940236043c850400440d6086074005001d010795840c1252103180000000700300b56842c1d5018428201540045441d00700001c0f01c0a08164010203c2117145880e00d0100822101520a09009a18003203a80b405440800c00750782c1c40060a81e00c12640060a61010903e43e401c0d49003440400c0e03540741 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 817382437 1250 817381187 817381223
    0x20606090610032c0c061920100b0f030f06070f090906080a150203060630090d020706020a081b0f1b010806060715020f0d050f0417071707 61
    0x3208200c03013000d504000400e040c00380d500a00341040019118000c000a01046c0391010002030400d01c0c210103494480340c180e4030308400901407418000300c0741060048d0040d01246102c3c40e000400c03084010366008003009580e00605035100482402d1010340c1d000000824601e52090003c2b908021141c9400c0c0b4905464404620845825500c10b0f980d0f42d001c0c3c0036035810042d800c800a00d5138103903001304600314030f03101001c59018460050034111071110703401401c40383d08503451602c0c401c24514490214910b415554241d80c1d8228070f94030405031142c0800010f04910015050300350031340c4888610304040e00d11400103621081003c591809004110361710b000050100210003880313054041c600940c81880f0000340c64441d0141145006403030802c2080c0104910310900649560610700c0169160a0000101428040c081314805006d0600381400a80100410b502c0d009030b0207201da0600c51110144440c2d080e2284420040001098030300c0c07801c1000d08d10019244050141c10116101d01d2003007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 817383687 1250 817382437 817382471
    0x70302121e060109140108060613110a09080f070602031b0f060c0d0f051e0a061802040f172e06031a010807180207060e0f03180102060609061003 64
    0x105941e59000c0c40040000145600070003000480c01d001c041c0f000e50401e001c02d600c641e030042c40319016691101c0c104404003001c2e4004d031054454000c0c070340c3c0c55492114009115600394442c8032769910408442404881001c1a81d00172140c00e900294500f002c140003141e241d80c0900305505030b034095810320605044044c08403612800f00342c1c42e00e0307503560304030100c400880d2000c203400d840f018035040402500c03001c00929040003140182043c0e071a5616400d948016081c1078200003100108117180002161044d0094019180752050b000f443c0e6445080061082c1001075010815a020b245503c1042d81703900c80c42d0001022140704540c911641001100955405500448140081c840089036008209a80c0c0c1e015158443c090001c5a01d0f0000248254184040d1521041c1e030020f015420883d0700d0b48800d0000000741e05a5444400c181741301c5131a50420300344507000042503c00b0140c2c0b5032001c184c080c810b88000304030003141d807180024040c0e841c071103044090503d5901c2c550328500300340d90 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 817384937 1250 817383687 817383733
    0x1e1005010611010615080103142a1f0e13060803160218010e181c020f1b10030e0c0d060b0109050d08031515030103060204050a05030c010207030212 65
    0x2a281c1007200b9110311802400c485507a03011401d8020031a50114410741d200801e0b90450360010101c28585440701c21817824003c40003840580e08104c1003001c0a84441218028200d80e401c8078016940c0d0191f44d400a030003029600c0d4540040e03000c0525403110b19000706890030204210100040c0302d5160300d0200d1440e80308682a0079001134040d004021440e10340c00a19030484c0146181001c0c1d45041840190302c840507080300c0701042e0840e001000c0e414100950708146c010703840c0c4a840d4003591000a511400f10761002e405c04d004041e80320b1007940d0003103c079411050001d09041840c0c544110101d0050118150006140c02400c401c9109507443d00751016956024200010f0709001800014081d04070652080d40030706140054200803c00c0201a2540308104100c1820002c03034000005542140c4110398200580c000320010091000c6030b400351007030311419503103414410307203500800d596120003c0329240141c0c0101c9040c401800c2000e180401040f209044490200c0e0300d540c2006000b9030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 817386187 1250 817384937 817384949
    0x30d05010302120a030f0509010215010e070306060503130215040302060d0f1826070f150518030a0c0c0f03050a17130b0a09091a0a05010503091e100501 67
    0x2640018810752a003092040b50311140d080080c074414140343e80241481a1074400c200500001003130110385a4000d122103822280e43c840c20745e07115030312040c180784104410349034803001030314001c0003140250240d4104e900904562940005080f960360800080a08091243e90b00360003c2c84000016203400001d400350350340d094004501c0458010031102200c880740c3c50780d6a204518030449000c04c81c010300500c01609803004404018803481811181d42c40b80309801001d001520b90200c0501004510742969115240f0f0f0138080341e281c20f4008081c0c1920000202c1617900100803204105000d448140000e40c8074021205055980341c81403000c0840700da0041c0da041e00f25102142c1000400341c070103040301d880340c2d940ea0f090520450468407070503d40d0080501003040014410455401460110000c2c40c0c4140c0a002c08001d003802031310b1134521851392034000d540d0210003041941c080e0080c3e80c03143c00c10b08018284010003480c41c0c4041200e81708030f00303043c4c0030f850400b050151050154134044c01d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 817387437 1250 817386187 817386191
    0xf030705190201140603070515090a03120c050d091a1308030a02150a05010b07080a03181415070e0622030606171606050a030b1801091a060307110708030d 68
    0xc6130b110600c191009000501ca070f04520700c00c0c8000c2e42d42c882c41800d40303160035402684480c000d42c0401c20000306a007000d80803050707030905484c00540c8030030070b40780c3c90384240c05607020441075000030b842d0b4102e0760080c0154454020808900c948403e000303850862000c508400208d555540900e00396400700e0301905c01604605040f10703403c03840952194104040c172004201e10341c50001d50f101c41d4002c40b80010303e64040021014407140c03080e00141408207442400302003a403a0b91404903565548101d142446018074181003484a5100741d106110b0316660b103030424440081010400c45074014194002240408001240e25081008910000d54818000003036024180712070304400590702040205d80754045444107103410300780c4400108860403414041e4403800c0c40b01083d8050102c48641c19003001403a07800d203a0890a4411190480d01454401c1103080003102d00409244800c001480d0404020804520f000317100c0c2d0300b2140030121800c181c4800030f49803d105d50950f803196251103101a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 817388687 1250 817387437 817387451
    0x314060c0d180f2618010f052101050a21030e01021e010b042f0703050702040e0a020f03032a0a12030204320405090c040905100c090303050f030705190201 68
    0x420300001d01d10464024403130b01d034100a59128000d034000c1c1074503840e504002100e070180381e5043c011415a010340c50344140510712038000c07450701c0303601d0802446402d00c41c8a03031940c00103008981d290300003142c00103943d0080032a031060300c0036074541101110312411445960946680d00c610034081034210b03500c410010a25640540400c016118590304100300301c00d500003500d40490307141000b05215800f07403440503201c800c9070038196018014080302039045820031180c03a1460b00081015800c40d4800c80d5402120300c00d080606030b0340c1c0900320562415008240c1d0030701e0fa0b40704c400c1ca80c640f00c209500894403201308070f540704041d09481192110120340c0104081c01101c080b4036407180c5801644945001e25118540002551022042114011542e40c0086814bc21051201501000020b4402d012400180c500035039608150403415075224038060111885912943c00c500860760140c0d142410f20149081580c03240d40040c020400b4403004000420498818403149624200c0380c0d00001004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 817389937 1250 817388687 817388723
    0x1e020f0109140c100f03050a15030501020d0501060504080706030b03010906022106010c031d041d0a020f03030906030103080f04050d0f140f030301060507020a030503070c0314060c0d180f 82
    0x4010740000f84281000c0c4010103c42c5d91100d12940b881c4441c0c64041001c1e150140c22a00801118810302441d10b1000b00100c00c0c004150018941100e060000300032a1380e032181c3c120303082c4c0941c4c010000d241c0c100c04010088244a5044804100e1005000140b0340b075080c1d4038036003283d115500e15030620083d02d254000c14860684c1140d408042820704402c000b00d182e130010509800034989841c090070182a0b8642034480c0e501c505407010380c40720070001d508071880321103590b2081c25604074424100c480e80100142030120a80e024500060100e600710390850f5190081908215060044c00209000005840c1d03900c94603440418040c003880217481c03649040010480950660030301c010b6210005c5080d209070001704585c11a0120710300140c8824503480042c404840d941c2c4080c0443c400400c81e14140300070104001c08892141807617224000040d5040740c0c403100c0482d540e5074098018402c4a14556580d040352101c80d4210f40e0b1082160b1040ea10002d050f840540300751102888a000c400031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 817391187 1250 817389937 817389943
    0xf0a030f140f0a02360910090b1b1204210509011710090e01050703061d010618050d0b04030905010212041e052d090103031e020f010914 60
    0x140300c0956000d0b14601d01c07100d0001d40c1d00c26003400001d004a000d907009401c0b248007020700100700c0e250b0804960030000c1c021515610320310152200603844c05088040c4800d24035601c40c1d100c00075448600101d075070b615811042c180d0100810284c012103010404400000144070410780300e684160000c600300d6007013016440703800c0340c00c60000060200c100b150740d800380e0700b0120b407088040004035282900e580380c0e80d5030501c0900c145e002801c0d1078100b44000100c1d44040d00308500c074550f80c1d0390802409070341e0350a0341d240d140f00b030320302c00c800c108400d0060004521a00301c16658240d014000d840480c1c1e031b00d0200d0f038031500a000540305180030000340001c041e071200fa03501c02400244001c15000c0011000740c4640e208901c1086808d09151052541082001e2200001814003c0c1492404140c5c5001034204512002401c008418010500801441d044c0c080c141a05d80582d03508500440000e01d50500300769044150b401e40c45a40540202e9600034010070f45420700c17444c140c0380380d0107034520024030f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 817392437 1250 817391187 817391213
    0x50106090605070b0f04050337141902031b030304030905060a090b0904150b07050709200a020a05010c0c0224030720060103080c060f04020a05040b0f0a030f 69
    0x40000c100055000700c4d4960202d6078020b1410900c0036486d03113035031034014610710a2200751040d0000144902000501d8150075a414000000b001072003c02005400c50303a084c0304c50000070b034000084c081c004400b410406582040c41a5004892030801001748801c031400e00d80201c840f403603000100b08020181c2c028242402010161146c2e410700c581124080d000071040d008185401401150340c210b543d5481d0030440000020251072803403d6220406240140d0140c03c050781d441c17182d4580080d83c24114801d55182001641280c2c081601950748041c650b401709000e00114031a111850000c90401e21440460b58003030f45400c425494640b040c0b0a900400d071080d280c0c810313012892024000041c4040300c0d88200b040c54103a000c105000f424504c0d9000c0305020a140d84101c00000c800c0044040092828003404001c45030903079a03030648911034240444009403c544192000c00c402d04058001801d583d000916034141080168080f5040c2e030500e510035201d0399201042345081c04a203002e012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 817393687 1250 817392437 817392449
    0x7030c0c0201020c010f050d020301082a151c110d0c050414060c070b03090a0c05040507120e0c09090c1005070f020d0303020705011a040c180e13080d05010609 70
    0xc0400c80c29500081d44500288102e14148044c2c0354503481140d1055003200d05107030300b41c00115200d5071184c4900c1e9450020044464503109441a21145200302e651003140c0098028a90780350f800c000030049070103800c1203406014400201c000ca4000440300d0065840b1242200e410325184d17030041c180a002d0f20300194000b000d11104201c1031010116103091041c4010f000e803911540e6684400007646000b90326404200d040c0b4020042c485516030218800003a01c4c0106518440c00b07890b0300400040310710640b440000300d80401c1030100410010f82025402c0e40b00c0006991400e4501c4021440041c0100d500400d40d4109904c00c81603480c181c1100c2c2d00d05801403402a040c0703006a541c41000c3c01708035402070f106020016030a82018825011900e20705d501200a009080b4884040c00b4050041929140f09508081400400c60321501c465406c2d00349a210450b400d034a090200c02c0c240001610503103103168044010800308119030010440910b1900d4001407075850718000401c2c050700b03a0800f07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 817394937 1250 817393687 817393697
    0x1110d1b0b09211c051e1006093201051e09030708060105030a081e070f06060b0a05071b0e010b040905011202060912010f06080f100932120307030c 65
    0x3c880d68110342d00c1a13807145a118800052140c03130351285881800c80000141900080d000e08220820f42c096000404460040d10b03221840c40c0c40d80c406418083c4103810951608802d0030700e1a80a1a0b0f10740310454000c1e041c1040ea151802c14010100c83c04190601c1c4061100e00240c00c1c401c40c00c040061400a000b064003030700103941807500103902d81c25080000307801d00304003103a103d00110641d2403800d0360481911040c1d40e180300a1410703000700d900c1c01c07a0a560491510b60700042d51111103007110058010b9503100c1d49042103d41e200d071105007140035a1003002c0c01220300421044002003009002e0244860034645591030a0642000d40303405801074130303401d200425408010303150740c815613941030011505400c0703242030085841e00601d8000d20481119041000000c0c1c4594082180349801d40d286065940c140300014041c810340d10700300002083c0403860f41c03030700c151510405540d0413840305554841b5241c050708aa60340c81c00345050410034410b8000410f1040c0d00c0e8151290309c910030054185 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 817396187 1250 817394937 817394947
    0x60a06061407061506030c030c0f021f0f02160b07020a081e1c0b030d08060d021c050a03090609080d140901091208040f0501110d1b0b0921 61
    0x10403504910042418a11010402c20104803994101c007048920700b0341c0d42c0c00d0b05661088000c000e813641140000200f440c080c1c018150364810391011400d10f405400411000107007051240c5120b10281000e91002d58401d814958400b06000405e002d895100d50080010000e050015924401920a1080d94090b0415030000303141c01046d60140d01d507171850020640003580821407184180c94009245c00100404030b59502e0704c0303504c80d003018002582142c0000591181c2a038a6010503940d07c3d03031001025000750010b2501603102c4013111089080d08802e99255604c3d03a2402002403411800315150a01c203120304c0b94400040001000e0308801408203010b8448041c03d05054200c61071a60000000c60310380d0380e405160070800404900d056041c4102030790130628142c0e0440e001c0c1d140c21004003e000191584102d002d905003440c95409000c4d0f10228030000c0d0342884c81609070b01261a8104006008110207450070340c402d080c80c0015040140b042ca01036026000b5130034010b0f8403446c007405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 817397437 1250 817396187 817396199
    0x3090503031804050a0b0907080a0f06050108060d0303090209040308010503060604021602131104081e030306011209020d021f08010e0c0d09260d05060109210320070503060a06 77
    0x12540440700000e80b070000384c5407102c00700ba81c040e003600040560029180703002e00241070751161015100b0910350004104070381502c0001801d40c0d910380700b0b990002d04040080b9000303140031f84544207441e10070b0500080320605036002c43d00074441206c00368007003145c01c030041042d400d0074003449074401c404690440c0380295505801c050402c010304060b009030160b203e4200048099448400240101c1c1001d40e20380ba03031102c0b0b090350354107078400030f48240d908a082c403444110000181ca00400058640f9406007001c0c0c0f41610040070310090682c0d00ca0004a066009604c41200c03031085480e90f006114584994948050019041030340720810b0b01d5220f03402c000c0f03214412020b0b12600b03080207502080c5520213040c500044004840134002a68080380500441c4403903100920b405a5010001c0c8007580d210350042d03452814900ca1001455051038026020144440845503194030a00b010080e00740c102343c6c69100c0c1d00d8214016074040e84a11400e019070328007040f00c0c40d8000d2011406200040c2401c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 817398687 1250 817397437 817397467
    0x3020d140403060e070503070b0901030b3007050402031602010b03340b0a090305060112050a03030209060d0e03040906140a09020f0c031318053102040203090a0309050303 75
    0x100c00500030603950134940716580014496035000702030040c00c4982207501c035820721001380c0c03012070001d000c00e18141c080300207400c0181d02d00e000b08040c001500030100204100d441417000143c0d0100150207461404a0580c1c0c4610144d409103000042003407800100920103800c6403101e03040284203070b00c035500e90340942064440c6000707204070115801e903843d1441103c40848030400c1d04960b800032004180c0e4105540d02401c0ba10440780950121000e503642c607891848180da106802800304c0d007001c4041e0003c00e001e03400601c96020050300071845c0c0150000700d40e00301c40d2001031080042c4c00016081000c08440c0c0101400b1300700102e14402047c1c2180c1c005001c030001c07403089440841d0080750881c1b4485817001524405241c64050743d540f203000403a10340c19031880e805240310f8041040e00040d600c1d00a845018030880fa034601100c0407400c95141107010f00380303c40b80da07086030b110350840c0d07c01a01c40303002850059545d0320081101100300d140190400b00e140d0800ca0195000380f04402d2402402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 817399937 1250 817398687 817398689
    0x90e0718090c090f0b0109080a030810030506070c0b0a230c0f0f120112020d11120312011a131404140403211a13020d1803020d1404 58
    0x9110a51003445031440080054200884081c105400703100c400940c034401c80d0815100075003c480204000c41e0004010341d0508814054001c9590000008030f00203409049401d0304074400001421140d603030380e600c01c0d24000742202c544c0000382400d00c5e1042000b0b0390000084d003210a9042c14004070b502c200d104203149242c1c0182d868154490300c049101c444209080320700c0c0d0b0308801c0000355580084000c0c03003255070120703400c139010085600000a0f4055a6168001d030705500a00310310041e429501d801e0091240001000e920002da2807900c00e00030410402032240900c412806642903140000038141d200c7c561a105071803810800031481c030300d940c4194000030364010800f41c034004c0079050085030003001c1d07051921558252140501051680014040e9400f1102c0850030030010b815500240581e0302c60a11b20340700d0b0500410f4a40c6034540640c4601288038040300041c10802c20035801c000392120003188100c810120885078042c1079040c48113036251410742c14a11070b41381d000d00d51031050f8896 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 817401187 1250 817399937 817399949
    0x71505090112150b1308060105090c03060406090c0e030f0a030519020c19031101030e12070302031c0b090c042102010224071d030d030c02191a01090e07 67
    0x1003080c100305005807035488090041c41045991019035100c44130040d50740c0c003001008200b600c1410002602d610001030365030688101401008140d00c0343c082c0806d0940000e407017079034407680b05c0c00c010415450030304c281240710940350741d0800b0014011040c0750030544018080c0e4140d0700169445030109412034200d686007460014501c40d00300c1000c104134140707130f1514070003a4403034499045013005c00c9440c040c4c001941e019600180380f64070340d040154111003080c208045a034110a2440b0380c407045070005011028041d0041c1ca2424242050b1003c0d01d22041e0003241e503195884401500d1404c0130483d00e640012602305640c54907080884104403800c1380312b0320b07001c80d0500c8489031085910070b10180a8a460455510902c46503540e869800c0000032a0340e10f0004520360091a602d51900c1006c4101c00ca015000c1d001504d002c450440242101174180170a512640c0f0031304440344503040900d1000e0f4018000d201c20349204861001c031454042e40500e8500d424409690480030012540ca011102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 817402437 1250 817401187 817401197
    0x3051804021206090603190303060e0106020105070207090513020a08010603030212030403020a24020d0b10051201140a080d050403021305040218180f2b05040918060504030e01020715050901 83
    0xc1c0361741c00280ba1900c00f00100400141d100d903e1020540c15400c220b003990b220300207002030b1f6a2560302c220308031901142e0341c100681c08044204005100d5500c981e800900d08201146005590340205440c80400d40c841c20740ca07990356104009056060043c0d414081100c0d940c90718600300354800941e1451002d80141c4491012544002003003203202180c1c828140c404001e54407032900d503180c1001464851680e40c000c0d010b996401c0000c81c4220304845c07031850500240301559083c5a401500d2400d28070784113030844410000860003200c100400d90f5250700581e29199164110301c180000c81d540e49098200c00790400d401d20005943e06120203185901031000034242c1d030b440001032a85661615407042a40c000d640c0794226135040400c401109820318601628081844c80c0b5405103400d50030310103c0021000d10003809148002c0e08407500c9441e00b100310088402c040c0d2152400c4601c00c1c0d03030480208080c40495035803541c040c000d940040c0f825086851004102e458098118424101164100a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 817403687 1250 817402437 817402441
    0x901090315020d090b0f090f031b0c060c07031101080f0412140406200d020309010c050f0d080105090a1506030b010216030c030b01170703060e030d090305180402120609 74
    0x1020700c1d4161003050100c02c005000545140c280003050300303001d03602181c42d603000c0350000d00081d000140b0183c0e0185120000c1d482d020150009150340074030005000f000e07025204081d1031503039508000d000ca069412000d004144d1540c030300b0021046010007118140a0035008010001d8599500694050b411007540418400005e00c1241c0f072684071484002038100211700400c400b03500c43c202c041c030400342501c503890b40d8000c254540e950340ca4041558005074000c1000c50003d522442c8801d4103140319801316480d00d0400010035040401110301c80c0c00188010004102c03514001c80c3d0079410030601041080102080400e01e40d094060b800307502e0a150701c070b0b00d4801c1e0301d034420003036459000e1070100070180d541e03164a0400d00615940c40280c0340e48000c0300000c034200c40080c40407110501414003c0c40c3e001d18558410300a810a801d40d03103154001400503034400708150140b03c1500f4440d5030355071340d91a8074018601c3d036000480000f038040e81c8107105001d2480281170680381c128004503122010ac1d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 817404937 1250 817403687 817403723
    0x204240f0503130c0902090126060127140f060c06220c030b070e0303131e03060203070905010f1b080903010605130516031b0f0207080f030d0b0609010903 68
    0x40070303c82c40204a8180210000b403d014158003500a2139004d03600c2da1101c0381a0303c0f010401c080ca010440c4480d000c7c180200385298060140320700c2840c09500880f5800e01c0c034081858030500107600c40201080c414030340b421a4901512244a031080c221825400c1000d080300c4603a44200003040078043d04800c28155019079010090641840d61010940c842a42c507132524140f06a000e441080119148569296003444d0205c1690028440301d45080e00080c900700c0314074480748802c50f956108109001c408000b08000b030008504c0b8035560340390050968606030004100d440020706050400c050032010405450000300d03030701da40c0d94008a070503031100751034000a03005110315845190301c00100700840004a5480d0402442403000c0d582200030b00549020a034181d030040303000c60340302c1c5000703010461046000c3c6001402c01c1d00c1038411039201d2a280c038060703450110fa91108083d07a91001c80c00040c03891f010b00954061400c2034a0700750034112150f0018100302482d000092040710b12141d20010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 817406187 1250 817404937 817404961
    0x10b04081e031303060603050615100302070303021303030309050f1b0910081906050a020301140118030209100801240510020f0a060203150a0e0c160c090204240f0503 73
    0xf000c000300c050302040ea079481c54814014070b0584021191405040009828800407404800c04203601800984254141000c210005d600c03210007202810b909201602c043c0301400540320265220751000034100c041801c00324a054500454002c0a6100e00440035200074500c5201e0040d407825900318580c0c1d244c2e001e6043c0d140010782c0000c0d11a00c9a11040710400701030b188002052401170101b04826280d680d4518103910090245440c0d40711140704103403540d4450982d0b170b000b000740c83d030500715002d0b2294001b40c032004084d1000a0000d80428003801010800c2c400c110202c100c0d402510000c41d0f101c6019405402240708080c41403241d84283d07036040740284039000d040c20b02c6130700341c9000044520344400250020340707030308541311040c421210042c10003200000035034417540e95408e60b6646420300070300282e2040041c0150080004a11000074920070495006081000c901689460900301c40011918542c246140007140c0180803001303058022017003521494041c07030180e90b00e035600e0b6540782e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 817407437 1250 817406187 817406197
    0x160e0d120f020c09160809030408060f0705160302011a040509120a0207090507030c0e01080709090b0319050604110d0c0e22030f020c010203130e1506030a050f010b04081e03 76
    0x2404c201e0030020404803e84401510702000c1141e101e00c00151240302400e943c90183c0c1c003810303649074403003c0418540b2089040c0e659019640c0c0c41d0141c07810300c24981d0b22070306445a000031401750791640322000c2d10345002030980c09141e8056408201514241d00e055039203400420070f49600c0c1000242d40c00300769100b4030058001e0704500d03905221034106040014000c10034175510800285d0350041e500c2c1d80b50b1183e07003d6070041d0256518040400d04082c8480010010702c0380c0d0503070600c40d02404650783c520462011758014012009800146864249045032124400d0aa841a0f040405400005141020361000d90b01c500e40001541d584103500f0074058986008145000300d1900c40820403d03502180d800c05085140d4280e404050b901801660340f0b00541c0c000508100c42210103100c1000c0c000c41403540500352081c2c9001c5980e210000c035403250710554682e010942c4800c10450510111810113006040c014481d44ca0540760141580d21031161081c1914011190096200c0201007001668 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 817408687 1250 817407437 817407439
    0xf0e15130203150c162001080408030f0a060f0b0d06080109020907051606110d0c02070b071712040f050d0507030f1b050d110708030306030a080d020f03160e0d120f020c 74
    0x40500d401741d003002d20140d2004150361100c408240400949940300c0e200c00d900480d4412384450464032140400e0b03501034401410001481c5e69100c0000d05000386840b01401403c02000003551107150f218ac3c2ca06440703098100c49650ba044c0490b00300140c03902056568086c0380d80c5040394442c04203400010091303c00c0750000d4a130f07a09058400350b41e0035800d0010810447e102201704a04108131074241d8989882c1d1050b8074101f01e0a02180e03001c60300d8094160702108044580c1460079100c404844044001610240c40f8405844950810040e08129001c504400f60800314204810341e5001050400754404060420810030108064500c041c030340800c0f2254800b00340c440221a0b400014001014805018030038070403030000058010002c4103c034010400038000c0c01030445070745c40d11183c640c004132030025032903800c00c001c80c940c642440141d40a074080c00c15508000c1e002c03150050070080100c250f1482180143e051038001a8104d0300540c0715039207800c10154600c08160f059080c85600031041d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 817409937 1250 817408687 817408717
    0xa030f030c03120518061609060c02130608010e07080a080901120f1406030115350f0c0f010f173402210414040f0e15130203150c 57
    0x210052803842c0d85d520042c04050030031105c040d40d408401032a288807045d80b0700003241d1310402c04d0002a21880324041c056002405500c4c00c50501c1c0d11a40c12a007440d404210565501c4a18841c04d1505010190041078801d0040c2907034101c03030300c50460074819032881038103105660351000ca000340c1e1030b0030050004041c080700b00401d2420b0281030400382d008a50341403080d441d128080079100000c8005505503220700f001e0f200801801c00d00c80c8004420220b070000c05801141151083e0b540400c050f80350040144044c001c41c2510000340240344c0c00c1c00c03503042e052103104162114140e501019909117000340794071220b5075445c0c40044c0b10800c600c42e80d1441c1c0f088128510045040301d025200d0310038042c19800c031003a0100c440c205052050829450402d0749004000401a80710701101000141d20003c000049959842c0041012070b00c032000448002e40010f6100b6552200e88514541e00400048071144041541d500180d12102440075100e00d10b040030b0041503940080005850f0303209205254 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 817411187 1250 817409937 817409941
    0x1050a1a030406140f06010e0418080904060e130c0f050d2d0b01050a0f08490207050102070828020a170c100801091a040203100501030b0a030f030c031205 68
    0x2601258645c01c44400b40418450015900c00d401c007813040c000a45491048522801c41d05e54034036006901c8491100c0c3d00c5521082c0214452403245c64060180c0100c05a210406030649440000100b080d8001030290b0b100a40c01c0040740c5821403211580d07540807003d52880c840030700c3c101866100d840d07040c02070f050071042034804100b919803d65060390300449a261050b941d41000c00b4100e0b010380103c20050f0403032454503104504002d007500c00740203400345030300f801c0d98079211100d000700d00948568014149003908008254042c0b00c10f10184c5028405001564142220701ba80d4000c181044081c040070095102005040d04800c5546180d000300024481035a0b03512001a1401444103c9a90700540b80000c42c2886d000040c0c4030b61410a440b1070030240e190070355201c01000c1401684607001d0110072482d4a41d034491000b144902c0031500d02c0d0f503031182413200041c11240c0c5002c006004034018041400495403000c60001c0c1580c1c14544081001c245140c101d98a5507807100e04038483c0d081c441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 817412437 1250 817411187 817411201
    0x50c150109090335130503120402090f0115050705030f07050d0809010603110915030d080a0b09100311191203030f020702150c0f030304120801050a1a03040614 70
    0x101d900414000c0d5545410018200484d00302e00464035a0803954010350b10040d54034002c100d1210b6801110a901c04155070407648589055a00c8411190003c85499040000b145440c1e000160041e1301c0d503188890700d41c10182c1100008400b0842c0710240f10011402104001307040040b207102c42c15000001ba165905440e01c3c9656049102e110b03000300f0380a20000d021301c801446098200c9400c148070303082a504020a10a401a010f402c00c4481c0c07024100241480d14108000288040d142c0d0b1041c081f490407488840486140c0d80016100300c148209101e40780040b010070b50300f0b40381c109484080039010500010b8000c8103452501c1c40349010180b000a00503100a00341d1401c138001e407001e00c02c824105488070200e00c91090000e40c03044910411303541401c055030242c2260b0400104a0b24090030310302c0c0d21032640c0c1044504550f114110582c82170125800340c0c0040c0102000d550300b143c61070403d14a204490310249182c6902c02c000b00004d0709114440c1c21030300000c0b0340d4041506443c10480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 817413687 1250 817412437 817412441
    0x90d0203070308070308012103030213080613051614042d0c030510060c030305100b131406120112050a14030901030b0307050a03060902040b18010e070c020d03050c150109 75
    0x1380065012802000c0009007040c642030000702d0f0000b01050008100b1945c0c1d800780c00940200b15000810046101c1c0480c600b441001140d01440310340d4407401701c0c0c0c000d500e0694544025100c120b4070400f41c1c200100001c4050b01c0ca24003018408039404646c0f031590301d0b01404500d01d03040071480100031111000061a00c5a848510038100c9682c0c24080342e81d03441d45040c1041c0f454803172800020313808580c1002092180d8412034004c12114110015580e58140c0000c054201290480020f00c90307100401240b0407103414610340e8141070702c030389007003500340c2018541c081814420800b080002003801810880c040c403000c521254081501d07002c0425205040d6541d400020b01c030b601180c0b81c01d5903590a407900280d00030803100c00426803004203003581c1ea8100601150b2804a8125480710800011544d071001503c0001d510100c949250703616140c0700d20100cd80251003003003804890b84201d800350f16440503900e0825058145a540c0c1c1c01c1e1400164500005024244211030001c0004a2107082136 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 817414937 1250 817413687 817413697
    0x909130f0f050610060507020112240e06090c0313030507061506030e0703050d300c091a04150c0b0108012c1e1212180f07050402090d0203070308 64
    0x1001200c80f55501c2e013a440000c11200d0280d50302152050011800540c410301480c62200e01c0c103c0003081c03c010243d514001c0d401c0504102407803150810051098820a5240940c0030b4012913480516080c060700d90b03040c070b2101512007140352000f21280b50078103000300120f501da168031500c100640007803506490f2040e0018058400028142100290f04210004264003940c0d0010050400441100c1c001d540380e0040f00c03041c0510114010311500030120106440311520740381c03080490000702800b4000c0604255400035420161049414a12520300d00c1c00d9800391038106c000c55000755100c00055484201d4190010038014001c1c001040c4a80d0642040f140081104412051a940180302e03040710314180c02c00c03142a6000b601400c2d00d124108140c080a01402016500c00140490090b2419400078007604052a01c08050000c0c021b00ca0358007080141b01400030700704001400041944529461007428465500072074807165998443e4440e1104030741c01812036000541e42d240540341c0b9044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 817416187 1250 817414937 817414943
    0x30f0f070c1a03221101050a022b09060c0c03150216060e0606010309200f06070c0e07030225030905180405010b0d020d0f150507020a05070801110909130f0f 69
    0x1000d0420b448480b00b2011403105036000d941d00000005c42401100c0a40140c41034004600c140c000d2a03400b0400e5031008481f00150365603254207000c0201c406000c203c456030000080010509400e4041078081c2010020b43c0e500141201c900c00c400b0300d0b844c02902800c2c02004c402090900c0714401c000c001d80c00480c1545158040d1501982c804c0c005500b11504160050b008c00c000c0550100002d0701d0080e01d040554000304070075519001800800c80329041500125a1144c4005051155003c0003050703551012483c5420351910501c450110282c032907061032114219031016590042500554142c001340c40040c00d41e08002078070b0900390752103180030303070303041c0c4c0c1c01d52909070340302e0580c1002c64101c001150050321246003201190743ea240001c4030144292410b1280800310301e2146038500900e40174003441c9d802041000301904000e030509043c4e9112030541d038901a1a04407104604c01a00d4011030121821b41c496518490031a0044070315010042070550203941d2032041007609003a041179540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 817417437 1250 817416187 817416211
    0x513091406040209010909090c03050111030a050f04020a0b0d0b1207031a1608130f1118190b0f04020a02011d01050403020c04051e040803010611030f0f070c1a03 71
    0x41d00014001244242d1240c1400908040014814480d43d500501c1c1c07001d1040b407010b601c0c0c0b40d0307a8070350600319415003a0007007110f07000206100710030199018064100c0d0051310f4008460a056000483e01581c1380b0601c0d10404001c9001c5080410f42c4c2d2001001880c0a05004004001100d42c242c54001600007107403220040c500c01219124481107062241141c0d03004900d8041107103006030b4800e00020548c2140072910710040002480c00725007071030070620945a81110001103020025945060200461002c03146010855280c154080c4082c0f050b000e074a00150091900c00072035504c1500b00c4040750010700000d050440642d056100b10b4101413102c682e200c06920180c102400d9a10640c0c002e80185d204807100c801e28a0103520041e003141c3c2d04c20007024100e404c81042100700c20103c40030349420303001000401059800c51103050081010340301440c5401c0b200060b00100b4010800c22a50b0154081600c00410030422000c8014010003444002295100031501d07a06a0041711030b201442 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 817418687 1250 817417437 817417441
    0x2010c050702151e04031b0806090a06150f0b19090602060a0b01051213050c030a031b0215031302010320070201080c090a0b07050714010504031205130914 68
    0x1845101a0756005900070200d482e50201450000c2c039a0300b2505224060f1802d000310114085454070050009602c1540c0c16480c060b5941c0d00d02001da001c503444100c0980083c01000001c080204200060030f500100000302200605070081c0e0003481c40c0c100400c650f04100340803c400d0403402c0071b8022100050080781108050002c01c4410f4001c3e44030f01009a400040841d940030311076004003c08030310615180e400c3c4506c0c1e41c215049500103907441000b44628015980500c90140180e944040d0240c00620031404bc3d0b070380c0140103a40c000402c5030b100380c0c015019003c41da1040d0030005842002c0700056240d0038158442c0720245d456501c203c0c0880d2405003981400d090040840201d0300c40318650078105902ca8006503080d000c02042150083c0040086a907180d030350011c4007000c0d0008440054a03036942d4600746190411b6a04452411580b100f03072030040f80c4c1d1000031501640e6100800c04031012070050266080d0003a5001ea01c0080300046000c100c1107400d620110254075000d50207111a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 817419937 1250 817418687 817418711
    0x5060307060c030e030307060c030209040c09120b22031707081005040203071106090709060b03010506030705071115031906050f0d02010905030a061b030b010c060c03150608070201 79
    0x1094103114038808100c0306002d0b02c0103e8004c0203513602428001c1c083d28500215680e425040b948d80b0030340b131000310354041b401c46420b00f003501c202c0480741c105050020416042c511900307580c2d005000b00a0200c1c203a00e00203452000c0c43c00c1000525001c007800444500321510340070308000c5818040d00e04000c01100040c01d50b600c95540300d070045106840c0d03500d20034241010301c03019500081c640401c0c080002494070350100b0400c54288140c03100d40c081c0208a04104c41d04003980e40b0795201800079542400140a2640c0d40c01c01c40b5040410341c145996034240600e800c5582e5606041200d078401c8160740d006400e0f0551a0045100f5111041d00c00c803001a42031149007103600c1c0d4003c80e5041850900507902d10b0070660402141d00c0d0050401100d01640c5500107403410040000403201e043d03c0305840746860003400c4250324004154101404040341d2000000c0074490b60754000f90402e900c40d0740300d00d800350003644160504c00d0041f69248580b40c561402405050003500d8100043d031a0540034451 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 817421187 1250 817419937 817419943
    0x50d020d0c030e0105070b0f06010908011401121a0403120c020102030411090a1e0b0f0108090c041a0904110a1406040b0304030509120106090f0606121a1201060504050603 75
    0x10118594560072074440c00350700e0032030340c0c03100300210b0364180082000504c0105101f804698070650000d0034241c003d00d401d80004100003441e80c003c1405038108100881030300880301910341903866000070034a20030014182040112007011442d002903070403e00348000d240d40489100710710303280ca01c0240465812414100e0803440304a4015020904010b80211580340410321035410032202c81e0045407201c2e0b042400c50302094155800c90f0a10340e5044102000d041c9403544940f901024203001aa51401d001610b0f12401100c0d8058465030343c483e4034030980420041804048580606004010320707080c9001071101d101c03007503001d20580d10b051000034010241001501c2035200901100e0500c0d18080c0410441c3c0c00c0a48120180001401054007a80390b82880341070302e04615001103030003403a0221900481c1c0d244808100d2450400c40140403044c1c1045581040034080c650014401d29086813a01c4400c1c54a40b031164010b0b00000303030306000c0c8015049030050718011a0100401d031148010103503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 817422437 1250 817421187 817421203
    0x90f03051305011706150d150f0803120c071a070215101202190522060819110a05060d02130b121303090305030f220b1603050d18050d02 60
    0x40d60142c2e030b0000c1c4560030000306c0b00c401e001400040f2820400304004200a036a00218056480d0100000801242c01c0c02e401c20f400402201014510f05040640041c2150400a0042c44030080020b103000070042850b1990300d80049003019681103080000d0000c0d240d0650350240f020500b07440002c200c0f5090503d050804440403040c64201e0501c42d84c9c2032143d07a107140fa204410100002c00001601d071220201c010b41046010048009103803030250510458417a0b41002520358041ca042a88008079000031600d03003508801210300c001c580c640001c0102c4d885d90012600085e0210340c800107401d2035000f410700280c61007013801c00f107038445e6103070701c224020301c01c00c1c02c400c10020000c501e400d00d40171b03080d4820500a00e40540980e80f60b8685c5403031984403904100c3c01010014028507c4110728401200b480e8004018283e0180b0703001620350980110084203400c9480c11101c0410503015000700ca20078180303d031003030004200c00c00b41c6041c00e005916080c1d4240c050681c030307602100c2c404a8400d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 817423687 1250 817422437 817422467
    0x7080d08013210090320031005060d110316150f051e16080c030a120b0a0509070306050d0f0c0501170a0536070b09031e01090f0305130501 61
    0x101c421190300b010002c103103c261401d41d003032021202e00400428400d00b410002c0e8003003a8043c1c502406142d00381842c000a030709a141c2d4241c9041c05111041d69074905c044021500045488141c1209100080c2400321001c00c0011110b03080390f002900043c060050101c40301e040c0c5030b211070f5452000040d500b41c4074102d0300941c9880b80d40c114052111001000d8070a10100d580702c00d9400140342d89800c4143c4c44030061110356800458003071280350b408442c140048d0810340061204020038008141011024003985106000e00c500181d4114460783c802002488010035841e0310314068100202002850601607070250282080815194044c802180d485203000445084a41c0c442810700000c21024101d225107125112441c41e51111007030035800c0e14140c0041280c0104510042e83d4600a515807040d1140d0405100c0200c40f5940402d01f699406145506500c2c03542c802c140090040074402001400c01c110310021105040d800b034081c01200f10410010f00130680c4800c015201884c84031002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 817424937 1250 817423687 817423769
    0x150207080409050c040806070905210d0e2b02041410090905121b07050108131118090d09120210050a12060b0a020c0d030801030b0907080d0801 63
    0x2001103482d07940c060342d441501111120308103522850b0150a040054820500065809004ac490b0780b50001b200c842c003820250014800a0038a03000ca0b803200c000d4404141480a1403166201f9615518405e40075001c0c0750220340c1040180e081044034105003088140d002d14500304807a400d00190710f11240c042d120010700800050301c1c02c00030b00060441144215068040c400440c55403001c0080942003401d880100720841e4074404107898035264041d80031a04001003034050040c40c420640d000d10344660003080c161000e440100109803910800510aa042c0d25540c081180ea2040482c0064840c01c42c8d0341d070504000c0d03840c9100301404500200c080d60201903c00001034460284000702403652050420030481c000600c64002183d8036640507030008080000d245050741c0d0f0600032400324450444114a008440341c07001000c40d801400010030f882c210300d010442018041003104010003203070341102c0200d1602d110003801c2180a1250803070000c401d9a042e480720741207684042541e465400c0c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 817426187 1250 817424937 817424939
    0xd06080118170a020f07061d030a08030a09111309050d02120307032406020304060201060608041703040212010f090204061202130b0d050123010b030c040909060e030d091502070804 79
    0x400d4038143c0c450710031801544601c0150700b9400380144001740040c00c1e9511003004503005600031810308207100f040341b403190b00003409040014480d102582d03000144810009096507103450035a107c100908080c9510200110b083c0402e20203170b8000079203e511540540d0388038202d054007039a4034041c00c2e070f1200c3c040c0000d00018a1030b62003035212400300c900032640c04030540d0307210f4400801005030707400000c0180c000040600503ea02400352074014085854a20b4440ca440d88881c090030006076030500e50400000081025540d444980e40d190b1381580000304078101040c0700c5403006042c512400c0b40164100900042d260711030740d448030020342d00600310109694240500c94008c20100c4000c940c400e04126207040414401d1152402d00c40080c9a0b00c441c40301420300c441005001603200000e80802082000034106214080c0d070220f4108180115040a182c13070190040d09a13240d200b011440042031464012106030420b1400f1f6004103440304203000c091102c401648240e080180c00e140e800c000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 817427437 1250 817426187 817426223
    0x4140601030f020f04090f0f0506010f0b0d0c17010b19030501050f0108061c0c2103020307110103020f181f0e1e0d211b02040f110d06080118 62
    0x1240c4031809600401c0006c0c034150a55694214098405040c2d8288101110003001c0002c200041d0340500414000d90880d1841e28076208414442e880820740519103501043c041e0300c1c0101541d2a103030040807000300d1a0768442c0c070010550340007441c2c40d450040300302c1e10303909000d8001d1250302e043e0f60024010230f5000c83c1000066401030405041c49403c4039180804907100150180040656441030b1240201545030540009950056203880b100030395121250000203a00001194201d1742d204020712032404000d0300690090103408010400e203040002c0b820790311000e5092551a030042240c0100313140b1190b0840b40d52000f006250304000ca203840080d0342803440c005000d20131040001409860203c6040c002c52459640010304450943c0340d503016a00f841807400054200d41c8080c6001448094040c1d01c202e8a1384c1409400380c02550345003005000015590445031a002d00709941076941c1c0d080214a0000f400c59200e00349255190120341380b01100b214612010041d0401420702003400342c40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 817428687 1250 817427437 817427449
    0x150b090904050f0607020d091e03021306150302120702070f1404111306021902010f08091c11120403120e030f0d0e0a050607050d0806040209041404140601030f02 71
    0x281c01a102d602c0361402180d041c1108024141c49040a580034054524030424050b141100030b800071404801041d50080b00c2814003c241001c490301280c01c42c50b203010a03e0200010405908861405118200840c80482e00340d00207000d921082e414200c1240d60724401241c85401c103014007205402e80d054100a81c02c4810102003c4500c000c000003600c400035034141220364450150403a8800c0c6035001041032036014081c0b0729600b0300c1141340000c01281540000c042001007031a030b0040c0711300103000c01d080c0b40d020090350000d41c007900c134402038000d011040035252000d50202c1c4003d40c810004042c2c4134090550544048070b40c00301821100980100c419640110411034450f010b22450214101622082101c00302c184141d0316080300c0f1000c42ca00340f107220056900b0241c000ca04c00c00002001800c0015400c4075191103140c010700507119040040d0182c0305500819a01c0b41c14900010003148600601e54051441034600160504555004688801e002d02c0040e1805007044030324800340c00c0072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 817429937 1250 817428687 817428691
    0x51318031107080303041115030705030c1b0a060f060b1e0703051c0204180207030f320c01050106030908030a0207020d0b09011b0504050d11240d150b0909 68
    0x1c041030340c8120b5100e0001ca80b5541040b0b0341502c1401e081d16500005041c5110300c4840c1d1026140c15600d985000200a031040c0b102500e00942c08400040c40d60865403c4035070b0002d0640420706403126004181401c3c8050203d5a407440c012500d03104000450b800610120707000004c0840c0b111801c580c1201481d05103410006007070741889810008450400d200e00e0808106640d5800700603190b40c105090f160100e18400304104a49104104420101c0d800445d00b0003070220703925064692208010100348a42400c0713281052a96100022140d044041e80181034002c0b11000204000da036202030480c02c3c0c810000e0080c00f001000c001003989841d10f6001001c00c140003800701004502c050ba04d158601c0f004442c0c0710300c0da9556201102c4441250009400c440c001864614142401c107000600000c5013114010200d81c1940c03d65402c1d61241241038034a507548824048810211201c201803079031050340b0600c842440c24915120146481c03400c9020360350910f94181c2005026004e0000c48480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 817431187 1250 817429937 817429967
    0x1605061812030417012304140f0d02010b060f030c0307020321040201030f050405340602060610030903080c030702030c010903030c09051219080c0601060905131803 72
    0x4440400e100352200e5529010505400e40103560380c9182c65851541c2110303640500301c4503410310350354402046d00d4684004590480d4165000302e81c07a076252820039801d2100031081140070311041034800e1017010441a00811107078000748800d240764001c1000a100d000e110042010090010603504009080615480381c4c2e00e0040b20f280042c6001c00a40030240301010f510820310650400c1304550341406001035410402a0900441c2402c3d502d05480c0d00c10140500d02107880358409088804076800c000c1c50f6082102200420b00351580c60080d00d80204644980c0105841004503c0c003e200707200e498400b0307030940d231a203020ba00c1e40003609403507034806480c203021840309128168030a0710038420b541109100362400550f9855600c07002d40489815407010b072003800b800003011309507000480c852030401c04401d81d21800608520b00401603020f03a04c18940d4520680303001007101600074440105484c0c084a004940117140c219000a407005003100c2c000c1035010b00044d000003406280c2d040c0e08480 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 817432437 1250 817431187 817431217
    0x70315060e040f0f1403161a04120e060405150729040209040f060507030b01030605010201150b030604061805270c090a2301090b03030405100804020a0f030308100602160506 76
    0x80d10700600c0d4a50b4100000c108011010410347c42c0400000170600141001c040123541c00301e00d0681c0744d0701002d40408101d03909100303140c441e1401c03d07501c40341110082c1900810200d0040c081e51807420640c0c1104004882c2000461040c500c41e074107014204e0701c45001c2519180e5180c0d241e5082c4040204040c004075a541e2868452000141b42d50240d03500c9403207183e50000d440350181d4001801c2d50700300e90000f4156490710241034980210700429070150380483d040c0755940e03112000881e00504055002c0c52220801301d4081221910310f401080c01504c9040b19190f04030304000d40e8040001460344060102e902076a00b0b078120b030606480e0964041c44407100085c1d41c8150b1000c030980c0381d86c503010300003410b5a0b02d001840189070610500081e403c055001354105420003001c00e60301d00041c20284140300b80c8034005401c669131081d452016120071480c0d500441c3e0340380307000381a0ba1026581c0ea49040030045004c503d0701e2001800441103081200506680c510f82814001c2583c007113414854805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 817433687 1250 817432437 817432463
    0x9060102060c1608120f0a0c140711030f07081f1104170f10091401051b0d06050d110f1504090e07031721090c0112090203070315060e040f0f 62
    0x40c1d40d017209445041c0b0f43c030586d502ca02d81481408210340d81c0140c41418404050380001f02c02e8800d40544150f640d00060340d0b00041741d0500081d00e0102481042d06040c070500c000440c00420102d039000b0450700c00c540300607a04824580c00d13015901c0403004145450001c0c40204200c0052407011424524420107803094035051b00c110600340400d45d0740f04441e16031a17881c03000400a041c0b10240321134484100800850405024000310b81c480c04080d420000e0300070580708542410341d0310000003800b00400c078541d24403051500090031340000b0398091055011074101007a0341044180000c030540240001440c0c1818022030340000d240240d43c011040c0314004002c00014800c40343ca07281c2103a400c0a0340d8850b4a03450f8015400c01d1040c0352030304070f441a9414030610410011340c283c0000d02c2400c0c001c007540b200e04411402000920800b81d494440c0c14400002d000382c400120014200c0b8800c284215600c405007000d03c0c0b10b0a69004101e00520068440880d026440810f655072095452103024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 817434937 1250 817433687 817433707
    0x60f04090524090705040c270e060d240906110912070608041205250224070611070f08030709050d050a15150303030b09060102060c1608 60
    0x4840c405401c46040e486904405040c0268080360074060141d41e440082910702500320070b4640200d80f00342c50040307407110b140034203071400f540405c803111880b14038205c80028035145500c3d81d140d40307105203c0d40d280c0103004940c00e03003030030490158003a400078a414116034a0600940302150302c0040025115a17030400d000010b4094020f149030045608451911180048100408040d400e0f0203021250b0164008020a5401000481d80980c000c0d2000b540c22041840903107551041d8101810101032003024445145004d40811029074000d07100c01c280384070b10420700d00c4620700291416400e07a5040c4000c0c00040c245410440c041d0540f01211400d00d0341c01c0d518540da407030070510226012900842000030142e80071410b440204004c6030030607410000b0b07499558a48140b144050440c000d10306100c441d001458100e01e030350021341c0d6031080880350f80f82401402406a07241151145a003400420f845610024041c1c1c0903220100b151071801d58003405010001d440075004072100c180178400720010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 817436187 1250 817434937 817434941
    0x3040b060a2d1202090c07022205040c0f081e01090b040309090f050606040312032a021209030d0f030b0a0905090105090604080a0c02042a0f09120803060f04 69
    0xa1080c0510030302c4092595010070103542403a402110b403030005509508050b81e41e10142c5034100080780c03446544c1c2e004034001f0544031403d4901002201c0415031860009000c0d41d0f12140c46075010710607030424a43c95440500e0b0300502841006041c2e8820652241c40780302680317030703070032050845030000906900795074070b006c00d842e0101d44c15008103841d66020041c1c1c00040c0143c00c3c00710003030b81e020000e0b40741400009031180210700010301500e00303408000035103a0003580300406074841e01003074440e82c0b80600078200f00405484540d4005000d40e000810340d60b0600c4040d01c00654008000e0000030015440417540c040000703208008042d201c1540803000d0301c80084c0400908440c00e404036881c1380543d1440d0940b880500584543e078040030030400801c03200419503100c041c240c40c1580c011021800020041d0030120040c1200181d6101e03070f52214071002141040c2042c0a03260741c2c0c0342c07039041141607816a813140720300e00045c01e8400f98100003945080c011940a80c00a001490107460314010400b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 817437437 1250 817436187 817436219
    0x130923030d11370e01030b130203061023030c04030b010e10060215040b09070308031f0503070308070f140a050d1407022b05060702060609180303040b060a 68
    0x1100080c00104000359038082800090030080f081c40a8031104800804002c800b6840c10501040040080c882c001580c880d400595800c180280a50610301280d14000000d40c8255000d51140114482ca50f5020b80926043c1d600901746884028004405d5503007990140e00060000301c090701c0402000c40042c1d010841e1a003e03000050038039505152071100703244404a580c203e603095500c4243c0752580c2800400700d20358041c0c1d0040060080340c5a03800d00924102e007a03000100a68001700400507425418070020102c40902c02c10103c1140c0d9038030a0507151000da020152200c070040241c000400c10300140d818204e481802d11030950741912412501f4500304600403111604034107210085a5841115080c044000094881ca005696400101101c0c0610742d00c003051031044c2480d41c0d0103c40c3c4804070401541040a0314414500600c0c025294a8101d6001d442000114040340840a100a183c00301d070140c08000c61441e240d03a200e070114890003c2032103502c4401c1c5000481e00c0324222070020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 817438687 1250 817437437 817437461
    0x3060c090d0f0b0411010815150d0204092004030506070804020d1208040203070b0901050406140d020f0d3602120d0c03031a0a2304050411130923030d 66
    0x1c0f080d00303182c40c0c014640554002428104107000c0c091000141100e45181c58960040b01d8080c3c10400303030603040216019078004c60358824404a0001880c0115400c14100d4214106050020b40d8402d40d69056a001d10300016120f0340c005000502e91600410500d078000d40020405d81003140300b6030b503002e118822460300c480090103c000b40411801d08209a1014040c4040e5040c109402180003c007107010794414030341000302c07400024070410b00a000712141c0b0786580c1025582c500203608400c0043d07011000d050b81d500e19000310701c2c9030401001110091001100588800c01c0702e10884256103903000282640e006041001c1c2000140e000c1050300c0c500141901e07000b4440a55040c00307803c540c006500448018000444d4810690314400400141c901e150041c4a080b00040e4a030213481c0c4120103010f402918200a220900c0608500345152142c202c816a60910710290354005540c40c0b900300403c1c0b001060509810501c82d115202e600800c0902180d0403c1401c040c9103003a510780b8000c170 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 817439937 1250 817438687 817438703
    0x8300a050a05070807110301180b160302040801020d1d1911030c03060702061609030c12080c030706201201030605060301022b0b01050c062202030f0c04050a0b03060c090d0f 76
    0xc9500c0c2002c9c0103208040038078054001c8413910984540d8000302005011013810b100000407042c0340c50007503050380c0243c0441d400864903008655102c2e0000c0c0840d03448260982e5410341281c00e1030000058002c02d54190906000c080c2e58603039200041160580d030034980c140503111804040392030410a2511070707030295000b480c80d400d080e0001c800c000c0d202c010000400404940a0001c103842e8905081241c001c003100c004005e19508024005002e1801444a14080003400c5028012030b9080b50b000e400340d4a85080380b2190050f0b15200910070705003441c1035050424010008605d82d503109035800b60f40a40003510700000041104c1c03804407000f10f490b070040c03603070f0b00074510013a10340c482c04c40704030b0302820002d1400d44030410790356603058010808140741c550030b4a4240c04c01825017150201c40c0d070250445540c5180750301c0032500c2d01d0403888200e01841c0b4000004180e44220b00074401c0fa980c024025042944131240700204581c41a040d10303402c115014003507000200c403428038030940c038062441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 817441187 1250 817439937 817439963
    0x91b06173309010b070804030b1003050a0803070f030e06130606080321010b121302011e02100c08010f051201200711040504020a2d08300a050a05070807 67
    0x40058541041c1c2003010013800910441c000103901d0f4080340d0550350058503418003075070f40303076400200c2400f950001820350007410400303810003400b0720166020f410039868000079190542c00071030844a1100c941c11840d44080c000c54848911046c1e001c041c1d601034100843e81c144c469030140c0c170710350141c01003562a0f185021140c0d40c0b29801d110303441c0940039000606280c251841d101103140c0c18050039002607501f400c1c4140003168082c1564203030f000095462a201c1855045011f034031142440d194000c400c1c1000080c41069200c0c0c3c5d4018141c0c0d88140c05003003041d0411050044001c46269403d005641e506003034200460310020a45a005580000e1941c0310014500340c3c60400385444e00724065400c1000b0300c40140d80c0c4d1030344541a580c042524900002103100d1104000021220305150003900840201b201c0402148148586400b1b2420805c000300d10388001124181f22401e1203460f16040c441406118801d8008040c0c00c400307031808606119050310b803e40390307a009407421188501e403480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 817442437 1250 817441187 817441189
    0x1209140405131b150f1115190f110306030f060702070b070812131704060e1512100504062c0c1308150f100b0c0a060f091b061733 57
    0xc000401d400c2450141c049031044040501207d4409008180320160202581d4809003007580640c160020400c01400784a00c1111080c2c2c80754000d854050007401254031100c1c10321400105113018210a0303008090b01c9240a01103200ba4004400440345c8240c02c200c10085100a20b4400c1e00426011a080031214074034500a60818002400200b00724410b003c100f00c2d581d0044140049560262445800e0500c000900603040c400d1104551a00c1d034a0307c2401492030403240e07900140c0348142c9082020f25201c4400684040e090070b2810300300c25800203001b42c03040100c80c20503003189400140d1414142c121041d4074181000750022101640310844030f2894070360b12641950800c0014020a03c1401c011140901c0c048450107842c01324007000414800c083c004104940c07001d41c0101e0104010070303140502001820b0950b506803a0034502089070f02e813191400c1c2201c400c41d440c0344c0b0741050a0b03000309911010004010840420400b404451002c0681c00a800c0000c1c5a401c0c90507802001d4040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 817443687 1250 817442437 817442447
    0xe0709120c05280e01170718150506130509070306030206030c09211b0a03021c0302030409060f08010e0321040f02040c030e01050c0c0d18031209140405131b150f 71
    0x20650b80480d03806900100248d02282c2071a110408145402013480100304140d429054516805039800040c00a4298106000034800c032050b680219000c094507120000114103403410350101039400b6208201141003444280e004140d00300d80909803030724a400f050b640c0c90180102c030070781ced01040c0c2121b00203001403c10040c050603121821580701218030b0554000ca0115101207007a0f03460508001300440c24075000700182c0d0000c01030320009208c2151100301c00305120f08103104803d0782d90300b400c124010f000c0001c01a21340f101020407200064071402080444414005007051300c850700e02e00c5103807000d03880d64090070014454a81300444e109800324603581c01c551000b4013041d00400180114818050007081d08404243c191a00100c602c21031b13481c00380c5030041648000c10032401d1494050303085403c19140f0040760322181d84142c1d000c40d1038041c4000d4034804c440b10140e070308800400c1030010f205107a8104030035080c82c004c500d540e0303210104003041c421403070b400802042d182000c8581c0b1a0b03120b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 817444937 1250 817443687 817443719
    0xc1c051006030308010302010302030426070203120702091603020c0115030b1b0f0a11070906030b07050c0a060203090a060f061701060e16020a0b010e0709120c05280e01 74
    0xa00d02003003114a5624020490401070100030304043d00000450f05201c018400190074001c0f04600843d803107485810000c02d40d009040480c0640600d40159540b54405020346900540160030b8251964810f00100d4034810400301c1042031660921100300c4801d001d01c2040c0c8040c0070914610390b0981141440090380c08000c102c201d5a184010040c1007110f00d0307030203031440036402c816480d440c2c0070a9101501c41e907c225411002c948100d010000e040d0ba0260054400c481c0107a880002e15181d004044525115100807210990b2112143d840002c0041d402140d0000d85c403c10368456002550320308041c2c42524002110181c0c03030720410300c18000c101d001c02d210181648001c0054910705228000c01070402011020030510f00541c0d198031900034012402156802002c180c4c166840d8050029070000641d00c800004c1c541d00c4020034118202d107101c10000d030304010b01c50700305841d0108201e0600414403102d07041617101095080000034400958014000c00b1000d80308540c1800340d2180ea40b954 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 817446043 1106 817444937 817444963
    0x1e090b3303040f0618080901050f0f1201080c1c0204051b03010815130b0a050c09030a060509011b0912020102011d1c022d0c1c05 57
    0xd201c1c04031150744c440c03103007000002403016400039288040c60740100b8144007000f5070b601560252001c3c007000340c99507880624141281101c03000a4001070104289842c02e00f00501540500b4032412440032810307a4940300d65044212440c00c1d000c18088003a020b9031343e40020842c42c038a03400d58030308d614010300e0400d9aa96541c507501507407030f2425002c00300c0302e1103080003041c80b10780028101109990407800e104459112078503484010304002e45000e500716003c01114000d44c405000c0816a58050480001ca42c50306407051401c0d41c241c4005c040300300c0110080fa482e031300d420414020a644404c01084003000441c40141e0040c0302c140c07109001321190710070044002000040107691a00c44203400c001401c2507520030703681e40c180a04400c04001c01030014025000d0445001c051425400c4102c1d80150b02c440041211010210100c42e001d4a80c48107113000d101003000045c099044c = true := by decide +kernel

theorem cover : BRFrame.Cov 817266187 817446043 := by
  have h0 := BRFrame.cov_init 817266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 817266187 ≤ n) (h2 : n < 817446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
