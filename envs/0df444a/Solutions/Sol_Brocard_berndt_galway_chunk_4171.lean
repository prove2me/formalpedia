-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4171
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:46:21.005433+00:00
-- url     : https://prove2.me/submissions/5967913a-ca80-42e1-bf5f-2c0531dfab35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 750000000 ≤ n < 750179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 750001250 1250 750000000 750000007
    0x114090409020102031e040f050f031e0c09090303090c0604030c0605090402040801090b0105030c032b0c0c141005030c030406050a1b030212060109030201050d1e020a180821 76
    0xb564070810a0b07402d07454001c400e4202d515004044290940c0244c411541c0c1100d081d0360108007410303d050b00c0b00e000700c0d0160082c0071041610030300181c88904410b1100c050b01ca109161103039a540c141a00e402000c2c540c000c0e41c2c0c0c0f410801c003c281011440340040f80242c0e010001040000c203410350340012600f1a02e01103480d0300072840020041d10569100120710760a14081100340300040355942c1c100c410850031030f0598006041456210541c6041904d682950001e0540d1606640c40943c00c410f0be041c41c0c0143c881130180d07200349880d9101d070000480c01b2484c0d1030f414840c2c1800043c1d10301344100e90408509600e00010201c2c000d110061006081c0d45e100e201040050031280c01150440354244801c0700b203803c51020007030094016040c01c0d038441c880d610204060707500880c2081c054a4040e9512440d0590100d001405004811103c108801600c0c10040c60041d803807010306010621991148100082d00040948482c425001526650402c1c3d2240915000041c5440319140002061544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 750002500 1250 750001250 750001253
    0x30402031005190f0f05071e111006060c0b1f05131d03090118030203070608090316120f03060609060c0203010b09250206071418130204140114090409 66
    0x80c203190707515043c0c2c0054145402c0703c0300c09000e0340102d515a0001d036001c101d180c4d1800004c03210305849013650302c82422100358207528103106050001c4c070607018900706c078030803c0150900b5040310036942c0180005290340c0308160812400f503410031303040560346101ca041108005d0b8020240390341441610700c1044600c426459044103900409005401d1240c1c02c030031240c9001205482ea4083e000040c001880b4083c101240c2c409906a203090341d802a00414001f0306110301580e9000c0050001903da1000707101d100f81458002140381c811030722407a928072400c4107620000e4401174500315100c09050600c001846056803100b60f01c0104c1d130342850700d04480e10290011070300405800e803825030401c011804214000f80c0203084a00020103d81071a400351032000000c90b03e426080d81d0920003d102601c0c5400740d030b8517801c00f414040c0186800500103025030b600042034814040e8a80307500d1a00424100000c4007180c070604002642130070028034030025034040a03450f100300420385100b140e0301c108400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 750003750 1250 750002500 750002521
    0x30a0818010608030c070f0f0302151603020c09060108090606100c21020d020a0f0803060f040203040311070f030c0306150b1308010606050703050d09151107060c0203030402031005 79
    0x110040346400801026440e210900d8407903100c1d2901ca035140c407650200040c40104495907130111840050004109400c1d5400c10000090110341801c9010003400f42c4606104041102e02480380300390001c0c070440c100320702480040310000703140b81d041c40f0400d400c000c000040814080d40c000001c550191011107a0903060304d01c542c0341c442c00741154100c040101d4140403003130450308401403aa0200c0d8540841944100e81e900b0b0001401851002c03850448000070301600d01454004100802c0c0d50845418075011504130f0300f00302d40940c000f90828400c602001410711095025110b401c5010056138255103c550a90300f0a1000428869482400f800107030f101c201c2c988060300000d01104c1d6505007031404a4502d900e5400395201c50352820000140c101d004500311074410340d142d112141031500180301d010041c10031030f00503607a01020b12014102003240c4d01c6028010b042d804042c40c3c44480d682090360458005500c01000d55000308141f01c05668000b07074807600781d0301c103000216666440f2403003c1d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 750005000 1250 750003750 750003781
    0x100c051c0905031606091202040b04020d02120c0327030d0501180f020a09050607170d020c010b030a0f0807030216030c14220216150204050a09090302030a08 69
    0x20000601006a0105141e501c0030940741114001c9080f42c2c0342400a180403102660144220004a0080c40c420810100f0201000f040c003030000b0703c002862070321440810300340c2e40502944030381c10703074000b40303a503003d40d180211141c22103240c0309520300310b00e05031800040e034220f41c07007011022821010368501c1942c0c0420880d000000c8042c4140304c40d507900c04406040034815014001e505080600075188101c1a109a0760140c8507079a030030710030620740f43c03d0001650003240c1c02c0e124080c1600c03580702c420188400600490b11488801613072440d4150b01070b400c55840103025842070300211020000702e4041c2c0300303425019401c01629580c2d03005070f15041e450102500c100d691010420580001480042601036080f2020180c00004e0041c0540030840042e0a4241c965900c0c42d542c1b960111510142e809030003a2030507002c07100480c0c00780c0d840f000c54490320b400001e0045900090244440d09280411100800c41c10b002448003012581d030180d140e002d100900010002c07805e002440280e00701c20079 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 750006250 1250 750005000 750005023
    0xc032304050a15081311060f22140906090403050c072403050a0b0117090c0904060c0306080718022107020c0901062f0f0d0c020f01030506100c05 64
    0x1000c1042e59160b4030114030b003841181680c0460701e21030026000d00d001d1003400e2070407030303015980001511429003007140e6500f2100d1011700c6240284122070758041100000d04500707004a1400600c01c0ca000b049030050003000c0030640c0201c50b0002440301540700c40901d550400d0b0705003447c9490f2414a5121850654541d01c03034070002210800c6911480c0e0040c0b056400c01307406036414002e0740e41e800004015240e2407900746000440c0c007515a204043c420742c0d40d13500160707224281c80000d4442e00c009888500f0a407002d5494940e0f558070b150f10705426110710030061a801d0080c000740740c94041c5240e107881d562080c01c4d290980001c1c01120000d003d121a00001034903404650781820810070003503441c21010000d030f01800d084400407070300d240501e209070502c20f0f640c001e541030a4507000c122802c004249800030b655108000d10074615840501240038003800640c0d420808116a0040013502040c1380030140c1454a404107000c86030301c5611080b8240415810000d103440f4040c40c080c3c0c41d0002d038417030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 750007500 1250 750006250 750006259
    0x2030c07020d0818043b12041502070b070807020a0f0905060301050a18030507051c210b0a030201081f09140c0a08040f0c0905010311100c03230405 65
    0x15140100000c2d41c01900014641308412021190b0207030900c0201d59000d1042c500708805080d007001840800d681755040300c00c080c1d48a031a52100c50000501d80301a215606525070720216081c00b450b510203030003803c040b8030742c03004140b0b0b18500170f500e120305c0c812000041d00603140011340071b0564444200600003800004407200d100c950b0f5225400090805645240c4030707508040200303c1264080c00382c85818500101c900b150403150390780982d01540842001c40e16405400d0b0702c400c40b040c007000c940003017442d16250705d541801c1010094040ca11403000c9601d0340c91a1a40518440d20349070814003d4940c20308003855107451341d0f00b03156803400e5020003452504451000101c0c101d206a00007522203904242e4280280d110455854840d0140c2c143d510002411a00000c002c1010385411103100790050b140a0030094407a402002503072800d810645111803041441c01241c00c0c4020340341540c40e51440d00303000c3c000072640d0042c401c07200303a8900d40c200540c1c1042804594690011203005010080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 750008750 1250 750007500 750007519
    0x3050c100f0c0e130f0b04090b0f13051f021b0d030b1c020402031b0309160e060a0e0601030b1809071d162c030c030a03021002030c0702 60
    0x211031009841d40700350301d106450920208503001400f40c946921446801482085841111000a0300800c40ca0945801d05910307080300c8420340e2524403031402004d006807032421962510703151031315201078042d14003030200202080d6540419800b1603d0800c2041030f00603802000808040342c0040d0040c46000010711441079402500340b02c00103034001c042c0b421500c1c180119054041003009940052181c80c030280101c640c06030061410341d005591218184069011070060440c00c4142e07500119445545503100e400c00ca49908415440c400c000c1015511007106d600d800c1000c40c50020180c49040f41000400d0041002607010780c225444800c0007500e52002105c202e00100c40000c800c3c0c0d4106c490380103030840464200302c0204840e2007400d001d0501c0708152141c510205036184c880c6400000c01400804c440c07204580181d0070700c01c0403000d99a0703c180200f040100342c10803030410b040c40d100798000701c85480040e40110f008580c81d202c1d642c0058807a6510012000d0b1403045590003948480c20b82c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 750010000 1250 750008750 750008773
    0x81b060304065022080a11120c100b030f030c0307060f060b041e26011419050411280f1a09010c080a20070e010303080403050c 56
    0x40070040090b070980c59115202e154082498425415009082c102101200e0028002000701c400082459440e0402c01c0840e07a0315172514002c58100c2a5440300145a02040c0800d40c0c0003040560b81c004408803200c1e1400700004040c66452000140c446441da0f1a414400400d6905011580e09080c0c040d054990306d003100791060307440b544030319011500186800c00782000b4002d680304d81020f481d03205010710300d820b0070146100306078481d0003090b05460100c51004900c0c0c106a1050002e51801001d0b81060346202c0803055003960344404112034110b400d14200542079840480030b03610000c40000c005903540303a40c14621240301c24404079540040c400181c01114000201d101c660808107401102443d640328022034100154030701c12001c3e46401c00c00c4804c0c44406800040141c000b0506188851000b150b40c0c14500b41c001d0382c0007a01183e88904408016103450400b4640c658016000c2c00501c0c0c100b0005d2000c900040c0000b804100102e1300003400c0500030700444482c2d000c0501161140c1685 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 750011250 1250 750010000 750010061
    0x108100f06030b041803020613050c060706020901020c0d0c0b0a1209080a0f1704030807030b0409050f100506031b03030c0102040e1b0a0905121f0f06081b06030406 72
    0x3c400500451814104080e00d0300300021121515038164040e141903218010741c443c41c429145010b54250045c0c442c0d4030388941c1c6104c02400c0d964420403025071034010349800642000d801104060003a044203a4540000d07840c042100305481e0308116990f1503015540080365080c2d44062920180e518101500c001e00c407030f54018241d9228142e0740d0500f500c0742c072482260344c14007100d0030100d1a00001c000c180002d018842d443c0d8013540518001440076810000201a50b140800680b19038001c070308049441c0105010030310628035002014440780c280707400420382d1040390680f40c080700c0110114085d8982d40500c202c03071921790800b0095464a0705d920900c80c0c80001540c003244014004901c405441c645003099400c130721310035120342c0d003600c2c51f090a111445000768450840c40c0207d40d40f401c0c0100312080254100b070034098001801d180c40889a03000c488560700700021551114000b044810700404400c0d0280409440c0c550310303038845151a0015009046110b4039001281c1c2800200c1c0d4507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 750012500 1250 750011250 750011261
    0x1d010f09021f05030c0702010e0603241203040302040f0908041509052704020f0d0b0121020901030305090d08070503120a020406091e1707060201060b040608060108100f0603 76
    0x21591100e0b4203140c0312450202c05052642c042c0812403d00000f000d420700f4502400d1810700606100c0f016101c94030000d11a80d200300e42207103042100c104407980304003004040c0a0300c0c01042d240e1b90b00c040520080c895070381c02240300080c85951101d036182202121500300c07400d5158002c003c1d60f00c8507220800e0785c4100c2000c012400000b040654001a545003008841c420050560082940c100e0710740281075202900030404d0f40c01c03071014040c0e03d60941b0b40c60a06405940200305189841d41070001c5813060305000000c410802602981030780c003580d030b2a070f41181180d50604201c0e9a400e903000100e100c1071103c1c2405081448046000c006000300800104551303031f030002c00c5080d590f03541c0440704102c1c010b0703019140014900f11814040c81226400d200800d01a200c85607031180d0380d848107503401000e40b10020145070818002006240e409001e4840030346801142c0f94102410070200402080004040904001108010440c10342c9260780140c00351441090304040240c071150080e02a10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 750013750 1250 750012500 750012503
    0x4110d05060d0b0a052a090a0803070b16020f03180103290d06090b09010b010f02010603030f0c03170907060e0a0b162a0e0a1e1d010f09 60
    0x40c2008001000752030001d60564140398004030841e21611071071008002480c00070a20b1410b01d11652140012200891074212800e03141044a683c5a2409051100d4980240d00c140d006500070f0000600084080124503800402968607691555180340d0483ca004160202c148413030100080e00e10880389074503104452400b0a0300c0c14840403100d041e907041c003803010303411401560f10003211400c0345241c800c4000a1460240902156003079480d220040f0980c82940c040155a55444409039596003041c00d44220041c180000c0100745e01c1c40e01d01812664032003800c5420070070b0028848041500460303080880178201d8a50004519041910554603480340c060b21000c107400c403d090880c2e24202051405036044191041d00301f0410350030825104259000031100c2c542101e100055a90b500410710035120070304030701c90000c14541000c10303003c0032001c0c0070341c28801c1c1444a1030018203004428100d2070301114100190500800c00e4408208000410860700d47d420000710024210b10758103e211585e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 750015000 1250 750013750 750013777
    0x305010606030b03030315060a0921060e0d050703081b0c0f1c02070302060313150b09060d0203190312110d11070b0109090501090204020f12011a270411 67
    0x3503c54904043c0c1e00d0204480207503032240c00d11091000c1d801d1035000391116203480d0070103610b4180c42e05103081d0301e4002070510501d08070703a00d506001801070314020400d07424058006084c0d14450000000c1040c4111180601404010008101e14065400000c801d980c00303c4c84058442100b48465078aa042e513001014061140c081d20b040109921080740c0c002044980040103018915424813101d600018a038400500803101440040350000007280015140c45100140091040081000420b8050304541c01480814100e42c01a03c0004564a143d00340c01c3c0d9aa00e4001a86000c0b240c01c800642e40c01c0c0c009041001f401c00114100000c0e003010307082601c09200c400c902516280c028001c2150180c84405d07100010461600e15034400400f0300d000301c00214001a180e00418280e911507919440d0340e01000610714406c800c4600024050158000401000360a48143c80d589000d020840c420080060340c50054002511032586054400900f081c041c0c1103140c0d400e408030742c1205803201c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 750016250 1250 750015000 750015011
    0x70813050a0f030b130807140d08130b0a0e0d02010c020613050712050109051603030e091005060d0615081f050907030b010c0501060306050603240f04030c0c030501060603 75
    0xc80c9441d801480a40e0089420a441140385071600107201e40043c0400c10407107210210540821203600083c1000742c0541080c03003417020340154042ca03103020f1140e0501040014024408000c4a0b00c480310070b0250880580442d540301d21071000001c022503040c4c1c0c4d5551151900010810350103400c94061340e5003a8080d2082c41c0e82c1d40304001d012002c26100180345402080041c03094407200c0e604240305901480001510604980c0c80c0d41c070740f50742c2200880d1103080b0102c00b001010307841103510f001c045c0c0c192031551803410300861000103018a4002c0620807034000c200c1d804050160392021009086070480c8080d01c0181c0040900182c8081ea60090380f8000a010f540c03840658108100c210348002d49101c0c0b0641d540b01e821002014004482c9041110034072004000c500c0034010803010718011003001a0074244034080520b040044005682142100c510034902c03003022101d000d030300020325900c940003070761070340381c01c5400520050004002c124440c001105104c0150300c040142d51310354904010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 750017500 1250 750016250 750016259
    0x604180516090b18090f070617070203210a0f060f080d021b060d021b1c0f021f060b070803040c060e1f030b060a0c15020a051603090308070813 63
    0xd5524140c000c039042a44001400c882c101d5903489194000b000009841010018071b04c0d179810161554030640c002515084202400e4542001458004d8214001540b03058400e407807604410600000749146040001d0000c1c08005443e04480324250099100b0880309894a902d503124580f140106e140d6449840d08207801c06000051045000c401c2c1400d44d03001d003002100700026a4803180c01e4405046d024003801e0b4072400c0480305031105252460191107585400a80b0b44c0c40595645000010407a07606030011138079402040d1041c0303441e00030b4503105203007401e074181d00d02400482d031004007007072030001d415418404245d02650043e03220380c0f0342c440f52594805084403540b80f1640c41e103500c49450b00c04116640304c0080d40351480180c5060202e50642d88100055440d0080c6071840c000c111140613510411825142c055428001d200c400c6050401c0440300410500918101e455101e0b060001102414041c40d4008011070344802680d0380c0e9041440c102041d030300042c01c255040c4248050208 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 750018750 1250 750017500 750017519
    0xf1e1c080d0f02120103080d020906161703010b040605210f071b0c06051606240b0a0e010f0c0f08190306271401030c081002031006080604180516 64
    0x24101c4110044e020f1850b4259124640740b030f0b200448800c0c22a03401c2024525945400029190340c1500701d585c102d1b116082d0070000400c1141e400e03040c0c1407000410040c041025100e05981c10b82d400d901e0403d40f51801000110700180c20795a080c07194400d00b4042100c1103009589803441441d5650703403501000091158202607031207450004149d814504000c0c03002d10300c40c402820108101d070b00303d0010181c0c01d448000840c0c6161141d000c4070a600b0072401e40c8106da2402510081c8000c15038640b8103d44054000c1c540b82c40c1c80c031020b04210b216075420b18041d1007602140764072500f041014400450502d0040782640c00b0507140c042800006c0c0d01000c03224000e100e0705040383c00d803001c04c0c5640941907001c0440e08080d1556040580c0c0d94070280c4209401150400c0e002e140b0175160801e1190a2902687c81d14440d8482518058010010010010310049000301152128240700000e52660400240500400070004181140201e10f0006101c8005410b00c400c3d01c028070701170304482d21103a40c3e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 750020000 1250 750018750 750018757
    0xa090e0d1107080705040b180411040b0d0507030305210709050f0108060d060f110403060506040e06070c030305041a04030c15090201090e15180907050f1e1c080d0f02 73
    0x200305604400020002400c064201f00031000004010f07401c8402140821206200180c80540304440d508241d0003140c1070a120300800076000311580004034001d956440d0303030b031034050000400f04017010418040e403e80c151407130035502002e54581c1d105403501000003060070050344200e6104464142c800e240c594000c6071414040e10000e08403840181003911850098625100000c0c00c4658545d121804c0011800141000c2c51050304045140d0034400308120650381c03115070302d50309a004501449203a076009030b02031403901d516087c0407a145e51542810205105544911400340428004220405900c1010409401d01c40c01103991800d48505560086680540703000780410071690003071111400c0c50b041c0c2d55001501d01c09a0000d44012408291900b292090b43e00c0c01a03ca20244440f807807013031160601600064400302c01d440e040340d00040b100308244405103603040e181c040145c01c6803200e881074030030b040312100c81480140041c5003007519a489901c2c9403010511704103001c05d002e603da0084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 750021250 1250 750020000 750020009
    0x1005090103150903051908010f0905161b0f0305030402040606020d0903020f04060807060908190201450611012f0913050103030305070e1e0a090e0d1107 67
    0x41110890034401402400000f03401d0301407200a01c8030b03030480c500900e504242d800c800d40c2e030840c86500d09103241e5004012074010201080c10201003141070501025245006902450440d040000344188101d003162030aa0150164600101e40002d0542100003940110702c02c1e1404c11045076203160481e12071070045101800542224810000352511440400e580c0300003c20010313a255684008501e0098030740d001c403000c154001d0040003611400d01c01d0a4075075000c0c240d01c1c0040c0c1c203035600082c601e00301302d540c1201412805112078014004500300005128400c08009821001100b20403250417813440f44800140d07106481045040d010301811102c5841ca2070210903c011b50000c00c00d0982c0300003610f80c072189050048041039940c40e8204480c05540e04000039155041d0300f402403d60784001c055000340200e11510b00429140c1221400064a01010b01c200d19500d0100103001d415040e4400c0780321310b04010904074204408290001d001e802ca4807116440301c0c5202d00c0640703683c0d00c0d02c40e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 750022500 1250 750021250 750021263
    0x8070806010806061c02040f0f2c04050313260a0f080703110610051c020901030b060301090f05030a03150803030115050d14010609140d06021b06010e1005090103 71
    0x400c00e0f6090034409485c040b46400035410b862415050340c2000c83e00682c1c400180748488403800c01612002084070400360016400807129601c10000c0001c4206500040d04c428440ca000018140541801612050407c00f00b000001d00d0ba11100b50307602d03071802c89807000c00c400d81c01a1013680c0b41c400a00d400030141d01482e20480c00034191500d85542d00400f00a40034000c52812041c1c201009101c3c8034403629980c0b4810b1212410302c400e000d160f0302d0640010000c0c03034034448210090380c0d40c0e56015044a41c0558010496555600420f0140c5070407100107003401c00381550710040100c00300240c605102e043c0d40800c040702c1500c0c0008290b10321032180345e005400410042c46910941614200166450304110345013000c0b8010300d00454000c030b6004d403900b4005900511101d81c2c0004950020204200c1c0c0b151700720040740025552905032400201020b82c001020b442c0c44425103071454500319001e0545a09603504e14450610034011a00440c41c000103107408951403030280d01c13044c1640d401c0306 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 750023750 1250 750022500 750022517
    0x10303030609020405091f030b0c040914060d02040c021011090312040e041407181a0103150e13080c07030510020a0f11070b04062316020603041e0f02010807080601 72
    0x644d9000040d0b1281c1c81c050b0401f0458202201040781c1d16a82802034032540c1c00700c3e5846180001ca0307812528200000984000000c0601c5140d82d1144070b9200810380480e00040c6240c0c0e0000d05074a4080c42c0801c00c00100d0401030071091810061001e0080964150162055207280044003d5144a1405100402007007800450041807001c41502e00400c1e108040f1402c071a01c42d4010b4200d42c1d8461054141c440e160010000780e0038015449a00c80d00c401c4c2024448003a010b050a0302c0508980211020003000100003207011a42d840000c0c2d849070403081140d07a441719180d401d900c0314824001a03a40d803080302c03c0040704040d14802c40e4450140b560f2805200314850004603501a10006921120700c250800401c11180c407000400c002c1851340c0321451641801d9140d01c24102c080080d804240c0310238401304589040913412011003d5040321510350302da89501c2e19880040d00071006146061403084900700304800408440302d168000d894600280e50303070440441d0000c2c012a5960700081111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 750025000 1250 750023750 750023761
    0x3010e0619060b04030f110d050613050118210815060903150708061e090c1e0f040303090b031512030909160e06030c090d0312090b01030303060902040509 68
    0x284600d01c1c0e95003100004206075943d541d041103650025002a104081104035910030403000c41c1d240c08001c0003d4441040c04070843d114181c4400000b4410740c0d0a5800c004660100007085d442288040380402910400d056030341072008451803080c42e100b00d88003550042c02070440c021040c1d40d1041030302944008141011205000a5410039a20690148180c403030401f444400c8003510f038850b8000742e462180501c2c1c01400c21200141d43c1070000b06140c1a014861440d03101c003c40e19a00071101c00000383d6034200e01172501c01c8400c0400d15404c1414020440a01021406000340101c90081d0b4403002442d0300c13000c03442094441a10103402c0c0725150750111100d0304003040711b03030000d40711801a00e08104c5110080b40c4000422965407201d10090100d01900d00e40010051030f881000ba6001d134214900099402940d100b8110700a1040320300342503401c20144a2800120000003980d81880100f4851808400305c540c280811004a428400d0100c1c50382c0c03082c8256011580d008040c1e190170340300d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 750026250 1250 750025000 750025021
    0x1110f04050f18130506060604030b040b040f021507170405100305060321040306050a0e031b0307060903121b14130b030414010b1e21120408070503010e06 68
    0x8000e48150801500c100d004843eaa00c0f003412841604408400f5552490916080313080410081a41d84903400c140410700c0441c05021000341d02c1a400154580c03152940c0c00c02e09110101407900079885140341c0780710340c3d11610303003c0175041403445440e504005002907030320307a80d40303010302c3c0551740d00124101c0c070307000200d0310940145030412000380580b00d000d0b00700081e8401e05401040c0f02e007000c540c00101003003040031fa0710880da0f2181c00301904002c004040d20350351fa100c1c40b402c10310390b0b01d4582c01040300000d400140121969a0752081c0e04018014481c5406450039600030505e0609501c7d285a910300f86600c4100b0300184100d81d5500c2540441d044d1105069400040808202c9a41c03030801003808040c3e0401140124021054031f4440c0e10102c0c00182036540d43d031000c501070642c40c1c020018490010f00e00c2e121204085400702c01240490b08014107103218656140c0c0184039444000c00d00c0d10b103a000500c290341f04a0706840c11140c560741070500b42d0384c5808100300c0350340c02400003c01e460752 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 750027500 1250 750026250 750026269
    0x605011403041103102007031e11010213060e0a05010f030e0f010c090f091b03020d0b03010c030b0102070b0c0601120f0f060f0617060f1801060b07020301110f0405 72
    0x210b42c00d10f80c0105460004240f803d40c4032014104244d42d640c41c00c106805001310301c00c801e00990711815103490455940102300030901e840041d084103802c40c02080d0b03180550084140526040000c540394000881038416601d1684100c42c045501490000c15038240f11050209481040c2c40300c007a17074400454204d004000e51042010640601030f000310b8800001c0c002d511510f47d182d078a407040c0c00d042c4a1050742103d402d5100b407a070b03e860b0950310024441550300d80c1c1401c0281d0b040040e128948100e039007000e82101c468180d4554a0217031a90780041e010f602001702a07000b81d0031034540a480e10307614601807142c000c904065600c0040100510029560a0700d0b84078486c01c1c0504003920140e0350060b04001f07101007261065260070180a010960b8480e07800240f044101d103c150480d01e983c03d903100c440103050340d1810101000020111004640146105805030008200c0d85903124110304203a04030071401c0b031195080403030140c403900d844401c2e29030405c0034001441c9040e00d8501041041c82c1c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 750028750 1250 750027500 750027503
    0x4080a11030d1b020f070605031005060309060126060103060b01020703170c01150e0708100b0a050306030d090501171b0c0c040c11100207060204080f0f01050604060501140304 77
    0x2110340d1000d00c10014009030216241042012480d00803000c5400121020910203000f1584810114070805170001170410807030301d140c149a55682c9402c071403034941840e01e030419900000c0003c180300354010002101c0d4120381281e2070541070200e800c07280c00c605414400646455074490f20050021a900d940891940481401240d000707990b6a601e803945203540031034828101c100480d1000d01c1450a010b68414902500e81c0450030908142d20341021a03005413100701049440b50001d0710100c0b8000081002e04803070702405407542c500c92340040541e030048659a000e40178000c0e0b000d1100e8080c1c0114019514161600ea00500d940c48200580482c002d103800c3c480e0b90100000c51000d20744d00010030642c43e911000d420044060001d00c4282c9045107100c104118200e21140d201d4000032420303060f100c040c6500941d941109044c030344064080d5400401140c000e03114845203500c07000851a4500d80420020b0050303603146410001114814891107000c6032481000c1a088008a4029680a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 750030000 1250 750028750 750028757
    0x60f050403151823070b07080306030111041206140112120c020a060c0b0f0c090409030201020705030c01141f030308090f1b120715030b03150a0603020a0602031204080a 74
    0x598892403940321424000310a640480071240c0c56804a010710400004c0c800e500b07401020490716042c21115544620302c0d01411103100400414002c2d0740070342140000703d4881d61280d4481d900d0f45030800c012040f1100c1224082e1400e0303404800180d118648904844c501c003114440007a59031030381381210701082e1544040003000d0503400c006070340d0f40d41c0010140003250345280e01100f05103401360503e40b01a141a404840010070001a02041004c494550b070302590049071400f458a4140d0184c0502c0b04010041d00012a401040c890154022000810300c50b40421880c0c60361300c800041940c0c408100c440709080c1c19030505c0030074000c000061b00038400c08100c0f00003444681d411408c01d4198800e000316214009251a0103140a1541d080c0001c05480984452854818800325000e825500c11041c5502c462420314144d40a116501344002550000c0120380b801036a110000c09260100324806c1c40c1038200854060b10000680b09a0b5110050460b6144c80b2501c401110750003441102040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 750031250 1250 750030000 750030011
    0x12032a0f090f2907080306090f0f040303150e0a0522050703020d080d020c010504110303122212020715030b031f02091e040507031b141207020a050106060f05040315 72
    0x282c40240a058005c11040d43c0346e040441c204003180c0703070190440e59039600360428041d50550103403030160802e41c035081c00100e1a400c50107001c00c022280e48561214516001001220703e0242c011600c00c01041c1c9244240341e460b86000400c1e10701c0d040300541954000c260910041c00c200f001a0610f9026902440c2807012110711441640d01c0781c0103528481e5121014002003191882c001182100c0440155003806020b15002c420644000e0908111060011120500010030050311038002e400c500340b07801c00224400c1c0656074000c0341c450390442015810601c107655209109000d10b001d80240908000301d00021482c904201810880d22817581c00c0041a02c1c27a035036102000352303000c4606038103402c1c0d00c8660100021210010900000d05040000700d25035480240e41c1c1443e01a01400c107003030801000344202c0c603540103482c1d101044a40c010248002c00703070000342c9410b11034490700003400b4550300c03040d0072074806192072260804030780c081c0005e1002446c0070b584e0703444216101200080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 750032500 1250 750031250 750031319
    0xb19090519091a06040209060d18050d020a0507052b0302070b0c07050f091b161b081b030705121203010608100e01050303030412032a0f090f 62
    0x715105100110f50110003034107401d2421030040315041d07011000311070841c207044422010840c83c0c8a00310004507003641d00d40410380e64200381080c0c840c2c9250030008842049a140102a644080003603080d0741c24403070f0040024603454440400303251000f0407207003031a0220f1200f46500410488040840c21360261401c007080000c65131000d04405410074004200551a1200344048098040c980d28002c0c0c40700010040c0302403002e11b00d41c0d00202030380115691201621074405c1702e00c0b1a401e0051203401100c9a80b0b0755291343d41c48410648444005603110400e103c200e51034003a101982c1c0039055008410100500c2c601807140402811085c01a103c2030f004a180e000b8156000b40c00140115880ea8144005805000c502c3c001030094801c5984075541403000099590000800c0200090103001049400d80d22030f420000409044111400444480a854048008020111900203818101c84000a0344100d41420495821135440b500781e609100100e5109000d6550000030b1265520b070b80e10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 750033750 1250 750032500 750032551
    0x6090f151b081e070f0306060311160212070905071205060a1a040812030703060509040c0b03040f0212010e1c050d020705010615020f010507260402010e1305010503010b190905 77
    0x181308080b1940c580d4401a00c40002404481060300b10100b0580340c88011140703106000c00304c2e415580324808403052503060384005407104d591180c550390940100580010003200303640015001c0c07035007901d919410310b00703200c5100704659080340d807a5480644607408210351760070015900011070102d08010314040d203c594891030614a40c130102c030610b50000c20020080c1d8144561400b4050844000040f82800c0d282d0700c1e0941d00d0f0b070140041443d4000302145c2089041c5c0603541c01c455005d4412002c010081840314000c1099002ca40000d0207601982e801c0510f006201020441c616264541440c2010700012300030b4200201c1110150341e1484007003a28030f01802e1807010142c10394006d00c03e06024669003030030b4817000b1f40180f080c0410b010740d24200b210000c2805540c0c141d140076602c0c166665000403191b4122000c543c039041042c80d40c24041c030300e0703084e000701e4143c5505500903c180d003c1d5509005615546264465540725041f0b0244509070300ca811042c1c02c100b03075003c20076409405400f40b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 750035000 1250 750033750 750033811
    0x106030506190e030301090c050421032a061d1f06060822030309020415090b033909070c1101020c0a090207060906090f151b08 56
    0x2a40c0c164820780c104201810501111081246014014090b00343c4040405070b490006000b0b90321b185072540c0140c06580d11860944004128400c80c0e1041d104400140002c020b09403074055000948000b000c029011042c032607108040003100b68480c11150945921009001c4005c81c44d01d01c0d4943d611307100880741c0411180c05100d581102c0d040100ca60141c2010444140c2d42c8200140660a070070080c00e2500040042c401d001d0701c48000607044880c5c901100103040c02c6000030340c0725151100e048804d940e0398148038140c46041c4010401c140c141c0042540c1c420b03178843c4115901e001004210210b01c0d9880504401e0706072702c40380b03011502c0920b0004224000403a800000603031201e5020013440454250242218000e0026050314020400402d060340c80600500380040e800280080c10001e4039401140c0f500d030000c10130030014045207800303600c40c8240302033500d0b4a206c1150341481002d26114450000c00d08104c5400c400400c800151102080204100300180003000007803144041035400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 750036250 1250 750035000 750035003
    0x210a1b0909230f011e0806010b09060d0c020706020d021b19030b0a0203041101030e120c030f04080304080d0504180b010306052e0509091512071d0f04020303180111010603 75
    0x1d00701c3e660414007007810401d04155580101036034910100303c0101e02007102811350344e9110f0016601d00030000802e000c1d03c40c00f58205c004915101c07403296101e80c0403c03a081903d08075030a844000c2d183c1075040740d03504010384200e21061000b40b030075501460718084012740900701003c6c843c101641c9456030944001e044911040b01c07600081080700304204641d401d10100800d0900708900c10708490b0840e59904190317100085071500158072011910b041064460400c85100c030701e07a40c0c40c0c03102420340d120b810500c19030352244680303040c2d1511030740510207642c15514007041c500300c240c0b40f0300303407000280c01800f0f680e030706040d51100c000c203081d1164124141c400c008081200114803250100e8001a00d0036241101008010b0125215642d900300055800c404e4036050819003056020000700b00026000c03003c03066109000c0000fa5888100d0700800300c107459001c51000d030359541140080803c40c215030096058204100a4440382c4104e0150100b480c0c0600d40358441d52000d21084d4210741c40b5410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 750037500 1250 750036250 750036271
    0xd091403070c091506021504050304170705130e12090f1008061f0c0b061c0f0b0c0a090b0304030c080f0d0501050d02100f05210a1b090923 61
    0x5051240c0c0f1802e0041c0d00d4211140007141e103c1d035107000c030000e4580c240240e600c80500382c80300c0800c1c1030220030816500504100300300d4902c412030031400c1a503140094440d0303a00030646076100c41c032040d00c0c070311561250080d15000b40140c00340b1a40c440100d80e01011201d41e1101c0030159040c11502c0d17000b8088840481e40d12241c040d81400820003100142c44c520f954588060044070201c8168403100300807084d076011b00c0d0200d0729114040020250014581c000b100480061450030a00c8640d84044e04c6480c000c04c03c8440c10f84508070304110a00c9080c085e00c000c1405828100301c2840d40c01c0c000c40d4094068642889010280e80d17860030658002100300c8103044001c18607041079a044e105140c01000c045400301d1002c1b203e0390208413503030a20340d4031209000010030a114002d00800444807881d4101c0c642c4203054101000901c039004080c0d4007030041c207150500803100304121603d60030b841181515561000342c50501844082c11008030f005400529801c40e111003c1c0c131402540e4084c503442403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 750038750 1250 750037500 750037523
    0x9231c0c02131a040207080403060c050901090e0c0f0d2903121c020c03210411030c0108010b0f0f0d051501210b040e0604030e0a080f030d09140307 65
    0x100844010803198407414076282038109201ca100c40c49030f80c00407000c15203000d40c840320141000c3c0c01c1400356903c060030090401c0020181c556200c8001e04580c0d001b40c84100b40151102c208150544e0b04546203140e07a0b100700300c00c80c070f909100302c05071250301c01c44400840d40301d044c4000100e0394400489140441c2d80c00d036000381c1040c6014071030001a44024003020307041642400c40d54101d003544003c20302c1019030024501803c00010701c1200d2a105d0100c800c102e01c0500b41c03188008001040310250f503a4002c4070b10010b2340d407402081c07185806505070340d4000240d0901d5041c6c481d86d8000c0100341400d80c3d08100c2929015050350190442000c2000000fa56141003a09014500150307842c3c01e042203403000b9000031006040f450441a1304100b84000341814181707020900a04068071141c2d9503115a10070841051b034000701c0321031001016502c00680940c2c2d032a10300e076915054950708409070010303c81403031005496400246017a0050440500b8008014002400c5030301601c806ea6680c1c4610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 750040000 1250 750038750 750038753
    0x315050c2a0f0102130b091c0f020907140d0b040617060f060402040302030a0602030a0f06080f0f06060d030e0d02180a060b0a08010e450109231c0c 65
    0x1440050b0440310520000d41ca0302c0c16007042c0a907015018010b1801481000c10840595114194400107035a6110f12034050003009003840110116141402c030322510441000644840c42100000200701003940814101082c4038040000b4028404500f0b420030303a02c0800140e02201c140f01d1550101100d03001d480d00307041407017240071480802846980510300412080006840014400a14076003003035005072a0303100c2445410141000c0f100884605041c90004240c2100100319aa00d498441003181e0098800d200240d0300c0d100108c1c0c0b03c50380f100380780350144c0c0401d0059101da000094010200c00c50030034540d0000f0b2405100348151152080070804001c03103440c00b40300c1d0b80b0240030400f800c0d908146580100904001050241405514801010a0f107a0107641130045a90fa04d0400003000000050720f1031007082039400440c04212000100840d8920301881801c1d806504035000401d07040c0390250005040000d40001c203024403490522040c000004001d210041d140703607580c3e10388200319 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 750041250 1250 750040000 750040003
    0xa1e03020f070506070f0501020409051008010506101b0305040b070c0510050c06012633010f03030806060c0102070501060312050a020607030b0303090909071d010315050c2a 76
    0x800c480703600121061009913a940306440c222a4418040d040c504400d103070590180c040d96210451060030141481049805c5480c441c060707618120003003110391f03504130400c8007107920f100026012894420807555462007042110708075900038113115203455a620203000c840d0b48120000e8540c6614000240030a1514400e0280d01c0b030301301d141050404d0b104030045621414113108005000360340460103c003031800c4000124819200c002034070075100c510041c0480d55081c10f024200049092100340c0d07429421011100d0594079152a007151541c11541c058500300800f61119603c00e10600c40c02118031401d000600d103040c4590300101c1c20518500e068050b01103440780d004280401400756136403159000490300c2d44a0007070300c2d003c1911940b01e4080703802e40c4285c3d940340341c00c04188010071651940002c0c40b0001c5400c500c41310720041c02400349800341d8903402e000007811400c03050344607240c1e0080c4e90002c0c0d4001c40701200540c42c1039081050264000c402c0c03103214410202201a14180100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 750042500 1250 750041250 750041263
    0x40503010e03070b0613230405010501050a0b1e130326091020030f300406020708040513230702070302240a021e01020403081b0a1e0302 60
    0x51070000e50402440d640c84e0f01c08114000d2519008103011a211240042241c100503200036002003481025003540d0181025024201c400350380542c01d1100000d182c2c28108030940071540b02808a0b41002a44071010111444460441d01c440c502803140c0c44400c03096406840086119039a94012100c03003c0080312003401e85120304200260138046080140c03944913141040d0f00301d9140200070003007591110b1801c0c41d00c815106242e407001140c81003801012030024400080b240f00000e000ca0450a58400500e04075000030107074050543c0482c0010b5050b4001e03012162080d8200e41c1026202c80203d0003041555904015490300c6452041d000120000044054403100c00030b00840d00d01420042e503508000d02c030082c0940300d80340702c05244070a1208018010307540c0d91401030740e80f061440e00a40c1d45820140b286000b00612140c0300e1034020500c203c60480c2e921010302c5007405a41a031110a0811104d404007090050b56020400910450403043da5002ea8030714859801c1d03054100240303081b9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 750043750 1250 750042500 750042521
    0x1b1e010605060f0d0f06150e030c0a03080f1c1a090601090806010623041202010f050a0807081801052d010e060f1c11090a0c0f0e010e1504050301 64
    0x300c04101c020701d0303d0100c2d003c94000d614035520108031420b6210340c2000070320701948002c10715800d0035101070340f8651065081386403803401c8044075201e901410410164804138030004000a03010000e00600c202e0040103040400c00f0700641c0b10a9a182c905c81505a131681404c241a500080003102160300d00b5031000c5400501c203180021102c5d003864842a6241c0741800341c401801040d040c03020040c0045000384a030303400190023003900c0d15511200501c2c02d0120143c100c0c0400d10340802c415880d44034000765420803000d40d03607940313581d01c0d850f0f000c0d41d4400380600205a544040104813014036001d00805006042d82010180c490118600038151203c0311149002c1d1400148010000500f4510700b80703420020803614103c071802c21400280d55101c4103507010508690403241d503001d20000d00c003003039070403074054448000e555145103074401120243c4519802140c0d00c1d4001c8050f42e03201c2c0d2404408880c040c14030703540082130180000c001c0b9410402924140d00c001a01303000c1410280504440d02c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 750045000 1250 750043750 750043759
    0x1e01092103200a031206090e010b04050711030307200303090f010b0415030602090a0e01030f1e02090f0406420303020a030e030c060703050c0106060813081b1e010605 73
    0x11425a42e110340c0360000140003504100400648500d0080e05502050041c813102404104401450b50703010302806400c12481d1082c1d25100000c0c2150f8020100300108130100c5020754030390399520b41d041e074111241e510304058030109102418044801080154051642d48008010b82504d440e41340b403e490900c180c182c0110f040c0f42d608181707442c0030407076401500c3c1d100750090384411b10a000306a103104180c0c0b0070550041808000024801d10032003140105010305240809140341d100309891052140000a40091083d0b0025a00407040c3c00d0142c1c0191150002003240313200a00c0101c0901c2010604000760302c0d00310401421086010341406e88200050358100b5040e1a40c1c8002e5102d1190b91005000d00403561211a159a0280036240b4860801048944c0310641420000c02c150000401c4000c1580b80480100361140100d600d18840e20640341c80c07039100301141e0b5504200b90444060416070303241c220b4541a1600d400d02800074072440c00c520000504484080903401d442150344968042c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 750046250 1250 750045000 750045047
    0x2070215220503070603020912011b0909060b09100e030f010b030c1206130825021207031e0501020706052a03060f01050f092e030b1e01092103 63
    0x40d20f01044850444260341401a00d811041000c079030965401c541c602015440c044601c1001c0509a00546483d4515a0740c081c43d140c0701c4250008030b646074051f0f03068540e028030401c071311303460840c403100c0d01c4901a16203840c100e010440072910b400b0003203d00500f140d44414440c03c070f50070104032021402ea011900300095808541c0f0a5480e00030191039032404501d010030890a00000e0011107416100101c00d07921010000c80c250301c88000c8c040d0040744100c000d1402e08480c1030000540d501504c0e0002d07104220414544219200c0316a03a440464040d5024400100860700c3c6108661040324241c0d05880f0358020100030010307413210403005040e5810140103001907520b443c00d601d20856000c2c00d00a40e1014104058030340c0b03000d8011000c2e0b1120740c1c20141d80818040b031a41442003420600000a00000e54030241d09460f800314905030094008900b600c81c001400c0c402560315141030410b00e5681c0d0b115003000200c00a20303103c484114554450000400d644401c640d0784102c1c0004242c2c24 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 750047500 1250 750046250 750046259
    0xc041401020309090423030c03031909030819180605010602120a0c11130c270305060c09180901050402091302031f021c090b0714070602030405010207021522 69
    0x30703100405440a0030400c1000441c1d215605d580074071b410422841030403242c44041120b50b103685d0340d2007210130104610450540c045824094017540100c681c0c181c550f04e1403030ba29100244049001c40c581380192649072070070880e61903800c141c0344007224010180400c1e02d604019010b86482c950f00c2c0c20040403002000318804807035003d0301c0d07812401d0f4400c503080e4801003460300103503d00c40340e01900710b0300302c1c03501c5602050160400780c010740e440001031904d11281070a4034244101e401601c009082c0e03400200c0041c5002240328028000380000074a180d0050f810550715400c9840100c8000b000742c1e5450013844190300d40f2103043d55100c1d002601c0700d1001011030340860349420b03d41c601d00c1c3c01e442d08111001414942034040c5c92891313108101186451030001c0d44030303000c1c0c00000390560740700c2e01d90300103d404648108a015076055000042d58030740407484d80c40b04000c1d8402030055441c1c2d50b0a01c14400143c0c0c0e03800031003109481c868070241e1106d9801c1000c51107074511040320b035190503200b8400c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 750048750 1250 750047500 750047509
    0x10c0507060509060706060806042307091d0a030c1e0f02060a0309021002030d1505030a030f0201020f120405010b03010b0108070c020301060b070605070215040507050d1a0c041401020309 82
    0x30151030151400c00d0300d803580c030004110369008509004041d907050031000b02d03404c075000400c2842180101303890b00503100030301c2c05100a0b0150504048154100280900102d240764005101d11b005071105081c813000940b0381c00c0d00713044600d08100d0019105841c030500b80110750750031590f01c00e091808501d01d407800340e40d6500c01d002c600b80001c0c0140c4020800c4540303d4001c0e4010818150090420004041d9505000f500ca46c420f0860030500e903c1c000e00401c0c0411040d40d828280c03840500240450046034a056403244915012281107640800c0000340091480019040c11a00f603007410b049420945080c60a44084c864402d000e60324012032200309a90184016402c0f00e05400c20b4180c045031400406d000d4041a0046491803000042000803c462a0b12062040e070f501c1e0300b600e50340b001c03440102d034808034103440142207984683c0050100e4604902c8449810380300b49212911001c2090b9049520341c000c44103000c0c40ea0340407400700302800203021036602c080b1003440030b9441c15903001e0028 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 750050000 1250 750048750 750048763
    0x100609030f020d060f060828021c1b2d0311031509060a060f030c0306150e04050c10020309060d0518060f01060201060e0f161206090f050105010c05 65
    0x70700164155400102992a002c0e25003101a03001035041c0b000b52041007400c0081d11040c0b0499405108000101c440d007541040c8030445100d806455000c0b021072902002844200c0b413141411010000c59208002030b01e01c0c614074090250007400001c00c9151031070050311b803ea00c3c001030100400401101982113442070098007070b03035402483e005a8404001c041383c600f005000040180c2c450002c14004903407000940140304000e403800a011454680c0601c0e40d000400740300c000d01390101c141040c000582d480e08803050b0680301094268040ba44c4d01118001d1000035501501c0c941c00400f00450b01d8180661000d4000b0381500003985441090400709520b0700c01c4904091409941e5000300704052045100480702845510071607200b81481351611a001c4420701c50480598a081720000e0b00c804541304c0580f01d200008001a050380e541640c507540b1490217481d5400304601e86012545200d568800c01000d0003c80c3c3c1c00051003c8403407118000c40e401a0401414445030002e1000011400a0711 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 750051250 1250 750050000 750050003
    0x30c0f0815090c130608041419081c090f020310050105220605040606051308011406010318170a0201050c1603110106050a090507080a09030207170703060603120810060903 75
    0x6201481d6a48050103529020308596a92100c1804c07070000380036640303e03648a016500406801c682d0120f902c0d8155614040d00303041d506480200440c03000491008070240c03690400800c4c0b400d07900702540e0485c5040300c1c098403048542c190781c0c000c0601507003402c20180b2281156464104202c2d4102000600b015160349081a40380214800c485003c151580005001f064050414042c0a031140e0011703200d034002c0e10f0304202c0d0440580c00040c142a050140324800c0b05030945001168841400440103050840d4880200005490000d000100209440d60181300740303060f5070707880e42c0e014400242965009030003440b071404103124174100d050f480b010610004c3c0d03050500300d011002c035880d41405030900394800c6a21403840180001c0841c41900864420310341039070303102540c0d03845904e09001c0301d45009010300140d20004051103841c0d200381c0c001070b0080e402c608550620f07681381c2da4603080d591541c00031600f40c031204100d03a013580c0c0c11150035a00140380072003003072800342000e03401841e40d480d0303100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 750052500 1250 750051250 750051259
    0xb0907020c15070501060e180601050603220b0a0f201219050a020403030f051e181203070303051b031504020c030703020610051c0f14030a030c0f0815 66
    0x844150b840e40b070200c03a40d580d802030007400125560041070581290413580502c9100d052a48048407000101c0c0e00342c1030b0f9400400c0c1c9401d503103601031044403218440d00d20642500e0101c0d14107010502d04070f0b069100310010900403c103202d00e4001507003a0780b1030070160360a90a18100480000340c0c440141c0b03400d5522014200c009603211701812001d01c8050501405083c9014240006000160010f00c2500e000b0b4030754a642c1c9040d65011112842151071303109807501030090b2071411080d460b00610a0201c180768418003414400002801858003181c2d40c0780e90342c4000384903001c050b01402116805814440000f0021603082c404443d240b0009080180041d01000000c00a680d154180c0d01e0050303c0e842100c0c1c40300440e10300a507607083c06890444200002d6040083d9600c2c190341c3c800041901c0051070109010140e85403088081080001c0301d80c1100800d01c402005070800282c01d0ba0441650007080d601104c0201510562945450f00200443c8070100301c0f81480ba4850361501c8201603c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 750053750 1250 750052500 750052519
    0x1060905040c0e0f18100f140906040b030f100f0c0306050d0f03090e041506080304150507050703060e060a0c0311180f060409150b040305120703051204030c060b0907020c 75
    0x400110070410401135240896502001d01c04021006c01110007581c0c91030450580013034841440b000c11001c0400d10a0b4000d424500040c0107060580041e504000d02804031006a215a0041c2e41094040307651407941d181d480c00c12088042080c02048010036250030100041e60600022038240c506001d000383c070742305c058031140341054401c100c0f58000b86400d51040490307046c289002d003006003003008007000841c1860004516240b01104503800c6a0b80781c80c0391403901400100c281c1e1250400c0009940c01d004ac41c1000011a9803130003604149150007018141900c0d1586260045032034600003c0c08142c50a00c540040c0ea27410011035884403582d0b1a948200071010001174a01070041d203204c3e41041c0c01080c0050b0404a0740c018485610f5482660001d503502c4440c02c840d117008610018000d43e00a080c1e040c000b10100f07000f0b01406000c0d00d000c501d88440106d908091600594003200010310440da40c10078082144200100c0d28001ca91582060034004c03030003907441000b01d040921540b00c00703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 750055000 1250 750053750 750053779
    0xd3e0a051b0307080a0309031707050405131812080903030f0609062d031b090a05070504120b01031e0506010b090d05010f0c020f0304270b04020c010501060905040c0e 73
    0x8000f40c440066011500e42d58500106200030b01800c0754400407000700b040c0f8540600d0320700d41c09001502c520b1a41d1b5a99041c603140c5000c100143e802003031024501d0f99564000210540c81e00101c03450180100300208800000f00c0c0001c0c00c0040042200540750428401d00c10b40005100c0324540007081220400002c2c2c44020000c2c007218a00d00252501110071113422407903055505050701450b03070440c20307580b448814481d5404183c14040103168803500550004007003c2c0303694031083c3c0003006c034501141043c1e200c40b203828844080b000705842c0e03440325500410410414004035092503c044407024030740c4c80c0c1c0c0c2d90380c1d6076655010700410510328004070341800f20380c0300c100c1e120702d0040d0044020b000c031080c1314001c100140902550380c00180030701a006007008000108443c04c0320318510f000c2808002915180644d20b003d90481518140c6521107140180d4039030004d460f02c5200e0b40c000040d954541035010340392101903401540a40e003400500080b81c1c0d000300d0308480c0000c0588800403410201c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 750056250 1250 750055000 750055003
    0x2030a0513080d09090b0d0302030d020307170f0115030c0f030905240f06060a0906030b0a1a0901020601090632060a0504090f020316050d3e0a051b 65
    0x1107400c902d405119142d51001c8540d030204082c0101e41002508110160350314061290003070340008080c01580c400c00042d8040c3c5002c0c1d00440c4c1c408041e2424a0843d00403018843d0303100803e4800d80c01c8030401c41d0062101441c0c0052011603107c15050422035400c50200241c420684810f1002c1455a182c0c81c2e40248078041c00580d10044480022403030700b0f01041c06111001006860750f040c040f24410000b203041c1811000c50f60301d081c0d1916580703603061070004220082e0158484003508a404c840c40091400070103243c503d0718820404040342c0700c60311403000a2030203205a100025540c03d00c4800c004181820440a03505401e40182c80305041ca40e0100080d040081148290042030024805110540c05800342080e180261400e0080f09134801d07008041c0c4c0001d0300c100303000e10488105410902e004000400340d5010041010851013103020517a41d01505070b00740345c11900078030b8000c0c0080c0c2c0205002000c14000f85c0306446d040c03110001c0010020b00540d18420019804400480c140010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 750057500 1250 750056250 750056287
    0x50d033609200d020a2303510d020901140109031a16080606161b030302011b050309030406050304050a0501020705010b1c05120d09050f0f1c02030a05 66
    0x341049a54414585552400030340c050b44164000a08400c0c1d06e140d5400c00d01411800c580380c0016503420740d2039030440f0301240001c1c00858940d4030513010107603241160701c402988910825a145030014a007991000c0c0c4103a103030940241c407441c0d000c0755000c01070b901c01c00384a040d14892a00324204a9507440142c810034200c1d00040c0a1801a02c034846c180c041d42c0c0200c5115044400e010042e00201c2d003001d0707a5920b4107561160340080e0070b1000c2e0a07500c04100d00c0c22000340c000d1225007080c40e540155036002150329041500140d459082c901c002c4441c0c14001c1c8410348082c80d000c1d2962030100b00407502ea000d28044c082c10400000042010700c60b040000c2d5208603086002199111001d10300180248110410329004108407041710703505941907010034142a4001300903000082041c1c1c3c0480c01d0313901c40b080f148081c569504088000c10700805ca50300b0340e4080311000b0881c40f88100b00d403500e046424001c070319150001400010107c1c1c0d01006544070002c1c542800c549817103501d0f228005802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 750058750 1250 750057500 750057551
    0x1030e0304080609070b1c1503080d0608010e0a110904081308030a0206060a140103090312060602030319050105150d020f0f090127060804020a050d033609 68
    0x480450302082c250710101e10700f80646200c5088511030360b52415111014020b0030500c0d0f0403c64a16262082e0140b160000601101d550030003420300c40d141d598036070864000005a444180e91030f101880000000d100300319000c11410700410b041700141d980e004d52003071040612405061070700003141c20440944161000c410000105100403510342500c3c6a1382c1c0c02850312507006114000c042802824500c044400340d4240ca40c2030504c80c0f075900700560180c03070f41c2c05084082000b0240d404042603858800d240152906502459907070400c220f9125003032000c0350343c40070903c4c0f41600401c22030351950910081102c031000d400d911010041c20703000090054018000c1c2d019400035142c000c1d0482c4c0340007000c80140980320b100c8084098031600000c020203070030090030300e00c2c8180c045c480103000d01d1145c1d40c01880146445107694845012800000980c03400700c002c00d0700140c0007181c80d64115070f070505101441c0b070361004600360031440c24100700d880d102d200d10031039581030380c00901c0141100644802 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 750060000 1250 750058750 750058753
    0xf140415030b040b100b040e07081801180308010504051e09100626151305071a0a170402030706030b041b261b210705070614090a030e01030e 62
    0x30710f01402c180c2401c0604480481c41106204400305550a046003a01d0541d440c1d204040c4255072000c409440140e0060000c80c1110f815024009900c1002d00519805541403c00a1906440e03450042c2480340180c04c9a0b110314203040400c08818500c02c01039040f4160b0400d002c00c01c0d00d400c8081820703e048000c040c86031394240780d00421510805070384034060703e10200c1103900001c607807500181c80300495200040115200d5010582c001544007094030b0720341c092802d5856076036454120712403000c407500d4000095080400c1c003210103074000d1140c1070416603422600110303103010303400203454a42e9402024140355407904100d00a8a5a034810b0040801a800001907100d02080280c161007925560890f000a0050344c044000201325101f4020481c41c0000b00e811800220f00c0c46998016549100e40b904140141c0c0900a460399262405454151140c03035841c015800c00d40140c440404445c0e01e00c18a81080c0011088009051081e05030545048150b4804640c0102d02070407403001d0301181d0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 750061250 1250 750060000 750060023
    0xb0d051e0a06030b0601020609070501031505090a0606030605010f0806011206030f060605030d0c030c021002011b2a0327090204030b0a0c170f070e0603090a0308010f14041503 77
    0x10351075840705058074004c5100c9004c43d0390309801240d480d54101d500142641155408000c29402608420025181d401c0c001130f02c01c0e1160003080c03640d1b600320780d0705000540351401040655014414036020b400c081c07824180d400200700e00980100e1020740b1043c100413050f11404080b251035440743c0c014542c86030700c06940035442d05118004d48100c0c0541b0388070307020b240114840c0301c1c06141c5006900c3d900d0b0303d845084118603002c0010070f2144041000070f55480703241101c030350002601d0403013101d159915402c00f4442651030380f50355590540041c0301d21600d00450440802d80000702e1824507001c15412110480b0b070f40f20103011030100d650154000c1c90020a01004002641c203107144144400b4004000c00c2240f002c04480d8601a10198950f06803540c01044030058805009548030b4904d0034405135003035080011417415441101e0304d1917960090039003030f801c00d40d00100d03041c01040d890303098101c07841c02d10b81154070b048141c0c100180b00e255034003070005205002500d40e43c021500102000314 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 750062500 1250 750061250 750061261
    0x20732060f2206021e16110612010e040b060315060d06060306050112140606060406140c070f05210706030207050c03060a020903101406090a0e0f1c090b0d051e 70
    0x103900070404d0081c0c0b042d169014030700400e0103101550107902002c184000c1b07400c4961141e54144000fa11910b8000d4000c021225003407542a181d140208040c3d00e000a0714501030403d003031711260242800348203412030669041c40402e00b600c601d4001000700d0701c03c60b8440303aa10b0580000d00716a4802030005080000009a004201042c51641401805c11f42c2408040308100c6441d80d804503821036001c0c20912045c80743d944030740f01e855844880e0312003035403800192000e81d034641142903101c88940e000c1e884052210b400c0441c001c44004200b40c000c1c01c09401b80003190f9848061502900381050350209804041c08000c003c010456400a001d4528038142001b12002942c03000800ca80240301d550503141080d40c140c801c0b2051885003070045100d42d107442e401c00c00e0752440034108002c05500c0c1c00c4e50011183c01404003401c0140540c00030001c0c1c5e5414140380c8110f146500380c0e0418400386160030404983c0550440d000c0003100d81000800e0382c1c1d40c00796031a049202141281c20340500c0c204200d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 750063750 1250 750062500 750062513
    0x20306030106050a0e0a0b01111902211509160807090c0c110f220c08060109030c0b0c070e190b0603060d12050904020732060f22 57
    0x1802008190028480142c548003800030501c1c0a12a841d00d00c2c5501000442000c003076030100d40d01d042c05160001114400e2440c8a1070403d010702034200d0408034030400c5045181a90002d080070000e4160560503111010600c0d498044070b0043c1c894a081d43d00002d0200e1006000700b0111026540d04082c03599203581c1071554a10242c0a0208050701e09500c0300361060040e07000c00200350303000590200c001340c24014000012404101716402510440691040174040840c0c1590701d00310000008441c110717250000c1c05924017074215814000200c000344042904454444240c0c0e0000018550740c04c80d40b03204925000c090f5100c40784441d4000107019905030345079224140a01840300c14081803503c0001c00c000c0d0300c41502c0c041d92002c03050720703001d001913000c1d01695103201c1c148c140035080c600034030081810b90f802040100c40e0500100c51642440446a03280ca405001d075590070380101d0b403200100381d92240041c0549814100d00e800203015807000d40942c1c914000003003c8c11018072030030310307000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 750065000 1250 750063750 750063757
    0x9100f090b0f0103080a030902030709090b1504050c040605070c0e09030304051614010f1202030114031605011b06180b0a0513020109090b0418050706020f0f0d0f0215070302 76
    0x8072082820030001c5840c040e59820018107a030f4201da01d091405842d00700a50080c604036104a80501844a000880c1800751040300109805942c0c502c9071458403000c1c0426003880c88004510452500c5c05010040b030750032050f501911190b041443d1340300e0f0706003800c0c2001001d540c0201e1013038400c00d00308103541c0340101c01341d8015032083e01140d9854946001c1500c00c2d000c5030052a40f664201aa000d002d90310070079442040740701c5401c0519502c03c500004000313a03882600300d8007d001c0c031804000303a03900f010000740340303000c048010010100d800c00000030b10740c141e0100a0805441c4000c11542800440e5200d0342145950354160354a0800c145000409540e08035030410b96a4540350000e8400800c0548400d1203680c16990b19501e00e081131010230003007480107d066001507980c4000031082000d40aa40f42c61030066005120180c40c10307030003d240002d07503021040c00fa040300c14084900400000c000740b09020f103082220035804100000c038075008501001c2001c1c07104c2c040501c4402509036004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 750066250 1250 750065000 750065003
    0x80414010e090414060c041d0c07230709022508280f02061005040519050c04080607050f09040c030212040f021509090c1e040b13120209070809100f09 66
    0x5441146d91041040b096600840c405c0c49444442c0203141461007011040740341c2c1c89004040c01d14186070381382c1c8440c4101d200040002101204915206402200820040300207003c2c0620561508a105943e103443d040080b41000700ea80fa48a03480c0100007039a01511010740da0107130384d000b21070760000c030801e1003000400002c0c0200301010141030000c0d2010494622a41d422190300c03000343d141c402408002c0c8002004840c0030813542d1158000f000203800b0340b902600491300e0301a110b0b41082051030409401500a4080c807000304841a9078024103026102c01c550300b280d0000d000c01102605802911442255108000d0354000700001c0010700388518008c540242c841300300302400e21040b54020b108007003030550b007c0100c000103401d8030000002004580088a01035400c02e02c2c4140c0026540c12a030401c42c41400040b802c40e0114a1141200000b8820000400002038403a0040340d90248054544420000202c000a205180401916175003c5010714104550000d43c10084010101c4c2c040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 750067500 1250 750066250 750066253
    0x506181617070e0910050a0b0d0e0622030314040818010206060303270a0b120f15060903012406120e0705100c0209010e09010c020a080414010e090414 66
    0x30703900034040c03100e40d1038801d0185440700c148214880c0c0400580c00c10040403611040c821580204580d25828139000052410000ca1529001d0810280d0141d43c5000813111040d80282c1c1000340d40d6481001074213481c41c1e003d4020405030308a09084000e08070305811403580300c035250240010040200010058060003000403a02c14806400481e100c400c2038804541c590300030300820b01d956241c940401c8000d001c1c03820890700c0c9200400441e41090040c1d101c3c056408002c00e00014000400744101c0d0b1202484031100c103d8030340500041800000d070a40c6074059034000c200e604c0181c900350b20000310303045010700010702016032001c03011040550703005d4000018140e070040d00340180c9600843c1813140020000d04055418402071100b84118600c6110030000c064180301c0250301d4017000a806414200600c42c010700c1c0c005003440c20745000d18100c4045500007400341010440403001c1d0740a440250415400c035891880040b80e42880720110180d0245100041c030041010b020b00e2601e40c0e110910 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 750068750 1250 750067500 750067517
    0x30a140a0b0708041b14012d1806090303120c120510150309020d081c0203040501050420010206070e0102010e01141f0b07020603130b07080f0105040c1205061816 71
    0xc044803103050180c4034011b2040703030500a00081d0741c0900340c11044005001c41100d02000108031703400501e200403242c2008074040c0a00708410140c0c1c0156034001c1c01943c108460b02600d1940d000b4240d188142d10314009030ba0302c030310719014140719002845841142c810240f15609001c042c044c0e090015210b1099010500f0042d45100b9000b40901c0c0d02c0e158004041c2c0301e01048644a0105540c0700c0710364202405042c0c684100320001030320256004c0c90040000007014a080e00c1c1a000403400300c06802d2840c110016000c925030303400541c8a5012031640f03444500080b42c0d800603070160816240b0318049500300709414000c40703448010b0612402d80200d5100348103400000543c01d60003d80540702c00201d04206020240c18200300440d00145042040080d003400c5486000103004152400750008074104140030901040612450240000311001c01402c54032250207040b8a00d4042075404280e11940040c0c0fa036a60702092035004012084408064a8800e0b51001c01d801c80795202d2012401d8513 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 750070000 1250 750068750 750068783
    0x81b071202060f1b180a05060307081902040e04260d020c150705190507020a2402120714070302060319050108210711031605010e0d02030a140a0b070804 67
    0x1801d0000070701c4660500380b490001c0501703501100902c0040d015400108404001545032540740c0250300c02d2131583c0c1d03140303501d041c00705000a90700442400e00c610140140018080c40d0105809540c001e68441c4620003010792041d05400c00034006071280588031404200780d121000c0e1a0020040f1149541c1a00c40b0b8041d080e5860206113025504a030000d0b03000e0103888070380038111014044034040f50901d00d0034209164001003202e1296085450380c0c0c3c00c0c050800005210007a0b03440c0094081740040c240341d4043d101c075035005004d2030b40c002e0540a481d85032502c9008003404a031000d5600a0700c0f0b55500e207002d15190960071800010043e000d4509000054402c502240c0300840c200100c40460384500804000c002903003100380240d40000c01101004856501007124180312100300700444100f030310b000c0002d00108804074100b80244104030b800c100503500440d1583c0c985600516200440030404201441c0910140c801024082d0841c01e100d060340c3c103d01107521a42c40b0b1140d0303040c6030110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 750071250 1250 750070000 750070021
    0x20c0301180c0608090106080703030905100c1709130203270d02072d0f090f15060c210c14010e0c0105031905040b010e010b0703081b071202060f 64
    0x68001c00b50002d003844200348645441200c00369000000c100001c00d807e511100141d00b480d04035481280883c4415900704018102200020601155030410001c0701d0780750784440c0d1303500b45100b03031001a84100183d40e8400d5503a200c100d048060340c502c011500e91070103101071142c007145484403d0120645980b82c0f0b21804002030340c900580c1042d40a000d013176240500446011200081120f58850544026011030500105010040c41c069034155507172441d145c031300c40840c7c18440504079580c0c1001c1c6009506504e040c4030390122211351520700130170170240c00c01c082110880360900c2007040b120074070120501da0203040e800103d4016010790344880c0d81289051700725210b03060200c1e00c581200d02c8180996005a001e180d1201d21242c0e200c240817030f007040941c2110801c84048801b0940314005000c041c2c2c07550710300b50140844201c91868a0401d86002c0c0c2200d00c0104035140341d940b00b0942d80051004070095a84840c0d1100c00000315141e200000794480d4400c565013150001e20720001400c000a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 750072500 1250 750071250 750071291
    0xc08010b121b180406050a1802060910020109020d06050403030612050c100e040924060506030a020d061710050a06060906050f040b0a0917070e0a1a10020c0301 70
    0x12070000411100c020144526003000d10280425801410300c19842c082e88441c8442c140f00b94800c001c000740f6071401c0e40b100000c907207030704030511303110141401c044005845640c11a140810100c2c1c000900901000d002ca01400348194001c0d013241c0041100b0040100c82c0d081240150712a450a000164a400004420054000b40035001d640440ca600f411418650340302c041481131841c220b40c01040200105041d01c00d4100100c2e280000004a00c40241000ca0801174000038210b040c8112850140011218040903280500e219800505203410f0405580f0841c01010300d000c05a02861041d0b28140c9c031a04000f10703101e921801c02c40050b91561082c4501020350310180c40348140c0c00e00f0040c00700d815400103102c01c41e2440c0b0820001c43c20141c03e0000d84080d14850755405a5a42000c40401a00c041000460f542da44030030028400c002e408000c056000d4030003080059402140e8511707900d4544202e0ac0a41c10190750120420400d5012440b01c225143c150001d10804801c410101400207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 750073750 1250 750072500 750072529
    0xc03030e01020615060705070503062a2a010b030a06050103061a031905010222030203070602150a02070201031b030b120c030a0f0f0c06080f0a020a230d090c08010b 72
    0x803451041040605d0494003601d0200d0058003107440254507400480e250000c190340000c0040843c803401807200c15403400741062804920080c608010a0800354044000310340505403034000a203c0c0850042c40c25400702901070f030024216201075441d41031100003004280001d0710080e0600c443c5141d88100c0246208518001070b00406280703904155082200d10180c1003150f06540810008000c2000504806c8061320355110008103a0311754410580742c42010f074011015034001c1040a004281c0d015111503100c21174541c05070f903071151440100c004002000382c6000300544600c02e5449507505a214005107101038409281640a0000d40d5548a68001c12107a150380160341e000d0015602e070036095a41442590f01c0075042001d079850604240036a0000b02c0007809003010088030107606404c881e000250b03c0002c501e017502d0014000d04004007400305611072020005060307000c0d8842021141c5000e00f515081020120b949026601102a0700c00d2543e40e60900e04100803a1a0008040040030b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 750075000 1250 750073750 750073771
    0x90a0507031205130801020322151e0203070f0206071107210b1510050304050c0d1401240914070c0c170c090f0606090405100f030c03030e010206 64
    0x224599942c03040c0074a100311034403003001818814442c019a003044c0d45006840707080f00140c0c403441d0101184c1241040340340d4a0300d48005450b9140d0125001c01c085071000e90081e000801c110650240c00f4034040d00b40c008040481d403000042290280d4840740708140c0d500c60341e082d29100e480c0c05004980c15000c0c0c4071401e0b42c1e07400c90030040060740145031903182c1506841440910aa4403074440617004c80f011245030080f00c403408688003141c07030070414101c0d15444030b0070210b04504058803001d945140d801c24060050700800c81c450300344006815900141c40c5118001c1c002941482d8030750064041003801c070142d4012401011561501d071b8014560704401510750341c42e403a61104011a1054580130068503803104072007011501110302c0c103048541011401c002c20f2504000814080b074004010301d504186501c2c801030200c03c3d039444040b900352160031a40801c06889003904048549582d5210221410942d0800010020307180702c1c1d10201e9000c0d807200d034041200003005a880f01412102d40501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 750076250 1250 750075000 750075013
    0x1b05041a0d0608030a020f1510061110020c0d11010501060807200a0c290301090e071e060206070e060304170706140114011b02041808070b0f090a05 65
    0x10112584041c003064281e5003408200c00303640b442003904542c410401c090060b080600440600d00c0b08200d201041004904984214513250000340c40c403148078040c0d4010801340c405025160002007200004800c070404d0215910301c041d50303260b40e4405006c4045008241c241008402c1800e0610415041f00c00035140e0403000ea0321a02d0444008820340b42e6008800704c000240e4694440410000201d28401c07041c1c410240e0a001d940703041c1403007142c1c0d42c000b08502c44003000380848040301500e044030110040440c3c20400c0b1134510f0305210050304145810441140814800e0030711190327800c01c40741c1c00d80940d8565101c010007101d880d4440c207250f80d0058030400228001443c2540b40d40c880600101e40c0da814404103695490503142c003c0007001606070104018130640d40b0090401444003004d013400c0155803550100110200660fa5011748560307540da10145007100e10781208520103501190050b9554054a080f031100c09e0141c42c00c00c8070b406030b1000506055400106103881941210040c2007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 750077500 1250 750076250 750076289
    0x30f0a080304060b01050732010213061b0813090e15040b07090308030708010807091a060c0c0a17010f060602061603180c090513031d061603031b0504 66
    0x82c0a04c81c000c5410083c0810150700800e40e06d826105422440b00a00305040201c00d1118040240700d04040c269a4410481c1c0484c544400980400307c4055040c6140f910142d89600c881c031484500000d44440000903400d001d000403c0a00c000303887c000801007144000a02095030360724921001089080c00c07603030108021840e01180303550b02010038540100155240d5440c40650341065950700d0100b0007400060121031010701a42e0042d0520400400c5050b00540c020315046807503621140c0202400a108004004184841252200082d03d011507156440305194007001480301549490351a020807012441c0240c0a6442180c140d50700800711038588a5858101d1202c03561003c0615644140c0c6503406600300d00c2541c41ca600801c5400c42462030300744008283d900003407003808040e00c03248005001030741001d00f0202d05040004408481c801c0440424081d2055911111401200059000816601d50000c100d5801c1820780100b00d02d000791010380b418003590141400c541d00f44e070310409 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 750078750 1250 750077500 750077513
    0x10e1f0b12040506010b07260d0c0c050c01021614060f0c06040b150904031d040509030903070801020f220302030106030b150103050403050f0a0e09090d1701030206040b0c0c041109030f0a080304 85
    0x25460743c08100e00c81c0b0701200c410607031042b2600070301c03d0b101151914840105100c4148458600c01e8401c0c006803050141040000c04140030070f0044410010351000c003800036494107025280c6403c9800c11042d42c884101108560310403089404844049551000864910317140217201503c2d0806080c8041d2600c1c0d07658191241010b03125002d003500102034000300695101c7c00741d54050800310001e03540d545004810305040c1610f5400507013280c0e004003c0725031700f41e4100302243d00300303c100640086080507240801d4100303812a40040e5156080000100502c40303c40721131f030b025840a91581804418601c019800c1e00c0044a000e008240c0c24424010f5a40894004141c40d0f00b0314a0016018240385000500c6c12105455104e1039a010030160f081282e00804c40d246010b40404103c0701035031442e400640c8a20842c0903003204010085002d200754001000800b404110007802449034074004c2c1c02c481031540056050500c41c4c402d00c00c000dc1c0000d030200d42c0c15610707078205000714915505c0745c503110b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 750080000 1250 750078750 750078803
    0x30706020106171c140d060b041e050307051002071a09012a020402031306051920030a0c0e0622120c170f0604030f17010e1f0b12040506010b07 63
    0x1089054800c000403098000b052080c7c41c090b000440c030f0244c507079050680c0e66411211649540206c095030103400d210660300000c000c401c840c000c4606045081d42400300f20b0511069070300400310141441084000842404094942268281e0316403094040d0380704c01203840454400c030201340703480b44200c240241c00c00340c00031544448039001c410241401580c40004450084030890032501c1c010320b41800c2c40300b0358000c514012a00000860b04600c901798103c810f8030020b850500001d566241e601c40050140c44151b1815200503c030039100d41100c504856044400a0704000d800c045440104000c00300e4801d05c00c41e15044823103011f045083c170340d0f4032940c0b801514184035244114121088800c500300b16291003184296a141079890b200fa501803c003010028850b00c00b12943c000502040c0858500c0a90052490101c0c1881c84140c410b98000ca6585801500881c1c40c00241030808000c00c11903d402248140d088514983c0d8456a8003224001c442d8024801d40f00007000002c1e01641c8030a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 750081250 1250 750080000 750080027
    0x614042304050c0303070308010905010f0b0307051606060b0d29130f051f0f0b071e080d0614030105011a0a12020417012301090c020c030706020106171c 67
    0x40f1005203000700d00003441c58210b00c908800280604006210103038090080500501e0458a443c48050800c00078010030302005080720100200483e40d040c088a40b4100384240345d03040078007048801d45032f824042c0294003082e0058813560a104611a80320002d5010030b5100f030507010480019049041000f08000a071218607216544441c420451400d0034032429000f040c03914295422a5280e01c28212034410b00e03030001c0c81210301040308001d40b6404504403200d403542704401d08241d481d9000d0000303400031400301c05415500d001c0740030308107041598032550a94200103c40c28540040800309403c1c0d030390034001c0b06a0f503c0308500001c1403d1212001c0c0640743c030385082c0f40c0480705252201c0812a00315520200f90b000c24500340e4004800c0a1103601080034a0300c0a0b9046513001075070f031072071084c010300c900d144030b03541c41030400085031080c00200c0c410fa0340101545c007855030b40d01c1c0080c0601118012004602620405501103442c0000c03040f0203241001d24800900f04401030a45003243e42003403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 750082500 1250 750081250 750081253
    0x4050411032413060615020105010302011101020906040e0c07050109050313050411040b0a050c010905160905061f030f0e011d070602060114040f1d1213050f010c0c0801061404230405 80
    0xb0f02103800341c3c09000c2c520740c408051f80002402d61550000402c50f03a2540c0c00f040301c03a40f0400040d02c160711050100e80079140c000344598001c1d120340040c080b161043c81805012546041c0c109810804044004c0002c021034028922607607403104100412100965680d10300250b0811040069001c02c0c0094101001d281c1841d0b81010845918107080d160954000c596a400180c4110904031030741540202504032000704000c1841d25201103840c10146441040003c0900300c101c540c9a07101e070b008400a0b0401c20f60500141d01500c441501811081c94402024464590101e0300314800103440ba085a056500a0a050740391440080e000020360720712540003622680b00889403c05400dc1c82d080c1054402c0780c4d40c030044502c8030f040c107002801b000103070060b8080107409000c141c80150802550307822200300c488150310100583c1e076503014003002003180184030000503c210040d4001000c80d111003015103040040e0340b00300070448030a10006403030b02d42c01800b4501d840c00e14003c1280d00621420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 750083750 1250 750082500 750082511
    0x908190b07030626100506060307140d0908180103020309120304020f150d0b060a120b0f0d080d180f030c0302071a090a0b07080f0f090405041103241306 67
    0x14000c2d008100004d40c007001d015619400b08041c400200102080c0d4140c08004000c68100744e030024025110180102c0c2c20400e08000c07100454038054101c07103c89800a10811413030f54503180c80189908071a603400401141d01c99aa080c075402030007128031400b0707464050078003441c0307103001d864031900054401e0380c00004a0703a403160952503642d10300b42180c1142410544910031200b440c0241c0315150504c0b401040180940c1010719040700c98084000074240002c030306180510f001c600d1814020038043d500028102401c4140050100107001015a040c400d000400c003c154031100800c480390018a003120840e4a040440d1045414822a41c403910596541d01c1d521350020080122420207d104000002003215040c50074603070400c0202003150081c1e0520307511351601c9225002d4020050f074003203000507401c03038601808400c5948448000340100264207083c2840624008058800d03806441850306540183d40c02800300904100c01614589441d030f83c444841c9851030810400312800e94981 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 750085000 1250 750083750 750083759
    0x90606130b040e060418030813080f1303030f0306060507080a0e0927120a0f02030d06060206070806120d1412130507060503150409020117090705010908190b070306 72
    0x1c00601c02008041410046030a11500304811107002c030015100040d60000c200000981120000360b00c50b0281010704d4521926090004051045400e884010031f4006100746220030340c14844c00c1a6130296031090004201100168126040c9028400104034180700800c0000c00500007814940307968a0030968944c00a000b19031f01c080b0594a0a10944000300c000d245039a580329925450340b1000300402c2140c0901090004034132611844d2420880c13101c540c503c0700e500800440c0c04101c1002c038200320300350343d809009490707a078146d8204001a038007001048142c6441e441290580304044042d00c40e20196440079100c0d2078058100c050314410a2114528020120300d0980c030038410340102c220020021302c3c001d4207102107500f1801c2884018814440d92180050841c1d140660540b40000c42021500040c0c5143d01c40c6d0000740c0c40d07030000b001000340e00391b408242102220f600303072541ca500c540c070356005948507054040340c0c3c0704020710313000807002040740290002d40204e5141400581e59455 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 750086250 1250 750085000 750085019
    0x309081501300f11060a140c07030209070f08061e09090123100509070206070c020307090603060e070630150f06110607080106300b010e030102070209060613 69
    0x101d51060310f20f0484042e00a05001410302000c4039000101c4080b890900c0c02c2c000079160941d0703120f440301210000b040340c403480c50302007140038040d540040ca03a21042c9000000244141c1c00c01280310001220750303000c43d180d0f0910080c00d01d04041c2c0c0301a0120540c01280500611880c02460440c0b15074840d1508103442000308440d08015003840c0000d5640d03c1c2c6041e05076200500c560100c0d000da202c1d541000213650340820980d400089628141440e0091400024a00580b035080314413020b2070b00000004000096001c6c000001720002554411540d680081d24907850f4078031411002d42c1d960020400800780034520880d01020000006200a40c000d115403c03440980c04c07140c0080f20301e08040c8071113a0440140c1407591400c2e4001c01d020b03e820380f00103011800c10b1058200b80a14a00450040d4100d070009000340b1f18141e4080c1c00901381c6400366009015003100640c0819588480307070880741018003c480c2d40c15000b41c2046e81e252030f50000d0203102d03885010004d0110304201c9001c50078010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 750087500 1250 750086250 750086339
    0x20040501050c100e0f120909010b131805071e0f030f09050706030c12020c0d0509061603031a030f34060e040b18220512070309081501 59
    0x71a90002c10302e103080500301e286408802c186d0441d20b00410b201403085a507805c9400d60644010500e01034441d90405118000660550010064000c0000209e40e61030429070000d8800c1c0e4555132172a414095494058005564440b07010002a03041c00240f41c07034034004c0d00040d04195054000041e201c15645603a400c003031243e007280002a8640e0b08409116a00c00c114003a00207201808620380301c0740f49031f100d68500706105030741e00340040417464004030750360002558a0200450170301e9111444c0f500d0000d00901140c0340900b1180c80080f15420581030004034442e01629803402452404042e80700c4283c1021528401000b00a20f076811310807590b04054400c004100b5501d0380e5106000410400c8240c80c1000400e43c000c0840e50f40c558002d100b04124180c01104411820114060b01000b004001c1a01140a4500c1c440c00ca22104440705007402015114000d036203600c1302ca6203c850036510740308810100684c001000e001400400c400140804440e81142c00045420a00c070348412944607 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 750088750 1250 750087500 750087521
    0x72d020a022407080c07060f0203040302150403020405040609200a09200a11011b080a0b190803030f06060310060e0607330501080703030e03010e0f0f0120040501050c10 74
    0x2e030214107800c05000070090355000d03010368240300c08c01d03555190009591780103500c0042e2090a1001c242c0f18491030703110840e406142c0140051009180905040f00500340f140000ca462038002a821034001160307004031700c403c01006111010b40e40c43c00c035107100a00782070800f0704521f808551a10f0940302d0325000501001d12251901032000e00c4440304282120100c00940341c6001e0b43c020440f004982c070900031680301100000001c1d80b06441008102403804040c4280400c2031141808941202c00101540c41000d0040c1c500303d5036607400042c49124041901d040c3d450704a0417209210742c60107a10707050800d103405040c4a04007402901d03501c0b0302440d0803115440042c1010250400c08150403482601e10b90000e400380015454401420b96402403403201500300318020030501c000c0d41c1d0139006030309180148001c56940d09610441c0d580c80d215070201c07410041d860720840c1d0b20846840081e446101e8000e20b01345003002c0c500401921075900895144a09000343d001c041035520b103511900740442c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 750090000 1250 750088750 750088763
    0xd050d0e010f140702070e070504060815121f0b100c0f08070c0305060601020d0206070f1701060e010912050303060603090c030703050303090706090e070e03100203072d020a022407 79
    0x9051100b4086e04103130154012115940011013000101a042021582203d002e4542440256031368414502c18480d4150070b542d0102021a50304032a020016090355442c20103001c105050501e00c03140340441c1d006200c0c20b500700d035007100140e09560090301d10402c028060014100000d0140d6610350040e4400c00303003110b030050014014802d0010410a06520220a0006100705000d89001030741d9504d00800c507004120700d100360a00000e1007005c050884582e590240b40341940c4800b03010b031002003c01429400a00d80080c001035501c0d03026810031a03540c01801442c44c640b100030501c646a0b00080c1507612038400c010040680e900c04100b018001d50040c03003d151642459800d003814045107922000c10404154018401d400b500410f054100ba0f0034108605810000008241840b206141c14524503101001300321040e03070881030249281141415911160703220306c10f00350b144259845a0b10050340280c1c81705c00142441100c40031028948145010744580711f02009030329500c07941d401c4490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 750091250 1250 750090000 750090041
    0x71401050a06120b1b041a0409110a05031521010c081503070b131d0402040b0909030d0b0406050402071a0702060105010f031e111305030d050d0e010f 66
    0x451a042c0314807409014600c841030301080351511080c55807500644810240c411010580c00303070b011018115001030004200b501e03005d000d5100500e40540007841000c02c42828015001400d8007810200e0700403210390340303a0034111f48031992080c01c09450120801d40120310802d00302e00040ba030f1505414040c07104030000c0341c2d02420b00340081c000c0c0405440c5045424007003110105039036021980b04252603107980030340c1c1c44c2d100c10000b50303c000c0d265601140c07440c00c0210407100d40c20b242d294900d114070f0080d5004e00440c80484c0601c80d20000071949401150014040c0300c10780c0d000c0b604034007a03480c0010b00126000c0d48541c001800c030b030320000044840801c155100040c81c4544002d881d405100360001d800300350314200028015201c407040b0102055928201c3c00d0700d2503070359029000c610072003100c02c10140d00d40082c030480b142c0c8108109064a590003400255920b03000940320075040440e518503003450b07490380d03c2030040d00c4c0300301e0003010a54907220600c00c4031485100e070300d071641e01208031042d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 750092500 1250 750091250 750091261
    0x813030c081006090204080c0909011103070f110d050d0c090306020a020313050a0509070f0215010308030618010501020c190e25080124021e0f010609051003110607140105 75
    0x11070b81c5503409010800d005110070841e810021030b0b1108510b1064603010f1281c0c0e198494140103133480d0302c090405c1d0f6404030601c500b180d03201100341d8031402da944448523108508c0481503070f94841580d0004c0020810020301d40c0001c0b10740c10010031001c8500380891900d4590340e4040607600103c1d00000140c1c07011803125101040c64840400400c6c0507624495030500340408030395241d000400300420f0121050280020ba8400c000d6841940e035801318102d11543c586ca0050141e60007519254402c840e007103030545a020361501c0c481c1c101e400580041128055410078494031028500304501e00050702c92001070305c072001daa03287d4442c8640c00c14070303040080258601d0035203201c13105030340e001c205010b00140301c44e281c08002c40e6103902c103400f5486552031580350102e2820800d012103048181c0344028500c0c811000080841880030003500901046440380b0744802200c60484140d200b41e00000c2d401c20209518141c482c080da000680b07154a004201d480300c0b450325002c041d0b1201c0c81ea41d2881080f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 750093750 1250 750092500 750092533
    0x310171603030206070e1e0f13020d0b0907180303080c070c090504020118080a26070b0f060102010b0a03080c0102252001050702040c1e050909011706040813030c08 72
    0x81100e10100c0d61090040b580c01d07d444480001d002245020714032104000d6069614044000b482c101401403c0d903070b07001030307040d8003014011002409000c0c2c1180307004142c1b0382e40a40500c07907000d07852078041200302d85180c03401c031780907003014120b41c4001030304010040110b5407081c0610003074200d00401040f60705142c4001440041d002000916030316401e601400044030200d8503100241e0811600b0038a151102c0c40c1c185014501004c010350314900183d000c0c100070b02000f0741032203085403281200d81c80e40e9101c0107900b41c60100c940b80e42e001515a2051000640c804007900003446e400e40010308255080c4407840c820015641c90038400c1c05000c80c200c042140900b41e14518800215599140030744460028185002c1c41c0c0b4005d1066031507002c0491454400c0e402d00321584020034000079090b03614079010341a9403111300c2140c016400040042090803d900d40196414494001001d540d9156252003d1a4021a240b0b11648044035400400b060a071020a0f0241c030240c80a803d08512501100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 750095000 1250 750093750 750093767
    0xf04020904062309091902060d0f09061113120602090a2405130303031d0303070e09090604050307080d0e031207110c0f010f02010609090f0215031017160303020607 72
    0x4c0c8210144410000000d101141d0640600003140c6044043c00b82407000941030301a8006450710079250001115a100076504070008160003010b04104460580c2c1e03551a182c40341c8403030150500b00011042002100c0c0103000141c3c24005c01005007015180000144090003540c403409665a058600440c044c0c40c0c46100a030003400c2d03040c120b14284482c200e03480c0b101b01c0c41c40003405041e0f4803c40e00d0402d5142d02243c0c46646402016640e41c1c0c40d01e6100a002d41c00050051030050744140e0010305201c2d00007800f14081c0350010300950a00d504d5030380c4c00203140d100c1c000e040f020725210f0152820702d0900b000900890f4070034480100380c074a0000d00003020000e2032840c010b001d6020904c240700f00d4451101c008410b40081c649451918050b04099000d40600d0384070f01040c61501813400240700010b000540030510880b899403c420400f0b4104009000a50380705120030f49106080216040001e202040300e12002c2c2980e07103002c1c5882100195800550050703002d6007000003000030442d80001d16 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 750096250 1250 750095000 750095069
    0x1401082401030b010308070807060e0610060c02030312040c0e04060515010f092303030d0903020706091a030703230912070b150604171c03090506060f0402090406 71
    0x3801141d89191940640c407001031002424410300081d0103000c0c80745150840300c00e50b81055050004d0240f092200c5e640e4001100d18108003104c5400105000e4440d4100d02406c17a002401542009070112502050000140c0100d40c2000c000100080e26241a041e040c862801580000740c5450007440c0f040307043ca900795000381004000c0d80200c4185070010b203c54151030711380e442c21241c018000c00d10841c0c40b46c02a00703154035100104201c00c2c0c801143e0000d00d55140f10358265040290756500555400d0309034020520494540e50800b00b04001c103e024551105041c43c011072503e0302500c03403990005c425030910300c0d1403080c4020032140e5901000030a400512510500e447c01740b403034481e03414651000d0440320f103200c01241002d0169441c5d0081d10050a880c0205640d903207203010b42c4994440c1070b110359410f14103000710f0b0301400034000c1c41440115600300c40500750036900c0d4410011140103a001e800d80c0541e0074840404c43d40c60b1849500c4c080c00303825080789004e400010101281d19000c544 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 750097500 1250 750096250 750096313
    0x70e0a15080c152a03211e060901031403041505190801080c0607210203122d090114010b04051c11010f020709090b06130e0304140103140108 62
    0x80303401480003040c984640200421246015921110030354103600c51142d0000301181c0a0b5a040d50f100740403035005000c2c1d035191245a444c4c0031047c07441d01000800711556a4044040e000401c085000610b840f400304040f801942c0c42d064a41754061100d142c000b0850001501c04900d40300e4400a90200c3d840e1003081c2d041ca03105c150300d846003840d034402c00303840c01e580116008034a9004000800c0000349c0c1c0321081d80c0080d1031550300c422000350303240c00005402c400c40e80d40701c0120b20100100b06400c0b15505016441d900b20004043c00c038141c8540182250360b480d90703038400d400704075050312100a01030000129401e40c0c0e1440d1030104500c291514a0032000b5006a214202c00100550280e024a20080c00c010106508030081642080c07081d0f80401412070070640017004118184101d07902c2250700322400b400182c0000c6010742101e4116900940c10b9100300028460444610b0503001c04441c145400302d51042200c02c10007548400380d12038030b01c40d44160f00d51101785018101d4810782a00311403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 750098750 1250 750097500 750097507
    0x9020a110a080405040b04140a020a080a050c040306050403050d0f0c021612060e071205010b120d02100b06040810050a0501060c12050304060921020d0f02070e0a15080c15 75
    0x21100b8000d07100750701ca881d1086940d8400c0a40c982c5454000783c092250840c04030030f40b4a81404450045c1d0b120302100d03000505c88100050541c0d06c0c0d8803a80e8000d91000e0222030a007411540c40c40e0080074054400d9050260601c004421050340e40580841d1007481c80011400319600d14020b403030f0401800030144c03504085401400388048090004680580107180415003c0c00c0c428184d083c04600e070454000d00c01d20301c1703800e0f0a00405410444820a0a541454200c03a80e003c420ba01c400c06481010300503040000e05100c030503903a800003920b500c001002c05160039039407a0742c0c030b2030701c2d004059401c0950303211020810b1510461084c00e00501c0242060f80c000d00a87d51070500081d43c0c0d8080da801d20002001140c140181944000d104680c0700040e80f402c46c8410f07140240008150b40c85d0b6005200c3ca00c4402c001d0f40c810003100c80f0004e0980c00405000d400c20804070103882c1c000304202c05950f52440540c180102520000e40144501800342001420720070a10041c000c008000c882c5400040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 750100000 1250 750098750 750098753
    0x1e10030524041101030e15150405010506030612010b12060a0c05040807030b070c0606120c090b010909050c0f040e0a0c0c0218070c050102031008010515030d0804050f01020409020a110a 81
    0x2441d040d510650042c41c0d180e40d24450801a80182105101055070b40711b801e070002c40307504000038524001e104100c0c42c401d0340c0c0c602c0d4007048180e800901860b0f800c281c02740049151420501824241d11054600105401c2103090124203a40943c0c18000015440b04c03007031014198051180444402c03081c541360380b41c40c9c18012100e0356003d072484002c0008181d140090390440c4956940035545501c00030a2116980d50300c1e4074a00200010010380b40035036840c038001400c0c052441031807103088041c2c503210070a6240003103400007800c006101c64000c020800c400c42003030b0241300040010f41404003850129090404800c802c407002c1a0100701401342500c0510050ba4454250882d8140c0302c003030141055503182012035207281040001086580007100b80808070a02031455070036036003220000c000319518900958220310f10601440e8054220217500c41d0305501c40c0181d160b0107401481141d24140040c00000d0072a0700c240c0c020212541d010420341d91499001810424403044480202102e0559 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 750101250 1250 750100000 750100063
    0x20d0506190b15040509040c2c060306010f090b0d0219061803030507111c03021f05010e0705090613030309051c031d0307030c090b090606160b1e100305 67
    0x154003600b0320605460000804005201c070480002e41705c3c007692007040c000103c980000840c81000b0041850709d401d00082c00c1ca041c00221035049400c000c045012581c50f103030100e00240710f071101c203981180c8505503040240e10385031250b0740d00d02009441c5842c0b5070316003c0000e1101290061600c0c4080703055208001107540002540e40b0943c000701d1515840600c2d50020781805440300556112012105980003455008a508000d04000e0b44c140c80c03046600d1100207044903400d00403100041d00c18004102000d2084000d0034120034040c00e00d900d402045c03240103400710002d6000b1000508200010b100398107108650f0a5603296075100780c1d00000706a0350103010041c101441c004074000c01640107000340d82c01c20000c4025030700600241c0750766480d0208607002e440e01c07940b501d004000381c00c00f0071174500b0154225036140c109450140c580c0c80d031540c1c51044104001c2c0c182c0d00421980a9030400081c0003165840c041c0c246001b00c945520b18514086050440c0d2540b6024084985400824210346 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 750102500 1250 750101250 750101257
    0x2090f04050c040c031d0601031e08071b0f080607030f0903080f1017011415100c0204060302040608010b011e271707062a0b04020d0506190b15 63
    0x242180c0105a190003014103c000b0300c00104c0a84071701d9100d40c441b03010b0050200d10319042c1ca0140900748005800119122040300210030020b203c510704024100c00b15141960071140f0130041c40c101d94580740e1b55180740c9403988083e0050101500f090040c000c4040e013500c81d4201d822055030bc240204182e68502a00d03c0c40000c0c1004880500a80001c405101000030207002e000085203031048900020081c40c002c1101200c0b1355522034032440400c84500c1c43d00381040d5400c400400f0110011080308080b50003d11a207012030f0050b807103103c0400141d50743d02840002c4d14003540005201419000010198600e206c0b0f820f030075004a0280b1034034607038000c8900b80f001c41128403200c5000a003559118404513640d0040013001030614180e100c40c10007240d940100c804941d26100f048800000102c0c0c03402d080b41c884420301d000482c10000007107a45658a40c0a0300040c41515440d141c2e450703040c1041d404583c91450000c189040543c07038400c2c0e11900c180d03101c3c2941e0118a1aa0003403043e01c4611 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 750103750 1250 750102500 750102523
    0xf0b0105030118060b03070f0e0f150c030705030a0c06051e0c1605010e0d090b210a0f3b030403060b0a03050a03020304090608031e0a11060c0702090f0405 68
    0x103a0f4110301c0c0748039000c41d04001c005103500740140d80c1c0c92410707000080a030f00342500c003d40000d00f810302481c1d0618207040d9003076081c04018071105001240310122b05070340c0e101400c05443ca01050110602150043c0090120303805c0e10303201d40101d80d41c107191850490300014034595143d107500c0030024403880038608042d4004880000542e4401c0500710010820980300401400d07507080405126514001080304001445a500c0d00480513803100c07006610f41c01180b0202e1800600300d804c903800629844044c580107960b003800051385941080e007900c2500c7c00c850400460801ca10500001e450030386a8190b0705400303000c0a8100950003590301900e031300c1244401740400f5241d045001e03140c1e1311114150000d641c4103084811803411440c000c1e4981c1c0051040d81011031810000040c072010220840d007031010006583c580c4049100c2c41c04030540c00460001040000858444a6024040150742c0c0070b02900008992516214070412101d0840184403007034070652001071000080001503450f0000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 750105000 1250 750103750 750103769
    0x40318240f0909060b0403030e01020d020c090606040915050306100e010e04080c060a090506160c38090d030c050d091b03030518030c130905100608100f0b01050301 72
    0x1d41e0201201c2c446480d810000d0401d19000c0001910301e83d110040c81180d101e5158124101c03007140040ea1124822480d40000d070700034441c1c0d4040e5140c00719031240e222400821140c180790b1103800751002c88600c2c030300042c0e419003188030030b01040c50700300315a40c3d000100303042c150a214244582d2078000d00c410300c01c000e41d030107862020400300610502030b2094025041c0072030300b01d072910410420203401a18801d03a0507020303810203d04407060003500303502e83c4a955107a400d0220006c0c1d403502d82078100388000c1c10350310003102c10407180080c0c0c4031000740b100c2e407858a442c0c40301e007060000741c0d090501c48600b1006142c03504803200556a001000e4410810841d1000644c0f0702080c284043c0c0015040c080381c825640ba90000303c10036421001400a01c480f003841d600d075655080041c159a5090080c646174000300c90560b003802c079081a040022032500c901c0541d907040e002e86007440140c400b260448800741c2c010707440c05002c4000f80e11820030b0101c500e04040c0042818280041c0c007522060150030144c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 750106250 1250 750105000 750105017
    0xa09050c0702030f070f0501032c010b03190b0108030328020909010b0403030e300705210f070e0417090a03111e0303030a1d030304031824 61
    0x100d200d100a07200042c0d0040c0688018100740d003407440c3c40303070440e0281002400b190340c004180c9500c64480c203280e8850494030301031038180d0580c1c41d4056082e4510914441e6407140c1d1000003a071801c0c401c0468503001c00c00c9089841c1142e15000308503003030580240b2030960052040020403000310110300d80c0015000c1c01c2c1e4105005004c15840607229202d02990807482c2d43e000010111205030081088038025550b540c070740c1540c10204100c0850145846600c0052014034001402c099007070000341c07400d5042107074225643e88012038140345d403085440076800061500744003881c000303100345e5800c20384200190600c10709045d0fa0800b11003002c0e10241c00d104810241007810a2460101d56100c41c0c01002030100c65924503210503803403d8040d250780900625010341c40c1d001b048602c90f90100308001c01a40c01d583c0c0f80e050b00c20041c09481e41e0356201c03d4080c1920240038000748001c5020300d0103540e40b48080411303a0700410440c50181e0218076524603070780c00d80c2d02d03006010214021546441c64003448 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 750107500 1250 750106250 750106261
    0x2001170601080903130807050a050303070f020936060907121502070618020a21171e0a03180b070c14031602090a0207030c1e12030509010e06060a0905 66
    0x614012405c0b205101450040c0c04241034000145100031600100e407030091481d201c1e010300d901e078000c180000b808801031a20a20052809000c00b50b44510104540c1d00316880308040100c41c4500345940c00441d0300807450030300c0685000c1c0902940070311064010b01081e4501040c888910440050103000038912001000031568940c0403102e40f15005401440b4410012912034664640705804a200f8181c2900004002800d504800c400816105428860401549920070700c10807814030282c054104018082004e002c2001c003032070504020344d01c00d445103507452002d0200c6190b10300c40244140c10b000c4070000540d0142c04030344e101800d0300c2c05868507400c0b0700d05007045010055640106000c04103502184c01850994070107032900031109a8181e0b00d400000c1c008030311400c40c0180005684100840120f0351560f0010055680c0910071002d42542c0d440741844c40c0346450364075000030380714000d01820100900410b40c0d9191100d02801c1203050400008140b83e10701d2240c5191241c4440005a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 750108750 1250 750107500 750107503
    0xc0304020d02090f150108280213030305040f0f15030c0905091302031e0c060a050f030a050a05060f100f1107031b08030f09040203061c20011706010809 67
    0x701182d003c0c0c282a07260030114103040103e0b0b0304460020903450030807010082e0350310581001c0c1c01107a0340b002000580c0a05910f061814041c3c00c07000464503000c00c102c05c4402520908100114060341d142034441d030030018015003d0805510403082410304010922115610080d41040351619050006004540b4482a50901c0a40d441180d0000440040084586400424001441c422000d41da0503144006046112039580344d019a001d0303101030500c1d4040d09056004041c17102507828140c0c280401c00060b400c4540c005c540207050380343ca81c4140b000d95905405060303009401206c00001381d031a80d00114200c4c801140043e400c002d0b99100108806020f4445c60540c968000140e414440d00da04007445c2e00740b00708100341c040001107000090600d40100aa0341c02005100f5080e1508024600b00720103034101410342c0b94481e400005100114008669000034948540c1803040505118031072032500e0f80498086030b050001441900030450180401641c2c026000d00700480345440307080c90035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 750110000 1250 750108750 750108769
    0x230d0914060103060c0e0910060809030d020c071403010b010804020609040209040501120c0e13030c11270a0204060c0f0507030b04030809071208180103021306030207020a09140c030402 81
    0xc2050302401d03002200703001180d00190008886a110001c215a01100344140310800f01e8001240d0003007440f081c00000d00c0740c4062030304450201c04403800c010a48014030201d900c000703d00140c039404407000b00b0228000b0343d20125124404c4000700700000c21100080c1403240000c0009106410000b8903001c980cec1ca6034192031011002600412483d07844200041c00507441035400c1c0c6924a0309100000c8590b14803244920070012281c0c062040511640d09a60840f5068021245031145d01e803200030325124410f410440e40030000100c507001c20300e61200c0e080240080d0451844600400c810310507a41c00c2004200d1081d03222040c000000e40340c0c20305a0034040c841d04001c1210b441401880241503010600340d02079144402a210265940c1078240820b4060701ca00908241e0b0602c62420440d501000f1104440010f040140c5001d00d5032903100c990000700e4112401195000ca80318056040044c405005050300f44030820140e00028421000b13802e009100001036800000001c0440d20360000c031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 750111250 1250 750110000 750110033
    0x806100210060602071823100911120a0213030809152a0715050705010b1002030c010f050408041e0b0d0501150e0a060e150c010c230d09 60
    0x2c00001c0d880d500000d460340d072540305802e41901079003030300f41d000403a41c031910148140020f1440340c1d0801c0070b1902c03100c0d80c000900644c2101a0b500c0002050303030890181e100e524180120341c2d50340c0c108450b0720040c5040d024140303809030707032050040792001140c0c84116802ea91300900c045885000c508001034074149081c01c10801410041b42030102041c12280c1c10139800d140310744080403800c07000081580d6007094414060001c03030120018400c54000d8009061075800389001003540343c1407402050b000c61021003540016030000070803402c09882845198205a043d82c0280031608258030344402502442c05410b10780124a4801c07008003000e221460004d00758220482c0c1c48142080507800101801d20640c07005803911003c004099100304065040060000e201e50541801c11038111515071440c0710542d00018844040900c0418100140c000300c17010100101d544000f0b248002d141c1e100311070164900c14191220308015500f040306076440308940d02d0001503615071505048001c16004ca92 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 750112500 1250 750111250 750111283
    0x712152715080106080706110706030203090c0904150b0102190b180106060f0e0105070c031403090405040c05120f060f0a09020d03090806060a12020f01050c031908130308061002 78
    0x80c0015840e9040d0000e00445c0c039a141510440c3d90303101000d03600d4200004c1c0d140d4003504503200510000340a5030256030407900200480b4102c02410010501640c0c044e0303815605403000704581003a0b21200c1c003900e03003000000e1001c0c02c0c003900c440030811054070034241e00402108949000406a05550602c2c91141032070754000d00003140ea44002030494a60400c5500c0096101200d0841a500031170407200e085030301007200c1c131196196813211201c050283c050845507000410680001c4e507564013402e80668042c0d038021000b280752074100000002c0e0121070f41c51a0f0850300c0c140560900c003180880d8801510811451603640b45089803004210111000754010501c0d264441490b51048110003070360101000c0342d00a44a0b4410040c80154a2081c0587d0000078460600141004a8230005800e01810024100000c0814480c00e40d08151040b03250215420a110790113070b88041d0441e0000540401445420120f171070051066000030300b554002c1341a00d21030981680308001da80390b80d135507011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 750113750 1250 750112500 750112541
    0x70f0209040b0402091501121109030d0504080f1f09050a0803161101051302150909012301050f03040609030e0a0f1e050102060403120f020307121527 66
    0x342c0b28150400c01c3c3c40070390080302c0140009181c0c3e4122141003541d00700c140c44440c1903240716403c0c400a442001c1c20420740080034400511551007c000117080300805440786919036040000192620b900f030700c0c0500340d40d401001c0b090003881c410120703001080d0005201050080840c1840fa16210013000001c150a40020412480100f0b0381c0700a88480031503a1450603442c0c5526100703090b1803040d680c0c0c0f5402c4250b0070301d40c001880c1900da0402c40f03803110031344541029107400020380d141d01c00768420200c0c1034001c011804220040c0988540310102420180d040140301c01121000d07020081000b40f58541e5030703a0100c00d060090482c814aa0720003850280c40d02d48890342c00b401200c1a00c0340c804005102161403004000c80c150990641d04181c0c02083c1320782e140c0d01c04490321b88080700c2106c0c10a50300c0039184400c101f540021480303916940ca40c0d000b15840808290129046e2011031030769100031010a00c080040f40700d940602010000f00106240b00c0007204c40f0080226500c4c40034080d841c030f07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 750115000 1250 750113750 750113753
    0xb22030503071b0506070c050f010507020c1f0804110310050702160501140307050a1b050102091c0b0103030305150315040b010f14010f0e0d061d01060317070f020904 73
    0x80001d611600c05075803030140020328003466840669a5002c01019908400700003030340e891250104401160080c0704441203505180025800c5a50650b01c0b803005030800354410805040080b181c3c0b8141503107001801000c103041000030403140e4040c100400301c50100f980c81141c2c0c1da01704041c99445419640c01c00481c02c01d45d0b806036680d01410841003010304840310015a940c080c01c4100320b40c003024210300345590385100c0101e0303107607004807044420f00c036080b40d10442400110105030800c900c0f81d4001a40c0e041c450382040744140124692990310018084030038000380072001400d0461b079150601090a40300c03014502002030030901115058810103980da01843c000d84011030095001c1d0040c0720b0940d0300c50020254110041c00740d2180400713030090450455105110f243c0d122340603450b28030f0604544400242e22085103007800c0d90300307503210168001c8400760020046010028007008004c524a1a520b44a1178840901004485007000c0303025001d001c098151030b00700c29801440d805c560b2809 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 750116250 1250 750115000 750115007
    0x4030201031121040b15030a08030901091401021201050a06120b0103060b0c0c180c070f0309120b101707031106160b07080f0417030405120f0d15030b040b2203 70
    0x1158150740700345e140000b11b0060203480300c40103995079028001d001c2002e221b40341e0554031741c03000d4001005d540da03800e02d44001c40d0500b0001d185040c0e00b900050b9842028240181b004403042e08058414444901c0800003035400000d120002c074440c01012518005183c0103800514841d40003038240b2900003601220b03410042803002400100b215001c100000241d410828900c4c110b4003000002c00070010131000c140703000162480240710b07240400090362038001c42c1a04611030002218100e0313070071043c41086900c4c130b4030240103403004040540640c91034171150340c1d071120b8901c0040c18007a080c0c2c907d00c9a6440e9401282d10501900310241d8004015140000004108450b200c000a0004020460035002700c04001d0190f6089150b03501e41b983c404151400742c2d84050000c596500c14038400c1c544200750903002e004890140c0c408a900d441b01070700e0f04030030f0320f442c460340ea00d40d20f0000800348005910540101d0304190805070560466440d0440a071008410070b400b0101500340c043c079802010360 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 750117500 1250 750116250 750116317
    0xf040609061d011416211e0b100e0321040308040f1508040218090a0507080706090503060121020307090510050f030a051b04091a0f07090b040302010311 67
    0x80c01070513410668510f00d880c0080e41c40142c0301030000b0840c80c031100086601030f01044002a81c010001200ca2040c039690319000400076800c0451074690400d01000e20b005044240e80702c1050828a01401d4208002038443c9001c01c84588400c03003018100721043e11800558002d1644050016076032070701c1d048030140e250924400c070041d0784042c81c295042c05d8070070704040d402a540900111084221003402c0804894000d10307001ea144541100740c0d0216008000c0700005203074450140c914541402c400410241403600f2540c001d5218100411125400c4811000e541d2140910041460550710019003410b1455100b0990242010180050407418404883c200d5404450740c40d0100b1054060544402c20601c3c0900580c21801264082c0c1d000e0b03020501440074000e0001031400f29940c2c82e040e40382c4000413042d490b00001010400500581c10010341c00c1082030512156003403403ca40c12900303100f640130003810035031914114440c40074040d00740c1c0c064103245180d486100d540c0080e480b00042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 750118750 1250 750117500 750117521
    0x203090d120c080408011a061c0f0b310e0a0204050c160c080d0f050d05152101050604060f1e150309110a050a0317070b0403180e0f040609061d01 64
    0xc101f40c40d0003654a04001101e4a51400720043d500294400702140020004900301a5210340c0f00c1304582250780c4d032200c4041c007902c0490031503141800c90080c43c140146c0d952800946a030301c2c100030015140000600351510650445d00454180d690b40400b0041c0d020b46124400500a1685000c0070452074101400c00d5944c01021204008400882100e1010003020381d440410710800c151103c461454203d1940008807400000c0031184040202d111807402803401c058400d248101f41006950a016480e0800f00c21181130101c81d050000d01009229188621280d403002c04100340328100a00c11218010650101c1d980076441d40c203080500a00080c901c2110780030150214810180f40c1012120107449025061901043c20360f40c55840d44d20001c8000020120148410b10000d01c029034164400d910981d5014200c0c007011500306420a92a0007201c00039a2480412074000003002006602a03000180030601e030056050080003004042282c40c900180291480d0200505401200c0c406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 750120000 1250 750118750 750118781
    0xf020c0a0521030412030608120a03110f03010b032214060f091b0a0803040602071a1c05070320090a061d04091b1e05010203090d120c08040801 63
    0x50521103004902500c0c03844040c040c2c4010b20228003c1092020007810000c980d0900107850f6032202503c03031501c45070002e000c186210000304000340c41d03450b00943c40300c41e03201c111007401c0c0210340c82d045099010500441128510210028200c4000c914100c0b18213035503200807001d52906414418142840c40312580403034030802d00819061020030204902c1604020040d0000c0c0040c4214081c24031400b54400d0381c841075148010440380010700040c80103003002e800810389945090803041d181d0702206080c5400c0e41c03042c004240c25814004080880301c03240000003c281c3e50f10a010340052208500200224849038079140c000101c1c840107020000007100c2420b0802d035226811a118010031820299906504c45020180d00b42904010001486410002e80c5a40caa1700c1000c08840190301080400c406003003d030395181000d41c82030024000a05c06180f80081e8580400e40001c00c0c003000428401e0f100ca204039040303100b00d40801540703500046540e40c46903034510b081d0103821503413002a40c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 750121250 1250 750120000 750120013
    0x905010506030708070f0e0307080c01030e0312040305090d2910080c13110f0301140d08090d1509150507030608100c05360301110405060d0f020c0a05 66
    0x21450441c003964070804030303540c4482e0b880d550700c50121105442a14a042440498101e90206540c20b01c07608e40600811002442002521b400042c103844c8120200d200542040210300391094000b02038980c0160903040280c1c0d0341420102141c1c424041040140981d4003440c20a003107108000031403010080301070040300e03035034070b40b07480403901c1103402d22841600d60311024410805081900031140d02d420188000907201a040321100f00981c801c5026803c28080000140034400b10441c4072144130400340d400d000e2045080d610300ca2107200b0481c000d4403420045100100b00000e1000041e5043d600d0141070104500b01c0c0380c5807014400d508214800103080000003120f0502c20712902c1c04580821b40248010f110240d038203001411083d82c44030400c002080164a08800000b40c0c401001050030140d5006103020480480703e00c1c810b418902c240d0400e402002c1c4c00000c1e6095400b90341045410359a02c111010404005103800801240c0160021608500f00304020400c0c8481500504c10f0350203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 750122500 1250 750121250 750121259
    0x13020c0c011b03030f0b030f070618031101050c120d0b0f061213290a0516140f071506030215120403050309160305030a090f03020d06091a09010204090501 68
    0x2815402d045103441c0c103000c0c0384030000203c3c1c4290032018102d42c202800060342c511620100b0f040ca40e092204690540c0703e04410803040703600c58115803959000405c0d900705941103075500f0001402030214107041000120380e81121017024401d408050300003407000c940e07400003003004001a201c459941440f5030007610681d034650503c1c2040320005102c000621031182d03900f031178a1940841180381512020280c0e080000ca24809805081d070b640f00c2e4040001403458140d014005441006002c400220aa5040601a5600310f42030a1040d0b455008140d110b124082201d40b56004200c2d0180c0000215100740d81c01d00c0e0180c2c80041030724002d0f6041d0881003034051000c043e502c2200c842d44d00d160b11712800240440d1190b4040c42c2c10889034001e171814640c101d29071106c218029003043c6c4003600000303141d50806400065000040c0490981f440b425407031038000503d5140524405004c0c00c3d11118510304015100c01c44809611080b04885564280103660038002e41080c05031259407440c080020a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 750123750 1250 750122500 750122507
    0x60f01030605100302070f080d1e02090a06080c070816020f030a0b0103060b1507200301180f0302070816030303140c0d0c050405030307030e0301050f13080a020c13020c0c01 76
    0x300342c440151140a0440e28028118029880180d0944210034025800b000092500e0000d1815201b00380b8049045007185003241e03500180c1e000568007042c41000110700e25202d80028000b00c0e551410030700c030f45642d0760441c81030600c200e41000f417240c0800505020350750076018030004424001c2e1103000208600c1e601303050340c640e403035100600005c0c1c50320b00410002e00b03250024606c0060180510803c4107085007400c0c680e40200f281101e107035070940c60304201c481c500c5d50448043c90045000b4440300d280b11050012020028901401418240d054201454001c0041c2d40c000c10800703044802904c2031034180750032400c460001f200024200101c80044540f0b165501d03000b4038200240070715011a071414000203003850407089082c0001404001070307036035061000d00031060180d00c1e0340c0381740001c0f8800c040c03c540d00280708444401e424824092982c0c04038101e140e1090744040d0640e230764000b0100503454860032a0b40780303620900351300909460314030503009080e40d001c20b441110040e151040056 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 750125000 1250 750123750 750123761
    0xb0106020109150207080403060c030515150a1b0b0403050d0606020105240103092a170a021c020d0606030312090512160804031202120c030a11160e060f0103 69
    0x40c100c10000320810f50100240d0340101034032403041688914280e926500c02d815100003036103090119680710100700d403e5240c0541c0a50f2480c040710b51000c0038104405030f84a90240304c442408002826000110075000345030403175181504010003142e1440d0034039000b01140d001c0005444500d0500700c2c001005401405050b0241d1704065502214400c40c0700710b404031002503e2041d04140d15081f064000c5024501c03140341449200903800002942d90012444a1050f03031b005d50181030718001141364400000c100c00313950507412500d0035415801c00c982500b4021400501070740c848800b074841d1040204940c400c0044034481d4841c01400c007602c9207807004031114a41d01928640108114141c140c907801c00070140c0b50940c0303036500709550b0b10b41c1b2660041c0d045604201c4144c1540c00000701d090303404202c1c1d03501c0340d01d503000440d14045500c0d915980342d0168205105c10711020f0b00e158000b1110a020450764650403002e920b412594907000c1c0c2c624000c0542e4440e014041a40c1c002616500c240142c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 750126250 1250 750125000 750125003
    0x7061b03060501021b040f1406010e010203071509050a0510020a0e180c0f040b0c0106170a08041e0e10060e010905010525080c1501060302040e162a0b0106020109 71
    0x3420800e540700c0d250385e80031160040c5041e40b0070b03900c20083c0142a418031505c8002c2401c1c0700444110300d0200c0014048040504010341950720500003640000c01540781e1401e0300801801c08240303103070245030080c6400400c0703a00500a008160034044042c0117640a44103064040e5983c00e2184c01c0a01030080728a041e8000803490524480082e10b04003070701e0010308803044440c2c011403078660b84800343c074a50303001342241c0030459442e00d4003000665007070703501001c40b5495400980120030260b651248203204a02c2400b5407101001c3c00c006280d4240380401001345a2036491002501e01100380900c2010207000302c101090f00300030b0244242d4420300e055010f850042c0c54491810040c50100e40401a40e02c5108001400c0810030390005030507113001e0007182c000e420042c40307403803c11140c0c0e45c01408143c000804162040c0010000190000740080d00500d41e20f00380c1e6140b0b60015400c4420fa00004e459a000391040e408200e141c40c0f503013945e061000d0041c2c91003d041d0340c0f00c1d82c00320f0a0700c9a0190 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 750127500 1250 750126250 750126253
    0xf0b01050304020d0519050a06140c03190209041d0d0e1008060d0218040c05030a1e053c060606040314070503060f01081b0102031911010207061b0306050102 69
    0xd006003404000c0e4980d00307000d10104c6d880f00484010003c21740c030035240119038642200d0084400c00c8401e010314085003290905101103464504400a02c1d800b0003000303940d8040d075810242903005456411205803d44c0540700b80080b45003042d45503100b4030501d481101a01c5064514201c0e28411340031b4451060380105807248000d0000b030100c0b40c0ca8800303001035900400e81c80c00100140e90382e403405e5140415540c1031090300e1503d401c01c0e0700c1c945415880180039810100000000032a90130f4006084052001d5440c420b08035420901d00d004c0405920501200798264406488000e200840003101403481d11030f00c07001d01035404c1a44412040d40c1481d0003007010b000510026015a044400d841a01c90071280700990316800645405825688070340132a14040060020b83d0092000c40ea0b40d060b001c84008030030580303400003540d80c4a05050500070340302d5030b158104040e100b09212440c045850300250348a0485e03040000041c60486802c41809501d00510542d19001c0d020340000c58034143c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 750128750 1250 750127500 750127507
    0x1060f0219030e010e0612150102060a050906131103060103050115050613092d050601080f0934030503180108220204091b082a1903020603070c060f0b0105 68
    0x20011741d61400a0b15100e82d00500901c1a2000b00982c09081ba00c03076920f81d00e01c011007190f000000ba00300744e0301400f00e0011500384403c00c80b50660020b02c00344c10050210400841c5011030625101e01d1801c06100742c0c0c140103400c0004141300054000d100d181014107010410b00e5a00c43c01c20965110701383d9070344003084010070100107140040d40075142c048107a1808044070030b2562300781111407141c60ba04400580d82e483c180b1a442d40d1119841d98800c0205100c051a03040a0102c0740e40c034045191914540c158551009040303941041148061401c0f00c00d0522200f03840b071410f40d031250080040100030010078030f010f845562268503014060300d0000030f0240e1800c1808088182030118450036030708aa01c2d594000c0c0002d51080e40e4091441640080c0300055090400c1c40713050084003074a901c03a072030700c9960740c0c0f51444d86503914001d428002c8075649040031074000d031001c00c0a850350029610a00200401c00c00d503402007200c400280c400d035020440c0005c180341e46011100d0450300140051010f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 750130000 1250 750128750 750128777
    0xb0f0a20070c0515070606060c0305070f030318031d0f0d14010216120815131a0d1505090d0c06050717010605090910081f060e01060f021903 62
    0x40005180303090090504503110750b00c0f480440d40380c0c02070151090410800150200c2481001d1003514054043e80c0f9201d06456100c0c0c03002442c0c0e02403a08090071701d220000c0313032404042c085e40c0607502031300c2c00c00601d1000c1e10032400d011b0202c1d080560260711081030719000d403030b080c600030300c501d5688100104550480da5a9488410550703c4a400070310f0159401c000c06030020406581d8201c100b4802c251081442415500c000d01101c40542000202d010280c030092071640c07403a2210000345070b2a2000640000b07940b0100700c00c15505002030f40c01400c2ca040e00b100f40704c041a0040c006641101c828811303a100e4444d036982d0784000711107050000c0d026200650010b034007a0403403504002c403407402c10307080181003440b030801c24800c0e07000c4400b1a0002032018080e00302410b01c10384c400c0f07810301010300711031030501c005448082c5001c0c030128880d80901c150390944069840f14028229100c03518686603182e00029119191010158001d4030501090304017003030011044095080c0c0c550745070342e4040b001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 750131250 1250 750130000 750130061
    0xe1c0905240a12060f06020c0a050f1507022701080d0507061e0e060a060b0403051c110303131703041104020315090a150f12080f04050d0b0f0a 63
    0x7585002e0104030280c00291843c40c0703d40141c8000e40b010645050045292510103864034441c410140d00505d8062010841c50b0f82c0d4505076014004140d0700c4039040000002e4403c11480b4001d0001d41c8009954803901480c0c40c081031162010030031201d40f01860b42c903070751490b9980e0f000c0b91409000901c02c1101d0000280585c102000050b00340e8003450444c02411030103429140060090f401c3d0b9804181004001c1580c1c1c010340001380100f240e00e6251a0554840da9159808201c24039004800c4040c079024180c440d0b540d035018031041d04152604c0c0e09102ea40d03a0f050001d402c405417514192002801c0c28200c1030003c8031301455005101d007212021a40c00d02c070203504002c015500103201700440e42a2901c40044041c03294415100008070603451441801301d00c202c83d0070654048003900801e02981440c521108001500403550320b4445541c01c41d501c2e00c9120399008180c10071a02d0503d541004907032020700380906d03c1039110341d03000d66a029074101100c10300448024520052120381411218 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 750132500 1250 750131250 750131257
    0x30d0903050d2a151505010e0f010c08070c050102061e0402010809070518090607110a0f1b03060b12010c0c030e0a0905130627060f0e1c090524 63
    0x4458041d26071446015216500e02d442c0c031001d031412a880d88010101d00034905c9200c080f0080c54002440c82401c00000078000a19180e6641c020010700090b01190b0b8001d80185000650181d4120354640300ca240107000304100e0310580d8094071580021604542c01410f1402400350202d9045200d035545400440d00c4190141c0300480c24041c00c8008103c1d81c40305084800341d10310060071580a03040c608910f03494110024520820440c07201c1c410790b91058042040046250000484414071080e0309060f19a61004c500480d1503622040001041003140c2e0044484183c00b121090003860031003054500381c030f0050034614002840f4030b080d540041c1c0204055942124003801459601d0303100c240702002c455040d0f0718841e4006075a1400030030007245006038480303900098040c80c030a0040da00000101030f4022002003000d0f444124000b00400b01e54080b16145582000311020070b2480c2080070340d00c1d501d003104a40054600080480d15003020341050041b04000c41161241c03c6060a0a041642 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 750133750 1250 750132500 750132527
    0x41e02070215220e0403090e0c0415090311120309010f0e0306070905100c12110109050a060203010501180b160c080f03030f0901140a020a17040c05030d0903050d 71
    0x111401e11408101d01d80c2c090007000d02182070b00d041400d19109440485040c6a0040766a09442c2d010000041d03809000102220600d003200003160f1120b4141d18101e00441d008074a60800c023804c0d82c08283c1d8042115022171f401414100d5001a9003018410007500d0284815603680c800c012041e0294400c4004203400f032810710f000340f0404540d000281c00c000701075491100046ca1078005100030f141c44a0640301c48011406c090140c5022550b402c80010107250001050080b6040c585811132801e400566805038898255401805607203080c100a420a00a550018100e1140303035404440484c600800e03680324094540c100100111080760004820b602101c01e202c070b881c000590800104007207125040540c01a6031680340000403276906120080000b000c40e810442030b1445c000aa00e10369400c042214405640d034009505d0960724111501c0203036048224007070800042c000c1c0c50f041081998401c50981c1c1401401100032200b9081714080034000f03400c024800c00e00f030b6010b00004c20301038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 750135000 1250 750133750 750133759
    0x31005060307030b0603040c06030c0f021009080c0a2d030219060b060309070504050a05150d020a0819060c050306181003021201050703050a0e0c1314190506041e020702 74
    0x15852134010602e25002503408880b8030709001414450030782c141c0034269400c1c0072032401d9001e0318190100290b645118034290483c0341d0395a1681818003400a046819000c08a011985c0e81103039071a10f00c07500038a41c40c0700b0f110f46480410750300c0300700402e459a02c000c0782c140c3c2c01090f81d0030307101e003a000c4455a81c2400700e454540e2a0160f4a00b5101c03403000d544141c0c001c10180c03811034070b4801400140e0398005d00c0c0254040ca0031003080058203091301900c0c041c20041d100095041c0c45880814410b80c01d039005980e20388a030090741d900740c110341c250341c00c195031045e00305201041009034207850901054504035071042560685000202c6d24590f00399108030407002c641c1110b0707920f4010541007039038220070b458282d46034000c000e0701d1500350190342e801011445082002802000d1541d49564052101d90700c110070560803045007800750303001110017400703840c0307200e10074105440707101c3e1903440004014281302d007020700054061409214262002460f055586001c00c20724444500a512940d03040340e11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 750136250 1250 750135000 750135011
    0x1b0b090c040903020601080c220915051311060a09420e10020705040903030912050301030c06080712020a0c05160f08010902060f0a0918020a030f0203100506030703 72
    0xe50350350050085090084d0040c01c2d4950500c41c2072810190418885402044c2076000082c007420100900314243e0000c6200003028100c1c0d2a00c0881958203840c880410360810041c00544464641c120310341e02d20400d21a079a00c25094148101401815081408500c0d400010000300600540b841c0c540520f0040f80170000d007003a46079a00070034001012100c480d440440d00766010360490103c41d8418030844024030722440c09000255182001e000e003600a0703494102da0030800d8001c0e041041055400b05c01803c401d0344c84100201580c00900c0261405080040c0001c0c05074010b401c058040c01560351480689034009805601031350100341c00c03408000d00a00034a000c40c40c14460030f40c4003007428480240c4685805084c4607000645c3d049411540d00d0921880010307a0fa220448441c075007100d000c03d840d250001d1090358000020760140610000700344040e0013110042c0d00801c00e175880d64404002d910154402d00b41203000485121032050b269180c14070a5241c00e0303000d1075010a85103000b141c1e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 750137500 1250 750136250 750136273
    0x90c0e0c0c03030106120501270c260a05070c05060f0709030503121828020f100f02070e01050d030305220305090f04023112030e0a061b0b09 62
    0x241d0f52003680203070001b5002100e001140c0c0c030540905401864040a040d040c070309050322a461001200d0301d00400d0079540c8440400f46070080607021140c0d0310254000c082c2a40c2082006000e007000c80c5e640d4881450000000e0b0360b140100c100c035901603003000003031540343d42e0740c100d688595102400304000d01441030740000c00517a0400080481c110b8a403074022050070b007447e000031a00003018030010b25403c0030004990040000c05454440c40c030300d05030b02404490070b00205039080b0a510207641c21280711400f007803106c0c1d004400041c1c42c01566084400140c0e4640051046407400c0c0200b5601602c041c0b040b90110707110740c00840d005462445904443c021007002000501012141240841d201207145502e40c90407514454400c801030341c003980740031009205200030390041001003c402001d241e04003900f583d104101c1e005410b40b89a020038098803400d001c0c08440b40000030038070a010155000c2881d903c605403500b94400700d1811010a01034950703e8001647c00140000d1961083c0c1d40c2500c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 750138750 1250 750137500 750137503
    0xb121f030b16022b090806072c090907060e040902060d090615061710060e011206080625020c010f0e03280c06050f0409050405030d0509030319090c0e0c0c 68
    0xf484d44100d40080720302d200b10400c0c0602881e80c150f0141009400c002c08101920f074102e802d0140756660084061104510000c6c0c3c0840c009042071030903000018102001221103000030700a0584280b42c4a8004241d50307241004190354503058001d4102e00d0500020602c0c0e415508020100c0b8071840001c03030340140ca44019682040580d10000014400c5d4101e505440448240d040e04025880001500e0b2801c090000d000111949001e504008a25120482202082d80300202034070b0030806071146401c01040301d4944110402801107a09417401e4400034050002401030a16401a1540100084000300580f13401c400120f2068040c062911130407040d094880345100700c080002c444199018443c108400d40b10000d803c41000c0c09820080454004000003d40f0304680050101185642d6030f89050781c290700400e41007000c03050815003400540340000c0040d5102d541003001f501d409064521240302601d02e14100904800d00011050003550310f6400d2003030f07125a8800100c1d141204070107180e0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 750140000 1250 750138750 750138793
    0x1806250f1115070e12070b0a0c061109010e01030b2107170d020105101d190c02070510030908030a0203070e060d06080c0a180c090b121f030b1602 64
    0x2280c0300b03081c0007044601c540001c81065191800d0300c01034041d640340e074002c540e581d09034010680951004940309180c80d201c0c16102030200d62001040c00206c009400307180e042d0300700d08160390100741410341020031035200f4801d2820034400240070444a10301c902151505104114002c0c6641c0641c02001c03c0c0748107608040b40843d10500000c0c1810341000030024210b504c0600100b5070360707000c00700422010144141d1a07030046400040c0983d6a180e41400c41d040807401000380e1622401e00c00d203901c0041d004500e1004880c0b05480c503008101001c88103c0803990105402400040c3c02d2000c81c03120b544503130240d9402402c0e8103001e441c00c65918005803103074000c0d558260010303443d03003424401c104003400201107100d8165100e601c514100f500466166903500c07114043c4644e9020000000e521804091000f0020840ca0b10b070340d0b2007a90031144602c0402c075401ca594a41341924668012100c061503000c40b5042510345c0d4040e250344441802a400b04035007001107219140c1c490400900480c20f1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 750141250 1250 750140000 750140023
    0x6020c0a03020a021509090c0f071e03030509160b0c0a0228050405060904060207030327030e0d0302030f1e030a0605091510030b1203031806250f11 65
    0x1411400950320410105c28988400c140031000e0610032550349881c1c2c040501c0d04001d01c48003440d00c1d02031a800074a07440c01408000382501c48200910640b41134031038240d20881b8001d50b8144204da03130b07103c185c135030390450b00e2006c0c0302480c21602d0800c054524400a8031175102540141d9040000c00c2d000685c0011001c00b1030b038407480e01014010965446681c04600500c01958103005501d0140005854900c0040000c2c000540014020040500c641d00c00c616480d0a1070f03840706c00040400c0707407006a5030b114104401280c84001c400e00e45140860348040030751b45c17560085151002041c000e4099030403031103809505013500c0164110900c0014041c502c1403a084000091321031a220030070524020280041c101403038190b40b805e42a40300c400c50310b200d21595050101311000c1e00c20120305c440c4c81e0140c0c0342840340004014070500c0d50140c142d44038120301c0380703080700c503a0348600c6005180c8060301401e00855030403800300010118019040300074408118105141c00d4810001c510741086076a280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 750142500 1250 750141250 750141253
    0x14010609050117090d050d1506020105180703050606060f160f02330a2c010306050616170906070501090b10030f02040b032b020c100e090406020c0a0302 67
    0x4140141e5901003480001e81c03c002408058904208003410703103c00e141d008100130006e000070201c031011120f801a2081c203200065104c0207681d504002130003000309803021640300b000690410f00000c400510b040c1a82e4024001e00010f8442c80c04014540d0f019082654201e80d083c480c40c2d0703494041c0000e0020041c0a01c54140f51030707032544100044041c810307108941013028044419002e64800180008507154415560354500702c008050321200075086152040c41307000728003024000d83d000c94404a90400307072004d02c616519030081041a0055045c0412948640d0310740c0700201e50301c030b82d0003858900e60407c0685041c2c50342010596540c400042601d2580d100c1c1c00300000c01019400350b907840b07503004404a00705815950766100d54950301c2d5010b4881c5d5142c01007000540e0f0107110041c0860501c0038007441e08403200c011262900d10741038000d40580207184181d000350074443d5074805510a00c0e500c0151307015a24042004da15800741041d14056070038000c80405ca9010048850a24000e40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 750143750 1250 750142500 750142517
    0x60d030c1a04170307050306040c021f090203060f071403063610080703060b040b0604150306080a1203200f090f030106030203191401020a08010801150e0c0a03140106 73
    0xa22816443d00c914110001e11400c10400c00d80f260b000301501e03000b02088a003c00d000490900803490484407564034142c00c100500d030340300c140f40f090313001c035031014400c0d01900c0303c80e6940e5040803806041110007202251500241001e1000f1130030056600c10801080c0c2c42065080c4815011449001d08030888502c0c1203052131032303a4502c4080490b0b440030003a40c0f04400d10303044c4a00c2039202c150b1480020540c3e911050048811307940d82d04015580100074010070740b603d9036801005c09043d41190040b0200745840000b0a060b0000302d0701c210300a40210025a05c1c001c0e4040842c0100804203408040003500d8012440d03403c0040700400d2510a0010226100d40e41c40080195422009040302d209138500917003000141c5010402e076890000746e00a15400840c10f0810803c82c40116413190b205500c00650610032940001c0e00074141e0340d40304000c00c884001489510740c214624010388142074081c10000b51500e980e80000d203200656468007281c01e14404150740c000312000e0b01b0900210b407030203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 750145000 1250 750143750 750143753
    0x1b080c1005041a010b0409090c08060907030c380d0507020f0c060423030708150f070e1f11060112050f120906030402040b0306100906050d0b060d030c1a04 68
    0x90f410010340700781029080050754502203603014540b041d4482c03429203907150442e101c203110754a2a0200100051802d5814600d44500c006032150700501003119140c407646030210b2207034000765860102003815a00400c000d00884c0c6032010a210407880c02c03490750010002480020458064140141c12a030014900051118801400c3c260107545180c0680c03020311081181190400a07540d031008840e6591500d01600d501003824405d0030b070440b24441c40f4a4050000c2c80380f01c05a0b00344101c08500d0903113029111118100c4050180d80398442d480792081070401d204100101c60000d0300c0c6614245001030742d113103450040c00c0040036403008502c0e206c0d44025400348401884034844481410014005001c8c0e92540d00c500d601500601ca805070700c020001404644490340000d10100009045a9007481c100d1007038803000e0b4583c003038a1100c6081c80c3c0001110b00380b8808030140d0315489800c01c030070b80d5160000d10100d10345124082c0c0400c0f00c0c00e618403021800706c102c3d4501c404104507481d08945020f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 750146250 1250 750145000 750145013
    0x150f0d12091a07050a060c02161706010b04140f03010609061d07030c0c0605070c060203090115060e03030a050f0d02040602030c010b0307230d0501050a0c1101020306011b080c100504 80
    0x30750b000c1c82403000003080b00c0c100180001c1744800b2040d0340f00000042c41c11284070101d1502e40446803200400c00301f04008122104104503600304008000100c5089a0702c0340e080034082e0090b4883d01d249074000188105807841c08818000d000d64016000003109030703031000a542503924903400f2000104032003144850a070002240e907a408000ca0800b400071445a2000034481120038101500c183d641d01c01003500144145a1401f18581040c01552681400e0602c58003c03c0b41000c48c0b08524100c038000103c0760b004a10050030003800601441c00c0410b4408295400e500c0501c1100d40c070744007000100c00c00d03040742c4060009490154003e5071280300001420b8215006100090308c0b9512410041040b5861883d43c285150a03040300100300310b103030350041030710030691080082c803c0d4200750402c0220416035000d818855000c0e500e4019a0038607452842c203d02c421b071080d40c0021501122940c1c0315a00101410185118043d031601c0c100300750100c0c9041c203549110351850242c8603010701c005d0050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 750147500 1250 750146250 750146279
    0x1f0605090c03010e1b0f0a09140f220906020a030209100801031707081306031a010305010e010b160b040f020f10020c1201061a0703090e150f0d1209 65
    0x864003603407442c550600d03a010b50301c620000c2c2091701a0503c044000402c1c052030040e00c000103401c805030740d114008424081c0120303e036409000d025174803c07880040c2925103040c58212a4801a049030100106040020400340074411040149a120983d0f8000100d01c0e00c014456115a80d0b8010780700c00d00d84081010000e138010001041201030b070700620100e0203034504070b6042c61f00031a00035a61241881e10306000d01032104020031061419400007003c58150b0401004520341040020401c0d401c0001541103400a001d2810610044401440081c070040000e1030243e040000e0b19031041c0e4075030b48600302c0c00800c8030205d914840240305001141003544005001400803268800020841d110096032150307100034480c4036400c9482030181d0750707070213510500141002c1c1101e40c45800c100c05d01c031680d6510421013140000c03c01b800c0020740610107109a4028007120506400e00300e1500b041149546928560b42e07884002503514dc1c0024240c800c408198245680360715078000e213080c903444140038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 750148750 1250 750147500 750147511
    0x303070e0a06020c0d0f0209090106060801080a0b01030f032102090316050303070303150b07030306030b06030114070c020120011d120405120120030907050a0f05010c051f060509 78
    0x2201d26020b20001c1c0d00070030340031000581074520450346403c0d4100102c06081204010f900071241e1410b201a8a0041d00f049040e100c4030303202c42200c0d90360fa1084035554104920040c0c6983d80c503600600010703e040c401401400e010389802000b945c12428130254a25106141640da60360000c1c182e100c1d41028040c031440c80800386150500c01c3d141a0200351680702740d6900900b059610751011200f10070748481440a04400e4480c6901c80900d0316014005203000d02059a034030719100300041861805004411040c0c01841410a481d12000d40a4070040b0481c03104a0512104910107044c0171540c0c0354481d48500f10780c001103110032040346510700c0c403408041001c2c02d0743c104e04442d244600c02c1004480c05c580040e14041411a4181c01311801011803150007406401000d84d92840444400f0165026041b03080640303140e587c0d500b040242420340c41c850501c0054000c0410130007903000c2c0d4800d500c0c8501500a642442403601a0740034004a0400f42c29900355a0300d1045c4168100084110b5102 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 750150000 1250 750148750 750148759
    0xc0a0525061805160303050a32090301050109060f03030f050c160501180303052a06010303200106031109132406090e060c1b06010303050d0506040209090403110c120303070e 76
    0x1402c3d43c4001f45a4400ca003604000d0101091034240704a015200d4500d120044200c40303251040d0122184c4107650269040394440c2d800d00001281c00c2c04a4400d078002c07190a40100200c261859a090318003078060109003050010500013203d0390442030100600421111110018482c00d200002d400c003030586642040110f2a50404d10000b9009011250702c10081b48103c074466400c0c40300c002041402c008014102e009074000001015044006002a03019520341031600181040040e8200d4010384005840c0709480c1c006078130a030410703a030115000510007001540402c107584411350f02501080f401110700f8121180c13402001c1862007150060010803006000301d10391000420707685d0341d02405280004200060306911905407201e40041d003500501034514540e504d08001d0007540190311844542ca04060000302203160a10031a4040c810062852a5503140c40e1400c07a8a03010001440300300b8459085080c50a55852890b0128074440d10000c40d0740e460b0400000b0600c001040095005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 750151250 1250 750150000 750150043
    0x41d0415020a020a0212030903030d050702060919060518060f070323011a04150203040303020709060b0304170405130e0f0607020a2904050f01050c0a0525061805 71
    0x29250f0100b81c502900f5011661400305452a201540c114440c90728015414840051054114440d40e000f82c2d101e0b00064003510320b1035507803c0c1940e40301c4642581000d100403e4400780700000b01e280e44099081180c010050405100d02800c4500c1c24900f41c40002c0481d05100c00c10101381d505000d0f14103910428010f860300b50003d50100c400e803000c107000300d003000e03280c11045100411145e01560024540018001c25440e42498003a450368818041a07005004e081004502034596000d10000c681031200761926540c0c654456100192194800301d001001c1000001803e0b603a20341200c0d2611030140307000500f08584c194040c0392100c0030401c0001e5420101c10030280d00d80105e103041c0320a07007081c2818050801c5003a50311070100080107900c01d404410050100744140000c0703112550002e60000c006a4498130a40a01da000700022100002c0b810001310780b01b0b41e18890b01d84d030400070b4a10b0803600c40c0c0700d40c0c0d5030b2400c0e03403c888003039142032461070141303820b1100401c0130328494040120b40050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 750152500 1250 750151250 750151267
    0x204240605041d091015030c08060412110703050115090f060303020c01120b03120703080f010e1303140a1e050c06042910090b0105210903041d041502 66
    0x41d80d5000c04000f5083c04050000924040c20034090802644124001000b038100c160540b10088a41c0d804140c1e60309031001c1001c11035400015086025a80000c10f803504510061f0b0102c946000d80101c9002c0c0d8010500b002000402c00d000703294500f4003801c0030030f05050034458000700b141d60046a0906581c02e01800f0404a6000300f40f181840741d0070303c0e050b189102240140800b034013080c4c803281e4040c403030980d0601111300700c0d6000d40540d51299481602a031103108100d80c00440078000c0c4203104106c840414003d02d07101100c50380c100e1090501d070300c00918503684862903400c85683c0c0f9020881d0015507412220340c0480c600031809881c203140c1d052203400c1c0760340c95440400400c014039401740004921540204d4446442c811605440d04082900d407150318592442c065218008000b8104003590b2920b40c061415211910341c00d00c0c2b04010042d60144034001c914001e4514115400304020100da154100c000c95085072180c00c0755240b07241840d180c92944442c22501740204507105208141 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 750153750 1250 750152500 750152519
    0x30e010f0c150b0a030503040b030f090105060108061c06051801060f0605160206070204051608091b0d03170a23010b120612030c0601031a060117090a020424060504 72
    0x2070b0001d100c5500081c1d840f10100400c82003001a00060003d00c000700e13000a05400c6140254800c043c0a6a1010140c82c1e0020003030070b0360001d480c1640410312030380c0000d8050074144600000040c4401c40ea900c3d0443e580c82d044200c400660f10701419801103018040860740900502008009415031803c442d4030b4980010715601903501c094083c601640150070035503036420240d50a0030f0b00104104031600b0519501c0205991103170084001c80d004200082440700c02245070111784514091107a191100713201003151810840d0800c4080c0140000c000d004040f003c0c140318440d204c81e000010f00e020720391000c3c085607014940340c41c1c104d280d1040140620303110903050b0781c0104800b1345d90201039280c4c00006611452020103038985ca03c008290a100034000040a074100d0780180702c0b01d0520f40a0b00013041145004443d50b6006c110011741e41c181d10b86e41d8a10a85d03010582a090701c1e402c0302c4590000341501c20950034440c2c4a9080b04514044ca0135040e2840020013180c180035142904e0050603a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 750155000 1250 750153750 750153773
    0x110c0603071e0320030612010c020703060207051005070f090e071d0f04020307170c181309050d0f17090d0f1206030501020a1b0317041a0103030e010f0c 67
    0x52201088034480800c2d003602079000356201841c10a6110301507580c40844c201d2640045482034420501e240b0250084036040c0700301800d02c1c84940c040c203030540c11502d130200658000c24044401340310b58440031215100b5449014011503d40da2034010380c5106440050480c80c45800c91078008980600784403c1c1ea400400f0850042c00040c5c1d1500550380f03070000030ba0000389040507589c0241c0000100102c56a100071408144840003002d201161260340501c4001d0065414410042890401c1030415240480c101490561240c6000c180e50000e99502d0f42019190745101e00801c660450740d10055410003200380301c00340d00c400c5d10507039842e250909580d1500b5a4920105122140d0345014850344900301c0e59801c040b0960041c0144ca80c2c0c0c2c50058002d5001e007001c0d0300000c00c900500401440c4040c1903882c2c19030582d41d058550300e09584d20700c0c0400e2010303008507589180482e4204d2102d10030352401e802180a0b0b01d4001d080c0c04041c001404a202c0841120b041003a81040b0320002180107144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 750156250 1250 750155000 750155027
    0xc0d09050a18020d06080f1204030b07031107050f0a030e030604020f04240f0f060801060e040f0b030a03020c10090503060c0313080f040923040b0a110a110c060307 72
    0xc00101c003a024460b402403144111480100c0d050500110700d80ca0000b50b1009000e48001c00c6801242102c1c500c6203a6000703d000003070220514a0208040078441c1e0403045109400580341850a29160794842c50415800d0b4451401e40000b8801c406040d00002c04000b0650160040c207607514080d800112005881842e05114a039039001000c20001d8000d0703034980c0000d03400c0701d040d10992038004030880721440d44680d03941d9007012100403641074403c2946504803003003500c03404c0707080f5514400c10020f016009445155165a262010b4590f03500b0043c40e4030641c0a60050300003d0640420310018803080c000903403d018182a0803c180e8400181d8107070311080702c0d220b60303491351520506440521049240645141008100c4c80d9505e28114003e0003207a030850800c0112504031204411140107080c1d0355401c1030b100d000054003041c0270704500ca40c4070000040000b103428400c092106241c0103500c01000042d90440071a00c02d480030041c04104c3d8a08032509401d515290310005c0850804145 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 750157500 1250 750156250 750156269
    0xf04060b12101211040501080705060d1e0c17010509150d1e2109050f0607060b041508010e06040b06120c0a2706080309100903080f0c0d09050a 63
    0x2030400020a514201601c3e103101061812103190a1041d42e6800084401303100720b1421000207500d00d800600a003ca8601030714007428100e0f1680807030028165069003000ca403c880708407641070009441402c115060586441e82004c49406841c1c03003555058020382c0c015000301060080c1c00721041c1071240503210403101150006035501d001c25460021028600141242080307040c1002802540000540325003402e408039282c10500495050078588140c1d9080b10003038806040382d01302040204022401070070301141030011070f0082001c40f40807040b0980c0000e4131200a1094001c280900800019960024010303424039441d00b45810070b0180c001481040207d00207081c2c2c40c2c0c14886511015801010800560790350f40b038803030b030003021031403d160340c130a1ba0010201910690300c24501521200b000550900301920284000c558910a181b17050041480300040040d149a00900d09088040d1855407100200a54680f0300100710441c4401e00460784d505101d181c650114010482d0003010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 750158750 1250 750157500 750157537
    0xa05060f04030b0a06170c090a1a0a14011e12020703050c0d0306170619020702150a2a050a0611070804150806150a140c2b030c090b03060118030f020f04060b 69
    0x64003c80d8240440d00790082d010032f90015042c03c0c0741150303c98100d02a2602e803042d44a180f0502c94074002c0c0044007020944544921280318003950291548038407900300742d89070021650b251840c00ca151030807032001941b5402d0610051036000c4004003040e40907801000641007440b4103415030070781c00d485108559070102c0c0000039503035001820a28407480c01e1016650302c03a0004010462054910040c11442c0744c02840c2d94001045d1000b4020283c0010142c4402000781e82c8000c090080c990101d40200014031120b0086101c0f54014002003040e9181090300500b003510243c040d520083c0b43d148a01c40c01d80080f84280007800480d1100c0506281184504000110021040c010f49100800710f10850f0044d00e000e000c09110719194154611051a807025414021001c4c1c420310039100002507031002003013061410784c20244d900000141828000220254148070141c2c026a0054607080040c0302040c00b0746c1021135121101030b200b603c0c14801a03082a082d240e4910429010707018100c94103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 750160000 1250 750158750 750158771
    0x60c140301120615030b0a0c0801050105271c12050c030d0f1121010509060109030303091a0c030106030b0109120b0711100b0909010b0a05060f04030b0a06170c090a 72
    0x40c1e0116001c20040e50a401139182c42e420920514803080740c01580c00707481d09490a200c00c0c01a480241281e1050f074030702d49040214201300920040341c4500b030b84007550350703210801640e49001049117088030050000303020842030300381503500340104c05040c42030200810070326051503004003c84980c2d5100341070100d016040ba03102c2a008009403001d000c0309080c040b540300398006078000076078842c444190500042d641c80d00204840c565090300d4082c00701c2c258440c1000040d004c0d41005150501a5010003880f00400001e03500f034060489510540c004008014442c03076405214213200c00c0800e1030400066820725034200c010701a4003101410101c1c0800005645c0ca00c0341c44c04006941640d81601e80c40c944401015000c1e06c2c00390b9031b86119202250000703001c03a45c1445482c004000040a0504151070070042c400c031a441910b0704640c0c1102040040b0101c0d410b5400b80340900e80b07441b8009141071816803044180c0e22054040c01c403a0300030011205042c1d550034503090b00702000200009100005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 750161250 1250 750160000 750160013
    0x617071511010c031a01031a04090503040b1605160e0406050a02070c06110712050312040f0b04030c11010503100b0f040314011d0a030c030e040e0f0604060c14030112 73
    0x10007400681e58201800407460300c0c0e05030017295401d00a2840141d08001e203030015070039920754070b034180d4241018400355085481d10b600004075043c01402600d01e007648910460070190300c0141c1c460b10009455000da0100001082980c548100300110b0407a040d041c04008003482030041c0024140c0380d115004520440c0240e4101c6400716400500d0765095640c0345006002c440202e85070960394020900300107140400700004038030203544140507500d00980140b255150040140c410345503c0100503001c000030309200d1409003e180603485000d44141140313014000700960f01000c1d0304200e014001c0c04800c5102055400540c0e0700224055220424410891100d0159500141040401c040038110350041035101d40000505180c030800c00540b610b100c6a954880320000070700281c00d11081e1008a440380710f8500f0f082d8070041c03001c00c134484c940c840c852412002c9600c00455401c004103007c1000800e204820b4107211a013005102c080f09000725079101e00051148000300080a0100c9042211 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 750162500 1250 750161250 750161267
    0x15040b06061e03040c0e1b040312090b07060b03100216030e011202040b040f08012003041109012c130b0c130608071106010e0408070f020303040909050106170715 71
    0x600441540c4900c4d01d030805d030901c0503061103001942c540300804a014104039007000302c0002c402007130162810346140d032207d00d1038910210300d108106255501023059884000100aa1809100c001c2883c40030f45081500f007a003840c02d20b4031264030410420141400c5501c3d404d00c640d4040c01d10a0142c1d2120005807188082602e0400946100050116240c110742010700151094070400f180415251400c0301c0c01c03074826610f400035a0550f00a41c1c000c11100784000c41e401480f03086d80d00080c0c0407000100b0f031020001e810001c490b014500c0c0c21034140a407140c06000d0b4030b000c40c4a905140c200140404100c1e0158030015101154400c000b8640b1020f28084070b001341e03e500c0300c00548542d5100d0040c1114001e8403010001002c001080d8000f240c0068028140c824600c0c105a2507180d5680d0b18096070b0141004031107400d414100c0340090380d170502c0900000c1005210100d428916443c01d182181c0e40c540150352000340c2403049003110040001d6007401d48101611a2011402c0307000b09640702c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 750163750 1250 750162500 750162547
    0x50117090f030c0a05160b0f131a0901020c0a030c090e0114040308090f030307080a0504020301090c03050606120a1e0212071d090f06070f050c0a060e15040b0606 71
    0x4800503001d00d03e40d0700000c141c1041c90081c400c0d44c1500d00200b0002140510501c9094440c1900344510881c0d00280f2000f0300d5881c003241010041103987d11480070300c172181d1506141425401144009444d40c0500c0504400d0030f08403205014981103944107000c09016000b4207040f20341d5a80806513410096000c030030300121000507600c0c24a06840c00810441d0110703040314060040600c000481a00001524002e4400d0745601c08a5070311814004000d10008000740d9040d074841580d18049490700d03404030050341c01030001c0c00a07440d042d03050200d5004503416031507890f0301200e040b070046a849c0c008200c0070f0589002c0c3c3c8020340c503140001080d11401c070861101500071058001184440b01ca0030540320307030040d1034126083d43d62440e2a40c440401c1802008030f508160001545584901e128071440d0042e400c0041c10f2030092a00b040ca020034440c0c045945903a5007111107005d820800c00d044520114000910380361074903640d0102d10b00005000c01e0b0140d200829654a10505482d042c203070360 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 750165000 1250 750163750 750163753
    0x911090d110f090903090d02062122031b08040e01080a0201030c0507050d0e0103021c061412150a06171b0a050f1e22060b04050117090f 60
    0x80d10503040c886211040480a14881c0c0c0404803100d01e0b034102802e0b11485100020040e608002d8114140044c2081c0c40750100c0e40302004200e82c2254003100070045500741040700600c0042c0c90000200c801e0b044080f80041800c00c901007103180040e52014982c9407021807520b00081240d02854040c0c0c01c1d00464100701161041031002041e00000080c828030f01d18002d9a00b4081c1c140e10007003c0d1401d11540e00003a00c1a0003859861003514003580c0d40e003171840410f1400510300540680c0e4503461401c07001c40040b038a03807211000c0181010754080c090110000300d0300c1a80100d2243d07541e983d82d403d0302c0021103490b9050700c00507003c001c040d404000101035518890041c02c0c06602003980f0b41e80303009600080c076419001890100d0504507104010f54101074185410030101004220040d2050740c54040004809900804140c442111501180304404d4042d082d0b110700180d03107030a403131464001107004070083c4410080342ea0302455011400020340c4421906446031105072741405010f2180a503035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 750166250 1250 750165000 750165019
    0x1d071a07060b0d060c0c0507140604030b0601020a05030c1501080d05120c070c0303030504031b2d1b0609080d0e0d05010b04290a120201030c11060f0a06080d09091109 73
    0xe00c0c0d0030200310304250b4400c00c10b5423005038940e48001a0152410002c0307403c02e50510041c07002821803142c1c2da420010500480d0260849035a609141d9070080b0700c2034182ea00006022000c100382e0144440c050a103400142c02c42e200f040200411900840760494211031300080810b26071070800048a0079039800a08440700c0d00c4d101e080140203044151001c40c00540000c810800d00032284003202844c60b400280403201000f0341c884400055109990107102040b454407200004d0105003020111844451040803231515001014010040d51b0340f00070405e80141c0d484540013588540f40c210070b59811200300208101171f0410703e005009500e00740780c0052074020044c0c92802c8241629024007049408203150002c101c0520005086901c41d2807400041c8030144401036010742c00c0958000420f280c5400000324492146150000685072089100c00c03603024802014414011100a01518402000c03600d81c25040142050114030039100d5196494181c0b4521650010882c0c1e0385080c0140b11642 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 750167500 1250 750166250 750166271
    0x110102030411090a0c080103030513231801030c030807141f0e0309090a0f140103031101050106080f070c05120c031803070f0b0c0106091d071a07060b0d06 68
    0x42e20020b000341c00f4071403a050400902c0c0c1000c9030081089002c1c0c20b0390f441d80540d20f1641c0598040d0800784009c1c00c642e2507401c02298a40e00301042070510f90b0384242908030341441105000c0180100301540340343c0c010745030042c000300315441110001c0382d0b80001450760710102401c1c070702c2c0603884200128105000b000400d000b403c001d000d910031180b8071004100000d00c20001d1840d42c80c480c004410f0b800000e841d00140381031400fa849421a20742d520008a83c0700c9424a584001c84001d800072804211200c0c12001e401000b48600c0d030145c6564104031b0b0391410104000307010800014512020407101d48c0d550001c012041c0814840525186612a00c4840c3d8014868883c1c201d0148410820303142010320007940ba000078040e040f51440944107120354140980a0883c2e44044941581e130f6403100320004805030301d881100382441c14008005030800c20028043e08102c025404a60403542405610494070011800c8841060340110005000c0c50414007142500d80e0341580606202d1901c40c2044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 750168750 1250 750167500 750167513
    0x60518060412022803020f1f020309010b042c07121101110610090e010516120207020a0914060103140601031d0d030c1106040c0b0937090506030d030c1101020304 71
    0x444c80c900c40c0d02515081182410501d540300d401c07101e41109200300074850712440d02c0a0b4025900030ba01034002103900c401004c003040a0f81d60207070781a9040c103040401c28800b00551045420280d11540203004014600311100e9562a945080541115406042d2084c035a00130001c005441f0400c40582d515803030440d07075070352a8105503c100036100b401d02d00343c0c3c41110b4040c46550302c0762085201460b04d41100c480c0850b00186148400e4000f158200f040d030000d6a100d21822004000c1340c00301041d9015902481801c5a03070203068181458101a0340e90882224814410f078002000e20307000075544040c0c2206051103044003c042c91a002d50b45182e10300c0d99040e00840c80000f000c0c2c40300d0001040802074603580e010100d90142c00c280144400b4030510b0340c01001000454401040c0c041d045042d40003101c5540310540c1e000b00c810032141040300000d01c4a1908400500528400b0490303460140c01003602c2e801000301510801d07644190b80c40c100d0b0700510040c2c00c1402440001c6440c0d150a15086 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 750170000 1250 750168750 750168823
    0x30d0209133308071511010f02090a050609130b1503090a23150c120a1b030b010504140418060b010810030f120912080706051806041202 60
    0x14460100002c0c141c04584062a440c00850380540300500c2d9907481d025200c464003041c03015000422000c60003892900c2d2090180c1c102404990070f006075243d5a1508100400c10160b1005004030703024800a00b4643d43c010020201484100011544501c400c0000e12410030f808210700e640c840c04004c0c4041c0810020b00b40b00340701d1182020980980c8440c0e250b4500c0d000500e0020391a40c0407013140c0c0d500b03801301551590405101142581802c442c490429441c4104440e1190381a503548039102d000c200c1e43c0c1178110b62806a0030f0030010340720740d000000c11030311441c0100c45100340a100d2034492a01c45034005542d8078101000700d600000c05181981c0541005c0b10194001240c403000301e9a0005564040800c40343d110b40d403000001d01c15641c00310750402988501040c400840000900c2107103800403030500718491011340350794400502d0702c10704841c8043c0200c0c0c000c6130003071030000b1002c0d8002000ea411540240340b402030324240c5e41e4128034002c0c05c0350b00d041c0b42d5181040b06011804a02120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 750171250 1250 750170000 750170051
    0xc0112231f0302060708070507030f0516090204050102070506090307030c0b07050115050127050a090e480402040f031a04051b01090518010620030d020913 68
    0x5200030010000741c0c261840325500010758004401c010444c00190003400400c8001c0c860700c1078a040c15900d4954030700c0226a00e2080d2880d403c00040c040108000c1d0075403001510742c9000840c00d01c2e0030003000130f5884615000e918044c40d400500c0d001030f81e0341080508000c40d84200c1400c41240c480149880c070b0780104400315540e40c201919501c002007000341e14000c1d140180c4d40c0441050305040040d6a4191910301c2207800d8507100000325803521003401c100c015080380701001c50f5503640c03405450f1a151980e00b0203450b132001d0841c5422030345030b0115914013030605415039403240c40c00c010001459804402d406540503100260014040740d1040109003102c0c0141d00c0c0c0007000c949010200c040102c1120003c044c1d4102c0b10800744110002404090b0105041c5090440283c46401140c100313000b1058118410342042c00422075140c1c0105d0700590400320003a10841d0b45000300e2915601d000708008054100c0c1c0200740500780e81ca899641505100d2080f006100000310746140700303850b0841008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 750172500 1250 750171250 750171271
    0x10f0513091b0801141e09091608010917031f151e0e04020c19151b0503400507050f0a09020309010908070501060608100303020c011223 60
    0xd01da16034a003d06980e904a5904a11844030000302c2010014006820101810004101c000000c103540b034486038903120750403071001030000742e0000300b10042c0408140e010001c168100304034100000c4d2081e2504100b03102c401d110a07140d40f036600d180d401c3c940c060404203500c816820400141c0001d0003550403003030007403901c2e0301540144200300c42c2c7d20001100c6094002c075600781707041d0019003000d40c01400485d8040081d01c5400c16441c01e24035540403845000e5616080e00200c1d0109400c1d948100c80d04113450031403550b0482d050a10203000c5010040c0080c0648011030035482d007808201980c04402c00b066040d10b81d85640c10660382e0342008065600307031014812440080381c1410035046004002000810640441380350a1005c000395100826050a554072003950700001034000000c2d10080388614004580a82001801003c02200500d5460143d40c03640c4c0401c00b294000c985031080321720a280c9610500e1204a030b40020705034440001148001c005091000025411846401400e2022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 750173750 1250 750172500 750172541
    0x60c05180f0609040f050906010e07120906090206070302011406010e030a0f0213050c190e1f09030c0602070e0c0c030f03040c051905010f0c11010f051309 68
    0x408660a004400c20a40a8004510031824515095042407421100140110318054419001c00d080e02d6420034241009902c62042c80703501c0340700740410b03405403050743c00c180715a24101000615010b103070b02c46251681da84109030024003199030040000b80c2e401410803541c0e803845241c001d0081000465a100c20100500403070460341c46050600300f00ca40c01801400c0f04d81450711441812480840c080380d11070704142d0b00032003141090041a00c202c1c00d01e8009a01d403124030503401041040c0d808540d04210990120240650380c0001c03c00f8a816500c0b0301038194070710040180c0d04015075800c083d200011161000916641c0016410705072012076881d40d8841e1035501886006000302210101260400c0c406100d440b8036450186600078007400402d03850075504c44c0030030350404042c2e0300c902c1110020803083c0701650304140c0c890000502031800d90329481c3c0640300c01c480102d520f881c81e4100800c0704070300022a48980c06036201420490309900f00d465584031400700506c03240c90440f50006002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 750175000 1250 750173750 750173771
    0x605031501020f061803160c050a0f1a07020112090501020301081902090424090b040210051206060904141512060c04050907110f070306050a020c19020612090a06 71
    0x106051140451a0006000b19202d40c0d080302d0417100c1c002560f04103403106005010102003484210301406002d00072880c641c508100030310110b266290040481e1511000e410020001c1c601307444036103402200c519503165041840105c0d2070383d0603410031200030360901d45c9807810321006600550490310001d044640014090200d44010b0300300c8480658490f01000005002c0b40046214403807000c240130014411046d104090742c115070785140107450030841c0108010440c2480754882d011204c070350a001d4200980007050440d410402010035001e2507011800070051744490300070007003210b403400c07240d01f003860701d0106001e0703802e0407032748240c850000d1949440c9203010100c7c07818000e100c0004100c3c5403d09080a0005192000e400881088103403580d09050690034804130040c0b5040070040d2041c1403650408105940018040001a510400a40040500c000f1308807503202a02003a0350040040e038000a4240d000b0f9002145188504000b008402c1a000c52a0395140f80b203040308100d4403450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 750176250 1250 750175000 750175003
    0x50f0105090117030d1a03150a0b0f221d06090114061309020a031205030a0b01050f071b050312190c030e0d020d0c08100e031206090903040b04060503150102 69
    0xa62440907160410000d0f41000705c0c181c0c111000020036001c0d80d41c5d00b041a00c001c60b00d015200c0003802c1c0a80843d030284201c042c5540546425450100e030410507a0f00040005090000760200708040e43e642507010360b1001d4001e410030743c10082c0c0d6007411403000400b1107200c0e0f1900000c940c000c146500c1c045000c1100b090f103012583c003980005d400100c060040382c0c254002000c07002810703a4882c080e00130000010700c1c030000b0756281144507915191603090007003c0d13070250703070801c00e5141c140f240031710180100247c0101580c141a40012100c0b1081859081c00d000c884503640090b909030003107034030008000c54114014114440c0c0c861185101100c0c540c000c40b9030b299100030040016420031030860280c545081d070b0100c4a80010f05a4044009079600c108a03115154031041c01c0d0b81194195904007441d030321800f80d886a0400140d4500313083c114130308038100030042000307114501e080301107800b1f0a0104166005000d80400d0142e41c0e0313440d0301c00030304150411a040c210940f000650328509510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 750177500 1250 750176250 750176279
    0x11071a070c02060d020f03040807061a1e041d010501031509050a022710080c01090305030a03020a11060c0d23070302090d0b0f010303091d0402010507060f050f01050901 74
    0x10310359602403840600340d081002031392040c100c141803a5000d10802c814554a0401075001b988078291080d511580d524084040c1c1e00101000c038418490010640b00a0301ca5a940710000c00388078092000d90a04000010004e2469030460075900890000896400c0e005602030b5050342d004a01c8030303950010510440c0c044c0c4003480002013031500a40b0400d0010309210220440001e5402036288015064403030141d140031040b10301070010034021908100c1c45905101e031a41c941350a280075100c050842e1520743d074910542503480101355000401c9488244540182c0c4d00f642c0b44041910b000c2d04110100240c00c0d0800161a801245803100800440c40750080e13160b640303100302841c0c0380642d403032000030b1b0002c6d0040000c40c0d8012403810031200c00200c80d0030074a403190f0702040e401c440d80d5041d802c00800c411159001182d0b02410a0303840807440d001c0e642003a0744581c1c2480c0081d60b920320340c9800009811450131343e480d42d60510301840194012501e0190603280c080d41c54400342e80e03980402d6070940c079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 750178750 1250 750177500 750177511
    0x310050312040e1012050601030b181b01110a05160b0a0813080903070305150f0f040f0314161b14040209120d021b040b09010501080a06050411071a 65
    0x1c0801c010444801001100d5034444009a0000345980d42d44c0403d40f001d0752000412913140c0c100c0302c01030041115410000d0b030032080082c1030300100c4104031a81c0382c2ea0004a00150300c240c222480c0c0c0d10060f0b110b040840d03408565082551141042494020768a8038100d00c90070622004850100398202d2758030545480640d02e03580c0303621320f0702c8e102c500d40d102d4600040d040e10750b02400c201840c010385040082d90015845403008280040d1403034a084480c17100030b0103a0120180d000e09101130b400401c0d215a400c281c000d00400081c0302c00749420b9440c02e10728021800d46020125512554045103101030141c6030060300300b12030101400880c40480c240c1c03406400115816100310100300e08165010b031504000142201150101403488180340403c0e80120b5001079000003401c00d85070000900701045980300b900c0c207009480043c8002142c8041c1401b80504212140c40001c40103601134114100503c0b019004018560700c101400744c071035100d283d0648030a2001d0380a00340013400e0950140c46403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 750179856 1106 750178750 750178783
    0xc18010306150c200d03200105040b0103030e1210020c2518020307050d2c070801140c0706091b06031b0503090c010e0d08040b03100503 60
    0x2501c404011000d004d91290289000d40b505501a03c1d21a45418014424081e64901a51810800c105608650b00f03103401d0000b44000260040d050381e00a83e14003c014000c0d200f13002c11a40d031106403007100d40c458010002c5002540d07018124004988054918120814901d10526050908180d02c3c61001d000c08000c0000350f280b440316a04200c40041d801c52910303441c0034201c1d0180890038041c044e10759400650100c590360312207480710b018501030705c2c43c0000070320050340d50425802016103a610b0203410096400d0140724003485454103103c0b86250007496501c6d680505586142110901070000d1000800e411703020815028241e9950b001640350402400644244100719618090007010028024245070200b4030f00c00c103035802c1c20301c19409281b039408100c441e9641c9001519400000c41c0200c1c13000c0e4903100444c0541c84010703800c20503a4855040540300c034034007070b28031000 = true := by decide +kernel

theorem cover : BRFrame.Cov 750000000 750179856 := by
  have h0 := BRFrame.cov_init 750000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 750000000 ≤ n) (h2 : n < 750179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
