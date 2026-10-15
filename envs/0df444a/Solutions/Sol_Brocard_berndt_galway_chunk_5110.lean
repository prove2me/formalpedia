-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:46:33.673628+00:00
-- url     : https://prove2.me/submissions/2f6852b3-e24c-4ce1-bea3-c36292b8123d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 918884892 ≤ n < 919064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 918886142 1250 918884892 918884909
    0x9020310080f070503061b040b031312050409051006022a100201021309050c040e0a1401140a0b07110f010c061803031a090105190f030c1a030115030213 67
    0x2400d10401c00000400310f04540d81201212502d4a44510308801e0142c1c5040382821001c0400c800c3c800503010000542d040400346008407548021600c0d5004c0c0240c6414050002910001c1c00708100500c6005580e04a08060002d015241c41c00c58060343d104a8600d80400b120187c01d0020400105c500c1e0801100c0c102814040503064403d60081c000d41c850030044104005a0741d0200f03583c1003d10805205810284080307103400c4c1040310132041c0c0400207044900d25900c0361030940c0b12800e00c04805009295101e281c44040040404001e2808207e8101812515050021401240041605400f05070301a82c01c80e10040c0d8400048540554440019047d01d0800401422641d0681d02e14284103000f07545c200101481320050030050001303144c1e11135000d80c03068010f05c06440e0190280194059451019089603a11034101d060040594000c2d10b0b100c03c84801000b415641411911a04940c100740d80d20710341c180503103540f850300c0704961001010b07408205000044007559050001d040b441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 918887392 1250 918886142 918886153
    0x20a02011b020607080406170903090609040f020c0c1c0b0a410a0b0f01080705130801020301050f06031b0310170a0302010e0607050403020d0204110304030206040b01080a0c0902031008 81
    0x85c200108240d115220314170005400c0c800c0c1c00310100d58911070601403411400510b280402070300c10424180c0007d1b0105078003541d68114a2925241c0d0302c001d0240c5070580c0007419240706080b0420101803841702d40b0342c0b60041048038040005010404181c4d221411100c0016011802880030503820317030100d6400f041540000314510314070340140d070610b00c5204d241070070010b0b0b9072011102020340e0480c0504a0300040340f0214944a58010390030158003440310320341641080c40e9003040040c502e0050b48400a241d60010061180c4c0c1070030810700c2c0000c0710558080703183d03051502a8181c6d171011034007903112601c80800410000c5903888403c0004028010a181c4140d140c001c0070342c2c0f201603880003107001d50720385000c1400119011481e54460101501d5660410740b0b19001c3c0199400b611000300d038490340e500c0203d8449952000a0743c025400707035000781b03402d1521781340c002140b040680109219a00071603001002490f01280034050b80c1c40180091307221380701e10a9000d203035a8550000c25042c002c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 918888642 1250 918887392 918887407
    0x1410061409040f0f0f06180819030905120406090f031e050f070f140a060e19150e01120e0d0f0c0c0602161d0705071e0b060f01050a020a02011b0206 65
    0x1284079405c105000b04002c004004c01c440e2180c064516000d070040041806004c8030100b102c0d124075404c0c40ca58941004141d1403c1940c51a081604081c0c0c140400c1d00e012600703200e5250b0002c0703024040d0880350703840442c26096803a0240400002c50500085803414481c10701004010701c00800084031083c00c48003a5070310b0350314412002076180529110600c5251101c985890481081c4046403096242c0c055103200d00c0b014055000740d00440c0d01c40800e03050400180f80002c88407a031480400076581c40f80e101e2038000c0010a007500c41c004610001d810f200040260716008151100d0380200c90403c000c8201c001001600d800c030003c24003904414907480e00150807074010604000c01d41202203403212240d222451074151610071b40f05805c401218000107040c050041005103040343c090040c090580c40300414180510581c0402100e843c04404244001810603400d00700442e1800d080050420b0f04c0048025030f2a42d000700d000e8100526207600b184150700710b4800c0001c1c10340140c9145d650f881e1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 918889892 1250 918888642 918888653
    0x70f08030a050114041404260706020315011716090e090c030610080a0b07140301180c091422020d240501080103080a1202071410061409040f0f 63
    0x240704981896000203080f210900d0a0300c1b44400c01c01c01866142c065445a8649080424400d00c44040b4040e0340c5291111500808001d411a14400c002c0560b0b2072a11400f0400c4840195000398180041600d0700000d020b10703480e20503030245000c080c540d000c40c610102100d094010790f00c100f00e08030340c00c4d0512070808000b103603200d4041000d5044500d00d44981044411900081c03044042e103030040c80c0d6200c0002c9103203400e180c201101d46041a016094a080c3c10059030007a0f01000080d10040840c00c44000d10f4000c900798001c1d6802c0000d9103074600401007011120300c901c01446541d0390303a000c2800308130000c0c0100741110380309030454451140b44200f500078007101945c101d1207402122055055124040701100380d4806a45060041c6d01c0c60b6143c41c3d460308101e410805120003007110b40030307202451018180c1c00b03010b00c0e80f0004c0600305414803070414022021400d21682000c0051003064100b800e54407440500f607420b20080d03640c50030410302d05807003040d0007010512141e15890a000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 918891142 1250 918889892 918889901
    0x20a08060f0c09030c0d06091a0708010509040c090905100516110a03020c062107050901180e1504090f060b1005070b070c051f0c020d02070515070f08030a 68
    0x58903200d005032a0b21240c4094005000d01c614440d4181d00c090012002c60410440c0f141c003003417013004080755103451950b8038000e20000d0444c00d40c04001c820100802c00c4d60100b5907900600003913802c4009800c0c242c0315030705a2142d0b030084441c010344070020001005010030004085410080b01007186040003400207000c0400010544006088001403901195010400400701c0c0c2d49a001000c030a10343c002031100c650010039040442e9888641c03904070040000707050a105000543d40e10b82d58110600024003111905800e03200789080f2550103106160698a9060300035042c205440c03d00c421000000d0064450305c50002d004040b040c4d081d008100b12904000c2c0410740849141420034503910b0112024000d910001e0f01070301420000c03078070060248100713040c0c1d02e02800c03e5810403001d050501c808040d400c2d0040c003d140c1d580320408000c0f07a06200e005000790207440030b080c1c100d20700000917200074800451080301120001c1c56204000c0883c6c043c1900715070220340d9a0300c1c0c0c135100450388000c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 918892392 1250 918891142 918891151
    0x30b0f2e020319020312061005040b070b0a3209011e020901140f18060f0a0c05010f06080c04150503060c0a0905010503040213050601030b130605030106060e0612070c020a0806 77
    0x150070165004241800401079807081500070141c0c0c403c0d1f43d1030030104000a400034000900340402008040b070200010401406094011400074115013840c06204040710b044140408850f4100c89260022400944412040104044000c07510303450705040c69004096011154001210011104184e0030441d000340809a1003621550f64804071400711080502c02e24000d50b8010100b046895134880c40c115440342400e901809050503c070207400680650791003d8490b0b0041a0a581e0a04c10800c0c240194401825604d0f410702105107003450907681c0300c520b5980d0520885e00c41040444507025054a0720040030024126a03da04116800080603031191003d400002c041071000b01b03007540902e00720ba019039030140c054908800b8070b11040c0000c20003d000d040c10107448822484055690100110440e21003a100040c2540b4102c01c141c05c40f910380d4010420310140c0c100c00c0c040da685060541e0a00c0312202e903404100e540c0c0e07143c1201d4140740820300035484100058045021000050607074442c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 918893642 1250 918892392 918892417
    0x60b060d090c140405011511210304170405060a08062707020d08150d030e09071106010e070e010c0507030c06081e0105280306020c01090c06030b0f2e0203 68
    0x1558443c1407100f542c1007405001e0b0202e0303846030b008880600c80e1584044409101d000d80b00040751100d05a50000f10040000e03e60040200904c81408500903901c1d203003600c40822145450301e4040856a0381c011442c0603014402548001609030311400a068940842100307038025120700c0000500d00c4800a130f504100503c01da0f10644d00c014040c1001600603050030502c805c0c51803a4004200481d03550320402c5040000800d60002c1a4440e05001070152405498a10035200c0b07040480e850124141d120707500c01d0711030b01e042c4247c1c15040100080c2c961020702c4d080600d01e110782006443c5c2943c40e031005004083d1142d00090069100b0750081c0681c0340a000f007080e4582c41d00c0030740725183c000e00480d5072007841d100031280421400c1c045181c202c240a8014a9059a00d0700d45200304d811003510840540d44540500c41005800019076000e0401c40c203003040b1070103001020072034050b51980540d000340311080c1d8002d1000302001d040120403090030580b4040404041c0000c1d1207801200d51200f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 918894892 1250 918893642 918893669
    0x20d06090903020d0f140703020f060a06080c0301110a2303010909020a08010b0f041e180c0503031e0315100c0309051c260a02061608090a060b060d090c 67
    0x30070305c0359100740c403031480c160f8900440c03500142508071a544503103412405d46c46001d0740104100410311103544524108540050280c0c50071040e50709100400c0741307084c4680d1418605e42e01c2c1c04042310658001409903e450a8102220260310901035400a00c400007100c2c04400003035003c0160300314400c3c0740d100ba5145110259141348107801e8461b05010294006600070139400306041c181d000408039904441c044408440700102c10046602c1c88400110340e0703007034240880901018107929001041c2c00e8004625040304085290014203202003901440d10b40000420500110502c64001c0810003e00f0a0402c0046c0c10018090121502003100030404a0800045614002061a9000fa0394111640109500d980c0f2500380c0c5000c12055016244003058030642030300e2000180809861a0700101481e0a101e4074040b1400b00400a1030100001c944c10030600c80d2001c20314641e0103a2001011620112090001e007481c060a41800c085a00d03003100e404c18040e100030740e48200c4204810205 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 918896142 1250 918894892 918894913
    0x20a03110103110c06041b1203080604060602060723040306060e040605060402041413060f1e05040213090c12110d0e010b0d0b090703050610051011070513020d0609090302 75
    0xc00328013039208440481e4000c18001000b042075141e4543e800d1911403000c091094483c4282117034607a005001760001040c580800c84541028464203001d40107500040c02c041c54000c0008114840303420021810054000340810440803850680d005960b1141040c0411501e40c0307e4215180000c50b010740b209410500840d03003038100303403080300c040c0d840088101c0740c0011004c0510444096a00d45600100d5688070000741c4d0699603181d00001e04107130340c01c44560000c42d41100340490306d1904410f200303a00c1045480d6002c950800380f04200c03031810030301284220440e0400c0d1a456406243c9003c0c0c0b80c180b008503c0442010301c010204061840341c20081600c0c1464000d003200c41c0300351040d410203001d01c25540030900f014811a40038a92404507100c9948955130789041c20421341e4801c012054141c424410313840e00215842d0101c40c146002880c0c4c004541016655503030134440c0d40e02035404941c84407813010190301140c100c090369003401e0150b15988c0308428000c00c5040410780c01806091400c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 918897392 1250 918896142 918896171
    0x90f0a0303050a050c030c010e012309030405090406021315020f0304030b150d1203020301060f0f080103060203090a0203030c060429070f030f0c090812040e0c16020a03110103 77
    0x11025690181d507030b107003003440c034440640d0558480c0d003505803284000d1001d2010f8907401d02600140d00454400880c144c0569201d0541d1031400d003410a820403006010007400d604c0000c03e40381150ba040320082400e0311141001d000a1250f580f02040c0d505140c14045000040300d10740c098a420103a00300c504100580100c40d48034042d5000040c007070b20020021075550000e1002d00802d03090000d003920294a6641c3d03810608031074220041c2c010a4022004114146c2c1042000080040d03604144405240c4600018250401400010718281d404000315100c16410090301410700e40c060112691013003402e110980d5000200d81c01c031059402000a400c8500900303241c17904813901070303038980269100c03e1810380b072408044918204141c0e407501d080d854142140079648442c02262210500581450015400d1a407007292544400e61304200c01c010300461076000c140d012980c2c0d21800e84508140324001f03442100c1440196010340003042c0401440101601001d002034262400c00c00c0d42d0126141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 918898642 1250 918897392 918897409
    0x120605030c3109061506050304230a0606090e0a080d050703091502090405061c0f08040b1b0105220303020a0c14010b03010e0a0b010605070302011b0302090f 69
    0x815416800500d040381903401d1080b450b01040c0100c0b0004000d00c1e4040d00c5054a04864024520704181c0354115841400000c1c07048400310701154619020980c140031001c0c0c02880f001e03000600c2d41140c0240f21102c4c0b06044055032465016074103441c8030725001e052841c05080d10740114003107039103000b404e20400140025803500321644440200d040c2035800c9920002400b00900c00001d041d01c68030076034002a140450340b20f411280001c016210310750748003400100e500c01031006020b0300d03443d06c8240d0b02030020b4038283c0e020366000351100949041440c111100c0c0c042c175441041d00e1040070a15408008048504000001c80c00d0001c01c069034034004c1c48004410410b8003080e1481007811024003182c4650020701c04041c003800c1c2440c0b01c5225554031052088100c4180d1702e00d940d170300f94145c4146003c0c0124890705440c10300400c42c102c22925403a00240c4184203160605c2000a20542018000c2d0410100700035900340f40c0185044031040074010307600c01103c02b4460b2400710380380c00e85407612001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 918899892 1250 918898642 918898649
    0xf1701030b0f090f010603030f030b040525030204050301020a0207150e09010e0a02160302030322020f0103180507230105070b01050f01032a0e18040f230703031206 72
    0x4079080c1c6038582109040c181c500140c0007030b42d41c3c003c5644083c041d000900444004510035074405022441d8860005e0445810701441c500c40c0d07042006002d240546007035002009801650303c4202c4014180b002d030003d01c2158003060701540045440107400360081520700880c3c0580c5030740041000064411202880f805d4041544504640014000d030503918048585c01407004e240145851f114408851140c18450422401a40300204004125045605811088044c081e11000e06451a070010f0b10440b1600c150604060b90f4001d08408940d000e0304a13100301c4e41000c160340c08161185940107020003035182168030000d0507080d0100303551040381101c1c0802c1d04400c400250b43d00b440e08000b800c607584003c0d18105074451080881210719008290041702c00d20340c074003000702080000a032005080758440b500c0780e110004e142208044080344250b0055001c01c0c1c0c0350034681946000b0724544140400354400441c9500e00b04c1080c28006542c00540340039840b0b0525024103e92030310242d900902 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 918901142 1250 918899892 918899903
    0x7021e160e1f0b030f1b130920070204180f050c0f0f1309170d0b040c050405060414040204031a0f0a0501141320031501050a090320030303070f170103 66
    0x2002030028039030f03c4449504030803160030a04101500000e5048503070041d000c40390b05c02c800344008000101c09882209c014800001c00e80c141c00703000780841c8005d402110b501900070390311000041c50880000725007106055101c1c0258503105018185039945820101c2294020644806120302526142c4c081c81381d10240200248114242c03a0b010001502c400031007103400f850680031640d0043e0500d030240001e000d8040001849000c00341c100002d44283c0d50381441444400c010070b10458070b4040842e410b440d045a00c2d1708681400c0c80c0820003e02c1950b00151095807404146440c0c0005181d506004003140048021145c84480401045400c03c0c071850119003000e182d06801d60811003070011728a80d0a10001501031034040745a040021490244082810000104860740c4104c41140300196420300c0c06904101034414050405071035400040c0c11000810388009a0314544010303494110380240c1960307180e040c18140540148800c889081c04504c041a181c000300300c142c0c48082c100d03900003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 918902392 1250 918901142 918901147
    0xf080106021621061e060b0c060106140c03041203080a14131a0a090309060309150b031603080901030e120a050a02030c070e16020607021e160e1f0b 65
    0x800100c8040c681c0045a68041c100082c00102e1907901c40c9003a190b0190100e00c0c9150118407545e411203419411020021074180008151040c0009180c5e0540f020740c200720f103203c01541140f602900405000300c400d44000100412201c0e03805440a8050f80702e0b440d8810300741c4400f1350800644541006d40074502580c4800151305140c2d070303075613440e2113070007400307405440140224503034180c050840e840c4501c140ca51019404259200d2400001803071076160410034400c1c3c03641d0345064040e40c0700e80703e400d107600c4004d5070003181d4040c44000c2d01101c01d490f1a501640d56850400900c0c0c001180e143e01003441d204421000e010301080d8410002c1c486090b15141118060341514280c000c0300715502144024054240d6568041010030007900080c0316011480c5818504107035108156016401190455800c0c002da01c0d400042a490b15950302c012464109480d04801d40b83c802046006c44107140d030242c00040e00300c0240c600328040c4100805114426045480400d0105128401c003d1842c108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 918903642 1250 918902392 918902399
    0x1207030c14210a120c03112109161418090606040c0201060602070312050403020d0c03020f042a11120309070501050f07081602060f090a060e01020304030f140d0f0801060216 76
    0x240c1e0211042007420306001840c0c0120103c0c44125401036100c0e0f511180c00d2281c1d43c41d11031503c5d040c1e580d1004000000f04035031444000ac8801141e040d1040307801542031818101810b90352000305c010344140c401418801807408140c02030f5123410035192180168039000d040c42d010752060044d08150303026a001440c100e8a90794038040d06040c14180300f4104075091101200681d1100d4601607400d00443e20001c0d124150f00400a6422132100d00c0c911961508118640d015220340c140c241261903039080305601c80602e1010340b15500984020041070240144022500c4000ca02550017000b8a80488200c1c03511080107658902c1510019455600240020703000100712030024690501d481c0c95241e0200840c0c0c0c04907100750001078a10a8440003c240c503c03003400c002c3c044034001c041900d0203001c1060a040040d49074882c40c0000303045007070010301003c00d0000d40803c4040c2c0e815200e003210001a058480280516150028000082d41e500c00020382c403803001450060494a03582c0c01da048130315 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 918904892 1250 918903642 918903677
    0x50301050a060809030d02071202150114040504050f030c0d081006080609070c06091a0604110912010b1e010206070e0a0b0a0221030907050904051207030c14210a 71
    0x4001e0407800030f03200c1088080100106d5001400c5294820843c9a106144030703c0e02030b0401c05500d0f446c3c0c2001c0c0349240100000f06c440d01c01003100d0f0308255400907131615a0b04146041c40d0101245e20041d03c80003030f5030110003500058209075886155100003c40d01c03404001c0745c80384d02d180314000003c1d40c2170003c1001440d1004003e0740081d0182040c8004802035034900d81500d51014090b10070036240c000c0d01a0303010741208035a501840c101c804002e8226800900c0401d4014031525501924811104158401c02580000415080240284111a0f540c1000240f4000c4003011340d00500806010039032150042d00e40303444a20340104081c01007402d0544840094106c07140301011886401d44c0e4400c4c40d50741e51291142007040d030029542da0300c1e00183c0b09280c25807681c00307680079803021020440401c20105103c4400f0026910303095030f41c885810101d5108075000d41c090040700380c40700442000c000000b00b0f504450b04c1d001c1003030030200360328042c9001c3e400307400c0301000030502c003a81c088003040703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 918906142 1250 918904892 918904907
    0x91a0310180b010602030a0306060302120f1b0f0306010e01110a0201080604141008070510050717090901061e0c030e0405070201020c010c0903020f100507061a04051312050301050a06 80
    0x1094650120001c241d030741c03034048200c1000c2e442000542c20004209103550703850300811000c0d06030390030250300e841c840600308691004020089101600745c6000700c0d07000744003000101080760f400402e00752520704041c6445216801074401c2c40c0462081e2003a0030041d400341c003254000182080281c4490103180d00156241c80703004040591042e586c018801c92139a007030821a0140c03107503400107a1f01034100038145241500701d0300118841c0080fa46290501c50340602111241a4483c144085a01030114122228000d00085940c07042c441d80001c210264003201c4c00e000e11a4910b0301907100e018080c0706968070300a000014001409140f803c4000303080ca07402181e0403126a00c00140f5121410403400e08561100030203000140288408000f5840c00e00c0b1103059202013182c0e08820a008400c2c0600355204d081c3c4001c01c51512083c44e2800c00b0f1070f40c8942086150054800d01c210300d0281240420785604070b104071500c2c200c0d5a20710107010311a40940741601c10207001400010b0400000b980c818 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 918907392 1250 918906142 918906161
    0x60e06010e0603060a051e1510030501080c060c0c030a2a03120c111e040510050105300a090210030509062e0f060206070e061206010e0a080601091a0310 67
    0x80e124107881c0000580d9801f8007510841e484180f45071130040749010440400b007240480c108040c1828010710a0140101d00002040d0044540c5941e80348000c002505241060654076494013900724010709128171408035111076840101c0d01010340101080407860201c01e400007030030400c01d0411718045c550181d1280e940550095820018400c40c10700000d82000c051502d400c408008550700d8102d5040c64003600c1d410032030320356110754107034107110000300b25014201265000070140ca00c03801d01090b4000c1300c4240070009050601c0c4500d01151000050901d41404074084d80c1021350111040348203100e028025044003000e0040b58079888122a04458881e6802c03036684194031181950540e50f0042c04000e10340c054070030b0034041c0340c55400703810404001c1049041c40350480d105002503440700126241f01c454102c602105403603410040f50b031031607401c071030343c4e0092000c880200d21148002003150485004203400d110300240a09004031040010b0039103038040d803041c00d03024240c8505400c803582d0f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 918908642 1250 918907392 918907411
    0x504020715051801110702090f0c0d0203010605070c0b0306091b041d100e0907120311011802040e010216060b031c0f080606040e1503030d0603060e06010e0603060a05 73
    0x1180901e14504035281034440c1c1c5280c04003c0c07020103143c030082c011888402c82d4840d600d0f06080c07450300407408116006141c03a4101840c5000518510803c1e0705076116a181c2c20000c6480f90384655001e050391b44106426140361320388210000740c4021071011244103070405080702445890b10741c40c698a0707403451248988036103400d02c000724840c0c08603504605490740302141007405040c089011841e8004076040403626082000c108410400c00080c45001c0394004203000560102d5401c00721003840280c0f00c031040e43e50070860101d00047c3c0c01c01d407072440c00d03000300d400b04030801190781001d08074070580000000c81005128640d021620701c0c3c0c801440e014001d4203840340c0c01c0000e44041c8007117400d52400400308042c0903078618451741c0702d400c00d41c3c002c40c10341c0c0492910f0300f040044060010010610a10b41d50b0302140c54a0030389050041d225003c00800e41801400e0301d0385412000b41031003100d03911451003034900008410003883c1e1024080d2002030003408440c1c445100800c090305c00142400c40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 918909892 1250 918908642 918908663
    0x9050304050310050109050603070536161106070e0f0310050717061507061d061303030b06040b1e070b01180506010e030309120f0303040b1006140405040207 69
    0x1042e0314188141900014180741c00105581001103031401c5072009080307140031354446401170000340c03034400818824803841d01c070800303003c44e2404048a8400f0100441c201480074a010711a01c2d411072054007030842c00380e0b12103010a0f890605c52659404044070008000362101c1c040044a0400c8000c028504c1c80140613a8100c510b102e00100544a0070f136115400903e408030900c1c1000c0404d91000e400c040b049034081030700040e030070041409005581d00039020f42d0343c4000701c2114011590003041c190416100384c4050745026044036000b09070000d002d601280c00c00445560500c0d01d1b2080b1410780c0c5145010500b00404515418070280b82d800008031041007c2000304081001852420300819600300c03080c0d40650360a05050a507500585141c0c1802014050000c480d5804415518200410f80301e244405203400e550b140760101042d21138803140400801d010a0010302c0c0c94640c45103c1d08000c9880d00381c0d442d10b045414048004100d440c091040c4000e000602d080d4000306042806021141c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 918911142 1250 918909892 918909899
    0x601140415080304051315090b0409062a080426041a0a120507090519051e090c0307170a0e030c010504060b01090509010e07030e0f0601140405010311010309050304 72
    0x5103a9241c6800204440d031010504001d11310b04010280c010200c0c4080520140e000352400c102c5455060144224050301d94140000303680b5664000f6490300c0d0030590500c00c0380100e00140c41c058800d1603652040c4541400d014119034041c140b001c0c0501d0348989040080c00b51000d900c048450031151511f1003003020000054080c106550048246c1100301381d1a03503407a98914090200341d40070a20703115144c03c000c10482480c0d040003d6500705e56055510003000c0300b9200800010b1021908001c0c0e2001c120300c62128802e04004541001e04020f0b20000030b140c50b4014180900c0c04111034480000c0d4401d240244100f4070f00035103a07000040e00001041c0e032103545e00500d0440d0081100d0340c13016950b9200300800d200c0d41340640c946101c820300b03240040750b00703110200d800d03103005000d00f00003941c043c400329003400d1080e03102100c900e026905407048112400403880c0c448400b849001040d0306002c0d134131071062030070f8401c0504807540081201c0c40c0b02c900400640c0034021084051b22140814403000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 918912392 1250 918911142 918911171
    0x30c091207150207090506010507020f0a230a08031204030f140a0f23160f0204060e090705040c0e041a030f01020a0305130201051213060606090905071106011404 71
    0xa03002d8240400398800356401508000c0c40d101c59a8000f0104904000c10720090b640c004086448050301514080001107440c00854052030b1036078004030322201c401c03582010712a104841507a40034400c5a030484100e580b041e4580d5a8014040c0c00c51210080c0b0010030000f03030040b807881c043c42005040c00c1c0c90041481d0801c1c0341e20b07008440701d41b0202c1c0c900034111501c40c0d4070400c006024020000b40c85444590514084141d00402d41c500107141c141d0b81006c002d0050906903035480759070040052285648851320591250f2094684071030b04c3c03050728030210301d92034a4014010055000d0341d400e02810000010400038107001114404c03131003071805140e000c5460911007901409082c1c00056942c04030741d4030050884400821341d00401c0050707450400181e90000c1140c0788141d504a20001603215081c00240c0014600c90041041d07240c4040054401c1c1c22200010440d00b56640c03c01090360b44070000d0b9440a40c071206c0611a800100043c1b0980d014002c16042080d00903100041c0c440a89400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 918913642 1250 918912392 918912403
    0x50a0503040c0b180f240a03020d0203041a01081207172a0c03120703030509280605010e060901030213090807060605210d050304060e0d0c021302070206030c0912 71
    0x549500c4e000511520030504048403140b00e0f0400c10744480000c407100010000d48106002d0780c3c4400d1020016034408128401c0d010346007180c1001c481107640307080615000c10b4826003428030112031030102c4000034030303084c0205820052980304000546000c42c0c90b076030200203034941600c80040070010b100c80c00b95208000748aa06003038400c1d00340c0c540251208555840c000260303215503c25800340c188000e010030300324203450ba50380c7d01d410041015110784802c1401c009401c1911004199820618415840c614402d1091b040c010401004140d0303c80740c040c641400b04440301030700404c80c840100b0060408289004917105030100004070b01e421075554080a500c505816034001c0e4607203c3c103001a10b00392070028001c42c11109003c0216100101c003940702c03800b09880d882440b82c040001000e00205400c200300718000c140680700c0008100c10060b00e010300340798040e40240e04880f01d0320740e040c105108580c0b500b50014599815950340324a6021160301004560f0b03005050100c5c47d03d4403003401c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 918914892 1250 918913642 918913657
    0x18020403060c20190204230f01060801060f0f2f01060312080618090c0a030b07090b0c0a150b090c0a02060c120613060e1003050f010606050a0503040c0b 67
    0x142e603500341194014191000c01903e0882101380c201d604502e10144a0800c11480140c1c10b59000c104441c0081240c1d541c0e02c03d1a80003410080740c40b0800008012580c4c646068505075224181c650341c03503441c112140300e4a03041d58800709041c248e08030030700d070300030592010760f0f84400c513011403902c049001000090030b051000180c2c981d1200014010010728900765140d2111510b014484c601d0510001042640380c080740c000030104230408101c03004030034083c0850f481005031641d441140e072441c01c80d02c20b070307000c5444000249100901042c00800350382210320107000381005103011401c1303489200e1907448100080c80c410b0f50303800c100252a26030b07016691081d07000c0c0c03401c1e6880e50801d49000c6e0800300010028a0250020410f508d001d06800d100039800090940e6840007868940e02000d0080805420000b80c402c1d096082040562606042c0c0060f244036401b80c0743c2200980c0c0c0d4007820384d2820300078070f40070035003c2c0700e01480c03d8481d1000c0c60380140100d02c4407070407580d0340511401c0c40c0d01428 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 918916142 1250 918914892 918914897
    0xd0909020c1623091b0309010603060c08180c03120a2309030601241d030a06050105120303041104050606070f06090c080a0308071d031b01200718020403060c 69
    0x43c9003060110b08070101031100d50160b500034072525002266500095144068110740c00b0003101085000c2d60941c03100b40035650001c0c0803c1542c94410b00900044402c68a882d04e55080c6035407150600400302e0508107030400903004000f00480c4402130151900000651000c0000003d01c082c12005034541d0f884500b42c82c16942c41e80c9e034190380c1c141400c00005070018081c010001c8040800f901c4100100200381c1903c0ca04500da0346075110105020300e080e0161541e261180c81505000c1c130800d944000d049410480d00b04039120340820141e9164042124040c280b040060070880072410175070003e950001c4003c00700391900703400342e480c40c04058104000740d07011a90323850350740c08104601c5512005444144014811036041e82ea00070a0100700070665800c1281c1c805020103c802000842000c40100070140c82400c03540d1400c1044a88195100c140002c40c035480e003504241c4c1540c0d025400b048514050301c107a0b824128211b40e080b00342c0b451800066400c02c4008041000c2d07219180d120182c55 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 918917392 1250 918916142 918916169
    0x4110d05010812310512070512010c0507060902010908060a0c030c1b0231051504020306010c030e01020a1a06040c0302160605040218090d020706020d0909020c16 71
    0x861168038090340c00c0c80d14541c0880c1081079025215142510380d0f91382e84006100b440d00986520b000300b0855255100f150001e1024030040d100580209030101520401e5070043c051035070502005d402c0e01c0188000e000410f17020007560300400d03c607130000c024250040c18000542565021060b2818400711081440305a03070f02c0ba90220503030b1500490341d100d032032454450820f044202030b80742c00c11481c8400910901586080d1451310754070016007040c803105914040d10f071b907181000c4140034180448100040201210304a00b25241c02d10942c1d020741410707501c0250100459030f055481800900049046d40308940c1da420010f4072a0507000851045511400d20600b458cd051000355040d100004003810300500014401c01c1d00c00408003010b640245011900f91500c0c00815500d6510001d100c084012003c1042504500000c20251101c07070340c1d08131900b5550b1220200e03101d9101c00c140340c0c0021400c1c1810480388d09150042c1003c10806815285680810f002409414126500262028422 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 918918642 1250 918917392 918917399
    0x302060f07050901080a050a2706060504090b0610180906170106180f0b030a0506010326090111010e0d020d3c021606030f060603020a0804080904110d0501 68
    0x4111038150001c40c03606080c1e04044200001038280003000346807426041e42e0b1000100c039103120790001d00c504000010400c2c4c0815a5190385042c040d0540341c01d4662030f040002c00502804c003031203620280c5410145006a640b680000c004907030304a082e4101c10000c0e001d5401c113000100e01342c208010040740d45d0000c1d58914140c03145030b90380b800120214490345014401c200451421a42c0c1d045004c1c900c00008200070501e2a00c0018038650341d4142d0075129910020782004000a0510305880c001d0b509005a683c3d4001407104061506800c44048001804201c2c419409441c013000c04d40c8040c40045901c820340500e840c41c20210150010044c1d1058054280f65904144a0034280c4103442005581140d159503441c90412006004c2c03903280051500e0400282c420700c070903144c4c001c2c40c0c00b0b400c01c0d055550030000c000c2c1c800c0911076006907282140c001030040c0684211000e640380360700d075108150381c1c07601e40000b5500700180355600661201e0304c003507519010200400c09442000c5000405504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 918919892 1250 918918642 918918661
    0xa080310030311060f01030308060102120304061406031204050d02060d15030b0c0a020a08070602040e010803030619060c030305041103030d0f0e0c0a09020307020c0a0308121f050d020607050a030206 87
    0xb04000b10386110381240085c80640d04800b0302807070550307400d0b007480203094a94400403403404401d0740070144008000f0050004108030798101650b14a04c400c0301201d44d031605c0b000c150712150810702e00800c0c40c00c00c020402c040d04001421050281c0010140381c00c110b08403421030117444101007410503542c54203c0c10300030044406034054020314130401141c103101e008280a90365840880d0094000000415008200315460301258050120580a519156900d441c210f0396504191602c6100305c00b148100d041b83c9a00b031044004030f42080e0f07101e560422642d14183c2c02400081d0080d10640f0344001040c11035102040100050080c0300c00000300b4560b038140b000100d503070120400116402031041c3c2800c47ea2240e18140554104004c01666a118810300340d01e8104643c805c0c07500036462140000c02e004042020700020155850310303110681d108401d50903207145103844000c00c3c20000350300f4410780c02e041e44030b181c21038070180020740740c00b07103036140c4618068264508600590110040021a01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 918921142 1250 918919892 918919907
    0xa0b04030b19060803040504020d18050a0c0b0f120a110a0c0c080d02030f0a0c021504051816031806020f0c0d090305060a0e0a0f12020c01020f0715020a0803100303 72
    0x2c8038482d04012240c1046406910303845140310700383c8210780219080080184030b500010024070000895004620341e46050344d1103070003005003550b0f00340d2081170005030b80480d0400c403104540306a0030380d842c0c02d0602003844010100601b04100565494a94880302500c100051001ca01c85840d520907824652401c00c071140f0682d04581d450b40c106001c008003691300040cc0d508002e800b07909031a141d455406040341c0c2c0741c80c843c4011394803e900180d00084034000c44002c001343c46040d1502c104e40c40700c04480c815400d409442d080b005805030310026642034400c0c1c0c4000d5400841c1c02a8401d2250309807a0002070ba00140140700c400c0c00e0010702800750f40c00421480c00314244a0030b050300118a56101c981d280d0348002c0240c105107889140c4000694014440f13440c0240e800071b0b0258103144182440d64001c0c0307010481d200540304260440d5510340c00020b000c01d450708524002c1c040282007a07042182c002400451205501c204c2118100007203440380a035100d4040014006815851420010080c9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 918922392 1250 918921142 918921181
    0xf080f030c061b0c0115031403030915100324180b0402061b030c0109030807110a0204020f1207020109020a090507081612021c05011418060a0b04030b 66
    0x3984100040c1d10710381d9000c00d00a0307002c03248802d0b0f0381c040c00015500c525036125240340398015518103110303400c041b8000703100d0070306407809608070b00380d151010152183d889c48250340c0322101c1c0d481010000b000048016030319038011100c02c800254903940c1d9940e50300211480c0003407210403185900c06000c20301103104621050f000c25060504245244e1a840403081019002a00400001032620050002400e080b0498441c000850360355280c00d40c013040c020020542c08400007584140403500ca18495058040b001c44004040e040302c811076400c0100a610100b0701402011091061480042e141c401081c8500d91540000c9401202c2d0310400000b0b07511604008203c62805081c09034070340d800700c0c00b2136005c8100320803480381030803010382a243d0382403002d44240e101e400000c080606280c00b602d00001140682400d01c500d98036102c403500c0c001d1800b44880e412080310200081244024a03449810410182807644116103c90500e030b11913005800a0780c81c06484002d014034403400c1c1ca4001d200703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 918923642 1250 918922392 918922423
    0xd0e01050613021e07020102030412060c0e030303090d0c0f0506040506012d060f020f120405150703020c10030605030604060212060d1203090501020d0603060501030c0e061c15060f08 80
    0x40c010024020001075804d07002120718014080f03420004c59000f0400c40e00582000032140d05030002d1850310802911540814800242d880d0014039140e08000041c4c90041e05901d029104071465801d0844400c1481c0e401a1054034041e14400003083d410300080f405140030303001800e600d6041049800d812a0120302d070464030190581e400c05141c40c204c0c1c01c0c000f555081c3c030b0300c204001c6036140201d25000c1e40001c03211403802100144080303000140002e2084580030364442d203008020b4400240341d8054560058003580008002c2c20f683e01c3c000b01d107802112280d04002603030a8503100420b203061822101211315a0f400101821700221100500394025411180c1d81c1a0706035a07030301c80d2100d000298a010515459101c080100f10b000e40544610281c002001c0282907600d060100c080d1800b032000f0350302c400c0d08a00200d56090740c00c2c8210b00c80c440180000c00d412150200c1e4840200a40e0800d540f10514070303002c0c0c690349915010710402080195102408207007083c40c828200300810400900303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 918924892 1250 918923642 918923647
    0xa021e06060d030c15050f0a0b2218060f092325090e03221a0310080307050c19030201120b01052506050604051e09030d0e0105061302 59
    0x1c141e5403620300e42c0b10340768185400f8a1038085450003030520080f0030500f5403203504186c10072180b2007050303200500c61200301409014401c00b2a0901c46d44172100b85103800140f55034092902d9400550700120041e0b44520304e070005400d0319032511002ca9804268000342c0ca81c88903002010f00004114000001d07842c0c0308650700c0b4042921006950b0342c40d51030640640312424400954106c001ea141c0001000852824406160340040c5241c89038824105180a4080c00101009002c650040041655002d60040020f003112440022880d00014003403441903507000c40120b030910f0288090014207103e400240591080b41c000c0210090140d80110303200c0c441d00f40108003507a40000407040e4021171040c0011000c1c4064012121840342c200480460718000c180c11104014070b03420820414001c1104000a40325401044151082a14405046203003c0e4507142451404910030f034100c04c2d42b5040780c1c54002101120810f42d00ba0300281030042c2d42d15810001c2d0b45c105003c049031201e0300e0240451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 918926142 1250 918924892 918924901
    0x604060f06080609090c1909050705120c0702030c100c050d111002090d08131403030a0c020613030c120510050408121305030711040b010c02100c030903080a021e06 72
    0x600c2407000508080c424204071300491810b130014802d50070240302c050985101064940100c0b4215020b03407260241052a0030300103640513100d081900d400c0380c054400200c041d1611042c0881e65040b0703010503a414000c1c0c0c15005425034507048c0310001d078509900d42d003915901f581040e41c242081040e003102030000c10380100d02c02d10804640c81082e85d40143e401a1500c400c4804078050010403c6c0003061100300044150725802e03103000110031156801c645410016182d414141c6a0060066030400b06201c0c28240d030042c40c000700a844010041000c07005503542e0394407060303083d0181c3c1d17001c030f076100f80080e40010510a00340040501000b2451042c043c0e41032a03030780d24206100d001940118058000085200400701c1807010701da1641040031651104000c0c2409101d54811416040c8610710f4503c000803103500a1026800481d0020180ca01241071280140d800800300c1d24100c3c1042a02000407000840f03000c0034000d1030301c10358018507610102d6981e050b43c205401c010030411394030080030032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 918927392 1250 918926142 918926147
    0x606081e0c0a12020c0a050303060a0f051305040519110a09060b0301090504020319050d110c01080106050306010e0d081306050f040501051b030711090c071e0515010b030604060f06 79
    0x469020102d442c0100200b4545004a00240101e60b845003c5004448800d0144200000550b0250f40100c920200343e944d40c0c0348500c08816035110b8a1703040340c5001781d03412b05020a075200650041c00745098030b891484000885010110b2503108850300070010310424441e08066048201a041c6040c00b00131190522541c000e550105202d103000107900c0b400041c0841d1401c1c001144850314040d4401d440344850b103051034851045106d90400101c4002e2400035513080040d091324184410385580d42103908145003141c1c1603200a0455040c0b0920001c4012603031a00c00c11022920300442065445220907490110000b121358807842c00c20009120405402c0c0d50340c42103400b110b0090808a0341c0d40b02880402d890b80280480451081c0804100a4103104540c41550301e51001200c41e101c6c02d90718480000c0300c2d402601c038040d0546040f50303503805541c00d692100c6030b4a0f5000c0c2c02112002084800c00744150002604544009007010007440039a0910340201005041d0105060601c2c03030419100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 918928642 1250 918927392 918927397
    0xe01020307110a0e070909050c28260906090303041e0615080318040e28020a0605040602010e070e04030f0e13090212010507080610120606081e0c 64
    0x103421007030610480c010a9440890b00f500a00d52045214020701d00740303002915040381c901c00c8a032080d0608000840100c120070484107403d030070004c45021403500b10380d4884440ca00402034018400c000084004891040008030a18100c00700020294589441e0540c10840050f1010140e54020b009210018000c50590000c00701508443c030070702c0c02142080f401401c161691600d03c544100c4012a07041c60110080c02125000d031001c00c070303e0302c180003400116842001030044c10303048291980e58440240c3c02d0007003500c41a4014604640740c5800241d03140c3c0281c4e000c90003088001a00304110341c1c0a00908418031000800b40c0010f03490300c0c43d6010700c801c0c0200020700700501c00802a1003207009241d103e0420741c02900304004200340c00781201c020400c5080c282d00c01d1181e20622548503c05000b401e01c2000030b075441b01026100c0c402804410488105000b0500000c00c0707020714861914441ca41c002c1015039182c00180c1010080002c1c0169a20301000070704031081c08210114040c9000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 918929892 1250 918928642 918928657
    0xb0d02030a0b0a0b0603010b0a020c0901050609150405060c01090b0915010323120306031612060b060f0c0109021c1106090a0807090c08100311010513080d120c0e010203 74
    0xb0b05540c990380d10712240008040030014180d10000101c000310f065103680c00a00142d540c183c00304c0d151502e00c2d00422811000034425540d11545c200718840c850704040318480b03101030315010300504040d11003001400640000d448280303143e46d100402c1d000c4c8003c14040c41d070810a490b015144410350450544141c120501010380b0100001c900b284e48980c06442170041d0341c3c0940c064900b0402c0707204801203541d0082d90745030f101b0b10a840c50000100203140c0c011044a5141c1500c1e0207001c05036035901e016060100a0790303405041800740141c04480c4000900400c0481800050008014810088505030603409600150a540d10746000a03003001080302c9114800c0315260f465005103400a00031140303d4102c1c08180c054400300003214401508103420f60300380b5845e43d0138075903a002174921800010f480007070705005010044912075406407001340003142d0442035414046072280280380c07030b00b44490106c600140000b000c0401a610b02d10440840c14201d1401090549412000030342d02c1c00350b0b11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 918931142 1250 918929892 918929903
    0x2040207020d021f0306080304080c1207030b0414060c0f12090f0d0e2b060f0603080304120806040507020d0825120f05040201090605030406110c010c02010b0d02030a 73
    0xe600e400c0d50b8807030201101c9954024400c0c183ca249030044034662988840290f40403d050110129183c07101105403000e480300040205000464079040012034004003520790300d1801441d80100200743d10000a5110758020b4107490550a0150b40c9c1615080c1b0003410301c03101010a0111002600e42802240c051a81c6102032003580e07140c80c49902e041110b859208038280c801d00718440105a00402d035032407001811503600b12171183c60b0000f52081c1c2c03202c03102c8a0120002c40031200004465034403180c0d07544049a400555a46c0340d03500c0c4035550344195010755003212010b40541e10280d11503651503200c40c06440511440c100800b0180d0349601442e09901400811400070341040c00c8210b02c0300305884030394440040b001c900310019207001d8400410310f0f850b40c2003040300d003040341071030080d24026903041c0d5074041c1c014030f0308504681c1078001800849800c0d4031007600a006003031080103001c6940f0130200010f0316050700344000e42110301204585000c2c000e020f15403400342e41c010620440c042d8008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 918932392 1250 918931142 918931147
    0xb0a031e0504050a120c08030105121e162c09030702061804180506070509220b0a090915020913090302010501090f0b0303030105060703090f0e0402090f06031c050c0a0b0402041413020402 82
    0x80d001c0702d007041d0080c146005010181084181400350008120302c0988601371940b04c8652100c0c4030441400c1c04021103440c101d07410300c43c2000d000028900507400300729030082d281000c400350b0000b003851b400491441c0711921411040400c2d80741901c2046100e40380900032040010555840d0f07525040020107110610501098400c1c5544030343e98031140e00d202d514120108811580300140003490b00c02d12450150869642c042010091072092400030703030300150304109a03800512600041d500044081e90040b01e0107200d0b4400004900840c0c84031842070700003040b03541c182048181140c90703140c00744601c41d08012a2501d6601c0100031a4190342c0c1c01e584140d03540089050940307540e202c076407101980003810314001a07902d181c00c0700180580d20071240d208181e15190420015a80180d0f502e80e410380094404900951401408443d105085e0520900b410b6240006606100100009a581c5c0c8a0903040008500d0240705560b200d41d6803080d0b9041c0c6042c4050b80d0400c40202800090155600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 918933642 1250 918932392 918932419
    0x905150f0402120a0f0501080d0207360501081002041a090d05030c07050103231611010e06041109040302070b07080405040513020f04060b0a031e0504050a120c08030105 74
    0x15a01120550f624030708010940e400c10340301880c010060300c9000a1214a88000402c400e6000b041c1b8074050401540100a140d0500c1084500c0c0c0d0041408042020904034800402d0300303c00031a0006001c03000300010f40ca44c9080b82450a0104d40030b45c2118641c41000705001c922919454408003c0174248001d80304c180410218a500b810880060418070020515900740729000481e102a60b0081c1d81c14454810500b41c2542d02c8003000740c500024062400014030038894918035280c0c404600d26280701d00428888038030703007180c4c649840d80c19280c104600300000d2200c480c3c41d2405081c000c0e920041c01d4a040e0310025210000c0e401100711502c070004019040c07080140595001d00030080c4100100d0400700300c0008e541502c0c00f012402004d2030345c030300103103450036100c4d5904642003a001d41c2d19007940340d24110020070a10b4103400140c203020147e465402c5140c401c00303120340d1042008210f40d04c0e850428a040c0e4100030b07040f104010a41117840000741d00b2030b0a407411200309940c031070988000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 918934892 1250 918933642 918933649
    0x2030d0b0a030c121203021801050a020a2a051503185101120812070f170105010507060c031404030e210a0b071124010905150f 56
    0x16107a0001d0041c80d5601e0010134911000d0280c10500340c031074080d0345101c1d0110a0140c1c16802022200160303a55251413079509540a04001d045454051040e1050440e6554404440c80440d000c6d400c0049402801e51000501502040740900301c2203a0ba09061002200d0134442c034400186a0186540c202c0c007807455110040104465840071944142030030010340c10016182c0c840541c00301d24040c030304203200c800012030410007000e03021070400c49035640c0e0a0090310400d0100800c02151800000c11058444407140c0c401d03140034500607075405c40d5407411224010488030221594080c54000341c030042100d0383c0c00034100d13590355a0045010686000080d8240c00514403015251600c44d101c400704420190700041022408008444160075268090724081000f01c0da444185001d50260703c214010610380200180c0c00a07462600d51920903140007080c0c20801e41200c4000c0d6080b846100b6040c001e0780c0c0b1651405840241001c02c003900e40f10304251080414660707424000d010b0511440400c1d00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 918936142 1250 918934892 918934909
    0x210311090f21031213050c0105030712020d050103060b060a0f18090c021e0102071e0c0f060507150b06072a03080903011107031413170a2102030d0b 65
    0x914520307000705202d00004480d126849540240b25614641c000120015480403041c003016401c48014101c0f640d1820065407181e002520020500040c0800c074071205955000604a03c080801c000c1029491841c0c0003003600c0c0b2101c0100d2049030305000e6030b524580d010401c15034904103440c3c01c6454610030700c4d0f003500d00003c0b41c02421941d8140b4003422206a00012411484074075024101840d0b007500160508071300032954024402c5003291480d0740c0c4680c9655103107583c00d00541c5061074491303550f80300220758081035100c20040740003c9011400d10120003a04034103a002c00405200c441c58a82c0091000e114040d0010031640f09590103011042807102d00200350750414006e141600c5d2a410320510369084040c10a2287d03003020002141002c04070180d031a0b1991603190782d0040c044443c031140c401e4002200385080a550b01000140314161520440c0b8100004405000140340e203080440460301100c44220621440405020a141e40001140e51034200d01e5000203140324003400142041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 918937392 1250 918936142 918936169
    0x3050a0509210d02010c090504050a021b070603140f0a180210180b04140d05012003040212010e0319020a0203060901051f03330504210311090f 63
    0x803510b0140b5000080d48a0300c215030030515141192020703101654124261130212003420002541ca040422050516400a640040300714501504040c616844002e1030081016030503280e81c0701003c10404c02c1d40610501000001d09140c000813454000003031460300780050b04075114250b0392038480c1c06442c2d208a8801100354024610451240c1303c00c8000c115002d031500f8404404080720002441c00040702c116801c43d005500503800040d9588104003007190440b03025241552140405100c8508220600c00c3c685840d840850300e138102030040c8840612501c9900340e05a1400542c240030100000698105214807466104182d5039444121304040c5c44200094051142c801400416801904124400d01d08140500421050480d007840310b944640f0025181c1400f032080d0341d0130505210045150a80103036100c42d10710070b003007034a0400c45e20704031025150038005a03001d5241154411090148d40040c0ca014001c9809443e5a80c019114804040f80b003103082208059640d1544024003c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 918938642 1250 918937392 918937399
    0x7050a0c020d1412160b0c0f0c0d090803090901090b030307060216140a08030a0504080f0a090302010909020403020a09150806090c0405010f1514090a1d0a0e0a03050a0509 75
    0x1a95810325101d551407480b1103c0e001a8080c0700d09000f080550201941c400d810760038000d84511102c0d4503410441d4202a110b180d00910030042c4004207501d82e0000e0260500034002084000c44044005020200c0d5400000c015041008060780c184e40b4800c042d13041d5000b28400003819242140040d2030743c4115030000b0202800851400c401c0c144501e405034069006132854010342e64001348454689002c2c200040400c0380c00d1000c101e40d41c0b059030040e03901500c0340226078a0014003104010603504159141c00000304c000c0428411541d05ca901e21006048050301517080034155030011341000c0203130154200641c2d51300c049140110b0644484401000824140c0340d8504200c1040364540c00203400c40d901075400e0500000e00407c40300b40410840f002d10a02d00c80034070110300202c580d00c0e09107107441440301c014003c9601954030784180c4001884071011590441d451b00107810002c440080185d038025141100300c0340c0700030f00841c5003c0086d070725140c51a550450f00383c00307903510b00075190704070340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 918939892 1250 918938642 918938659
    0x806070e19030b25050307181a03190b0102120d06053a08120703140c210106020d05070f060501030605040605161e1b030e010f020703020907050a0c02 66
    0x41c00403214041c2d0003400d8080c4411018018214036136200c204070348040700020020000661420710588003400c8080b01035504400090355400200300740d12814034800300311314002060000050801031180340304510380b80c00740000b2660100103516041e00d2964a02c00500000d500f01001004d0340c4003801501000340a00c02000e00c107098104000c107091440300c00768460790300003104000d403094051200b6600580003858000c10149000f11610f01a240c0421301d41c50b01c80e035207003d40001e029540314a09a86840d0b844000f40781e001031040300044200b1078056190b800500903290301103410f54612825003081d95a622061400903180080050090501880c103000031040000d103030422400b96000d01030078015501d565847d03403510114041c1d020f0105040305150741044807034032480c05c6010350a04000c040b48009c105024003c08402c01e0403800152610303611400396811040301310203410782d031005140c420b0941d404100d26101c003030304000a104001ca60000c08034481d4000302c29165000e0031018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 918941142 1250 918939892 918939899
    0x1020f03070804120e0306040602090f0d080307271518061815090306050627011d07080a0f1d0a0308061203030a0b01022508160806070e19 61
    0x50000d40180d40071180d04604c0c0340100f161610a0580d400c98000042c0a880c0300d4039580d441800039400b80007401e411030f820000003540d554600d11035031000b500a1400603500d14046800074030313110f00c200f0391220032021340c28009144502da69650703003640e007034802a020300c1c004001c09a5442c2d65962846070f807040424800700300386034030540040f00c1e250183c0d000c0009540b92008070501c000070010440002d1300b03400042000c10406e81203030781c101307002900aa901d502c2c20311148071f0390584440f01030070303541c1c06e2001004255450002d0100c0300f00c1001c0c10b46140e0400110042004034003030700201143d0b440c0c440c58810110142d00c00c580043d09150050010001d0101107030b19582d8810007a0080f03105000001c0c1d040c1400280121000c40d10030155245a952071030410003002c4030440c0c14114420100161810448009001b510071030121000340c6191500340c159103400500266503280418040080045c00750004929400c071015040424400d00e2504c04200c110000d0713101c0c40c103001d42f07051000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 918942392 1250 918941142 918941147
    0x40f020a060f0306091a040c0e0a0e040b0109020f0f0d33090506030c0d080d061205010e0d1b050c04050a0c021002070c0302060708300702010b011e0201020f0307 71
    0x311410342c003944040c8205503940843d0030894514140541d039012080220054500d0943d1182071800504d0400425800100c0b0200f800071105030080c00544001c00180b00030300101c040410300501d80081c06500d440e075114000003141c0104102e04200c05004a50403c4180840d04804190b000c0160f80089044000c1d0318140d1025000c54014410707042200040380b103400754083d842c07090703401400030045243c401c424454249542d45c810b546801003840150301c510120b01503030009050400040c1103442c2d980c24040d08503940406044180c0d80130000300024941c11528000319000b0300020101d02180d00d0801c2400c0150110b1904c2d4450320b00010018440c21340d90280380c94034400c2d400c035580300c450001c0c610100e00c64124090300101904001300011300d80040182074041c8a42d0343c0d0740c00c203a06a40044101252280b0b4201c00035408c0304080900c205842c091a0b2010441c802804404014000a40b4000d001c141500c040d80e20b1240c5003404500035011a84080e8034850f030300f81d41c2d10703054500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 918943642 1250 918942392 918942407
    0x1050408030a0506031204050d051006031209082427011b210b0310020f030115031521020d30050412020406030f030c020906101403040f020a06 63
    0x10030102c516141c0880c40b60308001907282400c0054005040ca4182000100314076910003942c01c0300d19220340d07000701021084074080c1c071000790311914190620381940100641181716a801c8004a80e02c141c0c07950340106040100d9202034035541621000c40d407904a0914154034146031542100f007484415180c603c401503100d071148006807017a0f03600100d1003003021940d0010b000101100340d2051100720480792100da10406c8400c01c008e08440d203a0702a8624a403c0c1d821540c0204000c2d107000c8010480c09001101580401441e0f00d0101303c1c104403152240b4403064540110480301d0006e500106030040307140031146405030010706004042040b440c100c250540612980585010003404500303000000011050009285458482c12b050400c40c0ca111200444901668060345901000010801c0001d1460300d80c0e002e550b80d100b01c80300d1401070100c120350140219005000c07440c107280007947c0c001c00000c020b0760300c6e08107c5e640c1c3d01c85050880f9500c040c044041d52000d10170b14000f034060303001500c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 918944892 1250 918943642 918943651
    0xd0606030f0c03062706020c0703120915080702100903121821050d110f0703050904050108030406171305032a03070f12091a07031806091a04080105040803 68
    0x174010700c54030b881c01d006011104512071061511369a94075000507001d801401c007445060040343d09155880d00c51100345600c1c240b0160115000801c02d00c2409102c0c00030f911a0304143c10100d400d400c100720020b582e901131044a000781c0d695213112200f01440b500300c0038100352503028180840c40b11207a0400400341c0814088540c410324a0841c908801400c415078004a8a80c8a1600740000f0070031060150079401401490008100644403404d640180030784401c80c029a80c450319035510506100456006030440c5010791300c01e000401c840c2d40d103c4c401c401c0600088481565940f1805400c0ca00310540d40b00042c840e000215004800c000c0082c0500604100206981d8603011507591940c0c5900c10444064030781d00380b1404c5500403924201040200442c5450407176041c7d950f03005c21264404244104070144d1000041105c14036510001581141c0240d50900038030714940b5901520469242c41591460307a4281e44401d10715041d40d0603980201080070090203945444c1c034050b22507620454 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 918946142 1250 918944892 918944903
    0xd150203011409151c060b030a0f050c01020609030a03151a21011a0f0706091b05011706150d0c020303010f150207091e180201020d1b020d0606030f0c03 67
    0x50000c0c6000340070000704d8001d800040c0940c01c1c240a1105c40c682c600d400183c05a42c4031362200c14821a03918100b00d44030300d00b4010480300c0f6400180d840c19904040210400b1411035210700280217401e08003000f12000444541000541c04c480a5240030310303890f031030303011440c5154480200500030030440d00a045950310300c00c040340010111021240c0b0030500703001350704128080c006000d6682c0401e800038002c1c020340c0c521503130030000c96580318000c0d03441d48501110041e80914005c0700350300440a22801800003400c001283c55040311f40c0c09020f80700186180e00c101404804d410078003500101303c408000b12114103102070038a0301c4002c2c5da2a80207109607803a80340c2c5040e000620301c008080c0e50007461003d07405011a2450145100e01605454800c5505071107059a0040741d041e0a100300d0004c1200d0b40c00324461221907000180c10410200701040c28824900ea140c508440c045500b014a103030304a0784d008550b195414220300504143e007008100c184040800c5080c4458120b400007203d100d507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 918947392 1250 918946142 918946159
    0x9011d0103201306050f070609032a140a0f02040506150f090a0605071101030c1206090504021017070c05010f0e03070c0b0c0a03080c0721090602060402010801050d1502030114 77
    0xd2130211410312803441007043c0a4014410310340040e000e03800a140c10784c001d10700381480665900c0c03800070b4081c0e000020b0104150511044e41003080031010a5510020f140241c0b030580815100d0181e08010080020700c5070307030b4880000d14036603035141074190100000f0a269888614809003500e42d640701d1401c440c4190b0f030004001a540744034500310f400d010380c001010142c2c0001d48005402505a80303100905008000302d481321000e110f84220001042c04007000702d21401c0c00c0c01030128000138482c0c80030400c00305e0300c0c5001c40c8400030404150000ca03245484004032455080c0540100250094442201c0c101242441c1c15070000002d8400d80d80a10b0b11070300c0d02542e03070320700000610841c120030b1080d400409400c408680609105a4081021348203030380b1308106541d40b942d00d114001c2540c2840c000e408400603009038088402c001409007400240110304058001070000c42d81446280e10480512807140100300500f1072811010408103800d40d16540c403403002011282018180d180241c0c2407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 918948642 1250 918947392 918947399
    0x1050705030406110418020c0c040213060801140a06050705030708040e01061b051209010306050d23010227030c0306010b1b07151407050706080f0c09011d01032013 72
    0x135001c8504a4544481041c20044101c110b1400f0303400c500d4a05000c1d008400c02500e20340c4481c0000d000400c2080080200385007000c5d40030300804010380201d41d41e031005561808040d19061643d400303560721400e0103511850306250641c0b070b52040070b00042c1554000b00300001c64030344141e28641a60300a40340d00d041d80e1813842000c100300100c004041c001d680800c001c03845040d0103200410400d4810b01d0081802034aa2002c10158882711008841c0340350800c070105800060003107030020079095038001398030342100c54019950f000300b030011964070400080d540f0905543d080000081c900c070040c0c1030b2100344d0307901c9446140a0700400a003005e00b500300f826002c800e85002c500402070b0740b8804803506101c011008200c6041800b07031805280008100110008500700f0004940180320340d5669083c649010203c103420b041d0083c21001c100e03402030243c10166a00424042001458860006022844400101c0c003a1050359411016501e03610340300380c15076030a000100350704202c1c4070322544110395 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 918949892 1250 918948642 918948671
    0x601031d0a020f01110f06180d050d020d020403061505030f07081f0905070e04020a0909030e0f0402090d0605150108040b16090b031e01060513090b06040801050705030406 75
    0xc90345102240e4100085580061500074111000701d14180f5102c3d903000200484e052030042c00e0b680150b150b5000c0303400c1100740740c205c040a441c80d80205000d0603d44041210103400e6026030341c1501d6500b6008101c80480c4101c0c0d905940040d03800441c00d2010380d80b0010240740c00c840c680903441c000d001304001402c4d03500c030000b0b01c5030440708100300404070320410404c0b83c00d844c070006100ca208240c690043c080420001c110100190600006410076800d20748100050102c0e10341c8100b03440707401c2c894100d001c40d80129120074040c00c00da0701800c2905c40840020001d2041c4800d9540c49a2606007900038030000c2d0b40028820002c0b17001412100305101c0c01507411550441c0c0040100501000082c0c02c00c841041041c81034501d402e00709800d946401d2600d01301d4004072504400000101c02c1c5c0710060260748410350051040d802d00301d20b04003174180b040701c5140e26801042103282e11603468522940b107010072140101603201c000c01150600c001c00070495802602c056507090700f404842c041811 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 918951142 1250 918949892 918949931
    0x3110d0b0a0f0b07021309060e060f01060201060315090302070e0115030b0d020d0206070f12050a021e0d030209030a2907110303060d050c0307092003090331030b060103 74
    0x1d800d605032a013031007460342c00c000c444e010000303c9400050302c2d040c40200082541c0200c00c2420b412802820051900c16010070312800c1c16448207045a0410400300049622484c1306e004030080500301041c401e0042c1030981c0340c4110755000b40c96525100d8000100b21401d0034503000d2003540b564052000345181c02c104803240c950780401a504c038071a8018900103150400081030240d00c100c210f80744a0b151519124640380b0002050700c08500001540354000d030f0305000308400d410f410808400e400681d000400e40d15101c00028600f85a4006144261a682004003041c02e991002d10354925180400a94001c0a40401950105018000886c20711801100e18200c02c1581c0c000a500315900c80e01000407006010b0310584143c06036081c00c2c851510144441d4014100907000410380560001400d603500201045181650b036091003440ba014ad00402214407040e040400008440c00000a03902a004805800711050760803ca0010420a403404c1c413034031400c000d0720208034a411114540f5070a2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 918952392 1250 918951142 918951149
    0x602010b0402041508071704030f0f0305040b06090a0207050f07080c10020d08040204060b120613110d0c05091e0a05090408070f030219030c0519030210020a03110d0b0a0f 75
    0x40307081096075000070300c95003503603511103500c0c588008030742c01c041400c591601007608d0a6001402c500701a40c201360b04040f031141c82000c0c0d45070400651406444000c401c00000d040c851040100001050903010b058054514158102d4140c484098105e801560354010380d00c00c1208500942d260080f05d03107005400f030044110b241d0090b00680c003105c5e4084550b0b05d4014812a4401e903211004110590684054486500484891140b5007844001c0001d80207400f03407011100c0d420144e1a01d0101c078180b041d103100381b90b1410040b5045030015002c1c2c403c0d00071190300503041559808010a149696a00400c0810044c2e91006005498000348801030804840182400004010b035200168540c0c04085100d4020300c15030710070320500f0395501d101881883c0d081d0001010a41d001043c000e0502c8040d01503801c405c004d560041d850382d80a0748586e060544001144e901290f4155118081d4100242107034946443c6541c07240d410b41c8031070040002c079050a00504c2d52400100f01010b20b00c4030202135 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 918953642 1250 918952392 918952409
    0x1060f030b0604030b0a02090414160806041805101109010905130902190302130504020102120c010902090f0916051509030109080d020924042313060602010b040204 72
    0x15256120826009002081c500a400407820840040130512800003103004408010015039100c1450040100f6902c001e046841002400c1082c88030480780300c0c80c1185005c0b920304103040640d4444002500070700e03200400c0698441c8a0885408100c00400c070540305a0725910b04100d034034114a0812124090804400d01080360284244170900c0d000c0450344d0b0504244d100031602d403040352301041e83c080c80789200107207418045509008519200c00001e00b080e81c080c5041009103040d400007035942c180160b0b0300900040000d058131880e0400c0d041901d2982c1c0150039403650b81040c60f006410a40f0880d0041510b006468a400c070f0104142507003c12a88018001c8590034220901146650300413007104d03900d036680304050307000558020090321407207030200c00060301d40349107100703003c0728600382c4142042d2010704d1081e60909070480401c0d14203846100307031340d070f10b0460001807011014406240d281d544040f200520f802140480c0d0017001c10ba8070240c1c028004082180140f105038040c50258a06 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 918954892 1250 918953642 918953657
    0x303010806092a0d060f0b0f0607020d080913090503190810050111030c0f0a11030601060c06050a140f040309060c0206030f0705070f0503040e330f06161a0106 70
    0x820701c40880e440720580c44004c00d4081e080302141d4400b401c445510f20240c11607038035500810038926102415445151003074801502e40700d025400a194104144001861480c02141303050302e07500d60780f041030b401d0b8111500402c035212180c14120b54030703007205601c11111201034415408041c880e04100340500d0190207086901c9080c180159240c0c0000d10060b05580b10501a8254111007002040c24071078500000c0c0141800b282000c0c002c00b813070030407514041d0340000c00410499501440288045412000000ba103403216500c80010340208262050300004030824429011250000c641c050342c803039150b40510540e41d0000f92807500d040c0e00b010f03500c880c0510001349030580300640740760712194600d045840c1c03008036900c514548042c00006d6035240e2000c00c1c107000b40d0b04200e89540d0401010030746500b85200c49059464140e507100805158000e05091105c501d88860481030b010070001481b00f070315113007110413100100c0000501500e54103070840313041200070031070300100341603030083e560360076 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 918956142 1250 918954892 918954943
    0x301030b060f3114180705030a1403270301050a0e0d03200307020a030e09010f030303091109131518030c1502030103080a11010e033405030301080609 66
    0x11080007810074602c900c01d22846880f003028500d2285403d50700c03181d90758038400d080810f0111006821001602d280f40c1c440b0710280308079a400034040ca41c01d07a1082d81c0b01200103640741e600307082d400fa500780065209041d82d107041c2c001030011405041c0701c0058008016950b1507034660403d42d031f5801c0c400043d5400070f00000d020107201c1d0b009904003905100554178507601440d0400402c0e4030490b80d400040e0041800780081540c001d41403400000122641c1c401035040c031152070148071040c4030040c145a65404200d04000c400801500384c094020817664031071510110603040210440b0080340e00f035007580c4084102074068411818448404d128140c40e4064555084c2c565801310642940c20300409051107035182224002103029500c070340d0202d07031a003840d080050889039401d4600c90480e414200300e1030070041c0c008240c034072040301d0b0090207400c81098000392404958079409100200800c50315003042c4030b000802141258450000c4401c41d684003080c240d103800c2c80e621060811500c56400301d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 918957392 1250 918956142 918956179
    0x141510050315040b060d0e07090509120a0e0901080123010b030609071403071206060e030a0b180118022419140309062d0610180b0301030b060f 63
    0xb08104840580006000f0350500005802500421140c500c060f0712032560381d1520400344240340c010071031200c0074440c0c0c1c14121101038030303001c1103800c01100b4180403580b03940c0d4070b21580e032100c40030348050100a01035840b003103018041c0c4501c07602d03030312210090080c560300307a012440310f28103c0c2e2500c8109030450320784d0000c0111160002d0100d17030030040d8002040047c0309552000707500800c0326031200001000410b4044040e03c400740d000390305000c07090803030b40250380700869824003c1d5481400c0e40750036501c0041c0800e001c80c210315010040c1d0b00c3c0ca11651554000c03052004102e9000329079580c401040c101272450101108100251010307000c8c0140740b00b0030a50f5400c1c88004000e03080103c0381c02c00255101c68160170440b52140968040d05c1402003e11082007441200059581101105514000080782c2d500005e0304e01c1d030080303864400603a0103234071540300008440c040d2200c50b00c682e0754851140301160000e02065410950545c04208103141a41416001809c003410604d04501901c503074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 918958642 1250 918957392 918957421
    0xf07020723040204150e0f0108130209180f0a150903090e0903090d05010c080702030a0207060c0f1a0910061802030406142e1a0a0c061415100503 64
    0x7990781240e002e100104200000603180c00080080340d80f000306030500d0b9401c000d100085909801d0502c210b45090090144058401006164060320060600e86421003090a1640d88a082c80e00078050301c000c0c0c0003410004952105407034015503280d0801b100100740300d0201e03241120000c0204041701820041008040341e1640e03c00002d030309513070818010f40702043c451f0384003800c119200d940d0303602003003010354000c0701c01ca401c0104d9100a50510b211031a0107580c070060ba01401c03043c03003443e010007810091603086114000358412180607002140d0b103908506100150341c0301c1c155000341445070300e060649100340000c80d41c130486075900701e4810b22810300083d44003500035200c85803103440040700b01001d95080b500a03003500c41c0d001a03e0388041c5038004500d08a19491a0040c000e00041160200010101c1c040d508581107843d9520440c0400b030710390141480c8010207090402c0c0d004a074aa09251503144200640500b851021785076404020644001d483e206021500a102003541e20740d58401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 918959892 1250 918958642 918958709
    0x6060d051203010909030807030b0a1e1a1b0c010f030b1c0b01060f08100303210906061701021219060503030304061a0607120804030909140f070207 65
    0xa48101c0211824411803592090300204206501c0c2c6030200c0815500c07600c000e510410500d0200b108054000000307150100030710525200350600c1e504100108124202030004000345200d44c2c02044000450807401e41200002c03044885104551201841000c6002c901d074120581d2a00300f160901d00080d0020082e00980c81e80000702c0388026560208104201d803c0140030b03449800c0340c0d6251101c010b00010034100d408003080b00c1603050003808004400b4800c2901c2d03240c03c094801c1641c040b00c001202481d1102e65805038200f40e040028003015234054400d95075400c91612018071214801403e0f031144a103120102401e60001603401001c61003100900c8204280c0812401ea55000291540d0019141552115901d19410b03602c1c40300da04000080040503182c90b81000c1c550f40352001491540306445042c402d00200080c2003521483d13407140605140401040790103014541d0000c0d4110465075240e4003011280803c61781c500000340c01e011203541c5203c0d007251244e120038a0100c5a85c212 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 918961142 1250 918959892 918959903
    0x12050d1d1306080a03080906060102010b0a03021005160b0406050c07050a020907020309040e0708010c11060103030c0609170d050c03010f0b130e0c2502010e04020c0c03030a050c01061706060d 84
    0x2c80401e12680074000000c040e40030799250005402c04540550030068054500b0b4156858911402450f48901c81c044086980455050014401040c41594a881040542c8d1180c1840e941d0b0702080044d443c84090055000701c2040100365111582828284a2190b000c2c1c01c0343d0040222500610700f0f00c1030b4542c81280d07403054074100481c54001ca81a01c10510301e00c41c1c140c02544050024400c03d1240c0c13541e0501d14684841ca00c900c2e802195100d13501800060304015600b8550303014003006420046045501005591200036044200b924581251450f144040d08000124088400d06026207059451207070b05021501c2c9071041c40e0301964081034002c0c01c1000481c50004e04d5040281d070b5240b1501c04596101d68603580024086c5294040485440d44181226000d0000d43d030b200d03002c20b00c0c10005540040c2d0f240340340c40d0f04500d44660756002590500c40054101101c5074001c000c0e20304555041c009106003900e03604426040c10f02c545c0d407184594850000512285480c011284800c0d0060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 918962392 1250 918961142 918961151
    0x10030b0910050a0621081c1b03020301030b071805010c03270302121f0b01030f0c03020a032906070c15050301031211060714120112050d1d13 62
    0x1590041d2801114184203190b0344d603a041080100c03000d044059500f0b5220341200340d05035591084114000c1c00103a81001506200b03210142e0344503803108590761031102d0881032080f1503600c028007a5100b4041121a5050000810035040c0240720405914561641038000c0760b083c000111a028900d44040c0c00700300740303000c42200c0051440410f40b040c2031088807003100a4294014031070b1040c01042164030f50380c040d1803c464503c200700d6003040512500107010078600c508500407406000511402a41149415203656810781c01d03900416804103161070902c0326000760781c01900203140c40c0c445800c6210030008040030034500800104865881003104101c041d407640d1644003e8104000414082400000184103001c041d4a0408040c506407030200202d4401100c61038039800027800301c40c01d104900e0400a111000030f4240d80d64090401070b00040c0c1d40e564103000139440f54800c0c043c1c4132402020b102400c01b51041c0451940f688d0558101c01c040301415003400301e450700441030600c08680c0c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 918963642 1250 918962392 918962413
    0x20a0c02040e0607020f0613020f151201051e1e1801060909050c04150f3f020903070b030c0d0603081b070510081f0f060210020310030b09 61
    0x491041a90b648007080040400b4a4030b484080d2920383c1c43c442410450b8800010400c00950341c0f810702e0250381e415203500f6010307191540442c0c14100403d20040d0b010304089514101ca00c3c42000380ca040321405c070f50010007400581c1c0c2215010f00b680300c1540d00240c03070a100c510201010394191441c2030000e00200680c0d12003d01070f6030b850030700717812070320000d05491003c0103072907101d015558100b1040c504051405103800c890651035031100c80c0c22028000c2509820f04900d0041004a000316103000403020512001402c1882c200c001c03100400b510010705403090180c900f40c1c400d49009100180c028020341c0d04041c803443c032603080102080002c13a010003074500481d0243c003400e8019442902615228900960f0081042142c100115032a0340203490810503907440c089901e09403041c40c280b005158a56407503401c400b455950b4404d0a00750124400a60190400584012988107900351801c40507100b40c0103099100c16031301484840c81d05c0c40140045414080000d400250350400c4603000181e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 918964892 1250 918963642 918963649
    0x150f0403080f04030210080108071d0105010e130501060207030201091d0c0d0e0d0903060506090403020d0f260610030204060801032a0e060a090204050d0b1815070e0d02010210020a0c02 81
    0x1b19050100700048883d8010042820100000d0001d803c2c1c071030368915840c00340c02d1103100810b0148582410041c4a1402e201c00d42c03210707a0584e201d0040d507a801c1c0107941c0c55240c065a0340780c0c540300490025401c2000001c005a0200105c2c003c1c90b0300b404d012099440f441003202290304005005558541c1da1b0f1620340394803400300301c5142500159115913442501c1c40c02c0c1001140c1003780414003d040c01410800080c0d8081b40445043d9400d081c081401d82c03038020122400007084000e0707005504150780740c131120095200c40c0e600c6001d044801c0340c40f081a19900701c0690056118050105221800610005404524040280000c41001c0606560400195814109541c0b143c1d00c0c1808100a000190402061081c050003041c0c0081d40740c02e02d40408074450344005507003c2d1441e65113601003840300c4500c0c6040d510b000c64400c200d40000d5a16815164080c1e401d682c49004520300400121f85030510700b65034070507143c058014114510313901c003000c00a94040d42454082152075021680140d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 918966142 1250 918964892 918964909
    0x13090302031b0706080108031804050a02070803011428030f140610030c0f060804081e030c0a030f23040618080706060504021c020c2a150f0403080f040302 68
    0x840b0b008100103807604030050021801038100e0106500708000f0024100201ca09802c208682030747d0000c3c0c56a00d01655100a005800c401000c0713090020000400d90b100c1e4203150b01400040307480d6040c40d5410180761901d1a408151051011100c080800200d015400701203240c40c06040d01c01026440040d0781803c0c914210303105155890140f505006010385100c07540d000c0c000c903c5111308800c1c02d00102030540c00e030051004141a41c0090110403030008040b0411a40502c0440750380c03242405590000036401054001e8006440c5c10344000c1c14111070301980d00d001c044c001c90b110404105007080703081c0401c020800d584503a1202281030502046450480c0c00e60b001d00032440d1100c000d4904502035515a230302551041d401800340440203c001d810800d00011825030050f5580102c80c2c0940c10031034521070110000c041d0b48517a08182d60303000102920542c3c111000711103040002c0707441d840c0c1d0042540f41c1c0081c4109100c2800000d20944c0141002a0118003840c1455a01d07400a451803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 918967392 1250 918966142 918966187
    0xd06050a320d0303050910020307140f07050102031003061808071203061e0906080115051009091103151509040b010908030a0f1205090d05090f090a02040501020f0c1309030203 77
    0x4e58a204010a21b203040c4414040825103010652842c00c0143d4024650010b414280c1c50500d40000c403905440301400031584540c1e8094020364407490900d5030007540001c10f00c002d951031401c202c14250926401c0034042c5d4039944c031002c0d0700d040c84100c0d159003241c0c1110703110718003c1c1030ba2a1400f003401925110300702950301d0030000d10030301541001403000546034940d00c003014aa0500e40502e0b0340d0140c1501c0c20055580950300360302800c0520000302c50880301030703124a950b82e2401406c2118040018000c43c40b907200200d010345020140014070002036210b0b042038514040502000078140340c41d400c00102c1c00d005162000740365854180f1541198010040c140c041248510f8146d0050303000721082400404c520070030455443c150541e152145d14040b0321074100301000540c21301503600d43c0d800b00f102c440701030040c01040c90201c1106000750b000707001d801e01611400c40002100700c0c0000d41213803070040151080d51103d0b021240d4401510100d80111309500040c806a011803d1059244906 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 918968642 1250 918967392 918967397
    0x81605030307030c0509030c220f0f06060e01020601090e10110a0f0207060e101209053f0a110604030302040501090e040503030411240d06050a320d03 66
    0x2070342032422000e01110760068035003090081c20300030800640c0c1d011030451803235502900c0300c003082040b038501145d94181020203820340ea440c180040c0703541d0200364000c02c444415514104240c0c1d46917a02943e0303510402e00d6860060f840701e0010700440d0003d40200300d0040d4140704880007000d40281000981c1c4403041c9801104001140090005510011025010300d190015200c51420300e040282011043c030205401103c400d501541028403544800c0400c511004040010301441d14044d502c5080b05c405060020040314400603031800641c0c442c905840124942040800c0c003503d030104660006c0c100381c1c0034480103d04001204900340801e0b8070a0b03209a800580d10b034240800544141619040f41040500f0b62081000207a000030889030000e130007500c0d40030f041841c131001a0390244081c881b4104003202600b00400d5040c8100070704100320308114107008003030316a001d0284400b10b80c4242c80705c844802c50401c00c00e541007103070314200340002d50040c101c03d1580c10114506c1210140110b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 918969892 1250 918968642 918968647
    0x305031902011508010209040614031207050309090f070914130908090a180e07031109060f10020714061908070212070c060206060d08091c060f1b090b030403080408160503 75
    0xc2c7d031410b845100044e0143d87d00c00800c41d50008007181d681c1a819846a07c0780c50002684000d1000410946120040003012a041464041c1107000c0c0b01c6d109551400c00305012072404070360b1200c8609181003640c00a00050800d44a0300300b14030203000d02000c05e848a990400c200c50307003038482c2210500509024004c0c25040d00e010a0f6600c1101c1845103860185d4000c042d003400007a68121200c44204011600a90191540030002e034662011035501640a0300308100001c1c001d0700802c20030101e801030f0704401d401c41c540c8018003580c0d12480e0f0000c6801c040c6a0702514219020f010031503040005031045a0340b20151103c0315615502034041a40d034100b4416040150390380c1009069400301d030a840b1a1641191580e80495500480500c0343c4604c4000da03907641c4801d011500e4104d840c0e00840144003101503804d4641c0103108090030054408094014680068014165001221422020a803455070f981d1021180c03004040c2046583e00e60400c0100c101d101c04110000c08a03004001456 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 918971142 1250 918969892 918969907
    0x40c080708283e030103150b030109200d0c26010c020a020406050102031804020912011a0a0e0f1506040305010f06080c221109030a06140a0603050319020115080102 72
    0x3c091a0501000600072402180d1503680c090b0450540303044035405842c0700e007582c0322800000c024000300b10340150190700c2c02c244a400c1c4048602004200c02079582004021100074040c8405001e407404041c1400c0071003501008000e01400d2a00ba500182c0c1018034402021805032a0944200d0b180000050b842a502c00f41549040e104040041400740011458002e03900c9041d081030410b988007a21603a40402c20903840c2d00c42c01000205407048800800c085d410b1052040d85000238001d00300d010b4803103408041030f050420414940030300442210090076543d2940044461410005415006131040c04004000780f0240590300c035804c506000425410b06011410f8582491941214400c62105100401c45215458a02e1080441c2400454090300c80100e40c0403d101d44254160148103d01c1d40300d06014017944080030001500c00e0f00c000941350440e0305d0042d6000c0b404003030320782d800800c140340e00c0000c60b6041e0141d00390140008100550b00c074000c6610701d81d650f4880e10241e500080e030003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 918972392 1250 918971142 918971201
    0xa1703010305060a060e04060b01090f062303040b043002150c1c05090312040807050601082a0a090606050c071205071e080d0e040c08070828 62
    0x144c3e8400d02c00d10080004514009440814000c007074805420151b55141c0c0030010791284810764042c00c0d0840056101c2d59482e4002010100e6045000d0205c004400e52842d800702060200d80c0039903000b210480745a1183e40390509054281040703040c01d90340409440c2e80b1407000c1c204640c1c4a0b00a500588000f4032140010040350781c00408d0a00c14030030412488000c0f924101c40008180c0511200017078683e0344480c06461840351340041500c68251108010401c40d0600040c111103129505841450360307136416070b42d0365003c5080070b5000a4551758525410303010055210568041c001c1c200e04101382d82c0c42080d4110740107508102c00050000031002003444080040800030400801d00600c1404030380c943d07603112500c40c0581c6044011b0030b15a4100910008082c03000f0707011900035119000c001c44400b0b000512452503250045003002601c0541e1401942c40c0c40c81044503482c0c84110355545080080200c002c541c1c1002404404406e25070340040d2845100c03001d040c11481c03905e620741821201c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 918973642 1250 918972392 918972403
    0x3170a0f0c0210030e0312091e070b1204030e130e01060501020a0503040614070c230f10030203090127031e090b030a02070506090601091b080f07020a1703010305 71
    0x910078099010088001600d643c0c0c2220200306840c0390015130743c3e2461038002e04500c10b00c1000810154108180041410081403000540490301c940d100e00c4d42540b0615038031040c441c8950b505510080c848210503142024089910500c0b83c50440949501d52000401040411100ca0950742d9030740e0207921201401d1007144041c0009000504003c0101d0303a445a880c400c1d40220801c100b4840d03017542c1c1c440400c0080c3d4840c04c0d400f5501c41c0c030b500e882d085005244948488040c24404c6c504600b5019030614144c03046410b00040d0100d41c1f42048600290042d50020f4010f22a948da2042090310202c0100410045110450382e5089002420f0034002c060382d4242030fa14041c41c880040540019401452080840d0a0050015100d0362610143c0f0020f0040031030241050203000c0070024404400f2909a0594400910411107085404050f01c103100c07802d41901c1c00b01c1c0d02d18011408039245076420581c481014811244240c500e0303660714041546204400102d0710f000b00042c810030006020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 918974892 1250 918973642 918973667
    0x30b0301091a091b120f060103060c0807030507120b37060e0a0e130b0c0909090f0d03050a1529130302060c070b0c0a050c09040c051903170a 62
    0x149a0000d9010b07100c044e08030f143e00541e00c40e0b14449055611040c0a20501e80383d01c0b42c190079a0265a03480c10400d0140154024882c001200035000070340441c000d200f81400b540c40e640c0c41c2100c0b440e5032280c090003081c66140300c503401103842401075000e61041c000d14000c2e82e495500381c0800c11800d1b11003842003110350031450a129180c9108002900c560504008a0309020440c0708180c8980c28030158140a035000903084002e49400c10640d0b010741c03001810300107010b5804820701c0d9941100140c45048040c1c02e230515401c4840700f103403568443c2e0400d41d00b1501004001915a41c031150f58105411640c1c0861440340b014411941d4000c2c1e00b000035070141449035202490b050041d00780d000a0b16841c04000d1091a000c20060003084041112401400c803510b001552544500e0041e6550b01c848101103e091055110115441c10581507050003142c0c002050700e01c3c1810041004a0b460504081c224440d25282c0b001003c01d1501d84840c00c00007482c000c8540d99111080001d00c048030700070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 918976142 1250 918974892 918974911
    0x3040e0a0b012a02030a060608060702070f09020906160c03031403040b0a2c0c0a12050309060a1b1217060a0603020a051215030106150e06070201030b0301091a 70
    0x401d1603a2690700809400c007080035608030b800048514501d141090144084003a400d0311451928004000f2240c0c401d1050b22050001c1f038016540d0301c1c00c22640c0c0d030b00e07a005203118101040c00c01c100c01c01307058000e8800320000811a9050030943c04180004c1c1e17040e0a016a00d403513010100b0014036402210248175003098440d03d40c17541c41c00e911201c5c10148040c0c0070b94481540e522580c5210448118000303c4290308680d11000700b00c10b58031541e55510714400b8184900c190769030000d800c10011401c5070041c2c2d4040041e500b01a416010004940c10401043e410300500d4075040c0300911001d900050554410303030000c452000324120040c160401d101725074480e0000030060107450394500103180c00f00d80480c90056030f51003180608403440c2c0070b00800031b00400c075510309008041220b419017080156043d4020400190f580c841001c0c0407008903260030101745c00050288043c01d2150091a0650040c103002c242840407001090071145140300948215181320981c0300450b243c1c107082c4e9004030580323 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 918977392 1250 918976142 918976151
    0x80d06062d08060a0e040c0e150d02040510170f0c060c21040b0c0a050105070c1e06090804090e0705010203191107080a140d170105060304170c03040e0a 67
    0x44108201c0181c112104018802d81a0024030540e8a464059010346943d140403216803c0c94507048849110ba4001c0c13000841404000540c0e8040c80082c0d0401c60030002c0c50750084007002d4082c40010103001c1e02d02143d10702c800c038002c02c00d4094040b0700b4203800a1180100003220003092042d04110789111043c0c419007003000080c0e03900350001042c092203c03040c0403a0f03110b4000d107154480c1510450f0311410340080d02140b44440c0d80030104141c000103025100034000c2d591811402c0b180e000c80600020116220b80340b40903590480301600c52600c9110b01d0001910107116112042e0580041d80602803c5459403580048078000b40080c200a200c01c0c00118103007002070702058248000c2100c0c910400c102105440c40070401007043c1801494190103540030a203c0d420070520004a01c1c034229854841d500c5440300c05481a450140c0110005006202603404c050400c80c0aa00190003601c0441c4544c144800b80d080d484001c005108468001b16a541d00c1c1000140503500024140e400311480c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 918978642 1250 918977392 918977447
    0x1a0d051501091806031202011e020f030f04050f0105131509030e0d0f060e07031e0c18090209280204080a0f14010513020f0d2d080d0606 60
    0x3880001c10750b4a03c0b0203099608021010080c020003250740090300d2049210398140c403a58041d841100a0f55098420290180764800707440164030900720ae0b0303d110503041001403c44011290b4039034010f44500706841c0c00c0b1100300704c1c4a0940348142e58003052548030a5000040000500307034030341a0604a101401000d42945010340511070b9003031203d014401054240003005800440c00480b9580020700f005200c202d19501070351802d440c0001c89000b500060070442125280b0045200954040b03c00400141048007a119402c1803400e88040a42c4544007040182d40c1d0f200d5461103007001584c0a107400e4007299040d58040d8003048a0302800b44104403d0013030b4480800c5460401c5e0b048500c2e80c00c424002d1404200009154084070380b203500e02810300c8004a0269070135403009008032a5284541986c004100170181c0c0075500400359526000541000c8002041ca48149400a4180c2c070b903115054480f41223540c0301070910b030301c80c42c0d075441305111403600005002440d020000010b50841c1c038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 918979892 1250 918978642 918978647
    0x3110a080d080115110303010308030f011a031302060c0a050c03100606140a090e0702010f140c0706201206091003051f02040b0f090307150e04020c01061a0d051501 72
    0x2d0601562150b000000d000510341070144103403200e140b44031800c490b52580d490800050f642c03c25540140f41901d074400010340c881c2c111626624805640c48040d155171124060110a090f2a000403078115100384400840e00c001401702031b05d024044d034043c1c00790704409410981083c8400118002d5545804018000258070100a0712100d081c042100d039507080c641e0742561408202d5003c0c1c8188012001001940750b0306400c1490380011302e99081c400280080e03991840800101c0707404980300d009000038404503e15401405120010014041c0c0d078074a03c1c0c06507669136000700e00040c8008004401d009140c280100c00399840410710f40401e804a003141c0d207543d2125255441c1e0394000c5141c2e18203420581c030318ad040710028a0080340703481d91481c418401e03082c1908014001482130040182c00550b1420354010401800c0c5142d0b5181080d00202d01000000d400c60180c072241c0390350f60600810700c0004441101904015800059100c114001401003500e40c01803407943c407039002c0121910f9598 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 918981142 1250 918979892 918979907
    0x71a061906120e0d1707050403082205030d1d030a050a031809090c0501020d030c1b050a1e05100209030c0603070309230c0405190b01140403110a080d 66
    0xaa0500d01503510b046002d030408090100e900521070035002ea018010310311344d00420b42600d200d2409207454803907603801100783d807240528070001c0c00b01401040507101118001c807003803140200e85804841c1007074644021032b01e40292440c541d8042440c1e0004401522500c248036403042c0d108078020a21125079584554680d1a100c3b4000c0600044a03898001d4522440ca400087d0203400403c021076002800c180044541d41d106050142c000c560600c000180319024100c40440b880d180e40ca00051500f102410100c20910f0549050244460b8040040e074946009540750400d050441c02ca01e4541c10403600700140d88260405da070348100000785541d2004189402002c00441b0310984a54030040250081c20800300010030800c01e42075040003403c507411000385000c41d90340841341c4500c0340000340000c8410658294404040e1829030200b07141c40c1e90042408080d0624141700618210880e080700d9821a0700b044a186107403100080a0f824001780e51001042c07408010083c40355004000b402d0403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 918982392 1250 918981142 918981149
    0x609100902100c0f050f011a09040f030f02010f0f020a0f0503090c0d170d0c03230f070311040603232206020f1605070609081f060308071a0619 63
    0x4a0484596000c4c08109100c03000d2254001d016102a224400c1e1114002e06900208440070307440b03840070300c034503003040780886208640c08030000946600d1510142c840511100f003070000c541d00c4080102c0c800c1e01d140503803100c00c100803401507224200040f0140c45010a2449032003000300a00400c1079210700054000e64940055a08903082c07407a504040d9198540f520300b2009100e0b0000c0e4022500d50542d000d007221000b140d9042001d00002c11302401e1005829211043d42c1c00c090020841c280c0c001407410b90001000d00300055004c04070300025107150030560101c1e01081e9600d051070500b490200170000304400001889000d0715003655120b03040c072203441d40504a00034040842d4100541395044070f80800d001c141c0c00e61103075004030f070344c40714040d043d94100c940d402155800900c042c0a072820009a5004102030660030012407513482800c140986141d0700180c94201c0040407814800003820154001d2011810140e502c4101c06a180d0740601241c2c0101648103400c0340d010302410b20502075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 918983642 1250 918982392 918982397
    0x6051e040519021906080a0b090105010e0111010e06040f0b010b0a090603090311070b0913060e060913021f200309130921260610110d02060910090210 66
    0x402e40c900124241c41d4024400c1d0510102e850703c081502d9800030b09051180142c541c081c0300b01c41c1b04a040c441011828424a40410042255a5490740c0240003141000c1c408000004100c1e20304c0200c40e15000302030b134054480c2910b0111390014000300704000c034050510503aa40b45402e15a10000301162164400d6004051b03a403a0843c0030584070f940c00440c0034000a00320361411343c4485640b1402d5211040f16445096551a505080703c09401108201c5000281e50200c030750b160802c1c0001401c000b00312460412030b528500e401a03580d0707800142c01d907042c0703150f15410b07607036640c00a041c0c203c0c9101e40450f007032010154080240070010407108911420b0780c0b6851000d201564a03005031040300c000038400c0085c040c001c500c0c1d07245040c8080144000f40d481c0d5041c145410030020000c04448410540100020300040c0c03281410201c003458040c0c00e103070003a00002c0d03441d41c0310f0800d5603145200005801c0501482080700c400c020102c9500554002044003400c55400542c64085c0107540400307 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 918984892 1250 918983642 918983683
    0xc450302101d0111030d050a050a061703030408090604170102072306180c06030a0b0f0a03260705010e0a0b070e011706010e130e0d0e0f15130306051e0405 68
    0x1001024001c6c1c07442070215240c2407100c0e091040102020781812503040b0311140c68108001049000c1641144d224a12200a9881c648554036050081d0b84920b24041d00848200400100e4548082d4800c211143d030f500011303200c40891503e00101c42050314800102e003d6009961051140821130a80110720042c0140e11400308800d21810688103495160b8451004020400440640e801222901c0c3c0101c90342d0300d07804d2489080000401e203070700001d0f140400c1c107500c840342500e032600700c540030400c40813445d81418030b0f9039145802c1d2440350403261940c0d0401030140c0300300140b070101d858105003e130801103288900c450009180c050600f0544001c0005440800c0d40707640580344110351080041c24111501e1181e403030f03110140a8100e03c0d00c015101d600b441840351445140383c1a88041c0c010981441e2401c072a081006006444d452045140810805001100464010000214411040801c00b480d28181014400503c08000f110f460028010000080c80104018141010300b28580b01d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 918986142 1250 918984892 918984917
    0x30a1209150c110109030c140613060903050f042306041202040504020f0918191a04030905091503060f04030c1e06020d021801030c450302101d01 64
    0x44903c1c201da00c1d0004954680190201450b40c00701c000b52800780190304c000d1110b03002c1c2250540c0c8a00803a480120440e2840c1e118000803c82e03004000040c0c028078045003400a110b8045001e940698020f4905d10402c050311118507c010303078104c000036401c132055410240b8001500a1701240900021f1145a0b070b080010219502c8070740d040b40c0e500003e058400306140c20b001d100c8810381c42401842032403151184c0d0031ba01d1501d07004400c1d5401ea003c44d030265a03454401000340d0405d800741c011000d000c142080440e16880e10a180707840fa802e400481e42088540400b8182041e00103032000c80203032400030401012940005510b2010f59100c0c103103100c0c00700b1010b41050b079130103c1003004240d5400041c0d020051280f5801425008054010390054411054010340c2243c9411721480c0200e20010f2a02c60702d141c15000b54820b1b03092840c07090b0782282e00c02c20426030300d84880c00b101e084d0700c01c044411310035410701103214464107000e8200f8403490b40405a410f0071480741a131219040003007484000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 918987392 1250 918986142 918986147
    0x90d050312040305091e010504030609030e031c0311090901030f03050d020706090b06060901121e0609050702060606030c030103060c2007080d26041112030a1209150c 73
    0x70703102510704040c020418200b6103002407090f07002d0b0035514131421900b9500c00b03545900030b1010800c2581612860b00c1d1601e90b64802014020202d015000d1184039212007825440c20f228064121300c920811010081d44185c028080701c000624420814000f441451016152045c11307e0649412004c1c4030721441c2c80745030456061040e8104c01b140c86001049140070004181c00c450b505622030080300c02107503200c209019032805440000c074005014a00c0140700c040c1550320000c18070068002c107000c0b82101c141c020040d0350b403981c00f400b8480d40d82c804004210344d0601c00b05400400441e59203140d41015210728440f030006020141c0f0040d07441010400580c0a0004d901a00f5401c0c07402e0028601007000040d1915064851450035000d5046130311681e61151600b982c0c102e038600701c4100c2041c00180a400b0700000100308580104c9a40c3c0d1031141503030703181c0c021078050060900543ea41c0728000c4009110804410340000c86a040c26445800620748a800d580c04410100300041c8035803038003c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 918988642 1250 918987392 918987397
    0x2030a091a071b1503050603030a0309060e030f070606050a1a0903031308030a020106080c010207090504080405040e030a02010e150402130b100906140307020d05070f1a04150b06090d0503 82
    0xc041c030510b01c0c084150102520803400c220356807000003110307820390308105901b9142c2c1140c1083c1d040c1c04c00c0184000250103540140c0038030740240c00005020a08103945851035001509500600202081940410006015460280009484000c0301c80c2c44d140410107850300509560242c0076000c1000c0400d610100140d4820003060407614125030398a904030394981d40258070707410055091083c040340403180000c0070b110241040e4010040715150941c02401004054411a5009800c11000a8550310b40c011925003241c0d04002c0c543c3e43c2000d100103401c54240012020084d040218a0005034001406d1941e03c260151041801d442c01865103600515005821591282500600c000b4859205400500356101615010b00811698042d0742040c00126034000060b88003c0f141c958043c807031409408020f10955110354074440d180d5440009212031080c500d1503004000410042c841c6421444907044680e40d400c002001c07030a004203000d03225001542e030040c100c01c0105070405c00c04004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 918989892 1250 918988642 918988657
    0x420040612020f0403110909011a040e010f020f04051806060a03020c01090606061101111623240f07140901020a020915121522210f02030a091a 63
    0x3d5155a60b449150014070400c0904d03a080c01a501c0384002200010140700311140744802c1c80406550305000d00c1040098140030500401d955202c0c01d10081e103202500203005061404034009032101c0c140384c28443c0403012660841406500301c010b01ca20781c3c031403400301c0d6170b6202189005607454079500102800741c000ca40340201080d250410000e5955400704244054000704002170180c2e031041800c069890194a0110b440c8411103001840051400280380400c00c00074407010b10303092580e51505080901686403003500d285d81c20b551480044407062003541c0200705c0c120800080c180f100d0001d04107035495060301a800d00c00280140c2507030080190303940490740203000c5a540e1408003414280d0624031000786005038071034000644500004160ba1030310f503003c07113003442c1195101441c0010350540c100d403411007510107020810108071804140307280e8a042d052102055106800014140301a1a404100310b41050118180590344200001d08403181120b803d5031320602d2504218640c0300760a03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 918991142 1250 918989892 918989917
    0x90e010209063f0f041416030618020102031206011413033f0210090503090312190c11060d02070506090c0117043207090207080301060c140f0309042004061202 70
    0xe110540030300443d4409a27407003a9001d0203013803403e00301140d80002148000340942c0040c00800e8090701101546c550180c41494242c0d480d44103031080b079040e41e100c080c205100c001070210a200f40000c001413a804840d1010340f00c8400d141007441440307940e0204614403031201d103891f12410043e1080042c81c1c0701c50b0f103006003000201c40d0b5103022640c90340403004180c0070f801002d1036038900c40c1441007545c00700790890440d056034082a0700100c0d5010b403402e05c1200c20214240000c0c1103601c400c0c02605500e01e010743c006031b6508031814500d00d4104000c1c0307040540c2d0b002d0f0700d801a090341d0000c0750030b904080442c2c608050752224030382100d00300c0090707907030645d400c1e5104268195550307002102000d1a11396030035102115201c82d8404240d1081900240142ca010001041103038465480b4586c01c0780901034100c07614881410041c28003120043c820a035520228000f5600c0c03070244608248640302e10500040c8900c044901e540700c0c05903104030010300181d100d00c10140c500c2d580480d403034a0401c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 918992392 1250 918991142 918991153
    0xa060810020405011707020715030908070312050624090d1a07080c03090615030a05010c05040f08010626210301030c0e0907090e010209063f0f0414 65
    0x300000d000390003d2160500092500c20428001c0025104540c00380b06d00394040d10189003803030b00740c0d6000c0900c80d10510400d691200e40c40041015003010348500c1e88203980c1d00d10b01030075104002c015200003400161044070400c88507504400140d13664004620035050701380e16048000c00040e4000394082c8040c0507002d001ea041844200c0c10607055200d14080e40f0f55181701e0700c3c2c401880540c0c2c0001c9031514441e901036000704d4100d10300e0b00402d840000c0020100c80241c1100d540d000d094901f10340101012800c042018006488061044800303004404000c002440c130309010340c1900d20032043d920081e8805044001c5003800d051140380b0b8806001501d03999001000395a04d1450b40c000d100c280c80911030303181c1c003044445502003014003c81c0e00100514080d8101040d0b40c000304000b5010760074030765007002055005d0701d0b400b000c3c0c020f40800c1c134081c0b40c034a113245204c00480c00200c18004e200c85070342070499540c0200c00c0560740d00200ca020000400f82d8031490024003540c01f06500341d4861280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 918993642 1250 918992392 918992413
    0xc0b03091b1809070305010509190609230f07091103010e06042316090501020a0311030c19020f0103230c1218010608060907121502031801061406120a0608 68
    0x110041101e100b80001c000c0c5640c0d544540e51148442b030b040c1a04010250400e00100c1e0454019400c42806081e4000d14490300d041100e0001c560310903c041d0030741218031207881010060008100810f2840e40a20403103507002500b072528031050081403803004e00303c00810456119903200c807811481c588411080c41c0d800c802c031800e11250483d6407070741c141034000d5448002c41c0310348811011100113170000c2c5200c0788940d5003501c100b00c10b80c42c0760041e4803090000641a01c81040075401400a03140040c1040300680144400307001f50100ca9410325080541500d0400134041941204120324202030041e516000c11000480c8555007891645405583c240020b451018540141c01407000c402000b0890740d40360301e01d407101c0084605000c07503042180c0400c1404004801007001910034030f4800180f00d05101980d040341c0040d20803a0b090031076400420b491401c01d1241034050407801e0706408a900c04d99000440c00e1040700484044400990089454203907160440c02c00741c0000c0d0b0503106204038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 918994892 1250 918993642 918993661
    0x30e03090303130905060612010b07030315090e060c190f0905090a1d0a152f210f01050d030302090d06150f1202091803070b040c0b03091b18 62
    0xa0501440104d2803174000452080d00d403c030112100f02e500c030100c51007140e2038408038041c142c001c440250149030b115101808407004048184002c0c0500c6100050080311072100c682c68080000d02d1941844c0040140e508020407034005003070719041c82d10702000c82c0c01c1c0f003800403291003160f42d00983e04814810140410920306401c1001c42e1001400711156243c42c021840e07568814420b0003800075550031320092120406500640000040c00b100707081007481c0340c41d0303080c0d003004440307401000d800e008600494180c1c0413034031382c001c0b0040480f10340442e070605c1200105001c2e030611402c3e11038060114440105030098050f00c04000000b8000c0c8100811410300398003400c100d004585d580c4480c202c0224900800713050400c00d0310000300064605010319401d00c8244030010300004540c000054200300d2907a401c000070403100c1c0c0b2070003001103503040619008603103034901d4104031054401402080300c031240004040c0c0d1138840030040051014081000700350308541080008000c9010201003028928 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 918996142 1250 918994892 918994927
    0x34501110a0b0a180308010e0a06050d080c0d020706080c0a032712090b030a0e0a02130c08060d020904300207150528031b0f030c090b0a030e03090303 66
    0x1605160502484981000c80e041c4030094010007070214a031b41c0014040c002030f402800b40d00c44208040013401e08c0c2c4500000740641d208140071551104001000d0a4102041c440c5d20070f440d80a0000b070414a04005c0050002032004141100d0000045602c10f252882500024800b446408200081c14035403041c01c0c40320000020241e51400321035480700340e450700c14900c0d40102c96024002030b0550f01c2d04241140501140403d9411034844d2440c84405230b568104030007014100d0718400204e5041c4210003606202d0000d21480c401c00da640c0040e009030700e840460301d60040e84202c1024000c4250f600c01848401c0c1c151034000c80713551840c240d004081d00018140103848110325154248004c90800320350354414040801080b1030707045039044403401c1c1c0c0c0b010310300301d04e00c24100400c0b514070350241060101181c0076100300083c14a050608003680510840221103841e10b0986100c0f420044407a44511616500100f09a40ca031081099003900744161900414003c007900e5459501d020b1081001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 918997392 1250 918996142 918996151
    0xc0328181b0f0605030c071209030b0f040321270302060a06060f050f122e061e0c0203120c1c090e0402030c0909034501110a0b 56
    0x14070041038100703412000216408101d80d401514103903254202070f400c0f18070350005810400c40384401d00c00d44001941907992460011010350300d1014041c41d50030b16140030b61016101d0b0354030440c868180404242d1009c1503024041071064010011500002030100600921603107980b003c0d03007201a10300f20714090f031111086d0340c0030740c0c221003e5482e5629140d0407942d80c0d10902c000b060b42e04009845050141015001507d00d00000505202008803424048041121300d10000043e02e10503030044548100024200042540340700381c0d0506246001d0000c203584540080c0340c0070048104d260280c07140341e02203501030b409001d50704484c11609030921760350000742c2c8982c6140100c045401c3d034030b00c201c2c0c10250f0350451555500c080c189882c1451807801405003042c3c0c1c0500504600d030f000741d12000074060088440d140110368440000c4c200d40040c40a2114128003072000305484c88a18074140c3d45a035802c0200701701481120700400044e6400058200401006e0141f81c220300c051154094415108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 918998642 1250 918997392 918997403
    0x2060a0b180702030a0e1e09062d011416080d0902060c15070c05101a1906080a02090609041d060a0507023c161403070504050c032818 59
    0x43c260f20201301f0003041c0107100a40301c1c0d2103a0700d00145894111800341e0407020103059064000c008440c1d46050824403242c0b15100500e46d403c091103541d000c00031602e5155807550180c18180e50402540100e410b0300c00c007500482c404550041601c010b9489110219401003100356203204050616440d86d0744c02049010300460701c070004444601407800f01d09101e90000141c44501b2113018210004d002c141411103185a45480050003074403a1501c1c0c0f188101c00b07100d490404d070702d050705c01040c40b40e000701541c40c1c880c01804140304645501c1c0580d41c0300e0404131004503401d03062030005400f10006100d020490b101d40c2d0140078542c1015400540100039a60035207042640d41c58080c2050101c080251600301c2609181007011030304145204d0681440304d040c1c800e40304071040e150124100f660498908124007c6480a181c5010001c800041c0000c0d6024000d52034004122400340c04010961021b080500440d1207000c41e0030901044400d0448204002c213001340e14845404c200101001c030741 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 918999892 1250 918998642 918998657
    0x7030b120c090c040302010c12020703020a0e10170a1e05010204030c030c050604030803071d090117100c0203070f0f0c030c061106061309140709141602060a0b180702030a 75
    0x1120f60b012045900343d980685440c1191042680c0e24a0700000d010150707011401105808030050391000c0800f8001c00707070030307141542508104020100008440c2e00582501d2200340c1d00050f600c50209414010f80d0300480b020116006000300a6070f034250084009206500c00680841000405034443c01568000d5901c141007680b42d1007401315510547c04040c0081000b4000135483e00d00c5101c0d0150040c51043d00c000d44013500d44042041c824003038005844101c00001100300000080100d00c1e51f480144200b4000105400fa004c0c0d03c1e482000e40242c141c0014075140c0d8148036000d0341c7c60030f00590100c1e00c04800b5980c2d0a02c00400303040c900584001541d0b9120000b801e480010b101c5014a00003010f8284404030908035000400c3c0d2401c0448507194a14540e05482c801030003240010113200e1130105990f030074103020320703030a9400400f01d40170305a4484480345045d60015005610081524000401440c0701c40001c188080c0031a12822403248902000320312a8080040d2109030320a464110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 919001142 1250 918999892 918999901
    0x1a100b0301050a0306050903070f030f0e150706050711060703062c010b09040908030c0406091a031f03080a091e030b04020d031b03110d030501080c0907030b120c09 72
    0x40840c4400c0c4242a800348024205001140300c1d90302507a0440c20303180403240392140580e0b94050302c400d03542c010340204240d0f003000310032503400c03054103c2500310403030ba842115030070701c1c0c1c40d03280501854030058040b5584400107600c01c1d004a400b15100d40b02d800450343d682c80c4c1000003c02030071490094991141c800b03681c6024485d0744000260b012038804440d44ca050307003444114141904040d81c42a401398680e1160004101c003c00214001e403140b117001c42e56142050400350401000d80c0c440c80714280030f54122900b000e070081c1500d40004029074a01d041d40d5452203d0350000d500340e000078041c0440002d02e440c4280c1c200c42036200f103a1440100c2031403600320705000c17400001c83e440701a0103c042c010004006141c00009400d18502c06e0908110456501410100020300d440e02100400c100900540c29108100500c1c2c101c1c1c1500c2c0340078022981001c17401074581007010031440c090807144000c60325081c0030f41c004d071000c1c660240140c5414411003501c0c0380d41c0c20f00c028415005041c00000305 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 919002392 1250 919001142 919001159
    0x50a0f030317060913020604180204050901060203070f0b07030b060406170901060609120c030f050f010b030606210a02030d032a0c03050d0204090f02030108010c0801060e011b1a10 79
    0x2903c40d803801410303500b40380c0e80d1303500103600c10028000880e8408401c02c00421519029840e2758064012544010b881c0c604000500c464008180c02140079540140055130004071544106040282d101c40c00040315107404201b074015000da40d12140c1d01900109011420300c0c3d0141c401e44000582c8210385440341c490f401c40c1400c0b92401c2c02400f0010702414018013220000024008204e44036160a0310416038036150500f0b602850041140c80e600300d400e6654603024240500d0410321001c0303010b0f00070344c1014000102110854a840d114512204800c0b1603c01d20a002c0300c02021f40180644c1c122410680e8000d004007d24200340740c20b0582100e2030000d01c9042268501000800d03110045d215417543c60a40389070f08442917011140c2c1c1c0810000c20511b289000e0308408220315100582c0301d504080c003550030755240d4902c80d010003c2c940300406c07040354050031034024000e01303080070311200e408480062a4686a0600034040107107a8103481c00e8407100014052103041c041180b850250b0721b94004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 919003642 1250 919002392 919002437
    0x12071a07050f0c07080a050705010206010806061f1101050415110f031b070f0b070306120c0e0901020d0204030f050705011d13021219051005010801090b0307050a0f0303 74
    0x400000401c1032000d4811101e00d50001e1468082c0c141c1220189039413a1840d5260003c182000c650a8002c554100f00c40c0d40c040252034090100000a82118a048808903000f07140340c025104811000d0001c801641e4000c1e9182c1c1551000304009100c5440d0600f021f00c2d001115001400306246401e460350810b804510580c0e64409028250600c2d5449175a4011001107240c070000d024080d040026500285e41c8803101121039200e00203003901e5240c654000380444180c1e40c801501e1070070003401e0000282c0c030340ba509400c2e12100314084407181c44c3c100030940203004110b1071203040d0f80300040100a21008044208001d841002110169500c1e5001103810b03880e2003900110381c01c0b5041d21b42c0c0d800d1070300388401a00f90f02060001800c00c84400a211103a10054685104100c4400304601007c41d40e4010f183d40a07200800050b0b40d10300d00800246580c0d81440751225295580b44c030105241e03018407010300101801416910940e0b102e0300d9003800a14584001c6000c01c0c18158070b1000c10500302071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 919004892 1250 919003642 919003651
    0xb0103050c0a03021f140a080406050c0414042013090b061603030903020c0904060203060102010f150306050a090b010807060f0c02010c150912050c0f0610051e0312071a 74
    0x18181c4685402c045a0369000400140e82c1403051900c48216a009001d02412080b401f9644111090500d4184081120806040c1c40d1301d80d14100001d200480e40450420030b188425070300003a038032081700b08105500e0340d06110704090f10b800041c0b02c00c200e07948140b550282c0307050701d078104405d20144042025134803416484490b41d0a000e0070101c00720303000e40d01c442a0b182c024019194a01000800112401d5040341d0480380107901106103c120350f4240301d0590781d8004001c007000a140745411900c201c40b102c2c40014078580e00c03540001c80c103182580007414815032081601001d56103c3c0585c60b102e1085016401c0040c040c41d0f54400302521844180000350307010703110390500040f607403200c5009032001000c072941c00d40c8503e02c040003c0c1b039680c1443c1401c0f440d60760380d03502e403001d03c943c03a401e0016890b09030f64140e00400502c100f01004907080c104803001103030007850b504040c0c0417030b15014400901065050040d4400305040c8103802004016487c0f207032800d00895110300b06140d13036003602900c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 919006142 1250 919004892 919004899
    0x501110c01091517130b130221031908041a010e040201080a0b0a1511071503050403021c0f0806030d020a0206030901060509012903240109120b0103050c0a0302 70
    0x241081041140c10803c0341101c02c600d031100c03000f020f03149909540d4005642c00c0c01050403504450701803060880c1256009154003c3e2581d40250340d8001a14542a114030460049101c000c1d01c40d00c484100100c400b07503400001004007581c2075032400b40441408607010340e0508551980090030010001c6210f05a606280003410356803155001140c034190000c2c070704620582d8800d81409250b039014004401001c140151800460750180000c2064003200d00305200340c2d01003801800011810700300603014503041e10300003950355200d00781289404030354041170403a020440c0707552060a41c0503260700703120055a11070f040706440c0c040625503102c0c0c450404e88010780184c00c6440040c45c00f00025604002060000300340c140d11640050301d585020f03072100381e441580b00590b9009022301c56151203004008004107003140b4060000004002c415003c014142d40101d00050741031713021b441c045016202000e0241091481454506c141d414203020036a0544107980c00a4480c0c90901070710313001e40340d015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 919007392 1250 919006142 919006157
    0xe180307080a050d021201140d0201120504110d060e07170615040e120712050a02210d0606050703020c03070b1213050d08070905030105070507030c0501240501110c01 73
    0x161900c880c1e50704503140d624108441080304040300402030004e004036100c0c0b0b00d0300e58499490301d058500e40d6103050380d140e4007402000d00c850003d42e80185a908008030304103004102c642d02c525001c65542243da201a13400006180750000b03201903507008075a1109624221018143c4846904460f0100014122a0f582c40800010b0460321680301d507906a64001d80301150359100d1880444c01c01024900580640c0d8012881c40c00348482c94801c3c03100401d5a050142c98002840d000039112140716003060305c1d040f000621641c01c1400c4004075110040c00c6e4504111b00c5132501c034020b01541c02807005500501c80c59110000501e408a00350701100d03411610780e841e0105099803200d04950080085125442c2d01e1040300120307805210780c1c2d01b0720302965140c6145260400015000001315001140280c0c50502000f0002c0d0300141240e10440e0076062266003c1014680760f4050b1030000f40303a100094550100d12400343c07038206840180e91090300c40014895902050030f9a03101081d0107a80000c1c000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 919008642 1250 919007392 919007407
    0x190b010825030b030102041403070b16020d03020a020d0c030b0a060f06140d022a070608061509030a050706031406030c0105071b0e04020a0b09090708100305070905010e1803 76
    0x1401c040c40e00c00c482e050100e8070003501c00010b030880e0801c2e80700c1941d00c588880302ca0590b103000c2c000701010f040f000c83c40d0340c1859a4600180204245514001e001e40718651052090500810460401030fa0041032203068400382c4c5071a0000e030281380700c126050b0001801045e07500e603580c011f100940c1c4010072a0301c286881d10304202c55070040300b9502c40a00700108042c0c0e90b684200e0004011145400280a00162000200c07180d250081c0341010a0360b000b45009001869100395459000305080b641a2810300601e11513501074440c0c0b44156515100b6405e00d03408004000c5840000c82d0700c9510104500d0010792810031101c002100d2055058000d0341203a80303a903008101a28003680160510204114000b950380c0030a482900120003084282c800c0204503d030002c02440600401074115080c04800000305203032103006803601c0107015407200019001c0f412003000000640d04034088a011a9031000300768000c020178010040c0310b15800000030041800002c144440c1441c030402546000305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 919009892 1250 919008642 919008691
    0x6070e190e0f061c11041d030c0a030e0301060302030c190b0c0601050411180909030f0406030f0f1509020a020c0907030b010305090c010c150e06190b0108 68
    0x2840c850349001003040081020180d5141e114440e03110a4400303a80750801900700300c40482c2c1c0d0400210344151444801c0000f601c00d10740280c00c0c04081e5008281c040000c2c080c82c1d8049107104041d9414400450160304039140000e603241e0301c40c06900d0300b11100c80d00b01d05040c00c2e10000d00002c0c0d0107a0202d18000c050741401c00e070a0690206501c0500101030b19400c01d031040e9807009840d84619409440113006a1405101d0140f0009203520301c0c0380303411a00000714540451f410100ca1094480350002200504180225040481d08001d103594958030341e0350141c021300111803072100d8903203401d440c101e03d62075500c590280c0905c0074400400302407412200310b02030340c8004180b804600642020055139242c2002c90340c02151182c8010440d02c0038480010b0031508028040780807503102c0b03507aa00090742c1140c400700c600c903009600400c0302040c1400080140c52180d601c21007d04c01c0700d00b00525598084101d280c4000a040e090148001d100011a040304007910ba90403003030650900c0511107003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 919011142 1250 919009892 919009909
    0xf090302010f27021512130317010303120b03120408160515040b0319050f0603011a06090f010e03060106080f0901060806190902030604030f0e01030504050c12030f1903060806070e 79
    0x11990f0022034038190815080103a141c501b80c481f103c0f44540c461290007003580190300241e11901c5460300086562440e01c1c001c0550300c0d0030700d84590349079446a0580399a20284214480d1492484105070b40c1d80c0c3d81c0003032030b41d80d030f08050240d00c403201000300c04222454282081c40c542000801000e08080c00c001026407268000f4250300141d1485500e540b0b1f025450b401072034440c1c3d1102c0e039560070710703e0550103043c00d4504550100e81000440265510156684020b0f1303268043c05a40400b41c1c03080c0480160790600040b2541030345441084000034a8640c840c1b0b055120b40401e44006100d83c41703801312203007a00c0c036038000c0f9080f03600b24000040142c140300300b103203521101040010030703c07034101e0300400e052540550302603001030401024505a076401c0641c40009420030702c0c04008914181d203400c0c2d201d80d40901524401d491b401d51155051904000baa4101070010100c1a5030741010300030622090001003149020a0420900191343c45c40490300301d114903030585412150329940d0f000c01c05804c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 919012392 1250 919011142 919011169
    0xb0f09012601050a06091d0703080a05040902130f05010206090604200d05010c1d131a0a2304020304202101090b1501050703120f090302010f2702 64
    0x241800440c07203030005803d003c0c0e207015540840c00010414101111001603440701c100001c0ca504850203180147e030b4001851008a942040f505070721500d5050b012075440c46594882e260b624004038000d000b40c0c551380040402c40354080260781ea2142d5038001640ca4003c11240b400e907030707000400010085445c840e550b45501d005a00405d4607141d00300c002851a4100d184151040d0b991040d1075203c2507005210b002c08200a440c4050501140e81c000841c00360043c6803802d03525403a08600c0b07038800c003428005000d214000b800c0704041c0351510390b11882403500503007200f4051403180e0203000c241028401c03240100d030802c01054034459010000092804070703110594100c520b004410b25104014500c2e00403210f0410000302ea10507107414404040100500200e8902d1502188a14140c0c0c012003221250781d81400c1903060008524500c1005250100c0ca980049003044200d01c2010740c1948a134401c0340d10100708101c07102e00141425160403031543ca50300b40c0c4410321482d101500d840c1000540350b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 919013642 1250 919012392 919012439
    0x100b031e070e1e070c060608060c16020d210f140f0c0f0706030e0c03030921190f05060a0506031b04020403081b070b16030309110901060207090b0f0901 67
    0x10788000301c1c403c00803002c80e00036000580c084049000c1054038001d420003048040010109420107108444652280c0300f00250403da6180340c4108644600301420501600300803020300400d000340054560311822001500000c4004044844544c003d01d082c034400749822003c2800c020820281001582c422a03010f4140d2048603091074910038100120702c06400150750115503101ea07075400624012646000c58401c0d0814800c0d01c980d0b480f82c03107854900c3c129901d000304020481c074404d5170801c0c0f260300000c201c0055014170790007031201410716501014410411104190f42d43e4407114200c40095a501d036040c0c0007104c9070151b84558140c04000f100c3d0050005103402d5680d41e411025a00c945241e01002c2640d00c0082107040080c005203000f040180c03900b03803038800001030100840000c1040181819030ba00300d002d00780b040451000e03003040c0f809440307049035513114000a544c540240c40360f174071081d04082a441d041e0a1010307000c560328001411404140e420032111b0841481e07600d121301caa = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 919014892 1250 919013642 919013671
    0x9030a060609020a180b0a030b060403060615080105010201091104020c15010914071b020d06111305040c0f0206041509050a080310171c0e03100b031e070e 68
    0x3155292140d00c0007032400c0e440050f81c5156502e0003602ca51182840248000701d010390820500d107401048400403002c91030001440313502c040020b0814001d54001400701c0c2c0c900f42003c1074001c0754803008800030b112a00c0b00d0419aa075000124240c46540307400030004d0242d907039290b04a04094000e072261004d808140d84025014100345160744a0907401140c442da1108080b17068503001c03001d1a6003010035490011040b1040f0035034440303c210310260080c0a0305100c0510801d220540d4018418030021705161a9125040308820300e81600ba4000c00c3e00c101d1500c0c0320305071014007481100103410165006440184c0c0c4640b40c0950000d202841080215150401c000c00a1300500921300c14500c01c048160301c1342000c405031030000030315802c11502084200340c20403400300f000403910f6250f0a03c948068207100098012a481000404480d41501c20101090203014241d00b180002903400e60803100418143d07100144e47d0715414040001c0303904001e42c1400032040f4818030035032000c00c4418015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 919016142 1250 919014892 919014913
    0x230a03030504140f5713020d0c0302090d02011d0303040308071101020601031502090d02060f09130c0503180c2706180105060901210506030d03020a020c060903 70
    0x28101420107400581c0c540050301d480c13100c00c40c41da10a200340c82c6040100614400030401000503017013a803443e900e594002030030b0f070012452031072802520400c0c0540302c1c400d40084010018003030f400403458200c440e410203905103815071184c8244c0382034100080c050600300405400548004454032801441d0300400d550144c0c0304e8070100b00030001140b04403241c596a40b014103000c14404210901c05045400180c010008a41c490301071050a800350391006a441218000054802c681804025004000030441c8040d070103082002d801801c10988900c81181c245000c58403c503039042d9180000b0940c2840480c0d0300005100b01e030100d6103041801c07500f10a5007103001404c107800f880344070411085280d440e81181150300342c1154000c3d80540d403610b40e00d080724408200c42d040500409000300b401092010309a84507442c2c1c001280111001c8428081d0700c4070310301d0043c003001c842143c000d02c100d4031401a043c1c030034400c0b40c070022241d07030241c48074100140c10440c051b440740d0f10065161091b0340a55 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 919017392 1250 919016142 919016183
    0x21e040209040507021f0c0206340905040c14182b060e03030f010b1c0e03250c051e0306132a0504020702030a120507230a03030504 58
    0x1c601800450300180840c03807811510f001b41058246250038100e00f031040c0788810b55000038000f41c104030880c03030441d81c1041d0807030707280c40300e0840958040d4000d0060380c000041680058080d01565401d0b00c090104040c02c04c025140b804c151400d10010f01c030300300222a0620b0380081000040302c801010007107044012407056203205039081081001ca10b00203181402c012861150100d0142e89002a50561604c207462692414052040390160000003461005102d0101c102c0200d85084080c01c1100c0c0903141201583e90b00301406001040700c5500c1051800750300c140100c09482d034804044a03032142058140280b05c5800d05c030100c400941034810300403039507040c000188241d0812400f40c07040d6401382090300121911901c000403060035a41c403814181111040c01042d10415103002d80e6601d19440402d140040c040c2c400b4100010b4890603010765507014008105081c000d0101c450385c000060006940001e1030303280c84000f603000c01c00003400a8007a400550b80240240c403031100140c5860840c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 919018642 1250 919017392 919017401
    0x91f09050307050d1e03050408030403030e0c060d06150e0d1419110a05040e0a1103120f1305041a040f060e07110f010b030606011b170d0e0a021e04020904 68
    0x38000820300e8604c00e15001c041d502c03400214441c4c0c611b001d11941c102901c0b040a00e1001401c003404154445c8158107408000300701d002600207015081950300c1070b041c2c10b001d004041c68040e11380c0600c4a8103650444500c01c1c003060b41e02282c000c0071102014980da0714014004e0540c1510503050041c100c0d9440018401000c1c40181ca0148181999500c580020448080b03600d4000134480c914000c140c541105002804400042d4014144815a0318050000386004400801000358a40c001050b004a5010202601c200001e07a070850220360789070820802603450b0140f46401d81c41e005040c403490b41c50140c002c07005002c00910000355450f02d0f00502450385404a9034840414018510031241d100c04014501d031410f6244001c220b4020903000003503e81c0c00160000c0d042100c1c180071032000841d44881d4444c039981c4106403025040d101c0283c070302541c0200c2c9109140034034000e0a4082c21001240751080303c1d500602d803d102d5030291100030504d00100c29a59003196003800000700c0364485105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 919019892 1250 919018642 919018663
    0xe060f061b24070206010e150303270a120506071d13020306031608030f0a050c0d0f090b03090721020301051003020420030106350f091f0905030705 65
    0x20010040301801c2c0300500c0004042c1281c2d0031035004c807004001000c0f4400100d504400c40000c10061407000b0000617146020b0554140340e1030b415a1406a424254070621807c0746400756014900e83e42d13100200e100c6143d403004058020f4112000155a10740708454409014540038190403e8144920102d003818010810380036605500005002c160701d41000403541d030300480555021400d0400c060943c9034018064401c40e68003000c910f408480c0d00940a984400361400202d588848010200404010130409008081884c0383c00c007050301d4085400302c2348119200310003400b51a2401400b0032400207a00020721402400700c50b90070060b41c0038000d242c0104c0e811144882c0030360660040000b1907a8081ca40c16522091240c80360300400c0c41400c0e6030466005080c44041511403240c010800743e0796103030400c040010a480c80400c185d0001170103010b00108072047c003003599406503055441100d03c90509511078042882802c807581504290702d178901c44c0007034030308020555407000e20b0800c4506 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 919021142 1250 919019892 919019923
    0x6140d09081c0e01060308091302040e0906010312050a0509012a05031206030705150702011b0b180d091214010203180d03110307080a0615020d0305010e060f061b 71
    0x40b4120301e200700e203000d00c0f80c0c4144204004c01441b40703180c0d6568118815440c01e1405007002c0c41140d00010500d82c1590001c1c4071503850b11109240450016884038000d01003143c50003c0844509400c512440c1035500100d05504c0b003a260003444001036444240c403800030b240009a24152040c0c90440c00d148182e180c0c8103400840d12075811a4660b0741802d80108040d00941c0940b01c01c211030b980302c0d01401d40301140d416810b41d40310f0650004803440c1c042c00398405000c00c2c0181d1040c0404c86030f0050181724180b03660b034500700d8690420350f43e900d03007070036800100c001018424144816034060404119491081c036000b94030740300014109081e80c0048441403140d11104d01842c1d40c903503050181ca12005150300c0c04021101d4a082ca5141030300010300790300100401040000c07150394075079120102130146c80031403800d420f1440c407000f0742d1040380c0d00500000034280703400041c001110303036006401040000d1448140c030402c40c0070300859802104198000f09031b0051441c1e8400d200340181640c82c01001e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 919022392 1250 919021142 919021177
    0x110a0308160212030a0207060503090c030d122a030f09020d03020c1212030c1b062409010315240f051807120e101508010c0906140d0908 60
    0x1401008101d03580c56401583c982c00400020414550204d00c410941d01c550905d035840752251900c0301c0c541218507000e40d41500c19403074400e4070386410000300c4d0010441d0700301c01d0203001d000070385100c5c1c40c0c01100b14160b00d14001042e2603955500035008001c001c00c811100041d0038240f5000610340300001c10b0103030701603000702d100c0c549a0304002c1801c501c40041c81004110020f0044414012480020280b80000d140070030842d91000150440394400901282254110f040c0182100040c1c8a10f00140c0890f0720102c0c3e0151260a203070350494100c03604200f12004d1000300c4000c142c00784c83c184030644503606c605407a24080d00b001c0602c840c003030f04170010014100780c14401803011404c0320507030b0040c0c1482281c042000c49548140d880c039180d44441000314042e0301a00d0b0076031400e058009005841e60030a0001911411200b40d0ba804480050000b440160005038007541c0c17484032809020005015102c6585180d0781440040c8408510030800040a4656407540e040380d4104042a40e944c0b00403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 919023642 1250 919022392 919022437
    0x702060d0f060501112112040c050306150307140111030406120b0607021e0a080102161b0602032d0f0304050105090708100f020903190b0a051003110a0308 68
    0x40c070030400500320a003400e0360705c4524940103540e245114002000044c3c003000d841406544090140c0d0301030181c80400d10210300301850141c00c088414040d140c003c0c454540001c000364507089204e400d5220203005408124200078205100f002c40b840b40c103040c07140020704140000d40030001800201442c0d47c5450200d0b02c0901c000c0d058a2140346c0c0d80d8441e500c10301c20040542c0c0d80c0e440d9485403031030f1031a81422001e51030700441c1c66000c40e5400701e9001c0d44042021000c460401c100101040c0c812240072400c0c2030b00040305c00e04c01410303014200040e030082c048908551071400c000c0e40c404041003044500007055000b031420640c00300e00008000300022046c0003c00c102405400d401000034030151030039508050003140c2d161542000b180006803141038101c0040e403141e04882c9580b41c080c06072881840782c04810341079114401400c0300c034000742000081c80c00c2c00c14400d480c040c076001d440a00001389941c5995507180300080ca00c1768001484039001000070344920040100341c042c0484400444103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 919024892 1250 919023642 919023671
    0x50a051c2301081006050604060806010c050106062007030b01050d080d09030905011805010813060f1a0102060c0906090d020105270a050d020d081b0d05130816030303110702060d 78
    0x10000401540351709241c414425591240e081d0740c162149881c0003000c0b03a4440c00100c494160924025103154600000818096405800c140c903001040300321200000031050100d645181c20310015060140f0980180003510f011200c07c007030b13a4001c0841c07a007017445a40d28401104c85030300007100811031480701000b555805c0341a00e2401200c40c81442c2c002c502c2e24001a06106000f016800d40380956030a40081000583c04038103035a20040c010803040b6a00c80c7c0d1810400b048a210038094401c2e000054074180001d0201d9400d81c50240000e410440d0070010305c42c85003400b4808a0600000f0320000104440c1c0340742c00480142c0c02c031003100261140d0814062010541d4100030301420300303c3c4014004d40c5590301480202c3c0d81c04624160340e8039159020012500d2114500300a038012000780320032080d803120182100700c1c0d420041c07801e5169201081565149600004010000121000c101083c00390303229a45804400d42e02a02c0e001c0c29a0008117144c0c00190307214200f65482804c20711041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 919026142 1250 919024892 919024903
    0x31c0c090801090f03200a0f03030506030609072c09010b040f090c180603080d020d0f18020121090804030b010501020a08221a0c0c01050a051c230108 66
    0x1800c5008004086643d207800900c8190354138050300340800034409448208810b02c1000110300c410059400c0340c00149403652045004030f205a001071300b0400401c22511700826024029500c102c0200043d6141c40c0034035071307001120605404940e416002c4c4821041c0f04044070784c03145c0d4010740000f0b02c0002940400c01222114031482828620304403101d8000741004041c0307400e80d0a5130b003881c60305032114401030004e0b000e44e030001450300d0700120780d0340050203094000d4884180c0007403040c04051607680d549130858040c40d042c2c24694005c4003940015502901107928800c0c10240841650100640350006903005020211005440010108217000500c01518090842480603121000560700c03244180d01488082d0042801d685505400403900d030030100009200c00c03c1c01c0350000c1640d82d00008550040060ba0019004403c00e52001750301c5103046840301210360325602d0600c1401c6110b071102e52810302030340c45841c2c2d0b59161240c064090704040200e0120078000809258142707481c890515 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 919027392 1250 919026142 919026149
    0x4061d0907080318040b1f0e030613060507031d03090406080d0c2a0e041e200d020a090207030f0206101502030d1a0f1801030303090203031c0c09 64
    0x1c0e0006035040c40804030210407611100c0584c10f5019600b0010b10009000346140b07011954030031540804036200c41c40003201070380c0380781103900d500c80d8540800c800d064540c032044441100e41061480d03400d002a266600468021a15180010f50b4480708410f2004020600309010025400401c1c044072520f4240681c0d0043c142c2000508080c80503280003a04030900c0751401004591030401d00140c48000311000c10078011a6800c119020303584241c1058420030564041c1c440344180aa0102480602c004514810781d10040c6095400e0701041d80c1e911890315010f07400e41c0012040204d9001d07a0350100103a010308224480180d407a0820724014080382915294441513401c00401c01041e01e0800307410300112201c10043c02035500d01303108100d04511074184038880340e40c81c0141e94010105e40707820f40051010195116058400340303c0421040d030b10705d40b1804414444507001800081d20a4102d1140c0e00e10180c112030a103440986d94050740b056024003d442643c1e1a40c4110329503178800303801c44c002c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 919028642 1250 919027392 919027411
    0x20304320105030c070c290a091806030510051f0b0f0a03020c0115060906020c1c060b100809010b06040e15150708041e080d030c05070204061d 63
    0x3411028103403010010014203180d414000048006489100c0c0d010444001c0c56220340340d0301020781c84551040011021014141d01085900308003a0516005011103c0c40e01032900d84000305803a00c5641182001e107100400741709a00d136640000040e0042103014085960b05001040758640b4280c88203071880c400341454040c8c002064100320100c042d500311616140052015655034134501c0d01074000c0d01c21260741004943c64a00b1006c21001a1141d000c03ea1f0015900c0742005580d0390b070f08a0b0703125100b04845a018100d0b0b1494100115540085071509104000c0072130036021080005a504d00301107603100201c1c0d013110402090410a00c02c51000c0001100c940d400c080c108803818003da04014204020a18003000b22811075039503590300300d04805038500090744c5142d03c3c5040740c03060f08940300c0d60403c1495151080700340c00c0c1002c100c60607034090340014111030242030b00440c0604036802070340081c00403c0040101684030b42c00b9542c00340000c5403203805071640c02031540090441c0103060040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 919029892 1250 919028642 919028699
    0x9081b0d08070c03020c0a0303020a0201031a0a05010e040f020f041e0e04030c05070e010909060f200f040f030b18011a10180617100302030706030504061b020304 71
    0x103400c0d400581c5a81c2008032407074071481c4651a4941a03240c0201008202d80c418107100c0300004042d80000d000548901c00c1ea424014890a1640b1a440224811946921150902041c0720341d5102d0f010208000000810204024600f025100c04aa0080d00c1d80001140001020b00000b802101d06c42d14000d41c0c1e47c00c5402c22703490000c20204006000d0402420021009480c4090020801c00600070b007219199400da956940e004100c020100309204407003c900341a007003031083c035140c85491600103102035585603002c1d0403a00c5548550240c1000040120240400714070326601c80e010320301035031003403050440904240c04044802864107201401aa050904038851521041000840403800342c03001200084003600c103035a02c42e94a8003400c00c40e0f5a42c0e4000030159401a81390b021408d030540c42800170707101d68080102181e22800080c0d011b0348a004104109442a031201c0da1090141c10000f942d070415140414440391290582da00682c0045010300c070381e02d03100e070585254103032004407860b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 919031142 1250 919029892 919029913
    0x10f050901050711030c0d050702130f1508011b08041406041113090c0b0a0e130902120312040308101206060602190c0506030402061c0e06010e041a04031209081b 71
    0x6541c7c0c6d008812501c01c00c240407404808546a9202e40324080c1700c40700d0140701d404001a140c00c010981600c6041030f804108500282c4400d0621034a10320060007050011110a080c1060740c50050141007181c152a401d1985100e620052103a140924400c5e428120b84418003400c10003961030200c10040070505d05103c2000190392082c20004032440c04080c030380c0368000402c0540301181408240d0b500001c043c081304150782c0d03803940100d070001d10844400750a075032407001d41a42c13800380c03100c1054096405404240400e024442199103d00c074a43d0b01305003141c0718814190300718107500c0c046030700c0e81e2107100600c0210340504c01e48094001c40b04440380481e20685a007020110b40740315483c090b8200001150664940b07008540340d8600d4641029104040340c02c506000300005507181102d401100000305001d201d0f1288103020f940c03c003140c00f13000001c0b010900d22120340076104505000300051800005c501500820300440c0c09192401e840f480f20740c0c1c3c05c403030409940040c0b10440c1c0007410300c0c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 919032392 1250 919031142 919031167
    0x7080402012607211503120e0303030c0705013e0a050906160609081c0903120c090807091d01020f0a08040809090c281e02010f05090105071103 63
    0xb994040c109144c08800c941340c1008640029007040b6800c1400d074204100e25400c915040d100c441101e00c22041004410b0302160100c4c1e0140c1d210680726807607041000400c16080d481000303000658000e100010b03a02000900c03441c64590010007403014180c0701801c0070301c1910000c004565003142030018910b4000d5918009000f445101c00d81e5110f800d002c211562008040351040e01560351042c41001200340908001180c0e8000350700421454038400b0000f404a201d5001c0c01c80c440e503042d02c561500ca0002c02c285e01c064028042c11800b0811800c8000440c1d003c00c0103010018481c0c0c2c1c10010340c61040100619205034038207031047c0141c0c01082214999640f6104451840c0454a401842c07611a86802030341071003030300d413560340c050400702c140640d400f40c1c00001c00165149031107540d001c94456807800c0108807100d10075004600803074109406162189000c0044524503c00040e8450944030000121b51050f10806c0307003603558004015180d50819950200407450360300035400d200d403441d0305 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 919033642 1250 919032392 919032467
    0x220b06041508120d02040e010602030403200d0b06030a0b1014301006081c180501030c0c1a070f1403061c0b041a150303180303120708040201 62
    0x2009960039002a04040113a100e81c140e8014101040c17610109507599070009540f03801600003518505503000c1c010b243c0314102e21149041c00c0d005440c103110340b025a00c454424010041c40150507009150b060800a181c40e00c00c24401d603030b0a01f0404101c0c0c14600001080320301ca590b01d5000b001d40640f12000744011040080e807a1400000300300c04210100740d039608002d02d41c00e10001d100d05010000c00d041c480414981c003500b281d8036035003910141207601101d4008000c5500c20710b11111441c14040b070751080c0c0000030300302201d0511002480040e50345c80f0010b100115181c418174170060501c032031507a0007032040030148020f1401e604c082e510224042e9440c40003400c054840d003e400c158048010004100e10308103508190310300520315040c14450500b05100200702540311032040090b6444a10580303003201001e020f0000c2d800d011105044102d46170700014029414031081c0404414800d6542425204142903520341e0890705083c400580b07202000301c0c4c04038511031450008107010509500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 919034892 1250 919033642 919033663
    0x3190c0c0f0b041b0306050403081501050a1d1206040c05090708010618030602120f0604061401180f060512061008040f1a0901150806091203220b06041508 68
    0x75031000e0307403550301d807520140d84a07428110300c00d0144d14000041c40599480b50b481240240c80d214001c1c4d5404c01e01c0e40c00901c5000106e40030410074070800c6400e6115028a00690313a80c4031166030b900396000002030b08550301c50901080f0303602c00e030304010400140000311030050405890001d00760030b00110203050b100f0140584000c0003505000d80a00b50444c0b850303400156000b05085544a0304110300702c00c3e6100072214550940156808103203607080c03078825007003160b43c11000b040074640e6a4004554130396215802620700f54004801180c1c907120440c3c17890080c420307030300c03095034494050968402c0c442000300040c1c0300d81c00d80c40b0b42e540c10a4100903403950041c2d205405128900c071030f24000c0800400381e11050101c501f030008000705013005511525506d424140c03019046a038400c0200e5440342c088502104682008220040c13401884001d19000451000d0b4071007003484d0b0303440e03880318002c03a80401c1c0c0d0040340d60010b200d0079040c6403158107180303005100c0c4011120b00340070002e540e036541080c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 919036142 1250 919034892 919034903
    0x9060304021002030f13031b0b031906080318100c1208060103180b0105130e07060c03091d07080a020c070b0a030e0105040503041703120604020a050705010203190c0c0f 74
    0x2491900ca02c2e10030300c100e4006100c114009500c88100c1d032038000c0004c200703000c210b541c00b0000100c0c08056028411840481f003030b1080c12880c65417508040740800032110240d401003511100b0121364034105001504e040c2440c400a00203580b401c800b00900021010070540601501040740c0021402c90050000c10720400c0c10003480da9120000100e0060010108500c0c1d5156802c05203010090b10008141c12900308440c5034080340f290060000443d0140c2c03072450400d03800314900b0080d190081e002c03441c8060003030801c0c2c034220381c1c0c88000030ba0314020100301b420300c005c1c0c100801c01016040402c00390000058a01142088107070315281d99900100d002d03840341448040782d0762840c14840d8000c03c82c00741d0404000e000908041ca84a59244c0103400b80840d9011402c101c103510044c004143c44560341c0c0007000301c2c02611414244002944400a40c600b088010000c0c540803c00c00d0000b140948000e8942d4000030b9500e4840d9800c0711050141541000791048200012404a00d0010040c58002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 919037392 1250 919036142 919036159
    0x2101151b0312091a04060905010b04150302100e09090c0312040513110c0a0605190513080c1c080702070b03131712160e01030c09181d070612020906030402 68
    0x181806099520729281040d942130301442048100401a0042c80c4007501c100024400c032861007040006545006209000480f203400d0304001601d410141079000098a0414440d1181c203440811268a0121201c0e9480d52081c1a00f0703a541c00d0821a00d518540e003800703010b00b007900300000510540c02650500040303540301e8188428880c449822221050241821241e4101181c94010083c0008603a00c4440f43e030b504591a44209550241a215604102d035410400d03415607107511480c1c015085101180c4118510081c3c44115503800c2240c04070151145001032500301d500925020301b81d04909246c000174400d00c00d045840e200c50108282d0b0001c0e100c1c00a0900400b200003034040c004441403050a00020b000345068030902c0b520004007641d542582514020005506560412040d000000c0311440104900324081220164049840602040d52102480d070203590110140003603a036608605402c04c01c486d0080c00c4100c0a841c040000e608050301000003034010300004001074010b0409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 919038642 1250 919037392 919037411
    0xf2f0316050d0c03201606120605150a080702030c0714090907080c0d050c1906260402040506030307060c120606020105090a0602070503040f0609030c090e060a022101151b0312 77
    0x148407a406d1405000c4a503001681d8500e00208045282c4800814151a01d1008521414182422041405a0303542c9620f0b080340e4010450701954010040000c40c0800e00844059807000d01081d0014003003c088001d0340d510040030480d4000c0d0161038000c0a9014001c01c100c0745c000440d8200c00c1140844603401d04010fa41001424281100300300307a07101e50801042c0347c1181e0104407902c1035448aa0b41c2820010540c240d40b007600380400032401c003290004000500515050308007a1f40128081e0030350341003803004e0390799a003920140c1621101040c400c2c0c80c034103441c4010b13115030402456070f440203010302c0c241441040e44854540070301401c1e150f00011460706100c010804c50340104244001d0407031255403490010f24044490008071421228a40000385209043c084d2a0f141801e1102600542d100c00400400070361110042d40030207401100c050700b0745103030716078045c0c000d00c40711000c00700105005000521103600e00200c0c4410000d104810400300307600140c0311400c80200c0d1800142e5005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 919039892 1250 919038642 919038707
    0x30314070b06190b1209010c0f0e0f010504030b04060606080604090b010b0a0c080a03090204060e01032003010f060315050f0c1c0b09070f0801060f2f0316050d0c03 72
    0x1c494206850b00d880000e000400b4200d0100c01603c203408640c020000c0402c40b64003151a41a032003503489c00158051030110151400350050b401801050401c5440c0c0740c0e50b6555030180c2a001c6909960088e0f607400204401c0e07400100540d400b5804880801c2841d02ca95608440c00406000350320000078042102256140601e00f030314103458110200710784800f100311340103001e0030b80100304902803418203400040c440d0414244505880d400700b2444c408841001489001320b6109003019450340d22010070384506d01031849400301440c083e000515800400c4c000881c01d49001500008500034040200066400b42c101525255000b13400030b0214001e00060380d60140030105d02d5158400e88100611420302e0b000b01180038407842940364040c1e543c0e44c600f17054490075046884100415000c0d2030b061400201480d40a5010034520006211030352550002c2d465600500007036031607000070020340700c00d010003040045625191841e01c0e0b100784030240da000b0211a0101b41c0030360075845a42d072405070f110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 919041142 1250 919039892 919039939
    0x6030111032a0307050d020901090308040f090b030d05070201080403050910080f16021e030705030403060e1b0114030711100f060603270c0905010e01030314070b06 72
    0x41a014644905050550b01402c110100010207068440030300c071990600354905903849030300700b502c943d0300f402c8254245d40040d600480d01c1e54100a443d10020001a40003406003000d4040042104000d60074091100304944125503050b220390f002c8185800066031180440700401d03428a454003280d140c0d46001c1c0e50324054003810a52024811101410302540704402da841264140740380e0b41c194944070764082145560000b104010f800109005065400085561501e1610304085a1400b03030075848450071340d0001d8204440581e00d030148240700725010401502e00f218141192540c010340c030400a04810743c13407400100008808800141154065040c8840710319859090706e0b001014458103000a000c5000120340c028503120000c00c40600c0b034442c0100303400001100151859000740e01501800410b0022a02ca5180c0c0e0400300e50324015011322402011441c008060650441c41d015041082c161000700003400c0921200000c1407412741f4035500120295a281c0a0002c42e00d03e6101c0ea2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 919042392 1250 919041142 919041161
    0x101e0c0f120c08030103050a11043303081804060501050408030a0c14010f05071d060f2b0c03060e19050601020705041e18080d05070309170a080703051608060301 71
    0xf070804030000082c0100881c4012202c1c0c0300c0d503c815500b410a0b801c00040300c00701450a44c080c0e40c0c8940b050b014400076140f007204c080001e844118480d40c0ca40d5540c8256202010440482180072402074940c1003d00a40d400707170009007031050400e03082201c3c8954034003907862883d00304a1a007040c40181310f400b02100c54501e5505000b88400b04114011201a00d01035500c0000900640c80c03854503100240448440640000c00c01d03890001c402040c5407103078200a0001c1c072208107030400b40c01114101018012401c8103040041aa41c4207290060203d80c00703a4040c420400d00320b400c00850407180440781a041115000020702d070b481c0d03000100d107010902e40113182c100c1d10304506141407882c28020b44503d00c0e125038050281465454401c902041ba24500401c0c4120034000d150082419800003503116100b843e000034803009a445448945034410740a41384860001100d03c0a40d500500315540055141414411420030803040c2034060f45050002040024407000b0035007503035003900000c1c40c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 919043642 1250 919042392 919042403
    0xf060f030207240b01080f01080307080f09040c08071418061e0f183f16091505010e060a090e0a0204080d030c05030f060d02101e0c0f120c 61
    0x3a100d203d494500140010181c0901095041c40050003405c03a00f41080d0603218002c0255042031010794461485c0e4005443e1560708010600c1515286d444901c1009410b203c42e80c4c40803c0c0f030408100103481c0c4c0c03482002170131345188c040000b210400c0070b240142111034002c1c3c917010383e241642441e4000058581e000d40301a030b00001255142c43e503007000640b1407200320f41e1049400304880c00400c8100115103020350315480c484812500c1e05000440c916091010000c01c00c0383d0303c0f80750075485080ca515502042044e01c401102800150704502c518111404d485600e001d5207400d1000181007000425070051181c000010b145403210320030001c000040160744a60802d0782800707240d800180d0858080c15049100b15444056200e111b40079402c0d115100d9220700345951101c0d042104402c400601c42d41e0001d541e10050b400680b02c0c21a40201c9904903900d0841d01c003001000944a00c070140c0150003001600000d460106442e400080103003548441507400d5148128829540c0c5080200302802 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 919044892 1250 919043642 919043693
    0xc010501180c0908060a020705120c16050108132402070c090b0102061306050604060803030f0708060a0602100c1e0203070203060a1406040b01140a180f060f030207 72
    0x3241d04802010031101240c0c05001c0c80840b05000040b52200d00d82e220f59807240d403020f00801e010791040d40c02003100340e002e501a6070101c04941ca43c02c910f680171101c550300c60341c88076115000035103000781c440019007401d1074010038078140b00c5414402e5580d0140c010302040100292450030810340f00c1c00703c01030441080150344940c99030500c0e05e9003071054418000964141007900c080d6620204040c1d1240c21005080c40061080d40c4641c001404001d2030f09421580c2e030400441c002ca01000690f01c00d4420350030380405450203d81c01490010040d14050264140b19014440c0c3e41d004200241482e02d00e481c00a403441001c441250640d02c200d0410801000d0038000f04a0140e000c0002c3c00d07254001e0b01180c085855a078641d00c201e94a4481d901c00864048022901a1820307400050040304145000e055500c1c000d041e40c6410b920000c003c03404101d02d140d0b00302d9818010484540240020902c0c0c04086160107806041040c144480208140c0d00103500c004000002600c040d03000740d428035050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 919046142 1250 919044892 919044899
    0x90b0304201c03050c010606110703060b040f02040e061008071710050a030302060f01290309012901090e0601020a12050f0406050c0f0a0c1a09181e060a14060c010501 73
    0x410641c1704103104a11075090a40c00304006000e090f185043c0c140e000000c0070540d04c1c5458180003040000d0705194425102d0b20529041c441c0303030028002401e0040139000b81418240104074080701c00402c18000d000b680020071484a4110800d04100d81504d400c44a056540c107020f010300700800e800496000200100200906500003945881021501e6203588540d884c0c403920b2801114000221806007080c00d680101144800051900950090300100c3e0202880300d01c0c0e250101015030114411928000c031210361742c0d112510b0002400581c12100d514200840001e482c0c0910300c0c0060928020310900d086090f02c16402c480301c2cbe4000500846d00c903519004003c2050f070140618030014070490864810810340840e040d0b100562001810404515143c140300c0d21800c501c810610300c040504c2500c1045d00c40c140c0150304107151516a00441c94802e41044000d03001064180044290394100641030f00e41107c420281c82004821500f40091305002800c1031050603800700f042d5084c03c0000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 919047392 1250 919046142 919046147
    0x21b0a0b0405100e10020c160308090f190515041701050103030f0e0901030b09071a03040b18071a070f06140606070b010e0606070b07050406090b0304201c03 69
    0x15000740d2280b0140c80e10310441e98051000d45101c1e42501d00c4640010390001880d4296900070302d014801c4105030f8441000000c603422801140768426280904001102c003882d10740070000c1c4416510803281c0c0210b003403001442c0c010003c81c0740105401440700d96459000882042c043d50018210709000240c203031407180b00d05002e0803003031000703d01140a4080a0f00c40d05e004490001e403055000d0948080d030b88c40c0d9210541c082e40c2c06080b0b80703401e004454010a40c410301c40200b00c906680c0035016580d1b82018989407105100040903070322440101451001140004075050081760041d081008008012004415440c07041120042144d0f4603107440c01d0400c551038005d81c00b507510b000c10350540e070340d22803041c42a90310420400405400305500184600c0d03112400c2250051000342c40075040481a540721117100d01309544030000310760040f40800c00558081100405400a141c10a0842c01c05650b0220407000114a0b0f0350601c0c0340e0100740019495020940303060001d280c501803101081030601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 919048642 1250 919047392 919047413
    0xd030309050303251b0b0417040303110d02070b07030f022d060c030c220803071b0f140f0f0301060609050103140601020a020603040f06020a030501081b090a021b0a 72
    0x100d9405144500500c0740e81da018111480010905e022013141803402c541e00e50340150002807003240c3e0040c220b404054081482405031000e1403107504d584e21341101500c503407031602079104001c90441d0b100b0001405004010800d959001d6410f041500040c14030b9503059050903501c0d001e0b018040e441d8551114034890110f214a1a815035070261101030b140d01c0300400721480300315600e1500300c500308a12022005158102413003002c522020410f40781d16032149a0440d4031856042d9050710081c0300c2000350200001411008014544a6414241c40d220055104e1001441041d10031239462000460320313200c0540040c1c205c94020020002c241d01d5100160405000d0b009103800240b6017841d4029120b1099040c41c040c541c16001040c803890355500f046038692004204484a4600c141344100040c194000b61110081c0c649005c2401d6041c04081403410f841d441c1d103240d003205410f070420695118010a01d0b04880002e4015070740c3c061142c840182d110310001700c0700345441806400018401d50030341 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 919049892 1250 919048642 919048681
    0xd0203070e1207030305270d060c080705030f1902070213050703061403120a12050403410903011e061d10140109030b13050d02030f04050d030309050303 67
    0x30301d8002d8002c208a00c0d0743d0740c0100d00004001c100d04214502c6164941121070080a002c00d003c01d4420b440000481c1034000301001c2190500e85600b0007400d041d030840e5240ea40007180c1c1c50420300b540b400010b12010b8a4001d00400c1c0c40410120000502200a404480c00340e5000340100b100d503560600110020407017240c0c884000307898011b0109140c0ca400c15840c4944d00d00074003c00c85000f803504000d03029071000780d00409021502070002421002c0340216845540252103400081f030710410b510b05034643c141c01010301d01c2042040f407100d01251400c0d400510400b08001e641f01c546500c0424018680c1074030314500c9401c004000c02862055412401c2913030f400f51600c0414044c80300100000f0340d410303100616034000149080c48442c800c1c401c1100d500300149480d6607059500c1d11201179081e029121081c0107a481e94503641801020404800d01c0d980c1c0d840210b01d0400e2444801402c0d010354001e00b8440c009040c0403c088c58400d4001c0c040403500082529902e00b4189000802d0200a04c1d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 919051142 1250 919049892 919049899
    0x9160e0f041b02060403140a0509040c05090a0e040b0c0c03030a0e030d140a0b030f060708041113091209050a35030307020d08010f0501120e011112010f0303020a030809030d0203070e 80
    0xb4000c4601c081924203580d0071100e549c5503103090210160030030010b84001245401004414030043c102c50340c85200c110024021a489500b1a04203800d0184452134000c2441d40f6089080003104032114001007200e074004121a000201203650318512800d40c4601f90342d10034494281a81a40720000004125000c0c0c6040d003410031901000400f41526080700c10001a00c03500190b001942e020301621941e644280301d858074500c41229000041d0400d030383d501260600c141e49400f80c1003042150104941d800325075003400c4c4040d0f860301d0001088080d0343e0103099141c030412205110480f03042c4031402c400310080040c252081c9010041342c0e03a00e030021621400184542004440114003c1f003256050301c000c030590700e500d0b505000040da42810003084425402c0d81d20040c40101741c0c82031140030401e01b45540382582c3d661210030388141c0c501044c1c22030445440713160400c00c0000d40000b0a0f00a440e45410691001c1c1e80303203081c803070071070050030b8020070054000410029440d620103c0300440e41000c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 919052392 1250 919051142 919051157
    0x140d030218092e230f090105030c0d0305121e01060f02070e060105132606091b01110d050901080901022a070b07060501030209160e0f041b02060403 65
    0x5820000c0071042030b5015084410420442c0c0800c1c070200300382e00a105000c09541440c241d40c1c40c02803109a00440244c030450443e810f403582d0b180741c40f2401100310f1a04981440403541810000394440d1070241030544207110102e42101003602075820f940f10b046010f1039100f021b281058a41038003203c0e0061201c480e803165800410198050703483e0729034035034040d80100469818480b16403071088d00a0703c814140301c000c0c429083d6922100351000051302c0450f21042032031040207058404481d400c20318802036080401001000d807400540050b41d2000c04d01c040402490b00e2005032380ca80f14654078108240144d0b0b04d00d80100b5007100003845808400c1c1e80c4d8011681da110400c80c08c030b014000d02c0120074410078040c500041590280002d035104403000362005240c1c1d4490000c0c0c168025407044581c00e898000410030341c50000103680d40b0032600c822500c0548010140100701408490301c031480b83c54012440d20359500c595001000074010030480309041c010301c420181d62580c1c00c8a0440006207403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 919053642 1250 919052392 919052437
    0x1308040902191107030b131b051002011a190e01290c0a0b0604060b0c07031b060207090e07150e040506041b050f0d0203010b0a030b060403150207140d0302 68
    0x43c2c0301c03045042002d40042c21038581035682d82c6a42240c09410388003090821480100424200a901c51104c00729503820b00e01d0900c1e040c20700009441d05480d90065914010020301c441a05054280c03850030111900541c42c0c0384141d00c0000b2642680002054440c4030001003141000d9144000d00803801708a0294681107407030342401540328246041003290448588900040e42800030b032078028000a1001c2041500d8140c4868036030802003401c0001c0e40306c0c0340100300340143d4070040c1d01150036211101e0700f4035080100203550b170040d5200d100c00080e40c4801d400e110050911042005c1c1c48200d0701051046c0101000501a0b0604204035114900d007001150003860305205080701c00b2071114082c2c20080d1105030586141e0000104190070201c1000005101502c502c011400780283d611001c3d01d42030088401030880b4070041c241c5000f604100410300c0494802e64101c2100304103d040540c1da071000349840c4581101022101b8090320031002031010703003134054025080c1503082c0c00051000d41030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 919054892 1250 919053642 919053647
    0xa0b0c0409151d041101050901020a020303030a090b01090c09050613050d0b061815060c0708010c050717040521011b0e040b0a050f1011070602010203070f210203130804090219 77
    0x101510014443c10140c1700350006035004a000c0c10f00180140103032400303440180c02090840d401114903070420b558a540c0e40b020441c0c8610002e0151200040030401107010100251600f0003d00031903200d05404246500750003109241036010349030150241210300050325156421030000c3d6003442c402e0702c400d0191040154460141441041c00d051a031400c0c4064038180f10b800e50000300e4241d0180900034011942400901030400c0d140880c0c0c0d2030300d680c0d506030b0403c00d034200503d20300b0902129080008001a40e02c0c90b03422943c90080000082d00d03601070b41e06583c010040f84c41404000070040b1407104085400810f0021004070680d000e000030000074040180d480114040c00f80d201e07507034031004045803d110942c01c000043c035050078070403280d2401d1581c3c42c141880c0d01480060790000204955030345c3c01040c112025145040611402e0180e00c15140e04001100302c040c0301e9035000c000200c0000360940000036054000e403061380e41c0c81c0c81d03507a40d0000c0d40c403101030b00106154010303029a101c1c1c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 919056142 1250 919054892 919054949
    0x115060f020a02210f150708100315020d1d0705010c0b01090207050712060b04230703150f0f0302030f0309130906020d021b0706020607020a0b0c040915 67
    0x4441d501402e0b4501190f0700b0804241e2494401c0550700079001303408465550f04106a00d441005800108480d072194110082005c03801480402008004c01c2444102d901d00140101565442400002d44000050280380240202043c8515060500c24031144145601c3d8a40b184071400b0700540e00782e41d44580c0159451038400c4801841030b000e2000400410b60198007611045128905440480d5900c04c80719002595510341550b0a0742d03105000c841a250610501c0d03611034501484076510004842003212502c0c1c0107120100307158441d49000c01e802041440c1402900382161303310569611490380d1000f00c445804201e00070f105621a07070540280000507500da80e2002010f11100000d803040c0c9c03030080c020005c1c1c12104203070240880f4403600402d0000e00205021045400c00c484030540c096458107802750700a10541d0850418030802030b50200360000035580040d01100c140e1a08550b4a02910865004d84842841d200d2540d4050300c0d502018412a0080864681c80c440002001c11000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 919057392 1250 919056142 919056167
    0xc0201090f14090a18051609050103080702120c3c3a290402010e0d0c1518080303090705040c0216030506091e0c0d0c0314011506 57
    0x101046007014149809040160f01040c980b2003c03405c207112040c0c0300198403200030120781941060201d202d40304401810b42000b414074000a10040d491525000341e82c1c85031000c040d019480d121ba0880130010200310084021078040c00400c130b110500c005403c2e003032502030130407415070345020101070070100b504102d10b1002d4001400a204c0450701121004042c0707035082c11000540d030507100110456590100c000d203c83c0100c03901120815080e802e1440000d4032803030404428941030038800540d13072180c54603419034002d5074664025500ba06005007248000d900400440c09841001081c056004070780203100c410f808504400340e5140c401d140c2c0c45e0702080f10000400e9001400c01c00075403502c3c0d005509000302170300607940d071403e240304256030364905034100340c4040c3d01800c28044200e00c1003100c1d1080801640c1c81c944003056081502e074803100c9441d907162040413024001b806010b60440f51b0002140c1c04070803514180c07103203a0b5403400380000c4202460104043e1100060791409a800000071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 919058642 1250 919057392 919057409
    0x2090f091002070c0b03060a08120a0f0c0308040809060f04080a02180106121a030d111002040e0f061210060e070c03080f090c0d0305040f090b330a0c0201090f 70
    0x42403c05e82d1050f0305030401803166500003404040041c484605010045440c5403100d500ba81d41d840c54903003e0000c140b021100c00030480040c040c000800da01110246e0400d031702840311555040c007807001030040d0007010600c10100720006000a42241d001409856081c402e4410400d564003842d00c00355851000d10965012880c1d5000410708001d030790740418805141400c00312800020340703001c00c1c03030100c2c001d800c0008140511011044d01004000d5140840120131081d80b8050601400c0400300304064135070038807946940041415a621501c0c910002c40003201260030756146502c400019052900c540008030016501042c00d241c4a20721400d4082c3c0c064a4003016134403500c1d48070f1280c0f81f00600c3d40c5007500960452401640e0341b019680c011500035506c440d100d034100303512240c49501507404113180510b010b5264200e600c920204820518980e1140402c8c24141c914079241e0b04603c030120031080c1000204560025006151032500c0d500030b0380c91148150300c40181c03a001c50401c5c010101d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 919059892 1250 919058642 919058663
    0x605030a02092e2c04090c0b28050a0804122109031101090210050703020c06030103060608060a0506031b01110a0629090408090d02090f09100207 64
    0xa00516400078014100041d0442d4a598038035001504030071400f10340c0910101d66401040100340c1e120b000c41e60f28000900120311802881c03291003e6060300504654069a201d0400000340072071012210000d00380c04450965854031192410050f800b07182c02c035035540394101c1074080c2c103500ca40c080c0c41e10060b10340c684202648894541192151520480c04104184042c1900030100b10481c1c0381c4c06202070700e00101d005005440d01600c4511f038130580c04100ea24105044002da42c0d00c02d14105034680c54146242d035000c00d13081c00c900700702c00c00d4031840e00604000000010404240e0140c011140c42605440701a2204d0208400742d40c8240c854651591040c5020b080840b03081011900450050509440c1015000c19070350400c0c104090030b480465030f880810884050350310101328900801c1c140c401c00241c0c4040020160345c000f4201400b580b0001c5000b200a0b11441c111002641d0020107400715450141c8220800050444a122681c024070f010881c0551140c020380350103a0b0b00944050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 919061142 1250 919059892 919059901
    0xa1706010303080c0c0a0302011517070506030c0c0a05070302100c0c1502010204090f2301030b01060f111c030c0e0a03020d03030b100806011b050607030e0106080708070f0e01060503 80
    0x543c0c68001814400ca0307100300700941c512000041040d120214869000818889050079a01034040038a80c40116515485009200352010102c1d138001982e034203c8485440741c9841051840300d00918030800a10300c1405044030500000107540400c0b43d1003201c101aa2070b05802c0100c4070303103110801c014500469050240003110304201c90b41141c0e85035100050034240d880c0452000d40f1040c10750500e040c1c0e59034020360007514140004a00a0700009840c1d800c03135255980703007901f81c04140326000c10840c003038504020b5948a03081400d03007140898102e4491441d040c3d10514560500c0309403001103403505440c241028001c1c0d55503124202c1c0101010141032458007400b242038902801201090340d262000003550342c8510f0080d1040146642352580c5280440000d01400040180302d0240c2c4015803040c5e0005400080080d0701100a20700429a009411001805846203070003c0c622806440004a0500000101081110700f803480c1c003000207a40341c06240e00003c081c054480015070030000107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 919062392 1250 919061142 919061147
    0x60060304030f0201020c0706050c060601032009031501080f06061903022215090b0d0f0f0c171b1206060d11030615031006150c020d0c06030203060a1706010303 70
    0xb01d0b1840540000343c940071250403001d0030600c41e5000720300419804165100410300c10008294004800c4c2000c00480300a40d003043c8441401500410318800000381c3c07400c903074405100001a502c01d0210030b11030f03075840c0e04400342c4408403094008254400e1000180903880c02010f0a003103071a9040c0d04c07a0500e41107400740101d10320a401c2078203080001001d100400304652013a80c122869030090040a1420721802d0340c29039964040091144001c05c0507140410802c403500300e00158008802c54a900312442c041480004550140f444454800e2070086c0511011404a8101c0b0000781c00c400d180ca102001c004071142421100096075000c0000142582015078900c80024050140354508044c00c1000902e802400c80d9150349204102080c42e607541030401c801070041ca8541400e20031241030a43c00c3c02d1a04051407070b40d04020b0b030002c000c03095494503992a0380581d000324642c80c2460302c401002d4007135030096494600590030103100140003c03501c18030031043c803401d502501d00c1383d00c1c50700c04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 919063642 1250 919062392 919062407
    0x1080604020c120a1106100b122701060f080307350c01090308180a060507050c01020712020d1707050702120f0a0201030f020906036006030403 63
    0x3102c244600c490740c895035005080076041ca45115030324150b02c2000b6900326400c01d40040c00b40c20242204101c1400710500d07a0b82502c005c4030500700001440d0365840c44a0030050f0010441e03101c40742c044822403061278010b40144003910340c4024641885596001820358034803a140340034050703101054622810380500c8104226a100c0c9106038000c140180094940c03940c06801d210302c950b907607020706100b0180c0040480e540159052400450f025900c282c540d1224034600008001c541d0f20300005400078001d600382d404402c0074800841d2504000c0c43c0807000010054401c0703003d48198900d201c00c0b507101e944540c0c481182903480c080a40ca840c1d006842640001d901207a21403034020513588001800c00c07281c82000700c168000d04c44902580009000c41d20100145a0740a0040003801071035281c800c122074000070b440a10960030006000500c0102004088400b41040d250039524403c0744032a03e410043c0c01030b0102201b10420405800c0c120010380b00039580c1001d030600009002c030b03009481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 919064748 1106 919063642 919063657
    0xe060f1305271303120b06041208041706070903060b0307030204050a02090f01032d0f05040c06021b18060d0b090f10062702040305030403060203150409020108060402 73
    0x4c1c0140070900c02c64080b648543c03a81000f01a5464040840d070003010510382c0075800ca4290b00d0106a1548203101c0c0303007083c0b0949001e8000c00540405d01c00d02418041d2118600b0920790740e035030800b400002d03041507858000d6400020150300c4500503140301d104001b100503640c1c00181c1c200f10b40f2190f0810518101850141c012681d0640c0d10321180c1c00302181c00c500c03142c0e462404000e030301611141c091022210308041c280800c124844000c841520090b4095a02c1202c0f40e2004280803a21030f602d10b5032050351400d016030307011040040c03150400310150840c900c84986880340f540c0e20303c054526001c6a442503c6140b03515009214440c0d800e100400103010081c41c282c2c00041c20403c40c4d07610800a1180d882c51203105401381d04a600456000050300e8486030341c1d0030020000d400c11180d101480d502074000310f809150510420144076030585400781d031612184103101c000e420920 = true := by decide +kernel

theorem cover : BRFrame.Cov 918884892 919064748 := by
  have h0 := BRFrame.cov_init 918884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 918884892 ≤ n) (h2 : n < 919064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
