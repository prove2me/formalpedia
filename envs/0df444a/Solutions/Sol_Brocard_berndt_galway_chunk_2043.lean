-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:31:16.808262+00:00
-- url     : https://prove2.me/submissions/d06bfb4d-a2a3-4dbc-bf18-ca460cda77a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 367266187 ≤ n < 367446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 367267437 1250 367266187 367266191
    0x6080f010609180f06090e010f0b030a03110a060228031a19031208041a06031c12060b03100e0114060705190b040b070c1a18030c0d080c04080d03 64
    0x3840d040c0e600011308088a90100461500d40e00156075045504410307080005000208800e005d00c5e1074201c140c0b8a90401aa40b50704215510f40010b4090102441909080b500b198103e00d01c90340c62104a911001c01c03007250456101c48104070305154140c241e148480d6290502038111400c0e16405041e108140e09441248403107002c1117440d2152403031200640c0c0200100c0004004904090301085c000d0b14107443d01d8400a03000100701c0c200d820f906000d54801390040c51000980807010700310400b407003440070810652032030030509801d0074021080980240000c03281e490034441700f0800c041c02d0960181b01040351010040000da403800e40400550481034440b943d44104074546039041c944070100030085c04407290940710a200b90305001c1c80c4100d100b90440541900e6800099684d802d03c4400200940c0c0342800c12180701394110f039180d4008543c0c1551900c0c1100c030345a0300381107400071b0600c80415403260070405001c07a404940c1581124104104034074040c1010901c584070001d05001205140e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 367268687 1250 367267437 367267469
    0x20a0f060e2a0406120c0302060a0509060309010605090603011a12010207081309060501030509030a110c040903020307110d02150f0409021c0c02010209010c0b2e06080f010609 77
    0x141c07040c0800101a1401c100d1610200500b0260030b07000d10742203001034091460075a011444840e04104142c6082d002001114014510307820845107902c0105447c007001014800c440302c94030380c40080c5002d40b800f2400031410f64105802c1c040c0d011401080d05109a06142034444002402800d884844109542c42800114070a02040c00780c400c4060061001000146010303000b01d81e1684842544c074503002c03e20815a07150700440a40d042941c4041341500200301840c031a50081082d41512050003068584c004500b00001d41260810300056015802c0094480c3c10491071100c5000650002c41d0481e20f060013607004160469104181f0b107001c07160008440e40b0300a10070080d20001c0c6002002551340d84c54110b640c500981d0b02d000e44002860602541461550041c000d850627090107030b513010741803c010f8a94102600000c0c0102c40e403003042c0c090760082c0c0850b85c0200320b50304407488401c00d2482c2c58190010201d01c001060051600e2540b801032040c44e5200d40c00c08115003e044403c1c04603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 367269937 1250 367268687 367268711
    0xe04021809150d0f031202030c04060c020a03081c0b0301020c0705010c030201091211100506060316230c070b090102060c07140a0507180e030702090702190605010e0601020a0f06 78
    0x14011501d1060b800f080740c5003450100541d28035840a024825516000c4260b24003118a059000c240c2c0e00c4008500b05100500c44a032180048809203030004140864456a94640d880541d0000601206090505000400e4003106009500100206400031840e0241702030205403154a01d006141c1040481c8002c01c00303141c0b0075040591083d410003608240ca00d4841c501034600c52103001c00601c24040c0c5605100b5149803803040c1482004058407580c9156611243d0919002100c5118014028214414042e00c0074003070300d208803151003c4101c0d555944800c000c0345481c0300c542c090f002d010300c1088050101d9a001c200c1c1504410b40100c502d482d502f20b0301c1d11035140c101c034045100083c480d03d900c82003480000a141000ca461104822000b051928143c0059a684c0221080240c1c401c021020041c03c10315030042d404070140c4162501b90500c42c07100240e140088105036071050b02c910060220240740e4040f0740d04004240000c002000450b0756002101d584900c01030101960b46030b03420f0b09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 367271187 1250 367269937 367269961
    0xb03060f0d060f060311040b0a050114042d0e070504030f0204020f0a03050f070f020a0b0711030a030207021f12050601140703021e07030309180209041b0e04021809 72
    0x1555500100500c050815500f10f4001403180d40f10580304a0180480f070000c90609104034a20740c00080c01c880110350420f0015690000c403d14400007030700e400c01c40002c1248510038514060f205000907407030891500c2c1c0c07003100310f01e00079002025405d108105000020b60094112000c59a00c070141207140314941c00003c2c002c0c0a58035404000b0f0f60005084c441644e0f0542c4813600c23443c03100c4480b41c40c1e0703241d0300811500b00e14681c504002681c050b16a40000c83d824440c1c03075a22400d00d182c04c884907102e010034181940c03c0366410501190f00443d0001c1145400410760380c5030a43c09081d6100012103010003008990310f80761148d12595550040340345644201100084d029407090040c0d619402850020355416448520300c1c50b0441c00203010440c2a0085041ca084940541c0d64100f4107041030a009680c40780041e000c10b6255081190700d03c0ca807201e0040c0c3d840c904001c04100c044c484040c1000d02941b5030405218403d501c10040540c2403032222120b868640c1040d107022000d03a07a88403803801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 367272437 1250 367271187 367271209
    0x81f051005041407120b03030706091b080304030b090319050a030e0610090e0d0f080703061e03122307020324041205090907110c09010311010906090b03060f 69
    0xa00581840c40c0008803000f4101d20f0f03030040c03060356551650700306210000e00484500703113151039040c0c008000da10302003079a9800c4030780207501400c5800704802040302205081c407103c0d400002d10750004102042440102c4903000e50003103404000d9841c00d102c0090903102150f40c0202081400800f04401c0314107807095102400400d8010b00f151030504090b0000e9002038446d105ea952003608050415108900c046160100200e00303072140c0e11441e0303076182c0542d107000002f0a2030301010b548590000b4a403110250581407181468500103001d800c0d0306200b00c103034042d41000f00510908074000e886803265120031b45a03900e90000c1d5940c40749410b20000b4100f0307201d406051406045031050802c43d034a200c05041c00f803481812610f0115000c81020382d901d02031070b840345031b1010600303000410b000e00a0b0254180072a128050300c00703440c081d0001445551007038009a4003500707a00f40d4001556003110392071020b0003140c01d111060030300c0e050400c2c02ca840000e11443c050f01c00415040f196480d04a1105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 367273687 1250 367272437 367272439
    0x7020c0105070305070506010f051507020f1c1a0a06120b0412030b060f0a08060a06171e040501090b060609130e0309030708010b24031317070b0907081f051005 70
    0x10701f455954002281d106500c0d4042c080c4a05ca09200340b050140410040701e110300d90161141c802c0503181000c00002e580b4400d004005044182c1d10320000030041c040e9a1401200100d69110703d00f0704464141c11640f1a03003104031443e965000100100c1c107540542036010750301c142c54240d28070b06400308030040d100d0803452507084007006c11a60346a40541004e081009400e644000c060740e154010030030580a2445124003085052014004100e0107003a01503001c1a00c0c0c03003200b900080c60b0300d11140c150045405994136555021424200f000e04658150488001c5500a0a01e800c0070300045515440e001d80c1480316607256000c02112500340141c0d462424018190740c078081ea030304421401b0b05520302c8240d1280a0011a034151005013000c601ca0013080c0010087c00c6a0340c0011001081f9150941561720b0000c52018941c1604540010711010384200581d00d40390912489480c90480150001f0f0240e8020142500325030010b81041c1b01c0c003022440c404541616940b18002188036290855 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 367274937 1250 367273687 367273693
    0x19090603050a05010f0204060504090c021f1b0305071b02031c08010315020406090303050c12030a0e19020609101115060108060409020a120303020405040603060b120607020c01050703050705 83
    0x1032010100351a0b102e50300910080c465028181070020491041e4003444010820034402803100381d105074014a00078a00340102c9014024040500d0220328002c180c01400c2900d07a881c403082c01440d0140301801000606040c001c60800c29805810440104040c0e0000d500e403101040c103558041010f00a00c181c0e44000811441405000406ea403409000680b03150f00010100415204035208440446645541c0d1081860942c4c1d0201c400d0360000e2203414203031080c418400703a80028440210b0180d071849100183e5100e0801c0102e042c2240e0780124244070b03518001d140c0168031110101e079040340c003c40f01240d061003e80c2080c0c0308000d81c401003071413611550003004031322140c0c40c241a00681003600c0e102c070255201c3d000c001c180c40c81c1540080d042407078007030100441c11843c074122030014403d040c05402c01d601c40000c079003101d04641c400d07280a600c0c0c1f08242c00506002d0091103446800c10040d1000d890850000382d038541224000350304000000070150705040c45207042da98055800800d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 367276187 1250 367274937 367274939
    0x20c180723071211240a0b0a0b130e01050a0302060c07090504050606090c09130f0e030f04030605010b0f090915100c03020d0504180504050708150f150f190906 70
    0x200f0300d20124406500440c0b034040d4611209400025080c0203840d21107404808808100400360380000090b008a16494a903144401207039658031000c400380c41c440e59201d485003c0c0030302030100340c03c95034002c00b9181f215100500040c5c40f10300c1d942d4140c0350190b0b11107942da001760b40640d140815552040101c40d14000c10300c410081c000c19000d0184408490400306600d415162054a104d1694000d500101c503202d482e2007000c1541003040c44890b12400064a051003910190a640c046800074901a8001800303004111a030710440340503240c1d012245080007200d0304603c5145c821010000e1149400c400050200840307060f4191400350060100307008090082c1c00a40b151821043c202c02601400520028081c4038000740e40440e021404588000800074000c440108406007041d01c00d07000b1083c0120303081004000140c54080c20f03030440d442500d01055400d144c41c50181c40703180e12450b040000342d0665145100300e40895401c4510400c030494250046030070803910361060107240c0c18014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 367277437 1250 367276187 367276193
    0x30c0f180c0c0c06040e0a3b0709020301030503070f0c0f08010c080a051014030c03060c03010609270f0e060a09050114060d03050a0207090615020c18072307 69
    0x20b0500c02d54800100c1e9848107120082289a00440c010a44001507580019001e004940c01c485041d42e13002c00c01810f000d403034000070000e100c0d00c22103078840c1c0101c4801e15168071800704003000c010012084d0841c11541165902c1c0d8492040d0303080a060407604078584018000841c00c5540201100d120410b6500d0ba80c40380e1901910b9030007428000b09100c903002800560440c05080c0c40380ea01f100740176203003e041c5100c0445400280310388076014824900500002e8904004003806250b042060301e40303030b40c5442e000500ca241d09801c8007150300c85030044450b000892070700d101c0a403085504049141c4603881e03600750052a215920b81410300c110024000c01400b9580183c1c00396004400900103d000b80441c007402020580300c5a03042845004c05d240481d20543c054001c441c0c1b03a2050326200780e078624200054404a4000c8600e99030700410114646030100b06d1059001c43c10744200d501d040c503000b00c039405007034024011710622650f510703124101d401e1809030b8100300401852850720360700d080c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 367278687 1250 367277437 367277461
    0xa03110607410a03080c0706111303170703050708030612070b09031603080a0e18040506010f0e040b0a050c0708040b0927010b1c050f060405010603020405030c0f18 72
    0x401108142d00386401032140810101d2401d00054254940840b40e0f00c402c514941a03602000c410f88809654032000f20401e1001d0000b06204100189625001070035410101b02240c00e681390010701240800502c40081d40040541c1c4001d5080019140c595407074002040007400b0035415465a0b0142e10000b1509541880107050104015006c445810b5200941080784522a00016010790418804a9aa0b030302c81c0034280b030f42c280b0140c100c80403904500d004092050303064804842540010b00140305003640c2c40c1c8080020802c2d03a03c07141e140d0902d0f880e55031141c60050800b10746030740c40c1c0b4006014a4050001c07030b407880340e100c111607903910303990820308159401810344c113403080c1400703000d001070b11483c50320104610b0300d140f021401070303483c20039044403540c84201221081002d1010320708545c0071901c1003910902c81007060b0b81e01d5140900402c812114160440018184140001e0015031000600d1006500c03081d00c043d0f810350100c2c0300007800104035080c1140740d1003c800c10008410100c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 367279937 1250 367278687 367278773
    0x25110307030c050106061107140604030212060f060f090a091e140705030a08190e0409030c121b02060c0f06090f010605040504121206090612050c0a03110607 69
    0x9800200845d40c1c843d0b4003115003105110030032683d94040081400140e000006a5003542da009062919190b42c1c1e5012502c411f406400c801d8840d08041c040158900c0c40701c1c01683d200f00c0841d4038035100c12043c0c000580c005005890400421f580e0722407403081000c50000e0100e0b81070308031026080f040e01460311002130f00e5200400d82c07803401010000a681d00b000030300303620300305e80c01140d19060105040908408514261205041004c44840000103484511031841020702a40c0e548081001a042000d4648108520041002502c50341540d0454000b01480c0591b40d040380c0c141e58401203510440d18211035040031030058040c0320144113250200003192001c07512094024400c103039994081204681045402500f070100d11850314402c0d07032044441e1031900c038695a00141082c0c442240b60110b800c245c0140c008450170700d80c0203060103010002c48072400401c607241401d050465075184c2c512001c1e5500c00c7d0240c0700206168080110021208062000029204050045450000d1105585 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 367281187 1250 367279937 367279943
    0x106091a0307140102060c0d200a231b01090c0602250b0a0302161a070e090c1b03040819030807110d0f0203070602120a0e0625110307030c 61
    0x2040382c0052641c080c107084119401c0c05070086d121541e9000360805480d0701c2250804881e41e6030758111607028400e9900b54480c50641b05885131603801303264000c1c00786407400020401068003250b0704544103148100301c070101040ea4445102e214001d4200345e0150612560040908100300c04c00300340d00307a0018400d24006544000c007a01ca8110700d441c503041034500c1c01174042c600810005003e8081c0203400403c008400d0300002442e044480e01c840d0083d01c110ba02d5008030101c0c4005019900b94012a028030320b10084880820501384000140348612844d100300101e90030201442c5036042041c400d0394024004031080d41d556000e40c3c054020310f401070000c114041030064001c13070345941c4912810002200b407a00240b82007105000c040d106104000d0101c1e04600c010001130b4001400c1e030014144600c01c0c0e211050080c00d140901708159248100b0700301040d07100304100f04c000b68240c0b40200113020005c9084441003116070341203445280304100104a440001555401c00d940604810207083c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 367282437 1250 367281187 367281193
    0xb060f040915060513030f020f040e010c2006040609110d080702130905061906170102190f050304080f04030c081005100503070b031807030312060909170703020106091a03 75
    0x184440c01078403940036001d0385880517000c01340107000281c8040b081e1a0118001402d0704003281c0c00400040c2526507169411080b0b9460358600702c40c058006003006841e08a400c10ba408103005003032015611030000700090400c07925541c200301440f2100f000359070307aa00c0142203182d41d07801c10304204070302e036001c1c20049005800030300c01c0c0c65102c8420320a1081d034540c050301070089501c0c0c90020481c08105146905011662074100080c03c115075450f100044013401c00142c0c0f00da03019440014110030103a108014052459407030401c10340d2002c1102d0f801a8400d02498451004908d42d610a014039000200003101c00031011400303c0f00091544480801198140700c03903560700c0c412210000c0c892040c10b40580c08104180040041c9801440d8401d240e482d516401c80103201d40140707001c03410360043d008546c51300507001032104e6900a1101030036410109200c06003280da03412481c0c909044c84880d10b070b18089486020907100f074100c1030081020400903c00c01e101441d410320720b1051813520740d1082c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 367283687 1250 367282437 367282439
    0x60c0706080604020415030504050114070f0e03030406080f040807050d080a0e010c02070b0702010e0409030905150c100209130518010e0c0906040b030f0a06050a060504021303060b060f040915 84
    0x103d4036000700e400380ca03410408000c90964100040d8080c050151045138155200d40810340d41c201e80301d2240d4441e842d41e50314802d810400303d0001d0f052941c004580c03400b0342c008000a2206640152040b600001c1c411562034050360303582881552030185150040050113890303050240e01ea40500114040c4403068000c00045111141c032a00722010300c01e08101580195200304480015000645441c50043c100f400e0300c26003101c0000c0441c2c12002d0f0880229105103c240080e083c402001c50303181889030380c0f1614014000d40c060f690750454502600d007254001400c2081ca488603018034600c1100c21105100a09060002000080480e134007060190320300a510440f6010008221510740009000390702b00307886800a100261008410945d0503100c2e2400035842e58104000144015008640c0041e05013880c40c00202604d00c40d41c0003070b03c140d0044c0040c84407440f05d02c1903c422250700200002e9240041e00110f0f000b40202c040205554002040c0092081500e8201c04a1020180303030509142d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 367284937 1250 367283687 367283689
    0x304051323071404081c0504060e0d2d12020312010e090307021f020105060a0509070f09180603060615050f090a090e1005100b0703080a020405060c07060806 69
    0x72001e22900750100c01001e4844401800000c0d55160400a07901d0008000e121810ba45034040d4807542c410300c0b1a600040031180906240c0064101a41440c43c01c145040d250403802012507903005404d078032a0a11040c100c0800000d180709000c0801120b040074404844041600c021000d40702e01919142e034514180f1190078804001ca0315807180500700d0b070b0030300d03400c0413692100510002d00c01070051208001101c00f6a550f0f4005070100c0b0206000c1d40d61842d1102c070028259080174002d6806226005002c0c00140e4888040650102d485d1402c84825828440704545150256202004403000b210482403d40c100c2d40001e0b0a80b401307407005100c1140c1c0c800c02c050760707540802014030008a050001800000d0444001c0c00100c1004025115179a01c07551424100d400c1d4040b0110b8540c0613241c21140c4142c5c0740a495840440782000010440c40d050341084103201c3c0000017410082e00e84000303001002d9950548000e003002410290300d40b807010b42c0071790752400c003409501c0100d0b25034000601c2d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 367286187 1250 367284937 367284941
    0xb01140a0e220507270e010203040f03051617041d091f091a01080c0301060e0a180f053d0203070c3c1e0503040e04030203040513 57
    0xca0040d11407901c1e981251080301c095080c1003004a4584c014034500003510030202907450552035401400599005600d80158101c416804a01351143d006008010102e034450a00d1500250181042640c039050100348828540c8400b0008064000da02504005c01200c00040d0082d01e00b5080a1409222030b102c40708080c1c0c3c03003107a407107503a503100d01002d03842070080a0104c4d0110004500114a400660359486198014424032400191851004100c80d61040099181d00c0c4000c2d4000c100e070504001181000e5a0018049402c141d107440b440326010035050988207106400007111640c07a11380d8903015031a5409203040800c1e0f5980b944000034207040031301d59000a6603a2071554001341d1030060341c18000e50030082840c1c00b80001e11440201081185110264022481118465409000342c00040c40c0008001200b0342034180710000c4c000030071084078408a080c00c0c10941e0304216107450300e180ba6205540100040320384010500080540010180054400807140c074208202c494441c081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 367287437 1250 367286187 367286191
    0x305120a27051903020f0312040c0e0906150f12030d140903070609080c0a050f010507210b150f0301060815131d01020703080906070c15020a0c0b01140a0e 68
    0x2c10350704009110300c0e10603000d8101040152107030040d500b08000301d904141c04d640010f075103016458400e00c1040208146000810301074202d800e1404024104074415541e81d42d07000f000644051024044400e0f503603200d24800c046650028009000300d042c00d65480c0d1070340c1007404200b49050034800b101c0c01e1481e500b1134241c030604244004600300005074944002500c29004251002001003048180c0f03030805000c2c0b521080e00401c0281158084c08607440d0856000801040400c944e8a0b1440c803030384030b840322810392891014030209a8055000004400141e070788892400300034001803480e58040d204001d94100d4200d038039071250641d079620040444180020104e50f0000341a03501420300400ca0f40131521198060110290389402c50100600f2030388008016400b1940712410060307001d07401c2041e1544a11680703040003660031541d0b039820748984086c002c0c50400c0c2d00450803a01085c802c0308240310154100344008480d59580c1070b040f4016818503107a902a042030303100410300100d03c0100394 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 367288687 1250 367287437 367287443
    0x180405070f03180b0403081e0912070219060c0b01050d1e061d010204030c092d02090603270d02030910090f03111002280305120a27 58
    0x7152140a40d0421001030415a29920001d2007a01100010406040180b407159119495040041c100784441880e1202150b40901c0f10409003410810700d00000f0a2030601c507246031384020f4840089200060240d0f052050105846181e6031b8005a100e50080030a00303014080c2400c4080740e43c865082c0a2050441e41010b030400300d1280220295142c1c0307884201c040c6003d8040002d0801c481c070318480205541c0100003505039000308060091013184c4840d24020b01801600704403205180d000c44410307441d4080c542d6050250340ca0405010b0304190102d07010301500800c95a034a02c0c0c200c4051302d803c0305001030013004015060504140f62800210404515100d0b0002c50800010340d04000015030708000300810860307141c02c001040d180280d485005544102021b1043c422100140064207d401c0041c504662100280180356015000e45c030038181ca4a140c0c0d414050200c0c01c05031b600b0b2103411107402d54030070380e40d0030802000321583c401803441800c11101c500c004007411082c8244514a5409 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 367289937 1250 367288687 367288697
    0x30801030209040f170a020f0c0a0b031b0c01060f060518060f070b0405060403031401060f12021b0a0203120403150f0908040f051009080303070c11040c0518040507 72
    0x103002626021a0640e071080c441c6809403407090041e61410130760100c113050210b03031080200d20044003503014008220750005801c014042d0302c04c9a0005000801c0c0c0f03100e15400044000701080c0c030401d802071008200040082900d030303540318003820305001300208c5c81088190000c1a00100b2101e1164080324006882c00c3d83d42440d08024204000b242d610900f1240c41c284030410043c8001980455414030450107000501001d240905020b02596105030500b00710058540c0140010b6422000580c02c1d80c03030f2403400000001590f01042c00a225021030600164182e00300000e4065000902c000b806100790160b4001d0a8a00c5492055008500005114540414480d04801807541c0014a026510f4502042d580015140c80a1030390054014220304201c892041c00f043c10f0945620000716403501c0c01803002864226900d0712400702502440420480c0d05881c401d01c100790034030004520005004208105a4a0703005c3c1280e403007140d101c5000c003007414041d00f036071030301380308230741c450300550f100c1e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 367291187 1250 367289937 367289939
    0x30b01180525120c0c0507060c0b040308040c0317070c060509060d020c0304050d050d0809031c05090f07091406040c09060f0c0b0f0121031d37080307030801 69
    0x2182202c141020072450420101d052401d15055a81c0581d046070403050722030907100d820b6070416504207403480c0c001c502800282040080012605000940e1050705881c2c0b2203559241c81c50041d000122550010b4a0707040e000110b544000e24140c02045010722550006a182c2d95454090325980240c3c002240e0100c018030803011500c1c7d8075001000000da8110076603150540b242d00049042c0311070f440a413420b0384411002c078821344e0005d1119404c003128400071130a0442030a880c014041c0e00c803144000306501c030b20100755599410000019120700c40c2082d02c160304e481d040982c0040c50500c02005410324141c0200d401030815100e1006000c1d100c1c1e44002016003400f20580340640c20901042c2041a0442d0007408903004840c01801111040f031070b91095458810744504040b032a81710280c3c4529085007080020b81c115505550402d020203008926200040c0000c2415000360001003a0a0181c000c1c11812560b500200004505000001c0c21454551445070b5032802071481c014042602800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 367292437 1250 367291187 367291231
    0x901090b0a0218130603120305060d120c020d03020d14161202070f03110a05010513090c030b0a091b1e051305041401060905030d08060f03010605030601030b011805 72
    0x804002540c0c0c3e201e4001107442d01c000c5509103001207541da07407290784c4803024800c124441c0308103440341e000317468180168200707200003e13030304014400010042c00002c02c02c1300d030f8036000b250640500d075002841c0c89a00074035810080d440310091b19407440081d114a0f1600d4003a070064007620722800c40c0d524081d001028581e618685a1030030700320902503102c1d0200014490b000c0440880c0514403500d24040e4803062282804100c60064020320706000040c0300d24402e11980310441811605114030200b2071880400042c1c0082c8881e10700560094283c400101d0b405500d90400f40289040c00000d100c41452100200d070b1241d000d810481001ca4504141d40c00b451090029000c4c0e0309020720250f41e8103a613807001030200e40b02c0c2c42c02411291585001000403a070845007c500030042600070780385040300c1030b03001440840010708140c41801032030711174000c1b520250f200781d02420016044500c5941c59083c0b5402e101400d01c208403030540c0040807049d4048580c0103050081d8191044607600740c501e00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 367293687 1250 367292437 367292441
    0x20a050f030601110303010b040801060501110c09190e0c090f06011e120c020c010807030e0a02010305221a07020705090f040215030106030b041503020105040501050c150a140901090b0a 81
    0x1420740b504200030000071020301001400158020803802c0c007503640e52440c4c40c00365400d46100d40d00060610802c1207441d9010140070554a0f80007400b00c2d00008282e031760309410300102d140500b041d05220b02d46003682e00038590014407940490000c581501c450340d50803256410502d0304413070044c0003800312600c01d155008c0d11b60708500590b001b41040c44150021700b030340310102c696011242e80140d120382c80c40d00c03007542c00040301c41d0840c240e480c2c180903000c40d10407002d42d42c18912500070704040d5181c0c00144100e400032a40d0352117202c0492490014440c80c1410792120303c26988040c0c0c10b042e6280420710450001401008480002d052a1495900c0c00c6644488070001402603802a03040040e61803403403000c0c0c0055000c0c0480d500e00081c904900340502c42120f08070b44440c00f2040b500340b0203002607a001802c0d10115282460001c0e0381e80c01080301c10307040800c0e00c1d1120410010704030501c03070317803480c541c21030680702610708207508280e500c08014230b003030f00d00b5500060a4249480041400c00d1255 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 367294937 1250 367293687 367293691
    0x60f0605120c1e190215190605030d0306150905090f0a0209090a23100b0a02030c01060807090f18081b0a0f21050409020a11150108060a020a050f03 65
    0x444100b43c241800012020483c205410201c509041c0c00103c6951000c40d0444c140c0308402c59100500107826102158200354901601140540100204a0928054941004000d440041c003500c0a8801c10200a00600860300440d55100031418080c001c0510030480d42e8102c0b4030080c480000741e00c03600c101c1001404054150800146c00f08079140c0681c5407000c0042c09129403810005849200380682414201490800c0407803540c00d205000e5402d00310000c0380c0a0340e09802d03255176903014500050340742d0f1194050506c129401c000c00003030301c42000f24005003110001081031000c040d2180010080f00c451812102c0191071300c400304004035521202a0000740e4005882900c00011040114544250503808aa00001e001e01c5541048481c0802c15001c01d20b0795218860004240340c080c0850066000704c445403540451446401445136010005c0c03500c6040035035090b0529203040c92642c0c1070074002c07509a0f200e20808995414036520031035008000568480d421329202e40e031646025440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 367296187 1250 367294937 367294951
    0x20f0103020d0218030f1203060918070906050405060109050d11040b0303041413060806010303081f0806070e09070903110409080406180503010506060f1b1e01060f060512 75
    0x424800d00340c854202c0e01c01041a40f0b07013100102007801180301010b10702030000c04144510303000040b52591003024a4250303074000200302e60038002581c0b01c481c20b040402015140c0040c91049001c0001c1c411100e41c01841500da003030b1002d200f82c3d621700b801518424a103118080d0044645c00040000c00d202511a400034080140b01003604040781c0000303072031900180c1180300e00c600e0041c5d4112481c908103030040514400c4c01d5082c00f011b481c10b90740303e4652605200c050148500000041c1814a960322011003070784076003031003a00e00b640300c002c40c07a40e0307100440b17500000c981038400c00c80403440c01051641c403402d001d50340c5034841411036503080c5807041d01e0302e50079400c181c45010503000a80b56002500c09421141c1d10140e0840030702c0006103114007203501150090345448140900e41d221802200e00b40e215050107076555855030f104090a01140258002045c010a020b412403a034104034034044c00003501000340801e60b1141001d161401c45441004040790040081c04c0d02c2c1c040441c802d80c1d100708 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 367297437 1250 367296187 367296191
    0xf07020c03011a03190804060c14060f010509070801032303090303160b010906350f03030105100503010b0406180f06030203041703061008090c060d0606110a03020a020f0103 76
    0x2116000c02d083d030b00306402c5958601c83e04a011070701420100110081614a000b124188500c2c61315480034030720840c0a44410000d00e0030a0609212100030f040c001c900340303102118914904103d50790200300003070240904c10904100480c450b00d1052501d90f042ea50008007100340391000210080c4200440701c000740b42e50106121000003545c003031001d401d034159a240c0040d42140d107850045031031321050308185a030f0f03403030400280090410902c5503540c0301d60341d6a4000480c0140b00c83c0020105843d002c03003c9c02d1040720b61850784c40e0408406141200d00a480d96156401581e13401e5a25000074014483e1041c41030000308002482014840340424103010749641068031005403c80d000311603044100465000020700040005140c0740c401c3d50b52540e4015030a44c00d12000040710810150b9100040213411004200022001d014500c403c54000344103e95610307010701d400e40546010310464000c1038a18074681100c1c4404594105c04c00d9041d030240c0f20810980d4200328003c00d4098140b41016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 367298687 1250 367297437 367297453
    0xe090a02040207050607030605062d070516060305090c09150607210e060a0e01030905030c0a0302060603100905100f020405060304060207050d0201020a090b03090a0515040b1506030f0702 82
    0x38656200412010380030348017800302807a2501d00901910259400f003401280c040000000084540031400d1083c000c440c60760203107155903140b2200038095a040581507015040e80081c405110074060001c0781c6281d2030a01050303032144881511500c0e1a4502504013a28800013a542102080b08680a150003008582409155203031916180c2c0c08084c1e40902c10f80b84400021815007100c0001c083c407804880a503d000841b80c001840c50020352102410306803541c1c04502082020b0058555802d008422104146c0b0f880c00c0c004c2d66840169522402400780d4001a503604007903000d407901c03040e0084010942842e07680d81c15802000924050080c1e41e90a100201d01596010001d43c0034074001c071005600d40721340c0e0500c03d041444189005040d0781c810820b59140c250000f81510845540c214126101d503900614242401184040105180207002e00805000e00c00c4000c0d500840c080d0803c0320682da40c48200c0310ba98070f15842c0d46036100806000003100c3c80800345020340d100d071851060314981 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 367299937 1250 367298687 367298689
    0x6030a0b01030302070806011e060302030601020a05190b0901050405150a020403051608060709080c0d02060706020307081f081207110909010c02010b01032003101e1503020705070e090a02 82
    0x4403001e810860040c0c201e60401c0025090030090326001d08851134064600400b08100940064924418842899004400213115a00a0010064503901310b000d46905c104022401c0c0340081c00b00030111030340c9007010003280c84031205201c0c039440b0700d911000800b00c4d040001040c84060b44001c011a002c10707020400400021000d000d001d0300d02e454080920f107c80d017080005030402400500702d00030000f00040070406101d0008541c9000e4005940184e0703c0041800421040d00c661900504418000024054207a5201614500c81c549124034448480000d05820384164454450740c0e2090703000340c2c400340c0c094069038018040d0600c5806040302c00030b540404900c41b01c1007103c2014041e5510030216003c29028092401002001d1804000b030300020340075442d1f4190390314a01c54075a40b021000411005089c4800e002400c1c05030f864072915071005080c141504424011020b00c10485560014032900a00a40e01c0141d4001c2c090072210b41443d8446284e04c000400c14102449240201d0000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 367301187 1250 367299937 367299953
    0x60b0a0b0a081605071205030a06030b1006030b01020f07050f041409010b010306080d081303031d0703020f2e031d0105011e0b0a0503061906050d050606160b06030a 72
    0x18288181d21400d0b160b10b0540061080c606800240106000301088014001210741403d814400e0141c10715540700c1c3c94041ca0311000b866260030003005081c0740300a0025000315056124210b40f0305035014000340e48071303000491f140c0c000704140700c3c0c00e58894903041c00710345420059603030f054034040d20001d94100d4403200600038007800da83c0e44240342d64840c00901c881d680344c09000040c1001d40300905550248280051604400500c2102940c41d0890300104051003600101012034054507441d2003401110307202500d074015844124841c0c80304000c02d901a02340b45009030800c46624150ba008007050304078610558103019403181c00c0580d50800451102150b056400c61003109000000d941d40c10305d02c00c91800390b03d0f842c0c00100b50070303180000c00174049002c04803040882589030150301c94546001059211074806c03140000455100702c08203141c0c1c0c0c403c02400d0810740c551024000c54031443c3c2400724511030082412041ca0780c81c184280441c1ca15034900e90002006811146914207036101c2d107603 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 367302437 1250 367301187 367301197
    0xb131704030305090a08120d0513060618060e0f0604020703020c060d0204051519050714030a050703021c120b0607150c0f0525030e0306070216081504060b0a0b 70
    0x451000f241c4a01c2ca42401707416007002c1c0c400701000300b01729503c40d50702882d203000780350078040007685841c001b540716122b0a442e00c8100c0e9000b80240038668413100c1d0f00c0c41802c038402c44001c1c06454074100007590150001040e0103140d240100c1205602d440c403c0c80041c1d0700c003041c01c0d03055214541c8001c0e09526600000c042208001d0001a200d60402c01085042c1c0040401c03280007260910010a181051190b5441030b4040741c104a55034080701d24044034401d20014002111340400304274000d4094015005144480c0719074280e0701c0c0c510403051070701d03d031030202c2480e0b030002030500d6964802c41e401c1d0f40c03240703903041002031400b401c04a05a17a00d01409052540b074100041d1251950303c560760300056004c15505079414901d050020408003030304000e44012104415596500703150301854001d1206295030200941510000d141206019649003444401c000501c8105000024003c1d0081001c00d54850019603d000a84850b00d0310400b920400c0d4440c0c1c0d200d1500c5a001994042c42c40040c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 367303687 1250 367302437 367302443
    0x303050a211a030a08090103020325020607080610201e07060905010801061715090a06030c060c08181504031103011401050315180714030f0304030b13170403 69
    0x400e001e1210b140c011060b002201d1450300944c010050040040c24170825240001d0080c078006885e9500c41011164852440184a20341200382070131110455010078040c0c0703e0b0065071101c4030561299401c9c4030441456000760380004401983d10412899003000c940f1004032050101c50700b01808a400e0814880712800d6007000d540404010441150020001002004242802c1039550300d4848060500c0026000e0700c218a41c0000c00210325007401c2500c2c0462000c042e000301d61718a0981111401808540030039a0342d2011039030005071680c03043c8840040d850740400301e541413201c080d0000ca81901035481c0c041d8080d81d0f454494001e50b0a600c007400c000e60090501104103240b26052600311149489981c9168989000500054900155060300070441a605190541c0c50350034000d0000b03590320b281c007003c0c098400d00180486441210151000044060b2400000b11851007a500d1045210040100c9241c00010303050701003000721464500c0c007403500b000340c503080c00300c07049580e42c0035410403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 367304937 1250 367303687 367303691
    0xf09040f0503132903010b041701090b0a0504020406141005030a0902030604150c0201090c1215020301171e0c0108040510021c0b0d08040522020a091e0303090303050a21 74
    0x150800c0e04040c08500c0c41c0c0c090131041c51941801c0c04900c0a1080e800f5a225400450100020300c4c40251700c90544550010180c2d8002e0620078181d8024190503139060b0302c900c2c1054004202c1901d041c10100b40c20320000c04448403280512000d881a820040800340303060ba4031024240541c40c2800a41d104912526901c4494055008003104440d41c401c100d5085a1500e140900024400010081a42c0c2d01d221500c1b8207144174900090540700c1c003440180c0703148c00480005118011802c20304003170302c801401ea5041510142c3c1c40144880964070f444019845090840300c030354090001c8641050050040c0c0313001c0050310b400d050036640142c0845020182d00e042100e0040d12610820341070200441c0c4a10354905682c4660101d800b47c0e015540c4078802c161100c0c900b0881c00d641600c0f08810a40055458241e00304001d80035401c648103026907040824901903000e0308402c2d14905580d41519030030b500b01d00307584049415402c60490300b0280203401948483d11840110030702ca0a030061100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 367306187 1250 367304937 367304969
    0x61b0a0503030c0a0909060e06132a020d0201110306041e02030c04030209070203030403020616180f0303090f0b0301060f031d250605190c020907020303060f0f09040f050313 76
    0x5c1c101c0405a0000550901d405400d0059001c80320550fa08030204607a80740d450303440c104c60900200600031120a041001600c184030103c94100e04120b1219036800b6500da0312a40203007642600c20185100300c609404100150003840c195001c005a48041c5c407001621701c4181a844080741d2055548485145000c502001145411403883c0e0344001c040c406913003541440d60b0042e646002c081c00394407840d145180f4000c6c140e4032070304140041460361003842d07505950300c0e00312400900b21400f050b000100c9807030010640b02c62804010080352405003030b5914581c6060f4080350a0410000d0076010940c880d04007107410072122075504502d061050103400c480c0380b4002c20841040d000380b401c0380c1030701012008018250b00070056465211083d245c410b12140d0341e001c110b800701c5008600075405040c98050000f440c1c1e0002c05103105140a51300107030142000410459281d4808103002d50040081000500151410481c05942d9104004a9040007050b0910415001d03540c0c22241075601c02c43c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 367307437 1250 367306187 367306207
    0x3050d090f170d030b01110d050409110c07060302070f0f050f0c01110d080c0f04060206010f0f031106070606030204110c2404020d03050d050c0309011406061b0a0503030c 75
    0x1c101c40200300b0b4000140078541d409a009841c0d0301e2921103401030640e5400c0d005403503402410300a98566a150a480d030461010b000500103070800d0090584035031508210b4061028000112011021040003d11030035140140880c065449a14221980701401c14440002202d218400342000d100340302030245402400d4000c1d01e4000c3d50300d000380c1042400c00500c0c00000b0045030100da06c401c1490000155502e00030360f5107007449080810f08070100300007030000f00140e0100742e15050760400e5026400ca5555a04000c0320340c10300c1c1c00b01920101c0c00500c1c40d41145400320051000c0c6214050200d42e096407500040c080b1100d5018008210780d0010b81d0551425041c451800100c0720b0040300e030151040705c060340040510040000f4000c16508880405043c0180151042064501001d100310724146030388101079001943c0f00a51503003043c002c1d944006501400e244110fa001d040f46092a25003141ca84480543d04c0485000d07004007089400824024401184100d09008e0702c2641d03460f88103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 367308687 1250 367307437 367307459
    0x190213090f0501050a09090303060e0c120c0903030a0302090f030f010b04060e04050604020d080d0f09020109050102030a0f141201031a090f07061409040905060402031c080c1303050d09 81
    0x14090207065890680113101313641d40d0f41c0c40c00055130380002001440d044507103019001030480d0b40002580180d0007040004100d110b000400b01c50580d201500d62580b210b1303098102c0c2d40207000019504d0f80081c458803440354404c0d8040e004440c0010452444000700310046410303c4818100c11880b03945370381441405042c01d005040c000c1c040c007480c035a86403505481c1d9944400c4080c000910541070400d201c1c0c00d1018510594482d0000d0650401c9244c440391002c41c0148503d000890210b58100c0001425600101c19204220880e85558041e801440c2040752918001e90360580e0400091010640304800c0612003806503100f010078007085004400c08541714180141030301d400f0781c403105056807020f00101d0705030100d500d0340c20040c641800c0360350292064001c041120390081d20b0103030011300b03018001070000e004600070344c03e803181c00d500b2460a6a0f0b40000c070305500045000c0c13102040908400c0001801001c2c1202404070102e51244e43c0d4500305060144508001707230a04d48103104040c108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 367309937 1250 367308687 367308701
    0xa0e1801050702030a0203120709030803010e04030215040b0f04080c010207060209040b04061d0c1e031806011a0304050312010803190201020306090a0f0b03071205070e1e19021309 79
    0x180011402d01c511740c00025640c5c4a81480034111044d4800450641c034014115040515071180015840c0c0d80c40780c0c40071014140c02c9800780c00601c0f0b044d01300040d0001620b90680103a8000e20001200d55440d20403001510300500102c4001c14100400d1552440038409402018812900560348121150401c801e542d01000011702c940d03d00302c410804158036610000f4407414000c5a410789a8bd4181403000c14090a05e11466042400504840381c0004100442c4903084c1090940316540315000303419039518090040300144002086103103454607441c405554402d00c190100d0317150100c056115441824281d000b40348903407006c00c0c210909079031803505680f5170034a480214158038144c00050f0ba40c90010781407158a9a0754480d0020380f000603000520380a0b00035040310100e60359140a240411a640d1080d5100e0041c100040b034442c401031002c44c015001c0c2d84142c02812240c110405d0060f0010380717030403104a410490407030566401c0c00982000040c0600d847c7c0c21034070f0210318005036410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 367311187 1250 367309937 367309951
    0x1f09090b0306010e0711210703030f11030705090d0f0c0515180d020d06090308070e040b091b0705190b15030703031d03120c07050a080604020402090a0e180105 70
    0x6000511411135619891584441d4602d040345a100c40007a40754100211004414a0900000e01144c0c2030060030004041044c40b942e01000743c00500b5203600304588403240e40501e4000104003141e0b5040c814170140417940c10040c2900d10328005540c0d60101d004010341c04483c1800e200e44101b00323501c0d140c000c002001c0f140c169003500d410291081c0c00300301c503a400c590070703c10204c9032070b44025515580000981c0c2940300e002081404114240581024001c41e40c0d00001071060000c10581c5c10b19014840f1041005003e14201d07032941019040003950140d035136505101c0902034803000c00d004000d852404c48072007009141000700e5003400624908028a401c0100003010f100400980300018803400300e13030305446c0c100441500b4100d6081142041805282d041c810030403812803102c003440003844d84000c40001c0b6040e06a0b41e03411300050100d203211780700c800d8201c00e0010b805401d180d002460f10301c0307008002880040d22103200705103118090f541003401d0f40306081d58030741e0341d4000d2241d16040380d9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 367312437 1250 367311187 367311193
    0x905010e0c0f030f1009020c0c040501120209040f1e240225021f0305061c080d0e010f062304060f031b05090103050f0d0c02130203061f09090b03 64
    0x110020b0004114400a401460403000ba0710006006481c0c0038041d1010b01a000001d40d6030380c2810507000e98411240c0d0341c1e14440c40c601000015011a6040d40d541d03d00e80c080d00240e07c0d65251b40750304110b140000c0c0140c03166040760403844900ca900030542d0441c070703120f101045040034040101e4655011011065204c583c03040110b0f40130484041d18100144040300480f0b242c42401e80b012510364001da844002d0b043c10303041c42003c00590140c0159124140c00e4a44c2c005010000c8600080b0702000c040c094a000c2c070800208120050a80040c0d5106280f40004180000d88401c420111078644e4401540d10740e4180c0d081c04805e15060101180c200c00b200c040c841c0c41e080c10303401d28458800d03100007040e034070314510f08518208140d01100000d1000400207882584d480c200b407902c985045000440e80d00515240980b09405000c1c4800410703000340450200303456480a200080d40040e10701d540c0211004a45404810211009801c940300c6d583e0b940f03c11464030b40f09100740d46084a100f40309070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 367313687 1250 367312437 367312447
    0x40209030d05070606060c08120403030b030f010b0102060a0912081e0118150308090d020a031e020117010803030106030908090306101703161118040501020415051602060a020c0a0905010e0c 83
    0x60b854425905403500a001545042e0ac03186010b400a015004481c1d03018042c140c040400b8203010750120104160a8003614007a0360f81840e098100d07080c03078100800f03c003500d400b0054400d01c07074840d07032787d002014100300c0d1240c042c0b110782400c1c808806d80c0104c200d0029020040803200c00ca005080c810101180180d065904595407414603024880381030740281c000344030103c10340d40d911507110001d5400c44070103101c01030003014045d40e068881c02e01343d01203a1845418070440c052590110704030b50b414400741d4110303402d000f4102d01510400f4001d8036651024840c8240940e410710501d4061400800c1c2d40800ba0b02d0f0801114511940d0320030600036410600506840c403000e402505e000607449190400f0b42c520000029004414403c5c55100c03112014081204100055004209841c0c000035441c071030010883c402c9602d03109000c0101c0b504848000b01000504100d005003000b00840e0041d80e07103007102d14000c10702031921540410251500c41e00104040700ba40300d8003e410a403803209844c43d02c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 367314937 1250 367313687 367313693
    0x130b070b0a02160c0b0c0c030a0c0302130f02120a111206040e0313060309110904051504050304052713030c080c030d291f030b040209030d05070606060c 67
    0x8503001001c0c008200d0b000a002d60901090080030310b0703a07036442108076000c0c036102c0440000513000300090000d01d100d007940001c2c882c03030001000099540d04c030b9401c161907030441d400d101501c4a459030350001c0d9520303820007401e20800d60001d409003182c899404101c514194003000c007a92448540368038002c40421482d2f517981541c050180e840101554017250402c8405509807440c0b11b4a10f900c01043c01c1c030398000c82e1050703140e086804031034018007812502c101c401c0100304403442e040e58010015445600340c1e00c080030300607407400e0703229000340d05030380c1410303920801300d100d035a00c80000c103064424004d0f07881c0415610a032110380040c80314040389040d01195801900551411101030290380b00402d2203204114200111405404142c0f42031095100e00c11862040e81100068856841214541c240303090400c1c0d00e03c2d508907070b00110401e6107484101c105400518a4941058100c6d400b04290b920948040152540401c078a030398540d40c0b0030440c01d01208899054001204203c01501e0360808 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 367316187 1250 367314937 367314953
    0x806150109082a1009090f1a010f121104090e07151b120905040b040c0f0309020301060806070206010f1a040b0a02010b0a0b030a0f1107030804031b08130b07 69
    0x150f000c1e8000300720700810b6900208007560440306816501c0818800301c000e805a026180700708840c1c2c01c43c01030092009a2816000707503088814804a801c0120751060100d40c441c03d21101c2802203400d040000c149580544010b45103411001e0190240004082000b4106480b40015004150010704061030030f08464081d600540003070b5400b000a42090918904190f0b680708155980c00100c1440d1558408006072078030f086441030034482c501e484401040b504041c0198440121580c1d50000d41c036003203403000d400030a0400000c3c0d80540d40c43c58003240c01e140805c88240030b101142c00412466245c03d41545d001d49050300089010004105040a0156680141c400361503151400e00d440316036010040303005128030310500e68080a1030b5000100c41e42c100c0c1c0158001d8140c00c5080c041c0c00080c0940390150703400c0001d440320307000f4104180d00102e88185401c0307030001d10921b4526100041c030001004c502a000c08150395500f4005001142800036010100003081503102150515140e900d940781 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 367317437 1250 367316187 367316203
    0x1e0d0b0c03090d02010920060d06180c030516050c030405060408010225080304200d032a0b060f010c0b0f060a0636050a06080916050d03050a0e0406080615010908 71
    0x103840c0035110b482d8807e6940c51080e07031140b1401c1c07032027000019510018001d05050b10f030307150f100d01807802c2030440540b8800e0082a1160300e5000301c3c0b101c03400044400316030702d0380030401c1001180001e02002c1001c0d40c03400300410003400e0100001d44c0b141c10100201d1010981f500b41c0d003c1c1d5045190350800003600c10400e6036400758000301002c1c030021682e51300c120300c8040000311075440108121083e04264200c42040141c41e03082d0f003611490440382421400d03c4581d45400381100c0900c2c00000c000c0c0c40d00c02d543e00f511000602d0724842e41c441c03558580101c0784090b11810f401e00008801c10013142090701c10100107020b149882007907030070610000449107402c4244c400c0300000d02d0564062003070049208400511b009002c42091035512400106030540940741c52005005580c0c2401c0e044110354510415514014505406040955002e4815502890f090018005000510402c80c0d82c1ca101d40c0006040d1000030303002c2d44c030342166007040302d40c04880e80d00c0c10710403c1072051212000014400d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 367318687 1250 367317437 367317473
    0x60b070213050709051f090803041208090607061107051204052803050f030a0201050c0310051e04050a020901030c11061b0f0301030501060e090c1e0d0b0c03090d020109 74
    0x10b410b80728401c0803605016a0342040340c103c03007460740703c03001003100200314500c840c141d507a103078200c540b6000c41645a102d54424918504400c0740c422010032682d0f0010f200b00580103002600d0000c06584100070750b800002045121400881d5840074044288480100300c000072480e2071a1a040c1000507941600b00d0b1240c0b40e43c4680d0004200503907640c158071030301468001003201d0101c09000d298917a030383c4c08004807030019401c10000c03400c07882000c8160b0380902118801c4656080c10507080c40003803a510b1212201d20b0f9018136070041c1a4440f403051501510440c54050380c2e5054840015040d10400a040810171011028a000d4044003148a9811200003081200800d010540c19200780c0221170a0340d401d824004000810400305504c071504661009150f0720b01075844909041d25010005902034200ca03d40810502292540c0102c1c515540000c1800a4890745502c40d0f040c143c0c001c41e52032921300d200000303210000400304501100000184000d214100c0c0681d942c2c403030030000700644 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 367319937 1250 367318687 367318691
    0xb0c0c071505071712040b1009050405030702041e1509050c090d11010302070501020c0102030901051b120703110a0f09090b03071701090219051003020a1b08040f0e010306060b070213 80
    0x4030301608980e002c95540403c418405d0b10a07003401d0400d502505c00c01d4503d041409110040050640d050307014180c03080307800501443c103180883c0c081c840900700004603240303584420100244907070240e105910007504045010100542080e20200455101030490031400c08103001010300b030341e0f4082e00303010202da128411807142c0c042d410069010f4003c80030010420350002c21521f2888205501442c8541d9000700240701c5038449208880d02e0103101000051603020404c203452945280f40d405940006440c0342c0021443c950010058150b040502d03107500007a00f0141c40594641e0007031403c8094000c0d110204201c3d409400007070b65a01441c403800784992400305402c40400380a500c20039059801401031014000002c88290b55007445005051244405c0c40c1d400404a02c81e20941e4042d908a40b1a119010b8012084004009210310f048030154010403010a4003c0031358682c400400c50140140403179415842e20100340d032030360f800c19070103020305010348009030fa50407003500c1c0d4440141d840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 367321187 1250 367319937 367319963
    0x5072c0102190807020f0405091209030c1201020c2109010e04110f1207081320030f0c0f03160b1c0c0f0e0f22090b0c0c07150507 57
    0x50781401891aa20b8128100410500342440850002001e03240c1c0300700c0c2d0640c104e48040381080100c0c2d0f01610100000d501ca005142da401003440010180031000030100e8480000c080d000482e90386c81e0a28840c0f035a500410710311072001d020410391101c038241100140017650207449501217405800f5032541006014039200d900c43d00e481d40907288007003400c000c1503901e08400421204a520580388440000f84440004c0c4c0386505c038042040c06481402102c081c40101074880584402591005480c0dda5510a044800742d07404c0183e80c40e892610070207480d9001003031003082000e02e8411000741c080d400c441e0003000c100c0c1540303902d5425112a00d0711162201c0441071024419801d580c1d010704614a85514812440d400c540642d050141e140d031454034051452050012082c15401516048031001605a1003204204905c03100c0e0b001c0e505001403000d8080d00c0d8081c01000c1964008562000000d0400f07004101b40840c202902000300781c0b143c416100c4a00030058455200090500000108 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 367322437 1250 367321187 367321189
    0x5070206041721070c1a0103081615140108301c0e161d0712150e0702160b04090908040504050a0c180605030a0209030109021c0605072c 60
    0x80f00f250558a2000040002d1620010240030400d14510564520a255080710520b03002082c6441c1600c1d4400662410105110000300440640801c207d80000022540d00444440740c07103403184000c5001050095549030030b030b010341060364907401c002041c016001100c0b00040040241c410191008180540e18094401108000381c490f1a91400c4c860034020910203000c0005400380e226613240c5188100310799103ca04485c054116540d450102e08441c0000b0542800307920f2584c0b0544c01442d01044401a1400003141d041c01900100c5241c02034109011105034104104804200e50214456a180c1042d007c00094022071242038181502d0b40d25801c100410b4100340c4008200140c4280a141840038211010313001480d801c82c00034880c104d12002034050150600704590341500c40b02d28684801e0b09840195005000d165010341d241d20031240161900b14850074184400010b6411030700c813600d00b09080e191301030500e00c00c20400c1404d074003140c158515981426441040c0013882154600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 367323687 1250 367322437 367322467
    0x70801180c1e0201060e0f090c0418030305040624090b03060402031b0105070b0a020d1505010c0b1b0307050c010b0103050f070c060905070803090310110403080c07120312050702060417 81
    0x508580d244400c48411f01c00c2150013150918005e00141e070030b48031119000710921088480030403542191120740000e1a022074021b501458000380580004100d510140342ca000040001010480c51042d84000810600f4081c0c850041c051108a0141495007090b400080d5101d0300c40700040300d14041010340e01544d80c0507900700e070300c41d55102d20001e19500e807100c80e11000303411844010107800e00f4040d10300905d500d40c0704140142c6030140c540c881d100100c0d4030350241140006003000714500800300c20088501135040614814503641c0c1d03038666260340343e03d211429034050a01c1e05040c9402d080900003181000a40780d0380c040540d24003120b80c5400e50509401030001c0c03000280590003040000320300c1c1d107008802807400c030300d090b01141d004120300c8040350200c0d143d000000941003010702081c400507448000400000c005002108d202c143c50b00f810001001d224081100824420040350b101c1004601840354071100074005442640b40c1070b1298404c1c0304c078540d281c07029410001075610076280740d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 367324937 1250 367323687 367323689
    0xa05151305190806060102070e1611100b100305040b040605040f0213150506190f050705030c150901051e19050f07080c0a0c1101090905070801180c1e020106 69
    0x1c050b00c0307040c0b155411584240e01203010f800018054240012419400060038100303c50710200d038038035581c2c1c1e0501d84074000e807600c0000400708a510807610703c0c0080e0400c4207000d801c03080000080d40c030000404001c4249115120304040c5400c000401010614248505034002d0300072002090655462500030131866040000941c0041c1514034444440202e0f841100c1c0304d000c82c080402107a84400400100c0c0c0100b10300500304201100030340c80c003a40700d420061204601420700505281c05562174a040d03400c020b146840725413014400c0c541c0000162025508071940d40020030190070104404d42d1581e0790805035103048214800072402c41e03e07030540700b10042c021503030040056061800751042c10360010b580744400611044041407a010940701124071038180c070345071a0046c91803541c91141822070410b01d81e0500c8005040098080b0f21801510300c10300407561610501c4d030415503549011171010000c0c01d4000e00d804e1003403158980241e0f80d0301c8088920705903089002c0d50381d035089014150b6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 367326187 1250 367324937 367324939
    0x170d05060111030d020f1614100908070f08090d06020d05070e0105070314090303040909021e0307170a0c14280b2d07030f080421020f0f070e060a05151305 68
    0x421404401030103500054840b4031074404c02540c1047c0840355489e4240c03040d5101c00b401c9501d04001d0f00c0c0c00100c039065550203051142040c0f9060101e40700c0010b5a0a03040070082e68255000078520714109003c1c8a0160300801c42d05242c00149800c1000804500030480700400740821210f00340c180d0424801070b43c0e17031000300030101c981d1591204100c41c080e0904080c12405409940711310042048000908200c4200140041c92103602e4481c480701c407481e41900030b4086000d034070a488041082010f6120161014103070b1000c408880708240041a114803140011310682280050140300101001c10104c440f2260070b01d480b03200701d5125586482401c40c1d510070141c10384441c091969500805440c405000351189410801d20f84810703684038800321030040c40b808000b0000340b040c0704580459400300029104848162006040d401c2c43c100044080c01c085500429080100250402d0443c1c0e1040054030340d01e084034900780c042101060300014221100002041220a070402030042d20011b0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 367327437 1250 367326187 367326217
    0x8040b061504080304061b0b060904060e0703030c031e0206130303062103080f01030b0103060f090507060917121b030d0207030e0405010501030e0604140a170d05060111030d020f 78
    0x1d9204503080d82c1e588640b03c5d03c404151b101030390303140c1d80b05000705147e42140c2200740b0743c4941e03460108001c40c1200041045550965442c40e0b110300040801c8140060340c0710b6100c0c3d40d00036041d810701402940c400002021141c80003442840c0042d804111180c12002220080d08a01d00610b000d030058545074214800980c0d041850015000c21000380c0c0038600c4c003a0300c0303811190301c0d031b5903040700d040d5004d000241551010318010070000301d0a500c101b80410f00c03c44000344020465440c1800c000c01c65007c18001228030605010380d109120300030049100000040400801000c4180300c503009944400d0241e200400070f4100789001802244d1000d4820b0508550b01c81c0e6501d1701804140500c40d04500851400e4008107855000340325000c502c43e075060091220341e03a540c0d6011101131281d90100041d0065801c00c1e4001030f203694250701e03614040140c040d1604500c40d081011940001c1010341004250070f5040362002c2c02000311035008211a10141e0f035820403c0c4001900d22941003601c3c1a10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 367328687 1250 367327437 367327439
    0x20418050f030301050f0a08060402010518060703020f1216150e030f0310090c022a0409061b03050c120403140301030302010e0f030301050604180902060a020f060907030308040b061504 81
    0x70328007200540c103840040310141205034201040c0407010b600c60241500710b601940100b4050760080c40642107060700d071170341044031289210201d074040d0040c1004402580c0481196540c141e401d01090211940b80b22120341081070b101c1070a264081d584502525402c84d03845a4004c0d101c040d0042507005420302c080720707038a03003010318400020f9001312001000066a6000480c0760021406101c1c06c1051356401020b5290700445034102c014030b41c0b002104407550214455280e0307251130045203141406004001800d24482c00058140c030b881d02406001c05240c5002c00020f80b07442c00580d40c0b80c0c030880000256665861405460364a074106542d04c0c69900070000104055054000794980021030084d00c040e50606660705035a400280507083d8040e1041c0024442c4a0800c0c081a031404a16540464210040c0c0c01040144d0300c035a03e90b4006801c98005d0204055080083e41c1c0c100b91401c00030300c00e0510710349008000c050b003d400240032a03807140c00b0030a00d50f9030040c1c0b248001d041d181d13900d5a407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 367329937 1250 367328687 367328713
    0x4051302121e0702161401170106030903120504080714070302030a0809010f0207060504060311190512010b03160507060e060c0c0f0304180509070b040801020d0b120a02041805 77
    0x1169a100b100c0c460b07541510000707840b14804252411100b90099458a200d402c08440d0345195000304c02290410184065401c103410352090a42d0083c8441d0320002040011400c000700441e01c0c07112010840b0b801c1005010001c1c20900440d5049900304001203d00c9984158483c107081035544060f500d441209401e1b0107101c03080004280c100400d881e560318a400941069880707848034801d6a000c5030081c44104041c6019401c0540ad004911044901c0c10f441c13101c1d4220240c0c1c800e54090001a00442c00701c44051082c0011805496858a00d03400c1d03251580200c54481c2c2400614030400401080c0002040200e40000000300e10f03403000c3d9003141c5004c4454542c0d54005c001c509801d88504076a402d609074010003214181c80b048021101410784446101010f04805001c0341e0aa20808000240c80d4507580301500140c103443c4000744c1c0e91040409480196000500224801d01d02456048001c0d00000350300c0048070341c150b030080b035994081401c600b2401710200001d04076008141001c0c1030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 367331187 1250 367329937 367329961
    0xe100906180b01031404120c1e030e0109080c130e1506130902010c06090512040306020a031118040f0605030102120a1505010203030a0e0721150b03030405130212 71
    0x4510322101c0100301c003003410001181650b000f0041796110b0184d010216000c11004525400201560f0170140a8880e090340c1c2c4100070305030301c0003040e1500b0b11440c00004169100400c40480082442d090707010710308058510707841d0000f000845105003102078210170642d085400034488079105a0907074004c800500240c0f400700d0340803034080d0301c260b58803080407843c21410b10508020a03010b9541b00805580307555104024220f100d42603500388164001484645507000080c0b000d140703c1e100c0503849513020007011b070907030300201d50030030301510309000200306413405280d4150010740841340420100c0c003c0a01c5c07001001160803241c2c042d400000c09008203032400801600403200d40804100c04680b061101d8070395801400f4460050300100040303006040d054102c08508243d0a042d40c180326620250001d46400d042444400108520720a40a01c5506216441c1da5160100c050001035048400251244214010b0522a4555140c85020f002c12035060718041c038052058442581007254035004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 367332437 1250 367331187 367331219
    0x8370804020108010522050402030a0b010b04060206070e060906090d12050714030a0827060a051f030819020a0209040b0105131103070818010f02310e100906 69
    0x10100f45081c0002466042014032509800411050f201d00320b0300c1c801512010b0711000d441a80d0600c903503007400c40414540b803d0070380200410341000342d9940c58108040e040c0080200200e043c003640c19034140c06a11010100c842c0503a080b1903495503400030000181c0422451100944042203c0c88981119a0080c0043c45a14081e04045d03c071540ca4041041c0d0700e200d42a034800000780c60f02d02007210090001e80c00440780111503d2100800301240700b045c640740045412840d91510740341842100341c1c601c1401100d40c2d60361211007100500f140c80724203062064020341404401100c240301c088510900a40b403940d039004050040e242170500307001000c100d00303001d168071a04120036901e200000503c10121401134402030350f41181c0c0c0340c50301a2840c034001030a05500301071032008000c0108080c440c1c589528100440142c5070079080e900070540201e00d0390110380c58150ba0030000c00c042c50070b035a4001110810092080d0980d52504401c9002c2165032190340014144a0042864004090800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 367333687 1250 367332437 367332439
    0x207060c0e0102100b061b0f012a020c030d05340605060603040309090903051909031707021e041803022a0d0308060f06040e06090a0204030837080402 66
    0x2442e81e683d00604402240d008182c000d600c44da00308580d086e503e07d8a00001e401c5100d810560b42d0421117059001d0950302582c907181c06203485440f5550b0015180c0c03004410600b62440142003007c15070000c681c0d9042c00c1c250b10f1081c401c020505c040114030305020b06000309036126082d004051803485154501c0900041115040d091100017040c504142c000d481c45180c00d50381d4454102c1c0f800c00003000802401a080d810408100300c010120084880800c4180e0340c1d40d42c0f40c9051510718144419444651342070514140b41c1040008096a202000300407525010130401840d42ea000d8000703001031419072401d0b480071494040c40414140c010406034492240448458081804c0407030403c1c81c108405c0240743d0080f40b801008022a00c6403650640c4488050056101842e000001441e690001d51100390003003807941c100082c500b060312505030401c50300d010646c1403500350f07a180c0c94540078402c40c4402105061210700703101d08201142102c40e0860070100252240703040c00c014907140d0112420b07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 367334937 1250 367333687 367333693
    0x60906120d08241509010c06020301140901050901080a0209060d020a0e07120b0a1e1e08070b0c0a120207030b0a020d05060d0b071805040203010905010305101a130207060c0e0102 78
    0x1802c404043d20001c5a0400801e5040715503c0d284080085070080d01c4158100880303003448074000391152008501078810718081c034a041184000304054044160061409152030400412030032900040305200c40d40c1c1202c41416a42d25000403640c04c030012003000e940555043c2d00041c280b440c0b1a2540d0107400681d9030301101d50300c40d413601c01c141e440710a03c86030480b1180f24108410f00018040403d07000180075032f0683c9070303601d107100304407080d40b00c2c1e062120240c480c904100340c000800116008089410000b403c0c080030410460f143c004049010300880301e401414000c107031090100030003445c0d00c13154100c40307410000c6141c0000d4101d01d0780c0885140c50701000c5140d41c60004440001c40d03900c0910400b03113a40324002164a20001035003105040d01c00500440c1c1075540c0c5c006113020f40550200043e180d0300d5400d00b02d14024031086803840c001d00c1c18007203126441e0391b0010100c40884c00e5800b049881d441607a501d000f4031a089010f00750364580f2014031300c21548103080d030b02412002d03821 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 367336187 1250 367334937 367334971
    0x1d060a09052b090f06050d022b0e010b1503010509070519020307061103040c14040f0207050d02010c21020a141603081006090905090a0f05010230060906120d08 70
    0x15440386113205d0280030080b582c1030100910b0220150002c0401158260b1009191a00c0303d0001c07101a005c11200b8403240c0c0c9031007401340548805d12556030300040440350400341888420030780c0200e00c418015940220b44a400042d4042d02030801ca80c01d00b00c2482111241c41c4041a009440b81c000000844600341854000600c1440303100599015a4201407860510340c54490a1880d40a1280381680c10940300d00404080e42180d1000d443c5840c0140068071000000210007401c484ea42071303c2e079003842041c03000310f40351a2025115440c01c0c0f81d140070050f40c0701c00e450401d460413140001ea8a25451002540350042c21020714103403d414400d0301c40e0201520741d000c12440c07502c0d150003000c0000304801010070607200c1c0c0d82c02c59034101414005441d2030740d4442e100c52030f00d801150710039070b0240e40000d511084c003900320309074490003c0d8054070308415010a40031104481c01c0500b94621580302500031400568800220700e1402d200740c4111040142d040d4006091008211449090b501c00e20b01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 367337437 1250 367336187 367336199
    0xd0606030c0203030f0621011401050102071214030405041d0d0201020c030d051015110d030b0906012105072001091a04030908030313061d060a09052b09 67
    0x404107001c0c03032070b006581180d0700c1e0303101d079074070300000034022503009010048052114038000040e00210785064000300b0007840d084201c041041d4103034440e0b41150f00c08101045006001c6003080f1289601c08940c401c9103040691a52450040340c00c0f85610601c2d10b01c4081000009800c1d88520041c040182c0b207407119002c40913801c178080c180e61812940c2080007035002c41e09071070784000c3e4030100c0090005d569540b51904600314440c0c545044020408007500c160050f1001c000d8100d0300621441d0910129042002003100940050182030500c0040e5500c8000d040d000e40001080c1d0360841400c000d1454000c0d001000c845620420f41c0402441c801c11803500c2c0018020840d903940c01010380310062072841041919004000c1041e000c128459202040e01d9005000031401240c00720151070004d2540c0c20913400715290001455040b80d0380c084090010ba0002c1030a5500c41c0c8006400a8900ca0504080e03040010001e85031058802c01000082c0c600c20701d100d0000c005005036242c0d425181ca900c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 367338687 1250 367337437 367337441
    0xd02031008150c041a0f180a12020102070b1b010f0209010e040506091302060d050901090309080a0b0a15050a080a03030b060703050313020f09040b18010b010903150b13020d060603 79
    0xd540b03c03008400030081400126000c41242e1407020304040349614101c0d42108030182a000400300b8980d000085901c40c07010b02d00510040060224041040c10003440d42d40081e5848900d48035004500c0001704100c42c0301e0745aa07074420f101d200c255000340301580c040b0100320029405a0166404140e039006a0350b02070402d4424144100d42c0982821403545030210840041032100d00200c0c0d00ca01c00b00469140d1380310500946005a43e50000825440e10910700641040d01d29003005010ba0301c441c9010300400c4d00380741503541210b085040024014980c00820012840f039402c8aa0004070307810000880d8000050528401c82c0a542c00300215498a02048030a00c0f41c210040d00041c41440880c044d8022940307600c003e41d200a1039403242100c00740205601c000222802c2d1040c527030300d408000e1480c18401c0418007142e4080000c100300c800302000a01080e203a4000038040c400421420803080c08107500c50506020000c0c20700c0c4001080100c003101a5000b4520300303800ca410300c00c001404d00d00038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 367339937 1250 367338687 367338691
    0x606020f030a020a0b04020d081b060105040203152101091a07090605030a0c09120b0f0609100b03060a0b040e0a0c0219020f03100c0c0201090e01140d06020d0203100815 74
    0x295000e0035240407117490300380d1421301c0500182da0018100588100060502d40202030004400d0004482d105c2c0c01e03480d00707040c000141d1045014500410400c104082d0b1103024072700c09901240c42c0d10751008908000b65034518410107544466207048080014407005100064100e500d00d4484038041d500c0d52022900500c242c41003501060082c804501d0211154201d003c00342c0e140d18003008445e5803002c0c41d000000f1201c02c1501d04a0040b82403052000320000c000742d1001c030130b5454441c01d0a18807100710300d0104a114042d60b1400100c045501552050140d000403e02a03034002d03100c640340c4080800018064910f405407e10700261340404038008a210040704006c01d4121609041c03d80078401095481030010394180a21043c28401407024030803200a802c1c95503800c0380030b903080d00c009000e03130403140c1240b018107410b500100951240004000c680300b4054502e044400118504040030780151a00c4010081c000b20800c08600e038400f90300011640c4001c100c8a0b0312081d9554034041e4842 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 367341187 1250 367339937 367339957
    0x90c0a050307061e020a020a060804030815090106111203070f11010911010f0309050a030906090b0c0319090f120303050c130b0c0a05070e15100e0d03210606020f03 72
    0x40701c2408101c0490780c00c44130a070328010b0041e90314094055000445241b01c5030000c2010031040c0b000c0c40b0625500500359940001207428880c0c1507494440040c185e0801413141c24104103d141d400c940140007800001e166010160245890342414400074101c080b1502d1610009107101c00c000303a4181050040f2000036030009980070740820041c00454503c028442c4d46801d1503110503410001a0040001c510b080e40259112900346060034401820f4280350b9110340c00200c0d007400b11040148006c42100c1d482c000400d0050306e0503034005002d0b0381c0c040700d42e4003002d50345000000025100c0300d092840e150070740c440c0c1e404010550303c050a0680600a0b00d01c10100380e41150018084003a002e0700901c40b540142c030889003121400c0d0754540c50282c840c1c04c00c05c00c2c1410071092049101c4540341c0c0441c0030004486407000311a44103002010001400d160621854444440314181030103007074101c480440c5890f180c07040c00011103415002d8040351040724014844d111070f0140481001c01031f1a20121 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 367342437 1250 367341187 367341197
    0x6020c03090306090a110d0c0503100b03010506060c07120c08070f06021612020d15020406210b0310090c030206030103050102071a01060e0d05010e06190c030b0105030a0504060b0405090c0a05030706 87
    0x141901f889104c001074042103500ca81441e40114240c0e1b4100a00aa161149030000c9103140036030050509503040a45003601405082c08003c07281000801e510741507a554000260042240303082030391404895034402c0605000788000410b01004c00241502902e026400f01e030320300307030042d000d9011900c25881660b1b00b18401c07640c1500189002c040c0c10a00318011040c401c000300507400b841040b60710981c031074400f2130100015600140a503d0520b94200d0184400700281600100440e480712001441c0446141d6102e418808104010082d60003440c2c01400860702c03980c483c41d106000354003641c02034407200400e1050404070500400254161031080d900c4203000d01d0b1820030b208210707642d40821500c2d5500c444000718481001c00045114610000c0400301d070014000e01c040c1220480341c0424105824042d85803090391b0044200c03038002c4144000010b540d5a41c0c14840004e02004d012540d02600345018041c07c1d910014220110343c800701d40c2c0031a01e690751002c0568031070703985c4941c0012070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 367343687 1250 367342437 367342463
    0x801050a060807031d0703140d08010b03071106040c090b030a120c030905120a031808030a1b060507050301081203090606010c05070f03120e061c0f0906020c03090306090a 75
    0x140301c1d00042ea0004003034180414815562540c500381211520080003050b80f02010030028003000700d0f1440c2e098111103002c0c08400c00c5603500100140c00501490100c0c100000200e0542e510a8156128062400b82030300c060f0300340352401543d4003207940701c1e0364200c40c2001e070499103514010414021442c0c0c800211011721164400956038500c0e002800c0d41842004500018141c40700000c90800d0b8100c58041c00d05403d4a20780a41101e448250f440302c031802441003072020b18000001c48801c0e08550601c8601004000e00041c2c5412840000528240c18601030100b42034000c000f45041c3c0b0300703200584000400348061012103000803140c40b80d203035000d40045001c0354014018082d049005a0980c2c00158480c500b24150440c540d0040b5100c5851031107041443d90300499400030741ca41120360f075103803003022003509a0038034006002c8020f05a0314010840c0c03141c1c041d440403004d07683c880811743d2a01210010300d0f88035044002c0301030282c061040001e200000c0071849074a029800b50040b0108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 367344937 1250 367343687 367343699
    0x9080a110901061d130204050a0306022101030b06010c06020706020d06260a0f1719120902030606041d070f050a05221104030b0a0507021e070611070f23010801050a 72
    0x70782d441c0c511120011b80c204070205a5803281184c40b405180036000250703849450322082200c844402181048640b6544011f00024545c1090b1b15004003092800d10250160b80c10300358000e00c99110020900f510000d5409164042c0c0d0308400100c1d5000090407601c08046c0e05505544050100828003d40156140394001810301014200c1103008102030505000c542c4081c070303030f00d40c01040140d4012000d26619643d060307104020100b034054011040c0411002070340483d5031890040d0800b2320a64403158005a9a4201c0031100281d21400c0d04940f040c0c0d07500c503008101403149006041c060301c40241c0120345030400e4000000401c8140003648002d595a203802d40c0101143d00e003e40c3c03845000c101c0000401e24642106015200941c000030301b030304100b80041c1c0307403c10b40c034000c10b0022201c140309114013101060f09411036149081074501c107441c181d00741b42041116004a02c1c1c1080e4540003045504d45c1c9004403547c003240194991802084400545002001f4420030340c0c08500c6020900007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 367346187 1250 367344937 367344949
    0x50a0b0a080d121139010b06040603090311070b042c130c0308131e03030f0f0207050603040b0f0901200d02070c18060605030402060a0f09080a110901061d 68
    0x103501100f1160304085000a1806813041e100c5145e07045c09000c0d003044121040c0c2100d202c260980300000801000c515800822104d004600c5000c0a00d9500e08004c07081c1801840700c44070103407410090740c4100d07840390b10002594001d070094415100920703950303803038031036850540020b600d1011030811810b586050b010541d40e0070320b4208640006101200200051250010301030241002e02d4404031036090160590004842c01c50710780071910b6072801000400d40181003220b1800c824540a00c1c8101514401c2e4030b000d11a92000d40c200350000308000500121240d0680a0700303a1091403003403a1a2107940c14240d9441100001d04507100c00340740482496a0300040400071461100907040031490f49502e1803a411940c440801481103104884c3d11034220702c07400d00030f04683d04040713085003416000b10b1000c1c01419100d0090091b051004402c480c054a0610020300ea14000c4079403182180c078062801c41e502150301801241c0800002c185627000350b40c3c10410b4203003156041c80d4041000e00f0015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 367347437 1250 367346187 367346201
    0x1030902090f191404060e0c01090b0c010618090210020f0c010f030f0218031c090905040606080a030f0206180303041722141804060e010f050a0b0a080d12 68
    0x2103403c20725102604001c483d0f00442025408072000790340707203152604107007040d0364003948100381e00d400266103101103a030403915241c196001c4416840c0c0b50409a03555038010030303443d0000492010051045020001c40c2c0d00094540c0f4425030740d01450100903c4166615044072030400031903081700c0c80741400c03544560800d0a20701030078a400b140c24003000b20b565049920100c0310099400c940343c0d08403000d00303040080500011039424190309490400500900301401d170700800017103e4445011500b4060300750400405001c415054030300300f0891346406420000881c0740ca202502840c3e0004241c1e8911280c0340f0603403170640001d1480d5517141d0b51070107100601d1340b00c00c00101e101407080c500c041c084c1e011003054050003050300301d014504014180902402c0003404d0f501c2211800320501569007140d840f02d03007096004c900450360362040e81000c1d0144c08040c0303070f01003200d16001c01c1190010700d070380000810399000c4d5031141d031b21a1074108164a0303040200c03c101c049848000c1c4200864800d9104035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 367348687 1250 367347437 367347451
    0x50d120f02030d05190c050a0f0302160c0e1009090807080a0c0b07020d390602040914061311090f0102030d05010602070e0a06060c110d020901030b011401030902090f 73
    0x10349809070150f4000100c070380695090b100c070441c44207848090040c41c42050704641403418400c5c01c1420404006200c0319050255008143c1c002c43c56501f0540c1c0b403068540c00700e40c82000103103019101c02000b003500c030007115001e0031040040d5002032414118810040c4280d00000e680d850104c1a403200141c130350103e4160010002001d01100c0450502031710107003e1900380d4007034081f501d6032290052100ca002017041c0410000b4070200074910800c0000c520080b45128140204952a400d204000340515400000401e050141d6030b00355000d500b508500c82c96003295a08440184042030100f00d4214101342c00038645d00300030f07401c0246801244010b0341181403049034980760f25075045c0c0d0144c50080c0e200401507800800203001c00e102071403400ba404078084004002c0b039454120001c4c08100c5080c400b5250318841007100509484a100c041c60f010340280441f045940c0d00c1c500908031100911603884070900081450000f58842c0c020030383c06580007003012030325031640e0210a0726008064102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 367349937 1250 367348687 367348693
    0x10308090f0a080f070816270905160801050f0606030a1820010c0503031b04120308060415030f02100e13050402010807080147070606050d120f02 64
    0x40d0314a56100b0320b4900c054a56900907021940d2201c100600d418080d4205103540d03048507000c258803c2012140f942101c20070380c841d034440400c03000f41905403c0510000c2c00502d0911090308240100059104070f0301e441014403403883d40d5a104110f0032948192080d109100d003000c0410118a004070245410610400c80001c01e6030508965415045d1001c2086440904181940b01e4110f0162800f155881c3c0a0030702416022140d83c840d6142d10008042401c011405012020201e5124040e603001d00302003c01917a0190903400d010b00410412a4030b14451820485003000d4660761001400490f03a00024410407401e83d83d0030001e180c0c0041c0020010031000100880413551070540390707024001051030004140c14280001010b040d8001c5c403034418444008010000d10240d2500724000d809050391900d4034185031034204003203c0140162030090f501080720b40d629260120000d14081c2d01c01e003010030089944a09205041d41d80440c090284000090203600f42401041c8503c40d891051050b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 367351187 1250 367349937 367349959
    0x30f09050618030c01050313060f1806090506061203070b2a030109050606090109030210020c0a080c01110a021008071b06020418140106051b1009150c050301030809 72
    0x21072401d070080d02c9940142c1c2520040304032142018810b03501003850a10701640f0354507098000700c07244c07401d401004220a5444a860a003000c0c0ea44c41000200c10070b60090310b5010050809102074505a0016902d82c0606008a0b14516003450214820550305002c0c2d402c100442d215144407881c010072600200b02901919004845482c03a02011100b50001c0243c50354103020107882220802440710f40280c1c410405071505a0b0441c01c42070842e5412282405554005034081341441c013010011034001404bc400807442c7d020100d01d11040e40800e0740c079040d0400b240740140d552101e1504010790081e544003a1404a14428211f055108405080c81c15880d82004503001d18650744003003d50340b181e400304042c00030007030404c0490401c1c1106081408410310b010616000c0c00410f114240c140a400075480c0c2c4515418104108402c0701001914070a0542a240e24003a0901d040c04450006050400101800d41441500750040d425070b9001d0842c7e0031580d61840b00d80c441081c19902c40f040c490 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 367352437 1250 367351187 367351189
    0x11070602120a0c0801181b0c0507082e0b150406031401030b04060b0d0f0b010e0109021e09150309011d0a03020d26101a04050f06070606080f032101080a030f0905 71
    0xb540d096403101950340d00b1003030508c90900904044032900440201c0d003007000080030b10640c1c00c607900450001040920000540d10b14000000d201c50602550040c0640d82c01e17802c2c0440600160040f04c400f501c040c802414100281c4202c84000d00005000c2e4080c40081000b045041d030201c0350190020f4101c101101d82c5403034402c960404542c044448043c0c035030060101d240012415801003104580035401c0c040d0107030440e14104407429901d103403100041014103169803045d031084569012070403690303a20b05000c0c0b989806000900303400e500b44044072110f11002a000603e0b880b5494060740503008001080408035260390b8418401c0346a44903000e4803990007120b100040c0d004a00200c1840000d9190090801e0070b009042d144c0705680405210411181d00c1d028202c3c000c0c0c80d0101d500903603078500791400728010445504004614880c2e01c1220001503400001012221440030420800c0865801c1507170400800340120180d54000d003020380700113400b0342407010342c84070705003800309001d51a18 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 367353687 1250 367352437 367352471
    0x9051002250503280f11010f180519050d030b13050f0702060105150702010c020a0308030903031e0402010c08131e091107030801031511070602120a0c080118 69
    0xc074054400340c00001d842800d080f0350405000078038100c04030355000c03c0103001c0003400b60114081c2034001c1c45801c060620320a030003980880081501e130300c0100403018019804010030260a54229040c0c82070404440311100101003a09000f580704000f044d58001c803000c01c8028000c20880142c008005480d00305044045010b40c5214000d0808000c01510b440d0320000c0c581300041c0d01042c000c45a401a0781c1d03c2c54040d1080340c202607028240910790318500e10110715200398030303800901004070100c140921114080b000358028048148840030000c2101d12803d802c2c0c0042e90000c1c0811420344489000500905c098400804615007070f0110359681c0b10b41a031091095004600e40b80460003090002012901c1084154010411183e00b010f280b6500985042018000605011003a14480c00e00e00281d400c0800c100080441c200d807501d031030740340a038040c0d0000703003540500820200002e00801154481c4000b098140d42e00c0d01816440c0205001c001150410b5000105880d101c004801844034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 367354937 1250 367353687 367353757
    0x50904080a11120702041b0801060e03030f070f02101d101206060e01020d0201020315090603030c01110702011e12052208030108120a090b1b01090303060801060909051002 75
    0x603c0380c0c1039481e06544100000c854000d10320b82d04550034020340103000c9520540c000d06503002400c1000690455000107442d5000c2d4504c880c401800001d1104200200c0c0d540f40e001c0036209072216601e0604031102503517030b00d011400340d50321540045103613480c0e171038109510328040146040c09010010151203400c265211a0010700c04508003420740e038801e5034100604c40650070140300843c02e50404011401c81085030440381c5110b9000d85e07004c500715603824801c03103407892040c3e0000c10400303010000541e56030f08441c1050307010030886880c000790703076440300c0d0b14070101039103a5100e000c46040010004010840503003000c140c1c181290050507082c00c04000b08404038018060940c5941c0361503405031810b404400070407070b1400d0611180f40b125420440000c01d44204001143c0c884c00801c0c000b400c02c1c1c196000b00304c0d5941c2001c0b01001070541583c84079066680740c0300240111503c1d0246070003a00c41080005107150301181408242140c103074042c18600c101c403400d186c01080c50301c2e0178021403a88 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 367356187 1250 367354937 367354963
    0xe0d02060d0e070512030d090809090403030b040606091d151e1c0f0b19141506090303070305071104060b0a0f0e0603010909061407020c0102010605040501050904080a11 74
    0x240310720388400e50b10304000000c0200b1040303840750700200003140001c0e01d82c064000280107082c2c4850f45c5004000c69442504d24003031018011345142d14050900401034180c82900a010360f03e8024041202413081580d001525215040fa035810791400c00c0041031000010310b440100883c45840c049079541c2e200045200c26001107003020100c1414080000c5c0301c0d640400102524003020545000602c20b6041c802e4064100a00c600070b60350b91014150401840c2d07917036050041c40d14161151035041d400c8a11b020709180042d400044401d10248200303441580c441d158540e10906c000c00009104d50b0040040c1c3d4032075038803400e42c222000041800d0301c1c81500b040c5080100810810b0006510070f2100124854520301b209044a40a0104000344018040e02511030b8840007014140705040c0c00c0010307103081c3e011442c4001c1c40c11810080d1124080854180154200140003c051615010b001c4c10380300024143d041c203459941e40c61069512510b80c050620241d81c0d17510407032040130f0210035480c1d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 367357437 1250 367356187 367356191
    0x102010e030c01060603180b0c1605060a051f030816050a06060803071401060e01141f050406021e060106110f0303010621020a0c020103050702070f08030408120f0a0e0d02060d 77
    0xc1484805403c2d0f50f140d00c1040340c01e500f0605007c011500e0101110703080440d0f45070084e0b440001070014440c070f51202601410b503229500900c400d038031980d84007501c41c40002d81c0c0400703140d40481c08580400c6461001910140080c1b0881100440808203040c98912a9044401802c110794030102565056405224190000714080080c005864020f40c05842960001c2100b1418400d1066840806001d600302c2c022440349045520740301c0b8181e40124281015180816480501e001041c030b5221b40500401801421205490102018078080d280580c00000c3d1405a08008003128030020b502c00c4da02c29403088000140f450304003407004501920f003d40c1c4034480386941c0c1d06080c4030212a441c60070b45a91040122942c00c0350320000d81120140e0901e13001c1070ba9202c0c491304038504200c60300000b031100344200000500700170001c024002c40304903805554000c0e010b211a01c81d01c0c001c1800050071500c0c20010000c06510800c90700d240c00030010544034551003903401103019078108020011a40b0303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 367358687 1250 367357437 367357439
    0x2040c17041202160305030415030902130606030f022701020102070c060801061b020102030d051009020406030209030f070303120e070e010305010b010306140a05060711030a0b10080303010e0705090102010e030c0106 94
    0x1541032104d41c1070907150b0800444140c1c9542c2e5007980e030f40704610800811104074040024813a100f6044a0050364004040080b1400010014401008c143c42160b003c04e240a1000704c4d0f2204900a841c071810003455038a65403180c0e420300c000240b04103003d042c1155802c02001e4002201d011806024080b260b995501540c18400090084e003501d40c029a54074080580c00c0d0010b0307034004101e0701011150300001c5149d46030440301c0400112260001031001d13001180100711158181c1c09096230000440843d21440c1c0d11500b82519900706001c00b034000742444460781421105074100408540d034500031030b14900e03a520201a4001070a8004644594540c05444541e6a0501078400904404201030b10a20402c2c00002c02e4040f0500c01d41d8003818011903107400307010240b0383e14004c683c00a0300303484001d481440c1071210b592045808040140c1810030100c4d2511000003968181c9545c04141403071a2106c0c1d0050703600760000e001e001e046640b02c2810080c1c0740c1d0b050000e0210140d021002141103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 367359937 1250 367358687 367358723
    0xb090405160602070f05010e030114010603140a0501050303070825030e04230601030903120203010f030c1a03071b0c03210201021e1e030f100e090a02040c1704 70
    0x20740c19a030310400840d84214018440300c040c42c5c0031507003259000d08001507440d40c8940801d0240c80100010002c0201400000400c076401d41c00c03000c04034800c070144942e5550703028043c408651080c0074068040c0c1c400d000090000c0c0c01c00004241f8084000450800b00b0307080c06040c00c000000c000101c0c001510440294610b06003402071315148c41946641c01d07231100b9145208141d00c00003c001034101512460740f1818140074100724900180704601c1590340e0744e10344007009030b440c586100860b1034401c05403001542d589002c8401034080d40d0004114a95210103004465440d00ca541420360914009074200000d804007554100851107030700440106c0300022210001181551003078402e43e401045120700181c0400b030000c940380a45113010340c4981001d00c0814a076800d11030908400c03031002090000301400010388074402da000c1c4000c41c0d1840e444295a05184c43c080d00c15446650000610b00c1c01071410fa0000e010580c814030b0200100c14036480524410300341500c0584561081d1010f44c001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 367361187 1250 367359937 367359973
    0x12010801020901110606090f0c0c01020f18060f03040209100e070f08060d080304020d05150106090f06091d0912070b010806090f0709020a0e10020c030d030e0d0c02040b090405 77
    0x1071000034040d002071b10740030002c107441c004020f101390081050717000040c1c220341607002916801c080301d00c000c548811406050380810380c402200348000d030512400480052415400b114541400c088600303040d81c407107500b03022040c14050124142840302d04004140b444606080e0f520404040d65004a0f402d6000c0c8d011306140d901500c454001c010034460071000c00c94a104072600300d0390683d03140000344250300b051401e00b285543d0307162000d5607200001647c1c6520040781000e9641496940d4500d658429080d10700200c00e2042115a02030070b1030b61b401500b000200700394045090415605625055160b103283d0f0781c00080b0441d0b140074010010b2010b54000c00a03a03501048a80041140c070302d031035004c02d0341e411070f034490820300d15000185000306d6407048403071107000d05018110b00d403a8001414080d403070300d18035103060b4080e00c289501e069840d48207000e007400c3c400d0460050f190701001c01d42c0407505030200c0b04081e600551150f0700806680c58090b00c0c2445540200060300b40f9148480d440c0d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 367362437 1250 367361187 367361207
    0x3150c030b060306180a06030215040e0a02030f0703021605010c11010506090c031311060d0c0e0d0309060309030504030c030c0608011e060e0f09040b070e031b04050c12010801020901 80
    0x401164207104205094642d903089003000b400400d20b485d00b5503501c0c40c0020207040150402074014481803d1b078400128a0b1002d0015501000c82001050b510501650100e01080794a04040100c1401003001d50b4005d40c014034035045031f00380b100e92243c0191140b03406d46d49804201c800041c241ca03016030019074284207150b08060203c072000e003a42843e2070a48401c0c04007920500301b02a0030441d03101045181d0707010400c90301c2e000e401035845241840c0208014803000c0b0404021a00445000c0258544031014496195058540b07940c500d082c06001c80040c00010001c50902c90304020100c0802c015110b848000c500c6052504051420101c0051000e80c060344400d99072800c201407001030042c461511020b55040e440c0c000c0880103010001807000780180c0c9502e4000c85444184010702c02442d103268410502521510041c480e818245640c885074180c09600081b50061502078620b050303000f26800001501c185810070074564010300c84601c00303a00c41d01d01e40c2c0d40091800401d58005000710 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 367363687 1250 367362437 367362439
    0x1306090504060902070807080c0a060e1c0305060102071e0b0d09050f03121504090f1104060b040608010b0a030b2101180803060d0303020f220b250c03150c030b 70
    0x9030402c2807680e070fa107581d8003c403a0b0080010f500446d00c0300041004001e14060560014bc00707010411000d28010b4880d4507003561040d2800301000c034004954001c4c0101405040181c1c018450786182980401c11041d0703008080c0100351401000184040100340500300d096030304a000a1a500140fa0203807400d00260300c488401e40061000140c111146448540e105221600700c402455078200000d00812001c90000c000c0000440c5810501005010016080c1826a01004030b20380307410000e01980514441c29002030344800c0180122401a0060808180281804a03946180c3c000007564803000300070b2302001e000d005030442c4004c0c1003401440d4006808180e580000415519400340c80d00c030080107107028060154882041501c26412540c451500458054131a215100c11203840342d4040c24440100d52200004a05a8000d030211018801c8041e0a9030700e03012108131204c090082540280c1e120150118000045541301c80c002e8a82c1c101d1204c0014141c1d1202c0c0043c0469024140319 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 367364937 1250 367363687 367363691
    0x9070608060102100f0b06070303150e06100327030206070f0903080706020307021e0703111c0215040306020409060e0a0605131808070b01150201180305090613060905040609 76
    0x1c0403159030045111040b60304201808902d9407450300b59580a051100c14042c0c10610003d0040c0605071b055101c00302412140f4403040c84a955210110804002911001ea11060100300c8414042c0254400c51009a40e02408130843c061120000000703c001380095015821980230095183e0b0701ca00d400208103120309024680c3c0d81035444002c4030f80254080184040c1c1e0010202e40d0700d034003c00c031800401030480c0402c0c80711070090b100c0c0f90322010a813104440440c1091000b03041450204120182c0c00306000384216404802e4082000c080021146800555400c00001c07011850900050019010004020568900e441c041c1d4007500401004e0250203864808144030940e185401034040902198010800350faa00180b1403030300f18051401841e002000503110100015a251241200c44000d91f121510003144016403e0305c80680f5180a5807104294140009010360083d00020101030003050074000075906400480f03150781c0108020894030342040180b0316050113604090711800c001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 367366187 1250 367364937 367364941
    0xa0504031e0c0f1410020408010b04052511060907060801080307020901090f060b040f0504050c03010f09052d16170c070f0f11090c0403020f010807020c0d030809070608 74
    0xb000501e0300341d8020000301c0c8400c0d0b072405014445241d075807a004e0360302c02e0b50300480c800d4614900952191150101315402e0280349a1540390520400703101d04000009001c0645081030401d1080c020800b0f01d406200e00800f0590044800700041071240102c9070040c40c6490525202601c107007030503803040341160b004126402c0180c80761001caa044688003100802c0600c169070424001e80b916410000d00000c0214000820814420050f03046490a54041180d0344400781030304400e21003401340e034804550792401048107540701e274081a4015100040a54400d901d01803114041480e00180100195410140314042a0454042c1120f203060b04000c18040035188580d00164002030200e51310308004a0103400b0300c04d25a40c00780c40c50342c3c0f241142081c405c41e032502c0c008840c2a4400340780142d4641002501079011103088505580d00103064829000c042c4004603242c3c0c03002800d060843c0103581400a680e1601c0701001b4a00c0e20989a4141320701d040302178140f038800c3c642e10080c100503030f8800b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 367367437 1250 367366187 367366247
    0x405090d0309060b1206100e06030d0c03020307061d07090b010c0f0f0b0c0a091401050708071401020a0504061803320d051c05070e010507050c04050a050403 69
    0x20344500c0c0c0ca04581804207000c1500c2c18510014000b07130580035004140c2d140402d03011100403030200d1044c4804040140d510b0b0f120140c03082e8a1341c0484002e90540e1041445244841c01614141d0740f06100e44100c0c0d29002c20350350f815003560010345034421090070304440080c81700014030089015180b685410000440c200b070000f8429034030780308007400d2009401101824802d54500c0008599041000e4a516080428010100382e10800001d00020b0303617210b000c2200340c00507050102c11031059699038102066501c418074181d100c40400c403a944842149400350381828005030902d80c41a40319603441e03c1c07030828060841d2100078400c0c1c1c00c941e00c2c0c250070300000c0c07a50944803c624800810342e080c803801c841442050280c1c0f4280d800c2e540d02c00c8602da4159180c4c440001c01c406500d00e4070703914020540190000a94006940100100d8841107015a1551181e8003600500d070040044038500c0f0340c0c01000c1800c0707400c250b415190003a11101003009141e000780480d20a10160b151454030740b02044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 367368687 1250 367367437 367367443
    0x9100c0213051005120c4903050d1d06101406040b09030321060a12170306030705041406040e0a0b010308030c0409051f140105090f0307030b010f03020906040509 71
    0x4051130344100000e03121000e1008040094a1900700040c0c402207406242d5405400c040601c00c0c1c0e4074821424014540680019118040b01600d0111140c02050101650b003540c150704014240b8000720ba960542c85070fa41d0720092280f03d5100a100a40001d0401440e06428180c554118404510590010729229104c21040f10704640e02c000780720b0340311300c20071000906620680da5412500c0300200300410381010074030307459406040101c441d84280350790344000d081e02005940024000d610f00300c4c0008802c1c03803414011640140010217030794019451300e00080484500c1c440c88140c1849541c02c00c040b9080c5442401d0200c40014000c3c040500c40e6560260310610500000b08041004808140d03625103000c00d45015003c640004d01113881c1a8940c8211203074103090250420140c0c0780001401c000340242203907080e0701a5230300d0745040100c00c00e210302e1140032150a60584100c090000100d00e0030714140d4040c000d910340000c00c140c03942c010440c480d0030143c2034610403440c2ca01442039000b800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 367369937 1250 367368687 367368689
    0x91b060702040b060301080607081e1f0b04090f0e190f02011b050f010506190e04050f120d0b0307121b030503041203080f2a09100c02130510 62
    0x1210a140c0d62442440807402801103e4002a045a0044000702d499034020032001d203d15100d5450781d034907a881001010b8141d6150320118405a001c00200310106203c0806841c0607082181140885680355100d0310150301c1980644010740d0341d00d00051f442009030061744e420311548002010748081c82c00d545e20f803103461610000c05805c48200c5420071079000d040c19804408503015500058441d40c10410784583d00c4221007101940f03404001249880d0410306d0780d108030701e6001000451820850840400e1102400a030342621914184c400e0801003044284030035080c050059032261140400344d4142c030141d661642c482e420494003409001c6440104040e001d420966480035000e040c1c0e800c564070900c6800140441c0400140810380400500b80b40701494400c0d502c3d20b0f525941c6158032540b42d501602d5038241911401c8080fa031806010f400b04a0300300846442910f80690100091802e070300104403900410000610042949040c00072609004140340c0248050300e000241d0800e0f00c016 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 367371187 1250 367369937 367369939
    0xb100801064514010302012714030f0109030c0b070f0806101209051f0e0307111306081c030b010c060c05040e0a0501050a0b070b0a270b0f091b 63
    0x219100740c0010201d040761035202d4a0031010429200c8094220030200003d02050340403581100f545c0d8001200300304030500264042d0080790b4403c2c24507142c40c911800002100e43d141c4141c840700c8003424800c0c85490507143c0703c0e446402c90980307945230101010360001d00b00c0082c03210034110b4244490f08500107030f500030403c8401c8680c0c42d11441055034040c84030b2020400c020315201e92013041150004192151480c240405c081c4180440380840540c0c3c0d4101504003950400d00c418800034202c0c0c0c1105c450148014052101802c03880000d00446202d03a1090204c0e92090640348000c40c10240c0307a62250704249014480030b08080c00180810000a000501d910360310b00324502c02520402c1994040c0c54111500140d500740b41c49004080e03d400c1c00342510500602c44c000449080c0f24045903002d641c070400d80491540c680b48010000d112000090108008440c05001c200742c40e41003503884180704203000b40d00c0d030a0004160b18808030043c4180925031144801141c1c00e54014011241510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 367372437 1250 367371187 367371269
    0x91506030311061e041e03030c120e0a060507031b03090219060804020906060f04060210110301030c0b0d0b0d0506040b0703060b0d1113031a0610090902070204090b10080106 76
    0x46a2030300421b25004400c100c40071400c0001c2d11800c041d4903822000f0640a250307195540301080c5003200301100d925001c1c0d22040d620001c08080044e1650300150f42c03014240c100007400ea980802134000c503490a0001400107580c1e420007004501d46502d200d912074500081404074182031900140c03084402070b1029104031844000265299503260480d0701114508003542d4440742c2e80c12019550f0302c11002c400f03003614281166444800031070010341c0e04981d0040d49099640e86041004900c075440302240071800c1e81c43d140201410344902800e0b020092050700102241d14080c00e00c41c0101c9805071055040500702002003090409810a44100b0100098000340c0030100a180c41d819210f203043c0b03501460a41d90000040c01818054514075820000c405c81065680404110f910b00c161183d00003c44c08088081c08080c5095000d040700a1002c2c01c0041c0141568a846411000854040c01b075001044010700980c04203008010040190721141d030003e003d1007903019142840e9100640b003910f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 367373687 1250 367372437 367372441
    0x340c0326030105130f0c020c010909020304120c0309080a0b040b060406050102030306010e01050d140712060506073810080105040503090103200a050a17060117060103091506030311061e 81
    0x70450360320003403280d110042c04121b00e11032481c010307468070001c01070580402c50310072000400c10528001c4910a9a0003d5484041c401e03401d81960f10340e0101e9010b908004c0e03072000119508408009584280e4050414455a898103140901003420003c103043d00540c288038007000b06980010950750001001d0038500090003003000120b4690207207030708a443d00c81c2001403030140340074000b4009000e811503503640c05800b0348c0000001c05aa12074810590403034010001d800102c2d102da0281000e141154800c01d41d04281901c2a45155580301003804440c1b5081040c80100b0701b800c54184018540c100c002e02103450f05443d0b8a440780200440e4605040d01c50303000340c1e0402c481c03208001d88064103410301512450300c2d03040109250884061080481c0711518000704002c3c095840600c44c0c1c0d016901c0c144420500b0343c2e440080440600791030306150711002c0040c0094505003044080503440a0002800751940c10010b060fa0000e00d031468042d0040001e02217544000b95104a103456820002d807255 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 367374937 1250 367373687 367373719
    0x50402090d06020d091704060c0b070c050d0f11010902090402190305070810150e040611040b0f130614070f02030a0f14011401050105340c0326030105 66
    0x700314440042c1001c0c4001a400040c0c1480e5000c020028060701c800701c000103c2c6080d0000c00d102c0c0740075074004184000202800034010008a90b0301840c1da10704030303010f4040c940d02c552403c40701003901408180c580980c40c1c0303010340c00309104035801c1d100002448401200d2300030504591024201030b01660014194451601c00f5034011001036511004441780240d6030704c6481c0e02c0f1f44d020840350040c00d04010b0b901603414025135240c0e0a0340c43c03040b0485800d45850781e03450b004001d40500804108010701001a0007003104010380301d440c010100d950343c0c803105909002441c814a402183c00c0c0510b8100014080010704141c2d801558403100070112240b1900000345801c0d100e200007040803110720200410070010301c2d02c5e040b4070204d1500034017a90310b40c0781200e880080300f4080d5600189081c001c4100031461602080400c042092041460003c0141c820f001c0b0799003400269042e404601080081080480030314904188040703035070307200110b50500c0e81214807040c42014450085540d03820b80d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 367376187 1250 367374937 367374949
    0x90b0c1312050102070203070e01060813030e0d0c0e0705040519080d0c0501020d0c05040e13050c1003110d06061b0c0504050402031f051012050c2e020615010f080105040209 76
    0x2178990010200d50a0517990f203c04032003102d090180d0341c00210107002180e00c07200b4a5501181483e1715072550829640e080c014803140b0340c815803041e118000d0016001510052041d103d60050400e41d54a0350742e5402d00341882045a86216841e14108044d141002100004164a01002500d01c0c000c000030a490810074007901908207a45075507441c2c0072040007850f422000510880f054154402d51941e1131112408160114600281841d007200b580a100d41c03400f80c1a0880366141803c0000700240180d03004901a0410b504c2944e4140e591001449000d41018012a1300c0e441d250310700d2001c00c0310baa10207054000318416a4000c68070348012408542d0f052041c20030f84400349021040c1c40710000c1d04d0402401c825255002114071032a804141502d803481c46255540d013000c0101101d100300014008140a04150080c03810000c0000402607504020744011035102e5600812003400c01081c00e041300810b08a40c203044c01200e000281103103402140941c1151021240180c442983c1008540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 367377437 1250 367376187 367376197
    0xc07020105070b15040b010314060105160b01140108220609111207031104020a140c0f10020a02010506090f24031014010f0806180312040303090b0c1312050102 70
    0xa102412402c0001030b100c00780e900c4180f02d134200c609010050307501005604581080c030801c00564221000246994050002402400c4184403015503aa0315a01c420081003401e8015103050001280149003541c2d2000343ca58001c095080032600b804030f0b0517140e034105001c109004050710345a10005047c41100501035081c0c106c09000c0c05001403503028801e803600e000d03000c101c0354008a60b001d0801b5081601c20740e00c80c405e40c0e4407110b40104000e1424191034110101c0c620b00e40c8943d50f00c0460b0918103008000a00304048009600d0b131104d0480a420f40c3d2005164900882c43c0f030381040b000c1c912418000d030700207400201d2a490b268550005040418500d1005501840340001c41d0107080050750081010304042d0166940703607600e840c41d1f240015450302c180419640400007142014000c0c182e10311205082204980c6401d0100040d40b1450030700301c2d400c0d404a696888031105224102c04801d52182900da0f1a40c03a0a111250754444040b16000d00c1852a805150b82000c1010941c107d038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 367378687 1250 367377437 367377443
    0x80406050c042106110f0906070c0f0308370f03060e0709030c05040c021c0203130e04061404150b1c0b0108070909020105030c0901120f0c020d05030405060c0702010507 74
    0x41035400d00f0300c608161801c410402142e0a901e0800d035103403504442030540380c4401d200840710345810400420000103130003d00d41070b03d800007821300c0003c1e807040c00b83d2090002c40c420140c035900c0d82c46480942c441d00a001168644240c6043e6001d1812121040004420001818190a0000000e501301c1c001c02054114003051840d540038000042d13004800030084034442e201c0d10008584590901007039880c2c504803003002d680511136030340c40d0800c051159100042144100c0341071444808440320500e4081d8401f8178410628070500052101c107025000348240d00050061950400c0e603a40c601e1284404404500d00d591145e0507682640d400d640d00e20b06a005e10200000304e4514280902800c07028401d1800901c0b0300d00300000d100e2910701901043d660161101419940c9902c402c03e202d50200c081d25042200f480d007540c90388441da22070418040d00c1000c1c005251341c0056800791408280d071307a414092010030b1042100003800010199800014241c0440d2101d01500c010f0750903000b640401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 367379937 1250 367378687 367378709
    0x8090c120f100e071a0f0a03060512033a1a090708010f140418051005010b0c06011a0c0f010510050405010e06010305070905100e041b080406050c04 65
    0x403246084000030500486100c100c2500c41641080e0340c01000c0702c00c03400d155003041d0000541000b005100c180c3ca45170002c1d00e200401d28103414444d5410301079019010b02004240d603210284102c0c145900c40c58450351a100c010b515080c100312008210302d440c0074858480c8104400c0d90b84540f0b85140501c8900d00c0010b20a00521a031003048581c0e196003074000c140520a4607000501e110300c10200d050498199100c40b043c4607080c803c00c0e40440b41140300540d04036440364400c00b41b0000e1082040f050901890140649521410010083e00d03010780c0b181c02d0412003401a14031406000c42ca41d81100c0b4030482c0026045d610f00c0e40d450b034034061401d0a00c0c1c035000380220b0300783d0020103410061140030245e51034211140c41d5030820084074428001c61050040b100001580ca50080d4049500900c103030800151a50392840054104404102c5260005824152070b000380d0030031380aa00858140c440302400780e10300c0310200400d09100140060240c035200d074040bc81d80240441110701801c0d02e1042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 367381187 1250 367379937 367379959
    0x10060f1b02041518140c0d0b0d020d0f050d110c0402030a090611070309091103060f010c02092e1215020403020303031602150438090606010f0309080a08090c 69
    0xe1813a01c1c80102551110034105001030080d00c44d4559080d01c0b88024084603801d0443c6514480e008020586815400010020070240544da80d5108510041d21565026a50005c9d40c079000d41013805400350041842084082c40c440007001180e080d0500c103050380d006840b50f481514010241c42110300c090034180c585400030fa03035900c1c40b1000302800350094558801240c3d58840d040c0031607200552a0104203802d1000c10741502d04120300764080c3c4814508002400c0640d00010b03c00724054070340e0140074003510a581c0c4003040c3c2d4800c5100781d0440d0307480350010368544040410010110000185028007100c403061190040f541641c002e96005421640c0300e1901142101c0c044900016501c050311640c2045000e0480e07040d107507803003190b015030001c5030b002018030740026200156070162111122100c403e200d40855402407882604500000d01240c280900003610f40719401c012a0100b50a012800c0040350001c1c0407610304a80524200406aa815503070f107003045402c1c2003250344a810030034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 367382437 1250 367381187 367381199
    0x15051005090306010b070b0c0c10050a0204090e0c060a030e07150804030e190302010e130e010c0e0904120509010908010e0120070201020a0b07111510060f1b020415 72
    0x90060520700358122841e03030362220b1461a02d0b01508100610b1000170305d00044050203640c001e409032440300c200701e8501050404040090350021209654841e40c0464200003c080500621403420090009800d89404203c00700700f4503c50810307540d080c03641700c01200f043c032001003249070000e000e0841c80b2070680c613504100400714001130f14298006039014241c0c90003490800803110600703000140e4094103e14540c0151402c441c0e44144540c801800d10014041150030b0107201c14501e010000080c501103800c001800f54084200440c1c000c101c000204800070b40b010004080c01d06040c28040d4640e416040101d45203001c58010319001d5003080c5245c00005015040114003064012520480d205201c690340c1d910300070200064016030081e00e000002c41c030810301e100d8000140340b821130700307108a200c5060300c0d04a0190030448503101400070490407008001848010307001e68600340e01c8280050b13400a20159002140c43c80111503030070b89130215561540450001c070801c0706c115201c81e54402e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 367383687 1250 367382437 367382447
    0x3033c020a0b06062a1207060603020405090606010909050c28080c090109050d0c0806010e01090c050a09030305280c021503010602061b0c0303040f050c100e04150510 73
    0x450481e10042c101010070f000f450400162003021103040110660300a207012010b80d015003042071403009000392003503110036040b20ba00401c1b001e8010310020810b640b45105010445100526090041c2c010100388226603a0000490040b502c031080040742c41d13240c0c042844054442d50809503282101d1601203981c8a0100c0e912241d8000e01d80c80c0c0e08034956900d0703611000c80c403410095500042d1080014046850209844030030540a1307000420b64948480c5541e1400340c0a0300031040010250004001106082c0101304581803e0320b002e60502219100180c58140300740001828014041001610019400c440303520030312001c012266013070031001c0c01400c1503101c89410303400b44599401d001c2a01040b1800c40b412074015600900040c2d86d82c185601020418842d1110001c101300b102c54030b000c2040001d180180c0c000c007912450052280340445c980745407520780c6070290500351410100f5940110b00040c00355800d9501182000a0b885011660741c41c5401161b0310041800307180c440c0c1a03201d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 367384937 1250 367383687 367383703
    0xa03030b030607080105091909050106030302250f0e0c0c15010528060305040f0507030302060106030f05150907020703020307080303040201080f0c030a0908070816060c0903033c02 79
    0x29030503220300d43c6031407904440b818001d00490b40c001403508041604480d03580c2d040c00701d540e288e030000101400160b90711802d540c515030040e030050b8844560518604e10b80c200a80a860039000e0400d041d07450484245c00c1d00c2c41c54070600111601c007800081d41003010b90300b142e20000b0f50a090380c801c0c00d840710b2000701402c000c1c022503000e030f4040207a01ea84160b4160382d043d4a19000508004485d242030701c218042e103401001200d1f1003040ba001030001920030010348003c1d5209402802443d810480014107c070012403207254800c2c2480b09000e140131040704905c0075910700380c541440c6503940340350503454810580e1009405202e0b6010020f14681d011001e03601540c0b00740c2c0c0d000c082d0b484403201e009002506494601052104202203500b6a00503488001c43d40e00c40c100d02400c118064032024dd00f6080303950042190841145203100700095803051440740080b03821301014180c00c64600401a40d4940d02c00c07a04802c4440c10b6003d602d43c08400106441070f85520b0504407458414025258006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 367386187 1250 367384937 367384939
    0x4060906060b1309050720061504020a0e191203030203150928150603090507211b0306051608071707200709020c060609041e050f0a03030b 61
    0x1d410004103104194200302d80c040806503500c59890b5042c11400401000b0290264046c452902141906010b44280300ca0b02920310101404007881e090406106090074142c0240c42140704002145140b6002000d0b00b4001d0826651240c0c0c61a540c03c00340c01c1043d280e0031040401c10701c40c806a040603410f4000350300c05c6104000700d66201b03443c881804440541580d0800040b500a81d00300340d0403001c2808000e0480c0c405102041d5900c0c54030041d400125140c100200098981c890f0fa805d0280401c1800010400c40070039080417014051a40c80140080c807000741180711003502c00d04014242611240a5508000c0422640c180340041421304040d55100c040412100400200300502880d1618007130282d0b41e503d103440d035640c09821111704012844214400420070206141581c0400001018241000c1d0050350f400180c807507680f402070002c1039148201c1242c5c04100014040d01c4080302c8407030f000070b10001342e000c02e031520a04015445525503c02e115075000c3d8800d140c1d1580103040b403814 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 367387437 1250 367386187 367386191
    0x121b0604022b232109090403020c131d1f0c0201020d150611010e07090c031407020c030709020c0c0f060d0c0c140a0314031812030a0e061605071a04060906 68
    0x614100b010803504c0f0050580c02d106842840101020708040c045594003601c2441603c11004d4204002506a112940c0c903a01a9944491045d0300d108151078103004190200002d100d20164800e100915544003004801010341f034641c1d4454840c003d4040d1052540164001d208001c0000d4988c22920007078403030100000d0a481209501002c103110b00d5a02510303640283c440c0d2410007000b08003400d844480381080640d142082c0a048411085150044460b41e000e0f213000074811007050703d41030042d00700081d414410040d040200100194558048006403101800c00300b0041c001025809072410035032607a4146494481100d90001c0c20a01882c45800c103102d02c80082c024803561481c4000c4003c0100300b02a490181540900d40030315445941c50024200302d040100c402e50401c410003110440420021060196032481d900a0701811561680142001e141a810b81c00041c14903645030b4050100018003a010710845140010411034031741c0303282d081380c14640780040c000c00380340c03009a48540c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 367388687 1250 367387437 367387453
    0xd0606090b0421020303192a0b0403030914060a1a03190c170a05010606080403080a02280507030905011407080d060503121b0604022b23 60
    0x240100c410000740e40000c40681e090a0070000d00310300305001c01c000c460b0301070096a908801a681000103160344140c030500c0071024400c0807006052410000d065040368a20603166035071000040f2142d160b119007150040102d81c50303604081d0010b040e64140680345c51030340c034140b615402c400507d09008400d8440208005988802c41003070203c0c0d00811590b0640024040e655100040c00c10031920030f00803110803001690300d51524140000c00042101c86402c000d60201c01e1000030b22400f00201a81d007011619031402c1d9030b004040010041040180f154042074808100610412a58469520803040e14824041c0e6030301410070341104108900080029101140b254402d00c01090790724075002c1090700b0700c03401da500d16005401c8804100b120a03510000010b182c0c0e003c101d1018030031561b9451503556014030b54000340f1b004070052400c0c4a80e00800620005032100c1c8070151003180d540c82d1800040b180b094925005603a1000003920b0700c02d10341c449241c1c200c10106080c04000389034089428203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 367389937 1250 367388687 367388699
    0xc060e060a09060c0203010b040203090705011103130302010c1104060f0510021b040908070c12170403020f060918010b0a0e0a050d120203070803040b1501020c09062101110d06 77
    0x81c42468401400a4494441004014058246800071510007400860120070301800b02d012a0030845501c1c0071540002c03004c00455821803400c8440082001c0a5031501d80c1a401203200c0621500c002810005542c07500c0d414070074200f18800001c24002c00c24000315031b8602030a59099018020b040c40380512144204820340001108203100d40c07140b211605611031001000010410408280c51034102000b8060024102d100d0500213416a00301a02d02c0f40708505000c928107111000000703451004000610160b030302d600074031400d01c0c01200c0040d0b50f403c0780008a503c80d810003180d400108881d000108001e1411009001802501c0e40e801509030440c4042014400c0e039403041980000f2803913079090105a510b40301c11040355560048030300c0c0454540c0c402c900d6501c1120281c803138216070402c0c00000c0c008443d64401801b4244000c2003000b001c0000542e0042010b082544520300c03103a030215003154203410b00b24541028070002c00540d440309049040c294010b84010000d1860004085a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 367391187 1250 367389937 367389949
    0x90506010503090a1b0902040b03090f06010b34200103060e1b0c0303040f021009180b0a0b0706051e07020d08150a150905121515030a0c060e 62
    0x42080080d001300030040b6641c0300c5003515003002200001070240d130140811941c0c000c0c002000202007003a0000d50300e15101443d2401c2120719418031040d41c101000400030020507500340c403200e0300301a00703e10f0003000044415558082c6c643c8044486000c0401003000d000304003403580710210301c0c01401d203480d500c203200441c2120000d0041204c282009404a4884100701c41845070440200d0004c43c90100d460305940c1c42c5400403502214001c1c1c88280d41c50844c201040c0000701150581441c0042504045068541182c0460000140c44e665040c03007480d5a03408115000034800f0381080c50f500c200c50309040000d0402110600c00d14039030200c150060076a01d0305001e1090709941c0c05000c50452100d011034452001510200c254000290410403030396481c0d03a404000d00c01d032440015141201d030800350412006602551185481c10415845070102041c1a0f400315072280441426035140041000007101c5040e42c680c0511400140d14104450345560105403522604c5000403a0800b40c10401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 367392437 1250 367391187 367391191
    0x70f080a0c020304030602131a04091415010c0303092003011401030201080f13150e060631020418090203070b09060a030e1e1b1f0e0109030501090507090506010503 72
    0x20043e0320802080004c62402da010700b410120044001001316a81c030000940d004040c0e880b4401e00500040070004981c443c4110b11543c4c100912180081c90400c056440f0848801c1c1aa4140a04016100b04140c0300b42e024250301540032039000f04400d6001440000c00c402580541d000e5032904c0a05c0010449207546207040301d6050b074036200315135500e005c0600300c40406080c07072084000000d03080340020300c0c01c0020180320131003171030000700140c14800d0309240401c0070308890b0140b00c0008030015104401070881c6803c603548198100c0036952903c074600244910350084d420030b49050710840111041c0d1300101c0c1418002c07000c580c00180c0b0b03122426074034410b4081d42503101900b0400007562a000340c002000c0a5041c50076a210000752a02c1c0e00b0780d91000c10803240740e0f038000d0272030940c20f00e0301c0400082c07048c0b4060b5080c5d0b01c03200b030395003040e00424000602c2500b40495a8070320311301a031140703041d003024503801070080c4107900952404540d15901c0e4040c0d9141c0b5410000080d1055115100b980c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 367393687 1250 367392437 367392461
    0x1060f090b010206130f240b2707052a0304030201030b03070e010510030207020d11031c080411031c0e03060601030203060d02040b04020d020703110c0406030b0106080915070f080a 79
    0x25035091080e5107042d040040544100d911281480c0404441f60070207400e001d02d41044000420f884c80400c04202c1100c81c0e00c00e4454905c580307108000c0032620800070407a4010180e0619603500c0e2840c07803070583c2400b00205024803080842c20380c03030b0f4a01c070007202810480e4804e072018042c0714200010103860b00f8180c060380400201c41d00c01003200780b070104001d445601a80c03c00510740241c0380c011680040f4154000c1e07603080c07017600d90030019003400c00850300c0c1e0f0f040003500791110f058043c00040c2201d4010300003904600001540070f60b20f6038280b00b141541e800303010301c46400c20000304001d8954151401a240320780200000101654024001c80c1d11900700107000c00142441075003003000030038050800b0340c0c0151f030034403000140549500c000c1141a000c0e8071180c5601003e8910035241c5280010420b00030381c20440c003000050103066020f41542c1081c1030030b032426078812651501d1311241e505d151302c004c2e0303450042c81034103034200070768140e503441039940d002980d907403041d070031041d01e100346801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 367394937 1250 367393687 367393711
    0xe16050904180203070b090d030309020f0405040b15040225022707120204031e0c0302120c03010608010902100c051204030c05040b0301060e0705090118060e03060a05060f0607031101060f090b010206 87
    0x8d1002a1095002281d0b5038030080080180c841d4060100d000ca4404030382c121540800391044c042d01d40700f44c080000003038070300b01c1e002d51610628100d1805c00c0c451044000401400e014112011952104078002683c01350000031004e04010303120300010707001c055400501040d80d92807a034401240c0350003103a050b40c1c0c201d04012101c3c80e940064080d0040c2224060321040400f07100030006a507a10b400d2103603105030b04010014034a40408150031500e483c0d102080c01d80c50910001c00585034481003010221890501007091000c40c100390b8288088600740314424800054040b0402070400c440700305030790040d0307010081c802888082c507080344c0d11801082c5041c9070b03140c0081c140c244504001c0c00413500624142d0488a80e02020000070f0b1015080740c008205c40700c12068440c10100315607503000c0e10201c024020350a042d40455100c1208481050040b14005191428540200c0b60018036462000003044101e80d2118030031800d03c02d9029202c1218140b1103026007543c800a8042e005141c45070017 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 367396187 1250 367394937 367394959
    0x303070201051b10020903070e0103170f040e0a0203011a120114030a0609211b02010f1e08060112060602030412020f0307030305030717010e16050904180203070b09 72
    0x15102c1c0e0304030318001405101d851108031103050b0f06100ca603078a114181130240c0c65071800410181440021380240711402601001003002c6180601442540f41d02c00180b1a0340341010004d0380e48504c5160801040101c402c018400500080c1e4011742c101c0b80f410010500e45a4141411032141c456101303503004c00c90880005202d16072041003a482e10050040031650184078a0342c5004c10b03581c0c00b070320648000c030740b902c040c1003015582c80d40001142610300d03040000700688408200c55103040100681080a140c0206d40003900484184103000155032242800c0303020300750020b0074188100c8941d4001082c440a041c4011118040c40040d40e5140e00990305140c200400d0040d03602110300142d9226400c040200e1007900c00b4040580514066038034260f9034a0400000b421135806200516400545100104101d000740050741d0740007040e80d00105040302c08040212011301407011b40e96032003880c0034813102603544110296003589100740d040e038410039501c0644500902940030000d0b000703410900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 367397437 1250 367396187 367396189
    0x607031e0c1b08030103050f01020a050f03070e0409060504061a0a090b030a08070b0708010506090a0306020304060e010608010b030606060c070501300203071101050403020d140415030c08010801090203030702 91
    0x30101d541411032829103448010b5800000550030114029038000f04000014018490103100f02804001040001c0d490560342a1000307045200f4460058103d08c808804541c0540c402c0fa8910a26a0300038824801c1c414541403007001803e080c0c4048426604d08200c000803500c000ba1001c44041000340400407141c50700c0c005c800544401c03005140d050040d1900380e0b0006902c1000f80620a0140b0200240d900d442030300035200d4041070704500e119103420700c14030303040350740d0100c414003170ba94000701c05a1a030319149005400b9180c2c3c00d40c0c05217654240440801d44510550021182c8035045003190060348486060092600c40c8101030a0b464200b0107060005501440440405104d420310f20901081845034a0490321030007160840c44075000018840b2569020403150f092044120003080107040698000c0d5480b280a5030000500034041100d1011524000c190340c010004c1000a1303968100f0b1040044c01070400000c441e012800e600000300d0250710503c40c58040030303800741c011482c0c04400c0e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 367398687 1250 367397437 367397441
    0x9091101020c330c120903070e04050604140307052506050c06040f03121b0807031b260a050a0518030706150503010c11120c03030115030204081e0607031e 68
    0x203c0940c1c954002080001c1d02010100320303030451050f058150549600f00d00c0e00300f508140381540310703d8241d03400c0418880481e0020941d55002079118401c0e03104070070f1040c82607043d130054080c003418a016510490301c000079490031034400b2100c400314500b403a07521801c1c292207a0042c80c0b41120580d020100003400104200618a2594081c0c00c00c0c00c440103a0005107016a62a10300c10002846000005005250000c0446400c100c0070306080c400d00c8260340204c94031030018620301c010009082420011030007900d41130003411540c91040751840c034040c0d0480002e02010b58040002d54a08800114071201100b50744440c1c102c20f00145207030850944608000c2c042d80503811960300e034090380008450f0f40911486648036040c0d110182c030360385180507050401d601c1e585664a070b001d04101040b004e08000c0300b2241510584900c2c401c0c12003000380d08400a00540d04041da45100d02201404006d171050300c0d5004501c41c15040300d0041c0d035600c00440550381428407040080c1c00409001003006070035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 367399937 1250 367398687 367398769
    0xf030f1015081e0c0d06090302070b0a051e040f0f05030601090e030703030203190203090606040b120d210e0f0d0203070804030f05010b040c050d0f0c141309091101020c 74
    0x300040301c00c511340e080c0c00541e100c0c0000d0301c201c9841c0d40d54840d40c41010b8060200100402c44481c00c141001030310080600300b071040039580071152001e04075036140d801d41c1500b501c0c081e04041003504011070702c685001c1c00802150003158468890724000042480950082c40c0006030f800011f0340c2808007696003a80070750070150000d10100465100003540b0f91441c4007451141c5100d20090900c1e0600100380002c80390040300c1c80d801504c214551865160000540c0340c6040160301c5c10310307a03440d8540041d08040030840c14000700f45003891611002c07138400241c00c41c91542e40c4401d855105024040a0ba0b5070700c1120001003481d48140003c01c080f6041c80314243c1800c1c082c0c3c0022031800da4800000d012102c2c1c488030200401c00101e64103400900501c1146008100b950b0100051401d904010f4800403444c5003189554030b0000b202a4400118403072503008000c0003005100c0224107182024525404031444c50041c82460101082c42c03a0010103060321468030f01a41c1e030141541030070a400d100030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 367401187 1250 367399937 367399993
    0x20f0f07170304152a02090712090605010f030507060f2102090d0804061124040510050411090a18021002120d021803070b03060409020f030f101508 65
    0x1041c400058000c00041a88510894035035031004085c281c82101d0346151070010000c00c42540e511004801602c0f00d00395035400c414a41442400c260845030b068000e07084024000704150305280000420b00c0440c9540e0080d203100d1000d403504282c0b1800704885a8a00d00240030004030442242c914004092107020400442400090720301900342004c5814881d44000480d001e00000400b08a1554400800401407089078041c02000c000481c10001400da428280030700c0c8880d02000c41e00b0802c0421900380107041646040c4030615103410300321211090b0040c2103006100103000190742c4145441589a241c1c40c0c440508050300943d0217001038415410000341c10b620800000b03188900e0410042c12289800344409030780d40802c0712070301005000c030f0b0902500a0717000781c406000c450924070542e0742c407100a440005505110340005071200c0c0700000c5a41d0540a01174284400c02400f00f030141d104a040d0714180300c21401c0d00c4a000b02c0001610944146800c041e180c50f4a00e025590b8015070030300b03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 367402437 1250 367401187 367401193
    0xa050403050f0a02070603180209010513061e08010b0103060501080f06130e0c0a120206030112061b050a030b010810180f020a050d110711041524020f0f0717 69
    0xb039040c400381c05070302c10000800944d001d11400c02c00d035503040c0203500c810320360080d0a207491200740c0e0100e07803d4801030084c588648040b4082503003105c0f0b6940901d00410f001628202d035403c810005001d40c00490080744000d500b400b00602c01c5502030b001d03003401c895040e542c42c0083c1e910302840d544800700c0078049940c8100c080c6201442c000301c81c06200003030342c110030141881007101000c0003000100c0c2c0d8090708010144c1802070000d65106403d81c0d0469105c1c48820b03003500c1b06440c0c10030003014001c0c0700e403040030318111081070800c0d0300c00050108404143c03004c00007004210010b448400c0304440600e49030189440c14400d003084040d04410042c0b803003c020540600c0e541d485826a0050b10080f0005140428207800560b40e80c000c1d000b000c000903905034601031250712103114060800b00010b0040b61600d20080c0090f00040302800203115050901002d0303180c03005450541c2c080021400014800e5140c41c00c5002c0000c0345d040401c03481d00c4003c0513014130300645101810b52911400d80180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 367403687 1250 367402437 367402447
    0xc0e06010c02030d030e06090109080f0c030412030804031209050304090e0703121715010c080f1303240612030c030224010e07050a0e012f0309010f0809060a05040305 73
    0x83c5041102c2c0360700071880d032401b040c041810301c3c00034a441c034000c01107151a1304042e40c0340b01090a00702101c0c00000d6409119a690050b080c100789184100d0340b10340030112882e000c880902d680034507032900992283d03807054844001d140380d2005840032407202801c19002004100041c02c004d5010140d01c0d00039100b51040c450f40c0751140c5010480c1c47c20010007040741c158440105000c421300f0254006180c042c15800d810b0000d00083c07904864980c002c115250025050031408490301c01c0c2c4035510b000d42c9480400381e4680c070b041d014001907085e84a0440c100d000c0d5001170107180740507150980d0f03203080c00e0000070b071010b40702150f0f9007280c0c00056040d4007920500e07940c040800310140d039a212101580d054030f545010b1112034400300041031841084000d0207038110265014038148201c000034138100340825010042d560b400d040c511503000d041d0a4008444043c40c1c00403000c2c1c94514426220f13905441420301c004d40d081002102c6481e0203800c6880000c5410810340e0181c0d41090181c40d01c00e06003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 367404937 1250 367403687 367403689
    0x1703060f0406090603170c1f0e0d020c0312090303120a110729070e150408030c1015050a150201090602030901090b0907260a061404050c010c0c0e06010c02 68
    0x22102c6030810b090044c1c440724148240f12a2005810381048070100803841c000c2c0d010380c0c0d02c3c0c40d174102841e2446410794503408807261070841c0c2c2007081c1c048444010f0780d25038024080007039900c10040c451a0b020f40594180c148045541c41e090b03820005014010310f02d13007030400c0c111466031040200b1101074560781e00c2500f49007428140290509600c01c075411a101288046c5499061a50208115a501540c0204010305a00400403802413106840550344040341c4065902c585c0241d800c1244a4840811414a108800284524041e2000d40100700301c40a15040c1407401e0501d01603541c0181c14140d0030408240004080008202c0c24400043c0c90102030f964001640c0c01031310380300a141e4480780d0340001e10880441d42038000c0c170400f0081c1402460181800c03030100b030300071041030f9108401002c448044004d125080d10f0541c0a20100058403210800c1c40f52000107503802d07101c520900040e2142540201410700d00190480c2051400701e160150032540070800611a90410441523221401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 367406187 1250 367404937 367404941
    0x60f0c0213020a200304030c2309160915020d11071a03010e090105160e12060f1806070c0807020f310b060415021c031a010c1703060f04 60
    0x4030b80c0165618151350000241324001488103401c82c003000e030002c100800c0040d8020f00c54408a070700ba0300c4407442544196140001102800d00c0068100038090104080703019100707250800321419454040002d03840b0300314003024158001e40d141c003582c04640c502e03109038001c0388012000312520040350610341d1a0075007154101d21b482507046d4600004001170004040300781c880c691214500000701704a241244090b80c41120441802d4240400d005c414111034450300c4000c920a2010022101203080c46000c0d114204e00444800301c4000c1003440c0501a4000440c0341800b40b035181c1d888961940d62a01ca108155002080c1240d110906e0101c211130f944401480c1120030303280b1141c0450103140c50310076400496415041000030b62800100107035558440044d901070f5586440d142015280c0c0c3c0905030700e000b00c07554407a80c034900f81c0d08482e0345040d0b2681050a442c058070b8800c1041d03410b9840151204800c03180c00400e00d01c11030f480e05056001000c09154002801040d400d0482a00408502 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 367407437 1250 367406187 367406197
    0x120803091615030c05070f0b0c070c030f110d03050a05031005280906060c0b07143106080a050c1b06010504050c09060403110102030906191206060f0c021302 69
    0x2001d0002c5410840d40c003501445040e1504031a828030518007130b140d5680300640c50340c0e410018945d02d02e60380414005004942518009644031408854140d141e0820103410b6040b405c3c202d4111082c40c80c3c4183c5030510014001c0d481e50303d03031185400c00c0a0440151429080100364840b180c07149100010b41e5036a410300002c50001c101c0c0710000c1c1c1d440c60328107481c0d4405150032010000d81000c0b000c01001c0c0c0d1110a040c1c0090b0806948032190700c5514003251074060980110300d180354003007012460f0107142c6500900411b1445240c0c00040d100c1c0910407c5a0740c0b6100d040045071035400061140c00c01074000560003150107082c2413402e01d0940c0a050b1121074204e403001c07194441d600600860405200d0580c02039000084a401d210000000426034030982c00010010091205001c8032030b4001c000782e9042e034400400071034a51388210034440b207010319910324000150f803101c082540304203a0720482042d90050303582d00442690066007a2441111400100d820015800b0300c01500300040c030242c9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 367408687 1250 367407437 367407449
    0x12020d05150924040e0f070612050106020d0f08150901081b060306060a0c030201140c07050613050c010c051c020d02060702070e1918030e15041208030916 68
    0x1d403070189003024001c101a00401c141d50032042c20345100c0124085001030160040121030104910700c814260300d0404190b00641803061040800114807140c1040c075542c5600c82c1400108245c3c0c0c3e907410102d0307841c1c20a00100001c00c40c80442c508189204041ca580c0c00b880b400e01c86044d80e1080c20200d264694245d1040b41303150030000700a0107460301c0410021020324110b41032811401c040700091450301c503a500040600c000120a6030425000b9006602c3d1804210440d6090340380a00d000c900e10f070311185e8201c1d4180503000c00100c1e03030440c90080018140d000300c0200306660032074005481c80d400400c41680e0038428080f40042c040700b07004400c259010300e980a40f48443c082c41001e4075050b0007030950010341d0490130090100c2c42d18101d00b25401600d0b8550940d100380740001c0c4600802d401e5141001c07440c0851030707410a05800207138032680c0c100c003642e03070440c1801400c241c2c0805004501680c01074141200b00d60011551a50140d0340100f2910192020761003180345403d403a04143d800740e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 367409937 1250 367408687 367408711
    0x60a0314030c0f031c09050c012006090d09050105070b0c090409201903080d180501022805090303030a0504140f060402010e0603070f12020903070608151009030312020d05 75
    0x10900e170b072000030b0351001d8222080000d102005071560b41d01d4550f6941c86030302d0304010400c180c2c00b11085400311903820960703144007038503500d0500c51441602d07095076144481c00720310301403400030b00d5510030011a03002503000340ea4044142c860b05111a402d038001d1410540c40740e107611030f550205954285010f03075144100002d2154030f0040050010951030240004180d1540f490300b040400c0689080f00c2c0b41d00c05114000801c08524600c0c3c0701403900f1403502034803941c0b01041c101030014a0340d8520240b40c41541803401000172460048034540b0035141c0c0e090b0513070810710104074408815004550080d210316a114040165017100d0f914207404001144003e5000109010a55030803003060004804162401c40c51440c10700000751103a04104030715000c01c0001040c900fa08055681616442800141600d003100c0d9507030802010014192511070075030364842c0d1401198500b003000f050502c491619000d81039480c544003940c4111342c0f0302403500c1030b907020001d45260920910440b40328110180344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 367411187 1250 367409937 367409947
    0x1020c150409140f0c0306041104090905070504020c07230409051f0209180925060e0604060c0803070c06020703030e1e1b13060f0815060a0314030c0f03 67
    0x2408241ea2940f88040011043c000a010544010b904882d501080204d0b04940c0c075198000860001c004c0c01c0d14002c01c1c42808100811120307640d801003403c003030050301101c0030140c8a10401040b4403c0300e25103000c50380324143c10020980080b038082da9140401c00420030400204c800300e419260b00c0c1c0011106504403011100f01e0701c500c8540a02d07603043e45030085040c0310003000400d42012a00301c41c8603a5490300c80c0002d08000c3c2c20001c05055170040c480d08800031885090030042d080d05070048402103261003c02089509001c81550212080f560302c0e0f2822056644901015070302c050170350003c2000510340000482c0c40c60004002003486582e000a203a41080703520f80c140070600c800c41c030301c002124007800d07019140010074000901e90702d07100c2410040d0b058002400c141c4e0101c1d8480d105400c02000199280c01d4a01c04c0c0c044458440660303c5e4000007000344180d154044420725402400e00c01c041c400b090f0015011442c0c200d03078500703c89c9410543c1610758a000704150b00001140d0000135 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 367412437 1250 367411187 367411199
    0x4050d2102031b03120105040f0b10020d031a0a030305090a0f0b040608010e090d0809030702120715080405030f0f0d0f05040c0b0a0e10031404150c080708060f01020c1504 75
    0x94140c0c0740c01201d20280d820b105e4942420a20030f1010301c21184910303256004810f610b02581d0009404442c0244180d80900c29031101030340311443c00b00400d0100b80741c0282c0d08100800b540c4645000800180200380c86030862f90140c50b55004103034030a401401e5680d000c600303044a10864006040c9070202c0c0d6449524003d002440300d04143c00080c2001100c03000e100c1101c80c00a00e90030200c00707900b041015030b50f03a1040b141c17640c010914080e40c0080c80d88204241c0d29004030708101540c04174070440801009628041d03524160544d4010659030007042180c0c5030a100c0409000300d0510a4442483c00f0949a1610150b50f41c03d40c0042e460b0340d0ba42c0c10702c4208901c0401c0b84005000782d21501c0d04081161102900340140d041c5d1150003a01801e1000d51010710070b5110061700003150810400a00305400e00e1840c18291130803e501c00380c50100c040c00014050306001c0e100d201160307180c0c12903640740414090b00d1700c0240d44860551003540d03400960383e5210b1200c1440250b241c81e206860b145005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 367413687 1250 367412437 367412467
    0x3050303040605010504110706050c13030c080105010611070e0603070b04150306090b0117040212010c081902031006110106030b0705071b140904051f091505060604050d210203 77
    0x79104506c41c910b80111a04030940704020b0b22801038110078005010354910009021074414900206202006c500000c02003101d1000d0903002e0340c5a002c001c005070b03038035020251101c014864490340180e100d00010040b002500703a4250b4408009000d48505954804100006410030b0304084841494800904040c5505215a00007010b152070103104401c400c80c0003030080045903007284608046170b000030f400c2d5100c117141a00c0b2586c102000308a000104400181003c0e0151214002d0304498075803501000c5083c020343c0d001e8032401c544908040d10b402000d0340c0d41100440a00e8055407600f10010100b0f11000402d84540007907200c50781d4030160b504c1e01c40840281401859981820981c09000340b980290680c90b054109075052416515035092481c0344c0300403075804003aa41400300c403441d6004410f4000f0740c0c1992040070096100170343c82c02070700150340c1c00700c503c00c0d00010305020030030003480c2050201c0da034940190510949428010b0f10400300c5003601c81d052000da403000405146d00f040d10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 367414937 1250 367413687 367413689
    0xd03050901031b1d030c030a0c0810050c0315030a211103030f0109050414070303030c080604090302060606160b01120201020d020d1d01091d010e0a140c0d0b03070305030304060501 79
    0x941c410f41c03443d0789200d4040d280356032114140740f40740303400328a400c203c0e1003c01c03007040703454130084c01c455018400d4684981e4210741402017000360700a103440045940b01c98004c550003800601c06a504607a510074106168054564030242d00d84100490038000c10340c06801c005101002240c54208160faa55019200c02d42809241c4415401002045100309080034002c2c19241491004115512141003070f85601c05214040c130740702d0080c03040010401d50950b0011903060f105499000c8038fd03907007074200412103503925009400358001c080024124580350300207106421034440c1070010a62562213400c07030440240c0050010440d28041401950b0701040405090f40d00303440100000302c44a0001060341d100d0840241e0303810100d0085010790b078010017042d4082d1201484103000854100740e8040114030a1050a100400d0440440e025a900c3d0145143ea840100c8402a61f9110701500040f20b504c030070a80b400b401e9130354051150641c0c2c1405010010750081c00296168102420f003541101c41c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 367416187 1250 367414937 367414961
    0x3180b04120e0607060c02030405060c07080118020d0b04020a09021209160312050a050409020309010b12060106050a1b02031c0806010807082710060905061915020c0d0305090103 78
    0xc40c000c0b42085948110807161101d520140101e405540441e0a92840c00345811081e0306c80e801160a4103c5803000a03400120748a0310000c0c000003618841e484000343d00808081d402044440c2d8010114104400081d0030070302c0500355146140c1d503020f8400032a0801d234040c4c8040c58002c01844800707401007014000090450302c070622003500d1682e565070303000740b03194000c2d0038070002180611817a8003a070203841c01000c2c0c101e01555240f81121680d0b00034806002c03151320488513925404c6044c00c00092083c140e80d11a26081d141c140140429a0000300c0c05105083e0040310048400041c0c07410f004080380884810240c43d80c41d6029903024251540060403031381008400000c01016035800407100c0e81140400b003082c5100300c2c0158a0341c501c0804500003410340d105420600c0c7c1003901c103a0180c000c96200c075204202d1501c0324000c210038416411031005101e6401e0fa01880041f0044075202c88140150049400c110b2044011803510002000c3c00e0700030500100306200746503018054a40f030001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 367417437 1250 367416187 367416197
    0xa03051314030c071a041a070203060103210f120f0b0301060b1e0f0f030a0f0606050a09060201020903060c0906120c0904061202031c0e0a0821040605160303180b0412 73
    0xd10101c00f0605001e071f4840e1801c0c006400301d982d090414400211800325801a040d81c03041c2da1641414065082c0203120420810401400c402c075244c481d0701e000541041035659100100c0403600b17034030003801101030a48007050f6104001c3c4c451356000d20a203001031004149203500c40861103042800341c04010000c0030350040030030035100d1b420041000c680d00d00640c04c0b21251a03840d0695583c0007408010444102c0c946001070101c0e80d6074110340540010812070341d4020071503071034240480c280c0c0104200907406a02c000f020440c6a80c03d0f030007404101d440038212604040070100140741c2d520080c1c408014140e8001008920f40c20240a14805040111281c09503612140c1c0425030720030b68511003050040c00301143e54052482820720b100040c2d801040350002030703100c0109507140d24052200118140344421a140008140f03070a503801c4500c1e0b91182400d0080d0142c00c402da82c0b0803414220100359450b078142000b100c400d03d40d81c201c3c42c016004e11805180515040c200405101d0340c40b01405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 367418687 1250 367417437 367417469
    0x10090c0504080c0603100b03042315130f080a030b030c040501120b0424050604060e0906070c0302030909010311031027330501050609060a03051314030c07 68
    0x40b00020383c42080010685256542ea5070f840005c1801c082190004948a4000800c1c030042c0213030f24845280120f140085003c5600707104c0c1d44503569803070300e84100d04808100c9000401d070320061480b0148190040941c005413440680ea615615805440d00c4804259100c050003201d0804000000c0c900800b950104901d504181000c0c854048504008000240403000101009410214143d075400d01c8441c82d004194054562805080e080b60481d008a26005002418003070000d00300c0d00036040032000e8420358543da10101c0b81d0b240b100c1c405030f0940c4410010389802e40c0710750280600030740c01307540440e0480700e641003050704200d06030040c01e0056041510201d00160084425400d01c1100a1540e480c481d03580f600220404425a01102c02c014169450b625080c64550039284400c440c10708008580e00c0e4001c0008600811000c3c5030409424003080754120300903030003140c00c5400804039a9140b03400e0303a80c6803001c07030a101e8203c644c3c0c0c002080d41400c0c81c0080080d900a810880e07450a0f8071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 367419937 1250 367418687 367418699
    0xd09080105070828020c0a020f1c2a06120c020105240a09020d060527060409020f0d081e0306030307031b0f060603110118091d030310090c0504 63
    0x4140d02030306280740010054000d0302691130715400054000c00c2c0c014299155520280c040ba02c50610401c107030300807000341b00a0f520914100e8290030b1071030b98110080c600d2100036243c0d10300313101041c01d043c0003c0d034100da00c49071403080300254007004140b140d40d011405680e00c2608410750750b1041d000d405580c180310074040181483d8042a052042800880241400050016040c0303880c0b48c0c01010380e984006a881c0b04010140c0094082d1381056030ac0c0a04900d482e44940c8031001c26000c05000000e0300f00104542e842c00380c000e9150a4002842c0d8072440400000140540311041800c80d5130710800640080c140b80f1580110021800e01c010582c15840c000000c29140d1090070402010032658441d2072100c02001a088020340d034105110036400d6415280210040c8a90301003500c01d0540d00710302810317079845030900c1c4190400e80c201d041c44840c58090307a003019201d0500400390f0707400300440c42000701c2810005180b05400e0154444c0c2c50724074003000f90341100e111800e60400c014041000307200e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 367421187 1250 367419937 367419947
    0x1204050a171932090111070f0306051008060a050603070614161b151202070809120c040c02010f0501050a030206031f030f0303020702010311130504020f09060301080d0908010507 78
    0xa2105a801c200c00f8000944101001d85118034603e41000107100c00d07600600007984020705091442030b00d4100c0c44c81443c500b020368a90140c800c00d040340440034002d20002d440ca030812500408511024150152245822400c000c802c50b440b047c2d1580e24010090140f4007040050014a554240381d00c050011181c0000c9501c00c020b4150204482c03030030110204031308120300310110024031a03102e0516032100340001030035198400c8900082e1411903e860b900f0840d02c2218099540042200d190940c45801c2c40401c403042810034003640209404170302d5648a9001d000080703051a40001420840d00483c0c4007110f0301a0070260140c1c0950030244016100c1d08110303500030030401101505e4040507055221001300343e42000303000b01c1c4480d41c20700030150190041c0004c03a10036202440228001e0717901d5407030340c001c0203808012810800f00c100000c0c10554010510b40302410740036842e0400320000b0070b826910030382c00030b40745600081c04400416807181c0c141d07018000140080c00207080140d4020303c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 367422437 1250 367421187 367421227
    0x20a0b3c040e060609270a060f120507080304120501140702060c16050a0b0a050a0b0f060a090506130302090a1503030f260603010e030c0712081204050a17 68
    0x407040440200740f00d580c40009884241c200204410200544612017943ca0f10b045860310f8404e055500105480d15124051b013001d40714074040b0711301d40301e01e41100301c1c2070601807103805c0c0d840e0f000d41c1130007140b141810b00080c0b02412000d03170040c00d50319562900030700b100c1703604800c01e01d03071810141400021680414105e410407440260244c40e80050340c0c600890000081006009114142d1502d0811030b101c051a8442c0400344030401059844469880540700c0d18501586e212805000c0c42c0c01c68075188020b800c001c01c092411030043ea07140c10224043d80c0c000194101e01e801100070420440c9014104a60300410008090001c459000c5000809101c5800001c00740502c00003007241041c401c9880c41a94000c8800c6400c4481c210052a140080280d400074000c3d401c100e080e20107003400004843c01c981c0b00d040103040f41481e1000001d00c100700030104a0702610f0400c020704240700000c400d02d010341c0c00382018100700809443c006240315080960200310a20500c8554400c1110703504103a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 367423687 1250 367422437 367422449
    0x1110405120f0d0c0c12051c050c0703110f03030a0801090b010302090405070c03090b1303110a0b12010f090612020d17071b0b0c19020a0b3c04 63
    0x71000100100715060042e41981030340300c3c0c421948401030340c40d88001c446010301d0207500c011040c3d46e2078030040000c0c031940e5038000d0200e41c481015075009560141094266461a180c01070401040d40441070400c1c05d00c3c1d109807243e4070a0010b1034928a441d00036916001022001145440101000944600014400d449600b691144245040d9011760111120100002c0081080c5c0c40e107100045d10700301c0034003420307000184115170220b02c505c01502260800e064440d80981d0340380c0f4645d294824031031030500898021001d40c1c2e002480306045009012090300044c0081155810110781c40c07103d09040e0b02554a190411900b040f5000e95a428001142d4050399510b4001a440c18503180c13203403034520b00c2c0030120400600305c8140800d101401c45200c19140441c00002c1d9140c844003018000c100038414582c003c14080034141c40390703a103440b00051025228440e410350b902014030181e0400103c00b098808444442c4a5072050303907044442103100c140f050152040342d11404070190095020746 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 367424937 1250 367423687 367423699
    0x70302130603020f120109020c070605041406030603160b0705060a09020607060f1d030403210807180e0705090405100e06060a0c0c12050f28020402070605010b0a1101110405 76
    0x4042d072111900304554455100f0f100068503541e44040341802580409440a662b004502000c29003900c56804c59040709c000c081907400e01e00c0010104240d40d032020340310541c148a01d0750844041c2d81113040c0c0038010045116110740f070303112070309000342001801051007035180e2900c014500181d80307650a9481043d080003000544441d0b4482c0d242c010480e02d00c10601c590040f0316074103e00c040c00002002600c1c4540e20407505c007062035010140c03590f0b80f040544045203041002412080c4208101c400c411201400381c2c18983c3c1d00e003404c0b900100d06035a071000269001444142908050040303a42151810398001203452804032001040800506100e01c00c0030b0001c1c100c01254400d07170984d228603402014040455556400c0e11242c91440c14084038640258000103014090101d042c13807200c20300e030311070320b0b01703c140050b04100c0c3d50031114040742d02030390034014070020500d240700c1c0501800e03a400100d556600310607406001d0310070781687d5a0481c1c0c14a44000c0c82004040241c0d800c4400503554 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 367426187 1250 367424937 367424947
    0x1505011404020906161b06021f0c05131502010b030115140a032a14010f0e060417010204060f050c0c0103200c0f0601082e060b0c0607030506040e0c0f060c0d1707030213060302 77
    0x11601482100d40cd08a8060b0045001c50030150140303400e01074100300d4008001c007014a40074107003170300c2442c12051205414981c1c10041a050321800040e505001460410066101d0f91850b4410700e041c0c0d03500c0724140842040d21030441d40310b107203080540004060b0304682d13191200002c0c043d44000320700c0303400c00015181020b10740d02c2e01000d6a0140159000781101c011078065401c0c000d4004d40304080c0000c40340091050558015800c883c80e0f409180050f0108600900042d409029070344428020204402030b1041080c03118400392a184440760050110407820030520391401c4030681010026401c0881e00b901040d0040c00c0b00c207407041d00c1c1c01440d40081003005502c00200500e901410400100181040107100c01107000c40c0706040315141000030751200300500c0100d43e81c00640d040030364014100a441841d2165501100d118006c00651900000400707040c1000c1e009a1480b0108144d21640a070355160302e04066441600b1345030843c241710b0110488694944030780319a0080c941c5c0000c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 367427437 1250 367426187 367426211
    0x50d080103021e041b030f0c03020306101b020a1503140601021506060903030c030a031a010906030b040e0f0109150b0109061b080f03041505011404020906161b06021f 73
    0x6042141500c240540451341241710140c050b0000c0d21075803401900c2d020880904500910969000b0350010b020f8040c3c2c0b0004040544003018441003070707040c503129076078594010fa80d41e10596001d89200e0303044001c003402001c40a0156190b18509004042456041120070399001034251a0507085000d100d241e0f840700e601103907242c0b04044111750140000604291342a000000508200d55031f0754040103032940000d62500c00c1800301d0905030010f1080542007110038800e41060071030801c014000288880c03018440f901e0450b0401500c021651a4810760b028400d081c800c2d58200c1100c98400c0c0842101c01c0002825107016005100920140d192440c0d0229030071240b0040c50b50b40100c0d0941da03900748024001103500102d0701203d0b4010402c020501801940c080c140c1200d1002c031141c4942a050000c01019402c4416a00d41000d020700005085081030341e81011001d014030030001c00030b42204040401c00040b60003000c195840780d000d690440603164012094104101c10020701140c82c10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 367428687 1250 367427437 367427441
    0x1a13050118020f0c010e01060302030d08090a141e010b0f0d020310020a1110050f0117070e1e010902090910060219080403020405040c060908010608030403140705090c0304050d080103021e04 83
    0x100705100310340c41d10301480304d6401b055010304203590084048820700301104d02d08075283d210440e212400c0350000d01510740003c03114103c5207811400c2400792200c905262481d50840b5180e20240360650f91200b0140880d070802080f140d80d0040c040c1c500180010003034020a0b034802c840b62081400950003d402442c062042c2d15420b10407002c241590802d980001c40c8801410301510340c001000c42c8400005814030300d81d41000b552040000c0584042d510b03243e003180d210180100040141d00e00c034100f1070720500350000e41a000e05511400140c8130412103040c442c1c5104010510303094014400300601503541c0006130310f04400c000300204640090703d840d2024850080e5440290014104401e002c2040308021035141525119604d00d12850ba8403040142030326914850300d0f5450f013042206002181910115440415034001111007441e03481020400d0b800f4210350101203002c02000307000c2080303c00d1010210309540e503d0295040c0d41544c000030300a4000c960020440c1d11070201e0140b1948581d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 367429937 1250 367428687 367428697
    0x1d070509060301180b061204030e360702030909010b0f070f06020d05070806010c110621010303030b30010b03010c02030d05060a060c030f0306091a13050118020f 71
    0xa800c01e501c03540c1d40e4504c0c07007180b0210f18000c5421410001150200c0c00c2440695250005280a10300c4544031901c0c05c0d201c0301d1034101b401e50098030303098020408000c280ca004060003c5082c415002001410700d03240403602c0603152200b103400400a01e0040e0780c841c844181958070001282d5543c4a0505084110348104040141004020180d40c024001580d01600c000d0400300d4003407000d59520030003180c48010440b10240807070089400324020440705030a00f415210064a1245400c05226404a01c24a00e445070900c3c03118075801403007010340c1401076486903074040e14500c1500b602c0320210540c4107480600315100d24803040f01d101c0001d02c25042951403000c00f070020020b0150089000751654030003101c85100d6810000400c400d4203200305540f007161100d55990b00038804541d01220017000c0f004142c0c04040c0c0700d800209100030706114010f58030000206090344d000304401813040c1580da0000c0070071240e11302801000402203010340d00d040103118400060b900c00b070740745031640d640c090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 367431187 1250 367429937 367429939
    0x90303110703120816090f09090201031d010b150f1b101a01090506070803060405090f0f03040f06020d210906150f320a03080703080103060c020102041d070509 70
    0x70400315514540c0e00042c1182c014102c445c07a00d10894002c4006881d4486280309044404d0b0504004004100041d406241418070502d00170401a02c164010344201180000c2c1100e0b596666424001c1890090b410b10100c0341300f901110b05101100c0360046580c007448080c00e0010803c840ca0362241d1509005030701c031601400108200d041140d01041c208030440e01c481c9804201d1a400100c0d441c42c0020940b0807a5511464551441d41c074941403001421015142c030160744901a14003450784024004034000e100050001d589452030103800f5480705016a0192096400089408194542c070944038148003030282c0d904400000e9040740c00c1f004251808015292070f20700903000d000e0700300c0c0b4410070048920701354a0402503911041281000c1c00d4210004840c4107001402030103c2801014064a0240050107031910656036100d240325544820011000541030b0310060040081c41c0c82400c080042c148001c5003490f0a10410080401c0e0380c40d20f0010800b20000040d6103540310700b0803900001c034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 367432437 1250 367431187 367431203
    0x30609180d02010f0e0328050403020d0f020f041a0d15021b0c0a05061804140f0f01240818010603050f0c1e0f120f0f0111030403090303110703 63
    0x2412090090090204801440844e4182400e50003180d100000b035585100c04001c1300310440310101c60304200d5035078003000081448810b100003c00b590b40e8060f003604181c0111121041c108451042001410300154041e00c12440e001c0704405c400840d0075144090f4000303854a103000d1805082003500c030103211000f290303094000110112882c4020880d51003102001c801c6950001d846c0c400c0000c0004240600b5801003c140f0400880c0319203100315560802c0080d100040c098030500004202c1c400480718011078251307405c1800341d40308040710054010140d03005c2001344401c4070f10000c0031103c5e8080c080820803a0710008991585000f481e03113a954a10074008200d01d030360304d00d072858079140c0b00450150140603035607400400c1d040c801000c155120340d00400030b100c244950f0420940100340070b00305400048102c00101420810004001c485515400401441592449807400c0d87c0d41c1904410341c4030018414400004c0d0004030304802d072541030504444440980e4111440d1403074690025103200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 367433687 1250 367432437 367432453
    0xe0c0301051305060a020304080f03040602040b03280b01050301090f150f0321050901030c020309030106030318090912050703110a03050a0e0f180c0d050c0408061b03060918 76
    0x80041036882c038070140b183c0103030b0b12255950010b000480c0030071a00500440d038100136940f49504403030000c59006108960042c2465168465880160412103050280d0071444041c0d40030030903491446580c81c100040c040c4110b1209200080490006210310381d00203449500744034442c0d8003500200d020240c071030644e824656503540c020503d040f8a02c415144203428010a40582d4a000000503000b22145c4a0600e0110180300440c0201400366144d02140418005080a5a4280030b0207000710301903507a110103440841c1c2d1100782d40d0029801580250325100710000090250a92540c903285107040040e02d80000d400c05980c980b0000b8020450741c00b070313261007204064103d03010340300b494656900c0e98210358010701840803403d0074a0055a0003110364529a10001e0f000100680c030503030242c415420810301000610a03507205484101a20502003000d102c0c41108002007035004080e40c0302c101e00d10420f5070101006200140c0b400d4041c1d10040f00080840001402c8400c4840300e40f41161100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 367434937 1250 367433687 367433701
    0x2d0203120313050a080a11030a02060103080306010c060c0816030b03070b030402060f120910110306040c0509030304030305040e0601050403171e030406091403090a09180219061713060e0c030105 85
    0x9610402c02a80882d00c3e641180c1f202d98400016620011195002810030340d0030764031001000d40004040f541080000d80c2d0300d00010702640500805056107450b280342608012110031451003900c0c5d0000d080500e01039031810300b07650000f60003040341c5801c03140c81c0c2d4984560020400a100303a8121003081040058410755290764480243c0c40313420284103645c20011040200c50503590f032066040d4003180c050011850902d0300d64444c101804281c1030852408124401090031500b00f41c0c001d801145e03010501300b0041d0a907403149a4851000d2a105c0d10305421540d170101c035101b900b24081035452010811801c1c03912112494080781070101d101c0c0d601d03807501e0710740f050240900c42401c90b0102000d0901400f11301e07000080d65a0500d008120020a50504081100602c0d0f1208820071064484d910400076880300780440c545c62440350283d5841d81c1c1006406000c8030610141542001114410400c0e907606420100049643c00301c4003054803140d50741130924003018554880c2d415403905044c0100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 367436187 1250 367434937 367434953
    0x9120203031e0f0c0d060f080304051305010605071e0204063503030619050d350409020901051c0506011b0803161205042d0203120313050a 61
    0x810b129078400058900d802014403500c02e0740941c1c08040c1c0d09211800301d82000e04180103441d030008a41c1e40011225607030510a03110110343c1c1d00c1013556400018061242d414010280240ca40c03007024144500d5140c03c0008060b031040b45009414445031809003203568400c4c041c0d40c0d041c0d5400410500030252154100140c40d42032800c01c5000a03500c8400031048140380085000d1031420b04c010b1800e40d5922818081e2029802c60314850303181c4441e0010603169521600c10200c1c50040d00b03c841d240e200307080c28840c0034001078460201c030b0802441c1903407a10140b508503001ea9240c0180542c03110000340050f6618042c01d54180110515a0708000c29451950302032486020241d0320140d44110701e00c11506061803000002d00540c0040001422042c503000104080103140c2c60507510b03020007400c08070100c62082c0e50842c1e00700f505040241418071070580c6803c0300c81550148041c0e060300303540083c1c1d0718003041803070150141c1c020001030190040200148000c40d0003d007a5a0700c8100d0f4588900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 367437437 1250 367436187 367436191
    0xf06240d0c09060305040201020604020f181302010f1404050607150e0f0d0315121a0412230304111c060b0a0605090a06121503030807080105310912020303 68
    0x4000b510030000000c1840c443d01501d8020350301030b009002240ca0701c0d028006c460850109980c0c10072046910001c502d014000400d120321300c1a410407a110845100051401c19034070444000c02202e000030f550138005142c202c804513041126110343d11141807800280e501c083c07450b8245038618184030103d64160100d25111284e140b4402c4d03864904c1d5551040d0100c920254442c080900745102c20301480041c0c4418041203405840d20b06100500007c500381c1d406401c032002c0340c03940b03d080340340d81c940c0da00140d55145108c45558800b020f0007107d00300107514000244080d1a2808000c0c2580032a117450821400801007900690b80381e50070790801d08060100c815400f401410b50390000105507101d035090340c6070a1001001e0540c4103262250440d040034802d00c140001030b5032028600010841202c0440082d4070980343c03400d1614264a000d40714070310590243c6d00404810b034001c82101d002100e44501c207101c14402405011406503440001c101c01c2400618001000c009132251342d40000c081c2d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 367438687 1250 367437437 367437461
    0x409060c11060c030903090d020d05060717150d0f2118050a0807030f15050f0103020102010f1104170f0102030705030f0a06080d050a030e1002030106170f06240d 71
    0x400b56110b00ca05514180b208940044003a0828404840720745805c4289000030350008000010301201600c4941c2498000d0721950040f0b0302040042031445011900c042d4400d000030a01500c90214201050500b0346010b001030000a01c1c60080c810000340080a00000c0122002a0041000c014015212210815228442c1c204040c000140e07454001a1201030702c00c20b01c0074000161555403580c0d0b0b100222003045410445e08641c00301c80c070308184985881010520f0302091294954000079084401071071107516000d023030005030b00c2d01c600ca0b4400c0350101c5451891881e00300000f505402c0c00d107200314941e0000d55000100740034015034000b01440c002c0d000c0060422150325072104410407a81c1da441344010b40d412a8809040f80b40c0514007178103440c4004d003000302e42c004164805900b44008030010031030300c0c2d038080010300000f94000d900000004155105c44a54149045508010790000307000620480c800c040b0000c07140c1c0740315182491032401d42c202d0740c2c440944410140150402661803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 367439937 1250 367438687 367438693
    0x607120b09061005032802040303030e03030f0c0306010207122009070c1b03060e011b030e0a0209060312070b0f1b0901080a15090213050405070801060e0409060c11 72
    0x1110300d8503200c00568052900144080c0c0345400c04070058034640c200030035803003401e14800314a40b6154040b0348010384450b04a000160703181c0c110300d000350860350444020301e040d5005004000b00303070740340c03455403900a40c2c41c1011071b0b100d9035420300403450040e0b07681201c80d03103d04680c0580308002d1604003109001c0c004510f4400b4002c400030030b00c20780030320807181800015110031085011503c102c0402c00b04100e00c041c0d155440b84c60761140c0c07081d036013030400c7c51000b40c1d540e0003a9002084455000702d07601c80e80d03246c2800a030720070b02d120503a41e0421500181c4945028000f08501d80c2d010414210150301c03480c6503d48414560034600241c40c4100c520701801c041407000600d000010f070519454200d20681c0543c1081c0b6210011544410000e2103030fa9010b507140c0e48591001d40300280310000300108100566541070880364104040703aa03600881c000c0d400c11082c41055034000b61400e042d0344d4980380610b4964604400030300640b40341ca1014041c9880e01d40101510b95226480703005202c4943d0072 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 367441187 1250 367439937 367439951
    0x1d04170904020d0209150a050a030e0c12030307030b09010b0d0e0a02040e070e0a0231030204061403070f0f0e0408070f0b0103020f03061006050d061a030412090b1218060712 76
    0x2044200d10035607d007480000c40800070b41c50a2030203a805100200001000c0711004034107200841d8805504840d05150b030f81c0044100070321694140140110103070251074540c16949049020f0310356000d59131355090120b4940c030701f01c1c0c003000b410018bc0c0c114540007401031240495046403c0e4644040d8020180e00c4484840007074271f402014001c0310344000b4000b51381590990043e1500101b011581c03c039441a1403002c0c8004050307580e602918002d024a2042c11207080c00e4441054075100c40c5603c10504c03018580000c004607d03c0c50198070458000242001c400da8036440c0c4030031540704240d802428a46005034040600a45065a0b03042c0c1e8800d40c2c4840d01149068100341d6121800c40c0d64200482070540140016031250018102c0d181c116400400c049442d90345c0c5041d1040d08100d40f030034074000403080205000001c9c811001c621180d081c243d426500341030001e09103100b4003143c8401c4142c8500490568144c0ca945001c400b280c01098a20b14141240018007042405101c41645424451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 367442437 1250 367441187 367441219
    0x100216020a08120304110d05010f06080705011e0e0a080d030209040f0506030a03110c03010e0c010206060a24050c0105040507050a080d0912060b0901080c0a1d04170904020d0209 78
    0x109591003183e500300702800c0d0703610390f039403244280c803e00e08440c5c104041c8a0036100080d0240142169904103140200300d5909040c941854804281d1040d41002840707015110001000c0304140c1340d00c103080c5003110000780d00383c01280c8e1410035980405c01d240304600600f03450603450350140041c008201d405000e5800c451410790143c0e0402c0c0d61243c3d243c0c21031440400000c1c02501c03098141c207464825180703045a0b0728000387c2192407a1820030301c01d801814507200309603418491aa0302c00d604031503c1c41113034204180b00d6200d0804000d0125000e05081d1074074401d50280301a182440654002401103140ca45403164485004d4440ca0780039010b014004680c10501280e0811642c40b030781e45000d100f0b03260038030380134010300300d444280d400c243c2c1c400d2110007a407200f401e40341c06044401c0c010071030440c8200510032468040c1d44a9001030054400725140760b00401e8903290800e8020700781501c68034000940c10000e100e104c0c0100e81c004d1001035030303482d00407036074000e0b04410b0000c40304009540c5440c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 367443687 1250 367442437 367442443
    0x305010e04031b033507050a02072c011419060c020d11030304030c03050f030403030c02010509131b1107060c020613050d0809031603080417100216020a08 68
    0x19070002c021480b020000360080d101820340307404035400f902c1c00074026004030040c107059030103820310300d01c1d194011190810100c201081054124403a0b1030b0180c601003510200940316001c3c0c1c001d08601e6690511424132a030783c0c42d0780c041010440100d480b4441c0d651102c0301098040007081003801222a600b001c0280c5808130003001c1125150b0301c403110820119401c000400d44007000403241c5141c0e004861010b0744082007e080a14454448800c1c41307421801c0180c81c1c180b811801000f9540204010700c00260702403c8080741030741c282006031725594201c002603a0007200840c0160003c0c80c1c07210170302079203c0f4051420150401611802c6041880940e007603240c5851b4003540c030121b40404061304c01424010020036290030008144c81146440300c0010320504096207060328409008590440949010301c40060a404440d0721000c0c011724540da140d1b464020b030304c07400a107405059600c0c170341d440d424460102d01500c40c041c1156038911a11a05151048455044c0d0080d9040200860281000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 367444937 1250 367443687 367443691
    0x1202070501081f1a03010e0a0603050304091109040507021c081501110a05060a1406060309061f120521030118020a03061511010e0c0d0b0601021204060309030305010e 73
    0x603560300d09196106002c482c40807401c98141114151060340021315250f02d60224144092240b0f040ca55951501c89401d283c281d001e019882d109180040410003d00d000048070121070107002c01240c6c1e200e2030031095165025a4998541203410901003182541d03002c560700c5040d8031081180c104510325a041210302ca4022200000e180410b50b90b0340c0039960152280f203104c1003c4c082103e0301d455050342d030a810b200054440700f06940e04c6010b142016500a0b8425500010940b5180c4c1980b03030903800c0540d030300005000e00780e410b0010364111440030f041c010000090680d41102c2e43c030445040c07400c1139450742120a07072036810818050039503040c4130b944102c90484a9011905020701c0d80c82030790500a41c4102640c0e4241559484001440e00c11880890345407296921401001305c2c07084845425210480d02c6603170380da00900311014441d03640125604015070800080d0320030b0791320040183c1c42c1c00b481000c0034502a030082000980c943e419040201a640309a40920050f42c0e41c0070080386409007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 367446043 1106 367444937 367444939
    0x72c0a080d0302030f060d0506040f0206041d06040f0501080a081c0e0607020f0f071211040501081f0b0a050d0309180c020c2e0201060312050712020705 67
    0x240200c1294080815191080b02d5040f03030303440d227427110030080000b4084034040184c0401e64503108152809405005000c41605e038250410a95081c8211080e84c840c81c10a00c8400301a0424000c0c0360407940c07201c00400e400520b40d80c860183c0e0f0400c0a00301c000690000c2403103840c0040e07020301d00c0c944100b1400f503d102e0406400c024145801e08401030115804a80c10302418540043c1d0903040702c0c043c41804c0c80300c2c043c2c0e01d030003600a80c3d81c400d907680c054106800490310300800b003505488240c01c10355488603900c164003402c050300d011202880e0300c100c41310130400003405d1080c580102140b00b1b11b411100c41c1d8035074400d420b01d0303220001c00309252542c52a01480b1560100310411038240e045640036689441240400c4030900540301840c1d442e480300107a00f000714000d4010304051032f13102003101a0820034a1004129410031002900e1100c4189441008180040f03100d5040d280 = true := by decide +kernel

theorem cover : BRFrame.Cov 367266187 367446043 := by
  have h0 := BRFrame.cov_init 367266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 367266187 ≤ n) (h2 : n < 367446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
