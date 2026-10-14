-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1343
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:29:18.24379+00:00
-- url     : https://prove2.me/submissions/a3d6f662-1f35-4b38-8ad3-22d6fd932fa2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 241366906 ≤ n < 241546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 241368156 1250 241366906 241366999
    0xb21030403120203031b160b0603010603170304120c0b060d05100e0109050c1503010b0c0a0510020d0513030f0e0301090b090d02060c030105060d0c0e10030501140a0311 74
    0x31406240000d400710100782031101b500d40325120316003008038031141d180e20403c0030406010311640c01a100a00115006640742c4074018202c145001c680d80317000d000828401041300c58181064100c03100c1c10304048148064540020581c03000b00541e0145413021900005c006c0140b158103220880382c0400c200b82c1e0036052080780244454901214031707200c0c00032800c0a038903050180d02c4202c003400010030b01e10380c00c064803c01c3c2c9801000b01082c0d81d01c05c2c01480000500c0501540494002c1c0b1240183c844d80c00362662400d841c0064101080f0741004401e100220380d21207000c00700c0c6505801c214100d2200000424010201ca800c0503050308407030024001c411001140142c3e0b88441c0740c1c205d54031500c4020490b02c80e44428421554016020044554107901541000c050a58241090800034190303001040784048001040c01c00030780e480d0014401d0952401021141700d1041e640c0070407207821960b40e501072000055515204005041c42c0c0d42c1c80079810b07125400b1150300c012019900850320b14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 241369406 1250 241368156 241368163
    0x110a0f0617040203060103030c02220f0b040b0a0501051c142d01051003091421070b0a1104080a05010b010206250309030e030a080d0b0102010b210304031202 69
    0x2408000407801141d0945018602012600458000300985503d034030310364007542c4032912103100703d8025201d03e55580c20320a16101088900c0300541c1c01044004041009404680c11800e140b40304619198084c022038482c2c0310500d003030350428200150303140e078804026803d0707031090400150b40500708100407140440101c9402e001d44000a49421815601684c0106621980744190024000800100310901d00900c0c01c98101d25a07080c00070b041852919841c010280600410129501c064090034007102040100762084000b85541414460b640e9203010b050f0304080c02075015140c544480880480c41300c02164010120a400c075101082c1500e006800b0340001c0e58898054001c130030016540011050013051184100c001e41c0303808002050040c2c1c0101380d02281602000310442407040c0702e880800c030120f2950b001e207908540314007100000f1070980b0303141000181103905000091003182c0b80c2140b85050343c1c0c8517061242040004403140b0303240d0b021701d6002a00d03500c100300030200803a8010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 241370656 1250 241369406 241369409
    0x71d010e030a0f021903150507030213060c020a0b0408030f0309030c03070c2d03060f09020406180f14180f03030a02030a05060d051213050607060c020708010c0219110a0f 75
    0x2590306600030b0790000c205c10500203041c4006010b03504c1c507450a200b4048154031159201c240c604005083c0b002c8c4048581c40000c00d604000c0206400c50010404c0d03140a2680c03030002c0102c41296450107007403025841e03c80c0078910034544054808804220000e809200380c0d0048014601100d80351000d81c10100402042c4c0d10803881000810108180690740107124000451050200215079500d5561030b4402071021001c2185400ea45900d01c100681e5039020f040000c1c0341b5000c00b00c14000044c0b43d21030450703003241128400701d131405101d03044071005e070700e807244d44242d510540a0058070464131141c205402120f0381d0f0640c0c0000003c02036400c28070b40c00f541c01909018801c10041e550742080c0041c90008840191856010400c02d04400d601000107204c414030364908090140d5a03440807aa542d04445411500e041d1540141c160459040200720007c0003d00001d1180181c2c0500294890b102500d80b03221448001c01210140b244000c0c41550305100507103104003c5a403048038520805c4079 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 241371906 1250 241370656 241370659
    0x30e1f06060f0327081207020c010e06040e060f030319020105160206040203100e0f100b040b010804030c02060703030b030d030e0607020703020603060906030118050a05070608071d010e030a0f02 85
    0x44500196400c0c400c0c4188100085041c0740c0665603141c2807a4680b24902c3c0c0f034000c1750181c0301009905010482002150f0188540f60003d01e90113400c2c6001521861030700722614040d58051104112088420300383c03540000060710441a801c07000030102e400c51051411103403004c4d592000c52401d465055022a1180c3d0180f40d5121303c01c0d42c4504226201c4c501590040d40c16400170ba0004110340d183d500c03981d000e40810085842e00303442030400078144401c2d100c184c03e0599840303100240500349409105213010003460208094541a41d0240800b5403d20300613000e10004106070301058001da00200c000fa900500b2110b81c0e41041030000d014008425100281e40901800315080a0002850074240c0354020545800c6545400a000c0040b9008004562544d250340181c039a55003180c40d1040c055000344080d040c0c0d1f800c14100280b9088655100b9020890040200301007164441b03900c039409418a0095840c40c00c56000496280817244103850745070094420b01410003c6c054881000c0510 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 241373156 1250 241371906 241371917
    0x11d030f0a0c230709022802010b031009110306060108070e03030723070806070504030303020708041a040e0c070201080406091b06050703030b09040c120c1a040e09060903040501030e1f0606 83
    0x32900c0040c5c1c1a400b511126100c04a901c0c6680412004224181c0b8408416880001103102c40900007a107000c0401c0f440304a01c82d5104102c0041c03020801418501800580080c02c1c1803c2010000345081001000c08040041044402d4480d40c1c0a004640f540780d041001d104da80251174560b00c0511154003042400c5219002000524010208882d485469180c0720b0900302403440e03c003900a5071200d941190b59240800c00410682007038400030f507074503050070002900e96003000780401403000e0141c05840c003161306008040c0180e9209901ca0360081c2d0001c408550040c243c44c3c1800c0e0b03121a080c1030914050950b4010800a51000c09412224040e40d8148003040045060201c043c2090760050030340d220042003800280407040c510307104644160b84040b2500e0f9a000e00c0c40d68001580800742059100203410011030804801250300140000f000d41000d040c03090110787c1d41d104034410581496143c10f000c89a45a040c406d1482e56004003e2908078040b030308130b5a000800103070044001152 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 241374406 1250 241373156 241373159
    0x100206010305060112080705161502011a0d06020c01050c0a1706061209120d021c1811220501030605071704031b060c0e0102011d030f0a0c2307 63
    0x14400651241201d400c00060000b60742800b440c100c0c0c69a0981054419800170003080300028020040c2074032281c040400c18401e10304000c00036801c02c22009004085a040c403d1080304101c1203143d507007803c007040b10031800594503490020040c2c000d080f40640294640f07010420307401e101000a0100754403d903540c0c0e1081c4003894418a0240c01035410681155041c0100003e05149500e156009400142211104020b000c0707203040070b601c080c0d000b1050740e8000c10008800c2c2c0780001482c84a150002d414484004518581d496a0506141c061721110302000d4541070780c1c460391100c4076003004000030021400305401e1248040d08003880120f900500d8200003568582c40f800d04c3c24450382c020b940240c0741d91100c0d101141d07080100d1804c1d0b00c2c070003400410380000980e58443c55058034290784402c00255408000a800c6070300e403101c41e40003e125100d06110248002c012681e00c0e0307502140294a440c031400302140d0034010001d000709105d086c1c11900496030100380554409141d15421612010b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 241375656 1250 241374406 241374439
    0x6050118060e1009080a08120c09010c03030b04022205120a0510020d060b03040b07020d0f020304050405130c080a06060501050f0405040c020a0b070906080c040302030303190e0105010b0306 83
    0x11103a4800e18000607001200c11480f8509801c0300003075a100c62805114840e1542980703410420510011100d00c9000154210700c2c040701100c8036070204907901c800342800d080c2c1c00060424500424010205651403400070711540e01e40d8161006800203015069074004001103010890500d03001d0248a0250000a400b5224001880900c0c0036440809403810b8801985160040d40002104200c0345451740350110f45101c0d1031001d584034a020b004400f01c24149000042c1c2040d1922000b641080400d41e2241d224031340000c01c40b412117100340c400040c2940c94020b4007000d04603001c8020000700c0c444c0c00000b01100006000b60f101401194200061a607840044d50241b1884550b1107882400788010005441c00c4d6002501a5140340140c0307120321616641d01c09000000c50b0280003007021030303d0510240358055036203540b2014a0310400d190a0850300000d9590000611494981080481e0898130008071b1700188034a050036002481b055844020081d0550001c40e1058080d0b1000105c0c0c0c3e288 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 241376906 1250 241375656 241375697
    0x1209040f020f090d080c0d030207020112150b1b070f1706072a060510090c0206010315020c0f0a0308160c0b0f060301240e09070b0a0503040f1401060501 67
    0x10402d01241c1c80d02c041c82c0c06004501c480103070305541d5940284070195291505024060f00d80d007807a503005a40d00e080c1d100240401c0d000003a005042c1c0d1600084402029181c041c00080e101450100343c1c0303c08082c500410348114403540d00d05d090040450006050b1000c0340f805080c1c94000140c03031458024620344070b5561401f190004006601c0d4421440f01c6482c03d000b1103052074031301540d01c803062071035142d800a490094550701007010f241203040014a000d40703e02c050070001c0d0301c050201e552454444000038480c2820030394402ea030000c2c2c02140b0306402c000020b48114040150784440c074850901400701041244c803c078854042505410180b4810000012120381c407030280c01e4a40c0301c41c4042c021840e001002542c143d036840e82c00103c2480207518841901c40c0180d22000380d01c3c20b02500c03058062002c2c08911242d44140b000b449a1504801582e00041c0d1070301c2d1103030f107aa546041c055150080f003000507010b000301c1c2042c00030181040d000101500d05c2a02da011440e100b45000015 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 241378156 1250 241376906 241376917
    0x30a02090d1a0c131206060509040b060f240306010903020901091e020705032209060308030402030106080102030f0406090c1802130b0408100213051809060601020a030e01110109051209040f02 84
    0x70000c1004c1024805c0c50720484041d0b0401e801901700042c503607201d6022509000065405440c0c0e40c10200401c0754929103000c164100d004c0c1515112051300350881a01c03c070084604071220380d41130210008409901ca0a41180191380080c11a011540d40341140c40050540d01da117031140c0500c140003259065030034000c660100d5840001946400703d840480d4050640c1c2094031221480c3c01030000a80880d14020100510b000304019070352401d1900c101403c40d6007903030011080d41d005004215421000300072590b40690002d00210f070f041001d2a203103c0700c80035500710304911070000100380d01000f910703806804100c06403484c83c1041a195008101c0502a5100d80d0003940e1103007040c03107458900c9401910019009000c0c00b0381041d11800010b1104404c01400d1240040c14404c101c1f282d2010052107400c02020300141c0f4041c521920000c06c01c03281820a64140050b00c0b0750b5542c001c0f0254488826940c01405036003041c01c000210700429801300d02c42501c12410b151120080d1002e901c200c4a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 241379406 1250 241378156 241378177
    0xc0509060a0308030a0e030406021005091522061104030b150a17100903020f0d09080a020f01020f0a05070f09150626040506190e070b030a02090d1a0c 66
    0x32001842c1d41d40c3c40803180d1005048182c05d40d00d40002540c2c4000400140029021913009050000c48810022040310801090b0342e505900003a0955000c04503216034135007042d205100c7d1911f40103203804081d880980700c640200315602c1c140304000f44071281da0162094038441d01c580034850329002020881240c1e0304000c02e90000003aa401c00003803045482403a28040000144c0310180c000019440482e0346042084d030161300101400442c0c503000f1f01940564185038101070401d281009003242c0d071411080002030250045030310300142607000f00202501c10011000f242c070a024a49401034848080380b1540d10110155900404e00201d98010252481c011407a21132425291120407540802c100c11100100111008a141c0c503149500e0f40a1040b40200d00410160a26848901c1035038884004502ca491800c2c2d5105038900000c01c030041290300a90841d80c894840a5145000b441410519075100c0c000000380c3c0b0400c1801c0a101d101c1d0f140d201c2d022166a5a1280d02140340c4c803681d003409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 241380656 1250 241379406 241379419
    0xc08010218010e0d14030703090806090a0b060409200a0503010209090a0515060c010c0219080304120509030312060301053108130603020712052a0c03190c050906 71
    0x80030395480303a0100030568800400b43e88548041c0c5d2100310200c8810a005410364000141d400141908031100400030048003000b0310103480c02081c80741d03c42c90301840003040d0385805000f1400941d07a07600400200350300003603003100304500c1c8211401c4e6036021104d050b000303200c002c01c0040d1902e010710a84175814406010803036203a90305801d0a00401009002910b5a4007071400b07500d440d1103102c090301040300c440000113009501a00d0103450540b0384403ca0344030350303d036041c214002440c1c0c0043d41d03001030380540160b003a14070b000c0d800e0b6014007440d4000c41e018400403c0407030f040411411209c2c01510b007580200200e884450840500741d01c418030992182ca000c81140e2003642e41c6148003064140140c403020700f005142022603039090324542c0004006034012900605214058580c22081c60740c40c2030240c07600540d44400032a41d69400015448034501c225642d070040000e0144003c00b890003003d455103a040c6607a10001d036000391800b900c07685080c010104450510094481c007036030008224 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 241381906 1250 241380656 241380697
    0xc051c17040506071b0803070c1d0628090f0902040f09170703120203010e01030516060e06070f0606270204080c040b040b03060f07231b1f090c080102 66
    0x30340017000301c4021001e08008407034400044a9506001034415148074201c0c3c03040c024913119180302008900c000c2c100207420f8880c188050b81d922007154484081c403da2482c0c00030b10342600c507520366108560100c010380c2c0c10140c0300000291554040b0a4142c400c5500304030076410080120112080a10700074149038154004641900650307020713250240c030915148140d0182d5580b010300740d030004e034441080142c036040140100310081c4585900d2400440039844c405140c880c0003881c55409205440c000d2070005400c0b0184008204403680c128ac202409101541e91041503400281c51a80c03a41981901c0420800c0380c198103008507000c64200707400500808403071204100c0100585201c6d590300c5075070703499a031039039440c28401c1038801d902540084403a0b00e048403018014209100c14a0321312a211a00f00035041e0200301078540401305400204011098000e0390303443d08146410900d04500b0316100080c1d10101c6400006145205030103804950380d85040032030031303401444024041000d840a8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 241383156 1250 241381906 241381913
    0x70e220203070e0622060303170708040210020c030724050a0206010b031e0a06080607050a141317060a0b01050403030c300203210103020108130c051c1704050607 71
    0x1070b04080014003580f54540b20a0280e0020b5405c1e10070301500fa40c841a04000f81908508007a442c0700b0074100c50300c01445e20880007062140b005000a01c142d05415049505501c01c01c15a00700010107411651800d407500c540004080b40c00b000d020200c0b038240105200203109000f80c075103005054000704070b83e90030711b002d12546820040c84030031004a81500b440c031f003041100210f4050100000d0000d4680d08102001e402c1c12402000281440700070007000c24025030085240c1c0c280000b003428a41c41d1011395003546011566580640b1030890050300d1103048040114900c3d001d05d9501c002008005400001134401d8021440040c0101c0c042c0782070100030a00040390791083e03c16205c07107000303950342180710300880200440c02c600040e440400d449042550704084030120141c0107030805d600390b03d0345d800240003000007072818400262403d800020400c0d18501c81d005484000c120280c64400e103000c2619950800304181c1d240385041c0d00400009864208580c03e07180060825441d109442d06e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 241384406 1250 241383156 241383179
    0x30d0207170307020604180b01030b0f0112020c030307020609210316020f011e0b090c160f020a030f022d0d031403042a080d120e070e22020307 63
    0x11a480000d000c00c010f0440181d807480c0050020301140310b02c40508808041c6100220340140c0080381c10b240c82d080350030701d86681341c001d0304003410401d00c1d09840302e0105c0c56240e03000e802555620a05840080706000c803040c2c02280c15840b80305840308940d0361000c009039101e243c450f2001e015520307103000c00110b0310030490203440c800c8100a90040365020024001d00608440c50740b8044103007100d6100c4142402d103d203003d94200044120345011540c20218646c440620030302c1d0300301221500c10981c4000700070041c0e040e4015580c00500d45a26155203050000602400c3c0d00224801d1b95521415161061418815110900c0700303011200f151040c20103008240c0030591040e014441000e54042a00040300002c43c4201d103d01071780c000e548034034a060b100e006542d0351100e049400b015024020781c500082c42c0c000c4d00c1541d24000c1041d005a10640c03004110311029001e150096160114507610b005804030b0150341200345424150840c0c13548000c58080b201300003541368100ca04200503850080c3c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 241385656 1250 241384406 241384439
    0x11d01050304200904060b030705010e0307210c0305100e012009010903050111070201030605010906080c03040204020c0d1107050a03080313051501230a0506161509080d0b030d0207 79
    0x241060780d5908520f100040000100700e0b0100c99580e1244508440f9081c01d02c40c2e00b000b08420308100745d05009500c0040c1c1c030f6455902480c0c00a01500008880b007078001a4103214040c3c20040827810291203090040d26001d030490407001c8241040c0c02e8992140e8140720301c60b4400501100240003801c0c4406003005640606c0f100e5040005003100400496000e01c5141203541d03038580310759032302c4401e4030001d416103019038010741c103000b0301c00e9003080490b81103004298040400c5a055560ba6150310000d40240101c2d5600b407440d2044101c3c1c0c0c101a078100c00c42013034481303c01044500860741d860070407950ba0154040100310b15002c0c030200c1c14080558002c00746481c4110705654035580c0312184d40c68602e0b402d07442802400420340c05021103010b58000c10034045d00c141c4659982a0401020648a02c901c0080e041e02c40c94030325481007444091040a800741e071411070140134003410780c20044043d41254058800803898110045d446140001b090310002c80e0300c0d00031307012152800800c00c252550a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 241386906 1250 241385656 241385693
    0x120a0311010b031509070501050a0f0f020a06090f0303060e1909020d120816090b03130213111b0303040201080f1b0a05071407051f1b050a02011d01050304 68
    0x94003400b8986076001d00460812107569040d03428180f510a0341ca61038100c0c070b9402a41805002c01c034201080e54010002038140e540c83c00d00035a080340e0340074100c2ca40006604007828580ca03000d402d1040000201c250310049010ba541401003c0d02c664501074001002c0d140c40400c1c81c0080b844c0c5c0310750342a0307800890800780020040543d295171070300d86509a9981401c5100020030780000c00080d520416101817901416141c01c074207503810030746400454030000d0401303a07a44000010700e82c1155a40d004038070341300183e8072080c4059807145024003e2504801ca1134a12244802c0603c00b41003000010380c2d214a40594800444d0b40364413f81da100094090481500c00c5011000320385281e545400404d84240e40ba91610307580d0301d040c10806242000c107003400e401c5400541081101390b5070b041e0192500300c800001022203541440d020380e140c0d4403032005a0700c0012440c08a1081c014082001420309000ba25080c2c00d40c1c0c441c49084a241900603e5640442c40c00d2000c82e001c102d25100c84a0960754 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 241388156 1250 241386906 241386911
    0x1e0906060b03090a0b0903090d110d060c02060702191a040819020a06060501020114041b0e0a0218091902030a0608161401050705070b0a0201021c09060506120a031101 73
    0x455007000c8a1035032044812240300e0340958420310400c403010b0041d03039101c0001c0000d9420702008100003141a40c01920292400d06510030700c1c0303c5544e8082c03811130010741c040d00c10403580c014402d020352205000c6600b40050700510740e040515007282d006420340700c2da0024041c807041c0c030780f107000c1525a078001d0015a1008824001802d242c044c040c040b030f040c501c0030b4000341003030040c9140c10004d44040e900060304590400c00304001c20f078007842d212508941d00480c42d030890305c803a8144940b0000da9501c0404001c012030b092040b80403c1d94010710680c58020a080301b40d20090003880046041030350364041180d40b03070318100003403503c5602440c1c00c8a00c030070b00856900c1c1e481d040503103131a075a0000c0284420054004100d241d0b180d034182000c054080c24901e0802006450359a2960761038440c0105001d0001030f50802c0718800c0d41244ca04e40103001c00c0c10f409400c0740c0da58200410224608a07111890000407400a192000c94400c90358080d4005000d05035403550200d40050980f0303480c2100e5134 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 241389406 1250 241388156 241388159
    0x1111b100309050708031c0b0105090405090f071d07051e090f0a03030302030a151a030604060f08061b130b1e0c010c170c120705070503040b1206041e090606 69
    0xc80900c4071300300400700307440216180d4440c070b805921a490004200c1071074524101300718020ba60001d00307861070040c044074001219513526071082c1c24145180c00001290080e4400030850b8000040c1c10724400d20103a640c40035681e140c0c801031740e00d44a008400d60345c5c40b40c0041d201440c03061302c074000c188145c4007030269200d8607a140082406c4030a141c0049010a030040708004d141030051243c0d1340e48440c000300002509180540621903495611085954030f00c00000160880c2c5840d00508010691a07030032956040da40c001c400c0c1c40c0d03d401c0c2e440b1017455942d200904c0b40c0c8500482503e00400c000c5083c6040140303070440119169004584102d5081d00701004881d103901140d0203000a055444008a0701d40880c983c024000792503c1e000c80b0307a40001c030307051000300340701e42054030074041c200f503098441d42d00c442d00309071207074011001e0043c054800041c0120745049480040c000c0c1c4014400d40d4106134841c8002c0105542407800303000140c0c0c0000014800d10030040c0c1041030241c0c000c510014446 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 241390656 1250 241389406 241389413
    0x30c18040c0815190510090209120601080c0307080604030e0907111614030321061c030f0e010203072d1e1a040b041709060304060b01111b100309 64
    0x3146842e0f8403030b4515140001c200d100340350529005041044000c042146103060070b154074003001140213005415601145500075501c800e00c13000b0360b0f0300d43d800c00c4401d02d6954252003943c0b4001127907800e00a015a84001501039000104140160751646a40380c2d01541380c800c1c0201c0380c1005000030204200d201103417008020511146400001000c0403081850512409546011030858014001c2c1d00070801e443c2000504002001403a00b000940c07803041c2c0340c007000101c960346640380c02050301141441c5102090b42003120203416044a0311041100003c0100598890150040140500543d038003890360b01c50100642d41380c0c84050381c0c0d0300302042d82c46450706015141c0c04519080c2d0641d03030300d509405000100c4403a04104400d00a012424a001c1e83c4050b0701000c0901300805040c000d40301d501e414114dc0c02901d4200300d018000e04c6d1286850700307010024140c0d611049000c18030120800882010105d13802c0d1100b108022034845410552080c0000654800c2202082664600303428001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 241391906 1250 241390656 241390663
    0x30403090b030f0115120c09050301050106170c0a0e1e1804051c020f03040b03010f080105010305100b04110c0d080c13061d061306090815070f0314010f06020c030c18040c08 76
    0xb0f03030070640c1d072380200941858180b40c02c441040e04080c00f40244800ea034000c0308101c503001941700c036a0744e0011380c40352600300d02030729202c81c0322051541c000d90b00b40700450780000d000300880d0080011142c25a1064403214544030011055502074099003080c1c0c205907072181080040d1402603854411100384192101c0550301f55005500702e0702c08924000010003140c400d020441c4c003d4180c1e40000c01140d491a581c4640c1c1d900309454a040154650f982d03411541c0c0d80e50320141c1026004402140d40b043c0d416012070321095030400b070102003008103010030b0b00080504140c2d00d203a030413072029a00d0f1a0a114007075030b07445032450055503a05200e8030100741a440d1240900221424090040b00c240c0c1011005021240039410007009688071000c5168104c0b103010035a600010b90707041522884c400400220083d01043c000d50b006100000000104401c481c54114200c0c1e07019401c3d120741c01450000c25031140696002d0551010500d800442207074214940386402601c15801c40c1c81e842e40d280c401a06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 241393156 1250 241391906 241391921
    0x2031302040e030c0f070e06010825170709030222020409141e0f22050703050c1005030112020907171608010803120a0c090b070602030403090b030f011512 68
    0x180c0c2004c500c040c01038100b04648a08010481c01500e8204d0410020b0540d43d10020500c0d4101300840e40418100d0700c070b01c00e02e0191840d160b524000c4a150049000c0c00b0301c7c491214420390340a0310703000a401c00d80304580d0001500c0d4010403188160385824142c1c0070406500e00b070202402e500300400544040c01c3c0c45080407049008112100a01e0200780c516010f0040c10703110040414a00700b0400c200c101c212100d60b0140c0000201200c0100e169804c2038460385415000b05a84160b050200a001c03001504810301e1204469010080388031007001c0f00e1038013080c0300d95018003120b0140f240c018541440302e294044c2c20b918200d1088261142c5c0c086100030b0540e080c4162181e880e075002c01466112034441e0140c0a07150003189000c064091343d00000c8002890604415a41e1501e480280e12500e200030040ca80c0a03112030700d442e2a0b0605034020360050300c045010512034072000a4014285090320700c125200c0080032542e0303113032007101c4141122115480b001c00c5290400c0d081020711600c610316 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 241394406 1250 241393156 241393181
    0x90604080a0c0e06010206040809131b03050f0112152003040b0604050f190b060d0e03040e06150414010909020a030f0b010503152106011217070201050406030203130204 74
    0x41c00c2443d000802040580c050140b5046400070070401020031150030032681e02c5413059901520b400c5560107041d00801603170b03003101607003000103180002d46941600828000c031014407a00030566a581900f400d0794411040041035103025804480081c91103034040050075100c4c1c08280c001c60040030082010703034800c4404413003541403070741404080c1c2810f200d16503000591800c035100c50308055a00700c203100a0801b06031410b40d00c0300d0b03c0d218207403981000c2e01c1c2110003005013440749450382c811187e101e80142c0201d01c094445180000c00524000e080002d01050b0001c61515140c10280c074021184800304070b00e4144040c00c1c01c0090a81854030040c0440d602a03600080c2421042401071305840883d964130341008010310910410800b20403620b000350808a5101030040340c4220704600346a500c4ea004641d5014071000002d6104a402450180c14415040004165a03600420b2200c2c0980c40c8083d000900a100510545010f07500841d0801a8201d0001c100c03060740d8005826903203119030707031b5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 241395656 1250 241394406 241394423
    0x5032505040513030908070e06060705010603080a2307081c0204030c030b070807080c16030e040609060e070503010b04140301020c06040302030d2702040915090f020108160c08090604080a 82
    0x4e06511a1500f40688480b40c0644285031030040300189170000a050310b0301c500000200e03501005001d41c4284011a0711031000b07500c4100b08040609414400d8600046851240b1070441403075240e40200d9001942c403035050303418402240a40d1a4090401c00c0304030500d41d0030000440400d850405c8100150300c9208000480d1501c0780303000b8440e660203460107090003004414092460001c5040e80c1900280b06c07040642c0c0569030030100c90200050402da03810614018000c10300640540040c0d00381d400803031668146895071681103985100074814658403000600090002d4441107999909040c2e0060002d82000ea40301e0001e03003001d50036901200540d02c00034401c1c0e1080003e0145548154a078685005a581801e4010b144440303084c0009100b560395404030803c201e055409031030341c3d18504504110552203031034183e00855180006074042424240003900c824240054000705116075036a480300641c26641c5c01c100b81c1c00c02a0150341c080c109120110784c80f00b0401c0f40301c0d5414001e6004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 241396906 1250 241395656 241395691
    0x8090a0f0b150904030c0b220507060206160203070b19020a11061006020304120212060907031b03020d140319120c03060b040b18150310050109050325050405 69
    0x1045264150b601c88540512005002c00c80425040340c000b4403202d4106181400c00d50f1400110f040c145106601c03000402c00b1000640d0501400150120689089400700d50071512401448603150045001c50001680708004e41d6002424005605800375000c0c00054100d2034529042ca081c1c2e0040e050a000143ca9840112003031642001441d801402180400f00b660f0704107103009440340320301c0c02603460800403d903840e421501d40c0260950f80c01d03050070a41e10a41013109041c1d41741c031440e10098802d6900701c19a155000319007090a0212940140030400502c016581c0c18522400307103102c01a9400144800c030f11740c07013017071810341c000c8180b0390742d045607211107103021800322000c2680d80002c0615103002030001074070300700444065404000b11542c44922001f1281d039550700680440e90440c40540d00c107204665620080d600816208c290925459201c400448240d2403902c5010340c144d101c2c1a2010002c24541e03175228030960424803210a450301e4001103420303113106a40742c03904050000d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 241398156 1250 241396906 241396921
    0x303020c01060b030601090b031803120403030606033b03160201140f0f07080d0207030c0204050906041509060e07080a02010210110405130207050a080d0609091208090a0f0b 76
    0x180b44042e00c1c58801050550400800080809000f030190407510040003020a0700c83c1030708480c0301411008002100e5031401d8200024259100c20b8070220003290900401080d058003a0003900d58108a141429540d41403818500302c100201c00340703450f8018190310103400000c0d024401001c1d040550078402ca0715034154400104000101301c50440c410718140144009019000f00f200d102c03940b919403040d203420301820013060901c558100341404c0c0384001690010503070410140d94000380200e030204000e84e0380c24055516500200d0b001040011043e50084180c40c2c03035804508154040e10300004c0781c000c0f0440c43c07880c0c903100380c2141c40154000480f00c01150390400c40ba81d160311400c1014400d160209800840c02d003d28082d00348034408035030368162a0042507054600140d00a0100c0350364940318101800c056100070b081841359410702e0b00104049410f40070307040d001644110601448405004215020400030b0f103807020034000c542451001c90000b5050410141c0241d45294081c2030404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 241399406 1250 241398156 241398161
    0xf010513121206141305040203100b010504170105011a071203050a02040e011d070512060105030c0d0f0515040605030c0409050c120312010f140d0c0b07050c100302030c0706090314070303020c01 85
    0x30b00680305e00e070400303080000588010500c540c003d2007035000031580d24000c0d00160707000d0017107801c005003145000c18510082203054204a0403510031100742c0c4040002e05005189500c0740e03081c0074101144074401c8100c0e1910135408242e0141001c1c1d0010b0030113888140310310b0764180030b0b80841911035002e0810840b4401400070140c1091043c01d0481c5005003124061500000042003203061210100020b920714400804441580c545510204109020310001c4d000500c803d64a070821051030203881020340c102885030b00141c54008000303210b010f4a040412001c0c0c0320102d42180c09000b400d80c000e410303440d40c43c1400b8600403100055903c516907843c43c0c21190030144c0c08082181d002e102d0820103070607104041d694110040d284003400c1010750510115100441d070110b480c0f00c200160080500002181b01c1c2d40e0310b00c04071034001402c0c80c00d8070110240e00056681d80c00040080203440c000800650084140911900b800c013044140c10400280f40d42140340282c02080c0c00040d10f5108020a2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 241400656 1250 241399406 241399429
    0xb041104020c0d0309020f0d120e030706051b011b02060a0e010b09010302040e010e121c0e06061c020a0923090d030e070302060403030906020f01051312120614 70
    0xd8400718104098541c1540e41c0340d281d54206010715642d04603071001d54544840c020b00d203040250030106904880d242810741840e00c0018000000e00078024080b85140200c1c142080300c3c025a1418100030b0740c07036808030310380100c0458070405668403000a105030480f01400c0340c00c2c81b01d5401a00d958906481c4280940c2d2400848038103030b901d00400041c2d190356206049042d80d4041d10005007041040700750034010003113103036121001d00c110390300c104940e960b290051000342c61840e007054206490309600c2d02610340310009516103820040c00501181020000501150041000c511030300130650042054802c80780c11501c4a540c40d8100e1034203004941010703402142c240c400e0003c203483c1420b012620390030202440401c0640b51506020b4030740c0304101840c0516001084155216940c0ca030180c2540001e1103003602500032051081c2403880c061140718411079807481c10400080d41541c82c0e0003000c0404c1016424001701102d43d140400312407049402610303440061800c140d004008000920400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 241401906 1250 241400656 241400659
    0xc0f030c0d050315030106030c081b090115051c0b0f060a0212030a06030812040507061e140f0706090516051c050a120302030a2315010210090b0411 65
    0x10011004a184001000640c12101e80760060301e070348135408403070b0000c4401c0440a0f855800d09034040248062101c100d021a0418001ca81c480d80d14405503500c401c43d045986a8080d9521004114042c026144040711042628225242251046441c0790b5141c000c1c0030787c1000395840c107a45180c0d00303220040280203c41201d140b4148240000e00a45c4c0304402000086e4000002c00801c94a0580380c1181c0302035584424500e80304c0c1c0f190103030020307891812102540c941c0700d200c10000e120b600a0f050b112307501040c264540d03a60101440c042d03e503024050801602c403002002020003854198001d868640d101e80700100d00e02107a41032880c503264050328100c00503800705400f080556102782c4128a80d074051002c80d14826070904107142003d10040b4080c10a854a9441101890303060380151320900c02c1d240e04000c0e00800c04900d81081b02e1841c956034002c404240495601c504a203800b9054600510480394a035a18403521410384540f004e040300c00e4856801804101b000050428000000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 241403156 1250 241401906 241401913
    0x804062a080a0e01120e03030a05151c031704050c01030e060c0a3624080f042d030306050907020a120c062309060411010f1e03020c0f 59
    0x305481c0c4071030510a4500078014010200300e00030080e4022a0004a5058241c0e820442d040c141405c03140c5036841250107a400d1458080054074400c44000000c00c40c00003c1c0c56001c2d03443e003500303000900d040c2110041d014001c005503260300c056220381d03209100c0c3e44114003802c0b082c1590000034043d02c150ba910b15005410480821000a01c06006d0310140411450803900c2064030542010364011640c07801c1c00784c12040c80188105c0000041c6c258101c1e0751007044004014a80e0400072200ea850212000c0040c9288010400100100307100640190241c08504c2400b034101c29181030071103010702402071109900a1403010706400d03200f9440203003815074542c07000e80703081d0301e0007915840d401000810344040301656020301c610510320005025440142000f682018017650280c11038a152101404240d150000c1c41d045c3c00840c4950085501c8540c4140c070400001c0151880e049901403002003050000b00011102401e5004560308001e13600d0060744c0313845e030105c1c480c10500a01040c028561 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 241404406 1250 241403156 241403237
    0xc0a0801450f06061b2607030f0504060f08090f2b1404050409170409020711010c110603060636010804030507030e1302121006140904020306010c080406 67
    0x50b0000c1519a0920600c04680c42d042101c0c07404600c20b442c1a0310000700d480181884146d0800036900800c40b05000c1d44880e01e4000044c00210390602c201d01a40780010512104401c5640c029420a50000308040c140d5541064071403105180203007941c1a08402d5428015100510003080028541c1c1d001c01d00d00350101d020203d55000c401d200c0e80c4185401560b4410741901032051a03001404080070540f030f120382c2c41d50745544401c041d400507081558000c507170103091019907000301c0300107617465403000c803e08800d86030804000d0160001000c0b0f40e0840e8080144004c0c25644001303500c940b507c00560103603581c1030f0501440c0c0d540c0c00203c010b4103111044081c440800d03048000c0d2000e03640d01d80340405514100c000440c400502c6140651b40d22030010501440050300300c00340c24131500b070310001e001403190340b41d1048a4603054a0000c2030040070400c6072005c0e41c28507400035035000760103040c9502140c003180d452041e240e1055105100241440c031903458404141c0500e9654521611740c407190701c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 241405656 1250 241404406 241404419
    0xf03160c05040e071403010b1c030e0d050604020112021204060b0402090307030f05070902040612230f04051b060d020c160b030f07020105040309050f0114030702030408060c0a0801450f06 82
    0x3d04084649c4036203000c1d60100c12042502c21191305030f2031000a0450400e4205626009944040688040703000c140049107400c0c0ca44064400d540c0590b070040444c0000c0c5e150364403000300604081b001290072640800c252801c5450802000d00110311482d9906441000c0781030907418100240c00c51011a4010401002800e070301500e000000255100c0000b803081c601c03050620038184501d00801d919180301308008000008414040c40f407801501520b51806d00c50f0840e407090500e1000044c2d00090030b20940450030b13815806000032514000848802c54001d103140204038401e5400014290800010403441300403440740c02d0b407c880075000030700c0981000c1da0098240f1b0503d00440d07006480b00244400f040e0b119010500042064844850362401c140c44000c1d2070394080d004000c0e1500c64000864070180b8550119401007041c0d54440d00c290b400e281c0a282e91914842d200d6112843e031640608000c580c03003000009007c80916100d41110f021001142039071845404052401c2c134005040064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 241406906 1250 241405656 241405669
    0x30106020a0b0a0603061406041422050c311505040903051e030a060602030f03010e09030c010629190302031f0e0609090f03160c05040e071403010b 65
    0x341a03202e144041e80f6a12241c2c844002d000d40da00282901741400c40c0c22420042c800303401401010252030900400841c140c0004846c0781c140c0ba07400ca000001c20420454124051800c81d070075210b00709903224001c9410000d414180d035905030085a0008100c851402da1001890301d041c01c12070003050000008440404002d1001c034810940200e8840100c0710400d4444c004850050348403941164904a400244072070a03041142c100c86090315100740400d0090000056407280c0c1e8043c112540b46030b0030f001e00b0203032171400581055218841404410101482801104007070701c1841c41d02c00f2511906000c621074048000c0300070394009030400130321000c009420072000740900d0700d090150f501e40b1018110104540903c1e2000c59130f0134000030120f05100600c003028000d0208940c681040e0b2284680c090303c61184a12508150b03004000c0c107480b4882845401c9442c4d8048c51000289960320b03c007080c15542c4401c01a2815004110b00b482402c0094507100180b40069000300030340260354022401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 241408156 1250 241406906 241406923
    0x60609070807020c100c08030f06030105060a03080702120a05100f050601030501180b010207050409050a060c02150112050c0909010e060106020102040f21050102040321020105130f021201110c1203010602 89
    0x78074002c15040030414002d00310011a01c0e4085147d56a034175101240d450940b00c20f071a80c91195003080c0c08140b280c50800464030035030360048e11103480e28005508102031000c1610308890b40703001e03426940c03001c07c3c03060040d8800340314514030204040896800c00070481764002c040d0b034149403170b010050060802e24640401b0340c0b02c0003100020020071400040c0c1c03034020960301041c2d105042ca941c07401044000314008003032510488041c804620345034400d81c3c40d6814081c0b8402c3c1502004010010341c0c890a000900e0b20307001c0e10544003403412500200d102c6600403181c20b5841ea440314103505116104200c101d00600b4244006c5003030a0a142c03914242072502d124400c21007402800a5100d501a009000c2d155030744030008541c1c0c0c96403031400e070ba0002e4000e81554107400071307049000c050500602030244100b0032210414032880050343e64101c454101c102c00ea8000346d40d00300c8003414100034403480b2210080d8841d05503d41c007200c7c281c50700d842c494041c138104004051004200003500016101d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 241409406 1250 241408156 241408159
    0xf030f01150e0409150626010203040b0412030b041506080711100b1c03030c180518041a151c120e030a080a050a1101020307021509030d0608060609070807020c 70
    0x1902e50b414140082c0340e200c045085170703169160017000160250f461a5540d050289407a03010303c54085180f05500700e010840d4081c00200c0c80b6400240060502040300541160340e08001400700b00800114046840289118400c903003404014090740c2c0c0c0112003664003401c107290006c030300842984201d81712031010342c0a46445445864104030350b0364022509080307c01d00001580000341c4c41c11300038007800741795402c00702180403941c5d0181c882d09040c100c641a260b01a203800e8181c074451401d14110310300103200b61884c180c41aa6040c0204000444500501000003804e0b0400c07440001c100e00e10150210300f1b281f0408640400700022400e12034496007401c5070800203084041000402e081004c4001c0013070603a240040c507243c4841d08200645080c1d540e03030395100c421000561401c1d08038842a1000b00169010f031540c03000c49110301900d00d6000c0c0059050f00c0c01c5c448600081010b1b210940c00ca01d4854018108201e00303804c04604140e440744807860121140e0400101c0a511b1b0b030144032845 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 241410656 1250 241409406 241409411
    0x41a13140312070c030c330c1b09151a03190e0c010305070507020a030f02010c120302030702010501060e0f19090204030f1a0f0c0a0512090604061103090d031e020f030f01150e04 78
    0x400a680100f91104050744c008098041c040040d4a01c5000408907000d100e030503c2c50145410bc0b03212425a0b100f0543c0d2040e41700d40d015148140c00d22120f50002420144015140a04500e44040600030710071011030002c02401c10308034410014040d83c1005160004011041c4001405a42c036001e641c4100ca4208260a6089800d80012650044424805048002c0c0c4180750040207030f05070300442c4124816802040140d80300c9008580d8a007000015651005461801021514010030318203140054011450002540c1e9030101c001d0b42c203d44c0c803d4a100107882295024050302c1a2280e041d20445502d030500343c606140703460103524003d85021f00b4040041814910240114200c030400440d48941031074618014089079030301c41c0700321400c0b01c9242c2000351403000d5840c030106580c082c07000c00c006001040d404150440080c00f125031001c1200030f00700603c0646200d2480100543c1c040840d10179541c0c0340402c80e14003290b006074400f5194501014481103600da010001583d03504045401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 241411906 1250 241410656 241410749
    0x313060e0705090c04030303050f010e07030507030b100504051c08030103030804060e01092301150501030c05090909010902011803030807050c0309090903041a13140312070c030c 78
    0x1400e00e00715282d004140c101c103504040c0046602d101d009041181d00c2a902840184c4daa40751040c00184203105217030500350f110000c1680d96000303412240d4440e030395240010314501c403800000c626000003a0150040342001078184802d040c101c8550b01c44c403000300c140d000407440d142d031245498441440054108440c650110b8204845d0f84c000c1d180865100000744814101818010b1b8502003043c8501c01c0940440300035200030b0300602800015040b44050001d10516020041d40645000340b00b0008210041100000c0d0f503032100446406584184000201584148009000b048407c0b010007800d4003990360400000398844440b99001000e860306545a54403006441d20b1030055184032076210a03000104652000000080d00031142e81c0c01c0040f012071aa02c2c0039050314420f20844140396280c846c814854003500401d89845040041c0c01c5070030402c80100141e81a0300800011191226601410000e0142180044025100301e0b000d03200220640c00300304c10084c8680401c47ca09194200383c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 241413156 1250 241411906 241411931
    0x11512080307020a06060b0a080a0c09090b030f07080f192109170d020c0d0b0408070813061806170f060609030708060402120f0d0503090c062d031306 66
    0x412600a5005c5020702401c0d40310100071a0039040012681c001800e031800285c2d140060303014221204986851700c1815504010740100076043c0c10402507014404c140c5600c050172010444c5038001d01e4000041c01d41030128030401d90810026600710700700c52880c0c08014011440d8090201108203121900c1407080010040136039801c41e11307a014425180201248d062a0781000c20079254001e815429503403004550b0b0b0400401041c2480003038480702082c0b0000d00091015402401007502441c001401c00900142e103c1d420045078001200180b10310310011158074040201501034441402e04100c0301801c8a150b4000725001441403403000140300119110340c0300c3d41d045608050014050380c0f990764841000079079500003035604038000d10150301c41843d80d9070b0204001726220b46c802c0103000c6203404a80103c5060b00080d0130f99801e401080c02d0054180d841c440204206407800b45400104252100c51901801d004a614114080204108070608101803196503409a014400041c0074031400c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 241414406 1250 241413156 241413163
    0x106050c0a0c0608040201080604051b0c120c0f0d0306030b060108070c0b010f06080a060e0f04050f420604020d020f120121031205070c021504060201151208030702 72
    0x4401a0020300040030100780f103903014504510841c001c0c1c03242009501c1d031000740404c1725800c9450000d036000803401018030014400040120f021000119045101c0b62030001c3c80d95030000c0c545031425803000710402d41d1104103201c8241070044a0030104546451070b2550100100000c11060402c001080012070960080c1e805000c0e458010050f01031319a12003002e05010030b00c03405004003044107100001d00803200c0e40240300070703180100013001c0280c5810b9101030700c81001820455150048021a07088808101b14804040c13002c2088204000e0090107889000c014540103250080307600e03094081001001c190503500304030141d030700503650342c1c04002c528000d0161010303021034800c00044c4a11070b83d4800ba40941650086000648a08500017541d0070403030f0040e50040c0495040080500c4841d1f06030f00003540304106003082c0310403130711a5000070301442c910603551544d68000700f01441699030901c03400002c41040c40ca1454120b04201540c04186d03000000140f589000100040b01c0b14400d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 241415656 1250 241414406 241414423
    0x504030e100c061506031d0a110612090109060c08060a0608270606030f071d0a06091b08060307060813110310061d130b0405010b0d0606030204110c060106050c 70
    0x2074000c1001302d24100c0c02c0c000c4400684101000203051181030050780c0c0d680c1108200642c200c00040480c0a0742e0341d91901402d1451080c154001410b100104055450305c085078813842105000242c4040103282c59822190074160000403c16000100150703a182c1039081421742c1c1080c203044220f613850300c80c41c1c0e0f4140440f1445c60500040411040c1480c040055030070300542e400c40a5031911603c5e00c0000790b6840300b51052b2111b070030078580321255804d100b50b041a00050600c00206005803201106002d80754400060184900031454680501e507111b0501c6805c460114083c110461520078010030a02001d400b03040c8403003103a210802080308141120490a41c061b00755a0702c1d1880d0340428006020603c0b0b015140c0ca034240c01e0468604040340701e544a03007064114000c8004071a281c052481200500403160703596114440e883c10ba590794807001b10244141d00101d079403403c610502090741c00d02030600600007014828074840d0030300881c02c90705480c0a4541913444000c0040c0b140c2c5820040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 241416906 1250 241415656 241415663
    0x70b010305101413081308150109140a0510050402030f06191a0d02041703040f0b0424121104050414090c0909190c0905060102120414030a1b030c090504030e100c 71
    0x61000000d90541c0109081c4512284802c402340503a984004810542d900f13031843c00c805200403c00208103a640e948065084132110a001c00d00d541c036a400f2900b26070084d07681141a145144c100032261800e080451038202c4c008117a0060203280520300085100c4010f0071100f000d07400701e94202c8403002d983c196130050509440c000c61344280300107580c0c5c80b0342c8240140880c48401038070210300300d0108000c0702c0448071220b084007692440d0069600d99403884080c80703001c1001d2483c1c00828200580104184400054040346e81c4500c0e0a040204840c00f004245030946040c0041205107100030130b2001e4600c0c0d056810b2550756503841440c50800d83d50341200f006402c4003e46a00c244080d0440540c1a1680213801f0040d5448a100590303403408a99410504000c0401090001c4a10f0300451107155030050200e03429107045560b0903400e149028031124005c0702001c410020f016450038008010300610b0010401818107490042084440c0c520081c05005039020759240244039903818000c1540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 241418156 1250 241416906 241416937
    0x30a0f0906020d02040806070203070b070509030a12051b0c03060a0e07080318090a05092e05011701061208040b13030807061b0905061914070b01030510141308 70
    0x400304240f0003500240250301c00c61152400041b0700034000001c4448841e00640c100c2d03040d980d90901190385500c0440d4041c2c15001d030403161400140300081100c101171481d204e403519005028400526400814100803203540504407084460700c000ca005500300403140c3c000314a200300e015110b031805000b40c1c4810010702c0009001c0303064840281e9081034207a07080720380302101d45903074003100242c039070aa074540e9284e0016100013500d00c1440281c000041e044012001282004020280884109074011808103444d51160301e2110400e101d104046e103510120480d14585544803032400740102e016842e4001000a07182c0418544003440000465100c1c40e40c542d6404903141550241140426482c480d07050341c004a6200c40c002c9400f0b500355032000e0229070610840d1000f414401d195114000c0030703c20800c204922080c0440c3c0284142400350b1984c50b803d515500e0042d00c0c0c1030001110480061410341811100d444001c110794020780c14441700302c00c911103030400c03554a100720310400d04001e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 241419406 1250 241418156 241418167
    0x40f05030406090f09020a02100b12010c0905120303070504061d04020d1410060c20090106050304150605060d0923150c21090304121109061005030a0f090602 69
    0x96210004006642d0075441c410b85043da05e03004001039021324401100580c03c00c10301745100b03103843d41c46000724400060078201c3c80701030030110341c1c212140768807808002500c6940030300060801c810840c5084003503d006500c0c5240c5601c0080040c007844c0164410000e611070100d5070788052004050302d012004000b10f42d90040712120900901c8503056444080c6e00c1800040c88546002c100d0f601290021746594010001c55510403080c04ca42003403800d41603600b640d20030342c107840f41b211960203011181c03262656030419050081d44412a403801125907420002c05200e81d46030b25060f41c1385d610103202c01080960341c03450400090a2900542d1008030a54110351762041000600030a11491805402c64140c6401d21500e00500c10f2150743c000091000c0f800742c9088500c00c0d0100d50000c13800c010751f030900c0e84403e495214241d411900b66201900c3c88400002c501d814005160080001c03652115403046100010f0224080148840c01040e901c00034189224071030341005038503690081045555a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 241420656 1250 241419406 241419419
    0x30c08160201020d0306060e0103020d0615020a020901150e120312250c0c150c081c0e031606050a06031502030708010f0b0d0506150a021e070e0f040f050304 69
    0x2140140c1a40180b080460350b80340b8500920811040e507896541c0e6900c43c000c20340041d00a94803459662110307958403400050f20303008501000242d41c0e4143c1c06404187e24030300407c1410308041c1c00100f1000501c030502416140c000d00c6400b61440c060342e031482c3c40300200d0202130841c06018030303083c10116000d04003c3c48002080b503000d0220000040303d10032090301d5030202c503012001396004080ca18454800d00c064052044c40c0c0100710780a24162f420b40034a80e071a18100d40205080390085403140002120a030124041c000d0102d0311038004600b840804401011450315a03c00074101a940340e000c00c58116050300508059a048815007000000080b48200298004c5407410f00040300c41d80003103011ba150070800380c00c0b03401e41603c060502100d03031085001000c000e1305803a88440c1f104a0000b1440d103503c00340612090b47d80140c0042005101001d0142d40c0c0041c1000e41a00720035014070060020750a1141c011810814890f040c1d80c9a10300100c0c1c0600d80391001d02607200100e80014075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 241421906 1250 241420656 241420687
    0x604030c0b0a0204080703110604050a0905010e060f0f130e030f0705060a15090b040605040f0f0501060f02030d0908040308031602010608030403080f030411130b031501030c12030c08 80
    0x11601c61941c42840c0c0c0d03501c0003518124011806080d0040d040b842e005c202150100a215078900e200411041c9415510320014002e0584c9a000c0407000380c50b2001080300055480550ba07201d6030039030b41401d04080c00c0300002e910000465015100311020010b0411000c459401001e480b6042d200f103e50740c0c0d9200c0d03880c4030690400042103440384280d0000071441003850007400c030010140d00b50300081b1401e00d201c04c805000302e04901d541050782c0e010009050303071311401200b0000480000008464102c4440f0005844058003c0d0041c00120303e200320f42564004100c0d181c1814920300000e0201c1d07e0b140010a81c802c55001908004011082c020717000301c403045028002031550000c20000780e4030820561603014512016050001c06d11441d101a0704c4900250340c0b00d8442d25550156100c00c10004d1600404030080920444c2d40b01c220101341e041c100300b4081d08811610340103c4542c91603440c020a001d10340207800d0308000440c40142050300503043c0380d10f4140c0c000d2045d40c40b0543c40008409 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 241423156 1250 241421906 241421927
    0x50d0e190204051501081602120703030603050c0f0f0f010e0303030f0601020d020c0a0335030603280f030c061b1e080c0310080a060b0103060e091b0105040503060403 73
    0x310b14642000b041c229050f40020186149041c0c41e1902d003540e41107011000003052100d072200394090303104820041c0e9004030040c00154865140010b4441c03c5041480c900340100b20040e01488250100d8903c50741c3d10321000304c26107012185584a800080300403140a0b07000700d0f00ca80c1511000c81804010310405040501c00d01080c1d00310f545000741c84404a070748a00121955030002c00410080c0007045480194200c020001c060f80300c0e03000040343e034440d480d0502c00704070440c00c18040240611460140702180d142c001a030044c40021101c20a200d00d150b610300d500401c13943c5616101b0b420540075403030302c40403540c020204200640300e44a00001641c0007148260000e10354001007100948130603c0c0b6258140b246d512143d1666804103410856840035004101d1100f0622000440600401403296003522419000c01c6900c07031000050251521604411913426000c030811540c3c89000a01e5104142c1900714483c0075805040165000c4c4501c1d009244c060080708100300605401015026 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 241424406 1250 241423156 241423159
    0x3150e01050103151104060e04200309061005190b0a0215010305030315011e0c11040608070e010501090602060c0702150406020a05060711070e10081e010e0307020d0201050d0e1902 79
    0x95407a560046100301c2c1b1031802840045864648805903600340b690088190400a580d076000c24122407540c68140c0d0411114101c00da8440400c100c085483c4a450000601c81542d0910580146c0c0383c09600d114468000e0200c10000850400c20f01442003160102030405201040c680d96107a007052038980d401103c0c0020482c560303464400176035104071640d58401c000c00081c0c0e041c18200e80b9045030102c20601c025200c5c3c4119a1444000350703500d20600c0010f144040c010400d45150141d0b01c0802c0b18164000d034144840080200f2403241c011881d140d004c950221010790781c1c0014030001e565901c10040d05510001c01040200ba0580c0005100680900410032900c2e55503540c0c1040301c0c00601e80e151480ca1b42c01c003100400030064400c0710103402c500031030b450b40c1d240c40e03d5454003860000c050845852680900d01e1440d5918802e1007a540f802130041c0145203002c0c965000f0075000842000002c1c100030780060300c9036510017550301251030a07201c5010b55181454140e4084000200c003030059 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 241425656 1250 241424406 241424411
    0x15090608091504080702010207150c03030b09060901030b0a060b31180c1b0c0e090106081507020c042d06031703090312010303051c1503150e0105010315 67
    0x10341c05401c00100000c00121802182041ea035460340e40c0c01c2c0d0340d088810124107600c01c82c0300100d0a0b400e00d030344980e61400103640d05040b000040c10000d0507034600b48015801202c51006210180d01c6025100d415a07400110070642c0307880e9098900000d06040d40010316003440403a0015560901200840c0142080040300c031010820b502c0b803595020140c0b00d41d40c00901d007440d082030b21040702d42100b940103002d4206800c400c400075003003101002083ca07003202d00c403441807410b20109254102c01508418641c0c000c00ca12410122182e9032009211381d1241c410076502d000500c914070800c0301401510b03020300148042100c00852508ae40301c020f5103d1070b0340c0045034400a9000462060600701c941110418003480b0301001861240d62015140d00d80c0c0c0e000800c1102090300554a8881c001c511076981c0940e14642100718001410868121107040b900b0031140310504900caa41401c1941d030081e04001000080c441c41c0c9000f01410200030030b0300d5081c00b0001042c444c0c02407000c44809501c1909 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 241426906 1250 241425656 241425661
    0x50a050d05130806101a0403080705010c090b130905040c051e03120c030301140a150c050d0309050c1011010614040c0206010503071a0d05011403010605030c0109060503090715090608 80
    0x81c0c0351034001c01c0380d00c1d0400d4921744404028515034000300c183e0030448010300c03e10306502c03a1500011a84860000e0781c107691680d03025804158028008401040500c41c21818408040401090003410f0301c00c103440c05464101003020b02110401d28001490010050b034450401280c2001e2884165202c06219021b20000140b00154420803a40042005005149036a0a0101c0b0405032220710141d1f542100741118082b4a008101c11450740001032900c4204e035511072464100c1c508140200020101820030b090780c1c000507000281551452001c507a607941c1030700040c2d41140e84201e140c041304e24170760230020000390700044610081c51154054606110100000006981d960802c1c070402d605640300a40402c4040241e00d40707940c5481d030b0382003c1c0d85420b003d0044141592000e8010b5426500045e149041d9850248524001803c068000c0c3c444140404000f84c005541c2d0f02c540c6060080000c002080d40d842803102c07401500d81c01c2412045541800350080502e08940504004101190301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 241428156 1250 241426906 241426919
    0xf050405010b15130b1b0a031d06130509190507200601030809010c030309061b0e0307031e08040f0f0509090102090d171201060305150607080313050a050d0513 70
    0xc1300e1006240420b0400410b1604107106a075500441840308541c68503104503070599414050400c00d01e0095413812865150107a0303204c12040078035000d900c074401c100903074004075140c428104200e45041340d134015036039208014101a207070440406120070b4500070801002a411028405103241494440d258401c0d2a245003070b0388900030300001e4201002401060f841c5e40c42074451250462103487d02141c03140c082c2d038642d4290392450200d000311145031040300000b25440100740840c244210001d140c0c0c2441c5843d00c3d46c21042c40070708100c80d11845461401030100000031038004100860ba000d00e0240d640424603420b41243c003489204e5641d030008a48609414001c0c1c9141c10320040c00040802d20702d07034404449840003030000400000c180620304070b41404902450007807140752800703c0c8071322b0b200c84c8030000310600303420729841642d003400344c000418101c00c10760380e2000c030401c4061a4100103040c03451900700c001000502901c19503403444e10303080e440405003000c3c1e00c02072144003500b9154071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 241429406 1250 241428156 241428199
    0x201140d05040b1b160210120e06010501080a0c0c1e051603030e0607110105030613050901150602070b07060b120703050129010203070b180102070302150105150711040f050405010b 79
    0x35404e100302000300c2c401d907001d0315090131f13003004641550030b000c1c1948400040e40029a00c2266010285400204c010481941c009061070f600800c0800c04020303201503000044e04880400c04003800c0b04205103c4104042440d907030440c0c503943c01004451868043d04000d0401090310700084001984042d0044038900700321040e6410654000761043d04810110011105500001e0070950320003c0c80d07400c42003600c10b62141c540110759400001c02d030340010012406001c011684510119031025900300200c03510b05050700d080795401000401c0040c800000940d10b2044d191414046005420700007080120541c41080148058010300c4032501250000e24404590440000c3c09600100140741c005a421042141d03c02e221034440141c50f81d00b2140c0500320f8002c218120007692106065403202c00111189600500c41180c0000c00b2072100103000c0c0c0540200c050041028070158081103044d0303540d0b0090701c403405001d44200180e107040e0428034040d10b0000708550041580c0c0e001e900a007003050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 241430656 1250 241429406 241429417
    0xf0414012706060b0f0d0e0c090405061501080c0a111501060f0e040209010915200c010314060d030c030509041107021807050f0c070b0a030e0f190201140d05040b1b 72
    0x200300031783c10091030811840203000e114600c95035601642002c0f805c2c1e035544102150240780280c000345038904d08250070382108820304403910306000405c81004400c2001804036400c1c2103291404642d401c8850350064a48200e00503a000c00d040900b001217003803580110070303041c00c0c0496a24504031214410921049118409021740021b510710400d1006084c0c001001d40c50b1061481e0482c0381c05d070300509422403640e0641410805030420401c2101940c0d16019100d50304081420175440782c20042e00043c3c050260500060a00c004180f4150906005000f40da4032010b01500500c400729614151030190f40c0100d10481c400d01072000155420410380c486207100313444545845250019465414941d074001e5942030901c1d100f240000304841030044082c00c02010582c9011a2201c0c4000c00c13141491032810b880340560380308104030582d00900443c2500c40070b40a003000891805030300a810124802c0c90744070001d43d4104414002000807002c01c261041c0100118002c243c4031641302c1042d0f52081c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 241431906 1250 241430656 241430677
    0x3050d1107060c0512160212060106020115050f0d170a03090303060801020a1d040204030c0305010e0c090c090103150b191404060e04020a03090510021305090f0414012706060b 77
    0x51142c000c2d6200f00c5c0b0000c1100f1124500140492441507001071994150328001a03420f82182004126194090151151980d120a44200803d0400c800310382c403141c21ba52401e200b06104c111242c04d0200201d50120b0032344070144003590751448410007034090f0002c941d04400191500f00700003100501842601e00319149596002441980c1910041c1c00070360308030070507502560070000000014105d40001004600c00c0f0004245050074071842030070b1101e40e80d00a809031261008204528420360115007041009090011382d154209c11a001501c4031038006131100040040e00480300e0341c0200343c0024400d41e5640d801100c01084041c800d40d401588503e002046050841c1283c0b880c1c00d402a146800b85854000b0701c030304186d11114940014408880707240303a0b0004030324442658010001016060950b1111014144044036610a5000a0024090441d0454038a1f0003040a401081c140c040505620003040607010f0041040b000c03070181120564a01080000d0341401c190684800008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 241433156 1250 241431906 241431913
    0xf0e0c0309060a0908160b01090b180f0403091505130602030f09150702030d0804051c0e010503060a0509070f0810240201091505010303080a3303050d1107060c05 71
    0x5030018044042c100c1c4240854030f40400b400020703034840406c104100024020700c14001c09501d010f2400c01120700b0800c5050080d003080881011002d400c035a19030304203034441c40301c814a6560f41011214140960040c06040d0f640302d80c2168078503400809001d010700070b0506001c0311941c5d00c0040c1c0c2e4a106005420680380c400340805843d82c508200303480e4000256041d4545008695400607090091a84480000c5541b50702800180301341048241206200344c20210200d001c1c640d0060f1040c0e440a100300e0402a0000c005040e60304c81884440c001c02010700005000e080c00c0038082c2a04059240000c00a140800007400341070319907a10904990340324022205003040c2e4400d00b00907420b0480407605640d00e445040c03000546100b000030084610030f000243c154118a8010001c01c0040c0c031070380002d400d04102c40c00c0c9070080715560003041d14030b04005110348111001d109c00c0007080e0780060030714001c03002c3ca202c00704d4103d13490250b10034100d01030b107081945800703056a0707100501304003500a51 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 241434406 1250 241433156 241433161
    0x4060509010b070512041e060806010207030b0a0920100c0b0402010c0c08060a1a042a110f15010b0a050403061d0a0c030b0105150d09080c0303010f0e0c030906 70
    0x420002c01007681c18015420380d421178105a005c10146d80c40765112130000b0300c0740910800d00046107160b43d805800e161901d65100d051040000790345080f580805007481c6950380216801c2d0809134403860303a940d4024228004152184030a9a908400600541c01032842440105c5e05620a8000d1407e540c0d105103e03803500d888940044800314407000c030440d0310100c0310070007061141c81000391034400d076103100000c00d141080c12050310044500402ca140950700344103e440c4203040101525900310311581d02c0340074040e66004210f92500f854401c00865008d0040d640c8400c01d0080755980c00c0500300c4004403c0c40e41c2c0e03000340750b90354454504110002a000e00c8244000f0740c0f42d402034180c000c1426000e048420501907030a0411141076070454001c00c0356401007040000ca0804c207801000304a0380b0f03003500f0702c01c00404043c13882846010305030250380e410300d0030400019006a9000d00790400489440e50b860385100058540c580c0100d244021180d070021f040b032941d084c1200d1003100000003030820358 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 241435656 1250 241434406 241434419
    0x70f0f060804120512011205012009010c0302010f0f050603060708160e03010b06040e070f03050c0403060908070803090d110a02060901080907090e1f0c02060705070c050303070b04110406050901 85
    0xb51141c00007a00300f080400102d1707590b01c10b4042040c01390100d04003e48107540546031040c21620060345950340f5400840e043c01c2c41e2803084054414444003800c101b881c0711800c1c40c0c200c0c0100b509051164a032803030801b07003000c0484a50302403807213510264112203494450389420341d18000102c9403691408901828501e00501c43c1650741e103c00300140000c5080b0800c5800108150004d802c89810010288200007e07103a0060700003c881e0500e003401c000b142800480d2203014030603800081c1102d51204154070400611200711105180c20800040d1282028403503652240f8443d072100340090f030f0811008105e503c02240076161070303500400c0240381001c00741c015520410002c054510302d010310000000c0ea1100c0340180000c520022000d40b1101d80805000040c2002d41c980b007850780c81c54449100324054002440301e400070720500b0401e440740102d203005003490255420090301400042072000400c0340682003180143c0c42542200d070142c12010920086500c140b00d01644180207c0041009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 241436906 1250 241435656 241435673
    0xb0a08030a18080a0f030f0c02010f110f0d0908070803040e0f041113020901021509061b0c0a03020a0201030506090603061801022a0705010908030a050306061209070f0f060804 77
    0x90112015019000e80d51005000d080134070741c0c58151042c02021000408040d4060140041d41e0124284000c5001007600000c0046111441010601500030581401003500308800840c2c000320b00102c03852707808882001080c80c00c06200d0342c811445140350101c0c0b0030b4404000e0303905442604180459035621000d40090b01080500241c0315000b40321507420740754481c55406601920340440150b56054800300080c0307010100341001024042c1441846420a404564260448451b1000c3d040313070510840580c2040c80354401000c1940310355041c000c205900444c40d4801d1034001d880c104415902c20043c4008060202c402580c550000340c002043c43c2c0808260100d40000e0000044c10800048044000350101c202004510294a003908641d44420082e500c06440c0a01c0c0c00b6284926090707000d583c0b0701500380003000380304000c40000c03460344415080d43c0040700c000e03521041310300f445400c8644900250040d8000d20000c504040313042844c032400001110265541d80540c0e81c0d07140c864042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 241438156 1250 241436906 241436927
    0x6200a1509020301090605061002010c020c06130e0106090e10030203100504110d200402070c03062a050c0105060f01050f130305060708011820130f17010b0a08030a 72
    0xc2590311596400940c80901c900034070a8841c40000406003003110800c41d107610035081c01421a81814200e2054650104800303122480640c6c0c40b90300e5a4a00340110490f0545811500556218000020f1099808400d240c00c44103030440d5640c041d01d03194030420440078140001394140e803100080304900441e0798440c07540203004500b14025201490002031904d0103072401a1400f0055021750740240020f149a140b030040201c80440c548640f599602100700518407010300b48a6480402d1254610091941d0f402084c10344900b803030ac2c10390000003400c581c102c5241c0141c9503282000081c02c0d0b0400d09280c5e489031805850f81c1d4100900e0450b0283c159000510600340081c042100200241c000c1021900683c60b64851540e29810002c258000031001030280e08030f207080810445a84101c00700c04058000005513544d80e4104c3c3c0014120201e11680c130540c50003990300e100060441c0302003254002400450700038000b1481c00001c101c105810780c00743d18181d070004c0140b260518000c040c07442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 241439406 1250 241438156 241438193
    0xb0307030609051806010504060303140a02030705030a080f070e0307141201111e1207122306030f01050f010e04170d050411120d03020c0712080406200a 67
    0x502580c0b00e1200406841e0140c4800307072944a8002c80c0c21100300700307110440c050f041c00e03503080050318038545000300103861603001400ca26000284100c6190700c00d20484040130703009000c032135542040d100c0082a60000710707202650107000d000441c1c02184075515460540c20b00a0081c0303622130420380e60203450101b4142c0c0ca0352004d030007800c44406282c00c0c000d1904102c50218032a4448092020306000b11040301c4150000c0b000800c00c03201e0201e8403840c0d43c0d42001e068603041110a149220010042007000340480222068025050403102a51807941c8250010f5090300d00801a4031942820b9074010359040c0503680b09000103002120856429076070140c060350380700e403c49140001003010380d80b084c02820286a210410042801a1034400741200c050948082050501d0040c4258440d022000302000b019000140b0b05403020b000c00c4860081c21502000086081c460710300402d6540c8980304000106003004d5a10407071030101c0c400350b02840c0700403000e896103a03101d68a060b0043c24120418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 241440656 1250 241439406 241439411
    0x512070503090c0a0b07170a05040e04060b060c0a05190308010e0408090901081612030f0c060b0a08060f1015111e030a02160b07030309020d0218070315030b010b030703 74
    0x100c0c031075862402c4c2c20000c080600007240c2d1105581481c4041503a004400c403d8210100444040d035640a0704032000c81cbc030700083d90112615145013000160864000c007a0340b0010100d8602b401c0b44011030740c0018944528102c1d1142c0300080c1d952210305092401c0500070070102e8004202800102c2c818aa02c01d00ca11810740c5050100c1c4000f0320003003000c4e080510b81d035101c500d203130494810702d851000113071080409805000b03d0507035004200c1444000103008000c59080d0301c90402c03240e90403000c800c402c002e003c038400b15110b140e0300c1d90301c1d0707000c85034001c5441d0318002085518154072107c80654403a040310809a621800d801c4c1c5003480c2e00107084400788900300303d03a9850520212046018540a030195a0f28824410000d1400c9041e14081c0b000c00c5002400301301a01d035513012212242e500d4103021402e209140000389507403c06240c00f83d00501700c55001c404103040c400c485881422070761000c020003c0c2451882e1855603580c080146070489070b400500031540c7c0c080c003861388001c252502 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 241441906 1250 241440656 241440673
    0x809030c101b06020d02031306060b0325020a0501110919031e080c01063309090908120a0501030b0c030c0d020903010e1c0f0e03190201300606051207050309 69
    0x5172001ca074011100030384144c2c120b40001c02003080354040e00d002441c41070101170650a16440c140c88140d490380340300c4c0e0030320442001c03885d009000740122845c00380c114000b049034a9403020311882e80c2d171200020501c00c1d41202c120001c3d65655000e0f4800ba2a040300040304601440080e40a400d00e00220544d070a6000344101720030300307101340a1344003d06408601481155605c2244413144040c00b103444440f4040310801e25807280d48400362808442441700007044000190504a9030340c4160002011000d41c010100140300c40103400590480c0e10828810306c2c1d507a20208484104e0100703440078034503502e01300142e08111440323801500c0001c100400000d084000211101e1070300e84421100c0701012a05114000c0003078004d00610041500c500b080c0c0c050b01540400661a2904080d10f03c5c5c20004036140b000940e4400c15844010b103204060031040800c40c488054000810b0808000d0f916040c51400314103944a0410340c1c8010070643c254043c1c075207602d24142c5c0d00da04000c0682d4043e00c1507184 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 241443156 1250 241441906 241441927
    0x6030c0409060f0603050a09020d060b0607171b0d050d0504060e060f0108010b010f0e06030a09330903020c0d061b080a05062e0909090809030c101b0602 67
    0x1100010626001c0481d0038a00e8084054142d6134007c040c92800c178580765845c809600c42038501c0800f158880b50028008a007203000031103500541802400040c0c0580700d0000c00c16000740202000f00e080110140d0002400380300300d9030b801580c0030100004a0601040060115503040142c0080c0b00b1600440e005d040644114a0403004840c003604001c02c240042180c02d41c00e01c50325180b10420b103088a00d003804418007600c0c540b013859409004a00000020b442d0040a5004a180d50b40c8103291103403621100b91010b69111105801203595000111440300d03010140c1301d009034403581074010b0901003464008115101c0c028410650300c09483e80ca90340c151000e0180c11801512154075a5a060300b0700c03ca0380ea08499000301054040d1503100b20131030705103200205020321303c400031074150740847d4140c1d412103000703146d584110f80e210300700700440342004904ca010b800000740540c11100341190352410428480300d8200c800002c40e0072000c2d000c51605500b02d0070b105141c0a403802526001080d81c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 241444406 1250 241443156 241443161
    0xc21140a02060711150f18030a060204030308100605070c060c0302012004090513051c0c02090f01060809010501140f060f130e0109060e06121501080102031501090308070206030c0409 80
    0x30440780b01c10b0383da015110602e011140800301700e03001d440e8141040207802035450244580c0c4011160100c0c4034007403005540d410070244061a40c80507081d5140d6650f0b20340680001c500340d07001c8034801c01c45680855203c1c440c100355054150001c100c03072a070a01d40302d026105072009203070541c115500c6800d6500d002050720f1980184445200c070040d9143c0c507229a0744112000030b1304040905000c02000c0c03001c1000002c02100384450b00d905a1404000c0300e8040d0790b205d840101c000e4000c0380c180d04008088420320b6065049640d0b9469002c051350300c0c03000d014200c2d0400d0164008140c00903804141a0905600d90340786004060600c62901900d0300c000401a00020542c0e084078034890002d100307003c0d94126050041c481ca80c030a01a150820110503034a0718020071050040d41c0c0654400e00741c0354100800a4101c0303100401040d9540c4500d0014040d50049032409103205034580301407010751241c0f03640d1048a8100004038200ba8495007000282d0744040c2600e014810b0520000c2100c50031407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 241445656 1250 241444406 241444417
    0x7060b010c061e0e0102040b0405010311040906061d06030601020a0305030601030609060e071404061d060f03130302010c021f0903020309100e0114030c03040f05030d0c09030c21140a0206 82
    0x208114802d03100e004200e070f41910002c64199001d640107100030031101d028942610700f030b21001d0901085c124410010000300307015903444122080d0500c2d00c0002d0717454109802500c1300300c0c900d281c498201d040d9001c0c4046840242c3d19180146d00007003d03030300428400c10286400107014900410a1544e42c6040020b503459a08455400211582401040d44d00211000250156101054146031034000d000c0c5c2009134203040350020040c2e40e2101191961030500704e810100c98036a145840781019114610307401410481103000d0b46c82e14030140030080c0001860445020307990050303820460482058800380440700411000e51205002c030014503138601c03406003840b00842c0c0d95101c8c4080000d00050019401d88030701302c080c050800911501c0d0520108482c0e00c280c21040743c0d00701001c0d81c54503610f580715200740a4052860880c0800c0107552040744c00d03040364000e07440554466111104884241c803100030400c024010b48031040d0002d03004181071a0400740140542d40040480c3c0c012800b254080e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 241446906 1250 241445656 241445681
    0x9031b060e0d0804050709020306060403020607110f1c080c0a0f1a1608010603020c100204060c060b0901080613030e10030204061106070e0d0219090b01020706020309030307060b010c06 81
    0x1224441d000e210010002150001c20624059081d420140c8450751100c07290f0098281c0340d03400100090315615680200d400950303004d48107603a51b114a08085c2061610b41e503586200380800a140726061900d0418040a441c4210b1281c1c0b050200e40d0343c980c10399026004240c003034054905000003088148007803510b00303070049075000d2030504216072141c0c4860000706880d0302c2c10700240c0200041030780303c1c1d4001e06541d000d060069a40485844481c641000d00641d4095107000040c0443ca260303000b086200b00303603c904030901c40301480e8010440620340c00d01900ea000d500810000b00f800c402104001c03103050280c00c00007411846940400c080041c403d0a91020980004040090a038002a200010302a4502070041414241c1c0c00a2031614902401072054411050341000e56640714001c52400018111403070300c8964a2410f400a00344036820507000d40208080010070311300100480e103032480c004010b140341501a41d1008010031851a030b890400101400c0b86001628511500381002d08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 241448156 1250 241446906 241446911
    0x304030f1e0207030803090a050601180c030b09040209060a030605010914070c0203120f09040612050d08151003020d050f0f1303140a030b030703140607030501080c0409031b06 77
    0x21030080c0641c00310140300200e926601403012401940400d40200762a0310150a6030b491320390040d080d00c1e02e00700c10000b9009010f40c100004d200408000c010310030102c121811b0107200542003040e4212610040e4294000e000c0200007001071800f254031590098000f448511b4058076902c0303072005c9450903040780321f009540f5030184000201902200e98095454076042c007692015901107a20b411001007a40d00c0341d07030041144054202e285040d507020329400341040000c1d075038801c40712084100c10a410307141130154580c02d0440d1032007890380f2841818410040d030740d81c0f4052801c1c0f01400503000d25002c2010360901211031f5003895030040b14080c254440c80c518281c1800c2183c1c080c0c0c41e401801c91145801040807070300020750030900071a01198821321880e111100340400350060218405010b60500440b08040204550070040003440f2580c4800c440d000d40e100706081d02190000e01602d000c9901110b841e284a29160b005850341e00d100e0b03d840d04060070704444449403d600c1100c01c581040c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 241449406 1250 241448156 241448177
    0x201020702090a020306060d0f06090c09150f0207120303020f0403210509030c0d1109011211010e1e010c02041d0c0301020306012c030607030b21100b120102030403 72
    0x6464001282c10483c0518114518108000084c92611071600400400307900c0d006102c034010120b80c0b1000c014402030740140300305858510005c2031007415000f4140a1030401c008039007801c0c0b141e1060070620449800801d0001e0501041d0380c3c000c01188000c80406408011a441120407840900011441fa501801c0601a920068400d607010480641c00704041800143c5165400040200b4081030170b0350715824415850070400111080c501711590450012000060018000810b4004190085c0c50b00302e07602e403201c001114a07000c0c9000b015800a0407458569003030198180f040c0003042e0504107c00111140d40c0440d0036540100d0041c920100440303411852a030052041014101c030071030085156150010003e00380048403102c0d40891680c10070145036a0030003403220034101100404aa056181100c40100a06040140c4a00074110080d80a41040701051010000045400540305030a0742c0040c8500805001240583c040d594444040b55000203100950145010b50394803076450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 241450656 1250 241449406 241449409
    0x50f0f0a05210f0105120a120206040515060306040821040516050d20011407050c011b050a06051b07140d050f030c070f060c020105191415041503030201020702 70
    0xa1240602c402c040d06015420042d00c244071200c0e8a0543c1c0e402c68151004191280c609481e110340c25000600300c8102c0756445440c1c580000c0d54521940c410030403201c200200300d6451000c40e0090311425090b9100401080c001410400a0143d8903001820705100c1c01a00c00141090308003a02c058070990001c0010102421102e00d01d900600401e8030110f10000050b82c0f09284120751003001c1c10b00c18407032686c0a806a1103100d54800c81c0140014058070b440c0d56040054072440323140c1810b408207078501441c518401d24000120441a0040068054408680c89803800b41000030030f4042c516031006441115000510003a0030654000c85990410401c915400c51800078030714400b0701030200503c60100c0d4851890122a4410708214a807a140d03074082c0303000c140e900e410b0000105002e00b060803e40100764158001c500c200d0750344940d0a00c01e21401c2d0650111000040d228029807040360005501701c0910f003c1c06d0386007402500c0051000d1401c0e0041c00030b07c0d150303002100140d4000440000b075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 241451906 1250 241450656 241450687
    0x50c0d0903020a08010e1b0604030b0a14011508040b22060e060f04050319020313231c11130c0801060f020705010e090a092102060f040209010303050f0f0a05 69
    0x140400200800855003040d44050361024106280e110320b10f1f00303180b01442e40e2a007100b0303100110b03408011103500d0304241d40a0030290903810310303204280d4516000041c110780901c915420001440c2c032000c3d00b5440381d80315843d540c42c000781940700c10300300c2c6c1c09902501e000c000c2d801c040d0103024060004040f8542c002d010f05060780900819522031041c4c0502010030360100813162001140a090180481c1c642426400c40c01001c40081c1c10240c40480016005071034090203029803c2001f289030710341c54040c03c009e26400c07890403e180150f00e445c001800910000e0703044000940050000d83c8045000c3d190f40d00f80ea4401c100c0b980054008001045100d80105030500d0079682400940012410403000a0034000c4606a48d84104008004100580e10503400041d95a40041080040c2204510b03001c03060010842210018441c0c80c0009807103148580030300740125801861251580d280da10708130341c0c1d07400c9090010320101d0104103252003262148000c1918040d551510b680b200e000c50b041c0c030f20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 241453156 1250 241451906 241451909
    0x30a09150c0305090a02060f0c01060905010311030f070b0306040b04020d0e3d02030a0b030a03080601090e09060f09030d09050c0a09020721020f070801090c08070308030109050403050c0d0903020a 86
    0x185175100140c0000107984210690301c01d202d42a00c3e003034075000280300e00d81c090516076012908051604001005004804010413464202a4201e808480d0982c00440d5502c1d00c40c0f01c1c04400820500c0404c4141c501900902e0210301c0080c009400c00700000c0301641100c0c00a403d220703959000c05412042050240d00300518181c81401101c03860888035480300c1500903c03510300303c842c2d074004001190b4100c0c1d035002101c2d0400240482d000c040c1180313409000a41c1c1912441d0228000300310008000f0741104501c0c0c403030800303c800b410840c0c0b41d5003410642410041c08028443c0024401880c00059522880c04894010002490321004440900501044e150440072603580100050408541c98061004041611101131000680314071070032410100241c812540034020a02d00203541101504203058260003400304858256840080326601d07005803000611200080c40104031440680e800300350300c580241441031403c04c046017682d0501c07071940019000700341c00420501c29818010316000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 241454406 1250 241453156 241453171
    0x1309050f040f020105070606032103180f020d03050702150409051302030d0e131103150a05030d030c05040308030c070308060405060f0d0204140c04080c040b0d0602030a09150c0305 79
    0x656605054980c19840d0301e54102c0a414000009107805c02c002c4079034000d170020740d005403a074400490007020f00ca0454040e6445240081c1c03c01e040035000d1520b4010801010b0f5010032103144086203a030910081001c004400e070280807041c0078002c05611202401d01c001c480002c200703a0340e90309200f104012a00082c0200700e40c9410b01880c0300058600045090f00492603050000c0901818000035080801411804140c1030404400400495840010794043c441035003070000c070040c10b141405018811840f440d40e05510800380c02000720b010ba40203121001e45c601e00a45060b132a51100348c42a4003e07900c5450702c00300010a101032503480803040d0f42000041b1400d03c62410841c0004801e070070b04680b980e205105c592041001c542e03d0f94072000d459041c0c6a500507552420000d040310035003142c400c1c04018040c019924000f80350502c10641000b074024800740c0c8002007516510005d4000030031500d212559883c2200c0401c01d1100380f14842c000003407011400700380205009060ba6405041103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 241455656 1250 241454406 241454431
    0xc12050709060e0f150f07060b12070b030c040801061205010506092701022106090a0203070906120e01090602031803271f0203070201090608151c0206130905 69
    0xe0040c254489007814081c40111515520000b13084006010300030503440c66902e490700060f044c40900100d00140c02e400b8004e0701c04025440402080c0007118003190304168180d08070590a010744001d1401860300301c5180300b04c20f030400703484000d03640c00c554407a007103150349043c4d0030030340420400c0034000c8a61204040d54450341c039040111208601191050890365001d02c030507100b41c030480742581905c0c1c280f07206101c0071b90344240645c18180c81c10810f5983c01c1c001c00c401400948180f50f45c0c001c0302d00920b51503845030f03412b80ca840300480714465062a1a0103080e02d900c0b0038071102c0400d00417076183e207001e9900143c1e2402c002f04103150440f180d10341080f50303800500940900c003891110245011035095222110085440b002445202c14060040d90700c40d400c03111003e40700c2d8004003528000e07201f078a62025050b100c4a081e140544200c5402c4000800800480f00300d0500700040001c01101e25140301e1006965800035085400c61b8040780f02c0e24240184c204110003441c040d207504446116240c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 241456906 1250 241455656 241455659
    0xf030c061b130b0d0b090a020903121303020d031b03200114060603040206073519121104060509130504080d2d0207020405370f0c12050709 61
    0x840c01c20a200b4410221500f50114801c031a0142941000b091404000e0480d80307036251525202d80250080c12185002e0320861b00030050a2240108952850a454001d141d50320f140d6403c110b110103000344210704101c40e040203990140241e03c50044018403a071034141101c14480140e800e580c201a51003149031f070610040c07001c0b0410700300340d460f0010b8042c1c410715070301e90301c600100d580d6200c5d0203001040740d03105c44d80c582e03940110a125000403940003500c5202101c4080d414942c0c2d40180c181010001d2001c411074255180144a0102075810003613004c503283c0715910844019400c254880b00100d000010076401d5880d0800300b007000c648614008101c24103250f1034128903030050101d440e2605640703899450701050400c038824020380b00c03a9400c2e9010700140100c0400381d042075001320b00690a00f4081190b102c440c50401c0761100304c00c48000c440c1c2054549440790300305104040d92460350b66051601c4c0000c20b50013103050400507500d03150740200c00c040d2450100c0300c00801d06010000007460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 241458156 1250 241456906 241456927
    0x812101d0a110306011202030603030702060703110c04060302130209220b0a05030d02030a08100e04060915050603030a0c021c0506061f120b06120f1e01030203100e0f030c061b 77
    0x88014001141006c0142c0325504e01c00880d145115005000e0b5100d440410000109a8000141024440d0300310a0f92a001c2d146810301090351060f00000703601c491056400300c84c1d01c01e250302404140b6001010f0922445150303403030504248040141c20403564072500004568100301e41d000c40140015001085400403000d0001d40328010019803400300021540458031070b41d0040c060401070441d07003031000345500f89460944020009420708a440007008408101c0404440c40340d503101c0e00e000b070040d40c074004940388103c460206010040781c3c800116a00c1c142100005146550139a1240c2d004080034127100c0c2c200f04d03081007003d04034900340003680c007003102180d44114404011a1035034000300b4000554000110360f4010002000198510725041068a0012420090080800300c0551610361070264030f610a6110902010750180c0c42030200c50012152035000200d03180002003170380c8140031402c03003c60465000201e01030140c0d0101c402c0c405911303404c20180400422001c0c8851421200e041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 241459406 1250 241458156 241458167
    0x50706110a2003150a14010603150302010305060a210b0906100b09013c02070609031506180c03140613090c0503010f0204030b060402070812101d0a11030601 69
    0x708240c0c41d944040501d00015101000b500e10384e25002c3c0c46032503661600c44210002041084e40e5540c81d020101c0001076005e00902c1056005110a141015203504580041d4050132000c1c20142c0c02c4020302c0c0000904c00c00c030080f03444c112403418018400c02c040e03500740400803281c05444840260401400c0c003841c080302d05103c80485402202e1ba5845004010050300d07000c015020541440140c49055a604050b04c12415011481c13220b02e0107001300b01140883c2d41c1d0f00140034007804103d02d0501800403030020440d21010032070100300403800503241c4030901300c111402c0090b05840394072118400440ca8150041117000516043c901e100380c40c1082c0010544007000450950f041e03a901004018030104c91120b2010b0722020b0020b110aa0700f541c0490300940c843e00c030640300180300f50041000c1c6e20713250003118080780d040190603040c000b581800000d010340140103d03444002840000035014042c20030f900c81200070340d802d1425490030104800c01e84401b41e8541e1502c0c00c0030410404983c0e00030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 241460656 1250 241459406 241459433
    0xf010311130624030203010f05040e0c04060b0a090b0307090509070201092909060606031902040503060c0903010b03060118021e28140a0309020d0c03050706110a 71
    0x4441060300204210106411030003403440300c401c1d28100b080225010802010a032802020031400b40d48520b8112411402ca002c28000c0030030303100c143c160411091500d43c0103615440d5910082c0c0f01c899611100050407643d4a41c8818080e010124100714044c1d00048180010b181200d00145140340c40503004103810102d004180c40b40e0b031840082068503200758440c410300c541c010741d0424080d42c0c2c0312190391082d80c12107076500312103540400618010320109205019680140c101030035a151403143c00d0740118030302c083c020003a40c28400001c0075038042100391700030300036181555510705080d1300389402e5421411210380a0b0b4000381c010840010840391000b43e04411150040e114080201c00d880803600011244410842c017040c0310092010402072000040024000c50311070400d410b00c15a13241c0d00900034030b06414001d1148106550003600590029840108001040122070b550080c40b00c5a44d00180c500d6840484180079094000c40c01e801d44540d51001440220040da07070baa68a001207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 241461906 1250 241460656 241460663
    0x109060f05040507051306120e0f0a110d05060708151f03110c0109051b030a08030703020a091e030201031a09040f02060405180403080c09300a030e090f0f0103 70
    0x60b0340006040a05ca801503c0110300c003c80015605d9070390b00f50041500040c0360001d01c01c20314000004100c1000010030403800d2034a100540b1416100c1e40f100c8243e8104d20100740c1e04001005504400541c0030700c4514030038025501c0f5230503a400c00310510003007200700300080c0d4082c074403103001036083c519125088030742007403d0b00e40861680141105180d40307000303213609160298244420542008800700b00c0c026190300203a50f88a0460341c49041503034603034402102405100d02040403a000500c41e40003000e00043c6410015007407980d81c03100d03d6140c0c54150712210301201c0c20000380115a85401072019002035503005040103403550001403240b0401420040c548512140024215102c0c075056400174100103203401c1c807a6801015230841060110350440c00180c000700007030401d1a00006403240041c0c0604030314044015100050321011241c030500f03aa540241d4405403103840100554640c1b10700c41d581d8500408481401d010b4110000740c12020382e070a4240030040720038040310100b81120342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 241463156 1250 241461906 241461911
    0x11220506030f030408010f0b100f0e0315090f160f180605090c03011404060b09060d060803030a0c020c101b030504030b040b0610030e10090302030d0f05010e0109060f0504 75
    0x16040300007850200100b8007040b0300e00011900080d910b40651180c11b04400515040c0020760745141040314891415034080c002c90b8010320a031001310f10a00b805d107440b96018048801515841150380140c10301140d50045e90350080c80d40010a171014440c18030a02c2c24507440300d0380107040042d0600c900480f400703000784100c49541400b41010064111000800014250300681d090050316140164024040c091104690420100890030b081c4500400c903816108291b003828260010840715034045089409169160a00402c070220240002e502841c1a142d000400c0c6240d0030004e41401d54002416120b65506080c00c6080c07600241040b4030419900c0c0e030708240039250b1400b034489000e95000034002984900400c01081720910005004001c201c5c3c0c280e0301d594807031004406640c0c0e0441d441440750400500c030803000350540c100605052113401074900380149a1a100d0813241d441c034040321000e0b00c6000400401010080445c00740040c0b400c00d112107410162403c00050407481601c0c010365 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 241464406 1250 241463156 241463161
    0x19060b07021309051b04110d020912120702010c02061201180b0111071502030c0a0501020a030513020a05130f140f160503041104060b0c010c2019030c020303120103112205 75
    0x1e542d54040320324200c0c7c8030b00c80e54031010320459040003508102c2c1d810b070040c0c3c40c4c04816040c10000040341c4c03941c2465044550700c0c0c490154011130300d84003e140d049030884020720185000d00c400d030074011701a2103c131514070405074800b14980207960039203006a06011240040307444441000c0b03040f07412f4443c501c983e265a01003491080f03242d4800d0800c20b04550058141c42c4c2c08010043d0020b00d0407105940e0306100f50f455040c00800c070b40350081030003503005034444000c00c01401c010112052071070300383e40b0001d040c070300329003611054034a0410507a030b684007894200110b04803a0f40c080785d081003001d51010107104c0407885c007419a201c0900302410010f00d6161803180c9036902e40040024100b1401c000d074440c800704d89641e020345400303104400461000c040450751070700c0d940800480280c3c03110040c48054aa08040d80000b01c0c1c030a010350400102c046c1400c0961810002848070100170050400c1942c554200004000807044505100b441905007818096548409002c0302c44d40c0c1c03640000d582d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 241465656 1250 241464406 241464409
    0x902010c0b0f07080c0a050a0c032606030609030702181f080a05010516051b160b030103050105070c0803280e100516090b0319060b07021309051b 64
    0x8805124004100784005010410207540e0407801a000344503646a122990725401d01800e02805440318410000e11309000d18180c00d44a00d842806281c080e05000740780440c00c80c0c210880c40100d00308000004110000c0c401e260504000d0740750300c08000c80c050b50500d5186e40c0000e00c1c0c405c1032881411b400b0307080e40105005000e800028481220801403900040f503039811903d403155081007065485510b030100003206007094210001c2080640d9450300c0c540902d0341800d01d181e000903420403400b840f81e042101c0c0c24a005158040262540c0710700551030350300d03500d401425990002e01401c04c100710811204000f1304802d090380d0b001190004543c9a142d0700108581481510080d0501c4031070420300e031648844000718500c80c1100c469101488582c1d600400f04840e041880030240005950f05410080e4001560103540c100481d11414138038901d980034004141c41058101d2110030000144980841c80c202c000c800f103026990340203100e2506182c4403140c441c691b41c1c2c2c1c5012082c01443d54005503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 241466906 1250 241465656 241465667
    0xe0606091005030109140105060117060607080904020d0618020a200c100503010614041203030507050403050d050301150314041101140d0608060108060f070e04020424120207020603010306090201 85
    0x10b0a0080c000300302c8903080f4108404940e001c070029800b55460400807034002d500ca01d0a00724020041c0c5004042c0d40c0700e1500b030150300e03804040b0030b88007035000303000318200c540d500d0005041000705180d020840600700b180c507480483e481000400254810000c000c0d403d5000354408103c42c0f500e60356043d810742050303162401c10080800540e84080b642e4002c1c82d019030410055410f854082e03031258005411700110081d24825802003d40d020311844035100024481d030000c950012452074003e044c5562552035924100e00200b07603001107100030006001e03001500d044164aa0b0162405022082c41c1c960002c400440250016045d42e58086c20441d85034090300500119111610140d561003030743c010002c004140500038013241d409981e00018184500007050303401401e036072185e44035030348900e40c00340c5050121407074694006400740400520305080303200010001e220604441c2c0c2610b001c0c000207244901401044038103901c14408540517850345030903a03046d00d5203e01d000446907070300d00050b0380 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 241468156 1250 241466906 241466909
    0xc100207080a1e061401030b06030307050c040f091202030414010318060e21070203010f050702031204030c0c030b0f100609030b18030a120b01020601050d0b0a06030c060201090212010e06060910 85
    0x22a0f820b01c1407100102004170002c5040f640501c41d8046903807200070425441c1e204600015000390304c520008841450180d00480345c08000180018068200e90341c2c11000151412070200076800104017000f5805003418030f8200c112003487d04101001c030348140585104500003016150b290340d03030031040e40d2600030031040c070200043d100c0300c00e0810300170150916030ba030240100301d001c0d501300443c1c0c8140380e066000f441d02611b09030300518104580c00172f40c0030424000400c16004c000c40b01800310046004030440070f0107140510145555868030136a0b9804000d4041c0141101030b5401c1301c00c1159a5102507100b0030750354401400c90342c90700e40040f221404242c20780c80079514040082d10401d42500300030120502106a081400f03100c3c0c40c02c00598a84409210f550f070414030104500340002d10013030413981e02841c0394400244003a01da0321442002125034018102503035548407107005524000c0c2002411954035402400b16942c442c01c01916401c024041034000c070a420081809040015410340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 241469406 1250 241468156 241468163
    0x3040609052b020106050d020f0607171305031605061c020405040f02040e180d0309051c1809023109020a03020310081b06180904050c100207080a1e 65
    0x240b4002e071580c6031407400120082c00101541c80c1100000b01410041424903e043c0c00030042c428802141e0140718a9910094045624904603031018092201c50000744c00e8204907503c10380d00d5603003401c05152078010f5020940a010400d007608201c550340711804c0314a2001503807030a817002c060410204000c7e0242c1d4211550107805c0244242e01e2a56a40c0580104c2e4030304000c044070b030784030015003450350002586c400035144c200091450390980250400300c005481001107030440000140c02016009d00150f4140c00035410706805004281060144405850714900852404c407902c1244a200c81010105041e0180300480c40407000340d00d580e2090041c211070001350b640d00f6000301c008000390700840700160081e0b116007021900780d80001d104d81c058210507890400030994802000f40541101d020255404402000641c03a62030b01a40f140c00340b442500242007111894080002141404140f5070855000b0030080018038400510004030540000c10344600100c403142140b0611034100014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 241470656 1250 241469406 241469443
    0x6020d11040b0d0b0105180103021e0c0d03060510080a050c0708180a0f0503100b0406180518030703020712030504030b0f0702070806010b070605090c040912030b040507050304060905 80
    0xaa800c41d0100620414050b0f10081060418402c01980c2e43e029000b1201e0400511806241c6154000d50050001c04010310140301c888007000c3c01040942d00041910440e5004200149600ca800d400740a0103040222140c003800c0340c2c1d001000789086001049901c0741515800452880c480f11001c40d10a25000328001c0d0b034030020304a400600c003035680c807043c0c0160340300000000d12031060400d40c01500c0b0028042c020518848500c1d0300036222280d58980d0260f43c40c8030014940654081001c560b000c88030f404119850401501848000001d002e8100c40d00100101c4001960120701c20301501e00d103c0310107100c05c4a034241126280519000209a1032070703c020300280c15032210b6090f105020503800ca8464540700c60485880ea14203120351100c0ca541480301c1d0000809541111303920000b12011903508211071300c002001d890b4020341c26505002407003981000b407036060003861444103050b0b41c00e2241c0e00346148024500c3c07100070809080c039540c1d040c2d1281003080c01d00035002c483c02500401e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 241471906 1250 241470656 241470659
    0x706050c1210031b030c03031110020a020c1903110907260103050609010c080c0c010e010f0204030c09020918180f0618070509010b07020a0b030420030609060406020d1104 75
    0x118080302c2c500054034410f144450300025000000395002c03d482e0302880d50701c1030629507a0191410a0b09141e2040f0a0180b8403c0e20b50a1a1504c0a080511407a0340101f1100300c4c0907060180403840604004c0c00381c0036404062000c00c4100216034140a005c2d5103204c01680c1c0c114003110804030a000082203050007282c1240c0e82444ea00c2010b05807070040050b103440d5203070154618222928440d028020900c00310008440c446c3d000041c1542c0c034514000401c0c00d2220700c0807982120a01d08034a80099800300d8144103100441c6980005807540941c00c41c648010a000543d00510076603818030309400b40c900240e24044854601034080b138030341086402641c0c212006544803101200e0303140307103000c485070741800d010350001e44501120f8001d040c03c0d2182c0d08001c44441140d210040680c1c006040d40c0d0002202d40a070f0f4015841540a4080c0104010906860080740885601c06610a912a20501900103404211140c109902000050b034616000e00c02a000d080d14555030309003800d001c02c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 241473156 1250 241471906 241471921
    0x10060e03030a08040c0f09090b01151706060c060f0115020a20040e1005040501050a15181b020c0114030402011709010b0409231914030f040605090907140706050c12 72
    0x38231065100d1106402e8680e00c1d10201548101b0404032900006c0d08031040b52400116441803c3c0c10110180141e85030000f58580c0c1b51511805403041d41451f410140100a05403c0c00e0260300c1225891001c1c10410115441e0024851408503804485042d8403c03a024a5a02d541c050014002100265640c81c03882d05107190080c441180e041d40c041d400c04c0002041c09200b845540c400700460803c80c070851b0304100006040b602c00940c1c036460240d032119600c0250440841421035001c4a6008100a031549000101407445c032540049002405106100050f0b0b00109181035039508000001001d65070011410302428a519120360800d240180503420302c050a202d9074000740040d50204c03c88401e002d400380d82e80f030324041c141c007403082a0390a40d0001203540421603400ca100c441180d0506c04290360b0302803158425885070010a1000540c8121814401c5645500c52040d0a00180c070a414410800c8a4800c0410080c0a13541d00c0001036070104c614016100000745151030b0040500d002e04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 241474406 1250 241473156 241473161
    0x3060d06140402031513061107050102041e0602072607230f10081605211920070206070606060801180e030d1d0d0810060e03030a08040c0f09 62
    0x40b4183d00034020408144d00091040d00550f000e001855004404c0f0740841d1202d50040070f201c0300c0030b50310090801c43c0da00820424000b4201a00c4225030b80c0d00c3d0380c09940011410318040b503000038203640004008120003481032602c82e042072038008058168a122010003403e088072034122251240003d089a03100041221210103078241c2030390046c548062020030882842010081d810000329180300140128024800e038004070112400c0450900308402d15080700c010344d202071820380c41400010031070b025811440f02c0c02c041c50403000400840e00d038440c4102d44040400f1503500c0d0482d000445004549031001200d0fa00ca4001c5000c1114644800000300458020301c41c0200300414a070300c0c3d0100400340c1c415502c04803822001035103018000c40303400c009800c0c032020715a0959036403002e80740b4090040c098090031400c0c540c0c400b0043d150243d19200d032010107070040402c121494070544003a442c0007044608155242c10102d465039034614200081c1c0e43c0b15004559501002c44000541401d9074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 241475656 1250 241474406 241474411
    0x2040c02031b01090510020a12050403050901030b0414010506130b040f0512030c1b0406090e250302030c06031803041205150c0313020109080d111b100503060d0614 72
    0x2d680070300401074110703406804e03181060405000d40e0000d0340000122040c0340c1c0105003180f5203050081c441084e60b181d2a00301d030350840f41640450400030714141d0035070b85440341150410080740c0420518150f00c03c4448410014000c25000d24000244200c0a20307040c01354000070024280d14540e12611640b00754807500c1581b0509024219400f066407264002106075401824110020415205c107c50881c20680700424140d410039550700d408681554030380200f801c241d03201c000a108020060203800307407200d07441c8020051141c181c070781840142c0c0e010810160401c0112044d544a440d0b191094001e4550140700c485140310000d00010042e80400492800902490543d895003205916140080034211040d05406e0320070800070b440c1451108044e4042c0d40107250030380340252190b81c0c10f490140c1c2d15410030080356190040f550041c9003040000200042e20001a20001e80040400c841e401c80565080a01c40007200040c102d03141c84069081041c2c00000170700c500003480c0c10200041509 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 241476906 1250 241475656 241475677
    0x12060f0f1d0618100203060402090409030c11041b080603010605100c1505070c02010c060b10110106090b01020d0807020c0901180b1f050f0909010b2d071e02040c0203 73
    0xc020001e2a505520180c011001d030030341010f131080800500940000358801800c0907480b035824444010700703413264416016400d00c2500c0300c08640d01242070104512400c0800548101c2c1000d540020420000070380b44c80c03074446414000003503152100001d000d0900394004507007100c00c2820301c0d00d4140c0d109524020281c018960408004200444070041c0d03582250a4400b1070700b09007152005521501079040030600419001034212441d00c0010640c090f0032074030300300041041c9005032a1140c00e10500000b024040d00802c0000c200300300103505c031072807004440280300c1448000f4541c17a0081c0b2081841e81d10003082043c49686482440c15900700406d00c04140320b1801840140c24248955414501030761100f070401c0030709200c04203c81e0741c0d000c4840800d4040040c00030702e06a4a40540e0765010705100c1450366201e6254850407180b0406100c01d4041d5501240c05051042604030121140550003507a451285882000100d50aa050b404002d402503c0c100e0f210351782c03a6001c800b80c04490103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 241478156 1250 241476906 241476913
    0x50903091305010e15040912020c01120605090406050417030a05040c05040903200c06031305010e070b0712050f0c0c010f020a03020303150a2402120412060f0f1d 71
    0x5400c18070800701c920901413140410001408140b240d800d81548044082c401031001ca8280020359035103421515070803010003d86e010310181901583c200d101481d604ac04001e003000710034908070025500c0d00026002034801580c41000c50305204a00d102e1229140c001122140d80741081d0780c00000401c0202c80039940318240c01e002013000e142070300a105640d41c060303554030300e080301e40103440d101080080381241c032910602c1070380f00c83c507103810001d1442001c17201e27807141400c2d2450034081d096894804106082d82c1008a040c0005195002540c009580018466072a01c09000c801d0341c0d00e20400215508410000c601e0080c1d140e00018141d4100e0400e81e12107103c200c080d281640c2e034400622000700503820500000d007004601c2e1152000a505c0101489081c43e5039014407400b004548a15074040030001002100f000d4040100300c480c0c1021840041c41c0601d000d00800707100315003403002880c40f621894440c00038645c3c0d401110102e13500070410030000d030503141d207032400c0c000001d000d408901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 241479406 1250 241478156 241478179
    0x301140f06031e0a0f090c030506010801060f0b0a0c150f0b060a020c13090b010806040611070c090e0a06051503070509090a030c05071e0801180507060e04060905090309 74
    0x1c00c00166809000c28880b000c0801c41d01c560030b41440e00c07004000f15406a5034408207240121180283c0030103600540f540f4a0040c00d43c1485400c00405030815040d982c10b100082044120000c580383c12140d0340100c00361200c98400303049805c20803003140a0048201341d003006015100c1070f071207036491030300d500801c00c041d24000041c04081d000d44102e00d00942c001d032604440d035080ca0040c180465140b00000030b9031a4450761400754045003a0045082c07079000100308000c004480c070034071120040c8900f030603003094040c0e5a094144031540c00b84200c11a107030301051000ea4010018808102d0f4061800d210500d0b1803161000c5410714000280c0c440d12400e0800640ba0401904d20f5004881c100050995035050341c40541d0202484134040301e0300d1052620000e021841ca0a40303500440d40c250810b1026807038600c01e0741c00d5402c10700480c503c10405000102c0010030000d0401c0c1140e0740c40c24501c00581c28000040c1c0248625404807508038100380400c595000c0c080010100707034070300b20741d0a850b07071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 241480656 1250 241479406 241479409
    0x12180e010b031f0608010521060a0212011e0302010507081201240513090e0a0515010302011106060102150a060305120406080f0108150c0f0c01050f091f0903140301140f 74
    0xf000d2071260401140d40300005001030b0a01c0b12280b0301400b0941110204a401e0161080c9019021944442080d5000c28549140c13125151041d0049c4080596590744581c0400740e160180c9003440f0090602030009103140c1003041800c203079107044806040000d810360399401c1101e071550f4010260205100c462003001600c41c0140c080d41d0101c482c0b11800b0806a0400b0001c100410081940341c5141c4542481da600107403041002500700c1a000e58013070780a501d1440090441c3c1034400c0c4440d0030360064000c002150340d000a4900030b14510410700c03236090310ba1507072800080c8200d07000a00303240118504280e6400310040180100e8410b551000c040307039541541200f8180b400e0169100e190080480c81400c0c03450613200c203070003081d000d542d146010706480d4003030000e40c404019603100741d450380100060700481c1100c0950000040020701301310201d00314540c01c6905041c8184d803405a450705602c050621400c081401c40c019030004983c1d03940c450b00c0002c2c0640310643c0403403040a1280100426 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 241481906 1250 241480656 241480711
    0xc050301050a14130305070c03140d0302030105030a03080403091502030c0c040605010c2604030b100803181905060c031201080a0f08160602040f0504150312180e010b03 74
    0x10f03100f1003a111403843d12012188420042100350a4042190500040340814405030300007004511480c0c40c164111308a024050914446040c02c00501d4418001007181391804079040040d282d25151004490303440f03140030b90340f038846500200702e0324072038109800c94103030000010501c2c3c06105040300d1442a82d80b00b01700076200b030b900809000031058005100000c02c984008410604195910000c00403c440302081036042a0720568030485c4510500055861003220311000d449400050f500c1e02030031003035140140400081503030054800a5008100320500c503a00000350200901c0c0c281e880d01b10312003003030341ca8000c0c00c0103281005815000194003540003c4441c3d103141d0080401c48a1100e6842d55032440e0032014208624034107165440f0006640c610050010b000d200c1400700001d403c0406000840d488000701a008030342c40402840820b200405c55402100d40d49451603104088040300c00030056150b20981030340c10180000f282032104080a14840c4000d1000301c0d20645882405858 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 241483156 1250 241481906 241481921
    0xc120d02091e011e02010e010c1205090a0803061504051302041508010602100b01120f06060e0114030c070f0f0309050f04090b15063f040c050618030a0c050301050a 72
    0x13185410380c03074020181c1000351600c581c20850000150f000034440d0114251241c00c2d15440005003080000d03c250880c030b00c2010740241200c8018034041086603111180741c1b00c0600380074803d000458240580c1e07510030302200c002d8807000c1d0100c1c7c500c150001943c030181d00180243d504039400240f035140707810700c201d16042c1250165402090013442c25400f000040c281410840d0401540c051b20100c052200c1c090740d0280606000006a0b0701e00d0030500600000742d2808150400c904400070b08031586284c0180d075005880300c1e10f0706039501c00c1e5262a000072a442600180340134110304107101896000040041100d81c16581c0c60b94125400c0108401c441120100401d48401c150105280c842e800e81c42500741800a84030514001c070f40305509400001a44903081e108100360002c42606040b800b031036100305400001443c0e02d0030141e455800400450180a004800c0810982c450700c810064000d424000078054400040250800642c1d200305030040601079070802012441c101c01d80e204401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 241484406 1250 241483156 241483159
    0x30b15370203032202060a02070807090903051b1f02030403081506030f150303040f1505040b030c0708071e0b160e0909070f060801090f0218060c120d02091e 69
    0x1441d41d9140b9058130707100f44103e007000c02c00c130315503010160058039514000d14540406800130042540b034808401d00d0080941c0203070740c1460520702c0400000c0d820800343d940d118030802c00c002c0410b5012600d20301d4081e980866400e01414002903071032100c11a0300440c000ca01a80d80c0c0c2c05150f84840900100701c0a20041a42140c01000020384c103a5400d9280c0f40c101079020169100d4190701400246190403503040303004808080b15082201034401d080e030309411507071428482d0819260503d02c031a580002886000600702c0000c1d8181040303001c1d0100ca0000b54484480d94202d0300100707065035800c41180d030880b10488000b022034030721800c0750803070124451170b07998040c0e40d541c83d0010700c000608042c103601c10a101d0401c0210b09042e000c603468020301040d40d00c2a180b0343c5444102c005907541800c44008083c0304006107c10b080003582000e2035494207a454170b41c1c0b00e00602400e45040c03001d411700f04080c00040381c650440301c5143c00515044100b264030b0384025152034400052080c0c900e940d076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 241485656 1250 241484406 241484413
    0xe010212120403090503160509010e0105090c1b010f14070e0a0b0d110307030b0306070807050d1802030708010203070306050a0807062a0503120f070807030b153702 72
    0x8207416030780328550725882031203884c00d055003070380c1e400100380380107121401d500c010082040140040e05201a00390700614124603140959450b10b008140e203e000900210012200000d803810380303210b482e144400c83c40050000308509030481141100404030740c80c041c01c501186001040b4518410390076414981401040d03030341c12514102000e1241e80c40340e01e0000c4801e4803040002501c1c1c403501d014501c00c1081d03171804074401200e10205820301000504140c18403e4001c2403045484d401390585040081140c000a51550310083c203598082403080020b5052007840000700c3d01c204190003540c060f003141d442c2400410b49403170070815421041d008a0006600c150003c2102c6481f502c110b034000254215502100c07480400c44c44002d4444030b01c160744035840050b1074500c0014000d2100c0d413016003ca0300751914100000f004024207009071000c02096150011003d840c1d0701d0403400c1d0710241c17403888130a507600b260130341d5000720706100e2004c00b952000c8104414100d40d69051407401c02c01c00395014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 241486906 1250 241485656 241485667
    0x906050c0c0717120c0d08010b0703020a0b0411040903090915050d0b041106070b06031501061e02100608060103050d080609010b070503040f030b090c01030c021f11030c0403030e010212 81
    0x20802085020300e0044621441c011802c0c4010144000e040c5c080c0d944000e403102401c3d000b005000302c041030b4000300c0720000401c98400801d81c04a900c00155070701241013140c0e6140c508107c40c003100701000443e4401d02d009521010150400c0b03802c01180d40b482e4003403000e0000e40c440c02c13210070500e108142d040f6248000d044002400940d03600d038824802c0c00020700603140c03500821304642140704102d945611003030a01102e03140401c0f0070b03c0d924000c440326995940c10890700030b0043c2d401041c1e4006076441b1081e403503010b500a11020005082c90304041140304c5e07031001301c0d0b0755900c400e220aa509024203001c1d480344d81d00c03640d281880354030050320300170080c3d19104c1c5c004017a500542e0260361602081c0008107608a1944466000b1805814002c609060690007141080c0f19040c0a60505143c41c01100240d50041000f951840c0203040141c80d41c071044c04040c01134881342000c3c640c412000400c0103100d0b2816006003091f030f4001c0da2805803091080005a80d500c181141038881214140031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 241488156 1250 241486906 241486919
    0x30d1802122e090501020f0403060605150f0706110307090f080105040506061201020705010203070e040f0902030c010c05010b10020a0c0602010c020a0809031903031d0307020609060a020f060103060906050c0c07 92
    0x6a05103200314542c000580395070700d0b8540780d08a8000e92164060980c0c000f8080003844140c1c001c403006803030102e552035000300c081c10068686105443c54258144030225480c1b00b404060742c00300b800c00104030082c0f5905e15000707500805559a03400f45400c04121600003180c28201480307501d20441e8060010f004a0316000300300a00c189006885003000d41d000c01001307000030390a00156000e1862901c0b8a20641c64060801082c1d40307000308803069032451305420300c0143e83d000414260000e800c1c01e000c04009075a04185015242c81e5840903044400c1c06003d29030305500040c1030740d1850140030070084450311404121b0a882c0c1000704200160f028070710106c089035100c4000c121100e801000c075110060f004000211481c0c0700d25080d00804d071307103400c1512081080c0046400d8001d10101a51900040380d0010f0540d0140d01d4566000d90301c041148000c6a00810004500c0910901110195a501c1c50050003400b035000c8212501810000420f144111143c2541c00e08180d090250400a05111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 241489406 1250 241488156 241488223
    0x1110a0c0501030b060c010f021209011e0203070e190503010c08100b090d150e011d1f090c0b18090103021f140414030714091305030d180212 62
    0x455030f505c201c0811040506090034411210500f0107800050b88907412403200541100d002400c0b901c0590510380014040241640d07480281400c40ba00180c49031200081210100c2d03c10042c540c01c580c0d81c0d078803a21072100005402d4102c0740120003d01c900c140c6680300312581c81c070a0301d044034074900b40041402002d0103c000f070248094007501003924044107444100c020584100e00041c0c090765031401c0a81498280144140381110034400d01c001d008400f04203a60310358084041c280074041442e040640030643c1c0007401625048002d1f15041601c6e1301c04501503070f0001004a41108440081582508001204504aa0700140009034014a040003080791420381c403440f004110380b4a2041c24114043c00182020304602601c80c1e2601d40000c05140c580007040d0002c000380f101000c86080150342d01b21a441d80a10001c1f0341003c00009460b25924601514030341c006c44500f0f0201d0200e20041480c0b1000e00e00303000b100c840e040c140d0703e0ba02680e100da1210f00b181c40314203180481050380c1301410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 241490656 1250 241489406 241489421
    0x919020d170702130e160812030604060909080a0e0f0f010302030603160803090108011e0317090301060905092b05130f0b030115020c0d14150a060501110a0c050103 72
    0x1008541c40d002443e40010b0b213000500035501d403800e50310401c400341c01e070040102181c0507281941c0900018201542d141da125901c012100301214000005403140d11143c101ca002414010000d010551440c40d0654058000400c140002600c07014007012501d170850314809000300c0a0107103031207030340301c2001100607602c0280407680500c00d06450340404202c04059030000c2c51450301442d1100b0140000500c15401a40083c0300c51000d12280004004100060811280c0c0301410340d501025058401c000c0b0700409049680c9946014800213181d041c0350421407081e507100c0103407500050120b04062040304410404202405410b07080d068031405040200055540c496440810503035600101c14403400c1e030380144180b183e01000412040b891550401c0c9000c1060001d410003a1381c0030045070b0486c001034409041000c0c0c0c611040700714101404a442241c00000c50388000380340085258002c9c014501c983c0c1d001a458007501040c083c0c2c08a42c140d40c1c103502410725085580350400440180210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 241491906 1250 241490656 241490693
    0x40510031805120421020f06091512180f0a060e0c090c07060506090106020303061003060504020309010b0a05060f0702150f030a0b1005030105010804060e0c0a06080919020d 76
    0x110001c510124004111202d2070101c40d40e0b0155413903040250350b41320004014211225211481188001030703541d08100c480345807094422907100d142c1000010403204042c001c0969040001510968070701c4c254070741c2c9100303034440100031101e4100b464141d9075582c51806640d85541094462030300242c001d8001641880441c0c040300c8480d8107a01c0001c8000c03d042d84c400a5654000610604100003801007644c480c0c0c003110440010740c07510f24040c1d2244401404c083c4140c4000c100f20800c43d00a07845240a4200030f0002c544a1418196240c000c01092184030b21803844524006224030b021412100380b9002c101141d81020b0499007070007006c081110311a98110b07014060b8418030b40b41030011b1071007510710702c0c0003080b070302c0380c60041c051840d01c030f08010000c0220800040c41030ba6048a030070f03504507078440303c0000c5810802d80f0342401d041c030343c00c441c6600080c48180000e109512580fa14000c059003411f881950076400004c00c07002004060094000745800c070390b400070501c14960641e04021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 241493156 1250 241491906 241491941
    0xc0c0112110d020301030b0c0903060f0c0d0e0303180d05040504150509040b19060302060306010810050604090204081204030222060e010312080702010b0307050f06130b03061504051003 81
    0x1030503030300c0081d2500054041c603405503001c40100103010451002d65000603075185640d260104035408251580001060a8801d0340300070040391070000910100c80980d5101031007000204006120b0f00c1d240d074010780d0700c00c2c402d4030000001c0c0c001ca00301192101080e02541c40f801c0c079052805040c000074241c12036a109101d01140c5e0001115180c11444500c20340c0710f42e0702038a10f0314081c01c440454100c00182d15038600d15204080c001a102c0b401142c0d04484242064031069840c0010a0300342e40d219048160881404180000c4107480ca4010740107a0b44628140c1c1d8284000e15920354103400380344070180d4850144101c011010703610001c0d090f41c451984401084240d04c40000d00c1002900b85d100f15408000c00a00481190303110f980c0035000002c500c001d001040001c00001c0d51060607000b414420300c410300040003241e46810803100d0880b41c5644142c5d407980c1e10401c601458104403041405840880400e0300c5030b0702e0401c00c850a95074004d1840c8601c5820001c203c004190107014000c1949 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 241494406 1250 241493156 241493171
    0x11090610120e0f0c1003020a0503010302040513050a031809090f0b0727090e0d0804080f0903010504080a03060e07050d050705070206130306060512070b0c0c210d050c0c0112 76
    0x940c180603e401070360f8220020068288900184100542840d20500405105120350000e0319071040c00c9a0441e03404a40100b11915004c86403180c3e540003d0f80182144035103201c0808050708121740b07600d201b14107002e103c0c40da81d50781c44810540b031038800000c10464030040104005164400c10f2030b00031503189800c1c5650340982c20980714040300b50000000361a5a1a0104100c101d00d002c0c41c403481c40610007a00d1241da03032010150a4003000380c0014400c6402007481c010311200c510649820000080003440142003606220f4141e9005010780c90009082030b001088800c0317840307440340c0901c5550760381c245800d10519105004180c080e040d00c040000030485000540e582c90040c043c44a8204070740b44210380b4510f000d85c01c4031900d138131040c055405091000754000001c030f0381c20300f201c0c022200c0c1035a40d04025265402d040ea01901154028410416a21011280e14000112074142011580745016946096400780660990240c05600a0081081c9548075146500c142d5803151342c0400c1e80c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 241495656 1250 241494406 241494431
    0xb040b0c09031b0406090c0e040f240e0105040608030a051e03340504061809021314030111190207030203010203090d0306050a0f030f170a05071109061012 68
    0x1902c3d00000440d50f40b5103200b0b120b9807405100300c9005100304442002043d035400c002400003580402224400ca0b0b503400d00c000c90721400c2cac200c3e50048109031702d03219a401aa0b62002c601003540d001d035030f1403510bc01e000400d880c24144500401d8610210007181004c0c2c1005044031194000e442080050420210612400c4240409540541d4542c08044e03540c07220700584d00396a00d2032103031407081404800307437541480d070700b01e0708450944906141508a101b401049412990300310703808000500c0c0b00258404900c05510500000c0c0c0c1c468400481d001043c207400c15090326051444a60604020883c0c880c140320306c00f90902c200305445c0151000311b43e907500001d0072a00f00712110030309500003800b03080320305600d8030401000c1d28040343d50255890505080400c0c8a005000080c24460450580780500c00c9482e010500c0c0c4400009c22581d801c0d0b840e4004040b500800c0341119400c606c11418980c6141055051340b1800c406000003081540303c10f0300b115140060204070300c4583d50f0b1306d50101c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 241496906 1250 241495656 241495663
    0x71205190f02040c0e010f050d02090d08070b150f1003090b1f1205060403030e12040603090b06040207020d0605060112150f0f0e0c0d0e1005060118030b040b0c0903 72
    0x38030300908074558103003160b00502c02510002c080180800030400c3e049803042c0e03040202c2da1021241031514640703d04180a0440007481030b0003103140d00a0aa03c2110100a8200c0040c46d200d0700c144110400c0b6100c0d0a52000025154a001540038100d001070a81c0350800c0d44c0300f440809694540400c50002d00d4651243c13000c0c2c252100022008020000c0a6600030007841800a1080c6071080c201c1400c281c031100c1c3c417a88040c0c00182019140d074084102a941001119151a000302907540d41e05ea40e444090010a0282d9003102d02c8130b41c0200007249494140300361115203401510312441d000710381d9100c10090078002d003842c0c11700032108031341c03240111684550805c00ca403403002074034441d0502e050700e01391454a40c003140c1112801041400341100719a5011703040184501216240d801103103e42000e03266030f07805242c1901c1a006803241b48172281d002140034007000e0b00c1c0d02d2a500d49030544918074085078040a40381c5a000c4000c00c002071026590154004030303114460307040c200840d00003410f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 241498156 1250 241496906 241496953
    0xd30080f0103020f2d03010c0f0c0b040201020c0a06031505040c0c0f080f0f030a14040201020304030308040c090c0503060109050a0501020d0e060c07030f03020f01050f0115090801020406022805071205 88
    0x30085d00000e40603110704003480b880c401e00c080783c200310706c1c006a0341500800755801103400a0101080c4d0000c242164002c202ca21040b2074010207910340e041c0c41c0d100c018000c00445450031028142040005800c1c1801d1051844c2040d081d5240007914845803121007241c20740c030208035410310382001034460703074040c102c0909405504018016a80c3c14201180410380d5080c00c0341c076414030b09090a0000503078002045400b201d03498242182036565a04142d2120341c1035501402c000c60506840e8040c45a2100040d440b840d82602c420442540354410b22642113254007031a400760340011400306c0054007a5044081d20840205a10b08e030196481260341000a03d0340201c404c002d040d00714604258050042d010f100390100000c014902d88614552400c0c80107100e02100351020400a40040d0b21814001000d450802c0080d55580c0d85c44078001d42e02c0351808190701c6940c40c464203586d80a4059414090050740060080031030b6402e14031504083c9141001c115800c0c40340910400b9460b00ca030944e5403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 241499406 1250 241498156 241498219
    0x30403090b190305060402040b0702090403030605030303181902130218030a03021c05070b040f08070c15110a051c02030d0f06030c0b130e060d30080f0103020f 70
    0x78003000300b003000d002e4500242c2841c0c17190380140f01c140040c4200c0e00c140e40380180c04907050765440e22a41820b400902440d04650340600000081054488a8011002d030000048044442e42c5140c02c00c800300075118580000d46c03041039070701e0441820644d034001d4480040c11488907902c0001900000e86040d181030070440150700041850401000000034142000c116030806610b8011241d64038500382134001c000a002000741c0c59a0410300c0869000e665105a2040741c440141e5100c0480c00000003880e0000d00c00581001c2110100303085c0801d194a03c20342c004000c0c0454040c00c214000f40e68420160b400840c441070210103038005880c090402501c100550001d0802d0450500c0c4409220942168620000c200040c060078640c800d040340442e42026108400354035201d00081c5003411800b00501070784114541e2461040c0c0c03014001b41410b1110850700d04030451500141d6401400300d400c12001e40703442e801003000d81030901d500c240f6907a0041031640d00060064868803401d00980307080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 241500656 1250 241499406 241499437
    0x907030509012c0105090a0f0206160b0901140a0b0a0302090c120a020405090c0703020a060c120218090a051003030c050a241d0309040906061d0f0a050403050906030403090b 76
    0x1c1980450078450380350085d42110287c01c0180c002e80b5640d1049940d207500030b024100000300900070564414120883c2c2d94002602d01640c00c1c04000f40c2c0c0a08080b2a02e546004d0030390000c21045807961040205c5088054800e0500610f182c0800c8101d0703c004140d00450b91040209944494181d100b0350300ca41030440c00140c5440c2090140134950000070000920a107041004030007080d00010203105440c0d00840c045641543c01d142110030386035490003148106c1c004101144841000d82612030004015600380d200c0b60f5480d40e400d41035640030f50300201c1e40310307905800f40042446101c1542030b40b800b40c011280c003242c040d07683ca9503558070302010b0506240c84161030313120202c0e02d020345c0e1044042e203424182c2c0068070340b0b26180c9a2158002c0c1c144202d543c1c00062040043c2c0750003040080a05c1183c490540174080e0318541901004c0710111040c100341000140c4030310140c4980341c091074055480310b0410840c0010b20045034005001941444072100001441d610a40001c00b40c0d45880c9842 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 241501906 1250 241500656 241500731
    0x102040902130e1e0f0603070504020a111006150507031103071101120c02070902130b03040305030402091303050a08191a10080f0a02070f1b05130b090703050901 71
    0x202a60440140110444a54221350b058140750b6070703240c903608005410701011103a02c2e05000245400b50543c0f01580181c0003140369540d268110909642c1e08000400707480c29480055245801c072402c9001ea902d0720910514240342051041c405880c0c21442401d22041a90f041d03805107185030024002152039400400500301c2d85d580c0803907031000341448404248203c0703010b07000282d15010540280542540c0c00f00c0d0a540242e0f000c2403840c01000e0140d000c5640e401c0c10b00303004109900c1140c059010718418004103030200d400c0540144084d41655030305007040340008080311710340006801026020f4010355600c040d90b01512075600441032200c070707008000305000c080c40110800c1d11000c04c20300170000304000c40d0301300d01c114142d031000c540e550059803100c0c107180c61400071916a4028041c0c802c015410f5121025a17294a0250b860031100014801203100c03500e0259007030f200030740350000481c0012030501d40c025000207800403007920010a9061120200d030000003a40254542060354080c3c9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 241503156 1250 241501906 241501919
    0x3040e25020309030a1103070f0e0a0b06070b150103020f0d0615051e0c011506050a0e0a08031812010f0207060c090503071701020d02040b0c070803040f03060509010204090213 77
    0x3800c5005540059400d0a40e1000000e4550b40a22800380265804074078041c02680e041c46204003030945095544031322503d482c1441c0c00b0540031544074409034940362240c1900c0c034241003541e10341544806812502c2d50362036500340d00d0004001d0114181a002c1c41100c074004100c070058001c90112620008002c0d10304108540802200c00a41c42440000c1205500581070400100400e50780300b00016581c81500d1009801030180c2102c2c0c0745406580100441c11680c01402849420601c1e0703a000c0b007140c5140d04000e06005248a40c606a910400c245414a01182c4060000810050440a01d46208420a400d46004811182d101d5600042407401c1007024424006030800c60300c4c08a800e141004042640c400550043c1c0410352480d0742c4c2468140000d4040300c81258000070155101d5a480c0480549900142c0b07084032207000d0060b01040c1500000f0540d412030b81c150703915003c0c803880c5481c2d84008000103046600706540070400401d9550f0f440c001043c07880b11200007010a1031030800f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 241504406 1250 241503156 241503211
    0x6090606090c0d090f200f060406110c030a14060903030c0405220615080f010503150916150f02150703110408010507050403050706080c0910170118060902250503040e 73
    0x706d44520802c00502c503c400303030702c03410252415200d4900b806900300742410911481c0c260f260196951600c641031010040103607113500111100000320840d4600e45450348929128007003155240440c43c170a1008101600e00b804056409a1280107580e140316074004c1c0100903140141c203d4402c4841c00001340142d1944022003036444845007900c0703c1c1c3d0394144000280c842a4580d81c0c80b10000144010070f215900510010900584070f110400c101661030350242c0584914000480c08200341950500c400c17130020070418601c00d51a60042450355400f0008d8000b00b206103503080e8000b40600c00410030070024440d4602844154032000d40346d40c40d502c0c040303103803544030340200c020850810140000281ca0364252206403804450043d80905042c03002c840c15103080303080306018113074240001800049000c0605006907a224280a003a4507019040107038464003020703c1c44c91196145044100441007000c0407103910800070303246003554502c00076103169004d5450300f4200004203210a40b070004031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 241505656 1250 241504406 241504463
    0x2d05010f05011403010608061c0308041a090a12052208011b02031c2c06150105030105040e1204090f0b0a0506120907080d0e0306090606090c0d090f 65
    0x91030650383c01c81902c828410907003c1881010140b06070039010850982d281544d04001c0c0600c5001c17080d01910b2800d0081500005440c00c2c0c3d9030440d52981c40b5103844025102070b1055003070304005c3c01d10305a00c2c1d9510340301c40501450b01080100602c0b6250822003030541401c08a0141d00c42c04041505180c4c1250854070080340000030644030620054080c0c0d004130580d1040503e0000451882200d800040c000e0010041081c0c081c07d144c2055000c03014104454041f20392401c000c9403200d54440384180740b2210a40811408205d00b800108281c0c6450b800010309482e00100713680d040246120680c10507086a0003503042583c55440040090003e8850318040c400f0441c0e0340c10090b0b1602003c12014030400e894142c2c0d031004840001c0c6641000c0105070014926441203600311103400400405030031051075203078405d01404020500c0b03942d0000e01903000300d0300181101c1907030b103035100009aa40c0c0f09130240800c9a403100185408128146c42c103481c1180100d07020196446000409500c80018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 241506906 1250 241505656 241505659
    0x80a0b06040e0f0f100504170919080d08010e090307021309020307030524010b0306040902010e061b010f050108031b01201207080c0904020a0c061104050a08030702010e01032d05010f05 81
    0x303240c00c01002c618238507103c00300c88850511565a421451000c42d1404464000340890101c28510000c1d8450001502c480110180e6403508141d989400c00400c503000300791807821040e40180141009460040715100162202590005201209a004c681007040700e60060301c094102202e0388031445030307040c440c500b440c8400e1580c07651503052688180c0f85000c0a090300d401107984400500859020710b050119140700104201d172262541c030011080c00145c000d40c0e1040c0d50a0101d88049028513028041c142d07042c81000d1814051060012004a0880307100a8815901c603500070500316840e0000d000000c1002405681d610840c1046000800000c0e0000b420003030f0341c0c410411040704040681d0343d002c1c800c80700560303500c0444a00311001d041a101c0640018503080c1d0305000300801d10b008204554080c4c03103403408140d891001c1c68a03406085000fa01052a0701c503040e000c1e41c03083d4010402040c00130307011422604120a8031020341030000121801a590701d0041c0401c0351154002c0005200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 241508156 1250 241506906 241506911
    0x9140c040933060303111b01090e09030d0e07170604120809070b0a0512061e090c0c0f100b090f0f0a180308060906030304032001020109050a0c0311040501080a0b06040e0f0f10 77
    0x2803100090274081c4a22130000160442e00201c0d00034401070007240d040880c10b01061098152403078040d03885420600c00d40010034203d0540720039060011601c248601e4000c07150b000004031042c81a6010500200030402c0c2d8000c0c400040b90045a5401501c40d421060b074405859058401c6000c0713654030043d101c54466011908610354600c1180703417010210b20195049031040c0c481c003114210500625031907900710b009802c2c003d1b40135080000d0301c80001a00b03840c1805140c04640512142d80d1041d162030205864036400590403050f404516904030324150000219440707103841c0b18018041c0707404202c0c0003407440d006014035803134042001c85d003002085003e5440c0c10300c0c41d65201400d00721081c801c20007080c00004c0e20701903030003948000b6030140c03c80c05541d200c0340795280482c1613602c6400110b841c0140a4a195000d0a041c0314040c10390b020703500206110a40c544440c403030400c0080c40290710a481e0030000c6c4140c6400c0c0540a40c0d0301c0104000c01465103007500e6541018038141c2c2d1f59010a2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 241509406 1250 241508156 241508203
    0x40501120f12091a030907150207090b0a0506030f04020301050709050609010c050a02090c0a030c090f17010b1c020102010e060705031f030609140c04093306030311 72
    0x207008084029200e640400000500022207509807050780305039100c03a9051519000340c880b441081e100551144000d8026240c0b19521000081d100030451035040c40103038820402031040032040d41c0245014007004021100082e561000958150b00807180301c020903200c80140001c50400f402540e402000900f040c00c07034103040c6000310f8401d00540b8900381c10014050b000c807040c00000d2006200d9541c01a0184c45145000d105401c12a8070500302c2c00300091030031200c0c1e002644030b02c03200d806458040c12000005480e020001c3c0c01d003100c0c865101e00c80e550303c4d22000030707603900c80454100b01c12186d101c1c404414139034000a03007141d0329000c220b4000e4111204000a8540c0719080700e901c041d24201d40c448081212100307150900d4550001420149003004c40340a105010014100b903e00f030800712042410200d0502060702c810280c014221704d40d0803081300032110203090307c1d940301c1c06020410002248000000b002d40301c00340d0040e40825000040400c5114040c0100072011020031540058171 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 241510656 1250 241509406 241509413
    0x30e0f0f04020d020c03120613111c0b041d10060b1b070801022101120f0b13021306090c260c0d09030801050f10080c07140a050c04050112 61
    0x4a100144040c03040b0360005448600c0d422a9041d94800f080c0d041c00c0301e880d60100714010540240c03e4505610980c006602c0d06440c510324011104060002e00055040c01ca500e1807200c1d65840c14004541d0403512402c0d003032081d4449229141000c0e0720100b4100c24645500d44080c1400242845001d0103030038800d040c408034092000f1124001014011074440750b07d01c05c800c81c2424000c3c1c110030520b5000044184e10514003603010804d642e200c001d8101540d90340c00840c048481d40017001840a0b61000400e408101c8800319164050300f1108400000305640c0e0002e42d0b001060fa03005811140c2d9020f0034061032100d0720404e54144a01d040849182d0580c20b4040074410940400c860480d611000051070442c40034203540700118107140c1070118182928018100302c0003400340030700401038401007851514114204d07002001c2c0c00d03198002b20740c03509541344049510a440540d001100412031030b240300400c005c00b021140c0940c01500740026050308110a4030410f07445000c090b42d4200461010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 241511906 1250 241510656 241510669
    0x219090617120a02030f1201030b010605041d04020f120307060501050301110f030a0207060912080705031303080c04080a140c011e05031e0a0f0e0708070303050f0403120309030e0f 79
    0x80c4106148150f8643e07044080c201c0c654413424202c014010300100b40100547c02c0c2c0341074075042c0c80c401c0c61941102d030f8840d01d08035180d003d180f00e4000203096110012020302c6240d00d006401600190500c110094107401203480250042980307801a07100180e10024002c00303200c0c0c0b5001d0b202c01c500a02020910200c211903500940803020080e0100001243e00c0c11004d9040320000c030352207102400a01044c1c00c00301d1590000c513414001180c1c1c0074000039022403064080364464006100a08072803c0b65403803c5848100090150741d41c264108404502c86004100d11000a0300c40e0100742e651444900b001d60a1002e0341c2400d505000f40214906a140141c0952504140e603d281c00b5849030703a108010303242000140303010342e601c681000038006400600c1d000700d810350040d842d0902c041e070340c041103003075581c41d01d803250a04a80000b2001d1000911031001086240320301c441c40c5060035200d40780d10361081d503481891000b103682c2c0c1440d40d0801d038101c3c80405641200301c48004070030070b50b18040740c036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 241513156 1250 241511906 241511923
    0x70e181b03102106050702070612020d020c0105090106030309080c010206070e04021b010507030c05120103020904031e090608010504152c0108010f0b060307021b0402070219090617 79
    0x400c20010000445802d0411200401422860480d80401c01c611101c00700c1c0b41c840e0f1500f03541050074080026940c138000200c910885155542e58603c030751032040c645000b9000740c0030686540703408000c108000d0b402400359a00405180c0c0000840618600c0c010380106099805030701943c1142c1c40c1000560703000304545502010608080511201880010700240b10301030f58580c46c80980341e13501503406415031040740308040c10784013040700c0e41f90043d05031a14050300762640c50060350880107100500b0400740241d0045d2207420046880300e4154802010040303042c41980014482c444104132441e40a034003580180030603182048146803240d0141300300c020a000b1400101301c1c400807194403804c00000c0b8100005c541c2c0807035a01e541c40e002a107010b4a10a041080054200007000c0313103c9c506681181e01a21a40d0018442c1c120200101e01d80b0320403026400364031581c28821480542c80e00c0d4019034141e0700d080c2c9000f400342d007040c201c042150440e070030a464503d102541006282d0000800c00e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 241514406 1250 241513156 241513201
    0x308182103091c05030a0207030c060315090902010504120812011203020c040b010e04091b0906062c04020d020a02060a0501211416030606050d0b0105040e010b0603070e18 75
    0x10a140003060801940102d8488000c104c0e00c00050240c0c02d003a404281001607238030805481c80c1e015035810045003035613100764400b04042c6844004000a20705a80a80c603481e1060610368101540d03205400030107030f800c050a40e030400700010781929403400061020b000d4000746240c9240c0c08140e49000f03640340c3e13a0700a064000c1e5901c05a04401303a00034101c400740140001c20510061a4030b14212a070080305041412201501d8800400d4004843c010b03c0180c4a0603511003402c808007200400100240707460300302d803407040b1070000c0e640f03078640340018034540240c00c1d401340c1e07964400035009180c40d10040191802500c3c100041c0150060144825480120380d003079981e00c4100d0342044407a91141944107107461164141002c40003e1026660007241d00444c401c00c009a0b0f00d100f0302c50301c44107584004101c5641c5c4c0d001030007640b40550001e00590312050000450400e214040f50441d88142c40360b00100d40c59085141d413b1419040644a050340c400a05032282480304400c0c0681d040000f142c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 241515656 1250 241514406 241514419
    0xc0c05041503170405030c03120f0f0d1103060913050c060d020c010e06100f030c05060f16050105191a120307050a1a090d020d110106030818210309 65
    0x14070300d5901c1d030604000a9500041d070302c5942210b0f441d035900d5a074414800c1c68024002c0c071400d41324514000c6201000e09004000c002e00c0c000c24144008520b50040c0138807141d0301002d2208210a107424814141d0001100c000d441d603a00f000810810749c140d0050129003001e45c400311080004002098107008810180c0b4450303115a42d0325110006070040101da0510b640c6800d0382c3c102081c48c0051424010b124881c2407036000703030b140c91380c0301074404241c080a4000c2868001c00c00803030030150000c010441e0084902c9041c0712030074440b982075104081054940350e440c3c20034011982801c8041c08101e02548508000880025414241e65100b190030184a0f104c5904041d1600c8028411101c0451340304040d42c4c64039481d07280100780d0402c02207200145850100028007035250004083e01c00c803c02e50001d0008081c0c40e00126035850110002d182070f55203c050001c0082d40120241220406029040c42800c2c114024030915050403a0084031607280c0c804a140c58440100c21111402416100c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 241516906 1250 241515656 241515671
    0xe070b0a170c030105040c0215130c03050a120e040c0c020d0303061d091006140909030408030a030f0b190e04060914030d0b0415120c15110d0c0c0504 66
    0x58030440c0c401203400740c0d100441401c2282c030751403050007036043c0e40d42200c0800410b0b0890100301e0341c54180880c41c550310400c0342c0200305000b01440ca40b04010b4440d10b01c400c1000c4c1c5a41d245800d003540c0d044100c60110420300d80103ca260020841044481d00390742c100700125850b240108071040410000c1d0080c054003a5400501d07100b034000401421610040010300e0b141400341c0c1692540c00c0354030036460b01440e44410500c2c1083c1c094030080b10705a50041295004c40c1703040011701c030406000700c901440100000503002e18248007500c90340015840018680309072036450f4055030f40c4011641d00c10f4201d0160b43c0e0300c0d00c030170080d82d105450100090301c1e076170307501ea24220005010070034001d45036400f074480388110294000003c14101410703060603c0440440d40502041e100361072004409074030342c00c1c424413801c00b02c2e00504004034050000e81c5001035859002d000405030b248804c00c00a848442d40c140c20000c10002000d0581c0d03a40f030a90103581e810344400090201c28012203214640f505803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 241518156 1250 241516906 241516927
    0x30406050d02041203020307060c0518060903330a09050d08040807080301030803010302041817130f15110f0309010c030314010902130504180f1a0a0903030e010e070b 73
    0x143c502030031102d00000031411181c10040d680f070700030b95011100319091503851040c41d84960262a0300c041100740700580e04220384100f00a503005600c0582c0c05100e01c014880c0c09004944840001d043c0807140e41d400101c45103070620032048024110f44480382440300700d20001e900000e42c0c1d00c04002601c1d04410356100c80c03402803803510400c0c1c0c0160030060301000100034014a80000d5040302c0c400c8404002c0ca080d640c0348840c044110090280551140e40400c0200f640000000d0100c401c045801d00d8129450b000700c204c150050b07402040c624908526a810125000050341415449110080140b41d401c1344034503a5134810303001c10780c0c100006403085804060081c0c0103280f58a0a12403210074030b60b1581941402034020000341c400307501031040d001075241018414400d801c150030700030710001650f41d1200e40070036607400d808443c3c00c000039201350428113031a510f260145903c5000806d101240b828002c0c151850100c241d4440d903d010402a0f0381c400c009603200858030a104500c0e1101503d20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 241519406 1250 241518156 241518161
    0x60a030f030e12011a0105031003020301060e0414030408120a032d24030f080702030609010c0905090c121b0a030905011506091e03021f021c02030406050d 68
    0x28002400303039556554660070160000e01d81030315440162501818020700b06807113420f884025801040344100c4a4041c00d041d40719000445d4400040c1c03540d0700b00c5645e80c0c0d0104c0e0843d205a40040034613031503982030004010054111000a440040045040500380440d0341d4454811000117401c6600000344070a1650098000c0240305000300ca50844c1c4460040e01c00c81c221004001c0c1010701c51a007844081c64502c000031041040e040d0209100c0d1300e50550b0340d40310310316601c400295810182031004600681d0108640761080f0640000405e003064200c03405004558542c2016109130a00c504102da120200300540d50184141c0040c1c42480c1c039115022409024807054110700f283d00001c2c0021300981540122070742a11400081001c00c455206441510b030645c000e400c00200080c90801141254140c01c40f249015003d05c510110380c0c85d8002690151202c2030368071444240502218019018050b80c50100d08070020020301901c404030007902c81c859801140184000800d981c5c983c40c02070b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 241520656 1250 241519406 241519409
    0x13060f05090a1101050a210b030105011d010503010605060703030902040609063809150903030a0c0b06030a030806100c05160807060302040b1801210b01031406030303070305060a 78
    0x28504004604040701e980340c07110b401d150203491a801c800d50320704065218808071002448240c2d40c82203016003511212140d58180301030b0365101a140e078451b03082ca680a05c80c0c03d00a201490125400d8140b48504c0418100c050b440a4801d92505c502045961503003811542400d51501c0c0010700c0721820b00c0040c2c0244195049009080c2c501000410303064151038403420908100d0304042c052907008550741c81e002d0881c6480031001d62040c400c800c20703424407100642d030405020f40036034105607185000c031340f554000344100d60000d0f502c800800244504811001e070822002e90180442c060540c9002c1e05221000d030059001e40c00001400400620600a40c00c3c41a404010780e08008103120402400c89200e00410392a4051707588005002e5001c1d1007104c04444010700041c3c149041d42c03220400b5800d11048107410710080300c402000c9000890007003170030f031480e61600044200304400010f04441c1d159100b16900c48501c81032181d183e4000007903e60005103490080740581d03804000c184501010b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 241521906 1250 241520656 241520681
    0x60a02071e05031b06061c0203030d020307030903030b030a0c1a0c0a05010902190609030807080d0203041401060b180913050d2d1e02070512010e16050303031306 71
    0x800111400304000400144402c08134125050884078500b8852511194281c13001c0b03a200502d120528240d45217903102e0403401d4001401d0ba403e1143c4011110180d90048900700c001994860004040607050710030750302c18281c103a0003000034200c2590f0b6050700010b07030f0185010400e0080110900726140c81c0445030399130680c2090f41c1418410307203004c0740030703000e0719100300d1207800e602580a00d0100403030101c500312502503640018591031a100d01074a64000c5030240c880030030402042080c1025800110700540c49620300701101200809403500b115202d070444141290100080b07613044003a2000100b620b2422200168030341c803500075072846c01c00000c000401501a0f00c0c0c21945058000b070040d0b42740644001014038400da4010100c014684155402e40443d22444c840d54500894022001000b800d0740115600c483d00c680008241c01103034190301d8000d030744076001010352000901c000011804901350700c140c00f42c1020000307600e83c00001c00000d043d051010050301840f240e40c204034030700000e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 241523156 1250 241521906 241521953
    0xb100c0809090c1905120f090304030318120b09100b030309040b0a0905070c050705010503011a0903070513020c1605010c02010f140708030403170c03150d0c060504180e060a0207 78
    0xc0000080c010b1b03002400c0c21050103028000203072004072aa013229100384c0c54400a180340c581540e8040c3c50080f0030500c3d900d00035190741c401140c05100780001807803541c042e20000c0041d2620115062904a0f40742c1404840d505200c401070880c1c4000080e031740084403c031004501a150400800c0c804651a4002e40c0454100420301801e1508200308180341c40c0103800342d8003029103035001544c462000380304003c008401d002040c00074604d000068094044010150f0304c14540e58800290491a03282c01c01d030815a0004030b41d0250300b010804c1c5510304200d00c0e1001416450040081c0c15105e0303880004c2d040c45020340d0908412482002200000405950b2503600c8182e581000303040d40e00304850850100760038600d1700e058402544c0308944100c542007652461582e411003c2011402e90707040f01c07904004890202800126038080c0036026100694030240c43e246442d03c00e0340d81d60f00343c2a1002420f0f16111f5801403111010400e160f105151200140c0e0b6002545041892080ca0921141c0d5000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 241524406 1250 241523156 241523197
    0x111030a03020a11070e0406091e08090f03060c030f190c0c020a080a0209040213091502030f0105091003031b0501021201142209030201021207030b100c0809090c 71
    0x681541c0500f44044060b0b80700046142e00031090341d07a400c92400741481c420103900c009070010f4140c3c0c0000660503c07c40050790a2100143c03050900000308508441110000c07803454070f541031107210700c0c50149040700201602c1c2031142c1c60380200d200c0581496400c070000f500180c190184900220202c00701c44000b040f007604901c2c4010220034002c4001c91107010603040000d03050000081211400341c0082044540380ca0700d60800130260561540710b400241c0f1900d81d100802ca0402100c00c08500e40d00015070760b840c2210b440308500c00c05800c01c3c0d1107141038105000310120084100820f0780d41c58142040100c409544a844e113030314010740100b00c0e6000213044150f6407014a0701034100d8404001d405940742c401c4041100b611074118406060001c2201c0c060740d40c41041d0049280c15009000052602096a03090680e444084820001007a280c1c1d4a4080906041d41890483d941e14a0440c6000c00140d6030981284181300c48288244a1030300464200034407030301210504449201c405807070b038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 241525656 1250 241524406 241524427
    0xd020102250515030f130c080a060e1207050d03021317012a170a14090f0615090a09140615030c06090f09070c0209010e180a0201080c0702011103 64
    0xc120707401078a0240307448200c00041c1a8a100a0302d005a40e28902800503540703141045100420b8600140c0d00c0c02d0f242d00c0f00040102040c4241503410340142c0c004a4442c21a02915140402c12408003500c140304000080200303c002c0380a140342000362401594807100c40c110f603140491940c0215660302e015102d4107084200550044005806168014401482c00d0600300076030320000c02c0705400300d040712040d500e100040c0c0c8840396201d441d203200001c040e5500d0510f4560850b003202c1e01010b40e4801d404400421000700256a4002c0ca000b07e000721b40c0c001500406d0210002901440403180c4a0005008121148461888000700c100860f241407601c80f501080c641400700e4014040e000c2c0325600d98880c10500308881c210000a01800c142d15000f17418041c00311001880103080141481035180103035545544a40205842403801e001c5040480250407450f114030020300e00365210265650050340c0040620f0717445a049450252112310500050b5001c3d0f4200a04001c0c1d40400078080f0b600c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 241526906 1250 241525656 241525723
    0x61404050301140a0507090b0306010c050114040c03170a0903060905030c0604050729030705090a030602071a0a050411120f0a0c060806010503010806010e060d080c0c011d09060d020102 81
    0x1348000c0d900500081d185c200060310b1220310f0b80121201200200001030081d40284194640359100354000950740e82d40d50a2440f003484203503012900380c07078071060070400d1119860101d03e100300e5800c0424079001c280309015104071881e200007040941c4400c10441400000d00c00c1d904c5088080303050782d040b0301d000c0ca8019100c100b207010b400340010302914009105641070b0f104002000c100381c0300625540303a0359001c2d203003501702e080c0450b445000c0c0d15000c00061010300191179628030075030a403182c071030160010540b0800000c00c4100700364540b808010100303c81d440c130120003003810744502000b19418205141850999001c40c100c0e071180180450801264142c0c2804442d640d41d03d11001d900d44000444641c0b0080c45043d03602c1e40000014070014841e5240c0c2a0402c9006010354040300705a03603483e400e82c01c03403c3d10501603002580040c0c10365801440d50100740501041c8010011400400507042203009040d0b54090034000c0c051008690081013845c5240600d60403080c61902c605280d82c03203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 241528156 1250 241526906 241526911
    0xa03030b28150c0b04110f03190b07050315090a020405060f131205100c0e120c040c020c01020d0806060706060305030406030c031a12160603020711100906140405030114 74
    0x2c0d00c0c840145904003840c45070803500c90013540700c2a08403054545031108164050500100c540c081d69503000c0c4003442d64100030390000c4240b1000c14800440503070810308070409000704048240320f002c02c1088a8500c58040014101c0400c944c030a407a0303251030020b80000c4c0155048150001070003c0d055000b58441c80280200e1542c004180ba01c098481c141030744400c6001200038500d42c0320b08030b0b0380b2807501a82c0194804111600e00048150841c0d40064000750300200140480c0c1c016800003400c0e41014014801c0c02006800200071914140000075502c0010f401b16a00700b00005002c910155540d0040380d00c501d8004c1c6061007030903101d06140707803079611600c40c2d90042031401c0040070080d8020f000311400d229050780400d041100310b5080c400c0d016100c0104580c14080c4558110304441012800f00c050003c66500584480c01031800040380b04212641314450000704403516049548001800185da01030300d4503051015002c0d5200a40303005e150030041c0c0c95424581a0030303211400090091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 241529406 1250 241528156 241528169
    0xc070507050a03210e030307080c0f060705180a0503070609060210230c0d0f050601020c010302130b0a18120b0a0504020d140a020405040f0203070609080a03030b28 72
    0x112410350780c000300400c15060f03220050071800c41c0d0b0b21142030882440008010000507050010402c044500000d04640c0055022200504046a0054000400c2040b00c90116208005111508080e2409003940c001c140302041664000041c20090b900d038100c500006080280440f110a915460068440b00b00c90140100501c603481c2013010755605400342009445ea601c2c0042c02c10100c02d61622440c1800606510b0304031010050088102010320681c042600010b0000542d810a90002810200c1c03000c000c0f410180107000340c003014010b003e04402154510381c0c1c900e91380d5210001c03d80c0d50008420559007905610328001a014201080520255105000d11a925580c10b00c0950031210241c8005e07401c00300007031043c1e0000e9944c002c440c4641c104a004c8036421100f0342d00060540b1001c550031142441a552a8000c5082c01c02140700a050f05060a00c07402e0b080141e10742d610f4100000c05001c01d0f03180d16901d0303040c1e15100441c02c00e10201c01942c001030100c01950590801443c812003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 241530656 1250 241529406 241529413
    0xd09050c030a0309060e010504270605010e03030909040c0308030703021e0f0304030311131d06010507051203040c0b0a0f020708030301050a050402031f1e0807060807081e0c0705 78
    0x11002860081082c200440d403640361842c0040c10701038200d902c06007603a1110305000c0100701c0400c45c044404a03102401c00c0044400c3c8290740c070480760000b5286141d2046c1e05001100c03179500115640070040d50345000b002d550fa0072a550312424011480c81c0d2a900141c21550000305120203540e060b0021704100203188090300b4840a80407007403204d8880c02c104405000400e10205000074070035001600303054150740ea03060a009d046204000d80d45107a500c41441003002c006c207140000e90200055600620909000b42444043d40701d041d00d40502508150b12001c4c0000041c00700803104100740b01804042c08001d86030b50140f8005003040c029200d04c407001d4481d2010014040d10300100700c81c169040680000c01d0389141005003c06508081c04a80c82200304811403200d8685041d0b103080100003003107410b00c1c0542090ba45184101c5103810a0300e00b0b801c011400c0c418180c201603101d80104407882c000d4090380c6c80200c010001d12a29456480c0c0314079040521801d070140c08080c0103003030f00460030f6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 241531906 1250 241530656 241530673
    0x18080f0d050705070f060e0106050604090204050301050c0f030f041a0a1d010c020c100c0803090604030908010e030a0f020a0f081b0102030105030d030e0a051501031518080a030b060d0905 82
    0xb43c50500030580e0003070650381c0598405c00007410740e401454403000590004140c860710f803400210f103504103800c0309886d140c7c045010040d52034240504c5821030301c40449a880e240740146248050700c0003d00020075500080089030030090310a00781191030800e400244003905043d0013440181c11400340e403441d0000c1500c002d5000850610a180c07010943c0c0c1c00a000c0400f001c4240441081c40240c603900f8400000f070310602207682c09000b54403508080000e40102d14240ca80a0110101500140301c00da251407000c29a5202c00001c40f03007540841d0034402030404000c5001c9242c01030055008003940242c0d110601002660800313004103544040c800350070841c0b1640000d080340000d1007160b1f4141e12104129640c3c50090380180d0100c2007480980d0103074055500d0313071441c1c5801105120303420442c100040042c40750341d00002c000d1070f0301c00406110080c190600680309110200001d0f10004000072035910050081d8401e81d0680402f800d40c1e03071580c60082010004010211003034540d400f60501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 241533156 1250 241531906 241531921
    0x90f0c0816051e04021201061404140103020f0903030c010f0e010c08060f01020304080d0806011407020618031f140106020c0a0b031b0d0c020f0105100918080f0d05 72
    0x12000000350142044541c2203281404004800b42085041148001100003550075520f45000a00950102184604995240030b80083c490f04014a803158161010300040c840051740d41c40078001c0c131400340390240e02c03001000310006c090b208858400754540300c0028681d010141c1900940d00f00c03140d1040401c000392035518842c0c240c9012042000002d031081e800103009191a0741402c0110206104507810f20362035226040ca4a444503042d0000325000c80700b002200e41e4040c9402490b00c5401b82e24a083c41d096502140303050280ba24904580020b004000c9580c1d04d0401c200d581040061400a5200140410300002031040342d012150004031400041070407400083c0c0c0a22150002d0f04002890f85884451802900003a003602e1110804101480e01c45403218058402e10301c1010001681d0400408080c0c60b145401c42d41246590508081041a0264844260444102401c041342810700c8521440782481401001810401d003c11101405070030040509075883c100070080007180c03102c52 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 241534406 1250 241533156 241533163
    0x40b040e0a0f180206070614090a0c0504111c091707060605030a0c050d081e040608090105090706110106030c0306051b090d200a1e0504020313060905030d090f0c08 72
    0x403d04401440108079410040c10940000d082c52406030340c00107100d02084820268030281950590100d911441542090101140080008000485040141d42c84440c4030403078900840200c43e00c1d40041c0e140c9040402d0258105a61091b4032550103010100c512180000b69040000140c0d09a841c0103030203d0b1a00740044d05400654010a40c08901403402c820428070b020300460480e140c6d00180244c1d01d04140d0301c408002d0504190020640391030070000010490b01b030003030102900c0c0e81040c0600c01c4804002c5001380c25220b11340750900580342c03c445103c0c05450075500042c02440c040342c0000501103241d006901511080601c9550102d64041c064514080c05041641c13010300503030002c00156413441d25600e983e4142003002144400440087c0b28002d090740320f0381e901011442c083c8015484480086c024203000c44045007941000031007a0400500e240d0000d005550301d1034071000f803150410a4610f40041204140004032031840c0c58207510340008000c985103071140f0310101d0f207200c010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 241535656 1250 241534406 241534421
    0x16060906110c0a090209190909060b04090209061302120c0910080408040618080d030b030706090308041e0e1003030f0f0806040903031d061503070602150606040b040e0a0f 75
    0xf03104024003070400207010003d61140c8404e03680095a0403542207111f070f070200781e00e00078a6203000024010800341003e1080d01c81903016240701e0f601c1c1070251001a178810b81d03100e0b0048401e0714400c40c507101d60f091400c020312603081d0f5203801c1d4444000700403004400c2001043c41580948014440c80c649060580302d070241070350014070034039040c00240038051007210034280c3c041ca41648030404075a6030010700d0a0480c28440000000d03101d01030740c1603d040c10007084c0700410072840c02d0301307c152440c1c503a081e49010b24007400140a072545c0340e1f450304403100703510b6078054072414842c2c07115420800441da0b08661203200c201c01041614494080c0e050007590241020807039a2201d0140d555828208401807500f41030480c14903585404c0414404d240e20543c001000b240700080c1100e081041c103002d800345101c42c60742e02c2580203d105100e072a0b400f00d43c0d021f400444003a1b00c4200d88880c0009101d03401150401c6004c90000b1a001490100100c440c501503000750340c08000d040d910070050300982e08903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 241536906 1250 241535656 241535659
    0x20a020714010e120c0103060506130608090a050d020313210305070201020f01020a0c0c050301200c0f06040609030e0904031d030c04060803070c0605070f06050916060906110c 77
    0x15500412214000c100308108080c014034040e2641c458010000d0f80020018400c1d00c03076a480702031451140c6d40c0610505001d4042207680f541031401040c2161001c80313a6004010400c041d9101041407441d04000c0c0c1524154040c2c1540d603101e2030300800035075940168040010a035884440054508a040344031140e4410300070030105040c51903201580d2682c0140f2049045224580c0c1d443c0e2501401e00c050714406130203035901600c5030b026040040e9120444e40295101e0791418090f503000b071000c2410900c01400c07140801d07450310310400c100e40c10103420074080340050040004100400c0302a030300c001b21007482034840c0a11641d0b1402400000d047c11a402030104014504512003003061701280006203000804880180302104003180945581d58061030440d03001241070800c101c10441c40d640508240d180003070a180040d191032034100300010001e0b0060b030b5224003042e0b69000a002c00c25074a034501d078048040c141c0d00c1400812500082c0300341c000080b2444013405651202003072600f240e000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 241538156 1250 241536906 241536913
    0x503010e070503070216180b0906030601030f0c0b040806071e0e01030f1e06150513090c0509030f0a062d0b06090a0315231501030b040f0b13020a02 65
    0xa5001c1c00341d4003a44090450825131184080103c11a1104402d040c00f40410400d00300c0c2090b001c0c030003070056500708c002d0745104500d8442000b0141d00c000800303504403a040102101d04500a04082c21110801d03041008803800000b0003103104140054001d00502e9107a555041c03465441d0004840610110b0794600082c44d0031500306000d40c03090300a0704045090340000981e03045103400c60284004520212050251282d004000e15002c0c103100c0c1e01400750758204180f601000ea04d49022040050059401542c2e0340ca402d541c0180c441d00958200c59005821600c22880640d241641c8603818401110818102052200ca0030069203a05242241e03141c440e506100f00d4201e40c4001e8803500e0162900100305110b030401680d296140c0500031070083c45078843c206108542c000603218101c01007400e04090303410103101005540c90f42c541c041207101f00c1000182c14040105d01510440031140d521a041c20641030a1200d00c3d44100c940f41f2040704c249401480348072640c0c0a90050098080240c0c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 241539406 1250 241538156 241538161
    0x301050a090e030d0c09090c17010602070608012c01060e15090607150908070c2405162414130206030103021c0b010f060224070c060b06070506090d0503010e 69
    0x142943c02000c05c0c00510305010282c0c540340e13080c0d00d044500c10112000003a548800ba000c402c4c4d40a02d0b050b0251aa500c054019036040c000c024020b07a00c18031907424a450b030601040d641c0b070001441b40106106c60721000b221543c2d11703500100328900c003003415031240e100300840481c1c1c1b115a500703c0300c0c824030107407400d400c0400c00c0e00c130541c25003284030807075001e96205e007420320000c1d98110007004044e114440b001d00f65424000f1040854002e402480c07860002e0400c00d4042a4102c01a071b800f24a55100a55101c10ba41c608106180d01c0c034403070b40018112211801098405541141c940f24000c5000414030781c4d142c4a001d0307900a0240c40103508003500b00014070160a1030000b01c0344005001d00b140003074107403542c1c4081c0d108100341d000c80c5c508102c000c000d100d00d039414000192100142d4056105400c60b521340308000710800751085050051000041c4200b250310f4000081918004003002c3c0c071000759007010f5842c0e51003155001daa6004400c001405640104190f038180c52842d64410103a9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 241540656 1250 241539406 241539427
    0x1218010e1e120304030609031e0c0f08030406140a0204171605040203040203120706020d0608030901090e060103090f050c01030c0c0804050411160f05060c1c05131202030301050a090e03 81
    0x340302144120ba40b0b40800c100120200320f20f03004040c0c0c82c2d442640c0d2003090120b0341e15102c40d580d4016141d1010408000180c102151612480340c1d100c5800280c95641c9841c0c0e0319061000b0b20f00c1a840ba1680d505400800c03a00356130b19406041141c2503413104a0700d0410f001207031619100e040d1404c04906105010a00841c00c1c20360245500900c0601111201064103560200c580c01400341114955000603000c010444240114002040c002d030056041048881c0042c00300d40c00d901440b800b60200c41c1c0002c4490388a40c005c403403110741000d2070b038004111a00300349403901c030a4650103001c80c0c00c0140725008144a100300c1e4040c82d811003800d034101401e1600700000342034500d81d21000c41c007050103241d000c502c07550300c510442445074031401200c0b10340740b03405418444001d0804036445010b108400c4040000803a6403404004001f0006a071b54401c0003254148880300005003040c9140705000c010b56030000000c0d410383e0411a00342d0921545d4158080555600170301c8401036030410320099651 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 241541906 1250 241540656 241540669
    0x50d11160b0f130e011e062007051804060506060903120a12140915060102030a11032b0b04110405090615030702010903120b1804051218010e1e 63
    0x4456180c1561410403280140703a000c1d000f41d040703000301c011000010000e0502221000c2000300300601d9500e006440c1032800380c1035499400c0c400c0c4085a03002c40072007a010051000d2005440e0081110514240320301030f49945002c1100c045a07100c1c030300b001181c010720f040300503110340d110000d0082405400080c240701d1190080440c2c0d009004101c40b084458040a010b004002c2d0142d040780e91807881e081c2d80942c909111aa03040042000d1601031203060399010084500e0307503015081180e03001562405551a500c24900c410304020034150403481200103a1842100200d003900050044824400810046400507040c012081100f00410440c1d0304180c540c61f5404003005200040381c2d80310440c8400c2d01da01c11140800140d640d00381c64410103410111902000741128000c101550020000c54083e1400507181441208103a001074200b020801c264000102c0c40840d5986900080401080f0441d19509984c040384070340c00550803500b07000c0940d0105503c0074031600703940480303070b010b0001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 241543156 1250 241541906 241541917
    0x506060111010f0f0f05150a0b1b030706090506100501231303080408010c080621030708120115021b01050a0903020402210105120304052b050d11160b 66
    0x1030765502c3d101c92800b490304a101d01381081003040d801017942000c1031500303801c40b50024420f4000b0f0f001c8001081d00b540301c400d1800245c4020340d464554a0f112004001c0801c07d20b4610700c141032200203140360804c244c0b074100242151251040b1032150301e0300c0c046d080c005030460040e00d0000b0107280b208141403044100c82d92044104e4100685054490702004121035056007003074038030319070006040103200030074403441c048804103250175515410080002124109111441e0184071200c1e40e040815400030b02c21600642e6001d040079907922520b0707407000c41c070f00000d01ca40c40c291020072080300300350750001c40e40160324800d529291007071080b2003005541c15008030201c001040811080400107031210700c018500c65161409000358441a005210301070481604240d00440b00c003030b03118100300b0000094400b07440003102e0582d81c80b41400499280e80c1e01240c000001d6011001041003842408038032820318816507944c0c00425102c00540c107981340e40203813001c00300c6403519404000d0f81180101400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 241544406 1250 241543156 241543187
    0x5030f0a0518030d050412020c030705040902030712060608010506012a050c18150315190b060f0c01050c0423060d0c091d13020103091506080102070209100305060601 73
    0x3455041c41c101540b031604811300030b40005980d00c0074441440f84003201c01140400500c001d01d4024050030100380c4910041c13081901031303516000c0d0802103541c1400103070094030420007601e420841384d044c054058a0b2910414010b0351070140819415445000401c60010b2810340360705064030324100301c070841140c500301900c0e14014140244011380e2240510710124185e00100300722030600d20300c0c862400d00c00402e981e100c0e41c000001180c2c0e0f040040c3c001940f0110980d88032101170041d13008500603041e486460b652201d4002846c02101d01e5007030140001d01522002040b00355079028001c4180d1041e070048020441c00080b90b9030001112a03148421002c01070009030030220710310345400035200341d00c3d07031500410025001802040030b86001c0c10154401c40c0480705181c05c28002500340f42d008250007904240d200c54007101480540c000440d0003030030310301041003020b5131000140d000f5001490202d00c42e035405808540c120a06107000f1098a030444060400c0b6110f61005450039050b10001c08e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 241545656 1250 241544406 241544431
    0xb06191b0f08030a0b090c070c150f0503100b0417010f090b0606090118030501050f130b07050f120c040906090614041806090804050108090312011a1c02070203010c05030f0a05 77
    0x4005c03a218000414010784181045603240c203001c1c94070503e440c0c2c4030340010043d03103215001107280036404024148801c0603410115130320344a111030030030708803030a4005c0c2900840029000402400c4100c152120074a060020440182d440082c082907030001c400c0540b02c84801008214149081c3c0c1c020014118141046c01d00e6000200d600400040540d20942c3c40317942d50f0f82003006520700c0300e0381c070342e030211329a000d2007040d508030f179618084100003a10010030040007080320901440e04070110740400e001103003c0000c5151800020740d10398020f010340300302181000800121004036004042c240c2c1c20914400f41c0500b5001c003030000a00c8807980482002d42840a0840460824410034130309500600100e50b40d60309160001d004000040d000501aa20403c083c0d144034080054150550341c200c07020750001c0c0d41c1341d1444420350055280480c0d642c40e0000303220b18a4032f429070050428501c2038009100c50390754208180d5031400100c42c1d0030070104541e0b0000d5100c84003540034651000380302240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 241546762 1106 241545656 241545671
    0x90c10050d050402221b09080c13060f0305061e06010c0201213801090605030402040906050403020c0307140a03150b06191b0f08030a 59
    0x803140c1540d6030003c1421541d925904283c0010300032030440390140c4200804005052032508100c0c680c481c3c1c40b881080a005803c40001c0b0f900c004060b05d5010740780070034025400020300346140c60a0791000080b07101d81c6805030f031401944c000d40041210340b51401c111a02c04400110310040d006c188000c10425070790100e648003042d68203281903204841006806000c072030342004600ea03c81e0401c11301e01e0a100b007404000c04145840610074047c0f0824030400c18407001c0c134402050014844002c03c0c403045010300000c5406ca440500000b520801e151100130450b402580c3c2140160000c81c040c03500c0e031608010100c094068980c0500e10b03400700c10f0016010000790f102c018410703240c03c020200890b4569010610070000a04902d41d68100020342205451400c1c80d48000b2440075003107800000786000982e103005501403480d114003c241d031505c42d0140c100400306d0600549480d01c = true := by decide +kernel

theorem cover : BRFrame.Cov 241366906 241546762 := by
  have h0 := BRFrame.cov_init 241366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 241366906 ≤ n) (h2 : n < 241546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
