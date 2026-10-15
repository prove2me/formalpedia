-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4956
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:16:48.403984+00:00
-- url     : https://prove2.me/submissions/505cd45f-33a6-4f81-8332-2c31dbdddabb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 891187050 ≤ n < 891366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 891188300 1250 891187050 891187079
    0xa0b032406400b030714010e0a060c150219030605030705120304030609050307120c15050405030a030c110706020a0606080304050d11010c150b03071406072d08040609 73
    0x4a8401c0038000e001488000d41e8040040070b009005072240b0102c96103482c100070300301c080d01d4030340c404610044681c40010064040709490307610548080004000c01500301c090f5842840c0c010011518081c801c3c032040380641303c0d1517108184840b034150b09101d0b05074154441010f5070011420384402070703a00c50403c4201e21204e1210203c1c0e4004200400c0011402d5102c10603081c820720941c2d0901c00d05d80c070340d441c10200014141c40480c10909a40080000c042c8800311820240034041195040a07260513170b5a016260a010503d5607800980d843e0714007810900c0405410881116061340d02c80c0300003074480e00c1c00c1000b01c8a40381084004621144003000fa50140d80f4040c21031450603500d603c0c0e000107221042031440c1402101d02c5d02c2c20214509254204101b126005e0115002100c003060506d13001c05940b180c80c1200410310402c071f0036a1224101e40c03260703410000b0b000c019114103029851809000c040800042c8100c1346580800601c5800b038002c0b5030b041e49030740c401c003036882e95620300746c84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 891189550 1250 891188300 891188359
    0x10c21020d18060c020315010b031009020406081303110105011205150c270a061d100f0c020411070c060f08010b0d1802040501080601170c090a0b032406 67
    0x914202c003400400d01c40ca4181c40524001401c03a03d0f48500c020005200d0f138002c6e085242c3c205400003c01580c0f85402e10319000800c2207090852030245000070083c18500068110143c665001a41809251050707400c180c441c248800204800d5030b4030340c2841d64024a0f003600300c4060123008030315480080180c1840703104100e0011783e0f6141642408040b20541c0c0000c982091a184144440030540c454103003100142a03031351290004a0207400c02e440b06180e4a80c0503500c50f018949405650503444924130903810303d10304240984048510019024007401110154000d00106041e42480791104004080303840584602202d00645070081710f00300c50901a064465008000ca0b104007605075000d0b010710510a2403031140e2441c10784c001000d0b02d4081c5d00c0850079910200c014002a03d0011307004580700440001007036031503800808a40c4505004140ca125141d0707800c00700c81c070764405208205001400d8004c4211308504800b80400807030041d80c115024170030b50211115880e44002c4940d00d400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 891190800 1250 891189550 891189587
    0x1b02090a0209030c04150b0f0f04090b01030b06070c0302060c0309030a0503070b0f0106080c130e0709030c050a060c060b0114030705042606151c0f05060a0204030b0c09010c21020d 79
    0x14140030b0604915400b20034607074210607040000271548210300300a00007400b00c500300070a44401c41400102507039501c40300c01d031288608000b040006200f11440b50210395054819648415280c0c00c16402c500a10308000d4160103010351007000c002d0048010308183e440380c3e0f038400b104c0e1034442040c84401002d00860303012814600118000780000c0000e00100d4100405200245807114120502404c06440c14004110800b030701381304202c003042644010340130685851045030b18286009214440c000c40c007525007582e03860081c4840e445182103260f102e038000c40316550307400c0c2000000c1103035105128114080c4070b24146000c80c4c0b080d407003d0902c40f00d407480c000c3c200ea07210414455070800501514030381c07000980b502c61001c5803032040c009070124082c01c0740e4a06160541040c5046c08802044140316910401c8280002051b2190154012102254050b195034003080162100c00e01c1301f0000c2c0900c41d01f900e240e1480102c2d80402e01c080e01302607080e2103d226184100340c540500c48145070041c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 891192050 1250 891190800 891190841
    0x6051206010e0c0a1211091c060501090513020f0d05010903050d0606090b0f03070e1002010911030a2d0803010f1d04050c100203090612010e070c030f1b02090a0209030c04 75
    0xc01990b5007190b0315413203401b51094545209840091540c01d035101e4000100c0d40300110110500595119042c010f008034407040c8103500d80441081c4c07400100c3c0c01c3c0240308183d00140d0f8035058403802401c4030030652213002000b01081c6410050110f410801c802c003021410460003041251041c1c01403070440300c030f45c014242008001601c0000c0c98000501180c00c01100581d800156545e4a0040500c9541c40d000014128001c1c2041c0b00180c0ca07100810740254006801540020501e14441d0300c02100b403414a000d03003245103000000805e11a01c040d111810100010584a8aa0302030030216460181800107510142120440003201124064410b400029019805003860040c50f000440c0c01c3c410b491601d04810b0000f44035400c1040805224111f071801480303c808000f14441c2c00a10310b040c00c4021000c0b680c0d00401030030715140304a042261035000500e10034804401201c1030343c0d0090613402070349000c41450000b504601c64141c0710341301d2101720000d01e0502d40305610160314441c052102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 891193300 1250 891192050 891192077
    0x62f0706032c0a0f0f02031507030e0c0a27020a02010f0501061d060a17102105120a05071a040203010b180a05070c210e0604060f0c0606051206010e0c0a 67
    0xf41101d0304c15054907407001c45207280c00165000d21102000c4010901c007400380303003403010009040f0381c4850b00d0103641e540081c43c0044959203008446040b56801c035a220021204814035030a2111207c08403a1040d00100740b05100c00e4040d00001591200d12508200d140c5c1e940f04122840b54000e81040b5000d48045541d0702e2a052910041c841e034040c502303243c20000782d5250342041000085507100f1a03c002c40d0300510200442070032030103840039030810501d951506030b200c640e1611410080e100301440300003040c8401e6400f07071041e6106260410550907454021000b0701040c0101160102d11030b5107031140910041c40c00004110700c4040441a9881c035a90790804e042c02000080d052400340403808a0445c0010b128095520315400088840580300a4811018108080130440c8610031a0180f005005c050307445403c1c040742150500d0b1100d034041050401c1c038010111500400e0f0401402a805032004000040290407503048a141c08110390b5680250340b40c90042946900018508411589 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 891194550 1250 891193300 891193313
    0x40b0306102321031c020408060108150c1e040803030412020304060507021e090405030a172e15021b03030f03010b1c020a08180106062f0706032c0a 65
    0xf0f100da00c1081120300e440407801c4450b01d04440001000d610540000f0144030041080c0841801406600c00801e1400000b104414040400a0010101c3e0002094218500c89040328084110003810006662070f51202c0c1140c1d03c0c0e5200300c4040d0b50550103110b22174034143c80042120110f884a40e19a401c28940b942044503040c0e0740818500c40c200070030034044035a50742c001418019032049004550f50489124060075942d0140316807003100644808000c05010540316140005e5008108983ca81d801d560201e08030314901e4000b2250042c21f140e1fa102c859800003101780c081d12a00d94000704000d00b0a0405942e4882c164480303000e01ca05100410000c00c200d00603011a89c51410441c1480b1002a40d4078104c3c2c2101d03940900168861003842000f01c288444100d11052903002401442d0422502808114801301c83c8118071448201d41c4441c0100c8054200413015840e003560700c480d43d5142c0050151041d5a0800110700f0807030100715000d41c1050801c03414605050107803011489130388402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 891195800 1250 891194550 891194599
    0x3030e07081e16060f0f140d090f12020d020c06030402060d02030c2502101736070302011106240f0301020a03060906140303070809040b03061023 64
    0xc00c1988102400540680142c8042e40040c06051341c442c0c13050701803005e00038102200c104800c414006079020142003503c94000301c1e86038030107006000c00d0201143c50006d02c1010000400740c2281c0d4440d64a400031a0b012a03410a0403029500701c84442c150b4500b0441075110559000758400301c100a80c1022100640141d680070441584032400c04030024030250340b0301d034240414840103003000d4921086140c5000250101c0302c140c41d1695020000e00100101403002030714071070000f4001c4030380b4142c100c0c5c460f02d02d0b5400b803c1500405802d09100c100d040d52440745000032404a20103403818400c181c1c0c0050003900c140c0c17449110b080c0b461411018280c041401c50741c40c60300650320022800b01d0b500d0034002001c3c00c003142cad80c001603060b2900f4003560881e00a500003e00341d040c6400c09100700d683c000151a4025081a40780303031f4540c001c200190007044880b4a064140c00380c001080000920a903c0c2401c5070a62551810700c040b10110507580d06906a181c0e640c80304400204015120342811107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 891197050 1250 891195800 891195853
    0x21060a081b120c0a0e160309030e0f241309020901091e0302040204030803060a06030b220b040501030308041203060e0f18070b0a02070b031614040e01030f03030e0708 73
    0x54500c402ea218000c540e0a0815801c0301c03142840305070600454000d03895a0b03541c5c807000b42c1f404000707044103550010300f5000440760092107000c81c005415401e80c0c900c9012448d0110392181000303214143e1202c1c2c240354201180c110b9000c41109000a00c480c01802200e03030345401607660007a0b4034180074481b09a80160204c01111200307000c00400140c842d440108040d6010740411074072031038848104001d00710144c10a204050800f50050840d0300c5001e01d1005511a000b005840310944d05900c5004110004040351b01c00c0c1030030000400e042d00301c141e1a01803401800740200c0391044002c20341c249c40031440744846100d0404000f484200c08110100e8011107003c071800705002c1c000941c5460804141c1020b009510700042d411009901004440700070300c44452986e0540c504030000104e111003c040c22810701c07440c0020308c85401994412070700a4803100710749015a5850341000f40388911001c0040700130903d01001c944242500181c030200702c401101c0180080c3d80c041246110b2403031240807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 891198300 1250 891197050 891197053
    0x2301060801020310080124170c0414040b0109021206361608090303010b07050a050f06190b0a06030b030109061a0108011512020f21060a081b12 63
    0x4168410280000c5000c4c0c100000c000d0031941c14001103d084a4444c450644c50f0030f28540b20b80070880b400c0d84503008079203025940c04c0381042d0745d850440c200602240032641c003501c0c12300302141c0d603801da84046020f240102c1400c01d145e03880752150303002c0f446550717502091212890000342c0f003860700049150ba1031060010504150560700056210080d0011545c004014414100084440034001c0e03820b0416240c13510040b182401c03003490b83c803440103025101c04504c002a02d5000c2c4402080b0020f07505921500306c5140340ca0342c3c903010b0788031102070791505600f80109805140000c000c8c001c41c0c0c0e6000c8006c2052058900e4410190002c0c50701c50076664255484a40590104100d44112001080c0445104078040d000320700050801c001604017400c00e003410201001c080364841200340c8600e103480c100603a5a908074002c00454003486445401707002c0c003118522850112011410302840058881c080e01540340d12105071240e03619610080e15041d404d0b00340da8985045c0364040c046514580 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 891199550 1250 891198300 891198311
    0x307060c09270b040b1c030c020303030c03091606080a0b2209020301050901060f06050f04210507090204080a150207050307030815011d061c0c1101060f032301 70
    0x1900005200c5011200c0780481c10702c031501d685000c1c1e050040d081c0c20141114200802910b140015051000310f420240c007501c0c4402620b01010b001c0c0e90709020a580040031030340c807071070714258440d00d5034800c5507941c1040c024045080c1c0f08284000302c0b02d081d512030b500c440c001c4d40e80b00240200204420b030701e881c1d4400b2070300c1e0745240c60b80c103220034403060070b88407500c00304952803180185404c0d2407014140c00071a030701d487c004002e00401150f2540c1565001e01d0640d0f65820744992111040c00b89810401c46d07000c11408944545d03010000b0604900d21802c00c2d9141c0b03550320304030721040740500d10400f00075800141c0300e000041e00303542d400004000302d03200c0181031814a40f00c1d240341d0740000c082200400c101c1c20500080c28241035010710a05024038116021401041c00c0c3c1030a142c1c0900498002e440104445904c8400d81c0941c40e01400e03208000c0040030700c48000240f00314054a031585003075182c49000700e441802c007150501500e070480390341014407802c1180c8184182e1844a940c07080d56a90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 891200800 1250 891199550 891199559
    0x7031a01090303050913112502030d0c060e030d0501141212090a080607030212010806040201090608040212010507020d2304031e0501050123012d14130311030f0307060c09 75
    0x280b050b020055441c019003032321075054049403054110740303407080924000b2a1803150f0041c1c1d4006501c10f030700401d5240c6003440041c0d52a1410150116803c058100c1c000807420008420440d440541268500180802918080020320624480105514000340c100c20103c41011070300701c0040c044068068400006180e0320700c1c00c2c4d400c064086d260040000c0d0000f072029201c0f00d80d588041d000d0000c08000e043d05040c2503002a2601e80c0d640b1501c42480540e1000605540d0b4004440742e8851400009001514101c4402915110a643c8410104141884018100ca505041e01102240c0c503c8454501400e548506048845030512640c80d50320707402c900c1c3c0000b0400c0c01b43d14001d04805001c0b0307112888059a0390310052103041507a040020550130062068410035150f0349183c0e16180e014078440e000b0a0484d210100d101181030801d00000d015030090042044100440340241c100c2c03140414580e08064072004000c400f104140e20521450000c5031040d80030b102e541c0e0450030492442540e5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 891202050 1250 891200800 891200839
    0xa0206030c0408060c0a0f0c170304150e0d0c02120a080c06010819030c03030504050f030f0c280b15100c03080604020301050109090b03010b0d080307031a010903030509 74
    0x11105101401c4010404011070b072410412603030402543d0000900703107480094004d241000001d42181040700d81d040320b82c2440305090280700d8410060b02c0c80c2e50f40340703454240862005280086420341b107150895400c142803010072142c081cad20069881c1d1000c412182c00700b00b00d0090f0b0240e80c24203030040000c40b200040904004003c00341d000703005480e01d5890300c56202e00388070340c07181c4003061306505107004070005e80d02846464600394103040c006001c1e111418118540001c0d41d400c5200341c40000b501403096003802d405030145510000880c1c14a80254014824003000c02c0c051091000c0905c01c040001610708040300e034008117418400700960000750001d0711218041a40381c01042004c1c290509055001e003206602030741c207640a525651604000800f07079000e0388110a44542c0e44c0c00e540a0982d400c1d0840e180c00b03030000703000c0840719256050071061588266484e20101b450800f44065000700c4a031410304084050b102c1c00b0b131079851920103941d2a440200903a40c0100f400c41584000c008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 891203300 1250 891202050 891202057
    0x111070e091c0c11030a03050a0c0f0611130b1905070602090411071401050c04051002120d050f0702061501030b03010b0d08040602070f180213030c15030f140a0b030a0206 75
    0xa070ba01c86400c040907080c1081340c20480040c05010f6000f411000c0086500541100e1144400f45010140d04100d0b042034980f8603180c0304020107031400c0154000c100314082000d00342d081c100440410321555203d0100c111881840c125100114140c10108040b42c05400a00032150041d20054035001517200080c040391551a055404800e002c074045c0203000100010a084d0040c8100811460504c1100c000c003e00032071144521805c05007000c0d542c0c40e8824000310503030071010440151921102204000030b0306040380c00042c0c40c0240f0b00002c841c2c52000901d14001c0140c0c0c5c2c4062423003e00700004602403d54484540d805640b1200040010b0711031035100d0304494041d0103210307115420024028102800355001c1034413104030760f40600180e010494020300b400e0fa01c030b5006070740e4509880080b10751109030b48040c00012550800088070b9802d014031104050503940c04001c020070301e0020b1803c40d81284044200a4800d01c009600c05555901c102007050005040f208404400d0f4002100c1e50b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 891204550 1250 891203300 891203353
    0x4022d1b0109030e0f0109080f0a1110050301030308040f080706140a09080906032215050a1404022218110f010c06020a030204030807110a050111070e09 67
    0x51001420340d815298501121442204050081c0b00390300058030020311030400340603028451a00f034144245280c0c043c5a581006045e00402d035580401d20900c0d040d142e0030701e49400d8500780c0442800f480b492801d0600e0341e0040440e511168216400c40d1400c071500200100104c0e480c4804036440b101040699000c0c117070300c512071000424100c0002c00c9021441d00d010f407190b038096060204e00c10024844409544401e1015203519850341d0340c4070b54050110020305954511901da600c840700c20310001c003c1c085520704007644140120b44a401e40501201d01c10030501078024500c6003c1001440c0c4807180450340c04070b070302030b680d07824481c52044401c81b03808910304404092012106400c01880c80407007038030320304201c482e4010800340b8400030b000100d000b01e000b881c141e800076100c0f003c107019034141c40c00b458100100341d40b13031402490a85a52144013661501c2602c626070001884c2d03106402104800c10079001818125161070701010f8a03042c054103c06207070050050203d46c0b2500c0040604010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 891205800 1250 891204550 891204637
    0x1903050c0a0902030624040f06230301050a05040903090803030c0d14311b03050c0405011512110c06040b0903030405030306100c140105010602010e0102090d020402 72
    0x550550421001d1901c541c400e0495500620411640e640ea0300c10080d0450218030341c00400306130b0b40480b03617414030690b0032420b4002015003000c0341c40c5030700c20121000780c1c03684065024a10f00c001d0130312a10740000d03c1034a6214002c0c0200780007605194000003803c0d8070900300000c1440d00c8110a90564108a49086512102143d0302c2c070000c506028650600ea200f80c502d14031410b102d4421070b482c44919100c42e00840d043c07070300714004845804030660508e0300010180040b402c0204c41c0701c40c081c914401601c543c17007400420011464a80b080a0403030b0b800e40640700c04034184a4069585c4034030210084030340b0395141c94a240130840007008200420002026100720300c3e040ca402c0c803502c000500342c19603981c424070401c0000341c00001100d4116508840c0300d0b20900d00d40380100e9044115a900034400003440591b04003c3c10150821410b8803001c0d00203100e2907421071440350807400b54424081c1e1081c0c241c8030800250501c5d42c018083d09004003103a910001980800701d030341380d4a901608440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 891207050 1250 891205800 891205813
    0x1b060105033f0a1710060c050f060f0a2a0f0302120901140c03070804170c0114070e06070b0f0c0c1c021209031e1e070e07110d030506190305 62
    0x50315400448410b0100d9200d400540030705005110225040360717801290144805002c218090008c00c0040a07200812507003150070364504051442c0c99035000759025080039043c17442d02c1640e0750502c041c81304c00d00810a90132079028282142104d50004030b021100a041e4200f0103807002810000025120798022800451075540c10603003603441a00003403584034061424000c0c0100c01e940304e0305484d0410340040d0303105600e074070180341d4000341d10402d400120503620b422604804c11880551051140101340c6803c141c0400361410b120080c800d402c0b00602104203603000820300d0b4852101540c003d24240185814101d8140100b032421415151103401c85200d8241030083d10341c10040f4042044003501042c2c24500d040300802c0d0356070740c180e100c1142c1030520003c0040c40340703003000085000d01f0b564868030070205000d4103036a1550040d00070048803420a00000d100c40707000d1640c0340755500e820401094490003000e0700714010100640280d51101c030f0b42c180d0f22898814802a280558040c1014141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 891208300 1250 891207050 891207067
    0x151909152001050714090310140603160b0901030f06030b0106021605030705011e0210021303110907090302090c070506040b01090f0902030616030609050c1b060105033f 74
    0x190280400c86000341a03042400300050a94010500001c5d1405049440e80390340b0f0032000642014a01d04500c140c1c54501101d82c01300015110915016820130b44c103460185086980c84030184401d4010561692401c01101c03d695119610001000b0026000000c08a0701e958a56086400030703404280141d20021285070703405400c0106500802044000f0a1410702c0c04001a2030700648911038512084400d000c03d0980c0e000380203056030204422011995007800087d203494019140c0029200c0710100d080500d001d080c007a0006014202907214083d0a030f10395801c100c0782d030100805644aa1034140310050005500700280c5001354400c086030030896041c0b00c021021a407000031807030721003814030301050013684001c07959940202d0529038890b2500100300303003600a40515402014414640820080302e402008081d01c100301d00506080385c010412000c0c20ba58500a0040d02c2e495009031410042e003440000005102815940541003041c8000400410a01030003070418102040050000c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 891209550 1250 891208300 891208337
    0x1929040602030a11010510090504140a061d0a0209011a0706020a030b0424090b040e070b040e01051207060c02010e040207030c0203100903090b07261815190915 70
    0x103104c8240b05008011500e00042c0a9070740009134407400f5072099450001c075040c00104250003648808000480d901000d442ca82040140b0614851004041d4800300c600790221011850708003507a00145070662503420a04041c28401600c40e00c2c0203940c404005610015000d400581f501a08a440019003102958144010b03600004000308108071002101c4d440882c80c0b540f984162071412500091110044012030010610f240025240388581500044ea9240c40c3e0020010750f42c149103403001c070366170717481c188001c080708010480c1c501d401005090001500c00d21722034040ca801490700c0b885c010306c0c10010501704c0c2c0c401e40d0103500003010064690154181004100c400c515040c20421210b05aa103004015030038a000d10b030400c9400060100505c01c0d845190105a2021412043d8041c0d00c070340e080c01d0030f80c0158018020082d824040403460b141c04090760f0461241626030514200c0c2d4007840711030082c0c0c1800f5502c2845580903000c5620355030340a4103016283c064036085505c450005818 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 891210800 1250 891209550 891209567
    0xe0a0b04020f0a1d06011b0b04150c091502010f0603050f0f060c0702090408070605101e060806060a0903140a052803140f0a1d1929040602030a 63
    0x26030180751614030410511424916146880740503110f9000603480d41c00048440320801500c1c547c0c01d854420041c4240000107806a004034814444640d050f40c2c44240c4c2415a040421080c000c40d0b20070302c0030411083d24924207880114184000540c3c4803008046204403135aa0b0001d581a030b01200031420508801c01800c00c903400304038003c00c03240c42e02800d50842481411002402202c909000c5400c100d84401030303401d4185c1c81001444035182980600395030340030a226502d144e002141226000b089581d0950066401c1552400506e0780d030242404210b13400364480c00300b0400c1d0800001301045000100c40c4045402a014048001d8a0302789070346061036003000c400c0c41159040d40c50003c1d10801c469000607507458100340c0c4243c9142130440b8403900804240303004c03420000580240d2543c1c00071041c2015a41d2143c00c400c0d01049400780603110b8884094160280721250040c03204c89040b914a03035200e840f150240f01e400380200c5a0305150340090b440078003da4004110404040c0c0c002c05c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 891212050 1250 891210800 891210829
    0x7020f100b03060912180a0504320705120c1303050105060f04020405061b03071209030309240e030102040506040806010e16051801030204030b0f01450e0a0b0402 71
    0x414221101c1d10209080d803041e10785c80d0800c40041e8081b403800f5102d07066034900610006108014420002c20034001c0301107100803d80c0b2502c440080705001c1603180c0d908500610300c07541d40d1070500400040b10a00f694010f00b580f0481c40b418014800c81203d0641c203900914450000822603040541c1442003c40da0900075900c00c900501040c021a2644402d48080c2d04030300511055038448540700c0350840c0f0039410082c100c19158592050469001646e24007100d20951395a000d10f6a0b40446010503c490241416060046061a06198401e010781c0400050080006160566410015070554001e03407048001c0c1c2c00c000d004101d0700800441140c0c0c400f42102900f100e081110400401c2da100c0c0c0c2c0600d050410740c0c0b00b4010f446c0c0c0d11a5050360040e581c000c401050506044242d609030010902c03d5040d401c0042d4644100200501906220910304040c00030b2094030040310a4240c000d050102210380e60f68880c2100501d00812480320ba0900982401c1440d0400c0d0042c031100e070881001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 891213300 1250 891212050 891212053
    0xa0f02060c0715110412060b090a0212042d03020f01060b0705030a050711040218031e0a020904170f07030f02210306031e0309190e01050907020f100b030609 69
    0x1a20224220741c5191168607084a80003400c44101303021444503001d10781000c900148081000020000703941e02100c890801100d00c1c0d00c1990700c0c202850300341c7c030855046005654100000c58005214107220131000200421100c22105808505d4801518600e10a0b401648185e0108064113070a00c210f01c0030f030210151f10b80c500034150f210107070b0340d215528402041150000c0e2a5044c04002007031606403980007001950b4405549940d0320b01803c0705c503102846405190b107195405000c03c1500c1d0705012061000c3e00e000445074082282540000303000f600c64200b52001e03201d03020828001401c4822917090354544030401414010800801d811883c015540b002064203849110300c1400704189080f000380695903542e260200742402c180303075186004005d404224107817903000030001d42141e2405031051a1003039965504580b84030040d101e030801b40ba080c03100611680c10094581540a81c190044540b44c00110a0740744c900404400400101651103040d454149010301049800c13039080070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 891214550 1250 891213300 891213307
    0x15050415060206180a020d060903020d11060c0a030209060a030507020d0f0e100c1709130b0d03030e03040e09060105011101141501020a30050c0627030a0f02060c 71
    0x260043d40d0341c0d0000d01812102480c21078003480200040018030502a4043c010307a8480106291000c094504007000f28094001c844458031481d104c0c0d11f2090900c0c205c0790081c10180c90328000c81c03c6a0b0f02c11851b4004061b001c0104032200c2d11801c3c014406546145d4000034a4541a100282001c0381718640c60300304480141001080741d84041c030320150030000ca61000b020f0402100035514028040c1008101c90070007401c0c09240c08000380078200d43c038401d641d40103507000c1c420000000c41d010440c1895104481c03c200d03c01003031007540003c9081c1d0344003044178546912420294401c040855507040707075500100043c81656480700d0031100b0040700d0002070080329425901e420900800403c40c0c4004240f80c0a503401e182e108010303650b002ca4102400038040555004803084124901d0712090805e101c2d8100040d41d0b40c400c4d000c0700c0341580e5420290020341c9038500c1d044440c142c5144592009980001c0f0069500c038140028141e4114580760102a0035100304040e0914500034a103e840b007a050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 891215800 1250 891214550 891214559
    0x2701150f08012009041d01090b070906020a050303010b160506010b03010317040503190512040b03241809030415051305120307030c14010905100b0402091806030a020415050415 77
    0x740075030b84d1404c0111030101e960711401c181c1d403841c0c202e00c020400c0e0a40c01c0074503c005104490481500900b039654070302c2160707621040d042c0e0395a8070110009042d64410001084181201009401c0850680c580801d400600b0f80b280c61408100ba08800b021003030010041080041200075490030011006001c0c0c00c0601d0b0000003030f02c4074114005141102424941d1104000047c0f00a5020000b03200b0115102c0344c94185031401c94004545501c01c2402c3c044403110321000025840c075413044e00500d150120b0f642c080726003460001c00303030145407248070500c0b01144050001105c100c103814140d4a9039107405c01034a44101160156000d9805400f13400384840700205c0c00310403900743c2c1d0f4141c11b00e031902c469589401502d0042e03c4007903031069480d20000000304040402c070140010381004041c0404074940c0c040100300c0c031851011592021158000c4a101c008600307109600c48401030590340c8011181c1c000c202965104803000c00109461401803241d868184200482d415600c0009121141807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 891217050 1250 891215800 891215861
    0x80d2d09091404240f020c0c01020f0a0b071d0a09020d050a0618020a110a050606011e0207061409030106090f060603061206090c080a0305030417032701150f0801 71
    0xe1203581c005a8541480c41020b040903900482005c070140f400c11561500000c0c038543d1600b814a074514018040c550014a11440000d0644d42140d004000b020954841d17140c1078580c0c150b1021048181604911588003595404081c500104000e02c005641c86022504000031110f0040007403204034030f0303c0c1003071105d840d5142400760108503070000140d5600300c40c6000e40b503840c444081c0e101c05220710a030300070420102044460192400f0b07242c0f91545019442146410000b210f6000010b0703102083c00c100c503901c1114100500d0100415103031138070f0b145d8000b190a40b0020b0f00000401030300d900803004102c40605c00d10000700028542001424100306001104110f143d401074000380c0c480454805108504114a00801e80b500841c3d14144140c60040c000b40c00480d0150380c480402e158056102901d442264411004103200c08691108920483c40d42c02c0f5080720f2561035965072241109554401e0242400b501511182940300b42c0303051080fa09441c21803501101c1e24204082070f103c12040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 891218300 1250 891217050 891217073
    0x60203044502090307090b01023003061206070806011b0b010b1b0a050f070603060308090d140d020309040606090e0c0c010908070b060a0b0301080d2d09091404 70
    0x524140700440c04124509100a4000e5020f2154036026005001540400c07503400251415400e13007e54480e440040341c9501e041066040d00e01d030694201c040c110640c4c1c420303401154000c3c00146480400f0182030070443c501071040b03400001040580c01845460b6030400d20004281101c0045100100c1e12541d03004401441841007190305840403030114458001003a1404000c4034820440d82c2000380d904049960b41812558028140070740b0300003040661080c010b106c1680c1e0890030080c80e02009401f40010009003071402e03103d400c840800015900c00500c0b40103510707005503005507110980c4030304100c219a002d07400801806001c100030409142400640d40e409066202e5440c0c4440c14190441c1c0585440c142c028a20040082c000040000580703105014480580303024000c66181c0c522814139100a0103000a42c0d80460045030825114442c40e641d48042c0c24142000112070a103050866014190b4031360204031504818400c0084a1299241c00b403500f40c1810858209a02c503000d0311071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 891219550 1250 891218300 891218399
    0x90615090406020c0d020604110405040c061809180312140403050c1f092108180a0206070807050f070b0a0503130b01081c0c020609040c14030106020304 67
    0x18040c001000c0c06a5903040d1440c0c442d99070250789a00e0b140c800c0080d104d0104071022520341d40f4280c8458810f08051041e036124036880322034100c40794103080003500d0740c0b071041c280b02c80c803280c0407903010038002c0f9540a05178201c1c406400c0201c0c111100d2130090541c2041e102180c80252614010018480b02c01600c2034009415007085a550706059110364205428110084030024405a035030380880782e141c0c442481e20303005e05004040303280b40d07030b150411812190065100054042e00410151a8a0041005040e1404040720b90240c1e9660204820390000107003501c1c000000304001d8103020003400000e2162641d60f0280629900b8114803005074060807042208000300031001404e0018901c0081c04680d4002d90410203039070790764809517070b68544158000d01981802e40d03e000c48500500b80825890b50013050f281c01d21002c3c0081c000180300e20703400c1904000b1100049000c3d5004440118041e00041e800303559914100b078000341d114104010721107100c010300c0b840c1c01d0545030404007210001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 891220800 1250 891219550 891219559
    0xf02010507020a0b03070f090b0a08011e0e04060510050d08190e0409241103220b0406050f180607031a061b15130f020102100513020108090615 63
    0x8030781c1800402d908042c04c0d040362401d40000000c1c01100364000044104000850340c510107140d441c0c00030b502c20f03801203d41c0c19000c00c4060006110720f078481c0204080030704070200068041a0b4079815009401c1c811717201540c030303241c0d07480030f1069540441800001411042e201741f600c48003240d0303c02c0311f980704641c01081c0d1000440800030040d44030b8118145118001130041c0040303009401c228800e1650130003002110341050201c01914031881c018560560034221a45096a039494018203068480402d09a4401c905038a040000351821032200d001e21f004100024032450300a400703e00895000d03000300080780580504c1c0c00319400c000b40301a4064010714000c00c001c8810381541000ca0009080f4541c080c40104401d50303600c103401c4c100210242d420b01203814076851031a503076207040800d44091080d0307070001d088440881e140100d0000402d2041c0304981c0f0004141c8030000842c2c4069510740303100d02c0c583c2c1c0c0c4042590303841014160000c1c40107002e400141002500340800742060300d50035015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 891222050 1250 891220800 891220807
    0x60c0901090e070e100e10030b1306060503090601060c200f060c0d080c0a09030b040f0b10060314160c0c090c020f071203050702010302220b0a110105040f020105 71
    0x96034480c807410801810140700300920303818051405043c601c0740244150141001c0c203030f010201d911408150f4545200a0058491143c1c1020110084c021401c540e0780c020b02c9504c2001c0b2128030303922401d0010811581e880b500d80c06c0202c91b1a044c0041a0b11030800c0201c101010400724003000e460007450801d42c4c0c0300c03a90320300510001c280152103003009294000400314000ca4413040105200311741c41c80ca0b60700e1190701c1e916000f005996000c1d000d102000140801c805000103040f042c00d40d80c0141c0030341840d0300f841c083ca41d00c004101200311444030400b00c40c400108004c03501401a48409002141005100c1c80c00703541c0d0318820b2469844a10030010340351029003c0c0510840d0b803070301404000038184810022400c01070f6803204800d5800040748210100090000a0742504500c195415a55a868501240c0044007c0e4104000312400b129604080501c3c1e40203c0d0b10041c020b214030b0a480b078969a903a10b01802601c00c1000e80341c03181e41481c080200107400403206240d00c1d030342420101e45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 891223300 1250 891222050 891222067
    0x10080717030f0c24060f01020a050a02101b0f0b09010504030e1516080c0c1f05090f19080c01030902030705090417041d0601050c03120c13090203100806060102060c 72
    0x340c50441c2c0c503004c0015850400b240310000840701424031414065070080750281c6500012652209c12040150090700900b40080061809808464801080c2e150024100340700d40400b01c445034200d4003c481101d140c015200c20011a100b0090b844104200200100d140545002d003607a0100d074a448e20804454414442500d2403009a03111280c031180b801c800f040c405e1070b00600c258001e8410804074404e500142289142204243c0c0303403000c81003400400001c0d00c03101550b446d0000c40c442c40c0d02400450201c0141e8850034100001030b8041070214002d44e24041e007407420100d2034141203041500f0103403c80f000da1000501c0c0d400700c03503007503034602d000fa5030f6030400b15040d801d0f02e48107070841e94000400140002c044080d41e4010b080062811040d500c80d10b00640e480d1140c9030b1812100e4000340003100000208805056218042c1c1c0500e40c5450100c04220a00b01240d07008902500c0c0d0110520460b00813000200f006000754400400c400c2c101600082c0d40c50720010030a14241c000014000c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 891224550 1250 891223300 891223303
    0xb0901030b03250f0807030302102307050307090807051c08040924050f0a03030e0a0f08100f02390313140d0b010b0a090e10080717030f0c 61
    0x450004030500c8480c1d012070046900503243da42e10a2800c4050740400100b044500803420030222a4550010507090807542c0715200a054950f0301c00240744074201e001380003920302c2c00c840d6108001658800e9540d142ca840c0c0a46a407089400139040c1e40d02500c0103105a40b25900d10300b003140080c00f60440307042683d00e030500040c4941d4001c0030103603007480c00e020202c00f104542801007104843e5019000c98890041c440003280e040c1041d03078000f90813582080800e00800200001c210042c0c51564041d48500e407041c0e42a520f980002c5042e0b02c00c1e283c1071503c038002c0c80352482c0001c142c0f0041d0b10700250424541d00c41642000d881d1042e9200c1d407280c0140ba000c0a103110310003400c200c241c03a1201400c01070100061510300c200f000560080800d03070a00c0c50107507071860020760b10100c89d10b0aa4242494141c45400818800c81804101d0b01c021448810342640b442c403800380321112800d0703c1d003084051402d002a640c84820f40c6040c11009559800307003c0140d0700d07586840c04025844107611003049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 891225800 1250 891224550 891224563
    0x70f03200c011d0d080f0c0304080336070e04021e0102030705070b0406080708060a06050a02100e01051503060907050d080922180c0e04030903050d0c1a010b0901030b03 74
    0x507240c1000962610102000c04a1100d201400035125080c80c6d645d04400c06008103801c0300c3c5201042d40400c0010000781220010399001180c0d4042d40c04049030781d03040b5424480860001d00005007940014816920307013003021401070039072544c0540d014242540410481030703030030201e0011940d0b040180303100c42e442041500c1100b5088003c07119215501e000001d2140e0090045030005001c0400003114140121803090061001034004d940307485c81c12108540036049108600110301030b142107202002c880d0300800c0e400040c0a00001a503080c0409034462034461040d40c5806904180c0800207000000309a500c1155000d60740d0010041080c070313052410784101c8800b55800a80800301041c050110100302c0b040050041c01000301400b5424040b01480c2050b000804849400e0309c28040b136000e042034603070442d1090a0410203103459548240c10107032001070500005803403170010014496044441c8e00060010016851594108030401c441442490400f505058456410346540d84041115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 891227050 1250 891225800 891225821
    0xf01051606150611061003120c0201030b0d050f0601050108091b0f10170c090f01210e03030f0705070f0219180b0f03030f071401090b04030305070f03200c01 69
    0x541c00c0d803603182d0f00064504030a4800141041c400c0f1400103900c441100150000d598008141e00c47c2c251a0f224112031074005948101e04250f103441c800c05d40da07150b92010200ac1031050006c3e05209141142c40c0d842c005050380154100100c4901340000030360049210400c0c410b40165800a0041810109040c450402d40b00f58202e55075100858034a5070021508a9030340458001e1502a15010700541340c40c09800066940406405c1c0240b100d58041e0030303409110865042e0307080c1c0d03842401140200300d444c45a98909036400000c1000a0312030014041039000ca03042c00c00e5410312150f921014a00702101e10002e002d01005001c4155084085d40c0d802c00410705c0b0034405180c4440d000f200d102826407070701550f006d200081c41c981d40d82e19020080c0c035200d01d2510740312428913030305894241914240603c3d03038101e5581c5022840105910000252089009803000320f40c3d8241003100404c40750444c00504101442e219200e000350141d10b403e05000031814089079180d558107082c450052001940 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 891228300 1250 891227050 891227081
    0x803010b160b040b0a0c09051003020a02010b0a08010605011403090703150b131a150d0b0d0b1e060301090f0209270c10110607030911060a1d0f01051606 67
    0x800042041c2c00d1310312031164080090621104040305004d42e0505482e000306a07010030b48892941c1d00610a0b80603001420036803001041202c08180802e142c1d00842e0000306169448410910186d60030030703560040040701442d542c0c55407411400042c0c846000d07004c0200400350481d200102c0e149207400042d0050f8005103015411300c4120390001c010706e194460007844040c0d444541c8243e00e0202d11030300c0e00c04400c41d40ac5290505201d0f042d0002c10b0301c1804a61b1000da2596050082107a117007031248a00301c038a8503007911401c1d001840000c44001498203100741c0c1040c00101c0064651045a428584d05603910380b81900d40645503508a817901c6e41c488418050340c5001d2110074000101c095010703c00b541c0c030550b0109104000c444071030401e1f81c1c0e0b800342e60021010440700381c807a40c016809a4044c1c2c12031300701c0651010001c2e255038410101d50700007a031070044500e42c1c5405840141c4010404a40400901c4c828030006040e5015940c590041c54447d803001070b041c440c007034100348640140b841c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 891229550 1250 891228300 891228323
    0x4090504061e0b100512040b0c2a210a0c14030d0f110c072904060f020d18030f1b03210e060304080a09051306080f03070803010b16 58
    0x20544001804058403e51003134400b1600540390354051401c481380030742e14054180d065540ca455144901a000d000c801c00d0a1003000740b1980c0c41d82d501941219800360404915182c150248103074900f24040341d900c1d6a030700c6a00310b912100b074401001c485c0700c0e0a0714208030500b80d01504054002814440c1c460110703010006800a136080750340c0c80008202c1c1100c00400c03070680300d444860414090780c0c1c143d580036807021000b4071600280754101c801c030742d100c000703010880c0d007010240041d160800c3e800040440c5000c1090000c00360140248a512100c0d0301d070aa04510b080c0d0104644011548005003002420030049401d000140318032189100c02c0380c0d00d50005540d64642201d05500c4c004400035000408050301c00b030940b04910203100050300408088c00c5807510341300c145282c0e014403c03000c140a00d11100251548035103510b0754449108040014070141342c5405035007020850602120340d504100b02c03000002e0000415a03043d600308014540d00c0324a4008194542c1180c1600648401d0418 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 891230800 1250 891229550 891229601
    0x30f020106080322090504020d150905031305090a0e0c10050405090106181403210d0e0c0414011815120602030109060b1e0a021e1c050c030409050406 66
    0x3c181c0070410000905500d40d40e41d1840d20200700c550564000790301000d40b1010030080303071242b02210510080390f030b00011019400e55031a0318640c4503840d0617402d0702c041641001645880450725500c01c03107019040c070005540409150311562110802403040e01d13420450710038184603406548c00303804082e0421807196101d48014050103580d0b07000303101461030441c02040704551120345c40f00c1103a01070001d03da401c07081d00107001d00c28500c0f40e41c2c41c00202c003848a00c602c450140038603c071501c0914080c1c903502c5c00407010700050350560802c03075441000e080f0040004034514584074007003108001000420508003810f81600c0c240c15807110f4440d0320101d4008080c17111a0f8000c504840090008216035039581070405030724004e00c0c261041c9580070000e02142280d054008002419082c41959950140c60502c1800d50300703181e80b540c48552102c005840c3c4800000302c0207126200d0ba08104d41415800461070307690b4425800b4041d02a501d0341d0103c7c0420010b0f4010080901d0700888004140c040c2c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 891232050 1250 891230800 891230827
    0x40203090f0706180b03130f0f0302010e03070506150102031201090f0606030902010e010c06020417060a150b0406120605130212150f0d05190507171504030f0201060803 74
    0x240c101c03507041409210710001c1c50354003981011441695030140c0400c440c0c980f014140f40c03a00010644400e000c403040c0460001f580c44074004060b5842241d074011021403504009084400c07080030a01d5030341c800c10400002c82c8000401640c04035482c0341000310b181e54800101c5c210300a08616150480d0110000f0a410300036070480003402d0003440d0700b04072041c0c0c0c84008030140c444544029020820402c1062115482280d54041140c010003025103440e0b6201444100058100c94903000c0d600410705104100c0010300445940d40204840a07a05500b854004072551140d4480c1c0740510000320b054501d00c901d19007049008102c000c000c0c00c5d05c0486482d06a029522804a070705880c6680b6000451035000c441098104d160702400740004c4841440c03d11000c41c80c03003c02074802d48211100840d59903803a160121644e84a800901072107072a127031000c283c3c140f960180e582c040c0c2041080040d0303200da00400b1a8800c1e014546048020703011002a03005103469007023142039000000706801071030030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 891233300 1250 891232050 891232063
    0xf0f0b032d01150c0305030c160b150901080304030201211b05071a190902060904050c040e10320909011b030603050c0f1305011d1303120510030204020309 68
    0x44064404000c0702c8080f0119606003903d072004010030024800303d19014004c0019020941c00080c1a20b40150700317448840340701800301d400004503c0881d290200b1801d00c55482d5005184160096040c142981c0c000f07000c4500422481c0d5400391392000703800c4270300c2107500a0125402d09070b00440d48a800072030300030300c141e0101d003096a03807a2504035020352001090107070302c1c03107031a1041103028180046a0b17800050280c02c40280c3c1e00c2007090010f40d0241d0349501c503850103500001d090560f00c80c0340440400d111040101850500814002c0401c0070445000d50748020b0b4881c00c0360303420014010808414010000781c24280c1184420b410040740c0e64055001b15200040f0f44090703491980080380c11026100b9a010041540d0003c1d8030b6181541000c0300c0ca010300d2107000f00320a0030006c0100c040405c8031801d9005100f1400860141c40001c8181411190804411a01c8038103200ca071343c0b03001d0205545000102d483e5591407002417411503200f4001e2020b19070040c410340d43c83c18040341c55030380e13000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 891234550 1250 891233300 891233309
    0x14040f030303050c030709030b06010903080d20120105040203180102070609060f0b0d12021f020405040b010c020d0b06150703050d0614090c0c011d0d020105010f0f0b032d01 76
    0xa2a1402184d0000014030549100c0c81d0203650386aa418110342d1a40c0718810094030007410300620307c0c00170000403d100042c000402d54031000060400d9500c060006000307030b0700c4c0c00754044002041006940c03c250341000b41500c00a480142e6651180111110030550034050040c06501c0859030300c04202c2c054101080240c01403c052003100d04040c0c900303044510043c0c249074032007900d00d05e500000d6220403034901c0c080114019076213103107041080300d4808140150124200b6074005401e2150b45010310880b00c00080a107050b1251660350360202d650564221000f4011200440c00210b4030358805403913080905000203c1078451425280c040c04980109907842103941c10040d0204050f0f0400101c0c030310072500240422a0b0742c44449854015602c05403100841d55207804141c9144c04030340001d0031040001000820074584441c40083c00c69a068101c20503601203200c1c10003d9104007818001600da110550564a860303c40c1c00c00000c1c031848807245c1200c00d11000340803030454500a800d040742d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 891235800 1250 891234550 891234557
    0x2610030b2701271103150a1a010509060d110a0507050f01020304110d17041d090604050c10090914070207090e19020f090f0907081603030e0114040f0303 67
    0x40105004900381e600e0b01078460301c1c40340c03c00301500030490401002c01e811801400e40072024850700002c00c0c184100782000c0d1074000007040c2480305807600c520550401e1001000001c081d490300000091591003140422031041001080b0601280c6a83e030019100320185240195a135014800151058010300e4065130f1b203029034419101051010300803a48195440b01d0b45c072800c00c5410701000801104400c0540b02c1d401e038480f214070084100030003040507061144d002c41000201066030980710b5801440420160855400d0000060002581c00e003140002c880819200300f0500084404910030b03441030592500341600385040300c520b84003150240c50705034282e030851038071854107000b55000b5400e40c007e19805203103089061001c0c444481081480200461028a00c8c400000c04280e0151100003007008080148104045d0802880004010420141c041d00c4d544e0180f041d0040581d10019003800038202151006038403440e90007100440d08800a80c1303e549071000031185c131109000440c080b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 891237050 1250 891235800 891235861
    0x516060306180203090a0611040906090b040c180303230409060306051b09040f061d06091b0d020a05041706100905040b1501051b060609072610030b 65
    0x102d0400d8004c891061210a0050424840568842d40184048844c00c41c0401c02400041214042d9005080041049800204481c1c01c0102000f003150105c44244051200c0304c280d80700082ca038100f101089942505103500008418528035401c807404100c403918000001501040c2402035901100949000b02410170040e6505100041280c4461031205e0ba12001441a0303011850180c1117010710110801001c2011030f5514604107188018200d00d03c1d695041c0001c00440b810011400b0303502003060f807841042620500b00c028040e20824181e2030180c0d40008a407410540681c007101c0080c80c50000c08840c40c0413007218a40c07100001c1c1c65112034070350f08880c00240ca8019005141c081ca0708941e0300c1c500380d111003096001880380d00708801e061003000e0050400d800d40000040007000103000c0640000e140c20800c00c003140703a00420150610400030400102c40e44403442c109020000c95013098145c2d1280b88e04401040c0950f4002028181030710304200703002034a40c019184032111440fa1202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 891238300 1250 891237050 891237089
    0x280905070206090714030a060203010909050d1b0b15030f0d020d03151203030f1104170d090e071e17060d02131e0504061d070e010e040516060306 64
    0x854000c2514111404d0344106024840c80c4150710151000200003000c86a07132900300c0c0d44810583e00241d10039280c8641d101800000d000042c002c0742c84100c010324040488041d09501c4140200d12081d000c1d00c401080d2000840205000f170100052407401000c80c1d040e4001d00031010703a10f18080d2180c0b0014018111000c40d800d00a0041240029000310310044c01401d00480d02a55100110103504141d0ac0790528015444503220b07604020302c40100e0309503500c0c142105030f1003030011080e03541240e500a034104003ea540c000001e0064079900d0045184075292044110b4000c04200710342c01030558011440d106050f0004140c2008010540f01220950f9400042181c00070700c0503400b81d00080e4038552103000311803079031180c0402c0d26203100d002c048813100b8460340c048500445084610a69854050f01d4020701300e003200c91020006001081a14104003d0101031913040c40360508018182012400300141030009480c0712201e941c160355a10382e95a0000c0191a0910400c0d1030062070002120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 891239550 1250 891238300 891238303
    0x4030b1014150c1507020f010b030c060f2a0709142e030c08030c01050f0138030916050303070804150512070c2d112809050702 56
    0x1c401c0030000b4002042003280020007041544082d01459032401281402a80ca62203038132030070700410007a4000c040c0344d880e80740f959084408995400780310b035001c1d002c0b810041c2d55042c1241d5041800d00742081e1100c1b040e980490002250203039000200340582072542c0118000902c1c10304894180c0000d00c0180c18410441810040c00d540c440001e4040d4908820940b900d841801e401c602152840907501c3d9881d168076000c0c11158008282e590800100544501424040c440d040400b00220003a03551420040080c40b1495034400103001d804c0680891a454100960240d820079100312560b6030314080058544503800c410a650380c10345403400110b070300d05002085e82e020584c8030b40054546420010310641c068440441102001001c1002511765082240070901030300245e29410a101404d00c0d100d6990940c1c2c00d00c00d9011403c0440d0508105031020381c52240a40044003400d412050343c000c80c8020000000c0450301542a11000c81d450340003418840440d4490182000b59864440d0200d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 891240800 1250 891239550 891239579
    0x9010605090717070e0a1206060806071205060303120f0403030f020c0d0c050a020d03080702010c02010b0d060b01030f0e0a02030f0c01020601172a1903020604230604030b10 76
    0x700001c3c4903115101c412a00058034203400c5185030078403c400406410025911220540000c07485400620840041080c18052600905805000307401c042c07400100c01080220104a6103420588807004507206407800d00448451600001d0607030014508115001102042030700d048000919000044280c03c40d64401d503082140740c5070141c03080195100c1d0854110b103803020309454501410406000580e0703020041e0147c10f1007511713007800038984a10040e084888102d885410b690606040d41800d50b41c0d007412050981c1d200e0000511140d04800484c0103007000d4412904491421503003c400c2700000541d0000345108904554840070707404011600c030840d10070b140d80542e00044c014011514400e803400c42c0ba4070008201c41d0f03a8240c1d40605003900d80c00d40d821040c800107000218041707041883c520f80b00ca000d9000c5201806203182d0101700c8920503440343c2403401c20300c0e078001941c8424810400b125074030010401c98a41d6181c0c2480950200c1c184d541d050240d4000c4000103400a044051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 891242050 1250 891240800 891240811
    0x90b032701050c0d09060e030705060714090303070602160501410f2e0f0b1305040c03020706060b0909060a12031404081e16080a061d03070303050901060509 69
    0x50904154540c60104003405d034018003150203a0b141c130301c02400000100701a140345801000105201c1c100004081c04031007104015031900e040802c00341113541c170700208484995500860060f907550124140d01d0840f090524001c0c165402c2c00d400c44140e50343c20030660180d01800f580f9040885102c151400900509500480755034811400110100d412040d266402001018003402032041c5032548443e01c0102c0701d00140c51000e40505000100020014002815445240618080911408a408003428070486200d242c440e290107030010310a0b015624110750040043c041c50b80c44440c51003203a0030901600e070040700c4900004040d850029607400032520358042c500c0101a250f242120603040e1540e180308000f004010004a911080000382c40c0e000c8203030818010b5400c2c05600900304014041d0403001100d060009219009000c20b0669501364010400034031022064100c01c80090103900c0f8442038000401c4407014540c05800c0a072082041000030014261185e04100b091b1a06a40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 891243300 1250 891242050 891242071
    0xb04030c0b030901060302120609060a0e0312070207090f02180604120803130f3e01080a090c151101020a0e0103020d0b0a0810050603070b0712090b03270105 69
    0x70000811040c0007540c00609220011030010b13245c1d00820340c44180125680d200350301c110104440044d0034410b0b660460090003050048894800417140e41e400b55268681b441100000491801c0d8020480752000b405603000030701070f182000380c0e80c0c0000c3d00101c2651030b14104145041109150034800c42c9c09071002c104514244120580f50400070307420050560b800c0c40c0d0785180f48804502c180b8103940c0c400348a907040000d080c802004030700034604d07440c1d404250413510f010348904040002c00d0400b0441000e1814202076601c2500c004042c10300c0400140c40e90480c48404100c6140014042d1100f8038a5140d104491a01c0d0007428206d100701c024020014015044c801480d40c4a60024000c41c40b080302d01081d025140c07030001c1e10241440d8440d90541e8049800d0410380c210f41d0046903032016040307014107581d174a42802e0120f50301c62070000800c0200346a0303141c18280d0140c100c180c080c111441140c0d4880c6480c60a408840503010942b840c285540c181c45074025005004151082c030301000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 891244550 1250 891243300 891243323
    0x709090e070503060714090d1202010b0a0f15021e010b180717090a020310020318031204170409060305030403020a090c0c060e0f16030b010f0803030415060e090f01060b0403 76
    0x103c81030000018100e1b00001c08205185055544d0500d80007024040c2c04040e00890707100318044d00315248080b80900802034642d0070018460450110011122000c0c114050012868000c904196100c0c52100741480c940380c440c50071900550101810010607a02e8026030049050000680381007203c8200008521885044244090300b00142d007101aa8084850f610015030000782020034058445108035404010010544034419024a2664081d80610f140101c014256a22007100a1029011144601d030161402d4680c41c00c5400400d551041001400d4691501903140d901500c03040c2c1c417800300702d203001c0354140b550700c600c854900c400e45036002222000d581e29405070207850501c80590194a0a14400044c180b12040001031001d116244003400c51400c000020010303003009544140310201070103031140000449400a030000b1f140c20b082d4484074121000b50126400004000b100c1c1010300c51a004c2c00a10100d40c024111300034042c00d5155108a00d05000f1440007030421039004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 891245800 1250 891244550 891244561
    0x3210e031b0a0314070614034b070801090213050f2101020408010506010e0f0d02060f040b0706110a020d0c0c12050a0506060f010509010c0503090402030705040311010302030417090103140709090e07050306 90
    0x8d4403020000ca240c9829107180e130140c8000da100b90604008450349d0111050200045143d00c20501d6001d001b0072030045041807070070314112846103a103019141c0104004810000f19a5480c42c0359a150140102c3d40e01400c100144494040d4100c0c0c0302d1484076601340008100c5540c024031812032000b40c040e0100c0c2d4420406000c01c10455180b080070f90300044200007502c3c10381702c044000e0014150250405950f8601440c140046815000c14204418010b01c26100a0b50b0702140c454922070440c80d004031503c880f400c00844220271680402c501d0840d901d480310401201240700982c090043d82a610755684074001e0000d16402d48002d41d00140c000c002c04041c030341c000c094210a15008038210307420a51420041822684160388250100340081010001c2024500d1101c2201800380781c03d50a5003003903501c01c05113060010440315440800708028540342d20079131021040f9904240b102d585e80c1068840500700d40082d01521400b2414066441c82c0d90f02c002031a00c2c00c850b8003034000c000c0c5a440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 891247050 1250 891245800 891245851
    0x1050304060f0509240f061203040503150105090f07050405131b083102102f0d0203070515100f03210e031b0a031407061403 55
    0x3001101d4141e030300c2400e01084445032041c0c6110700c0500c001000f407400103070300541d4101c44c22084046038918003800c001c119291034001c103420000a0303c4880408040c03220403421401b0fa6003000d41c0510901e1701880c4d000944040c254101c56056071081d040742c444184050381d0b0881110200c0201e00b082004100c0f604141c804010346903189440090b142151741c030001c009001c10030740200050f410707109110341078044811100c2192104840a8081c00c88030005040100708050042e00c14480711000481c5e8a014803040c07184602030740c0300c04a06900c03c0f41c003041d805070621449100741c4038042204442030700020484503600e80100c0140f4100c5070001c002210f82000500f0010440300e00c07a0b00003002c110020b800d202462084102c100c40e100d01201e8150704a02c41511f003420000134000914542c0c5020403038900d54040e00742c0c10303081c0b48441e41c0440c08046075940001d1881c5c1e16076810003d400d40c0840d03510295105075071842c841280d012240151400180c0700013001e5014600c0040700c1004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 891248300 1250 891247050 891247057
    0x30702100e1801090b010206090d0f0c0201122c12031b040314010b010f092105031905041409010e0a02180d060e122106060f0c031201230105 62
    0x30002e00484042e00400308022500000383c3c0700c0343c4030b643c1721010240f0782c5d0b03010311407a680f24407584024042c04800982c0201211181c0c60800c003130190300d1a0301019a4070030300f00311040c0d00c4d41540500c5417407400c9c1c1c29200d0071400ba0006402414414030003884079400858100760080e100010541103417901f03004660020000d440508001d0010000000025101030a2002320b200380c0c0c000058114443c8000740107501d09414110400400c080c0074080c800c040605000f03012411480350310504071903c1d05602c2d51050740200940c40c11400e901c801c040f684100104203680400c10780030300c0842a802400f03d207000c00c0c0031b13402e00e0701c90000004a207006e641e0701400800902090191188051001007a00d94060180580d1485d88406108140c0741041146d1526244960b0120349004004041042151060866030b0030035400840441c1c110b03669141520f0b18404840e081c02e50700d20381012116a00d038480c600b0480e101507800c000103100c8400c99080c0d4120104604080445c00071200112007590 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 891249550 1250 891248300 891248327
    0x705030108121312081e1318150b0d060b03070504120309150306030b280c020f060108010e060109110732100f0b10030506060d0207080d0e03070210 65
    0x42110300024036116001c500c0050702c1c050a0300b02d40c5ca505e41300740a25514240d003d0116002c408100300c4041030200d0901108231114680b40a10420000c2d0f41c1c035000d46842d440150980056080100d60400b44400800c460349007040200a49581c50b10503d100d40411501e000c0481d50a201c1009014280c0d014114103030f2003803800304201c0e6290949803072200c0f4007001070703800a982c3d070307400b48104685820f406401c072803401d14003200c10f10300540d400c0722084644407a0b090f46482c3c01024141d68020402500b42100c0e41e400d43d01c4542e11042400d008040c040b001d000302d4402e00d000059680760b10b01c664150840500c060701c1c9000307401d071103040e0070307400704045810342c00b94001c4042801e40465101380751114206020307008588000d08020203071568030203551404c40c500003031b0310001c0d51100c15220407911141004100c40d0b030b0b10b000185840c010307240401d80c920b00006109080010010080c00f4034514810100a9090142038003540c81c0617145000750000c410840d80c90b5101e014120022605 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 891250800 1250 891249550 891249577
    0x140411030a0c0b0301030213051302040209120106031401180b1b09031c0f0203090f0f040e0a05160b2106131802030d03020c15090102070c060c0b070503010812 70
    0xd1619540d000d5000140c3c1c0c003040c0f030700002000601c01c501e8884907107026680c05030018041e6040030350103c02440543e40c0000d04c034643c00145803005460310f04100b4203a5503400c0003080019078034103140c440940e9030203040019520300801c10070301841c01c200c4020040c0c0c0006020000c2d948410505d020394148421058445406002c0540566010131107186e126002072110403811400800240c10485044002c0007550014030440485888800804481400c01c403509440c2030318050102d4000d0400500c0c0d0b9410780100c0c1e0140d0140b00002440c140400da0082ca0140b1071a40d0301190881c502400e2034005655981024114280040d0b02d0b1403508004c00400c002034400c2e55002e03082c200d07540e0301000054074910314151015440c00340b1280400040720f0809610746440501035a44521406403072120090141d808600450303001d5043ea100107a10901c5140c8075510390700b010b802d2880c075a20440380c0000f0303a0002100a8420420f480c100c8810074024000c2009112000c0110f80010b42d104005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 891252050 1250 891250800 891250813
    0xa080a15141807051f080703050903070f140a08041706010303080a0e0c030601091e090c0302060a03021c0b12011401051c0b010b0301051e060708090d020d050d0e0414041103 76
    0x10b076540d0442d0305c150403220034000c070700900d10090140a01c4001003546052503c0d010802c00780403008412a2070072540300304400f44101040ca0141c44921800d07040302c0d2240300d445090010170114034020000d0f51507040501c050054401e015541e151824040140001c0906d004103200c0d00703036070b004030415410300d00503210314038900c002103443c0c603200740d00c84281305407108aa0603541c890700481c400c40140d0302c1001e20a20900d902d034145060800c1c40020b010307680c00900b1180c014480c0d0306980c500d10329449001d40c0408810266000707041011502d52041340c200034405e041100511814030058a0040e0070211a8a8081000100c071292200203405800c0003601d41c001594800e0658060404001d45688a50500050041406402000e60340300681d080c0204c04666804055900b4241d00114090340d54604030042054150320300c0d070007500500441820f0007080800306490003103503018fe859041c05100f05040005031100861140c004418200c040b034049003500000b000d41c090b024003225203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 891253300 1250 891252050 891252059
    0xb0304111318081b070e040f0503040801050a09030806040b010c06020f0409050a14071403270a0f02091f030f02060702060d0b090601030219031a0a080a15141807 71
    0x100c610350100031601c0d483c00143e0700d84169030a19070742e800a01510f00404d03549040c0749803040302c1c001c060300141070b01802600c05010400d0800485020f800000d000b80032904000c036040002c0c3c0b0070020b007103002c01c802d030380001d02c54206031250490415050f90360312991502511a10300a40c450419881e0000d0100404110f0300290701403207010b10314550000034041907400c0d801c100e1400203000a01000610b115030408030001c80d09883d0490f15162004205010303170100114020b003100901d59403401880303000403d12640e0b965001456009841d02c000581d80c1d4601608042c0c100d168a40c01c44121880600c0440c07a0892035642241c405420300307180215580004500d6008141c01801d0302e521640c0045003420455451508a4020700303042d400c0581e210440c55411416544040070155507424041e403240c01d41d0750355081888007501c0710b441c0d81e803550401c80d102d1098100644121890080480c50046140700703401000300b261225a19503100d001090781d4801c4030000c0100307203110380c407004907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 891254550 1250 891253300 891253331
    0x105090f19030b06030c030c150a09030c0603050925060503090c041107060615091403070b0a030605011413121a07110f0c0922080d02130b03041113 65
    0x165016103c05603c602d0302c04209860300d198040085e00130740161204203c035841d80c803075401000c02c885101f180c0310300c600401140e00e910150300107000c00710408000103109405500581c0195502c4050320a066a142d40548880000ca0800769126004c0202041207070711400c09103400c400d0300c034259241010b0b9840060140d070685050011642000030f60303007042145911402005141c0c20b804d40e4045011540d01504249191003400e95a042c00070301e5a000796800c0c8402409420001900c80d12582d0280c2c0003001400c584c0901c038080780d0403801203505000c00500b0b6404d1403803e491440200d07801c00c8405c5004103005e01c2d00321624251070144041c011860006036104202d5a0b95180d0340c001c10300130840c6404500c1e1050303151500030f01580b4880d525126040e0342e006002141c510340d800d0481c2c10030803c052030030034041c08507000450051080c1d0a5a001028103008024424030865100c008007007140c403081c0d9006200c402003d8000d280c5041c4412080410704020300e0010300e4011081d101c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 891255800 1250 891254550 891254599
    0xf090e12071202100902011b0f12120c08012925060501060513050105030c0904020c010e2b0e63040503131418060105090f 54
    0x488102040c410b8450569030704020380c4030110380203035007400700070050340020304650303003680416540e0b1040781582400d101382c902500c0c14869029003040c406a400e100020304000c60355150184240c2442c003401d10b620301c02c40800b41618003010603040844425054010328110902c8070014182e000e102c3c0b034191106005800c0d034014090070081e00786513407602d050011114141c20500c00d1000500c0700000240c0481029003da0fa400e0800f03590f07036210307001c503078045018200c0000e5105e8000221550100e0040d0099001c2c559000700311040300400d080240c49410754070240220428090104481e210f21401c000c0c200c0c100054507808100a48840b02d420300748d01c1d0180c441c6038030442184800380c0042c10962a2070764024450803003510003001d18100020b609004103110710707514207000c2010311000f0f104440b202220903030301081e00c0c1d6442c0d0308140d14983c41d25915204040b0001d200810010401782c00d44a03900507510740d8940085001002980c04044513950b80200c0310490b0381141c0040394611 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 891257050 1250 891255800 891255803
    0x3031201030516080c01110309060c0c18240604050a0806100b04060c030c080d06080a0b0601020106061707200c15041508090f01020a03020a0e09010f090e1207 70
    0x4000d40c11401c12a1600840032410740d428a9251002c020f20724001c110f60407002e03002d203071580c4ea4200c0302d507400d07242d03006881401e035108400003000a0340d450009000c0b10404400d585130240303840c0e9141d001d050351004880d41d02ea9022001c090710864105540c118990402c010030242c10301da2502c1c0803408c00c00c003980090859505c0075091101f2880c040d444840103154064100349080c0c00c101c0020040d441081d401000d00c10360800300300400403013905503440100c0e682e82c01c02015035241403032a41c2c1d0556120075034042d044040442d1055206000d00070076503599442d252101c0c10519040390003803000400403410420f4001c41c1001000980d0850500481c02d00e0003007600e07410360b00c00c03c030380d1604c00042e2842c00242000208010841021190801c00050405a01c9581c488094909150117031180d180d081d403000592640658166010b401c0102250390f8406c2c41d0443c1c0018068500c0c020b00036040b203080051010014107840d82c110f40002521142541c0d840031942c191005542c001c20390 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 891258300 1250 891257050 891257077
    0x60a061208030414012903120406030b0411221d010308030a0e010c091409151207030803040308010f0b031009020d0207020a14010314012d050d0311010c05040b270303 73
    0x107100446e140e12464541504100d01a200e03484991800c0300300b41c49240301d18802e043e280e20381d2007001e9596038094401001c542d86610303998511700c8a5012164003001000c4a0207401e1500400c01c3c40d61200c0340090120346c00c4e01a9116420b586640020384c00052a550f6195119501032504c640280902c6130741030b610392100c6c0c080030f080448040d0048421155039024259036030400c000c0419040c132900b42e02030305980305401d00c04446045400c088590300f01174043e00c400414070040690240d50681200c0382a6201c0c42c8458840000c4003052100340c0f40789480015001c404d2080300010b40c010071843e51020b400615003c03042d03001c54540c940c0342d40000da0840020303600d8040c07540c05010711a001044141552402d60401c0c51a56021000070114840c01141072201c2d060042d900f24240054800203188901d04825450700610700005111075049650a2608602c000da0198040c0c1d416107040014003800e040c0803008841c1c1174074140440c0350280c40740c0c041e0462251405d10081c5045a007072038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 891259550 1250 891258300 891258341
    0x1e120f060f0207050a03090801020c03040312020a0b180d0c0807030f12060e061002061311012d020d0504290f0301171c1422090905060a06120803041401 67
    0x1400307018641c0788e5002180c5640104482561103034044120740549038400103003021019081e034103d103000c1e401c4038010b0048208800740721402080d03918a07402103200d042140c020320000b42048402c000d603020003c010b030324140041c400080c0200c00e0017403010300600c0d0684502480c1201241a14400e034000940100003105000b96818020240c0542d08464001001d180c01c09402420b040315880d000034203c4420b01e01e141034142e02c200e00800d2200ca5803040040400b00e842c1d43c0d0000180005c411402600c100607040660324040d20079075049072003200300050300303441000f241c101c070711700007244410400340030401c2c580482c010340082c60180c902615029840742000c90898600340c0320010000142d16141d0700c3c185020b42c0b0031023510b4883d64200e2000d480d42500c04c0c10080503d2680b03070b4603500340c0b080d20000c9541c424070391080754501e004608851554903130407440d0046032210700600d540c000710f41c0e8206021426000045410134031403003000800406140d041800c55a01c0d1441c0c080001c5c590 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 891260800 1250 891259550 891259553
    0x9110403170d1e0c020618030f07060e060f0117152e031b080a080306060f09031b1e090103170c030a08180133030b101e120f060f0207050a 61
    0x100400c562001d0018445014040c7d40c090b00d56690044040340c0c06007003c00140e40d0300b003150790703089038010814003000c59180c0d003825001ea0b035034028240500c3d581190207607401440c4c5040011742c09540d1300c1200a15005484400c0505168920444901071400804031407003231500c40c4038044d6009500541105607040d00050007408200720742d500c80e5540b0381c0b100343c945004c1114a02100d42051003101c1042d5200800c4020342114000c4440302c035414001c0a04060b0240100a4154541e4104407400c400100d031405864030380d095201c420365080683c0c24018400030b010740301114001c00189a1050402280b070f02010320b96841084080000b804c2e0f4020701031a031192400ca0080d100030780c0000e02080101c002c0d481410400c03001740003c113080b040340d00c0d0b1004d0000d6000001841c0c00041240f0740380760100031188400d83c54403400c0c0c075200207580300c0c18001c4120b00e600010f031250182c003101102c040d500c0d904405030411074191366007550381a84c580800840d00c01401d001c0d100d0000b501c2c0f2a410b0703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 891262050 1250 891260800 891260803
    0x60f0c07050a06080a0207022205010305011b0c020f030a0804171209060d1e02040e091006030b07050705010b1e150307140c0c041509110403170d1e0c02 67
    0x6a51225002d01e044803010f1010341e8203c0300070303580311102e807500680f110010f00000d018094142000707850081462100c003c520a1f9400840c140c901850081c00071a0301c084d00c1d1401405114000800140b2080c40000186000c41d600c00c80c070038004007112002c0c80d181e00c5031100c40c1d1150b440b04902c04169101404400700034407111700b814403a51800b0307003050304900105240b8030a8079811001c15981d10202242d0034400d000201003004040000c6440703d84034450428426000e4903458014840c10141d2a802c85113170050109403030380011a800c468580e10300980d00b40c1c0281c40700300c1d0a552180e140c00c050380c89015801804150080ea094150b110b02e0b0140f01082d500305441c20004203040040001440e004101d4030320f03840310b40001036910a042d44442d41061080f81182c0e07408ad003001600003444c500700001501380c1308552410804030505034412805407003a44001000300c1c171104040c4c0107400c2e0060140211301c142c004d0110b84607040d180c2001d0002d055159101c2850b03990440c1048060f070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 891263300 1250 891262050 891262063
    0xc06040308010617060909070906060903030305061c150209090f0a0e300f1812010b010f27060807020c031f0504080d0e030409053301050405060f0c 65
    0x41303013004000d00010740202c1180d2032005140e01c0c000c510f0300d0040b408007001080810010108000300f0043c107170301d480004090030424801580024204008580640340c0303d01d00c02941c0f444042040d523a1a000e90364000c12039640c400e0b84900075801d100c1042652202c0c003080344200d6003014001114507101090390116180c0d59001d00c0180d104001e441c00d41019510b40054240d0209010b401195146c04108658410b822080140c0c040110b540d08040784a44412004044116003c7c0d01440d850f4264500721a030710500c0600188144000c5060035014561460102c04184074210b884609401c0501d280809039200300300040000c4108840c071541032002481e40b05044000d03115607140044013032101c004000306c04020300d0355140820100490b20702195000b01d680c003401d104036101058000e480350498404e078481541414000343c401d4880284a80700210742140c16403e2880144501030031080101d60941848810080803829555100152164034405c21603160791340e40b20b4211030309020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 891264550 1250 891263300 891263309
    0x7020a03020a0305300402120d020303060409020a0815040615270b030601080c010e06040302130e010f09080711030d0c110d1203020d1d1f090203030c0604030801 71
    0x10048040440029800300e10480c21681514025407210403481390200d40a017141d50741059882003000340d45036884a0361005100d140200d400e220005400302c80e003a00c64400c090305c900180c00403c00981a441d10b039004207411360000c2c0c4102c11940c4c950207c10b02d403960780c00380d850107070200d8000c000030040c49010360781001002503101c1260a1038804869100b100400d0424007051000c00076501e242d0840d4069403000200a080715880c4d42d4450582d5190b8051480490000394a4095075180b410080300301c500700d950103420242e04030810800d490042a020500900c195200c1000c0450441f4a01a00c10440c1c000c0340e507035648841e58500040315207106c18a140c001c1c1c12004103a8680d903003041c2000809504450900040d41c0c82000240051355203034002001017110170058a0020b6150b80500401c0300001010400c51220040c0142c8160b03220351240720540c082d022480c001604510303442208032890001142680c415030020b811078001204c92403480e0300072000c00c424154030003041401030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 891265800 1250 891264550 891264553
    0xc07050111070f1b05100c0501180b09010608072411101d0a02010f08090c060301030b01090b010c260d0536061302060d0f0b030d031406040510030501050412080702 72
    0x30340c85d0201082030100d0541090b000e00481078500414031a0a40000d400e081480300c580e00001c14610340142e050300d085c0c070207829a40ca8503030040381c0b07400001124801d135240040e803403a00441c81d5010481000c003140d004000c00c040e80d13001540d44c000802c02030701d40ca0700c541c0000c1501d1615500c0030b035140c100302859204c01d0740070400100150b60066144216a0003d1511501c90303035500c0d9500e450312034039900041e0462800000001803086154240d41610703100c040c20301820a0940045440320b0b624940540702200000c482082d440040c0040c440311002d14071800e09010154050f5009c40300c0c12111941030510800340c8125407a2584040c140c5e505c40798250083c54104442000e55490005000b51115151008400c06654605c01170354400c604404007800310745010075611020700442c10200303019105403034428818900034040c40035103800c1596031084035030b00c82c0d0800000d8000600000c90441140c000030010500c28007078a8425402500c004940c07140e040c2005000c0c42008210038110f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 891267050 1250 891265800 891265853
    0x912100609180206070f1a0c03040b0601080417133219090513021207150212120a0b1305011d0112060b06090316030c0b0307080c07050111070f 63
    0x503130f9000b05880549421880708601140035280c040107005200340a80020041c25041080c03412002005500c00ca109012082d0b03d601c81c0c1c2c00540320103c044e1170050840d02080500640107000720080c0403820305081030b0301ca41d29500d1404100c0c810720805030340400d0603001b10501841c006845282c014400981e4261420341800d030200c11031040354000c03e0016505ca80c08610019010f5402c0b070b00550b00104030074041c0300801d101940e104064842c440000e070200403c400c843d40040b6200821298910080340f40503100003d0903131580c2d00500304a0625900c0014403120f0701d555003440380038003400900041550404080c2d0b110086d0090a0003808405400140440010f0354895174400b13500100100b01e080a01c0001112801000c41d0b2a03054840d065042c070345400c03421544011a802003c0e00c100040e20b800111206100c12035088011441000100c0c0303400c10308800800c002405200001010081c1007040207039588458420340c1d1090316001d16106000381078015121170309144818414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 891268300 1250 891267050 891267053
    0x140a050c0406051804140106170a0204210f1202160b03040c05370512060702060105010c0515010308031f060210091109130308090a0506040206091210060918 69
    0x14134400c1d0216044000f152503289001340e00d07035410a07022401c4880550301e0a42e12041c1c000c003907951141d0446e02c643d0204010844503d210300c00c03141519481921b04220150480e072404444e40003031700468a08a80d801c03240b0100b070003403404100744c0820354080c0c03041c141c0808624440c4c0790a07810100b220f4000700305010000300100c1c041c1080318030503070b24146031142100380b204042e02e42c8020100a00c1211402030b80f0411951301540c02e03034000702c03400c19800722001c1d074080d0790702001c0b1000800b5a01c202c00611056020b070038a12000d5100c0c1049941d01c3c1102800305070094420ba0049030309000106c2480300000f840c031803481400419240d02804545041c4000399510303400440c0712200ba07901e22407403041c031203801640d00704040f0181008049080098014500002107e400ea001800900200e0b0700403001041032141d050b000302c020820f42d1190340800c001c41e48807440301a07201c0100390700c072004418248031011a50241c05000518507260024074401c0e60410034024103002c100c5580d100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 891269550 1250 891268300 891268307
    0x3121106090712060e161802030f010b0304050f01020a0f201203100f0b040602151b0f120a06290301150903051903181401080c0d140a050c0406 63
    0x81280c003c104590b50703559107410000000e103002c1d60f01d1900ca000b0b03504070042d000700394101a0215414865000340c840c0389012800101e020984203202c2043c1100c00410200405401458019001c3d5040e03c20740d4058510441c2240d005010f000d0100b1801c03038150003010340194110034090340c0e42050101101e159054161910645118050b400700c02101103a50300c010300034030001403c0240021202140c441c02c40203001d421038420803005115070a004502d95041c011407a003c0c60407a0650f41203102c402c02c0c5a0502d4101d0b1628413101d07403040c030260f01e0f5140d15400050040050560008000d0b003416008072a030074202d403101151345844641c5215010800c000c07281101c144c00b6028101505240b0119180807007580050200e205007448003a144a407a459403000c544240c8404d1210f501e41d95003400810b050313215800421000d0a9141c009501a100f1142d00c5889509214546039041e00020704440060303007403075441580c032000c02c42e4101c813038812980c105c0c000700303006c505203464070310b004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 891270800 1250 891269550 891269563
    0x10801060c32010e01050702030a02070e070e2d15040e1b0c030406030b0a050d0b060f0910050423180f0105070309030314070e0402071401060312110609 67
    0x622031420140c2e4401421568980c51a001d194807048801400c42c0010b281e01800403401c0c0004254a00004500e5403030002046445860094000e00f00030b40c40c1c1030302c03004800c030300524078018402d80480d03c940300d03070310350390049200a103012066040020700345c078480c42d440c0312103d543d008407600c00c0b14446070745022080e88c0880319004000029580d0b029115540c60b02040400541640040703903896000304044007620541e400350b50200007000726001008140d100074032540e5000100e1000d42c5000c5409220030329400f01000d84030b030715541c11810110305038010448421102d410703882d00600041c0350a001c2c01c00c00c4d900101c440c0c40d100f099503204064881c00074054054040c8041011900400180241c40e80d10100d10004c004500d005c0c040940a086c8205084001900d0f050700e0610400c0700e25501800380f040c0d0354482044162280901c4020f522403001501c900f180412200c07810b60313090062801543c4291030101c9031141c40369011307054200042090000d07821080130010b01c0701d03002460 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 891272050 1250 891270800 891270803
    0x7091a0a03020a050d0f020d060603050d0c170c0c150a0212180d051504060c080106050a142203050a060605030a080909042a080f0c13200423010801060c 67
    0x801c103118591b868544814981400d000750452640e0008a0600c00c40794812000c032402002501d52000116130f08590300c0e90f02940c01040407844a28620052400794050414410300d03d04540000802e40f0010b5005403d1061600e1017050005040b61040d5041c894400548058000e20b03007802108050800b0301d080b1500c8045c06062402850310a0100c1002aa034960b80c9110704000c3c80e04107402e28030090160510344002040300c1d8400058840d100d40c04860261915540c2c0700f191104101d0748130304690014150f0303608000c1e640703500800c00c141c18125500440c0305400501e01801245012802e903941c960007644280c0040c03c0b10404514200d0403610210401c1f194000f06540b070b8a4000e8070303040c0c0c1d24001902440310b0041c00b01c912410001c22800c1d0313440c10342181c8106a80880c034541e244070074030156401c0103845029510344525500314030b45481800f0509152000d54030780c42511a00300d64400d103403070000103480340005594a4909062030200380303400c042643c10070354050028032a0200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 891273300 1250 891272050 891272059
    0x10e0304051f0228030924031d150a060506090d03210c080910020a0c080310090e07091503080403020d020d21020c0409051c1107091a0a03020a05 64
    0x511071000c0f8424080020100365600004114000c1c554840102082503203080b80400e14001010601c00302c1303d1064005035605038044411076480c814210040c0040c149240071803025076000403520001484004008100b0310410002480c14002e04400e58000358041800780c0c0041101c2c9109441e00c101000110303805007400700d00b071708180c00304c50744003040c3d8181c0c03840703c600d80104800300d6540070750f10b03500030380605c01110260a000007400040b403240c424020701042c00c010121000619810185a1100100310f0703910500703035030380344560503251182000115500301a5091000c41c155100345074221955040b1000c3c04e42c1580d031042c0d0288650f0001a12034400d0582003021136950202c03040741c080d401a03151600210170700044906505615144025009a80030000b00c1d0900d440b41a1a20b600324009050701d80002d20030b80040d0343d569080100308007001005404400042002400801300c40d10b00040d40c40100c2914482401200c0390148501c140720020000759440f80c003c0d5080e14030884 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 891274550 1250 891273300 891273349
    0x3010510050c0705030304090c030f11190302091309030206100b03181014011d0609040308060d060e101109011d18100510020a0b040809040b130e010e030405 69
    0x81d100f450401d00380d000310b50500c0002004030b07a202894100c60456001e685040c08a0b039241c091034400e40d20220140d00d0904410311141010140a850745580d000c02420018580050100428117805103909182c0b603854481c40c15600b0180c0c1041001e521000841405903643e007004d0704007015100240003100d0242400d0358500c1003d806002c608178083c0f00b91010090710660076065540c01c0024841d00286070b00300100340b00b100f032170001010300c507200081c4680c8441c2d8550342c1c241c4144c140601444d0300502e00680c00c0001811b00d20802051492002c0105003180c085441c0b803080c2d0f1281ca0034090071031800c1c4021025a40c02c60b42c204d8506d1804800880e11149920224801014004440311f141003050103001250003c00500000d88006444440002400060581c3e0380c1e82c030800b000f407c40e02c0c6080013174045500b0740c002c4d0030040001030020070192682000514050b0002c0801104113503103090812020009105100d18600e56402640c2070901d0640000e0b0380150340040310524402c0d11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 891275800 1250 891274550 891274567
    0x2406020a0c290a0f0806030d091a1308100f020901020a0210230d0e070f0e1e0c0d060e01080a060f06090e0d02070b0f091309020306091b060301051005 66
    0x1200c42c0b025036414086901c0e10f404000500405005031158075002003414a008110300c0d05020036441441c03240741d1500d0544503d00a8078442034406130300740f280c403260305219200c0d81c0385500442030000d046040c0200480264124030404541180300101c004c207204114140341c41e41c0200c2c007840c0203a0110b910941861036800c05540000014060044c074511481603180211800740c0503105a400582c01000300b0720705150b0460340c618503030042202c000c10780b07042001119228400075901925503203070080100040346000c04540c800356130200458801048511405c0010b208000081c081c075124182a54901100552180100c5602400382512517840d0744c080c00c0a034010340300502100d241006021414600662201039145014005026018000030380802d64801c1d10710080801d02114a0300b042a81041442190002e03420200c0c1c2c0c83d00c88610240e0380038490f061180c100e4101a02c643c8860b800d4001c4a81c040c1200c4030b1290100384010300072500c1d50b4828110000550402c6559403a19 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 891277050 1250 891275800 891275849
    0x62a060f0f01151806090e1f05130f02040312080f102c010e0105180f070e041e021903140a0504050f0a12110c010e041a042406020a0c 59
    0x4108220404d6458400e00046a9078400000412204064175044294072505000e004001c1109250100315454880034001d61a0254104030b140040450006182c03000c114910142c3c1c01550040d01c02580c01040104015001080c0a6004400b8004c94800b45403c00011120308041e00400050108050102c82e0004000e02204050510415844c2c460760f501c260103604078a0900403e80580701d0001e20140c41d148600b061800345140d0140e00016654180b01190004060380d0135640c010385900715001c0985a1207415691800c2142000da541e01c1008004031440003140c5252007094640a00f42c00b140303415484a42d0441151000800c0da902c403814014a0090140c505000303602510208a08105180039000e010710181d455401e01c401901c445d10351030703590300e4038418040303580310880404900d410780c04200d1440e8282c940440b040d8500020a04480224144400c59000e0341001c00c0d4290652180200900b0305200400c95482139558046040000344910302c4054440720018801745078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 891278300 1250 891277050 891277067
    0x2040503070e1f030308192403021009080304120c0509190b040605030c130608010c020c1c020a0306090807150c0305060303030603070e06062a060f0f0115 68
    0x1022600d5482d19039000040060080d5180054503000b0046074031054880f0380740d082183d800d500c81040a07690034005281a14104c508880c10a40d1440c1a000a2100d028040140c4803032108003080c0509600c103200b2800110031a100c01d200540c00d04008200000086a080d1000b181a0f00219945881c10241c010307465000140c1c070480c044100b1000001c8500c071401d22455015007030102c06000800e000442d6030360b02800b601030f0005011f0b03149074148030503808512000d04000240503695240200d007100c0003156008010f800290800205141400044010268007104440111156400607008103918440140420b8480c8503090174040300c072040c0e48600307411020009a400010f940c010007022450f03010780108c1c0c5441d001c10020704000054920840d0b01070014566103080035014220848020200c9500000c2000b014074803800d920707c00300e8401007040341c460084d82c58481103070400760010a001b0421002c3c10403c03c101c0c03c41201c5a0444140018103015003406001c01c854090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 891279550 1250 891278300 891278309
    0xa02090a1b12020d060608041709010512090a120906080907050a12110301050a02041e0803090d021f08100e070203040b160b01080309150903280f05100e0a030210050a0204 75
    0x1484d0990000b006600070154a00c01c52003114107209c408104031401559009443c0340c103000a070240030401300c2c0341c80d8141083e00111401c0c01c6604807412681c07403000c90320040c480080041c080a4040203082d82149500742c002419201411006003440c010407102d01441c854880210040340124041c00709401010f502c0344800790088c001854040c11034400395000d4424071091a050050000d107951031041081e0540f0400b0700a98502a4480704100c0382c074810303076002e9900c4004800a0f00d4200128441a81014050b840b807492a141c608136800754003000d80d10a00468003e44200604241d000c421070301942c5e0002551900c8142c00c00d08016010488000201195a0000003060fa480c001014150149003100c14070040b681600710070a050040f40c407100d4041e0b00908a17110100c0b0311186001070b005000c50105a04e0015807210001040f94074010341d019002040c03c5414a0b425016403030f54041100d0081801c01c0080c1d030003d40e10385040c580822025942e00125105000580460f030080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 891280800 1250 891279550 891279577
    0x180f050f13020a0806150a1212050f041805060301060608010f0b030c04090e101a090f0601050c0d0f021902100f020123060315041509020d020a03050a02090a1b1202 72
    0x40c906a00d1552856646c801e0031841040f20402c0050401608802d041280ea809890030441c00b8404000352200d801880902d55080fa0a00000c1004010311200099480034914080340e1401e0a0061508603035040d002182000000001840000210385a0004a9150401d950364a40d10500c11940034015504030000060074a5030211042d01700146946801d21400d10420101d0042d003007240204d80030803402c0e504407000d400020144020031150b10f038410300604210b0326140380e030b40c0660304206c0f0b00c0c0c000601003813508215040107030381000744000148000e80034080b02400380e00010f003141d010519010402403124058081c1c0c41c801c0d0842e00040d0f2000c14601c04174111030625040e09007049485030f001c0c1c405c0c41e40d0808210240c031445402680c1000030030912102041850014048140d007d0341c00420b10018000140c40303003000c10f0000c5001310080c0c031901e1018810050074803c09402c0c00003041c205144901ea28040c22450004c403445810621140755442e40902c1c01b9014400040000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 891282050 1250 891280800 891280813
    0x30705040e0702030307020f030c0c01030f0b09040c080606010504030209040602070c03050f03040914070905060d060302060f0d0c020d120b030703080703080105010216081203070c02030601180f050f13020a08 91
    0x14543c0000c040c6014042c15026a4010205414116641e0150310490015540217140304180765020754464901d03e2511200826880e00040201d61020003d031012542e0501d540400c002a04003440b400340c1114003460840d19080c03454001503905c8101600107041158002a80d5082252042c004002141c0c040240c80745020002c0c02d803512034100c0c0c1716062419080c501a41d40c0c1642c90702910303220340290345070403160504000506c0825082150400452a91104d012000d0380c0c940380580210303803083c0780d456030360794040c01d0000c251850030441105660020b400a035805400241503024142c005600044c1d40340d400700041d141400983c00a000b089000441c0d005065011003003905881081e02120050088980506000c4000d40300b41c50541d0449410036500c1401003000f1030704000c0c1850070008840700ca400180c200003080c0d01c08034652011440203903041025001e03800d00d401d0b0380042000a80703040740410b01c40c0c0600500c0507580041d6001d0300c0007195541114240035188031000c03200e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 891283300 1250 891282050 891282061
    0x5540405151e030c0f400b2b02101710061b081909080313140a0b0f0a020f030307091d0702191103010c03022d0f030705040e 55
    0x96101ca40b51096010380960320501c81d003414484882e00c1e071000058011a80103100c0141601003401c1d00005030050b072030581502403100640241c007a82d01030103410000340e0b02d00945c1000441c5421144c50402c80c907917031001508540700380c041c201c4c8494047e5041042c40d0035424046030406001d20200c203584040d04144684000070310742102c1a6905900c80c81d20000400c84a4140e68140740d000426600303081143d80302170071070300320041011040f6061500c1025210381c005811508400c107952018a5044000c00ca41c90010207104c5408505a0703d4508250a1000c070018601c128005040100000500400028420060503200103096010740340c6034248050018003074180c80c4606441e600e0340b26000c082206280740b00c1c0f40a0040b64006200607a100f13400e800d040040080d090b45d41000c07040d83c0258944080c000d420500d0341c107940c0141e6440f0041c442c10342141528440840c40f02da8001c60100c01850078040755140d240c50a00130b5200c2d0360b8803104a178284110380280e845295180203014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 891284550 1250 891283300 891283339
    0x1201020a0c050106290703021204080109030306050402090a1703090a030f050601090b06040303030510050603090102090312093a0609050f0a03091202010554040515 72
    0xd8041d10a1000f0f010b89a0303522001454514620509585c044401c94100303145601d14005040082c400d00590700d420040c03207440c40031034000e81d1004003940d4480919070100f5078144102005807008903801c60401c280d02c4082200c60049009400b0748981c440c001c0b0000788010000d88a02c220014280da143c2a20391402000c0b2040100c0211014400c80c80041114016400388a198400140030141000d20b180c504070040e110103003120b401c0c4c010002001c107040d2a000c006511420051001580d00c400038010315240a8180c0c0f80e440a12509000b80f811640d80d202c880d0f24000350094821219440700000620500c01964004042c02c0c1011500420000b0640140c18424051810f55404030000d250040e21280c403071000400013034486505003c0100f03001c1454460303074010701d09107060030719540d08804101400b42d000d6008034002c000c1056085050303c100e16100c0e00300070180040c0c500c84501220f00c403003901015882a0340b10000a040c542c126200000035003002441643d0220b940301e82507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 891285800 1250 891284550 891284567
    0x1909080105130b1b07020906041d070f0506040302061b1006030302150606070203060403030203220f02100f0207060516081912110412080910050a0305180607030b1201020a 75
    0x2160810000000188140529500c031010a003409001314078016040d420884103210081c01154444e598030300e42084020f685d0401d0b419031b100103009026290400c036030f170680c07506c0781ea100c3c0303104003130401003440161500800d481c0500c1d50400000850f072464a0803d09001d1081c1d102000185403040c0042855400546c1ca101e09100301140b0740c06844982c2484031f0392188800180d0140e01c4100440d0001c0c5c440e50081d940482c0c201030100701c40c00b685580d40e41c24410140c0a55030a04c8841c410800d41c5840e80d425200030400b0b04004000d0505a800030703455076520710501d41400381c0803a684140d1083c1d0034200c0c64859110028035680d000b03851040b000c011000c8074a4000514507140300d0b008101d0780c0301d8030b113926207414003160070a4a09038558269140900d41200ca204040c0458105510360903400802c400603a01da060315031400c184011308a0b40001c00082041111001e0111542008a400b03a0050781324540800c079265a1004944100c44009610501d9172000904400395940440340f13 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 891287050 1250 891285800 891285803
    0x10b2b06081005040c0e0112030c0312110711011b1707020411030906070513092003070801080d0903030914010c1212140408091c050a11120d05190908010513 69
    0x3078142c2561101b0320325401c41e00074000c80c610790a80d4234a150111b40038030158540c043c864544003016100c8181420203039081c4d007040d1b01d29000049880303c1041810422201550000c0c41c0072030001d2004089100451142c080203440c940b03a52501c00c07a0788002d00c045441e039907005441070010131a845001ca4050380200c5103401c860241d0300c04a5107140c4510129848444081000210f2070304242d00d550041c49161100e003c0040a080404100c0703034414017844c86542980c6a2184035850051160701f41041d6221003010003604031000e01c0020740222001e820340d20741c00d00d20b8007440c1d02e207001070312545c0c807903000603020131200220a0361107a40f100440e0702950002d54140410061100c4c0a03080050654000300b4400d03082c08641031900b0648a4040c0021103001550780074603090300c40905002104406440c500c503071192140007400c00d403c00c610300300c018500404400c1600e5100074514040c85162540c40d47c1525036001400f44100216030140089000811090078094003000400381304460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 891288300 1250 891287050 891287063
    0x105040b010905060415020705030d112503060b0103020909182a06031f0308040303080f090714010e120304090e071202040f0905060f010806010b2b0608100504 70
    0x104500c254401c250640c2110000381c8803031309041c00c01070240f800303200c8600244111301c903a40700058a950108842d4140003015241e0176031411085144a0510482040c00500007504100b00d000050041c41d1140849030011030000f001068240124068031480801c142c6c80154103040c0959040d22030b4000740900040e0b411946035065007038040040e0100c07900a46401420050428103074288003000316845418081c5155415064000151008210760016541c0720f0001c5020f000309a000082c07642c00c920800c44042d0189043c00e502a03540d0120300400c600c10002a50440d400d03402a1031183d01c1c11001025071045603622000113a0b40c1c0c100b4820074103c80d050509590802401007801c1c0241c0b40e034014210035080c655000d2101412520301d0620946680d43d516a01141c024413800d4000c0315450807d0320903501d00702d012450000c06801039002e0850422180a1010000c40003480d254020314441e04901c02c00e18211b00245800e81c000140f0340103070a80c0560910710359000500c9070348500c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 891289550 1250 891288300 891288311
    0x1050f1305031b010804021903171c09020306270316021e030d0c05101a120705060a030911060c2b090308071403040914010e070512090703020d0b010504 67
    0xd82e02062007429120f00c5002c100060041400360408428800c8100701407059941001c0d80d0b603032170b0700f00e808420b141d41e031000340045854011090a4030145500040f44101446004185d800198a800c0041c1a078000010340744000149100c40c64481c41801e0052400d07a80c5421003803281c0310000da0541c1080b8800c042c50034031009040b07044031030181c0ca014007400411030112038100591714490040d40548413881400c1c808c0712111400e000d01c1410b0582400e951900c16904410701c982c2d5456440c00b070f07605800c1418107020907101c0c3c200759210600141360100310210039062035030084072100101600000c00040503141a2800101d80d001e9840d5090300d44c40080b99044900d951522140c0c0170400550714050030004114424080c0c40c43c03601401447c814107403203440603480c6a2141d0b202c0404d80f1f0b102c1100720385504000410724010414020504000c2c54100e43c0103101d4413500d0818007600c94403030b0201e00ca40d20100300d803802442c3c0c0640702ca00f4860050401d11075002c402d1103410321890421 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 891290800 1250 891289550 891289573
    0x20d020c0a030f030c031209140c0d030509011805120106030b09060f010e1f0321021c051608030124021504030818060c0c0c06130603090201050f130503 67
    0x15203a84080320b40100321604410f01d20b41d01156040c0d56904150b04100000038282c00006144c822000c689126014080d51010074245884c149420084440e1054005040c0140880d410104440c0317400380901e011242c1c04000d0114820401d015000550008510010310040c1c3d1815400001039a01038060a070090341d80340b00d002e554510480d401d0078880307d032400400c2040c0c1890820b5800c48900015030040c40d180e10510703150300490341e00071f03a0743d041c0c240c24005071034880c03c010441c81c112a2001c0c290b00070103040b20540740040b00025a003009000a21807000d03a80007841658100d9001503910fa40c0e595a03070501264110415042e601040340500080c5d0090000581c80d02d4010010241c100c181c3e15610251200b4200070310784010400b4145010001c0b58040c440303103100318112007005171508000c08213545024490148180114003c1240750040341c1200e000f401103e120b860b0100351543c9510040700c0d1402000c940ca41e50040108952201c0d454800804056076029011a2402c2c13921 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 891292050 1250 891290800 891290809
    0x1e0102030a05060a150e0a03142104030b1306060b03010605040305010b0627063006040e03030a0f02090d030c0201020d020313180e0d0207030c052e030b060a020d020c 73
    0x1500c503500703005c45c000c2e40c011051030007000141074000b0f0003080000c40341d540c1d4171100c1c03442004281d0b07020a600030b003041303441101d43d15000c54564140d0f4600c5030704042c02c42d501c40359003d50140c54904984100c0c0200401c1000c07030340090740034209801c212034503035070748880c0982a07810a0008480d25401c00804100a0070700205403100070805940740d105000840440304610600c010a15030046407c100c3c40b0180402e1580ca0b45e007809141f40d010004d0081411192040000a0700d01e81c071503800c1c02000f881000001041d80d820001710b1800080301c41d0710850840092003480765a03600400d40261480525400200c00c2d03ea0038001e800396800030110000c102d07205d12030344002402070500075000b0f05c10b10240c140000d1803565440340005203001204009454040300e810503070016488600244100400c400c502e03030040800303a030341486803080d4880e03280c0f50a8881c1780c8540100001655038000620903042920400300260a403603079250070103002520360258103252405803240c00080740c140e003032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 891293300 1250 891292050 891292069
    0x906062705071209051203070e010801080f2e060605070b1f0b0703050405090c04050a080c060f0304061815060602060402060f3601030b010f02060a0c021e0102030a0506 74
    0x70fa5541841d1607540b03020340000c1c0516101919103220f00c008860422590100039809500380c1d03195010600900e1000415103503050b0000d0030150008a070f081c00324000025050440000c042046035215034050300401540141580e0790055814032000040140d04500140a40d502544442081b6990740b00c031501245000c1062409280e5502d00410640e1141c00103003001a00c2498100e1409941c0c0c0005926000103a42415200c440000c0820031440c00e1a0004028400c520180c40c68007440f000250150081c071030f500f11205e0000000a00300001031f40826980e500d80914a5040b11280c102800d120041003020444c003840d02501041403800010a0b41c442c907402002c0d0f03071a107112880901c2c581c3c2c000366883c001803800e0f9480c440e403032110100a1000c001d622034044e82d00e9481c2c10001000e80e00516403070303418082c1d0300c6481c0000941c0814403d500a0840d071002c611082c1440c000c03854400c45503c8041c208a03940b004003003103c4103400640c02070100003018030864032403500b080007002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 891294550 1250 891293300 891293311
    0x11030601020705120a060f1a0a060e090a02191119151505030a0305300609060f1e0306061903031101020d09051c03060b07080d0906062705 61
    0x2e000040c1084903103000300c0c0001c0244541420343d4000021581d81d0010741d0551100b1050082d201c030126000341c2000200c8410101c41107442e040101c0c41c008010303040c0c000304a1401e029000c198005400d44980f501268111140c2010680c244169610000d02740401550120607a02030701181c030f561a454114800082600491804c0111000c0642807008115000100807800b20082c00060995014001402414000d46036141d9035001480b0007d04640107001c681c5a889030b00401c404400c0780e03100025440030702500c00310b0ba20f13243d040010b5200c840a00c2c2c1c0a902010f450141007000d4034a4400408080c0c0075411200b140e00c503c0108403110241401b42a50380c482035904002184c42080e105140c0d010be00001481c00b4002070402003903807222403060724940d1140b801d032504121050304031a0701480741d181c100822030610032211954403500e007000d803200402140b40004150f40c2d0303004204c1158000000c0000c04d60720031444500c0c04610303443e101c1091001100c0c502d9040349000ea80c0c400c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 891295800 1250 891294550 891294553
    0x321061906120209130507020307031115070f11010c17060906030303040219081603141f020d150e160305040201052502151c0908160201170408030a1103060102 70
    0x164030b00c2e4140003074210310100742d0b01044203030342d03500b01801c42d00c2001e014030215400343d41e0f40d94441c103019202552005100c00e1a50200452070700c98589160607a801600c81c2c605420014a10001101c0d0b00030015074030101546000600d51406400041c52051100b40c00d840c811603a881c0f00c00c1140e09001124150381642080000800601d02450403000611010102800513900c4158180ca086581c11010304200141e490520038400308545121f204d0b0f0841c0b00a10101d621000781501d1003582e0f40341c00e000140c01044025610140c2d420811b8003030914421014440e5840040059040081e180e1034200010b0000c0000d0341c0d0f02c02d001e518820754060311000d18000620a60660002d10301c0d008002d1503051a50010060355030078404187d1064a410b51621000130380045000c401182640900f90341c5030070500d10000b020882542e41340920b910503000c7d154007a00040c3d454490081d41a01f41031724074000c000409c5091005503011b0003190707408200c080b21000f220311061106961403400f5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 891297050 1250 891295800 891295817
    0x909140a0203060a031a1504090c030318180605040608190809210c0307060509010c1209180f06050105090f09220b16030501061d01020321061906 64
    0x30400a9002107801603c068400c01c00c00790f0b0b98445070441d40000716800078100301d0005004400001441d144100d075070865080101c3da00d2030391144d0b89040e139444001c083c8020000d002001a50b440c03d500c00500899901a034000c0403851083c004000d14010544141d1500c4c00c007191441000a280700140880b0000301c0055149448105458002e1000a580140040c0c0c0e0380e10724059200c8014140107079940201608900e0300105804c01c0200e8105004006050240e01c2d103aa03445068442c00c59080060104154cc03c0001280d00445c66007000300d01c2941d0785c030000030f2201e10354080c15144814220030411079455400454440c801e4461aa40c006401c8100d04c40c145000340000e40c00420701300c05c801500a0034815a5503d01a00200744c501445460030060b0340c40307440e152000801d01520741000150304104000c2c00ca500781100c00d071107111100c00921181d0340204101c42d102c0031801103a801030034035000104032100c812502d150280e00b12015180c1e02e070645941c0c4800382c0349136841d105039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 891298300 1250 891297050 891297061
    0x506030a030c0524160206192a0810080d0e04022a0309031504080301170a1b0513060503070b09041b02030307140a020c1003020d0609060501090914 65
    0x2111a48140c054845000720441c8503450141c0c498111510081244138403458500540070ba42080003800c415030654009808200b41c0c03145601101c1c9002030840400140e503135944542c120340e561340e00d10f41d4190700242c41010309100c3c0c0108105124a2018081188503603e44081e10b071522000748441c1d012407202d80d0795280c145825006046070708440d000704850301c0c824800b51000c00c40c280147c022180c10018200b40d02d802c013800381d0b946079032024841300c0039030501d80e031806210f120511034101c00601c071070080c4580003814804020315a41210340140940303103940b0004031219180c49464440c1041000600041c8458041c0108031840100980510ba02d040003000d155442004959032141d51800182c0120030920340710348403d921070b8001c0da2685030200010381504030080c0010401c940a1002c103000d140e0010b951748a0800589003102003100603d0140c0107806029420382c1460306040010a0589242e8482004c4603000d0340e03203d0030b07aa80c8814900c2200c03035103400304424124407000101c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 891299550 1250 891298300 891298307
    0x50601060f080a0507030b0d0602090406050f06090616050f370b0c04080f010207021815010302090103180f020901061404150e061809061e01080903210105090a0506030a03 75
    0x103034003035021b00f400f1030010180700000d86143d0110ba0210348099000c139281c09036081610515001d00026140140207000a0000440f1030085428840c0704e0703040010045a031071418120320b054254801c017100c4691041000c01600e4400301d00b58080d0000d1883c0c40070320390301040d10300400305261030980b4509001172a12503011110000304070001e4800101b1000480176010801003200c20425400140c44088620410546894814011410000c0d10052040c0c0d40a5610b801c003a940d42400c0044e592100c1b40d0041e006403881c846298074121440f207419040c4807040a507a154180300321101c0b41d80d030b130f02c400054400342d2410005001c400000d00050041c15000c0610140ca03038079508189940c520354000050055000b41416451426038615210355810303d44402c9030849022114821801c1c858000b00b60507103017514055042058410110308030b080240210754402d030205c3e0350b4050299041000740000c5e0707001e2207400d0113045030f8400201e0b440d1482c401c0700c0c003508005024004146050301c088 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 891300800 1250 891299550 891299561
    0x40b10050d0e121314150d0b0a0e01031406010614040e0c09030601240f1d0a0e092a0f1314012310020303010614070506070507050601060f080a 63
    0x1412280319003807407025182c103d4009440115a280c0c0700d00f030114285500c3c0c10f4420800080640a861500480800951040103490690400141c009019001500042c0c0805415072000c05648030040000c024806007540b41c1d1100f405000445907540da9510013256900c00112510303e4891040c04140840d0384003d40c8160828400b1080074101040079001908241003a40010030300d22940c030040c100c8030300c0c01c4440e200310740740d0b410002c0455505003005011346281528981d49a00c00f5502580707595900d107004400f1f4609110751a00b50324180540710f68030b05400301105a801c9000440011b5107010090900d48804054a41580080d10758140101c1130014000d0031900345d140c2c040e100c65075040701c0380340e80280501030b003104103080c0c2c000e0b491009060703918426009103030340002400f1082c3c002088a04440c014688010000041d14044a960094100003495406a0014004255808005406958000e1090700c0c0c96907651041a50180340c2c8440000102d00100009041c400460340700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 891302050 1250 891300800 891300821
    0x601120902040b0402031503071403070303050a030e0a05010f1406030a030c0302120a1701050402070b06100221090909030a1403131b03060507090f030f0519080306040b10050d 77
    0xc502d600210f40090240d81080343c0c460308644464502c00d0320792500b081540b00034540894115801340c002d0307001c03270780f610b83e180809818402d00042c654a400d100707a1141400364803103010740341441141e1420b58060454240305035122418005002c031001d880030042c47c09254014000d1803c469903a50540e078100308040c00790158004e01050500780c5011600070002c0040b03a0b40c0d2205003524000301e2035030b03414040e0000c0740a140306016610005035a5244150042c500315148541c4515041d003c9184c17080e08504111020302000940069a00020141c400040c0440e112a620760700c0560840e07480c01182011b40000300014180100304201c00010754118940e41d00003403408429403078146c1c00c03400d283c1380f030149441d0f1030320200300341300c032a10985402c070b08103240ca14620351602c1025010400c150001070000000f40c10084100301081019422504054000c110341d58a1402c0400d0300c2c1d00100c80d081e01403070522031050740c240fa0280e40e81701000d44548840b4180700c4100000760080240b00030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 891303300 1250 891302050 891302059
    0x4050a020708030c0319050606031f0527010501170403030b010c06050c030901110c0a0215221707030215031003020a1203030f05010e010e0a0204211202060601120902 73
    0x142401140b040300c01036100b0f100c1003058035601e05103100c11103010842c024601c0d4070300b840c7c00103121540d5200d004a9401c043c50441405074480350044602c03003805594031090b801341802c10799011300b5110602c0c41c40a1000c10488005507a030300c81c01941d0800c0d41425001401c104c80f400503001a000b580300400c000c006252001d44220ec1340c0c0c1e001708503442a00c0301303a070394071000c007c00008000034003580e2907810b001c0b80b0480c145030350034802d242d0b0b480e40e0400c020f10035000c10450340001d000d200150362400c2030030a0a10b000724050900c0b0048a480c500a21016100c0326000b81da0a8000040a03403c072a8042e00048410b0301040310900144c001034405500b043d07a0460000247e41c42200c648041c04504a80c803030b49031113514001d000c0320b082a01d041c0105041400401c19070068065140c111044179500c85107550301e00010300000c1c416500708030044240e00c1100441d512160807450251403092006041144071800149d0b9159400c4403540d0000d0f101c007070350380c1c050300b5550048410144041c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 891304550 1250 891303300 891303307
    0x307050d021908041b2312060f0f070c0b01050603090a1a06040f1a10021606050a0f020114041e06110c0d0507030509210f010912020c03030904050a02 66
    0x100e940c0c4400d4104038900b000140400144824060007030041000202940c2409213020314140041c00c0f050f21038030b25146a018403462410307032134942600c0321100c1441041076400070f01d0610000100000301f80e03080420004a42c001800d03040c040c064a984d0260815174500780e0360318003010004294401081d00050b80112103200b000552421404403400f41100d2007021035190040c02c0c00120f982c00b210b0380c001d0b030782840d00600ea0030f409070380142420f05081c2c82801d05040c0c094000d80c40c140c050380c02d4071a007072080b800000c1d216500001404c61080d0a6803283c8008a40440c22402c0e070710306140044584000402282c000741442200c810740710b041d2140e0410b95000c586820341107980201e201c000320320001540c501c0e0000300f4400402090340f0b50415506042141e24018401e000303601009008601d02081003140221101d0300044000c40c402c12a0b0b20440100705031030103400c011100b150100602e042401e5500c0c008142c051109401070000c5060400950070400030303000c05002c261b0030644c02c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 891305800 1250 891304550 891304567
    0x170423030c0105010e2d060406080601030b191a210d0504080706080f01092a030209011112070b150a0b0703080a0203071407030908010513061a060307050d02 69
    0x60000e0122541c104000180d01c1d07162a603507990034800100582c11049800040110785205010145112601c44172484e01a5640784045070041c191900300d480f4611807a8000002c01c500e00803428880d00c0031002c0181610b07140c480c0441a1ba071b03042c0c4c0d4000c0c0d031041e4024404d55404c00b03000505540d90a1800030b140440c1c2d90100314208400d1040d4030002900015091041000801004001341103d1074035406511b4044507451784540e0600800210135103400032004403070803403d110b4112003500d0082c0302650b603510601900950116020a010908003640400381d0036020864640224a00240074034203c09075a81d00f00c490001010703008426203405c0c840c2c3c019207076600c0c524050580c4404951b500d08007410f001d0024400242200c0e60b240c010030400043d5580070b00182020f5030410340e05516400d0038603083d6009509030304210110740ca44001c000c24040345042e1001c0c140c0c000c0804110b82294801c80e80890741130130382c960ba0401410000b18078054400c6c1e008190301d4100030001420301c0400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 891307050 1250 891305800 891305803
    0x20f091c020613060e03060103080a0c031454031005090304030b0a021306030c051c1b02120306011b05030d020d050601021c1404050910060f170423 65
    0x602810f0106034191805000c00c40d0054502005040c0481c004c01c1190302d590b40c0c01d01d041c429a51000c04010b20300750590304040c000c454003138039081021940b07a03c0321802e8400e0390026219440b014003c5140603440c00480840840d01c4000c0c0a8655840320f2130120a041502c000180070321554051042c04404000400c2502c40c03107001d20845809199128a1820006800c4e540a0100c0c0c85d11441082201d41e110000044041111343c6030502060b0015030860a40c0c0300d0282e998030300074440b550407007030203440d0103980b243d0010580840c200d080e07211640300490b941d0401030084186444100049400c40d80203540006881c8000b240c03d940d041e45503a00c0f581542c0005158011064020505c0c4580c12181c1c003c0d035920600a2000344007580c800c840c1c01780e01d41d110380350b883e05100c00c00368509018120501290040d110150a5400c1410001030f0000c4649030b40c406d00b400900d40e2000c3c003028500c0b811052184508181d541b000d43c2c0c81f5a180d850a141d000300841040b501c50000c6e580d8013500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 891308300 1250 891307050 891307057
    0x3020307120e010c0206100806011a12090f2103060910080a0f0b01121112070503070308070c09021219020d0e0102031b0a09181805030a030f020f091c0206 68
    0x140c0400484c24526800001c1d1400001030110901c3c2d8000b403206010360f03070000074a141181d03021113a02e20741c3c00c20b805400c0341502c01c1d650801071103807129080020070307100058480d10b1842070100302c43c02044022400020b11040e000308104004040011640c01d20b0702d41c1a440c1c010408189005e0415034a015461800114071000c81d2080003010100c8203005901c0e403c01d004210b10543c01002c03c103280d448080a80040540c24415152078202c644000340c20000324001d800e0107400c8030003042d202d04003141c7c143c001c800101d680094080d400314200420340240ca03081c4285410340c3c815034483c0d2124000b021002d41000a00760b0f424001d000c00038501d4010016829006c400040c2d99091010b000b49400608085110800030200021403a41d58444141c0e403c9a1500c0642e040c002d0703414a540000d80103d01d41c80380307500c4800d40c6e000c045c8540440101a9140903440070421102040d00710016406481343d80e0f401c00c0014009448942400000c01c6802c01188550312005403050b80002c03413540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 891309550 1250 891308300 891308321
    0x11011110150905040515060a060c0f111908102c01110406030501080d020604050d050c07080d2f0705060a031503050714331603031407031401060302030712 68
    0x80c0004001c081030b000b001e68403a08580c7c00c0c1d4900b00300340c0c2406000b80044a03134881c024a45c1800c40c00400038415407070502420550020144025514141341da44080344003400740040302d00684202c04642c1c0d01d588166a0741c4000c182055400400700944005103d442da05a07198075501c4905000c082404440140301a10658a00003000d504200e540303031808064501d402e040d54042e40501012903000240000f00001d0f620f4943c4d40c9040c0850680d0038081954002200d42c4900700486180390b410028481180d0021554280d56400c4104410740b405140c2000120741c5d042100103100c282024030040101b6a071a04002c80e000d2100e800c00d05c0042599031040c0d4854021080920810400800d40001e400088804550781c0b03c0b075003281844500f0541e070342e4003040c904c816644007a0a01e030b0306540c038040b61401440303403004c0e050402070040d0200c83e4500242c180907000155806000340318044c120398000e00c09030442c0c4e08103002540294005099441030007184c504409894901b40100030300031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 891310800 1250 891309550 891309553
    0x3021501081e030307090e0c09030a06050405010c08070e0907110303090a02010305060303120a0917030c12160f0e03010213090204140901050603042d0f110111101509050405 76
    0x425001c00c140e09030408690300b000c1d042041403241072a40220320406071401d80c0701c01411504d030b1004001940c0f0800102c203030503004441e040e0062100b1503000502c00d0f0300800080c04203905984013260100340484000020074285e20b840d80e10f038104084020380c41048c03401e02c1c214019207903030a907145420841c1c840c0f9440d07000111500455a06001e1240c10800c194010360404190340084444c000b0000d040e41d52103641e982c0310744113020007401078100c440d020301600c80c0d49003400c200c42c0038503900034048a02d40c031164401060200001d503441516045040e40c80c03101c40804403004682c000064a00c3c1c0303a1664081c015951035032002000d50b0020104000016600c07441d01d01c030307801c070303141c811008a202e45080801008903031244c400b2030790f0050784285114144200c80b056510748400140120359881d40e9040600208980d020a407139140307005501818841c3c1e140001120101c40101804031150000000300c4840f1460750000264070050f0758030000202d896182203811a03d0494068959 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 891312050 1250 891310800 891310813
    0xa210201120e0f070902030705070807020d1b030b09060105131503021f090909080912010212102102101805060f040e103b090606040c0912030c0302150108 68
    0x3c03003c007086184014548140305605600c0d200b440541070f80203170400946081d600180c50740840d510001c9800c80c583d8010408844003401a00000f1840102e000403600b005441c0b0204045440002d101c50417240014a10300b610303006405400060300d071626080c10071074250301d0080010381c2c89151103050020414103d89040b01214001403d103a0b466002d0740c461407600c0c1c4d40101203901d81040b10090030b403daa04001e0003620620082c0244a0f018030185030b0714010041c010301c001c401040901b10f6140c049044080020036101000900f0748280080d417044803480030051890089400b600404905994001003507540c0c8003048581e40410060b8010343c078005400d00c01c144400d41817035080009150340960903400c00aa9508000304240c0009000002c160554001080d50020800c103044800240e0410b04001000079034a100940b80309214030308206110304524801d0380d01204031100e10000035840c0300f040c1c400396241110300b40c0c01e4085009088910701001c5880c69918001c18400e00103250 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 891313300 1250 891312050 891312073
    0x1b060315131103090c0a0f09090c0f0308040e072f070302300a0f08130914010f05061c09060b0a08061605070b16210603110a210201120e 60
    0xf00300c00c1c42c0076207211ba0650401486001c0900c0404816039141031400110f681880c02c20385081002540400c172814041c060120421044034060422245014422440303030f2107611080c8d9030107401050000b5959488001c2d60791002400321202410030b221400e840c1c0507600c940209895540b0751841d64a4580111007024081d0044007103103880d00d410001070000c010721651002e107007811240c00034004c16008103019066141800400f070003022541c1d401c200142d140e072681c05508a00f4403071500c8100306554000f816080010854150300b14111110210822010300c8900400c400c29080c2e42995a5440d01d24681d00c0b025002c40140040e50b004040a14040a1002c803400f100e801e481c0400c04203110301c8000855014080c0e401c0520560b403d03a605055510032110b00c100400019003030602400c40f400b9a482c0742d0b200070305681c020810004146a010103010f4001c0c0d5610901c8540740207280b41c504000d81c4be1a01d2840c061052414200054940949034240c1e40d07040545c868039004450303603c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 891314550 1250 891313300 891313303
    0xe011503050402181b0d36020d060204051815010f090e090c03060c040501090902040e060d030c0503030a02030f060906150a0c051e1b06031513110309 66
    0x14082042440c05200510701030340070a0141890201003aa400207134400300b0b03030b4201048280540b440f108141c82e03440d0f000700030b20315000e070540d00300310b4084100d411f10910300c100180b0b1407014407103c400d50800d00080300d507080c03254814111400b80c0300150309210105040d50384041c5101c491a58041031190340c00d0900724400000e16543d0000d048c0500303400d855601daa0001200012030f106104544520341d2100421800d24030f0807014140d1500650307040004020014010380281d86080c0c1c0c540024a8640304003000b00e10403806003444402003000018114906481221f0035284203103010400040156581031550308143da50074103054011080244490721142e540d0340c828003c641400b584d06106010a130031034003501c402c0c02d00100001e9112079903800340300b00880e465488001c075401181c2070100100303548520f000c400010300510132845105c1c0e90840707482200210041c6914550349540d03110602c00c3c0400001507400441701d2000410b08281780c4644640e445010420075074924260074540e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 891315800 1250 891314550 891314579
    0x110c060301080a1b06090306050a1b0f0f050319240803270a03140a020603041101090b0423010c06020d1509090b0406020c07170c100306080604020d020604050a0e01 72
    0x2240301491303002c400c21031907a03c490341c00201c1c1e810040004a545480030154082c02e6844044600c020101c0b03485022103510609900000c9919650a03c95015501c801c4480d4801501c0740f510281070560700080d9901d0075803215480d00300d40c04242c0441c200e032824500401e0108d03804000b003034101003040d0f1600c0070f0b06101039034240301102004401c00c00140008003110000c3c000505519540d8007000700703414040160003030241c3c0040c140e9880703190a00d0410512010090000d00290481e4070000d021509941a00d040c1c400b650300c00303a0980d410080c2040b009644581d0729040110504005001c10203901c0105000a20000f0102e0344081c01d02c2e4140c5480c0c5550b1103000f070203280407914404140c40c86103158000e580100c000d60344802c0f0240c000c1c549401d541007201020900c001c00e80409400054241034800160744a50044070fa019068040710090300c030340e0700c1c19040100001c0040c5462222118000d2000380340e14102600c2e000801c60b040a29081025140c0f5040300510007000c440014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 891317050 1250 891315800 891315833
    0x3070e0108070b03090319091205030c0f030708190905040608030c060c0c03070609020d020909061b03070804030509040e03030138090607061407120e070510110c060301080a 76
    0x1014914203000003445d41da1f1052290a02016008004192145200c0c4001c071004140510140508142c1401c2c010748962001b8402c040900c9075403014118003201009456400307402802850508000507415440800100032034000c00618980204442d601c2c2d20548002c1d080800085858980b01c0d40854038041c006050101180d0b01402034a400da8400001c4900d529031101000c280c44640e07201194660740c44440003540150407404102011400207003040c841c149041410b03030302c03140070809a15944410707540304002542e131000140120340504002c10303000401820008110f000031012a007144c10a0304500e1000c41c100040b10054401e4500e00c0180c2818001220501e074080180e04402d8814002881d000d0140420003e05201483d403041d10010881616107005260582d0020840e00c1c5190600010358605400220041740008110040d1030015029004803000b161003520104503036070041e02c003803042c24070400250300c801001e503008041c810014441000c1510f010f00002030440003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 891318300 1250 891317050 891317069
    0x6151e04090b1f0f061101020714210405150a0e040903020607020c0604180c090e07121109010806120f150108070602120706090213090b150a060e0f04060503070e010807 74
    0x30244079468100c904141120406e041220b403d80f01116802c5c00f900413030728058003000d000e000151400ac002308042a480110001d02c025005c1c1e903501c940c4d17080c02140038040e0044c011680350b40003014220001e220352480ca02f045020b110f450000103003610103c40003100160000c03c2484504c0e40c042210000c040f004903881400c00d410840c04807140840c80312552440c03a08d0b0b4580c20001401824000050082d01d0030b81242442c0c100000b52076000c002840f090201c0c901010303662111460401d9588a2005959403486030311400204069022130208001403401382c036112400304a420800d1130507801e41005204082e6240058850034049142e01803020754211048140780c0c0e41d800e4045038100e9601080000b417815883c00441c02d443c2c0b580d480d500c3ca0501e01b1900b03e06200402d4000d520a241101d40b0415001818080c009128520710405000c22240d000d0700c0014a00400300d10b542c000040d100141560f51440000c1c5060016407041240310141401404210801c0c80b10340c019140881 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 891319550 1250 891318300 891318361
    0xf0d021c06090605220b0d0b0903271f090510090513091a092415030d1d031c05030403030b010212090108090f010213050f0306151e04090b 61
    0xa105440c05d40010181d03000e503520808846540e507500014442d54000500ca003103840c107002155507075842411010705042001c012904100c40710340202a000101500001c40c4494a050960300320b070124140384c1c02e101d0809004203c80e00c034111102d40f0400b06d0781d5008285403400e810722a0340007040d60354014040c05c00740c4060120702c902503580748040c84000141001d50300d0001860400b5070155980740c041c800c1101da0f4011715450040207003e86489200d440c41c10842004066495040f00d00010108226030001003c110500b421604050307009003d846001030250703601179003081c0b9107041c8000f19501006020a244e8503100b601c9105c1800e000400b6240e1101310903103070a00454485034100089500003640554040c4044400002210000c1d52a40014400c2002d00c1d134050091502035040105a1a41454009000d0b8017408594200301c039240c0c803c0c03040c00f8807034440315861100c51020a021002c1c075100c600c20121005e024802d819054141406000da0030810100248076060408 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 891320800 1250 891319550 891319579
    0x20f011b080c090d1202011524020a0c12060f0c02030a08010b04050603010b030405010b0d0510150b0426060403170106020105250c020a0906030308010503070303050f0d021c06090605 80
    0x10354134100900c0c0c2042299010048440e0300728050b004071b4880782d1042d809044001030080c100340c0701c541c0c5c1c0c40020b102d000d01741a210008070317a40c0e210624040d00ca43d1807500d00300800d03018420b00000a5000344ad003ca00307842d11141d4007058440984844006910020300700e250664000407150140100038142c0f40b401389400c0029900b0302040c041c2c0145400000041000c00c6002d501103061071078081c0c0000210801403d000e80c49000503690302da03403241003160400c0070190b0888002e060300c80f02d0102d030f410541040b554074203007a000130603c1521030348004070031414082004480d10841c842d548199400300300c130800d0a41c41a041e0300c42d60540e810007003400b000004e44100f86900750900461820b828000c00300031160310030343c5040603400022045020580754030640150050702d0007900d07255010f9030384505050740d50229100c0074000500c240a07120380c26000701e0003401031b4000d82c0405820070010080b52080075540000407502181d44050170042c504071802490000d000488650030f05600c01d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 891322050 1250 891320800 891320809
    0x1f030b01090506180709080d111b01260601180b0304022206180b0d1515090f020903010c0503011a0c01111207020c1c0b07020f011b080c09 61
    0x1802468461a102c0e0000342c00d940700d40750494201e00308501ca803181400c29100180034140180511642406003010329010709008858160302030110300001c0081141d01c481107080c101c00c1c500d60030304100303054141181d120b9400003100b12880c2d0250f13903c40c007070070070800140c40300360040c40702d030f001110100702009411300100503a84c0c0560181d442d06c0340c01c058003144c83e910b0041d05250000a07441c050700450b0700b60b061760350b001186001002c104004405a02049011145a14014000050100c0c0c0c600f01c0e026513001076080d45138986a800a070351301c2c0c050314415900341840ca58021580031900c3d5009240901407139451030a01d080c2989154100301c0c0d03550003080b1922804803101c00005080b50360319400d6200001c0c04604404a50b15907100301240e22500358280c510100510032201c0d00401407810b4072404080f2001c0e800f02d03c1c015a5a0b0380c03580c5001200a01103015400340e2208480615400c3c00780001c2c5003080311100c0d403140c0c4600000303800c000c809844c1c401c003d0b40134000400542c54 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 891323300 1250 891322050 891322073
    0x10e071b030e120c1e0406080a02031207060e0607050901030f0c05030c0901020a0c09020301030203061e042a030b090114090a02221e1b0e0f0112050f1f03 68
    0x2d040c0d6103141000d407500b001c540341840c00c10311542c21254162207a488200402c01d8860b00c0c0204940174050990780da400749660f05200400a50f0682060101c00c08549500300240140c6110b041d02091f0001c00700b43e55424110111111404070740c0020f00c1081035a414415a140201030200c10401c070030001c0001484c2c0d0000500251100700006100d0038641e00800c03182d46041d0780320b1f14003112aa10751405070042d42081c84224000d114800c04240101c203000b800c091010038841346810540c1d215124070034400700c03c954001010111060708102d40300030407003520140d03008030a5034030036080180a1a00b100d1108580e62031100a810510042031804622244400c0d01224024002c407d500d1a43c401d1281404603082a5480c0c0310894411021810030880e030404a41010080c280303411900c4c20608100070034800024604141c60a0203203001d15030410901010b1400c6120084810301240844909440c8620542c40c008104110100b4200b14508402c270725085209446103940e0318400f0320708 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 891324550 1250 891323300 891323327
    0x121814030c06060f01090317130e0106080c0711091f060905031c020309030d0c1e020f040c020f0d030b100504081005060301090210030c170618130605010e071b03 71
    0x14100c0e011320400c1e0b1300c00e2444002440e00642001050400c03015105d506038000790a0990000b0307120b400103074040310103d486040316400e44444980b69200c8480c2c141590020404541d000040006070b1811740b40c1c016000e10031150590007819005a05652483c091580d41c04001005041c4605100c2c6403400b040d00083c200c00c441c80341440286070a016400c600421280d1501841041281c00307000b035004801c2e242c4180201d4803040307042a101040c0c110390090250107074214201a40307040c1c45007480c2d88403808861a500c10388220203001c03052103081004100041c400682c449148070702a00d400c0740e0407068207180703003842e0307140502c0c10900c2e6403909910b410310102695604006a595282074218115440e402003448800346403a1001070010884405020001001e03200c2d041c0c0c1801d1142c8035a030107401d004040000310540030034a8124500c000b012000600034180030103000440d14010349020f04044002c0754400c2c90142801041c0c85040e20310341c01c41d49554a0a500441d401003000304040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 891325800 1250 891324550 891324559
    0xf0f13181d030c0742080a0b090103030e0316060c02030c060a0c0b100816090c08040314090109120b180d080a051e04060608070504110d0903121814030c0606 69
    0x615001303402c6090009503041750702540c4098500115403000c1c000c1601e104600741d2146101a1500c007010812101d108003220b8100030400b0060000c00d01410040f028140014211980b0300b070304c001c903414540540d0788a400810000856001189014400030528000564801d814404100c02c000d2006d000b0300c4000c0c0441e01c0403004280201042854603018101e8001142c00e2004034103078481c0c0341c1580c0e20038090801d10b000d0113161514841c401982c0a2a0903070790301d4040c41001216102c1550200035941d042c080084070004405500148038002140030702d070b902e00d007031401c059001d01c40e58521a0040b0302d0b81100d6220101d007904407070a941c000f000035070001103550790442e8901400714024514407440402c80c082004000180e0081c0083e240788070152007841703507580c0c140000d54880d011a035107802001c3c01480f038402881d0380061450b0b0300a261000304162500280c4013201c0c3d01012500e20390304007900841c2440518a0140d0b086050000207502d088030448040c1e45070427014281601c00d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 891327050 1250 891325800 891325829
    0x72f0f1513091806061502120d0f0603050c0f03061e07050d020304060f0b0303070213050718060809010b060f0304020d0809040f0911060f0f13181d030c07 68
    0xc440050000401402c1140410048441a03040f0700b1030380c1200041c100c90180c00c0c04400f00d0703041c1410405c981d075040d00360002d204680b440101031030680c201c1c25003a00503a5844020013000111030058000940c001c1028000d0701512900340030244160159003400303a0300c21424020b0301d45e904140124010502d021821403a214040200d40c0e0303115501050300900e001000340310501421360b20000f4141040701c404c00140400c50181a101d000d60319000c2d6110240c0368040e42400c03507030b8103d1039100d5003525280c00c0e4180c556100b401071419035000341000603c01403c208081400744201d25542c901103450500f1300090b11020803082c40010300080c020340d034001c0d4010030410500300b0fa41b00600010001d01076249850380300c200034034107414281c0d181b0480181c2c4d42d4190810720b0880d111102c0c4414854540360b03142e1600f1540341d01405101c6586202c00500051008280c41500441804c01002088840c0e070404940744004414140c60390070f07007003080040d880712400140d58048071400c0404501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 891328300 1250 891327050 891327067
    0x50f070303062d1403150a090b090a11041b0324090e100506100c0f020d060b01030506040e07060309030e060301150807170417072f0f15 60
    0xe0290341d8803036103420b421001c0c225107071903000031030f01c50402c200c01c6030100190b59846101c85440802c1c00454240d00101c1e1600800300c800c1c1c030003c0d401008050046207c8804c0d50301c59231024800c40340b100c80b5401240c01c80b001c01446c01403401d00000222428000b10801c021840811010141c5c0d075820300d5a00d00c90403822007180ca0762200035072032041d40d001d01241e5800c42030004d07210035107200999001b800d04080900302e241c4261400740e07101034212840c00c0e41b180410f4922045031081900c007145e02d40c0304000160383d006001070307203584102000b0410300740080015060301e4002c4d207054816410110340e424000c0c40003c03070700d00310741c26450041880c00240c142903c5200700111000c1e04040e0000002c1280300c0c203400240706140ca41e940320381082c0c0ea9800b040714a1802c141e06104191092008500400d0744500c86441c0c209451005525242d595510034060400300c00d80b10840c01c41d01c9179031443c0700007540710072440b242c01580c2c0b131003c085000c80007a003d001c0d11000b004850101044501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 891329550 1250 891328300 891328307
    0x1011060a270318050301020f03150d300206092113030803060a0506070b010905043219032c030703050318060a020c2b0305091f050f0703 60
    0x2844100c101081d05031414042c100201480703401000b08031410b5815100207418141482100d0071900213400d21403d545601c41001c1d00d00350306805480c0d220380040c1c142000f19080424140030344010080714079030317800213600f00340103800c8811510f0195009441085400080132800645e02d10941412080904040c0d50f103100b1805030301c0350440b040d0f03221030b4040204030301000290b0188408464142e5510355a8041004600c180507005111418150041100000b29000f141e04188030302d9582da80c219880d804007040e001601c00301c6c8007080340b4010a4140782c0701849820304450310940089942d06040c2c070094912840005024880038009803145204c3ca801e00c0c1c109071420004007031304c0c44195a410a81c2d070b81d07000003e48943c6042c14a44407941c524044085a880000b2900034040f40180c12003000040c802c88a04000401d00004642c0713140c2405802001106220f83c54007902c4007800018400080540ea4452041803c5081440300d655088015908185c50248507144e480440b868100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 891330800 1250 891329550 891329591
    0xc030c0603140f43020a0611030c0a0c0f02090f041202010b0307050f21100513030c060519060b070308060d0b010b0309070b040b0306040e011b05070c030f0f021011060a 74
    0x101301e806443c41c80321550704e40c0895001407280c00f40405110312030145010506910007030310b81c2100728008111030381c111800f590704d403040c041c010240160902e000e90081480140708440d0000d462112204001c1000051461010015428030081052810803400710341c0d60030b00c41c00b0b003a00c41c3c910b03025240c000d65540c01420303002d08107183c42d421066494403409607452500d00c01281d50035040000061840d00703260b12400400d6056a52000000003580b9134400401015291078003a010010401c2c940c50a81d002e50001040400300c1b06546504506005100050207407005101d00700103d140b41c08910f107450340905454640089903030365150342100070300d03015803a4480b00c12000046400904482d141015501c41c41c400d81d014445500042500c03400c0315189280c0d840c081d0503121b03c0c10040f91040e405011018426114856090b48a0301d82c45c285008007141240c19640040d80b820440c281540000801c2280b0f0070701c9890340954030780003910b074a801411000760907034441c0e24145801c130714a031741c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 891332050 1250 891330800 891330901
    0x90b04230301090f030f0c0c0b0a0507050a1110110309011b050609010605182a0d020309071e0b09012a0c05040e0309030303130c030c0603140f 63
    0x300f01c400900d10b0980c48903c5030002c182c0114603403401d02d61359107002d0100300d940283c3c48161459200c0c10030480001c0ba03040032520b8410410103000940001d07400b000fa26618034062914014a80f140b4020001c0f083c0040c0440d008200300c413219005610400001c3c7c0e03d038000309080030003010030030740c40240c1e060504507805045403140500b807015441040d880003040e1001590081810300c0170b20080c01060340180e480c0c90700c0408201500300000c0310310204180b0726540d5020f852400b2500701002c07060381c0069483e2030a03500907690400400b80011410039800d4044500700c1d40b45842d2078802201405108072443c144030316002075070503a0300c03155a01c80d01200480202061400d40d0708146884040e94010940280c0c9011402107204030000b06682000c00c0040c0118075507600c40e481070302e003141c2010080701d440c20107000c04400251105146805030030b02d5a00001d00c071201103540700c0c043c071002e40351442030100d80048c0460b00108240c0e141040c0d6402c0c9444949a24400c03034002e400d41d40a0b80c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 891333300 1250 891332050 891332053
    0xc0f060130020d1a150d02030d080c13030c08060106090803040b0a0909050c09011805030a0f060204080708101a1503040f060204080313080f030405010c150f0209030d090b042303 78
    0x902d0070504e03a8003201806000c1445451200401801c03e20a1213410311307001075816408803501c281c4c2c062080c00031035413041c80c2c015002d05101402640c529011a2900704880411031407400340014603080240300d00400c014541500e9562400d00019160310641c020b290101a0020b111034401e401500741d20010301c1c82d100c1c10400c510b0221104c0405800260030280082d00d141e0311700209101c1203103107800740c44000b00500ba5103111540c84404059220000f00e456a03002d10000680020502107107000f81301e0b01d0040c001e08804185240d00300c40d80d01e556000d4a44180000555548414441c040c240b010803c1442c1d0ba03842e941403003500d4080640700180103030b000140100b004040840038021344d9034a101c1548555450307000c00c1d500c40301540009021644148820031081d0b21440e4003400f054060709101c201c7c01c48606882c001d03111030042e010f070041d030000b9003003009003000c100030b9003449000e28100c0038007810700011850074402d5204c0c46e10649892401e0300c0c0ca0100c1c0041e407000b0290000d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 891334550 1250 891333300 891333323
    0xf13030c03061e15180e10050402131e0b060d050703020a17010b0f2508070210213201030605060d03080a050a09080c0f060130020d 58
    0x1038020302403d030703008040101400410694406441034020320642d4040340310865903941c14965000ea01e40300340603034840e40300e8591544c2e5251180501880910043d504404640791510740103100300c5140010390b031680d4901e0049007108032002d83e0301e1102009401d20000c2181994400020810300030761050541e598644411b010040380c0550042c1107000c080d840c1c7c181c4015034000c141602420920504210a80c200301000d10404041c000300442810500114800c401480c0311000800016100b00c6480320006000d00a515003500d949440c0c42c082d1a1581e03004840300010590f8a1180420400c03098596040e0b403101d00840804400c115200e0300340b20400c201152401d1050720003032100b0340c0c00c0d0b4a0000400c2c1c2900302a41801c80179500354584001d00d40702c0c000c4950041100400541e0700ca41d85580010004100d14000c00e5080070200007000ba980c030f203030f28050802106a102182d28520400e1605848980c48090040344070720300003445501c00341d40081442040d4802c0300810010020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 891335800 1250 891334550 891334553
    0x51c0c0924230c1507020304060206011a160c051e0121023a0207030c0b1b0309010507080906011404020c0708010204060216060201090308060d05070b0c01240b0f13030c03 75
    0x28005200b440307904144405884655042c7c2c1c807441540101c1005030030010040c003100d0410420355034000b11107041c00303107048500b880582d10903c0c81e010881e00ca10186100304081c0c13030294400d000c0d86540714010380007030521a0010b42034600b02c60f0751100924100c0301201080d0400d5040e190100c0000c0072025604c40c07050145d4004201001c3c3e541c6095241d40e0785521202141e109031807100740c1c0f43d1070744145501161203003929050010447c00d00d01c030035000020100d06005000e10301031103141c1e0002c516030501c00806018141e006103a0245940030b80b004101180c0b00104092100341c09680c01642c90f010241e8440c1403041c140c104040035030000400003401c0e1783c000350182c450040304a01d944096102e480c200c0c00d8821005003d00011011070200c1c0380751804407180442588280129101c059490101e5807054000c0216044c6596480104c40640001107801da160f40e0b508031840d031985d600b0300340382c004036014100b1080b81c5000007080d01e181e000703603003801c3d030f405150064400c00d5400c1e901d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 891337050 1250 891335800 891335803
    0x2190503120403080a080c04050d080304020f100203040902070606090c09060206161d060d051513110f0c211903090309090507051c0c0924230c 63
    0x5481810300900c18810400700c50025081682c1c1070300da1248a503894030038208030444000c50040c01e00c66022004000001d0603950b80c0e042c43c4c4545220f50320321a22480c1c2030040210400d4041e009601400641e082003003040d501100b220151284000b0060f10350085090810061030150850007805181141d125815508200c080084400781d9088440d15076503032450740650b000c0609030601042400e840c0070b000d150021051140307410302401c1c1500b40550001080c0c16500d0039240304000320183c1c60424614180340780010880600c1ca102882121400d80140006110712070344010042d0010034034142281041c0440001c607205500c94402c0e83e4110000102254030000c8910030740c0b00b0f09480216914002d0107400310480e0140c49043c01a4900340c462000740800520a00400108004040c0030030211841614212668800001c0c8005000805400e9800580107015180201410841140400200791640c0c00c420300d0020740690010074641c044021281c68076102c590f000ca00f10118100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 891338300 1250 891337050 891337099
    0x123030a06170a050c0904021206070309050706020d020a08090a080601060806011706032d0d122d090201051e030403090f050102122805030a06090506130b040902 71
    0x2000602a80b07101d102c1259582e40c040141004140b6003100c4041425481c110644690150014204034000500c0082890810b03504440c4980400d50340da00600a2040c00c02150010380954002044820300b180f1019540302c40c240c0005013400000155074000c1d8940001c150f00500584040b1000c950711801d000c0c1c4409021142240028100d28114483c180c543d4099401070b00003a01500c1d000c1d68040041240c4c801d640361001d90b5110242101c203000d0010860520a1200340c0d451092076600d20305071205895291030458280800030301c410003030302441d00e21584040c401c903c000403211003501c0141da25009000c408030000e40c40c1d044550841c2540e1000f144154404e59844031455180c0310610030711b140c0780c0165801070b40140200c1d4800c1c81e0000c02031824030380202040e16002c0c0c103035004040c405480c3c2d600200041c804000e101c040d00c0c2600410b406014003080500c81440e00101089800e130220300e0078600e054903a10364182c0fa4132030f5030001102c0380c0c024007200880504030540c111b0012 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 891339550 1250 891338300 891338309
    0x102040b0d0e06270c10120e0c030316030c02030d211406010c0501090b011205100b0616081e090a09141314030a020115060e0f0123030a06 61
    0x24182480d081c0400300116032503104503041c151910401e021300454240c0348860000c0908a44140c2d4600d200035501c1d00c0300c01501001a5903044542c03103055034039005035200c06406589a900c03951200e68195004402c0e1030000e0f800c0003a10103260940d0400301c03000000500301940501441107000c010550050f804005106501e8422078804000700c000380c100c0303500542c2d440c0c3c01c005110208156600c50b032110b0141900860011400030300c1525500d540e00003c2c0c1c040303580100c2184a900400c2010710010b007000726070300c808000300c1179640701140046c401d800274a074550540201c0001003004500c242c51503c5900100718904c00388907090050558000c0400501c0785041d8000028001064000c0c204640d04040038641252903070004c001e50503044100445140300415010f014061041004d00000300c4d06030f0000c101001103010200d119112600000c04015003035001810702d880d100a448a03205003860618100c07032800711080800a680306210804010000c00d1110b0706980360011000c3e40c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 891340800 1250 891339550 891339577
    0x706080402040e1c0f0827100e2b090501030f110d051501020f070302040932060a06030305180d140a020a351603080c0c0d0b0a051306020307082509090504050a050102040b 75
    0x29003d03101c401300803404008ac2c2c0001401d181b0144002d5200707421130040c0002021003c5040c91003005090308503041208000b03150340d681c00401914000703a05501d050180c00303001410f801d088076400b25440720190302000e40a00e4450004504002d160034010030800e00a0011502d00c3c00729104481a640f07038081001c82911031240414004411845002c086a41c140c8500d4500680d00b5051601d9580c0d00c01e01560001401e0030002c0441c805503000d500041ca1b100c00f82011064620400c4844001600304a00e251101e030540f885440e5070740000d611101ca29902c4958001886442614141641c030340c41540030640c0000200300004070015000a403030360801c0ea0003030342660085c061154580c24010308418066008038028a2060b0b002039000000c038841442000480d4444200740e0340701b0f13a40328fc0050903c80812a00c0914510041ca100c19000300b075021180400100030288081c40c041c0d21802c0356501c003c2020803508009a0040f254000003e64445603101c10440c607540106200c41c5e2003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 891342050 1250 891340800 891340843
    0x4170a0318080d0c0c050d0c03120201291203211b190203070c0f06110d02061f24080115020706080402040e1c0f0827100e 54
    0x3540c4441c01c010250b41c1000000d101030f50180c0002c0b1045864103006441a14a58001089640300c2940340345c1c07014000c02a00e10550300d1494050265031140c02c5481c21649440c44c80c501a141d04e4100c940c545521a45da0103001c41d6200014244444c071101c004014400003440303102000c007404103480c2071148154407030803d81c0d85111004202491007071001c2034034020485898500c4001000808611444c0b04036400d01c520f42da41d0a204031010f41100708420701901d800c02030168000021505207280341c000d00f5400c05003820107580e80a0180681d1038800e240c8800c4510201c2450325000107008c0b1411081c0911241120080d4003082c0e131044200141400001041c00e07e8010303000e402054056000b00b0f081c0b4034040c8212040304001e07000300e920640710041c60041402c1080000c549588030303252065078140d4844042c2141522844031004d00c0b440b40d040111680c0d0319690500c0030070000289c04850480c14842c681041416054440100d240200f1500c42d071100042403500c428000c0c5c1283c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 891343300 1250 891342050 891342077
    0x1050a0c080919080c030c07090c0e181513051e0403020615061c06050a050409212a0b070309080d0f02130905150a030807120504170a03 60
    0x410250031500b018a03540554a200f0001803842d00d000c0042d40540500350415440c10400c1d800d641c04011861200c0d0b100d1b00c4140002d0003540320742141d039101810302c00341042101700401c0d0b5000c04442d00220560b816400121800c0300041d01504112008040c10740901941103410003c10080d911400800d90404054400c05251265a4000c13030b09a0014031507540c0300010306610703140554500b42c2140f4140034590b25103a070f0f4a15409032807011900030031a5403c15082c403d03d046241d112611960a040a41000ca040e60b1a104100c4900d000f56480348042e55405039803030503103500c00e05070403269a0b99040c004112004c65584861140852074843d4685c1e200441c00c0d01d102c808098403600d01004190b040e64103e174000d40e0070a800c007034007609000c00c510140d40c0900d210b600c40c0307180640315400c00400135012441003002060403292101d201c4d0460702c50100c2c900800d90010300074203246070352510307150140081e10018403180b40300004000321200416200d004606048010586424203000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 891344550 1250 891343300 891343307
    0x1020409050a0b101205060d02090106020105180d05040b2d120c0a17190606031e140408130302100f120b010f1209062c0105060a0302120316030201050a0c 68
    0x800c41805980c0c5d5850015008000342c0082502030403443d80f103949010500c00603280e244400c1d0007000390350000159403408a00c10820480d1550700d143c20341c0c102c482503070005a0070074155416a6003981c001354440120745458010b140d00400d04201c28104644004890040768005002040d007041c0d81c1c1e049070b242c02c40000040d0260642600225103075400c420511006000001e500500f01c50348001900c003492454800c440300c44d040000025140c800303c0750307080e442407107246096400d01400c00001d102e9808031340c44104041c1005051210009407411510403c07603000c03002d560024016201722540c80d50250400b6402d1400c100880c040a0b80240210b1061162842c026010384440e0404a0411411103401a0a40c29840d41c295100102808100c0901c40c241c010b1070484d050026040b01c1e00c10000b00d02e10f0701005404268144001c0210941307035882030070308495040d030300100035009840901d803d50081c4054145091001c00038402450742c1504442e008030184d1004200700040200200c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 891345800 1250 891344550 891344569
    0x51801060903110102010b130e071d01090b150c03190302180402030702011d010e2b05090103020f0304030305010e0a14040816020a0b090315070f03090804050301020409050a0b 77
    0x1501058800c0341c104003045001d1240c00d80600144000074410b0080d5000514400220940c0d00c915681c46c8210b041140081003010b010f031651111b98080d010791414158880907050069207078560b1038440d01c10a98840c1c0a014100d059204c100540780c0c1418201143e0340e41003039202c182d00b50031054000d0314050083c0b084501d02c1c2540d21540d02ca204a803003d00010350f101030410011596942d804040c0720114221401c000c2d40c8a10010481c0749894810324508400000d00604100c40f030004106001d0082c00004450201070800d1074949440a0040c0c009009440014200e00350020800c420903615900460507505540024030b09911141e08500440d64158444400c280480d40070034042094800900110290141c1d074900f0000349038041880242184c1c4402c1ca17014010441892130b00e02401004900e201088800d41e152070700d4580242880703e612031141c00e01d5902c4030300400384440340e01220003802000c1d000307541e00c039612170704000107010031100b80c41c1c81c5290801e05103442c0f1f084039a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 891347050 1250 891345800 891345809
    0x14030c0c1f03091b0b040807050f100804050307080705010e0106230108252d0c1101030e060106230301050609090a0e0105270a120c080904090c051801 66
    0x250868100340c1c034150001c042c1c2c1d090a80d50042c120071440c43c440400e03441d10300038220112115072184c0ca4a440986040c10311741046100b00340340180b410903600d408500700c1c441190751800082e5511103040540c10341c424000080c0022400203031140c288030054000f1149410900003c0050304e50f15070420118070b42d107101100d02c101c0e600603504003543c403650165800c2464581d000d542078192380c6142600000403003085c03000c1907802c41d038002550480c1e03031072020310404034009000e240010f600c010008050301400030801c003014100d2882c03d034800c2d0701444400b4007000c22500a96103c100103010602802c0d00b408100750082e804810b08508c40054034100d50028043c141008400000c2100b800303402049242d40390780d01e0340b181950180900501d40100c0ca40201156840c11142c0d9400000141e2412051903a02071011000059142103000024503100d19084036221030034603100c0524851405142e5009040c038240f10306000c442c1e0001401c40b0b03011146007018124140d40c5d6070071a40d0900c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 891348300 1250 891347050 891347089
    0xd0203040b090d050414041e060503060c040513050a090b0117070b0f0d0504140a0308011409070807080c07060509150f3916110301021204060c02010914030c0c 70
    0x104040e8081c00d01150f4282e500410118503000105d0441d00e840c215804040e41158449e2000c1049040c28001c0940220761f0442131450310b8100710100c0d0503044203034081441c040e580c1d000641f8000302381d40003e4404d40e04c50000621541d44059146401d40015510031160090900024180d05804110b964241e840d5441030304269804007503400a000041094131580c1c110020300326551828031200d82e0040c400d8030b402005504000c0085074803800c001c1820300a4007600244082150001001503111659280840c80340d56000ca0003406402031043c0281544d0800e400d01c403425030041030561140414082400891f0380300c482030b40064109442c0940350950306141005070181400c500d840709071444402820480385042180207543c44131203068401d01042e5140707003c20034a1030300c0240500d0214000d40c14180040c117094040b85000d00010190f03039079a046c3e4070f0090b000717410440f04650881c0101007020b1035010029142c0d44501000d04060180041d0000c0d80d2424502c4000502014032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 891349550 1250 891348300 891348307
    0x17031003060633021e030d0501050604050f0f040e0d0203190804030f0c0305040b0313150213140312161a2e0e010f030203010f0b061606020409020d0203040b090d05 72
    0x410603c506082080140c0460044814041001030a000d5141202c110b1000440e41c07240f42c800c2d540d04032a01030b0081403240340704100c1085655661a07110780c0052080301e055800d00740410000b80108000c3d201070809024030028080000d4010019043c81c0103800e02004000e040e88100302d96013042140e0060109004080e0038160720310800e80b845000e48682442da26140c2c888000001e01c4c1c00846010700500e441024a50411910840a95440000400540c20040d0000c10b5561141441c05088501240c4082c10039541d074040002a008440c54681555100c0206107642d0721031241003c1541d55440c07016a62b94a0002802c80a10842030401c03520f10308021600c1107070a52060881c0c0300402c007520140400c5822400108031300074000122086005c5181d8414142580c040000112080c1e2a140390205542c0b41c0c9001c448020744000860000740c0d81c40c3c60404001c2c025608200000303840030400a4052015900a60080c0c0c06a07103580a941d46a5801b15590760b041c5448800003041072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 891350800 1250 891349550 891349619
    0xb131e0209180a0822090c18061b05010b060d02030105151303080c0c1801080f1501030206070309080a030302030a0615120506010e0306040804060f08071407170310030606 75
    0xc00509003c9404c82c1710300706240111381c42d0f80007984894002c0b200040c2d917142135001294014040e91111001e1416001d103482c60000050900a0715a01007000406002e4175002008000c0d4000c0c002c07001c0043c155911480300b24071010003500301740541030040d0500c044005051200400360344452281c00c01c511190741c155559001c090300014404001c5101c0c0c204020080e50b9005030102d1207200242d0412407a614200b184e0b4035280700e00c080e4580c150011003c0d05030301d0742c0112246040daa010307503800d5519130a070b290840704441302e03038000009401090845000c2540c5500114091388000300e0a111003a00d41791140c15217252160b0361408240400d01d0ba4101010381c3d00010b601040c1410040f540304980300100e030401c0c400300c0341128042d6000074140003464200348104060038031490180154507200707102620420740e103070366408130701c002042d844100102d00008800c7c403044210025240c1c00d150300c8a00010500c0d0004a500c04d04105022070340c02d054000101d543d00301d090b0f081d902030295 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 891352050 1250 891350800 891350813
    0x12030a0f05040e04110f04020702150304020a1e06200d0806030309120f0f0105040206040603051b07030c140105100e040c17060403020c011b0b131e0209180a 69
    0x88240032003400024000000c2e000300080610384140c0c001d003251080e0055400400071700b14511400d2522481c81805000096224250300035005901030803480d503240c40c1c50002460034078080c1e0003004451f1050007608140307140103d050049450b10380782c0e106030140d4a52440c500300e00c1212011925801030006030395492040307403013076080500170f825030b440d00c04204082620051aa5800c030400d50002454140c00c050800400c0760703407504227008020070b0410b41c1c00100c03d44150300c0b03011308040d10347d030201d02c80002814052465130154078070f45a603000b0500c0e025111400340c036826100c0d2402800258400e0006004241c0300360040341130242401d04000e140156810094000d903500c0c00309500102e145003009800c480030046c035200030105460f0500d40282390103000c4d89802d0411108001c854010440985000c07001e070340c440611201a92120042000000c0441c2d01521300f40c500040040542860f1902d90314960090700c580c0e5007540c4540400301c40d081c40c40300040302680040d01c4240400c0d40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 891353300 1250 891352050 891352067
    0x60e011d0c0117130606150e0a09060e0408030a140f04120e0307120302070b0f04171b1002240709080309060a03020a0516080405041a18150901031202010b12030a 71
    0x8500d2000400c1c6e900c9010745814240c00c003072000081262050840140d20f4403010b503500034401240c0600043d818012040080079004e007005040f0710000c00070580301e242640040d40c038840c0c1c0301601b110f649408070040c4400241514203543e1161185c1429500d1071141d03003c1c1d51054006130040000714613180510300f49000b0094160214015460041820707080d410061402c2509914019100c90130800f80e04446280442805a240e02c40a024990340c040140701c644011002c88010004421142c1c041c0d00784020204d0745036003e00c0d5006100001e12a00751158001d00e07056580c0041c07142c4640ca496a82c1c80340204680d17000382c0510045401c248250000d204000c294a01142000410900c144c0301c02a144022180d4070b401007410300c100e062502c10026881c44440f41c45138106c03880c00200c0d0030b03022450103513a132075105500081e20752031442d40030f50600e1074050428000d9603560700b82450b1019000e0310210040d401e000c0d0610a41c9002d8080c1d01d0100f022801a41c9040a11202030341d8508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 891354550 1250 891353300 891353303
    0x201f1a010810090509030d0608031809060d0f060504031107060e06180a030507081902090411060c10020c12040b180a03020402070b0a1409031204060e011d0c011713 72
    0x142c0c8490301107001102d034083e140c001c1c1d0180c8025515145800a4542600c200b41c11045043e481441403902c111b1071005c04141e040e2040d10f0514864449902290320140b00c4038016000b4610310440c8401c01041c0c2d80b0407403080b8000e03a20108072a582420803030f107840c45403240b000095504001c402c01c031304d4441d0081c001a201441900038502a000c0030403500e41866000780c41c1034100f02c0c02000308850500800c65145101c08040035540c400b9800140c00c5200904080c140c80301c04c520035502c0392140c070100c4a044444504031740c4507507201e8032000043e45c080340400c4180e004224a51032600b1092050300c003034031660322016041c0245504110b808283c4808000c4d800780e4507480000161f1514801008510301a90b0b10040520704a03003000107481c0d0203003020050071a81c504100c02030700f0100a540f090403d000d010241030702c450030804087c3c0f441142807240c95282998444455050286519071244a1400c0e0b500d884124001900e10481c090485a9442714000c00035500e400507142440f01079 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 891355800 1250 891354550 891354571
    0x60f0e030a0506070c1401050f0a0213031b1701090f2603010b07061508121e0f03040c080102030c19110f030d0e0106140105070201201f1a0108 63
    0x507100c0b621403501d000000d03140c45020803441401e500c10300a243e1a00d10043e07949000030303c19030a0040601000c0c1c3c00040851b58401e43c081a43e09041c0070080b4144000e41c6c01c40550001d103284200640140003d501c500b0300070705411070b6011042c5c44180107840d8a2600719100e40c2e0114041d44450618044c000b580502c1044064443c40e42e074000200590f000e00121400316840d00402d00e0b0420494030194440c5580c110203003020008000c000514142004a403005903071600c1c55041c0304202100c1c2c42252000340b080c04500d00d10800e0301d0b803020f144280d002e4850f4140b001c1d076401c078080c202d11050b145403101c141d0400401c1a840c07041034015a800c8114542035499072607164503d4203106404010801a400001d0176201c3e14100d40507101c460240e21f4000c200e4103140024281e002c0c600d924400d81407041c0400c0c01c60a680c00b4a0340802103066580040754040010301c0f4441c0c0314805088140c840d05403004038102e41c012103100f845882301c400c4840c0400880d500c001500d070914024a16601c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 891357050 1250 891355800 891355813
    0x215070803011e0608060a0603020a09051e030111040e1b0f0c06010603060803131e080312011e03080d0b060c031204050c18010e06010207031707060b060301060f0e03 73
    0x34000200450081c499469008040c082c003d0b5003a0115030203a000c542000041014071100f0355400c0f8407081200c40a040040c0d50b0120f015080d04c0c21400c90f48520392105200800516142300c09101d4414a40110020050022401e41031102402540030350a100055180001d018100c0003101d850102c0c0349180b86414070f00c0c0d850400c0750540c800980d0120980185004011242e010300580d40a030611002031418401c00500030038000501e0300ca82858074088008840c1800034100440000d485000162503850910405280d2454002e118000c08200c8810000c8000c8145c425050140c036445905c1e10302c1c002040c04500d026000003925158080400c01200f0030b0b85404000500d9051500c00080d281480c0030f0500505294407100c090b03000b2241850002c003c21518034030a4191000ba100b031801715220134004034602100394000400307400030050600800100722000c1d08010b4424034062191103130290038032006000a10996004c41e41c2a00e0f041441c90003500c543c510100050102c401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 891358300 1250 891357050 891357053
    0x3050903070f090b040b0901081b040902060a0504301410050901150510080403080907030b07110118080a2303041103100b0f060901020a211107050d021507 68
    0x102c40815600030f211040c2d8408410000d42450b02580b640450126038820141d0304d031485081d140c80e00080300c025035905800360580140e40e42d41c0300100030383c2c015040a85421058070041c010f07501a004041b007500c02c140050501d00d09200d10807020607540c0007040d01d042d0f00e9664a840d07640e4214945402c07030142e08444003044803a0702c1620300c500381900000c140754030808400d51210790b0076044203010f2180034400c40c1190390407130411608a80d16280c011070513a21040348505003452508014040b2341d60500b4001c861780e2000c60581d10350b548600030801e00c8101e0403140f10200e98108018200c200601c80318500d103004100c15908203165040d01d102d5862a107174840b041d54070484003202c050311404503031041d50a017002820001c40e4810010482c121001c4001784c444258941c40c2c07489148005112202c1c2d034401e010400f101030340701842d081c4006221348a4034450010082d04130000d410034610356000000080d110381103c10203481040304c0507480d000e01c00441c180c02001e03105200304009640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 891359550 1250 891358300 891358319
    0x30306010219110d050102091003020a0e0114250f0c05120f1015030c0e0a05070914060702010e100c05061e06040b0303071e0b06040525030e07060e0405090102160305090307 76
    0x3542d0352552b0707401070b9038030f120050191000c410300910314100154680c00c281600c900c03204a070741c00020403070f501e0440081841e00000c023403040c6000405990f0302001ca5020000f0130002c1c00c007900c00440e5038010725090545a41e664240c403030103007a689e0f40f112107405040030540d03100a074101528851f6800039501c0c5c0e210f040000303889a00450140c802d24040000c008414407460350000703c0c520b01501100d25149050702240c44015165215130400142c039011607001314000c10040e0009003c6411040c000b901c0a4034072820f2000c1680c02d405007a001a202c8003403101c6c2010346004028100c5100d441e04000e000041000c025041c1d050f11003000214040303568568a06640713502030903c0350b1070101c5d6290040307940c40041e0409005905000a000001c603018640c14412480740f0f1030b041b483c80b1219011809801245042280d0303010360300c400b19045034403850750804c2c01010f85082c0450b4580c0c105141c203d1150104401d500c0010070b4004c00000d215070000d100703511004048641564070f416401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 891360800 1250 891359550 891359569
    0x6060c020d200604230a06021209041d100e16061808120406230f0703030f0e1e0c01020715020a0506250305040b01051302040314030306010219110d05010209 69
    0x301252084805400032281c502c5c204031403500350960740840b28500e8803a01035980c01415100603c40000451140c2c3c0c5520350b42c5c0a1451b60101181c0c51042c040c0125003113480e045103000b25402036007056244040c0e24070001d8a0304007a140491056011850054101c6030200000801400c0350344140c0d0016608404014115110943e1000c141c0e942c0c0ca040000340403d0b5404991a038030502140d540c2c0682c0f050001a03500d0301108141c0740d41d40720801d140c120001e12001c601c1141f00c900d440c03030a02c49050009824551450025607507041800c80220b2180e46591606046005034800c2d070007441219910000e0030100c2c1c20900490707126090741c0e5030b080c4c100101140c1c40c100400c010b040d020f1414800e16041c40103094103040403c198107107a01e4a6003440f105002e82800741c420701c2076546940d01594119001075406c500240f082c00103880e00c4070348a50068400c94010f200d00001e000b81c40a280c08608a140d81c010a04440c4414000502240345034052064500395800e000c100b0468072001440b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 891362050 1250 891360800 891360809
    0x90302060106170c0403030f0c0501110c010c030b030309010c1e0302061009140105010e030f01020f03040209090d02100507050904090b01052106151504090b0406060c020d200604 78
    0x340c4410360500c40001c04990303107a003a0700d8400440074107002081103020100c0381600e4040c58900c10096886030141c5c0e43c00c603158001049507181940c5800c2041000024112001c0070308001d200700b1161401c120107a8101003182039054100f04000d4049600500000c0307880d034842c0385814802c115050354481d011031900c030f05a02582112081051002e808000031000c1c141010003004034a43e00a6804100b81e0140125418405021102039040d9070405c050b050030b4032010001e659484682e4503d03003c54006a81c100e00819900c0042485550085440c3c050015682c0c0105510f0002c02d5042e07010340302c06090182031200c20060701511b52690b00414100500540d51141c01c0c1d4034180c180525100540b028100300b604000c403902041e48003050751900280c1140056640064110001d821454928102c82c40c04400060000789803c55402414000390100d4081114554405098400307010a2000951203103490300140001000d685101e030701c1e50a2420014680c00341103002c140785601c140c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 891363300 1250 891362050 891362053
    0x30301050103181101110304170c04150b0703030213180e0c0301270515010f0602190c050613081207061512081c0504060603062313030201020c01090302 67
    0x5020650700341c0100403610f00001411154050030340c0350101e18401e42003e0320b04002d440e04070110210420403d0b10054200019443c10f41440c68008070754850031488418095400c0c00c0c0c1081d020f00751006a18203e8080c203030700501d820700d01da60440096000c15062650171410401c0415000f00c0c0c820700102d12001c1d01e0001030000c1e40c203038a01d8649002085200e1103607042c8407501c040501d40d03071011038080041e841c044241081915100741442007116003958a14014400082d0031841007002500311181031302500d0007840b4140b118004100c4060f00905141000e410801c0700e42403040c01031a00c00511000c1100340f944400c03076107013080070001d1403061007280881c1c040184903035031180718200c0f04144070650400386021902c00340c0358401c81000d0651100441c20b45a10520f20000d12000000705070100201c0c946072501f64000c01a500003520710318a0000403e035000d008482e80d003504030204500388007036039400507648880114001c040341155002e0203d1207403001c0034050b41c18540e100c1d40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 891364550 1250 891363300 891363307
    0x16050c0115090b091302100f0c0203060a05040b09060403051c02070c0f050406080a050d0503070c121707050a0c080a02030705010f06050f03061501030b04140a0603030f0201020a0e0f030109021203 86
    0xb048025a00548170404034465148203000503070702d0201812514802d0f003015506645a51001d85208070341e52350294060103030f10204200b44980c0c0d4400303440740b84680d4000301603403220380660395550b50444004012450800c0350030520f5450040310400a94040405440c00c2090307034070769402c0c1ca050790010a001e404658103219510780303030050901400c0400002d0000d070010744c03240ea0307903100156a4a014001c000000c2090244a11400c1c180c458109001583c00900c0da0700c024030201040d4464565500321030081074440d40f140c002c40c3c0c100a020341e20b00001051136115010540d00000305101544010404c49000800a000c1c4611001102000049039890082070010300170003840d1492094105100700295040c42c1c981c100402c00d001c0c64001040001ca0010500500007121483c500313106040422604d02d40640007041075a10035640c0d050a8801c84c88107070700340d0289085410100380350313000042c3d06003809200200021401030010800803969004140071712003406c151030041c0c1000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 891365800 1250 891364550 891364571
    0x6090402060c0f2a1305150d050307060510350d08060f0f01050d09020f0a090c09050109120605190c110c010801061209021201020307050c070e16050c011509 69
    0x20040703a00c58600c09014094191300000000300f41d12201c0c0c0e1420344050740c40b00825031041a44005910303848000e071600800c040c003420100e90741d420011040ba8428103000000b04051183c0c4440c00413282c0b00490203240c402c075201c000d051250a000309154105444290f0400403070100240001c800c903030f032500212800e0840c10300118210001c100c0d030003410018441092640d01008031142d10408620004011000b8400500d0b4215124506540305500075004500c0302d100790301c0f005904a640d04c4200c511940c48005440204040c890745908660031082c0fa000b01c0e00c107400455110814849454000788e551511000305c400c00003412740010300c80c2d03004002c04070042010300340c050310034241856590300d45880100103090301e41c400764503551944001000c41d1144a501610350103208001e541342c0c80c0080004105803c00f0021482e54400c82c0c0c0005810070b483e00d44940182261141d03030b645280003140c1070302c03154001c4000884942d03035000908400c1203c050202d014101146001c50050100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 891366906 1106 891365800 891365833
    0x110717070e070e03030f04090f110901032703020d020f0102030912160506040605100b21070c050703030f1403070c060b03010b0409080c0d1706090402060c0f 69
    0x109586499000c0c6c04050030554450300410461b0a0700095814142d607a0b0122500d0108020040b0320101e502c290000c59200c00811107656010400d03211461419407408015001030b0040010801e80b903038140306c1c1c900c4e0340400c00002d60640c141029005c0d11003a4106111071383e6100001d140b00300711080340c5001703119034100c015038101d4600790504c5400707003004031001d02c40541a00e0004c10842c070840d040e550510030b4094032a16581805d1a2a030280030050805002d001d01608840d002a100f00f1080c0084c520a9568084511080c00003400340b240303407404841c005a040c800c2000d000d40c020320f0001955003001d0082101a810404240101005c2015a0300103051200030000d001914004200391039980701245c0075140354143c101d610760707085008400445190004100e0314580703030328181c5e040b41c001001e0034600300c01526818502791070013034210b282d501f0007100f103d007032442d = true := by decide +kernel

theorem cover : BRFrame.Cov 891187050 891366906 := by
  have h0 := BRFrame.cov_init 891187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 891187050 ≤ n) (h2 : n < 891366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
