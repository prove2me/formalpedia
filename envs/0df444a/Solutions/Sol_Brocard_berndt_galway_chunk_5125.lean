-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5125
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:49:43.229576+00:00
-- url     : https://prove2.me/submissions/f65de7ca-36de-4406-9fc1-a7cf394b4967

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 921582733 ≤ n < 921762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 921583983 1250 921582733 921582757
    0x2070309050f0f09060d0c0806010915080c0d030c050a1203050a0608071d041a0c0904060e0f01090b040e031b010b030616031503140c010e04020f030606030615 70
    0x100200242e0900d00041003204405a90081d504821840400c1900b440540498019000c100d1b07810b0901c404170079408094050714050b95410350b9900e88940190a47d00c0145164441d9410000350120f00011580440800078020307007426001e07510113a4904001030008e503450b0045c0c010310000039986010aa02048054400040303d08010744c05900f02c429a0700880100d500c0960140103143c01d0705511241c0c8107469039030800340d0f6258901000480c01c13114485450720103090a00c252106418090119114151001c000e8250346000390003405106840300e0360305415100061010080070380020390120000b5001103400d01e050f400c4945141d008405c001224400520480040e40d400e0040f080e42c81401c03002044a81460a100c00c0000c038070b07110781c0701410341c1c1e880132203010440f4606943c000c58001c421080030b24440040c25803078844401405002416071020700359586442d2003941c0c000c6450f40f0200b81590f6400e0203000095001601300c5030700c0031009480a0340e01c4010001440e04007a00c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 921585233 1250 921583983 921583997
    0x1311040f1119030608070b190203040e0106020304030b1005101419030209090f06010206131e06050708010f0b12040c0506071202010c02010902090f042121020901050f0d0b04020703 79
    0x120758018100d41382a00305610980108404100d00c04184003507407001601c0c4464144014040e200a92a41c4030b951b000c04205c007251000000c0341c64010000d0f00440b40034001130301c0c15990708440c0f98500c80d62405030545c070882d02c0880214030340c4900410721144003150394a92510703540e21003ca0744036440e0303038844c40001d40004200c00340d07003003209920ba0050340b00c40640c2c1c40d030705103140003070f48a0340300800f004010003400e140f0034288050440384611504a000302000a4181410690081c010849140d40854000000000c1c40c403500600b480454810300348003814500b030100550107265002c0c0095848200c07805010030150381d200010840c00384240c4490000803651440a42540c5551982e08251b915001301070025132100031405a011840b02e014010f41d9a61b0315000380841c0b08200d11000710b81d622100c03405c0c002e8001c070751182c002003112a445982e1404051180c107074400e2940f03280c00650300344195080c03e2003100140001c0700c41081c1c041104132154000c90101d0b00480c00603800034100e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 921586483 1250 921585233 921585277
    0x1d0604060b0d06030213140f1021110d02032a030607051308030a080606031e10050102070b1317070b07110901090905070528080c03061311040f11 64
    0x55007250f0910000b15004c0c070400c103141903800c00c0344000030038038195238541d2000622880b101a0150020f0020603215007880b18810b1041341c4400c40b454822a01e0102620941800c0c4c0380c40a40000c490780d000300204820500074840511030031704001a00c5040360040c002806680c1c00340840c1e40724404c950741d09500c44900e03841302c03000702c2080c2d13224840d2a0402c02c2503201042e44041c18952100081d0b501c0c0f40c0d240c5403050f85400028481042d820203020b031606216841d00106c0c500d41c100c4009a00700c5184980b42c80c0c641110748100f40c681c2c0880303400580c0800403940d4034a110f40e8030400f050140c800e605d5807106e021200e80c0c0602030803941008211b607400c1389454225043c46c050309000108112502e4203940da255114070364004d803445000d242484042c100c0c41e07000c1c2940c22440312004850807591306d500f0250745411580f10036229000c2c4c0d4002175400d41420303804040d5650407001800240f00d03c1002d0000a0242c208007000d80c80d102c601040000b181d200040c81414003031030900c414184 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 921587733 1250 921586483 921586489
    0xe0307120504060504090908250605090d0e04051003170403060c2a081c05040605070806061206060d020f09010807090f1a040503070605040e09071d0604060b0d060302 73
    0xa1461031100034003005000038030095901c60107803400e5603448000003c42d000346082000c80c40c02000600640d00310295014211403020710300500e070840c0300311418003031a15041c84c103c0c2c40e02980190000040d0300038070340d6400c0e4a01500540e0300301c0d10040010701c00e642c0301d03202c112903508000070560030100c00003820020011a849000e4100d2443c0c644607142c40c8850001c04c090141d54484c003d5121a03031400f250500ca024401ca03941c03070042450100007155410356000261400f2107055030640d180c00b000540250240141a110758030040a103454190351090200c0c0702280a4170b0b40317400000501104284c91041d10090400541e452882a01d801d102d000050450070700800d00010854500d0040140300c0541421100f0b40303004a04003203955400d81f410b07000c1801036910151741807140030000107040d81c0000041003905c46010000c82c065944441203640c0d4085032250741000000c000f640003071100d90b031010342c2d00600020404200d40e07545170031081c825000303102e80c0c0710030947e07403801041140b2b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 921588983 1250 921587733 921587753
    0x1503140a0b0f010b0406031518090c050d081e1603050c1c0503070f030906090f05190506010509130f03030e0d03140c1e030112030809010b0a05040f020d0e0307 70
    0x600b4001c6030560406140f00d6090140381701d020149a1601d414005803c40200030768060811500311303c07c2c82012140c030001801040f402610101c001c1c1001240906105528006a581010b942468081d05542d01c80340d891241104508591044c0b2194906041c00340c0440c0c1c0c076900a40e507854071031180000160414403249048646100701c84040840140c120b8107980d400801810441c004070942602a800b90141e82e0008000c585842c00f50300411040d181c00c01785482c0254116880c10612010280e1100c071351503800740c02544003600400252030840201c5512848108030000c03245d0075a075905400b030181c440d00701c000c00d0310340280c00100c2100f04a2950130082c10b24003031152140c402031340300380d0080152000c9445840001e990b091460910741580421811001c890390b21340c1d582c031090102d0903503258100e0009140034003040c0d4030181406100040c40c0c00400000b1082d00c0c0c282008010a40c801000590a40900211114800c54402c0c640a802c40c1000766544426601d0060000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 921590233 1250 921588983 921588991
    0x30f0d06060e0d0822080d030c0f0507080d0b060d060509070f1b1a010b030f01150210092303040e102102131a030c0102030f0a031503140a0b 62
    0x2107281c01c0e4007060303990343ca40302901c0d198010442c3c036a910704030369901c1100c0140100e0324061001844002034200c1e00024101c0706143c150340c0c10030a50f025501c0407070301440514000d40c00100305010050211381c58a00825440301d41c8038000540f008400b000c54001c1e04911240080c85a88042c200014100160090381c0315025180040034603a00340d0b8040c16151072000c51a50121015801e0006c1121410160120104010202d4143c0d0717940c11058000d03038011030351420034041100001a80200e54002c0c001c1c0c07103540b0f070003510b8109030307450f0800c0080c0f03220841a520b40c231005c01c101010160651781da0a88050b00d00c091940d55090004140c0400c60152242c1a000250350742013021580281c040c00000740052300040801c00c5900000e098860140412008649004581d000b83c0d000e060301c3c5404550300b88e003660348130600c11005903164080c4504403500c1034401c00c5904800d506c207900800b2440041c40f40396030300d15182d45481c02144010b46040c0310b5a8840c00000302030240c0a03455680c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 921591483 1250 921590233 921590237
    0x460606060e0607081305090f1e100902030702160605040509100b0714010f020316080a0603030206060112020d060806191e05070203221805060a06051b030f0d0606 71
    0x6010030080c080b904030b202d07080c0007802040c40414540540d10480e806007008104c001c040d0401402c4c44520004500c0e0280d84010f00b08a4500b10311100040325400d45110380020528507400d01e10f40050f0700060f42c00280f40c2c60450080d0041a5071011039070f1301039406807100c3c1c0d85440c0c4542c02c00341030040c09400074100c000b0b180401c03141000003036001403c42c0d441d6640410120288040c1c00d40c0a4050030740e06041c02e01090010081201a41c0700c00a0841419003940e03070300106844080d8402c0031103210f4000075005070000000609130354050542da0003400d03502c0c9001440d10314030403080d40849400307412040c102e4003c90140040004d1850004091481e902801c2000a0490300d090504079502441c640340c00780c4440000d5100350007403094591000c802201388016000850051100d412107002d003520038207550001030304000240c800c440c4507010250002c1041801e0102c10b940981200c0c2ca0280009280486543c4010040c0054030020031640f0302c460700c0b10552054442541e4054000c001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 921592733 1250 921591483 921591497
    0x70e0409080d39120c08060103113009030a0831050622021c050f03040929130b060c030c0f100c0246060606 48
    0x3010940c140d0448160580b44000021030200281071020f20350550030015060741446408003100b1a5041611034401100c1d07902d4583c40203808038903100700d503070501200c00040d03542e07400900345502941c0243c8890441030080307800c102c000080300100420001d09c0302d202e050301078459031580c1c001d0304c1e5040c2c1002604000d1824884000750040483c2001400c00d14000a0003d8003124080103101c260324945410586116284080c148180c9d00c0d542a01c0d0a0014007070f9038141300d441b6003003400100d029640107203c01898100f0700c200c510129100e82c0180c40c00c2c010a1842003407480c040005100a00080c40c2c0400ca4840fa02041c1d0501080704828142e600441003065016542c1c481c15000506464400041c10045130008503107a80200c050b410000c0c440002c0040c030205000502000054640301114265040324002c3e005444070380307100c100503038020080715449607141190b20201c4208400c60161004040003007051180003c04015a08030240c10001e0030700c8114001c80020303020700d0800700c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 921593983 1250 921592733 921592751
    0x30408070f050607030f201b01050f1606140f090c0102120415020f01230c0403020a0e0903090405160f0207050a090b1314180606060d0207031b0605070e04 68
    0x2d40c0d948075588004082060703440e11429100d01030350030020425107403080083c6070500c1c01520307035a841003000708508c0140703202e0301003100b584200c08403407060410f03200c1641440d0306011301d030b1901d41040100301c2d07155444192040141480502d42480307500d500074111400e003020541c040c01e003211242800e0454002e00040703200328600c502114115400ca03c110780c5d460706440d00c224100f8004500b050180d508001482060180c00041c800307001c060182c80304c00f940ca80003800c0315203104512002b9000310b4a00700401c03a40c1da03003820840d40041d008082d64a05146480020209d4100b103031080b40c1410200c0f00301ea03805a00c90080c0f1185d0b65540001c00307000f030400d000254440058882e54403c02d0b111a00c0d402240c8861400340100c4400071000d00c4000300c0401c41d200c424204541200c0d254683d604030520102001540a004550242020346000c0d01c42c2c00c2c69029510164060341403001c501001440709410312230701141103004440c0012941003165004004d000b5500c10907105e54100300c208 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 921595233 1250 921593983 921593989
    0xd0b090a05101205150106030b0319050a110d080403030206070e090405061605070b010f1719032003070b06040f1a0628030e1203070c0b0a020f0a02030408070f05 71
    0x1c0a032080c11000c018100f0840ca0803524000c0440001601c00e9031060001582c40d8050f0403681c8115400c4003950150311401c003005d020031a004001074290351200c2c1031440410516000b110f48040090059407a030328144d00ca901203075016074005c40050740807404021002e0b0744082d64013203844088400702014103007a2543c5980d2140a0600744010008484417850a8001c1040340c40e01039129241d042e141d82c0d01c070101c00c10b003a0b09104074444c42103154a000c0c10f011000c103800c2e00d03551104c45001103124680e102201e06d8281e0107040c9500703e07100c090007207502d02c0402c041e00015124084c040010703e40801031005803000da902c010b1748503003055070b01842011600ba441406d41c1c0191079441c1c0300da0707001c09440188100c0e09480c00d5091100000c11041d10740c140c0000d00d0075480c5c41d08032010900a4624000a80300854801c1c00154030a4100000285c0100792030348c02500e110005410719604552071003190380101d6420b000350307000040c1040203282c24000c138001050240e9080e250b040c030700004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 921596483 1250 921595233 921595261
    0xc081e12060415180e010b03070e0405061f060e03190506070e0a0b09040504050a0f0803160e01090b0c0703060518191e050a050d0302041d01030201020d1d060d0b090a05 74
    0x1400d40103519003885d120a50fa00b54402520b800c001800c41e145555102148240d0b240d0550303041c0c46c83d008480000d5a05500301000c85500340b00c0c8003001c0d00e018504181103847e00301c0f02d842079505000381e00711983d04c41106541580060700507400303407680b800c01103000b810b0b283c02940040c0c0100455502080b140480000b81e9554000565011446a6135403610070f09080344c00100406185130841401e092107050320245219413584914061300d641c0c2e001055540d990401c00c03484c006464014103100141074140a0002e0040d104120391003140c4070303135405054070000c90b250714580d850307030207400e0b200070041001010b019803407009001c10202c2034803000340802c0d89a1000100c0c03c00c2c00c0b030503c01c019080008100c915009401d9680000402cfd600801170f601610440c101c0d40c08192401c000700240c01420b174104ca074143c0040402006000307055982a9204c030035002c000c00c0807840d004558171030303100501ca207014602d00042c1400c0544104002510090840146c0600d000c04001c0c4100300414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 921597733 1250 921596483 921596519
    0x1e050a090b04200c060709030506011802070c2d080706050c031213060507021507230f0a03240519091401050901080c010c081e12060415 60
    0xc0c0455414208000300b0080c081052001015500d00d00302001290303200b402034100c2202d503c050780e09540b2030040442e0a400280400f40264001600403c1542000c0c0c0b40c09003440d8142070f015090115030b4844400c650400e078010541d01a1101d1303401080690110344002c55040307041004102402c00c6105941c4940030b0007017105001c00041c5032190301a0800c141c50044c445c0c10341d50380f140e10b0400320251846d07552040840d01941440b001c1041c690000c10b40e003040300c01005012840381d03590402169038402c001c4454502c8100c03a004514960141c000070003070301c0442034807035a40e2000302d60300804a82e039510b1018141080313481500d0000180c00340980031144216413a00c03006000f0070003036054403101e5100000c41ca00c0d150140084022200307025040b01d0048400340003da982c0c00061b030725061808900c500150b1401c911100046c00d02e07024010b0164940b1601e2181540705140102c02d60043c071034052415220010040145004d001e81e0002c004104416100c0501c1c0400d802c0703041d90561 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 921598983 1250 921597733 921597749
    0x12111606080f041a0a020a17090c010e121e0d031811010e130b10020102040b0d1d0a150e0c180402010e040f020a03060918030c0c03020310061e050a 65
    0x2c0070900384041070360540c4c0780c0c4440c1c0710020103604003011000000d40c0030590200114002001c1c412039521480c100034807420b40304000d80a80c207580340c01103402503420f481e082d90081e080300015100d01402c02201c07c0d044002c0032907881c42e00341c0c00e80701881e14a00201d208200b60424580a03c4070b40d940c504182c403141e0000d00d034540c42400c0001a2000c2048621464004000440038240e09086800a5115000903034201d0341c02090414101c3c01d03803040e4003820001560030800c811058090340d0000082a0041c02ca40d107080e01030800b01030a0507019482940c071700c90580d1001c5e1001e4860300c030322418172040b40d000742012001c000c04522807001201500700003040303030700000b000d690180c5603007100c40c0001882004521a1030040c0c4000750030100d0b501c6e000a142c0300d030220b1980d18601c80c181400c0c9041d4010008100299012261b1041e001e034201e5010070180c00000060314200551462600200d03000700e509418602d008080b10350782088060b0f00e00812004020303640701c40d260007058481203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 921600233 1250 921598983 921599011
    0x711010809030715020d0f09080a1b082a0d0909021c0501032022110d0203090a11030313060f0c1704030308071115060d1211160608 58
    0x941245055000f840da02400642d0125106448040154024402d0b101c9804040084480c854410800c5541c0c50500500030901000002c031468080d5a1152201c50040c140c210000c600361369201d03003500b01c0c9040b050301c00b030b0106400ca003a2002000c524090301c981001820f418400c83d01c010808400751107005120359002503220b1070349001c402c40200001c44140c05110550356031800c288110610b0506400c88000340040700c10515144446541046101d541082c0f004420455803000784003110350100081c40c100b10300c0014601c64009580f0a00d900d1000e0000d5071058100000e641ea0a482c9440c400d400810441401010300d0145c44140c4085180c00d080f51000303013a040e241c950302d921014002d80603500e02c2d1541c0d13042d03420003007050345d200b0ba8901a031901d84007810340e07007032020b40342c6c02106412990507801d10b0f030a150541a8024001062255115540e44414428060101e013005c00100c1d203010080400504000b0f950040c09501e400820003807501500819010001d84000010060707 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 921601483 1250 921600233 921600241
    0x301030210050903011508010c02010605010e040b032a032e1d07230306060307062f011d060702030a031d060c0a1d01090e06210a020108060607110108 66
    0xc1841552600f01d07002d0b00800c0000b000c051808495aa6807280088541c01e09000c4515584103010309006ca400607190b0b001181c2c41e4500b00000340103541030054061080644001c10910569888020001701c6400003130f0f031000e480140b6003000d480c98644072100030350000081c01c90760b4070249003109a0003107400142c08808100070130804070009401c2026031107001c00104400204000d440300c1855032600c100c0702c1c8007070202030644880301100c0040d455001080100045400b84214409048401c00080d2104004a50b0100044000c0304c170340545a64444200824400000320581c150245e031006203100c0c40d00308070083d0b89200c3d02c2060410940c039189801d44030090381050b2407104070000f00751143c5150607092040b554125004042c00241d040910100f9804410181c2890b4101a075070740402c0d40c10309507220b4800e0000703020b21350031180030a84d0141c00f4120381104d011003030384880503106d1000d00b0700004011400c003902e001d00c140410000c5000083d40c201c00c0342a80070302030070001000c1d84c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 921602733 1250 921601483 921601487
    0x7350702040e01020d0e070e010311010f0203040513060e2a0c07051002011b050a09140d050a03020304050a0608010f06081e150a0902070b0a02030603030408120426030301030210 78
    0x55105403200340e640c0042110341e175840b642c0d00055402c101070380484036100c0ea1a101040020801e10010308048c02400241071107500c50740100d80110a14011646025558808107103003246400d503c3e91540c0d0b6840c0240042e103844c0c00382079000b00d100d0380d0200300c0304001140e40074000b4440b648154107102c0056050441401030008000921000303098010710040d414001e80600708034803480500ca09408900c0e22040d0080c2e00303a0b6403840031a51514910ba00700410f140d0b007041b882c20840e41c0308901c034141717100041c020040700e81228400d6001c0d40d02e50349080d0030700c0302c143d83c903802c10b2080c011064010301018034011040710848a080c603010301c503500c6010100713000280f02083c0ca4581080007040044800703403000015034100c425101840c0e410703510001d140890181d880300401c1412a80081400200950050768010000070241c914140c0c0e601d04091504501013455948200041000c00040e415980300c000c0100284032142203904421041503120720050000910402c1c2c0f101d1005400c80c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 921603983 1250 921602733 921602741
    0x1d0f011206090207050717120d0b03060709090b040c05070f0303020f04030f030e04020316110c0a030b010e07110d030f0908030702031810020c010e031c050735070204 73
    0x40000c60400c852525414050007a5001c044141c5191064002c002003400b10341c24001c000603580c030043e184c0318600003021169507110014081c507840e1682c41c8000c099605100c1c036030007161f0540b64030141501d45010704003a20840d1251611035403402e030400d00c4081d0070404481da410752150f020b4990f80418541500280241c50700d1000b141000309010040000c0b0381c000300e0800740280c50342c1c01d8a000000810040e48000c85000044c02e0103011501075850040c1111401304d02e61070143e541001c4003402241c54052107510582d951108a401040111580041690803250600d01484143c03c080040c0e5603e84509400350201640d0300800d4112043c0d0b0742c4012240d6900c00101992810024002943c0750000940d030b60640ca110f148000c41480c15070381c150041e14150300500000700143c00107490755600b22030300e107405004288403030300710151640c1510550030311a103496403542c4450800303075546a981e41c0720108101c0314100d80302c010009545c401c0001d4a210a885075141034a20106000e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 921605233 1250 921603983 921604007
    0xe0a02040906060e010f060806030c0a141f091a09030a03120b030d050c010b09040c0501030216120917060c0f0d0905060411040b030c06030a0b01020f07030f020108071d0f01 76
    0x1d801a0000425003020b1440400111f501c15900c1040036115502059107400c0601140395200000c410b081004514600c3c2141001a00809043c3c041ca1081c51040030a2170307010000000401101d82030026010b00c1e06001000e811985207242032441c20001710390380e000d1090b0050b060141f80351082c2011255900802e10185001e0242d44c1e0002c20340101a03d10340100444030059401c2101c007000038100481d1040c401d6400000440320300303240c0070040d0000d51000c610403132078040c1c2180c80408030341c0c405050403c1c8503540e80c56400243c41d02c81c80a059a0fa0000780145640020003848114402c60040e2440080410384031507441082d50300b00d000030483d0b01c2c1c008016004140c2001305102c0c601c49607001242040d6428400e0031003500401d500e84035035882c0c8941c09003003400800c0090301694424075000c48180100d4107107402e003c10951914100c0d51049030314000c400300560441d640154071a40003a50343c103112032540a00c12120310f5119603074120074001d041035035103000c050303110324110014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 921606483 1250 921605233 921605249
    0xf09120d0305070f02060411090702010612050a0b0112051005150909010c02070801060e040809041d0a02010e0d1109100b040e0108070f050102120c0703061b02010b040e0a0204090606 80
    0x1510322000010700900b5044030f81c0740114240d5054103410600120b40c403031080ea808084440307100c2401e420461a801c000c0c000f402150741e141c0010a00341c080d820f045a8440c019001015000410b00e8880c1c0400c0d0160444041c0340018803444d00040c80009103031465054960740841c80d035a90b18405400c01c84200b40056010300781405100400c0c4065001010301c05041d4241c47d802600c99464600780c81c0c9a110340c0448020920000f4003040e800000751515020040c0080f0700ca40840092b4407080224805a00940e000601000b0456802170100410f40034156040b602204c103940b180450403000441450044552000050250010303403421005010407150b5580c035aa1558445070b5111002d010708000c620911034041401e040d0b00c8100c104940d8140d0090100d0f05ca58003000ca595040054080246d1007079000c00320000300c2a000e20400c1d940d41d00041c42d056514240000d0940781005c030301c0c50040780b0701101014440300c04122140c255405607400b1610003014504400204200da000c00d132 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 921607733 1250 921606483 921606493
    0x70804030b04170d0c170c073012150e0f0a090c12110d0b061e06040b2104031d01050d05041103101a1e0d08031006090503030f0912 58
    0x4075070041d85d0142d0468011941e407900068240721404901007029958041585070500c1480c00241ca0756842c0c66205106000c0e881c642801000402c0240c50a040e00368013003103025501402c01146441010b20140b1709a0740950b90301d16010480d200582c00bd00b20307003003241600000482c00b4000d82c1081c100240e200901c600785607901e1142d04003001c05a85c04640f000e0841000071010714080032801059900a0a0f0001d00e0720351408010082e030748100241d891340040c1c40f09030300c65910800508010401c0840e000d54491041e0865882c1c00c400c2c1007500c1d104612041800003003940000010385145a52a031404110802c40c016102070041c44c8514100a04000070401040200c0ca14001c0c202d0040d812143c5072842c0340070308010b4074050038403404050326920190003949040e0081c541400c9000c0d80100703001254030007146440d10301c2c080560310300e580000ce101700201c032182c41c90000e164a103084c840345410b02001035120f21400e410038518107400725401800350384200c205000e5240c0b00d400c42e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 921608983 1250 921607733 921607747
    0x1e07032304320d05060912122a04090203071b0c03020f0a05061b060f0115080a1e0c180305100f1509090218060d0b0705160c050f0303070804030b0417 66
    0x1603517080100c0e09200140130b268640650124100c007691105881c89030490403a980e10301401901c100c803107108100e001000c004554032801e14000034070180a806901590300c1c900a08042c006001ea00000c0c00f00000c4511000041440740f2150801c1e20741c1115000302d100300b464009441c021040d00003507070150740001c441ca041c0040b240f4040345c20450b0f40c25a0820b984210011301029024170900c01804058143c03102854401c4405a42c00044001d00140b62090319650088405030740c102d03030101980d2071008822485e000815003402c258001c02e1480d0075402d42d940c2c3e580300c601c4818100c2100e9244c50480501a6071604401801c2c500e41144010302560b810706000681550b0000344d0040316043d4840c10640c0c20204028840d00c405407075603605003550703683d070085503a0003404801040814003034030b9036044c50490702c043c10303a029a6400000c10300b440f0410054000d620040d9100364010080b031000202801d0645040703940124042d6510f5540c1d080915002d12801c0c10707803602400c000f450b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 921610233 1250 921608983 921608993
    0x810050928050106061707030e01090c062d0e120c060708070605010504050f0402090a060e0702070f0806060f10020a05070914070f12021e07032304320d 67
    0x80700680c2c01000280803042c0e540f0011303100303d11203942078003403488002c00041100b801f81c2c001c00b002030508800050044084d8844141d460300c1c43d00700701c1c002940010905401072501d01400140c18a100740900452010400580104455038086014030418507103090380c0d03802800784a407103400180c01d03150388215600c0c02c0070140e401003a00712005460600045020704080c405c180c0324078852412819603441d19000c0020368a401441424030a807150b60100d048440c040f51680103003515001802001e00300142c01034124810b03005250294800000c110751551340c0200c054481100fa00c004048490440b003c1303050040015020305076120f100c0e000161600036511400e864528800c8a900d903448001d012034880202d480c03038400040544100d9400a12298000d016024820091000c070203403880c2d48030019005800c055000c02c103c0400e521601010001004d12208814106803410303083c110b10111f141c103852101c0c1c440058003000c490500741c05018905e0b2190b0014003400c4038003841c1c546 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 921611483 1250 921610233 921610303
    0x180703110c0a2d0302070e0a0e1b01030b060310060c0804090203240f0f09150405040803040507050306040803070503220f1209030f0215121303081008100509 69
    0x400d0508000c8040585503c80380480d0000d001503043e030290640310301e01101f00b0258078011b410302d02c1e4940e84000c030030f11503201006a21000001840e01400c2c604540c0c00250407140d4092a0a0040d2420400c01582c0b00c28210902d054450509210011760070b5810200c8890145400410109100005102026008a0180200f1048540c6900345501003405024542c0000c002e05504070010090400b460b25200c814103610215242e0b0380796502d240180014150b9409940c2624201c8000051006004050101c07030068002a00105038074140366549840c9884000c000d20208040400800d203140440540100c0e490f912070481c4032409501d0520ae040702d00c0b1580111440b0030045501c2c416540030351001800c0701d0704642c949002a01039000d00150b0591840c0900c01d88000300598007100c0d58005240b802950524100780280d1441e24000d0b00480014000302c03011141030008101d10400010801d00b07541002d9008580c0340ca070314404030314010340c100d00c4518090070041d290910f0b14031155 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 921612733 1250 921611483 921611513
    0x717180f04020f160602130e0a050c09030a03050708070c030809241c20030a060e15010c0309080616021603080708030405071a040302010806180703110c0a 68
    0xd000038200c26032010441244600360030070b11034580038400c5070344003000e26509a149074043c2e04098074105818010008961160304260385034490001031000000d840c2c03085690014440851b1490b00c0c400000095990711211070060401c4800542582005a0700054501141e400301c1b94075105a264504000d4035004540018054178450b195610314005202211a201003a00d00c0303545000b00f1820181704000b22415104802c54883c900d124030610100d182417074000c0140801600c0e81405403540303040c2e03401d54ac0000f403a1b010480c2440403031000425030102d1507000f42030148641489140c142c40000d17050307000b106940950400c01c0b146040c000b14000340c2641c2c40c1d0990784c100606111484801020b408050040e00c03080c0008000100c41c1380045030071038011421a041c440e40c82c20308280600408500d1030002401060400444d41c1041030241c210100b1608003600006441d1110308140009007201c0405131940c42c024092007007076085580400c43c035802d8614007103c608200e5a040c0c01a8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 921613983 1250 921612733 921612739
    0x5061309090819031a010e0a2d0f0b09060912070b180306010807030209102d060e011403131b0e010b3901141902130506071718 56
    0xc406225601c42c0c480d9049030045d80004c0034010a110707004491b040604054030f90401244040410303a01e4411a40403080004c18600c8000c0c0007000b11281c400241c82d40c80000300062441040c8298035040064800201043d03440c40d0b29030645d40b000840d5400e007400d212080340a40790012616803e580010032902000c03a8000485010302410b056030f40209104e0f030072058001d01014001403a0480c5c142c0d420440c0c10184445281d140c850000100c0000c03018004082d9480e215081c014000340584001420542840310540000c0b030000b811903084100d0f841c4c020100000056080142082a0030020703800c07500403d0191034140204085144a0040b00c481041000000903241810401c41d14002e40d555100d0465120305900641d038002c043c0304410b8004d4028510600c4d001c824801d900442c2d001410203c941e040a0442c0c0c81c1450b1241a14689240108241c6410400080b501e00850308196040b5030b1303c00560900c0400c1d22881005030240c075000140000304948140a1030341d1302c1d03100b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 921615233 1250 921613983 921614017
    0x5060706150f0506030a0e0a020306090708100b061e0d181401020408030726030a150e010501021e0c040e10050a1521061e1b0504050613090908 63
    0x240c030300c00c0404099103c0c60b5406203003000011490505504020200140f082c103c800b0303400700da80001d04010701261480002d9211a008010a200030843c3d015004524141040140d405801180d07451040080c0001c0009031007645010620f4600115130302454424010031041da180c800e401c0e0301d59060340e41903411004c02e14100306060310610850b000c48462100031441d00c103441e42c0e801d10301120072045460310000c00c2006445003c610005505c500e000301c1c000104000d20101140300000290010890f0309510070050210703980007d43c0c04031650020040c800402d000040c0c0908e008690000150014140040c49e00034040018102654140d01042070009a440420150032a032003c0d54030b50070131203040740401c011403c409840800c07005108405104501d90740340c460580e00d101c101c43d610440c503c1c2150039100042c1c490840328400c00f0031801c141c5124010018402e010780d0103141d01c038000004003136103503460f5040358500070710b0005014404200035050880c01d5170411450030a01401c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 921616483 1250 921615233 921615239
    0x9020a020114100509100f0905180a0b13050705040c0203130602011e090201021009200105040510030b0d1203021c090c0312030906140103030905060301030506070305100506070615 79
    0xb2041d5a4840d8041450310b4507810b16007410400b034000003812000c5036030b844080214041c03095903180c0028200030500441d072401c040c030310401503404481a011251308000c1c03d80c1c0000d110b549006412182d60300d4408909003d60030050308260050344410f902626201056003e160040003a08210b003046558140c001e0b92544264240c442200140020312172481c80841900ca1a80c8080c01582c010700c100d03031080070003940d41801c17125001800e49280b00125009540000074403542406c504c3d0030300c9d0042c1400d142c10080b0715003260054503c0c080c5600d841d5030344000d0b101c450364007000e242c2009111100038501140030700294040c20300781090b0660524650352a40d46400b03080d40040d4007040e1920f40510703649901c8104940c0400e10806c16440d800e841c0c011134154000c0500021040e4421101e6501d180f401605008031b542c0154000c10042c0010000320313101180207903000c095400c1c00308056031604807440145000da0001980018082103c2c014004190b01c401c2d5544d82c030795281ca9210392 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 921617733 1250 921616483 921616511
    0xc1915050705032a1204150b04020403020d0b06031f0e010b010f020c120118061a120307030305070903080307020c030105100f2903010b0307080f0708040b040c03080409020a0201 78
    0x48100e80e140e060100741c5001c0c1101c00b02082c4c0c5840702101401d6224108007440d02c80c507070882815141903d680424036019054400e10b4800c03802d46410840c0e045140c280307194080f03942d21442030400340007a00704500052092b00e0910403a5070140a40340800100c4034940c21410043c04a45510039056180c04144102c81d4001c244d8107c0010190300104440703403044080048000403845021259500c54001c51800c102c410f0903803400d80e11400c0c000c688141440481e101c094102a100703440b0f54054200642e00302800710803100c6c13503501850003240700c1d52110000c0d01d445079180d1005045100000c10424419404101480c06410840c0244459102c1c64648552401c2c80c3c01038003101c02141700c041141c5100c40d088114081c8a103080c1c0194801082e14550307498000b60711082e0490000130420030103075440303400c41303a004018840321400350030300c80700c01071500000800041502c0200700108040c094030f070300ca4400541d40301d50700030f550f42d1310750304110040d40100c548a8055030900d100c3c4c03200b0754 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 921618983 1250 921617733 921617737
    0x3306010206041a070e12010c020c030106120b07020c1e1c03140c0a08120405100608030405090c12010f1a040e0f0601050706020703080402010908031c020c1915050705 73
    0x41d80001264041d003a43c840030980320b800192142c81400000021020303992a50280c2c103104016060002440407039020002e414254409550b500c0382e450a00c1c00d200100041400c070440caa00900c5840c4940c0c2c86039016441e190152003095031101da204000b0104d00b0599004000e9460187c96800d40c068030710700c0180700000302080c02400720f406160900044d03001c5a000c0c00d100100b041c126668000c154480f07011541c001684440c050141200300024080e080100c02100740c2244e1040080502d07286205469001c1d40c0140c1c0c1c8505100802310b0380101d0000d0130703111078103400101e84895594078000607110088500c20f5811030800b03040e40510710400c40085d2800c40d90004143c03100c42e1382c0c1501000089100800072030600c08240031490101c2c10a00c003030800d50740b090b1180c0703219003403a0001601020842c4e1021075160310400881c03d4155007210401401d0741c2c09040542c45090300941a400c018061000d412600034842d0440180401d05042d502c109074132040800c0151a00181210702d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 921620233 1250 921618983 921618991
    0x51209041811090a06031403120702030a0c170409021b0f0102090f0d050f0d0207050901271d0a0503040515040614070305120a0504030306090203090d113306010206 72
    0xc2c0004521104a00b410300758a584200b074090b0001d03009440c0e03070b98021218075040c1c0032101a84040382c50780000341803d001503007001c05400154101005420001e0400002c1907008180d0400461010072184444081c0c030003070a40300700290740300c103122a00512810102c4034410454425120b0440790300c40f0620880b0810f0801400c4022a908040180030304030680d28000c131064400c03a4803240e0041030510a00b04984056406480b01516120030002c2c02081a003120305042c001c9041c00c6084240c1d502c50300140b01d01d0800c0070410400d050107203030007524000400c00c9207004421b108020000d0200c010016500c00312001c0b010103a410510f1091800780d40182e1000c54a4100d146c81c500801801030080f0340c5c802d1810500d0015232003001d0640300b10648900d5042d5440d04d05103c03c050305405118007805140500b1411450000301e800d5403110051040c005000e080310300194060b0051056100d080000410700040002d49140701034005880c040d003039402c420384404505c1540c4040307000c5000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 921621483 1250 921620233 921620243
    0xc02120c0f010b040b0d0602091c05060a0b0105190e0a0504060b04061404051c080702040204120302060a110d0b0102070902040b0a091a03040305030c0705120309070e010509040303020a09030512090418 88
    0x1b1040280d0b1090000d40c45803182d298003000e18003848084070b0b00815118a6244208050445801c1400100c3c1c1500d001c00d0390a0705024050101a01920074000c1c560103561031032400c402d408031304501207183c110581c3c011541050402001180a00c0d29000410440300280c1e50a050304d0700d00301500070396020b14052180d11120f02d028401d1040b0003550010f5503036000f4151a1b10f400302c00e0380010100ea12a520050003103101585d507200703254041c0b2600f68000d50014007441510201d08500809205489149032516a2501000e0389039100300981c6010345404041150380d02c0d00c3d10000b026036042595150b0000d101c2d4880801d40410183c13030100718640200d15181107803204c1c0c0c0c0623502c0340c1000f41800c41c008401e00a04c00807403000c00240c0140100e0420340c59403800c10030083c03800c000040d0021520841d912004010030f03110010f5043c2d12036010702e0010f80ba00c0d200241294024040d80c000f80c403920540c91101c007080002002803a40a000f01e4013004132680035042c01d5881440400040c103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 921622733 1250 921621483 921621499
    0x60c030f170c1305121e190c050a09020c300c210a02031911160305011109092a0f0301083d0605060a05030a150e0a0c02120c0f010b040b 60
    0x1902c0c0310004860071618840e0107a03103040c102c0e00b0b142071080100c7d08043d1944044000104045e081c004e44560280c80700e818158078001041d4007a560340c01c0c180110050074514013009a40d42044107101e100c1faa400361541c40d960b45c000d0a000c3c1c3d52428a20210305060300017044a194548686c0111028101c0c1a0043c6040142c20b400103039000b0076203044d2030301740601d10140c0340004005006039449010610711001e801421420080c0c02c503141c001c445642094100013480f001e0ba5030b032824035030180107800744000c5403500314441d80295100550b02c580c00d01c0c011486d0215204641c01a6040c3c41d1154121804070554000c00c4c0c024156804900d11341180c880c61008815585043c2c0c014020301c0381001050544e0b0b6080400c41c0c0d940240e040d0400070346c3c04070a01c044c011030b07401850842302e89001880012030501888030f10a040183c540c00300550f4036560302c01e0440c002d1140c803034000b0bc12205142c80c0ca41030320b885038480340e40004181c815468408080307400c0c0341505c2031035800c003405030502c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 921623983 1250 921622733 921622753
    0x30b010902030a090f060e1203090c0904150518060a060308180103110a021f0c0503010506210f1f081e01020903160f0e01060c030f170c130512 63
    0x24002e502c0940701605580d150000301000c0395814810906440c81908000303000021001740c10704101c1e02c440040e10701902041440410880040c02514a00e800c4480f0362180d1607c3c03401402c8860508050b070700b01d80c140000c021215003800100c1c107203500d50b00c081d50201c0e0346901c01f4104695181c04000d101c05814407022484a40920b1000f0314400706044c005400e1202000780c1816800c0441d1580c0107034450420390048290340740c10220001c05039a0280404258544090528001406003600440d804144421400e030000303541200100720702480f1080d820300c216106090b1408507400d1a4032605410541e41400c001001d080865818102034007030003c2c480400303001d456240480c008a59024401c014603a64140820401c442c0915070580209240050b030907031501c140c0c7e205803450f4940c0c000400913150084400004c540e81032510352144d00c40010103440351b40b240c0101000c504826800c005040082c00d0042200b82c103094240541d01e950751040001c1c0c400007030700c00821078100010746 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 921625233 1250 921623983 921623999
    0x2190203150411040908030702010b0303040e04030c0c120605010303030b0306040506070e01020312090606011e08011a04210b1f090c0219061a0406050105030f07030605100324030b01 80
    0x554101d842400d0351403207050031100003010785d40200703000d441c11007002051046081d0244144040c001056001e142000c1c940014290030b0840180042e05000705054000c04000354215141c000d80080d4080030341c004100d081c51002408240003c0700030078036040b0740040da0b10f00041c140b441a98010002c0596640384001142c0c00880a52504d06500c41403025121071000d2441c02c0d8842d40c0350303400030308480c030b800c82c001408080c030000c0040c10703142c580000400141d804420281075400c02c401c1d00c41e818500c0542e03100c2500c01c640c09041148031340440e842c4207070440700d031020581d40291207030041911a2040c00c502001d0740d00026070403101d02c03041003041844079040140c04908900507145181c418071800d141100c40b41d68102c680c140e4512001300341044028166000c11000c1d07900f0821a07041c10b00182140c48003400304042502940000390001e8841d80050024106c050401603419150b84406400303031462422130940c21114070300040c03001d03000c10071241c1203940280c00c0c610380740d20f0510360f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 921626483 1250 921625233 921625273
    0x6051612120216050c060a0512061302070609060501080624060903010e0d0212123709150c0807081806180c010801290405040e01050702190203 63
    0x51101401200781841e000d00c03209101422140942490091450b00c191a04130308040e404600743c3e1103001d0034400003910750350001c15200001d0319000c0021a50b107481c1d0015440285812524140e540002110010419903800081606100f800b0520541e40c03146000b41d1102c004484418a00703001c1c5100e1407400084102d41e042481c00513001034a481c0700c00011070301355206082804920343c0820740c205d20140e4104850700c40d090104034614104510300c04010507804001e0101c002707601c4c148692248040001c0a0814100000040040c2102d0303541c0301704000e00240402990101030bc19080a5440700318001c00f03200b14155030313440307001e030f5528481030720900e0001d05480700003211018001c581010410000d40900c04441b100c44c0c0c0740500403007240c54078400f058164104003003030004006100b43d0040081c0311140510002d07211046000006d40c45000301d43c08a50300c5420680e4008940e070707043d03000b10f0003014254282c03020320211418003a2441d2000714029016030201403551040c00380d0002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 921627733 1250 921626483 921626513
    0x211e1e12090d05160e0a23060103020c1006050a0801050606300705190e1f1418041803081303120903020705030d0c05030f1b0a050304030c060516 64
    0x81028003410b4143c40d11032506503e02e00c070711980c48405005000e100c02c0c20139440d602021041b0b0030b02c000000070003612204045629484905205034001c00c1090b03000350180c900c4543c0143c00c840d5500c5091404001803c218030601d0301840101001042514060140620400c0003a18040c03a00b010310100c4c00e01d40c0c015049500d03540c00340381415030841c041041040c1c0a11010340d60340c4c0d00da010401e104030710300c480e03010408188a104591400d0a4036100000004081c640074000480307a032041003034031410450004a03a00c0072000600f5019090289074089542da8291010004c3c005c025581e0121104500005401f145500340098990b100020b130240459102e881d0918017100400100800d44001c1c480850268101c7c1b1030511190400300160401c0703000720310302a44a19041d4687c51f80745d02c610f120368107000c0c4000902c8201c11948039031070392103507a0031803c07034291a04508000d0789a0f045408100c0e0500c1003140c00080851280c010342d030039038542400c020251816135807100b250f1a4608 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 921628983 1250 921627733 921627739
    0x61707050f0304080d05060616060e0f0a0b0a0e010212011404060f060e3307021903080705060606041422051806061806211e1e1209 58
    0x803001c14000c000010314007031407180c40015120480d905100701075510041005018141c14001c4444040031002d20800242e0402c2002580710b002c01c582c54103241e04504081d0f4144500594103082081141d10607100c0d2030407680401030342d480c0000b11400e0380724404040c9000894240140030041150300c2902540000500001c1c2203660703002c02c05540e901a601c28000b01d01c04800405907810152281d82d801440131000c0e1a5012000c1414900d00b1400c1070110381880000c44d041d0304540b1004051042c64031003503801c50350780742e03a0303d01902e0790f91100e81c0840d41d60050a000c40c12600b04641650103031071415030411289003059007804264028849201d12220820b407104102d2805445054000c03141604042881d00c02e002130b091401c98050300040c003a050b200c141d6141da401201009400031801c0300c10140500381c4000004d010040520400c0c42070040b00107041e00d0218010300981c8014501e01568603151850040c0b01d2040340c2c000c3c01c5c0c240b5400002c0c0304e401c62038900009002050000b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 921630233 1250 921628983 921628987
    0x906040f032613110307180207020d02040501090504050d080601080a0c022109190f0e1308180a0b030f0a0507090315330909020d0516030c0f06170705 66
    0x40c02c2509440da402e41d031100a40c003104612500f0700102c0708186407006829001881c03560b00d8800d071182e0640c040e002100d0303e180d002c510b8200b150794105043c100300ba0003c000f40304958448400c1d800819080d02c08960a100c0c00000c040000d0081440901c5040c050710303900e460340d4444a80d80b0160100000f443e0840c050282d020880c0005030404017214a00800161385881c3e40318280300007420b20403014041d80c8030312041008000c000900305804d9900a001c00110b94494032841c00c854590703200c004000702004980840d119190380c0250b000250304407090b0003002c0d541c0076062070b40e01c03042c1c0f10402c04002c1c120019811203201d4004175040030051030401c960907034940340d2540d5282801c0096400b42e1311910100601d0030040c0040904120607120101e15448445900c91240d04030b108411040f41c482100e80c080d51303110f0807030a403a1500482030b500c07c0301540d414520722166901080352400c16251000c50240c9400700000255541c41c2c681403001d80e849091922800001448042040341c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 921631483 1250 921630233 921630287
    0x71412150a1404051509071220030d0806030606040b1c050c030f0f0708010c0525080d05040b0f0919110a060203030907080a0c060f0c08160b0906040f03 67
    0x8861452049020708050318074000d002d424144428005407040040b6817000e130f0113000c424023450308002c44a500180030702c440481d44004003040304894000543c503000d02d00030007407619000a0300907c43c20044007681c0c1c0b0395994004210482d4020a07000390000a54881c60014049014445040740e02079811078440c0f040e0b000020b80741c0094261045001e4010385240344250900b0011b1801a2070f13800002d0140a4100c0001440d6000f0092983e02050800e0468088a11080c00b00c2e60f07020741109410740d032603078196428405441c00345c808844a00806000403850350b554410240100c065038044e140c64002840c60b18035201c0011010b8800340c0011045c07041c1560380490800041516070040e41c5c491138000205410700c0401d03800000203802400c081030004100c07111000c01c1e540075040c01301880024000444940e800300d6801008a82c00007080700c081d2000b844540c005520a80c0002c407166a0007040c0c6407036600683c0c0003030040741c05030301c401d0003e03009002a4030240c1b00203c1c5500001d00b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 921632733 1250 921631483 921631511
    0x3070c03020c030307080f3a050105240d060503010207030e01020f070e0a020702040b190e1006090b0a050904061433090d20011101051b03100306060305071412150a 72
    0x2c4110344c400016000701942482601589c041e00b40105001c4403841c20035103e0100c4410b0001d01100072007003000d00040c904ae0f030181c2035800907000e8000078001f1034481d5030358500588400050610355000d44118401009050f20005489050710101aa80f42c41904d503001007101030741103100d00b240e100b41c540c84242a25128000203c400b0b0601031030940a55180620250190f400030f8403058480000798400e10000d40c200b1401012540a400c40c5562400d42ca60212498000c0842e4142e100342441c0e400111041409081c021040d8101c0d65040081002c051111820b401611100320740078146040c485c00e042100e001d00100da9029142d8a852900342c0e442508000280c1070340b102c0503603404054071507942d00c0040d00401684510081280c0d041000e543c03c41c81c65100350780800d1000000006002040e0701402400544d40100e0511074241c0b0fa00e00030752105040d0042e0700c00d8243c6107401d40c50b10f241145060b8044034006000c0c040400b4141c000203001000100020340441e1680441c01c2440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 921633983 1250 921632733 921632797
    0x11401240f0f02120708030406061a0331120f0f020a06090305250b0601050a050d0b03030d0c02030c0d09030b0f04060b06040308120a0c020714031203070c03020c030307080f 76
    0x9840b0b044001d50345c1c5823500e401404c0700e400e50044071030020031244c800e44480e01801180c4d0801410003031003031107034803031486d001c400100d100d422104041a0f0500c0350030000220341005041d100380d00c03040076034075004000321102d01000343c040005901a40924001c182e2503448598083d029180441ca0281c418154030413000782d010300b140109170b40d580c404051056122a03d41c0180c401d103425031405807114001480b502441422050103580d400b000030441c1d50400850341c2e4a180341d4420701c011100c030203010b91240c000c5102c0c2c1c1110f0203501c1a080070a4030a15101e0240d82c0c0c082c0401d542d5448040ca44011101d00810864040e03030307030305820a030580d20b050241000314440c07280c1540e00d40e60312800185100f000380c26111400c0c100076650602c10b4000c40d02c401980c7c240141c108040b5081300000307240070360402520b100e18500009000c0b090f43c2c064800d400c40e9000c1c0d021a061000500c00341075480c883c0510150800801380b00200702000c80c40d001f004640d05185a40c94640c0d59481c40c20008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 921635233 1250 921633983 921633997
    0xa02040f080304080709060e0a050727060e0306010303080c0c0a0c0b03062707050706021902070e011a09010e1f030f1415060f0408011401240f0f0212 66
    0x142c1e0000c2400c02820408010703250280495038820302440345080c0003440c185402030082001e16407120005808140315241120300b1a1450701d4258010b01190103480c502c08450041ea0000303005442c000c0c00b213007400520a070403a641980c52442540c3c0340c545105030740d0003c0780c19880354011555a10003040d079621442001d00344004080b42d880c10540c081109a106211208101f041c0c03400c29650314032560a0700c25802425800c2c0266200300c1d510740305000f48142d2006003050b989100894030025400200700042e604400c4580d2100d03602c8502e504900b0340300020001c404070041002b99041d5103e44007105102d007010b0715040c00c401c44007046064040d880908040029603c2c1d81c981e07070070350150107941c0000446164049990a02081d000c1d584080b425145005a40c00100d0118013000c0104403401051088000c1140c080500700c0b5400c10b02003842081d0200705202c1000000b490b603010429070850741c1d500c8030b94032201c100d401035030b030f03000c1400d1440150700616154504002056000b0155 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 921636483 1250 921635233 921635249
    0x50306090a08130f090c0f080601020c09090c1f08060303071218080a1110170408030c120106050901080a060521120c010608010f050c0d091b060f030b01030b010e01080a02040f 77
    0x1007202d594009040c1e81d100e4060b1f07400c2001000900c070480e40c0114483d0801d0034151a032040b2030f072b2040720036480d00c5035070b045040c2c001012400b240e030250f4440413407240c25201f50380d81c0002521000d0030141d0707038001c001000e400050951032403202d00707002d4248017114080302002d0210b407959842a00d07045c020000c40540f400d8070711090181d91032078118080784c95051320381442480d00c860241192110140140010007001001010990759040c01702915002408840c0f46074840d80c550350002c00980001c5009408643d2500200303264141e140030307010689102410600580c03150405903121380d41510303948056030090b00744846042070030300014250b0314104000800c910b4a00703000307a42102c0e80f00c11b0546440d85004240901032000300700722500e1004400e00803e100ea0f0b5070500d09060403520703e1200440d454150006005a004411201d205219440801a401c900d000644c00e40b0800518540003071201d984e40881ca41c011445260080c0c002d4200506003034903811035284456040e005501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 921637733 1250 921636483 921636491
    0x21021f080406110301080d120207080408030a080105040b090f0711030c0d08060402070308070f050909071d090c030a0e1c1107080705030a02062d090406050306090a08130f09 76
    0x42400b696004180c4040070002d10f041c91076242c10300d0a91a0090101d5460400c5070410309260868001d405843c000ca81016095544075134540e4519500e51040c03001c100401c1c1071200001d12443d04d48503040b0706600c068003402850751150720007071803403100802c3c40e007c0c0580954a861a40c400b0030141010350110030042038a00d1180344040c0400030020a11486107004118090009522000300781d082744d0141001005002803600640b103e0140d00200d0ba08812280204500c05a000c621140c084c0c0880c22441405210717001403010400e0122068022003a0800105228a103154807001000d101c42e001e4a064004d540c600c1d42c8410450104400011110324040001c844180426001000640010080d9628010100b07072544907414001e441054085400d01c42c0080b05103102072400c02c1c0180815501c0c10000c60034090b6000801050b024a02e0940c0210302e174280001c410f800b411042004100c208800c0d03461b4840341d440301d031a001c5040d864220004440e100f0801910160800c00c00c082 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 921638983 1250 921637733 921637741
    0x8060928030f051309020a121107060e0307060e0601050901050414071b05100504050c1009030312021b0105090c01110309091f0b1909051f180b13050102060121021f08 73
    0x100050a5234988800807031400030302614050f0058103d8030900d501c40008260702120b48009410340c0202000601410700700140d10714800303c04102c00b03050700c01c115041c50300e590302c070390a2000311142c5480c01d0680300024404180e509000715181d01075040c030940600e05100090369240d0520442e02c0c0e100400d0380e01c420900007000418001060300d00d50036503256654618402e0014041c4485101c007406101031391002112101041d011543c80c00003411030340310120f00c400400c43c02400c0486581d031060207805000c2c00f440d84510f2007400c0a40400c2c000314280b003818010007244260180448600c441c0d405003040810b4440c020800007000700d0b000141c4c40e003034010300606811019481110030417040303180901c100e40d5101c414107040124101d1499031030002c0481560120b0150691030f90031002542c0008807010038030010280700e1109070f6650140c13956080166500c44081c05860700c210224110101800844010011041d000902e40d00090340c0194100211020308803525000405d070f68200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 921640233 1250 921638983 921638987
    0x30705070801060504020c1207300801051017090a0b01030308010e010909080f0304062a02011109010e0d0f020a0e0f280f0b0a08060928030f051309020a 67
    0x80004d00d030030b84040d031424418a40c0c0c651100c103e0184149120008666142800444960340c40514070701400001c7c10120f0720228111103050305218000100c441c0004078842c1042001c1004115450b1511200014076103040c0c0c08192004119400500c100701c20900460311145605000b90f02a8070b0750f00d4154107024045804c040f05030480040c45051441c1d02c0d0001d1541d0040f01d8960004100040d2a5201c601d0100b01500c40c202d4140407003200c4544840040c00c80c04564003d10058ad00204101c1c810110345800501072480000d001c100000341c480d665007001d07030b0441e03c11441065550f54a0368140c0c009407418099404c103140381d9002004100185181f038101d50780052031201003c80111442c140c030307155490175240480e4002d840e180c0c1071500c0234640e00103003c02d0314010000c1c0d01c01c54550346810703079680c011180941c03940300340016840740c807003078040100230044a000048440c5106443c02d91354850030200d40750400c030301008081d0030b200f00c5241c54006020502405030381d51042c40d0300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 921641483 1250 921640233 921640241
    0x12050a0b0f06010f051608031302180106110703050d2015040201120e0a0335070e0d11061c0e0d090501051201051905060c01020403022106071d03030705070801 70
    0xf4076000c0c404d04101642801038040c6c00c0201d1617904c404e80d9a030741d98034030505603104017007021b00039040072a00441070603019601ba091030690b500c80e0745d082c102101c21841e10355185054030003c2c055410018004c941e1901c00c8104402405448000c3d006054031409030701e103024220b620b8180054100c0b8244800c540e4003100180746c085059030140504640c40701629100c1015030030080c00c0c800e56144c119905601d054220a80340610248181003481020203140484421070b40b80000441401c2c2400c5246021044c1c900d0300d0381c00c02e201450100085042c046aa44190003c072040301501040062820b00d50140962020000000e007802001804019000101307076040744d81440010f12407800c00c0120262414111801103403030581d140e12640a40349402e05070340003550001400107410720702c850150024801c0300e1080d20212200c2001a80200303210542e10b01c14038080c1c001d80082401544a41c240740050482c640824110361605c9001900c2c40e4440c3c842100d8a400103001000041c400b841 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 921642733 1250 921641483 921641507
    0x4060308031602120406080702070b040e160210150515070312020f0d06060f1d060d0f0e010204030309080c0a03080304030c11060a03330e0403230325080112050a0b0f0601 75
    0x95464141070030320040c2c0e8601c200080451588038800c1113b154800d208000c404c4642542e010308026000b00d091843d20541c0c40b600806020f5821000c5c4d44403521084012500115016900e9400c1c03288408a040c000e54001c08081c42010014404c4104010151140c40300500140c5c80e28011088400d20140021603030400380d11060320680c0522015440e072208462195141d4200004c406a45454440040900320300c1c1070b81562000c00c0220405802461007405d58215074200c2e01000841c43c100b00c0762445a010080c0900820b00108000a020b100d00d04a498851702d030384044c04820304003041c02d980000000d00c00007515841d40c0084100000440b8112034203031620f40e43e4042e1481b661440f035000610403401b980c0d1f0703440f0004082c50f01c2501c1c1c8000d6188846e00400400284130400e0b441a0400c1d00c4103c41d00059107041001c0300341c60b84c00a40035000ea0388400c85070707a10701840744902414141003543e60340036541d42c0b24000741d02c0090441c0300300110f00c6802807a041420004100240841e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 921643983 1250 921642733 921642749
    0xb0a09060506031b0f030703050706020a150203010602070e18060a0c090830160c050f01020a0c0902030a020c060c0705011512060507051b0a110406030803160212040608070207 77
    0x243c6035944070003114241084d0744103071500c00006004102003031034443c06901c040c010b80500c030703004101142d020804c403601b9409641c440440a0318401200c00300d100a200c1c0308096800759204010708401ea4154039401605145080c090040d100b9a1504202c401c59001c00c5580c0d5417807244954940010120001e0044003004262800714005c030b401d021044840000340c1d440a48140c11020400101102e1015101040b416403181c428500180c0100e560f00596115129542c0e50464a51001034103040e4284c0200c3c0d04110140f510b074640c0c000350300c0908000e0f8480e400700006071190508120f40d5001c0d10964908a584103920300344142104d0540c801c0c281100069941082008200040405ca4a03005540080d03140c03541c050958031885a034000d240c40c9030303c00c54031903613200c404158021a01d008103200619101088208000c40c0d2950000404038034007840402c0040c00b2a9826003503081d25130040f40c04010306500b420750590060780c048130003c0d60500801c55519030611908004000788 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 921645233 1250 921643983 921643993
    0x306080d08240a030f0b15091614070c090e1f0c031d0f30180406180f0c0c03111e010c020105011203020c09070302070b0a0906050603 59
    0x5040010880c0e0405403000e00309110b14800c501c0c803258a042d1803040060018002400c9030b689150107000100c0b03851082d9100544280002ea0a02800e041c1c56400f04c402840760800341d0301d800b660a401b80303480e2411030070450540740f0942440020380060400310700803a1040d0320645000c80e1041a1030140c410001650045084659282c481f4020103110096201010481714078645c0c0c11002423050004241d111022040140b42080001c141c02c201901800305035003003151004121002c1109020050300c03003030207403108030750350b000d46902520942d0428082262606400000641540d085070410300201c0200300c1ca0007145101c03841200320446a4540500075a01d2001d800b0748001040c0402406004809400c2c0301307210350500410100d2510400389a50419030180b065001702051800c07079015619180010a8401d45078100844c001d81c544d000303100c1740c0c0c030340e60500000c0750f03002e041c10082c940c00784809400a0401210b5910414810340002070001d81410040c00341c502c0508034500036082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 921646483 1250 921645233 921645253
    0x1203070e041a010e21030a0c05060a0507020705010c08090a0632030a0b0319060b04060b04080d030b0d051203060a0e06030601090b01050f040e010503060c2503030b1906030608 77
    0x44111440c01180465207403800c03201c0241c3c00c0c5030b0000150380b000800d0100084441c609604a03e123012a603026100f04da14913518420600308650051301d91101590201200b0031071980718900000381d580c0b00740d118504021080e001300b9014074040e00301d40081070000644400045061304054180c541420a860426a954500d98001d11001d81200c640c29100c0c202403040752010403a001e138800c0c4141024602c005d0340c3c10450014589000424415070420400040407128241554180c40500d8081d051304180c040042d0001c20101880c182c2001c11030805102141088c4200316944c80040845e90303a134a4403400f0400f099009401a452032054102805040c0d100090300c02c2c15500a00e80c0040c107102c0760300041c2c60501400c0e0060501c241c000070082004c13984820002c0c1250415012600c2030380b5408c08243c5a030242d18410300048540103a2a01009d090301b000920b0b690090800259007105003011880030082c18400440c2800c03461810003d959040c0b01b000000c0420102604030711031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 921647733 1250 921646483 921646487
    0x160b091e0712030309110904150f0902061803011409030d0b0103110703080a02090d050a0209070302210c0403060c17070207050f0d17040303090e09061b0703021203070e041a01 77
    0x182c0820041c0406544540f1102040851880c0311400400180504990719180c586554030042c0750a82092003400c050340f282240e102401681c4038254002e0000c1e00b44200d0402d00d244030a144110f081e491743d2600705110703c0e40c0074a51158091580340307019540e1100b400481c0c0741985d0031141140d04051034452880c240d0a8154150b9840e154940383c11042c0e0345414520b40d020340282d030070482c1d224138442c003003404101001509449680c42524414031594407501c06500720b02920346403140c100b0303000711400c80c0c10150303034105944030700078405a60030603440b503d400c4212611002c81c200868041c114400c07a0f0781080740c08035071004403440100b0b011810200071600317a030581924103000324114011a801c000107004c0b000510303000000c0082c1c039140c0d00d00740184414100e215150601c481040441c030308020100d4000d1007100032501c14540b6483c183c6980790030b9880440d00b0b80442c01810181400b220015004500903019941e4000a080d5046d003000f084454500511141300000512844d20366 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 921648983 1250 921647733 921647759
    0x1060c110a150c05070e09030405330c070815090c030a171b01020706090c06050906030606161a0612010204030b0606030702031e180609090606160b091e07 68
    0x3054900c1c1c02c520100300c1d441c202d450034001c1d401c03816079000101b08120810100002510484000300c4000880791840000002e014985050140e0080d0b881559001e840d1020401080d000703405004407000641d4030b03070401c1d04081f607500415440301401c006109110004105003501a44114090001d03041c49645828035000a0501c5491030800072480c0c0400c81d0a54207408038a0321040c009558500b40c42c6000c0c03005000040046402ca02a4100441d1a501c00d605589907848040c0c41189562144000c01040b90804c02c5550001456000d480c800111806415914a100000c000c0c4060030300c3c030108042c40d84c2038013200c3d01683c414042000070400803508590801c00030b64905e652926559005c900714414a82d0070300c0d034113491410134003402d0505001840c425180c0c01c00d03055404c01c084100056407144511082c2d0040c10600810881c3c038246000300350052500344080400000f5658812035a45c0c00c071030004083e08203000c0c1e440010401ca081d1002441124003400c000c505048480c2415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 921650233 1250 921648983 921649019
    0xb06010f0806010f14030901020403050f07150509130914010c0f09030b10080a1419020102063103120c090807170a151e05060a0314030d0501060c110a 66
    0x3640c5502c40c01c3d04c3e80102e4422814000360440342d6500d00c0c002150034041d500ca440200c606100d40c5c442140e0201300840c440041e1104203540c07019020070003070210342c0c1e0f40000b02c4007a4402d801200103800002c05106540074148031300043c1e03240281c0c0b641498211195501444148191100800c5055074454454420b49500c001c0b002c0c22501d884064030100e071069080411544910340402050000c016400003841c2e0301d050481d42580e948030640303280121100d000901591040300400d1128007510784051140c4086041d080c2c400205600c14040090740090580115154103192000c076076290250a031072140e9810a4803142e487c212046079103007068032880d150826414a8100030000a101c0b40311700d950800d0012016912949146000b0039507403103483d02c0c0840b03100d0b2030000ca810902503d0303c82c241c020010040145552120308409903154120f03500b90004103c00c0740f400f0300354030856000e13100c6079954071640040d034074085d594005180301040c85540c18420402c12104110010419 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 921651483 1250 921650233 921650237
    0x5040b0412150e100e0d050a030e010b130b0a050d05030301030807030210150509070320070c050916080c1201060e01051201060806040c051c023001030b06010f080601 73
    0x840c016030b00302418045405958440326904150140e00030303501c0029228980d000c020001c1000c00600c0340c0203035440c07000103031150104a0034000145110b004c0e505c0b0058200d40c081c0042695151000050001d00b6501c0d80722024580c2c0d2000003520703042ca880b8035006444180c4070040c01d041e103502c4035550b9010510005110200000f803260403d4401e100741142c100c1e0452040c0300c810344c800440304210741c6602841d4002c282050020b4030041c8a40503580b0044803604800f506452140500c0c0c0340c642c440003090f2001c00303050304000f4581c0c4441401902c07500002c410808411001103004062610241000c1003405033030255419000301c03040c4060445010741099044150340b00016151809030365001d0039000140d600019041760045d0702d0714403c0c141110104102104500140c60602507900c9050002002c0a046030388030f059580240320340c414141c000b02450504032441c182040c00031494100c1101418010000c00003a8068150841c4003400c02543d0f000800d900103140031401801541 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 921652733 1250 921651483 921651509
    0x4030f0c09060e0f07050307090303030b0d0b0c04091d0c0618060304060c030e15220506070507060c08011404050408040f0b19020703020303270a141005040b04 70
    0x812115a4a0100401e0960800e00401d65201c07407501020604651041c08641c1000004203c20f02c038604892241c8481c0c0c445044080c2161802c5000340000290b003604004000c0c4440d01041d9942e49051241804180265a403800e1401850540701229031004201c0b00a0f00d46000b130030008501d0f0908030900352201625846816a441802201441040e401c80030000921041c4859500321300301b66280303070310f00348030704181c1800b4075035200d00c0c00107600e040f5558507001c200c503510320248071404868030301c02d41010650301d0b464260400c2c000303583e202c0214400040c1c0c4010802d41d80900f55000c0820308003141150301d861510b00131403041300900d80c81281e446000a08001070081500c1c05841c2400d40760f000300d6150049814540e00c140d00102a203140c05c1c00c640712003440080c4060940764003801031410200c4500c1d14810441052580c0300001d00542e813041c055403654500080201015448644040050400d101061144145031801c100041105100c100d0b800ca0403142196601c0d42490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 921653983 1250 921652733 921652763
    0x406270b1005190e0c0f1b2b080406090203061014060708180102010f0204060c03090e010305070b03040819210e1f020d022208010903020d1b050f240c0403 68
    0x3c0140e2048040c200160031020851003035800c4614659502c0c3e082c04030445811002420f01e044203c1d01c4490610742e80108c04000140aa11500c200e40d0030038030a18003c146143c07a540044d0802c0e01c110781110b401d591600703040143d174240581c00741c4910f2050322954074002040d20340d50514807030103c000288002a01800d10b2692003544820444a003050003192a1919980014002e180260f81503000561100020500c0340762b03485024100d0394480c0062111034a0542990603c1e0001802506d02d03d1040c8041866000c0c2108400c082c0462655110300d41e60400c40d4464189000340600b08182c0c4c40c0c034864106c100760000d0008403245620200000d01c5500c0e40816000e4030400440c66195030011501103c02d802c07480c141c2c48009800320300110215110308082d401c80311010b03c0079006070b0086050441850040e00643c41c4045101140302c1e000f50107460b00c5142c0f106038403403841d007940129540c1d00044a030300c5c000304100340c184081c1c00c4a403c10306035100b1640554000a0a100c065005030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 921655233 1250 921653983 921654001
    0x40203062202190f06050f0307140417030a080f060d0213020403150902012a0809040b0409030e03060105040c0909050a1b02010b0f01080705030406270b1005190e 71
    0x14100c0e0382e00829002911621610560511180d4401c0410300d500624001c20001d0003181030300c40d8500800383c020704655410208403240c03456880c0700300005104000c042007050389030303420340040c0741c400340190780d1224034410080041500a090203000c2c50800c052102650700e64040d000456011606100310400c65000c5200901c034903070000f03010503524829000442c040e42c01001314103000362141c900d4088017441e510714010485564510050020081c0d0000400c4d000c054185900050000180c040446000c41c2c2181c92582c0d09401082403000a195613107420445075000d41000e403000d002002c254070019100c082d940c0103800d522511000041c030031022503400342c502016440b5043c2020801070002900920001d10601e01485003044006115401180743c903000722150ba88840c0313141d075503481f4240202803044d0b080c44040c0d503024050341854414030035014264011400c0980508040008640c0c0c40d0240d4042801108103200d820442e5416070030403000c4803a0310145000307959840d400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 921656483 1250 921655233 921655291
    0x71716030e1906030b090702061015020c0a090f291203071a090111030c0403080a0909020d1e06060206040f0614010f152f1e0a0c060804020306 63
    0xb11400d4605512400079080c2d9054000104071002620381e0701d41074990f0042244c980c5012031f6a1002112295400c00a90700c1902c079000004180d4410b4800c104141c07030016007d451554040d841c0551905038a042d40c0e000d030300c203119a5020000505110540315a04000500300e1040680d00c00c0d850402e10064419061040b2052140c1c0864080d01001d0000c058000100040d80c03151215845d0400f1640c1002a010845e401031b46000405410f0615550752500203078802c180036402c03c0300c0c070300000405506d2800581901c14000303802281c2c80b942d508089044103800c1e07a000020740d0502404225098001c42c10b0358219401c8080004455094102600034020300c103180740b10b1408600002a48800241c1140265600c2c0c2214049030314246070100c1d9400fa117031129080c0c50400c00b003003502d11080201c03149000160307001610680404502c1c0d560781c00600400c403d40079001400b0401c01c1289c49005940075003c1410700da0400e04154002c0303a80d5000041003400c40b00000d511914108d030361058 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 921657733 1250 921656483 921656509
    0x1816030612240204141003020d330311060c031c05060405060d0218090106050402070804030209010b0f190c1202010b040515030303151c08071716030e 66
    0xa414910400d1518040c1044402607070100b240504100351a4480c00060086500300e80118818450500b5036400b04803d07229030116402c00d040c0e08010704441c20302c0c07034052030003003130b6212005450381c08071002a8410205111100740c000c5442c050184009040c02002c0d120075031043d00c0b4a44c0780d5041e2352115165210740541d4407114000441404003a01c00c070780015108820a550a00441d107601c4180024042107200095000c221910080018104000c400798401c0341d81001141c640e60b1900454201c1e0710445d000d8030080070005044c0306500340442c441e03004100301c07a2124509250000704400b00d0107090000600b2584810540446034821103001603907035000441c580c100911190064028586d2060f501e000e94200400906080c8110380c1807080e508000e1701951843c1e9940309a464003030f803d140455400714090301c90303100100d105644851100d202d80036203590380b038150401071005049030304032010888042283c80074070004d44201007451941814030740d4181e5803600004201c1c44106c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 921658983 1250 921657733 921657749
    0xd0f020f030108240603101e06120c08031e0a0c0c0b0d0c14070204153b060f010819180b090606031c111006090b18160306 54
    0x2100201d03042a01142400d02801311540c000100e90494500c00c10b50403048503026455040581e003017000d080d00d9040210413514500c0f42c02c4404544030001c00403500707603400500300b01012016500403c026000400c01500d050401141019004e0f5984d03226800b00c070320514204803010540c01911800703011903224041d800109046000d80320702e04d0502641095035420441402c122520302100e0141035518070b540d1402160ba40340002c541c0a210182c5408142a00011a4650001180e0350791102200e03504007914000110b102d044e00c060401c1c82004101840c6c0e4010041c1800926074030b603490707a00040002c1c2804501561000069292907000b05036013549281481c1c000705602d441c0c943c0c519041e0f4420f0300c40501c0c07522aa040540c0e40c410441d4041e0305031f80b2a510a04241c40700c682d1911004540703242014944030401031180c2088805541c040d0943c2d180c42d800e1100750001e01500910060a54800034010307449142080000390142c09620340d502d0030344050354042d110f07800400c0500399071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 921660233 1250 921658983 921658987
    0x10050a06210f062a0903050304051c0b0906041b0f03060e010f06081c05090a0905090a060c020c120a02010c0b0912070f02040b01110601030206031503060f06100201020c030d0f020f 79
    0x401d92130340c010f420a1124119210700240040340050083c02d20b101a680c11000560a2608040601950100c1d811031000d40e42200712032400082c100980c01313807184030340c000544202c1c145071070100040310b001e61880740344240071902032190f129200c8540040381c0e0030417800324001c1040340c00280184030a8128000c00d80c20001d000c501030200050b02e07544002140c040c803650201800c022680c500803c4600307980203c011104102640082d00090f030006111000e413500d0a890783d80d00000c940c103d02c10240543c028403580e01c01854841da40703001e0409101d002c1c100e84049540000c1c01d6181043c0020501d1050401051142108001c070100308000f00d045d10380c0c1c402417070500c031910700003041c4c081b0320580c2090141c414a511644810b9040d5850500400c6241d086608100702074200406003844044210680c60b1241d4040201c1e80c01018900038207100781c10404240000b2070403000703104055a00402001140810010454218800152000811480710041503000c0e01c544a0104c550143c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 921661483 1250 921660233 921660251
    0x19030504210c0801020a0516020103020c0304060e041a0f121c09080f03130e1306090f03080a0b0a06030b131d0601150503070c0309090e10050a06210f06 67
    0x300303080e04070150b0051065200301d41d5144007075800e070b105020345200050010300c0341b20b2900c10030340007240035184141405801e041045800d1803868005921040001c0c1c51010340340c0380c9081034400e21441c204a80c0341031002701500d101050340d011500354114021301044589044140c0140241400203400d00c050403e00309401031b00405940f0b0300c3c000c05115005860b01505421400012210000c080c80d9080c0b411903c0c0041c0c1031a0103e0051821085007005442040040d03a80c2c814840d00520404941c1442c00150400400d081c2005080c1d4890900d854404003440d034594035800102c132001d180100300399081c1804101110b042000780581c0e141003007000d84107030b1840c0c1c44d604041d0000c081100c440d03a90f85e6174950409801c5541000215030104089002c4500c03076090500c040d4001e08011144980c2c8550460841e101600030310101d03000440051009611030203610f4004405c0403080c0078a50034200609000c041030700c00f0045261078422000100700030540040d500d1034004208008800e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 921662733 1250 921661483 921661529
    0xd06050a0b0913150e0901060902161b060e0609030a05010e010b190e0115050c12030a11040518041703040606062601090506030c09090102090f09070219030504 70
    0x4680454450382403c0804140b14141d80304503d940c40b00d855801e0021460b002042580440180c50300034079549905000c200c01c403581c001490208115004442420440c5c10440001c008401042c001030551010410000d9444100440311510868a2131b40e00c5011800192605204030001041542042044246050b040d4080800c4007000e0380c2c0e41c44d03085482004008094000c0c0100350300740000a0040c00f0113101140d1045c0c103001e031414500d02c0c0115108000b498401c100d00811301c220000401c201c200b284070f010310b20401031920394640c1020305000c005a02d50844000d06030001060100041c14400707190003aa4502d171a44a00350b13a6400c10f070814002070541402208040390b1409804004c0c101d44a43c03181910801206984440e42007001308409001c001d044a54180301d06070041d03400f55600302c69640506402c01c00140d88060004c1885245145d000f0800c0c46100c0010030442c8a5801180c4c40e1408110b80d40222000c06448c902900c05000c5d0b6009643c45481101e080c1c1d0361a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 921663983 1250 921662733 921662737
    0xc0c0c01030e0304121a091f050411131b020703030e0f0307210b160203070f1b090609051e2208121801061401050304021503071e0e010c080d06050a0b 66
    0x103402e00c100c0141ea6031440f0555859200c1c861030301c3c031060048d14000d00180a9446607801521402101203404d03206000500c2d03440c000d004000d041d41e680c1040380da800b0041a52001501854005401070900e1500d0140a444042881d280100041c01c0416980d0b5018001c00024040fa11203440d01d1440c10041400d01c00e07005001210030000c0c034800b00b0108403c0f2040d0000110a9500840c80c004c3c4540e038183c07240082c15001c9034020100c140302011480b012107510050a2501c40005203d0301d440b11b503000755000176106000e000e4201041c54502107a20000d141c0c4600c0c240c1c1610706080009600f2100b000c2036041c054100c0300c002c1044c40c15180c0e59100700d8000d00200b043c64a01000c205095401c80d040340c41004071920303001c1c2c81c250655000350007459220f80000c01c0c01907412064441507007103900496041002035101c1400c55107814020a12105c1e1400c1458400360840b600c00000c0c00f140306152000c0c0242d103002c41c4800c8050510b4200d0005408050000c1441030759070407010b551030f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 921665233 1250 921663983 921664013
    0xc010c02030a090504060509150f100309050712020303040b0c0a051005010306150f060e13020c060f071d04180210020303010603140c220801061d0c0c0c01030e030412 73
    0x40d20410380040c44c3c0c5002d00904d030588500918004282c2c0340d07030340500e62080c07001d03500365041443e100d42e030055561401485c0c4000110390718041112325151601f03c2c10841c6139002030300143c298100900258800200b0f8509803002c0c030300c545540d001184403141c6401100c00c001000c601c03c03010141841c1e4510341009040304c0c4606014024a140250404441c11260060f994103e9408504001c8140300715640318030204040c040403c91803413000404140d07440302d40302041c20703800743d0207100d602055405040e90120440c40d00304032060001c68031407450050b007031009205135211501c0e01e005c1040085001c0102ea4000c141401c90b40d800c49001c2d403240c109100f4000400d140a40f03441c5050103001c182441500100c00300b030302e080c0489075a603c0c04200034006000e00600ad14010500d61000d00c03c81c009803c1100049580440c040d40c140d4a0441c010110f01e5030345424800d204c880d80001a285140800174207000c00c01d048103111003443e5010380ea0180076203141400481041c414520641441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 921666483 1250 921665233 921665237
    0xc0a08160605090102070201021209181311090f1b040b1207030e030406170714040b0d0c1b230111130e040f0303051b190f1110110c010c02030a 63
    0xb25035148443c1508034005c449020740907030011201100c020f401240149614040200f4800a0510400f8400c03c3c1403c105c88009822100380490410b0040905030708241800495042e905450702050f00b050307005002c0c03d0906010800341d04541800000404d40700a030a110303240c99101c3d64000500450120140d5014022918104000003c0d88022045400b1707900c807074407201078018075000709000c140030041020b002c00a02a00302101c921000000304020101c0b1800140c80b01d00303100f10340c0111008a001c1c0b50500040c0140b0320b40d0815610101c148107600040300b51003d06004504005400c0562098051546442c1d40c4544144091001e043d10a081140c0340da00705446981c0c08103c602c09440191007001d41003240c00000b4402e0b040170f60b001000c0901e10410284035550038890b0b030080d8030040c00d410b0b400c1007a403400a40c004c500540c034a1003890040300c000b100310485511150302c1d1415041035520360a0201340d0511620407608802c4d43c4d030f802000188000840292643c00041000d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 921667733 1250 921666483 921666491
    0x30f0a030203062103040608060d0f08071505040f02040902040f0219120c0221040e0f0717010e0c07210c02090a0606020607050d0f06090203100f030503030402060c0a081606 76
    0x102001581c04e000007540140e80150300c0d05003000b07003c2e9044ca40080259522038100e01624001074080c2644039001440780d94050307200c00403481c09040642030700ca61714a0b01407411040101061602040041082c0c0640d0f00090011281c00800e0190150154100c0100d0002035000010380259502d4640c00720240d17204400030300160080001c0e150525011801640a03424040340031024100409a0488101481d03240c241e4501904400141c122030710f5000d4440c803400c2100c1d054000d400500716010100030401c1560400c550842d040f08040c201d004207910204007403040040001c0008220b044040c150345a11103803c4e0300034035046800c00228011038400011900e041110b000741026901642c010701620b03034610404590540203d01c004030520344400104019460900c81c01e005858100390160341e070b2401010307030000c440455114402d0b241d44054104081103011040d46d4120354112082561420308038490b1740740140b0300c180078000c0c20b40011000940b03a118072190300304030701c0307100248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 921668983 1250 921667733 921667759
    0x18060c202e09081f0c11010501090617030c070303050a09050909070501022401330c0c081209040b03150a0504020a0f061e030f0e010f060b04120602070302030f0a03020306 75
    0x1a1149025050484200040c44803800c2103132890300140c000d8021880e12120f4140303456015803d44400380d2001102623135803001030ac001d0081c4400685141d800c40004c515101240d2046070b41d424940c032002d0100a408208101d100b44a811820b0007020001d10504c05030801100064503800a407183c180944104000400075080c001c040901045c0c02a0744100e40340c0c40d21140c100300c80301006c1555031149a45e40317500d0310300d4540c52141c4480030311960b922000403510710744040c4c0412a034200d080154800050a2000d81e4044111100c200040d14003080d107040c00350100e403405c10029511030000b10003208200d542c0000d0b5020710b00c81e50084800719a01555406a04186041c6002c0c070320001c0c1c48010244002e900781c0d50103032803032503091800203507008025019004480643c16181003a035111081c1e8554014a40902800b80c008803407244d1900349414500d4400c5403c6c00c4004041c1c0d900494000d080c14000d1056803040c070308140303074150b80d044140c02c020001e5104039400c82c840d0210034201 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 921670233 1250 921668983 921668999
    0xf0c0801120807051212070801081209150d180c0b0a0509010f092601053103032304140f0303061c0203070618060c202e09 54
    0x5241251510a050611807009031140d41407588510020780d9640709402c1ea0101550302c10008040a20072001081c000f414107c40003414440181d1104110b0b134031094404450a64440032152540302c1103d0351182003081d4118843d150003010551000c4a241900365810b10000c4c1c10401012885010403280441d15010b00f00c00c1c0e4040e02c00200300051041c410362005500404031203128080904181118941c0c42380c8603002601c8280610310035001c0c03010f06103d0b1290034090160484002c1c40b241c0f50408040544456a400200e14034a2854030700144a013451b0095004050b81d0500d10070700c500c0265094020456070000b41c2d0101c4900d86908254414030501003500083d070701c1564061851500e41c0800c001c034480e00d418058180c04c3c504012000183d80402040303008006584a00e00f0700c20a01c0016190101d280d800f40c0c0034400f01c0c03500400042c000240030f1080b12844892010300340e1000700800c0041000402c0e0813110b240c4001c0b861190700c0301301008c00c40070000d42c1c0e43c405002d84506007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 921671483 1250 921670233 921670247
    0x60315091b0d0f02071403042612070305040305060a1d06060901030219210201020c0307180c092309010f06140d140a0204080c0d030f03050702031902010f0c 69
    0x4003041d41007040c02585030000a6400420104611000140c14282c2c01e84130821034081800e04440aa4800101004008103540044001280c103150080d488203000183d43e40305d074089805003142c0000041c0000c10540070b5400d0b1409190481c0c01c1f50b90700c0c030340b0100e110014880c9481903202c909040c00c0a01a940c1c0c00102c03584151000340000300300d40d00c0c1d03900788081d0042040b102d20450003d0300340422139180300108241c1707e800b6000080d400c5100c50002a0030083c640c14441e0103030704446ea050000703c41c06504810041b03074a00c800200e4504480c0b08442029168000c001c038941e101c46108201d0301114903500f0301c20001c6403500c01d0390f42d0318034000d8035142c0030b445100d011a0200c007c500c05641444090038a4843c02c0b88003088a4551380c044070b9464400711141c40310b4540c04038050200b100700b004820001c0310709840c1408404540e44002c0d090201c402540750415494100003501d4600c28800c0e02e0800c01c0300c81003642e05080500010703000c2c00a0280314225145084e2010720300c548281c503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 921672733 1250 921671483 921671521
    0x2030313080a0c1719030905030a0f0614060901030f022b02030d0216120c120c0f06140d050403030e0d05120a0c0e2b062a080a0e0c06031509 62
    0x42200150800c5d00f080801415081981841182940040c69441c18010740755118400d20f01d030f201c040c60525120003100c04000d40c440100090700100040c40d281c0020850559030441070f110214882e5200240428a01600010f40c4c0c004c0000c9200c0490448110b440c0c019108a050300c0c2c4500d690002203a407030031070115550700140c1136102003010400c07840758210405c0c05426642e0000d5150f00c55010300140180d8200c0350030b04556801c01c409c40c020301098014041620380709500e01281e5080a040b402031007041d070030680c1d442c80401c1c10180207a2000f4100139a0350300340c9004c00007518010b0039940000f61907408040c400c0000a80c038a0b03061007010b032201d9442e00c071000070114140034404001240d4142c070001c201c0e90f004402c0e2808000c0804010944030b14000b160700200803048564802c0880128503070b88030021088a8140e82004019502c01003c0e003000910035401c602080c90301c030203821070603041100082842051031320480e03a03c4001c80e055500c86e0f40d40c3c03508003080e2521500303d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 921673983 1250 921672733 921672779
    0x30c20030729040f15020c09190b03100506042d0903140304050d11031201170709150905101215060306150501030b06040302061602030313080a0c 64
    0x6200b440807000ca551041400046030030000384610380e1244201c850b90003034200c00016495554104803c240e41d207101d50001195101500c0f8504e01240131075100b01001e000e20951113200d00c09440101c59580c08240714410040444440c8600310200318020034060b81c00d940128200000e40546445002d402403118007280c0000d17804074a1005200007c02180c0c4084042020030540e1400270429880a0750149002e0b502400203418000400380012000441f00c0403c0c6d041400880080c00180c85082c5c110303811291003000c4400c0c0300034202d00f0b001c031580040a2551805080e0b0140c07601d00c0d001d510a40380100e408200580301c030269800b817180c0c1442480001e038460ba40c90700c0003981490142c804415071030341c042806901c9503110030580d00d9103042d40c400d038401c4e660f04000d036607414051184208001e803440d6240508680106403030b403088049000940c0030500101c2c0454a0400c100d40c04040203410040740e0301c3d11000d0460315194040c40550300320b40d850b44045003a10a07000032201c40403200c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 921675233 1250 921673983 921673993
    0xc04080601170f07080c0429010c1502040b090a08060412030902010c020a12110406150507020d0206040b0403060c0e0105071e05010c0e12010c14030a090f030c2003 72
    0x106407106480844540341e1400e003c2c1c1c3c1d01590b0410010407145002d02600e40150048568030810300044445250003135001d400c4d0481c21400c840901e80b60b98036000420302c2d001824121908015100190b1024142c000503c00039000505182003006000d000c0002c94101c0506a0384001403039131140d0a0760080c0800d604441460203a078080d0340681c00c40b61041c10126490390003038000451180855028902400b1000e80d428100300c1038481c04800104212002c11065051004d07003508040390502c480d050203400205103055584201940d2a143c2d070041102e656070741c860030324050341d4000340f00031205c1500341102c1501c40744c000c80f1404010311040e03481c2c41c2008919103404000040c1c2040310105c0360310211060000c80c00038007801c00410000d44568058510030410700c01c8051010340a6141da900d0000411846075001c400759440c00c6403450501d450303803207851002000f04120140200040b2100441c1002c05030414204500e841c0078085551f001c4041800502c8003001c40140280e0540003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 921676483 1250 921675233 921675239
    0x60e011e090e07291c0e0a08030a0c02030c100204030b01061403280507050903071a0f030c0c1507080c0304020a05012106030f050d0f050d1a041803080c04080601 71
    0x1091108442e0880240042045003002d500303404d503913520014048404012030700ca60413480485000707078000000400010324001b4050341300c043c450300000c4c00c1c400e030013034944140c1d8158510810036201849038240a40d100b10924910200003175100748422101c0032107400000841c2e034060503019404040d041c1c03040b4034554421070f0501002c8924210104110f100102c1401c0d000b11601c640d61054805031105aa03840290b000c2510f042c1c8503501110280400025104407124900d064410503441801c07041c0d104c1d10380302515911805000300000c420312550786c0d0301a600e07041c0700249024403030988a01c50503455200035002d80d84000c1741d000c0d401502c00134041025500c038105000d10b81108030806c0550868100030700301510200d40c015130304010040311403400d100062100007030517506400c100700001c20700e03100501140074901c50248080c0d40c8031141650f0f9070080e00813082c0880300030800c01503200710051030300234508010b800380c0c0025500400110490312000c201c03000c0c4e404050083ca403a80c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 921677733 1250 921676483 921676499
    0x6011116060c0201030e0d03060e0a021606200c100c0e010203120912181503040c03061a09010902130605091302070f020a0b04080c040204051f03060e011e090e07 71
    0x2c441c007412410160303612011840700d84d061100e805c445507075036000b01d401482c101d81c03680803100103801d00070241d104001110001c112141c101e03c41550281010a00703003404245050f90b010a034000c40000007000030500c2400c1c0e0042860006041d88200400ca4015040811500c1c110194400c41c0960700400484a04c440f5004080341e003c24024201c541e1080c04420000079500040c000282004d101d0384940c51b6407800410441c404003400d504076046107011340700e0003518800340c030020707090a0742da90100c600f44403a4451400c00c0341000c4d052098650799110000000d42c8500d200541ba040401340204071244a4005ca0740700043c01025040800e607400c000f10000c0d400341004079030f400c4000586000586078007020500800d060400d150300d070391074a0302003401d18428010843c03086104010920240e034607140100501c08100c24807034200662904240d00901850300807562441e0303803000005100e0230603031280c03880c010118510400c1d00d91328000f01040d0f8401080200264100c1c0d802400000c0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 921678983 1250 921677733 921677747
    0x3140423070f090209120d0c08031302041401050910031218053619050711010e0606030f0106180b03030d090807170c100203090f0f03030601111606 65
    0x380400003516010781d61032849000c0245aa40000030542d00401c2c3d002c181d18003d000720b5a0501c200d000340207030041607800101036051181008100301400b1022501050004260303440c0c56a0282040002843c10028000009424442c15104002d1440000c0883c44143c01c48400c0304d521851041040306001d10980310a0f941d440d9001c0b4042d5040400141550f0356508103540801e503109d400c05002c1551701c10010300a00b1940c484017500314200f8002c01c84c074034860125450000d1040000e00b80c0b00d49408a0752204500081c000a44c00c003080707050134440c007003201c0b402000101c1c2115201034001e15110b082e40d509210702c414011200d416a40804c0c000c0c2c008150010006080c1d80c502816410200c003100d0300a441910a00c4010800314100a052440f101002c0c00da03d0039241424941c05c4030f541d40780600001d600117181c000c0042000b15100700b10002d942c0100000790f41d0714404601c0f0b0705aa07a0400c851150014114078620010903a0118140e02e5011700341c0c4110b07400c2c50602c00192144c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 921680233 1250 921678983 921679043
    0xf0e010e0d170a0e06040602123007020c0d0f02040e0c0325060302270f12100f0c020a030f2a0314090a030209040609080a080403031404 60
    0x10324030041c804005400d030790198030203600703449540c2c0c1c464807034038001805245030b0501c2c2401030b01d00f00010b12100b50005000000d010700d9070401c640c0e48070111608110340b9281c0818482c030800c0a015031048085c0451024465501c1d40d080f5086140c2040404c0266683d001010f060660031440110150405800004c1c0d0702d20442c0031078403001010004a807401901515000413200503040c0003440c0c90f10200b40d1070051107035242c00c3d4281290601d01821403c1c0041c840c0e0900300351020001826100c0b00300c850070003a00148809030380203406030f0403900d0300303050b11071130280619114041100032164801c0381c0b5001c0701036000b0046001c5569080e0383e43c2d41c2c4c1e1900c00c01480410740c140400302e0340c01e009016141401480c0c2d07502c540c650307203005031030740c011283c6010081d14140400311050310703500803110072203404440c000304988460070001d00400c9100006440303540002030201c81d1541091280d40038910a81c1c003000540300060031100c0c0da501c240c0d4003c02d05d10507040003100d085c01d00c000d40410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 921681483 1250 921680233 921680239
    0x405060d05120c0d020c0a0e0a090203030a180518040f0510060f080f0f0318010e030304060f12021e0a050d09050c0102100e0601050613080105010308070c060f0e010e 73
    0x20321821a00c44901e040c0700030002482860001550541d1100700f8410760403014860300060a0041d40c2100043c03440350f250050644c0f2440900000d80e1461460b040201c0460b0083c003502d550748891100245440c169040030300074440007420000b12030810300d08103c10700c4000d0ad0114016265542d803104200806102603036980304500301129500c2992089038000c0c4240d85500e520301c6d00d01804942000386d400e070511156001880d8500103903502004641030080c0b0401415803003204040180c4038401000d41d101d4051101048c0480c9603900554810440503440d02e03184001c1d81100f6000045e4802c01c008003000e07941288000914056080c058105500103040072810000070701107081c00c58000020a41320b035800710748845100c2d60180101403100004030801d02032080003480d982c0d070b900412700c02c0341e018410000340416440c07806c4101c6800717800117030024001541d6904048034a900061002d6959031150000054011300a011110030a9000d4842c0c3d40000014001910701003004d20070070750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 921682733 1250 921681483 921681499
    0xe0f0609090709091401151e140f0d0515061e0d020c0a0c090b100804150204030515040314030103030807080c09121e07181a0d03050c2802040506 64
    0x1d0300c2c4050f000c1c0924030f04400d444605c0540c50606081032450b07070a0601014841504c03a80f2a500d410114080890b1000e030800012011544821803218414401c0ca490b010380e000c81c1d806520366241c0c01482c010000e02e40c80b12203103642a000c204c00c034403d10b402410100f104086183d44480450054680d16201d0f031001070510481c80030060901402110440f00760001d58000c1c00300040700c0c80750500050060f20b10702840c56820502a10581001c0d0002d4800782c0340880803070407010503404440140d58441c00303540003d00d12440c1d4410204c400e40d41140844c60300c90400380c0440b08207050324100d03501940c85a049032a8480c050f01c000c140505040f0807060104404507940d240d900000010804c410018110a620341c2c0c001c2c810b484442401121039000f1460410001c0c2c80304103104c040c006041c20000b091521141504003110103000d4a6402c0b040c542141b50506030800c020b401c8120b0f42900351802c00503c0c01522075000e101c0c0e140c0301440301a51100101600302544441d07030018010b00b007a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 921683983 1250 921682733 921682739
    0x100809010906090b060102010f0b150313020303041d07170106120b0a0b0a03050a09050c011b1a0a0e1f0c030207020918120c0d03090218010608070e0f0609090709 71
    0x2a190f9203001550048034103030138000b00c0e5909118200040307a0a58042049000c60707000100d08003200a1181400540800429240024205294070a40e03008081726503842c2c0d02c03a14810381c0c0422244216612804000044c030980c01542e2001d240b03512910172501a03030070400c0550f100c1c2d583c040000192a03440c40c182c0c2c0d658441144090150403109881e544502c1c010b5001800d50f403005101e0380b480350a00382991300152000500d24440102400d142004078254080700e0008020441d0140240d0f1960403c3d08800760715002c802c1c025004640300344005010000c02c165544000d80030000301039a0740e03823591034003820b0340e21003003c030551442c0252030320303489800003003108406980d1f40e03414880c044d048000365442041007070104010741042504000012620549402c0200055818176484001e21811543e51001c40d804030000340d00e22b09002e50710349034020080c1500300c0d404008203401102e4132400e071800201480d0030303401c01484545448103000c2405902d0701d02908000c180000f401c404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 921685233 1250 921683983 921683993
    0xd090f0c06020f0c19030b1807090203160c051209031501080601050a05091501051c0507030c1d06071b12080a03110f070204110f0705070302030c01020c1008090109 72
    0x41c0a294020324100c84261020780c00c3c62941e4081d0341c440c04403c0828046425540040000c0341c3e080309001510743e4407840c0b91440050008a061083e010b00040860700e1100d59001c1d40c0515036000c00c00124010b00300050301c0284400c0343c05481ea6215008049100400c0c0f802031403004000f9040e24184a0038540445080c00b0030b07042000d258200318014015414a0729030b000c010b01080303841030141d082c98007120a0a40d0350101144c100000059184842d0312810003008000c0d0820030200940e240220008004010380360310040040d4070550300f5142407801c008a00700c1d071030380145080d2802c0c002d030395400e4035882d207401c945240c0e40303e0101c000349800da5001a460058000c2071500d981701041c000040844102c5607004800c01c20912150013008401c0054800c2d0540c1039800103051405050307040715034000ca41e6550a02000051340c0810402c1c00b0800904a034030a070100ea0981c0309102c0103903107034106008099080315405a01d04c2e0b05900c600d140c40c0c1c20150300800092030f00b03003948034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 921686483 1250 921685233 921685253
    0x11134060201091202010c14030604230613020f1c0b0301091b060203030121030e04110423010c03051303080703080f0a060303021e070f0e0103051905030d090f 70
    0x40031000d40d540d0070141d41840502c4144904403036181c8020092030035032090141400c00c0564040c0409080400090000e0300c40398010658610210320b00c0c00321050700004840741d00f204131084c80c080c40312152820f100000341d00958600310440c9103168102014014080d0720252489120350b94207854100e20041500e003032251803011402480f00c1d000c0751408507001c2c0580d4105a00890866104000400c0756a234140e00080d05e600b40c42994810007840e03824110380001298442590107480c1502100c1c201034030030000d0046031881440044072090b1007100900300d00700d04054a0110348030040c0440047d2080b0300405404010080008446071207072655041504050b0b411004204140d007848a040003581003654000410707003042c401c039410350340c0c001c0d245d80051000f0100005100400340c1d5251041c0902c0c1c028144c240c51150000350344000300841e84400b03110076240d074001c040724821280480710403c8151608000294905403010015100030244010705403015a00074411000240c02016 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 921687733 1250 921686483 921686489
    0x9040605040903030b030d08151c1b08070609140d02210d08061012150e0a02042d030f0317160e010c05060a020903010902060d0207060506011134 64
    0x35002905001740b4007418034090565105c8410b02c40c1260800400e441501c1481418110645004501025000303070b490740990500d42c0242001c0010215040610b004241001114031020483c1c03041580d40c0b80560b5000c00758040c10300240d80001d080304080c00c0c5107031240011840606043c0c84003c0300562500312100c00c11024807650031045038000b4265100120903008442161142e86200400c02c028051000e80d0600d07504490321a44180c0011098000800040840e0a406101c600d0301d002403100035072060151180d180700c054003250701c040c1d2094081c1c601c00c40d101c000900c02030841c0c85900da80d10319034008904102c10050340841440030000d0b0103000e00f101c2c4410f04000d40c400d40001d400b031040800700504002482d00c0200129500040040d0440034001c8010f9413941e51401080c09000703640d0010f50403450000340c083c02504107a004100c0c050003040c0c02c104c039407540301c01100e04003e0001c81200961000c0c0c20316540111003603000d92003184441440c240d90a02d401c10320001c00d403540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 921688983 1250 921687733 921687737
    0x1030212060f011b080a0e060c0d0305040c0f0f0e0114060a030b300c03010b0f04050a240905150d110103090b0108010605030709020906030f040309030c09020a0f02070b090609040605040903 83
    0x1b0440060300ca400440000c601b0b40c2c101d40c0306081000c28001540c5e980c6110b0355040030103442d035022505015003201108003401201c403d03105540d80362600112140901d124200d0b00300045000000d80c042c8049010145c21001481c040c81c00c26600001c801421190b01071540c040100411150585c446100082441851040650a44000c80c44090800c101002c2550180e410700c209401c455941d8544801c01c07140454001030306031103910740000100050301aa00950481014521500c0d00b614080411158022414002607a5240000e403000403400c5550740c01c007022200c1c40c3c0006d0801c0380169058081031500046218081d2030b10040ca650a0740f00c001da80e50b44000a00c114201032040c42e000d0070000c60250700e464504408a02e1601c4003d00841102c0320840204082601c1844030800641d004103201c2c5000d0303260900701e0000c0d440201440b0208410680b195074040c0041024011501d0240c1001c0c1444864000c0c01010b0b80844440360707000c3d68404010400d83d03201d2080c205118000c0e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 921690233 1250 921688983 921688987
    0xd020111010e1f23071404150e0a05010f030e030708030f090618060f0901021615060807050a0e19050c04140d1205030933010b13090f090503070303050702060601030212060f011b08 79
    0x2a20f00500314107140c1d902713a03008001200c0103000380c1e41c11aa80440c416001d290014444607007404150850240e550006c00b88500003040c450060a4904110b000b0466102075800944a030880480000135850550b4a04c1d0403403400101d091142065a56000c0e00c00d90004d40343c2160440e1049010b01d1000c0100d40d66000b00f442d40c18018914401d900c060000e250003000350900f0000090701d400074510034010004002d04c00624185d070002017075850303000400c805015508003000b1034070300da4210340500101c2100f00000800705107040e0426103110307070304540034002c0d0070500101140e460b8002010310601d0722540c49003080c2e485611000390044410000b03001e90082d040c4010000400b01a802580546024041c00101c510448c8040040b0340c007440b00020280055030241d005009520009060380c000801e1000500d601038119900c66a4542d00703584050f60fa0130015000c034003468060100c0120301c480040d4140c180455204400300701410419405100e101310711000c044001c008903020000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 921691483 1250 921690233 921690269
    0xf0b090a0605011406040918020d0809180103031e091a03040c0602030408030d0b0a0f0803030709081b040b03070b0307201b0d020111010e1f23071404 66
    0x10311407030740580f80022454984801241c0003074850702540c01942c9904d540d8048c58280444007003c004c2c0416409054149800b8103401c0082840e01300840351809440001c3c00c0140340800c0e041c0150590341c9c5601c80e550a42c0c0700d008403602d0441c500c41c0c401d003030041c9100e010441c683e401080400100c8000c40381d40e41e0f031801c1d2501c54003400c09540120150340c4280700a0004410100544655440e0140e001408141000020740c0c41c80c030903444040720350414030011405110200065204080640b102449180d03900841a520340d00b81400d0b140301000000e1008040c034003030300042082c840c01011078001c1e98440311585990341c004d440c102d002c261066450328020741d000c0d108520040b0500045e00d020003070369294a00d6101d81b581614401d030700e55a0102c1c21a8082d460b40c0380c800c00700200030490710350680045550f078a01010303214018007800c034084410402c1401103143c178501190641450480c1900341031001e06015104d1424001c4004040404000e09000713800202000442a0241c002d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 921692733 1250 921691483 921691493
    0x3281b0201061502120a02030405090a23040308060618040c0c0c14061b030705010f0606021006030206090402030405151510080f0f130206030405070e01170a02010c0f0b090a 76
    0x2450740d00081a000143c0310481c006034011580c00b0b00d100043d41308554581c4050030403801d6103c4c0d6000350f0750100c0090248820750090760700401441001ca4507246034921080400c46007034404980060006950100240f100e0800d24080c2400c0c8100d500078940110b240400101613440c1c101c5128000707956801000f050061540609009142d2040140054040c0700c0c04282d041c0306940358085054030101c09a840000204119074025810070000c1201206400d1100080c0c030241c45108018420015080340ca90a540304800031a50300074451803504034128248406904014810740c0c86000d41d520b00040007100c1d90b03200d88079010f00b80b80060100c00400c100640308046030301081c1000070703200400c083d040060f050250850200001d4907490396907403405401c003000303c1c1002900301d00c001c024002000000982032080d6000a0207101841c2e88464008045421200303d0244590102d0071000255005581c425000d5010b041200900d1a1b0b944541d10440d800346da081c5000d51000500c181400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 921693983 1250 921692733 921692741
    0x2004050f1605040b090405040201140304050106080708010b1c0c120b090d0309080d1e090c14101e0302160308090c101d031015061701060503281b0201 66
    0x420302d00703001d8109400d05080c00d035680175101c1000c0c05959544081800d681c02020040000075001d6060b40d601d02c0c1a141440c041d282c3c52044510078866100d0204041c1418001d00c0345614015000c0c4504d500140c48060005003010b40607214005054400700c1e20140014108030940d010381c0b444105804d00c1100f56241c0036a480505003090324240301c0100040c8910100c2308140a100004030ba20750b2410142c001c0715840708859007809241c908035804115020100c203048a500103840720040c0c0f9460244034203c0c2017070410700e00041038245500e50500b00c003c81841908203d180040c14050080d500550304480d035481a00465070300001c220307011804201403404008241c2d202061550380c00700c0500143d031190384990344042e88400714521074404115010190300241018401140040180700c2c00c846140120800958010411743c1d0740b408000b0214125000e03503031160b14540e68a039480d03441e045001c500703000d001001840c4c1700c1c6410346401900c7d0781c500369144080c60111480c4000c1d08413 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 921695233 1250 921693983 921694021
    0x1c08070305060d080307030e030a0f09050d0f12030207150204140a240302090d1103060a02120601050f0c0a060203060f0d02211e06160e09042004050f 66
    0xd030a0804000c61a159001640c103103540c0303d450f850b200c3d203900400350040d00100228140521011490001165000c282e4580303684460f1504009146c03140c040c040715107090300f0041c01c440265030246000410054403690366520701e00e00141041142d546000e03104108854420b281394001c141480b602079410800c4a0750002129252940791521840c240c6040310200640403103c0314828101185000f40c04131131131032400600041d0811110300d02001c6010b41070b80d05030b00a2046900084250249108031660345d03140002d100f07020740d1160b0044a540e8481d0038400d45101c403d10080e14400b400b000100085807183c5000340e12464000c1c2031101807103e01000302e208102d60410036001d619402c013041400300605c09641d2187c4440b444051611005001c00091011400610781d40c03800046111802011885148042c17401080001c440029512810550121440000c140021007c0048649c580380620f0190344460b83c001c005000c40d0307011218600c0340021401049040c2100000615007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 921696483 1250 921695233 921695237
    0x10303090803090f01030b0a170703050f3007021908011a01140904090c03060b04110909070806040f0f0e0d030603051207050106090603030e030114070516060e1c0807 73
    0x92030f03680000204110121001c10b030515030b035072003e03004545481000401400f03240446102c1c1040f4103140581d607044622045d180c5008603850b6490300c1c000072039142d0503808008001040c0411340c0c5e604140c1c580051121007081641044002c00589480040420303040f4040d1881007036a10700001c641c251a22103036030f16900d007000503040109030b0f0401c004c2e815a0808680c0c1036246e02203240803c0082040d4030024201c2070174203500104004890b0010f82d030320b85c07094405000c80b044000300146180610b5000c070768011803005c0007440080c0f00d04401540704400420200b807260341002c25000b00d40d42c00c030060941a895410081e041c810800c4031102644541c501044002d2442d202d8540f2004084c01c0d80740780440000e4079000340602500890045c14400c2010055a652841e000d8039507800806518025420141c0d00781d040f4000415580c480d55080d1515840c00c0306143c0b40415403228950200c81043c0d40d2502d0200075101005880e044515207034681c50300f000241000303015200c0080c003a42c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 921697733 1250 921696483 921696487
    0x40c23090102030a0e0a17060702010f05040c0b160c062007240201020f0d0b011b02101107080a0809011e050403030509010e09042d0215071712010303090803 69
    0x3190340e000003200e181801628103c005098000300184030008151312108040326210000d00d48100302049050280c3c00d03940007000503103c890403000581300204ca014003000c0a48038104509421100105007604c050710309011803e40e10b03034484081c42926006a40020711070084882c0303034249603025a004c0d804200040410603e00882ca5441c00320601607140b800c10f072941c240f04024001d4059071840c1b103180c4c8602d512640310b170011600500b04064580c2c00a00d0100340d6001c07005100510301d4540380c0103002c20034007a02e08075055440400003241d44a552080960010b508442440b040f13070705602c9122055901e41c0e40710300050111050040b45e980b41001000c0390f11065401c0011901125490305141da103038a00d400c01625500400c00c0c01c5900012403200300002c1020032550402072008108255143d1b8120050615940d0341c501030007034200000040403450035500001901440384581c081d42d051401294003840e440d0015a408401200c6c2134006004064100302c0c003a001d4060304000758 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 921698983 1250 921697733 921697747
    0xf09020708041203020a05030a17071106150f040f020a03050c0423060c030c0a02040f02040b041a04080a03021005150105090d170f130501020a0309090209010e040c23 73
    0x1a100d103203e6801c010041c0d00b0020b04040c002d2080d0792000d03800c1000c1da9110380d031155003d000c100b01c940031340658001002c005400103001d8440200403c0749000104801e40d205100c01602000328683c01d40d21440b080e50b0340005994500620707450282054003d17880e084414009000d95002800001d4180e41c2400180400d503642c034503035803144035006100808640c1400100d00c0703034030404840e0007182c00009039280000342c0001d035855000b4820b4030300b042446403200344101203009071300601e800201c0410003006500c2d0248400c00c0c424200610161405030384110746442c16040a0b41100075130031035803191382845514412194000d4800308035243d500742440000340706118072401c1c0d6104100070b8410781d081c02040301c000502d41981154896991031580c02034581900440c1403603207400d402e024003081030351010800c00130031689078451480540c2000c40c200c01940101c134500341004044078800401d03598900a20313012440d2600c0e40307490b550341429491200d40101b80300741440c560401001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 921700233 1250 921698983 921698993
    0x3061e0312080403120e0a020307080d0504171014041401020a05271c0b09070602072c01090207051911040b190303051c180201050c1e070f090207 64
    0x108101c50102d00d40010a0340d114070b000d4a681032922409400c051800781160514900080d03400400b0f4000c07012160301d00d556460f055503983d400c01d01e02c0300107142804104003c03040d448150046161131400c0d40c003181e810318040401c0751002801c0c0606400d4240078402480b0000e420003014910980003035140004d0301d14080c0140c0705280714029241fa1507051045544445060310b0b10303e43d401091542c1400303d0600e00e8401064a54040d215034a4000100342c000b100020800110b40c3e05070040d080300c43c07514040008054100d01c0d608551591542c00c1520026052a03d50203021942001a1200c1d5141410752070001e4003070715440c7e00310121804001146170702c03c0605104c00110f6021541e24500f034041540100b014100720b451140c50b51020007059089009815803a0412a05400c400c82c0e0109582c25141c3c0d0006000700009514001030140d440f51009140c0800d488003101c4104002c021201280b218298050301d00c0d4001203418852071009440040003001858420360408106480d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 921701483 1250 921700233 921700253
    0x150102030306060a03020d050709080d08010302030a0f0804091e06050906090c03092d0105090d090308030711390f060702040e0303040c050f0603090d12020f04030303061e03 76
    0x2a1500c210b9000c04c2c0c14480e2846901290010112030809204904090b4406020090a402610260302a100d003041c8118031807882507040f02c0d0010000c0c601d1600d41c0d11141c0e0200348001c1c1c10b0702c80260410010524000602135085001100411540c0142440c85030008460060300280c0c490368000050050b50f80d0b51246171500306855965032541e946030180c01e0b501e80307120011980115072501100200070007480700000b1400706040024010b69031345440c011380719223402d1b60745408102c5000080c0003003070480300a59404200790505900500701d070b810262400c540c685981995801691100d902e0105050010a504089840d05900080302c480050031030940f65140343e014000200d02d60013503644a402c4080110a0142038035940c1c189404d18035525440c9020f600e00404078090000440d050680c1203070f00c03484404000d80707140d04600c2c404a42c1100810b03032100c903568080c04150050110100200300642c426100060f2842ca0642c542d00d001101324001120040750590400224250700380b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 921702733 1250 921701483 921701491
    0x20907111011041e090b0414040f060b040911150306060912010b0a0e090c0306010e0f040c030506010f03030318080901320306030c0301050603031b070b0f0306091501020303 76
    0x700407804004800c500803a80c012544450014000080520000a89030142d1801d451300c03101c0a100e2820804c041c0415101c901000d04e48050954000070085a186819149174622409000c02c0714002040010f081e0381c07818009980f5402510780701c64071450721066000c00b184181c0784290451512500081e03650150b105d1450040c1081c500702c1d07200c1c0d00213512116483c0300c01404268803a0f01c6a1540300b004404031582030581c454200d52144501d000551141201d4905032048055561182d2007484c1c2e2501520480b030405d9407510200c00210b0521400307019004260510300041c6c51401c0080a54a080000ca490890501010303404103840d031085990001e0f080c28200101800007100e00b000e40114190103120908a252a204010a0000a60041208408541d0000031117403c0608803a401e5540c0e0358168000c000210010440701c003039a03801510582514200e999410240a40354000c009041c000c034800020801c82c1e1500180680d00320491205040e4201c0e400c0002075a00d200240c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 921703983 1250 921702733 921702763
    0x3060415060221040905010909020a142407060c021b0a030209010323071404050601170a1d0a05030d0c0507030c0305030c0403020613141c02060a051908010302090711 73
    0x800f200da9425426011a001084e205800304003942e958a1140c00421004070100d11400308a400061114903682191a8800009010402c8603000704041c0d02220005800055400002d00c0b409001c1103c1c3c0c810036540d48041c2d0081d011802d4450306000f4144201418544224260401030000d40c03030307002e4054103481e40f0000c6806180c0070180c0060b00050301d070722000c00600c80d0960100e00074415400746c00800106132014481270302c840005485400d0450b10031243c039680c50380099a80b40d540e4200003582c90841c0e01a040c0c400c8903240050038003420803030950786a403002842c0314524546201c0e813100320704d0314038119007090451340d4000c0101209100281c1001400700114500d02c200c400ac84009680c014a2103550780c2c0c1ca504440a0901c1900c40c500180c12160305e0a045814155401c624510155100d449a50341360341c00c02c4082d03001803032200200881407207660f016111b03180a8200103140398a644800e98554810881e186600405000800101028400c1a84000601c61481000c40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 921705233 1250 921703983 921704023
    0xc0c060b040e0f03040e01090501080604020d062004080f151501171603050c0c030726220b25020d020a1d011202010207030305030709081002030604150602 68
    0x2070042d0400030422452405440a202144800000200304071190400704030202e03070f40c030050041210801d2140b240240c004000003001440c0810720b90758400d1050900081481d1015100c0c0b0702c904544800c0344480b040003c00303001807441008420300422141c0000d00d8030046500180600510150526504480341d002000042e07003d1078030703403840b15142c0c88030614a02d8218641c074203214280d07444902092500300030031000c0548200300d40043d10707000c0c0114a0401c5c2030f51001c408a00001c3c07680402c12640d003220301040045070042280042000a2204c40c14075200412801c0c2060b502030780201d0b0003007018403003d80600d45542408000800024500c88a0f40041104c00602c0d210003944000c2c8004d0101c1d82c80d01c1a0030340584400c2c1051031241903a01d03090b018501201150780680035134441c000400001e0300c01d00003141c1c086501c1ca403490300d641c0d4410105240121202280000940210400c001414030b40b140c0401e0340e100058600c881454940040d44a0444040b03101d405510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 921706483 1250 921705233 921705251
    0x90f1e060303020322030b13152c03041701140a200c010209120607020f03072d05010606080a11031513091401150501050301030b010509040c151d03010c0c06 69
    0x4017800e01d008503004900d0481c0c501e8540f451003e1205a54012144661040e500002200f514400c03000250324800e8070b10b48803640707400700f19504d1488911850403440b04100c0400d070602c00b0304a030005980510004640c0c255500c0f20380e0301d04840142a581c030a071500490400c10096980103500c6801400482a40c411490808501a00c0307105101e58000d28a20203440c01c16100191951242181d68296016a1900c40b01c0948911440d41c0103004040b00c588200310b0000a012072805510180a1054100d642e694540e403e440c6180d11000102d030f0000c040104508190140a4501001005040c40e515080300248002141c4540b458022009201205999801d55200f0354250760018050300b82c001040c190a40a0480246040700070b000d05840001c895000c1d0301524103032a4081c600c040142e00b040c040c8800c000c0024010b03100300c5004003000030020201d4008120811140d43c50800045d00158030000b4455048107090090380f4190548244550000c00c030640c4079404240400c08400b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 921707733 1250 921706483 921706537
    0x70c1514030c030a020715050f0105030712150e0f120d180213050603030f070f060b0906060a0804030905061b07051e060f090a0b0715051b070507090f1e0603030203 72
    0xc07d4081001d203141c03501d021311a542a20754140790480b001201101c50403a180c140110450b0403c480c014803d4030f400500b001c007450b660300f104903080c42620860318980c00d00d01c0c0365442c00306e0702c20020000c41800128008480800c0c003625410380c601440280d007958050b07002c01c2d080d085402c4044540d560f1000852210713941032003201c4405c90550361081e10b400d4035003400000700004082c00c8034a680b40200b50320b503e00700400c01a10401006001500340010300c1c80955401c94020021020044040808202c5a8510014000c0c1c0204510381c9481902080d800b585030030010382001d841042e044140a1003028100c850400c0800103a07441c40d00ca80d01c914550382da602134000c0881e03106a2011000c02c80a000401401d95140108118030401c60764451300c00c00c5850566285003450708081c0d1404219603c13070300a00181e0301c06c00c22117402650b00d024283c1114040e00b403040000340c41c0d40e56034580e010074a8450b0754003092218100103d03455640c01039664400d06070203804000030702900e001041d07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 921708983 1250 921707733 921707753
    0xa0308130507080d2d17040c08060c07060509060f0a1e060e070f050309030901081909030801060f1107060309230a0b090d1211070c1514030c030a0207 66
    0x810000b00b152012a403504c0050300c038190030701400c0e101184490300c0e20700062001d00043ca02d010281c89101e48100e4100e480e03510340030020410340300030441740d0f00020754520401c0000c0c400c450034020a600c2d0100c2d45062070035605d0180030b000c1c55911240500020070760310710b0703110b4002018000000348807028032407603082c15002a10065a0b10b180030400119800d03200002c510524a0f562030141e031080629003a50207010030f032910201c540c0f0901513104d16502a20300e964000294000e04003200317075922080740507207480010440c0050743d0704004210b00d80e042420803030011040c0c1009038080140e400d020750748088a1090404140d00c0703030010010320400c51000d400510781c0c030b0b500810a0100c0060780d995031a854000b140c401031540d00260203400c000c9611a000c03002c80d40e4040072081410350003009840c0c01c3e6a03084942c3e43c108071420000300391078240c2000300704426408410903128503018110030080e50160a41e91000c00400c14082d510604aa0340140810801a00c400250801202032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 921710233 1250 921708983 921708989
    0xa021903150509180c120d030c03061e06080912030609070e0904060b191203120e03071104050f04020108070807090312020f0c0102010209010e041a060a05030a0e0a0308130507 77
    0x940c80c4044c045645001d1040740c040390030f02002ca80a550740742c000e0100e01d002002140c212904400c02c64000e00788603070001200001145804205c280e1502490101148500e01920000a01400421525410405680c0d012201402501c9a130103414002003141c400100710b50b00c10601c100008001e140903042400e89010b004d460901e1728074141c60040d0061a80c0030555100351504845540c1444103082c8000a8802124000d80c456040d07603001e03110b03034030011801c045071030b20344203103010003030080003d014042c0c018940142e868102c0014802240c4000c4d0800002103010420040980d0f08000c142d42c0142d40e615201c1180c0d035400e542100c281009800003481c00e0748031000c450119a0000307030040a07030442000d4580041076800164201d10a88d19154007086c0d1000c40001d69241940c000c03c58079059500310039107050000000f942030340c890122140410008424003d180c80103129694140c05080000d100101c181d4074003500501c0020107141200c002811420308011043c04480c0007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 921711483 1250 921710233 921710239
    0x60306100e04050a1b080c060a0c03030c031113030209130f020904050f0601090b030c01020a0c060e130501080303180607080f070302090a0f0611121b0a05070f0e0a0219031505 77
    0x7201c184408002031403641881181b01038400c40390881e00380d160000807541c0c4540d46440340350a039400c2d592f054010b0031120000e03400b03043e5914440c01280700c4a41c02040c085070395071440c040e250706610400061500243c5200d400700d00c1240044c00082c0c401c110003804503011507035550f0543c3c85203001860406480b001030968040c840c00080c150f40c250300603000b2040c0440545d0400490364004a950351602500a08100c10b060402c103c01030048a000d0344106026002d000000201c4d01c004003641c1d020790081803a98400405c01030908516650340e0640c402c02400340401d420400300041080801404540360100c1d0703000841d02240c0298125501400c014040d00c41c9969143d4084151003039030301c902d00214452480d180c8503400b010030310707001001c0c8109100e03042c03d80501c010b440000a0702000c8820780700b07c085000c04a00e04000100080007860311041c83c0a040c80c3e80703090007401c040d05204034140107101d00360f41e40014004840140e50f041c5400145000c400003100d2007108250b00c0690 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 921712733 1250 921711483 921711503
    0xc03150f060b07081c2405030a050601260303010f0602060105010c1106090f1c033e01020c030c0304030303060f060518040216050a02030d17010603020706140c070506060306100e04050a 81
    0x80100320124100d01584d1440900704807880c1d0354010300d901c544009c000100545c101400610030741400280315948445280c0141c0450110b400b5031918680c030a0300942c1460302200d80402049a04200702c502400c828a0044410402d075a5030900281c8040141c620503403012840c000182c84450703000d0007202c8000d08085256680c4521120000304101044c5c0006685403000280341e8500f6542c162120250b0080803411050280c0050000a8400c43d040c4c0300d5400b048601a81c03002000a4131118070130401541d41e4919500e405421181c19a01c500140c10481804011190300803003528039a40184800c102c14020b0f84000038002e10071001c0c414090380ca000704203000d1003400592a882d01d0300c2581201c00d174484403642590311800c031004c02d0b11011120303001401386a20a8020f494101e104030f801150f8240d6541c41d14012401c01c65403441c0701400406c020051010030031032942c00a000750050a468203180300520203003220b500503900c0b003500040101b400c1100c100110309180742c0082c180c0d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 921713983 1250 921712733 921712751
    0x1b0a080606091807020d0801080705040b0d0b01030c240e01030213080d02011401090501050f0111010e062e050f040209030307120305190605030c010e0d0c03150f060b07081c 76
    0x82c0600c000384c44441c0144107452580541d203008040030b0b416103281b030000381b1500e80307002c0801c40074103150a21103402c042c10b0015040012082c4042c1c0e030203584904201700740142415040d00004125140c41004003000480c03404082c1d80040811580010130b2178050380c0d0343c1e84810401c4041000d9803003c02c1503c5444000b100ea1a419404000000c40050a43c003859907924014810b450b006e0085a52114810072284011360184503e1041c0007081000030580d03141c6034286504140302101c0340c07981340d070701c0c1c222244d64221405984068420b030410580e00503070030207003c80c2c4180c0340310000a01907580001d085d8030300d0358108103640c071166108071308240d5102c9414000780601807e03207996522078442c0254034808481c602030b5006039400507000309052036404004558140301c4072106500920801e4242020031030641c500301c061405600c418011804128018040301d91070740200040324034109013801010301c504200d07000c0da50880309460702d0b05115400003208002042070201d4043c0380503003072 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 921715233 1250 921713983 921714019
    0x307030303060611161514120a140f01032405010b0c0d0f0f08040809060c0616110c0d080c0316051b0d060c050c0d020a0204051b0a08060609 62
    0x11900351181d640e80c405036913508030901c0c1d644e101c0940e00c900d4041e85c0000c082c00340200c0c052039140e2001c0b052a28020b2000180300d1402d15070310080e45c42002d00740e10801c010000309d090040e040001e107000c4aa01592070422617100707001006000007868070360301c004107c13642246090380c00c0301e100c4070700c00803c12942c0d074414400840d40400c0052544d801603130f031500c004034024081100032074501d40b180205041142d030101e8034882d006004071901d15061003040b1458440e03034090101c0651080040103141080300d070314019210090402c4040260000d0031103081d200120300c080f031110090b41c604a00c1d900c18604a000b50103a05031110385480b0200382034115a0040d00003040c60b81c00744041e102e403450b6019003000c00100418a640c3c21110501c40360002903955445502004258074200303003010281581079081031a81c44001c0b0059019850803c15413a1902c40c00390081d030860741c20440040d10fa00410014014440c4075400c2c42203140000799107899940854125490050400c0c815a0381c000724 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 921716483 1250 921715233 921715241
    0x71e1b081509010203040302070b07080412061d0714271e09030414120c0913060b030309090412091a0414030d020c040e03091c03110102090f040513020307030303 71
    0x800c0c603802003100e0200d00b10301c00602c00c1364044d40d00766010f801074906194140119901c51481160115020480054020460034981080324440c2d2004502c42160034012a8502d208134220001a08242c4080003680c541040d003140b01c00b402d881c4110602040501c54501110000750404072200742d13410494907880703a402d20700124225000b400001d07101c018401c0e50b81d001e640200070010364510101c103454640100704240d901422012203019000e000302050300005c064a0150002a54000b421304010841c001c41c4011300007600210300300300d17046001555005e0044c10180001540c90100c00c10980302d0307550071025040389551540d41c00038100807011507a00500c070f100d81d20a4030222612240c030b800325014441048560050040c403040104000c010f04508500801d9407000b0080720205485a5642030b09074425940360100218940c00c0160000342d40d19541e411a03481004104480d980b0915004405c0f82c0640d00040c6995500d401d0702c41c1e11000003400396261050f144000304141e81a00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 921717733 1250 921716483 921716503
    0x207050601060f050c1914100615080907060c022103030601030c0c0309052107090b0909061b030406091e020f010c031413150305060411071e1b08 64
    0x1403902a800c0c8440811101e41c0501d512204203a08844048280b1043c0341d010005c0060051f80400300380f078412200145410200d1102100d400c0d10350303204020f06080034100c1c01c0d02502c1400c21032070030b2500b1840a03840f04258003031030042c0800303482c1030002c2d03480d500c0e000440280500f6015424200649200e640d9130021904540000d0404141700000c41c880c01d4450f50389541900c81900b5181000200104030329034408000c51901032006800328507008002c600d004154600001806146c1f54007070204140008051f040d250740200140100352003a44803041c2e07031080400f0a50780301d849515042d0301410701020007030006120900324004c05086214000b020342c0c802c640c0b0042c0e010090f0015205103110520180100d03008403648071144490000800001d5010a4080d04450b112031001400c07040784a824000a5a280c0800c0440e051509c00e00c0c60311051031001d41d041804039952030200961803c180d000f003054405503201040142c0d402c090003441300e500c503003290382d441d20b01f05030361582080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 921718983 1250 921717733 921717737
    0x10e03070803010f1d070e0f031f060608070804030e0604030f0311062a0705070e0c19020c0a060f140c0a02150306031e12070b150307210309030501020705060106 71
    0x11000603076400d26400c3c4405c030f1102d180c052a42507071002d0b02959016041c0c0d090365003020104441c0c60140d5000c2c0040030b81a1003568075480050011080d00c0126580c68000c00107000c002000c0c00505500200c10541c065494a01040c2e00c0341c0700c4002c50b4030fa010300d41c0010503003030258250604150300055005980042d08084606550721102080f091484480d8000d03402141c9881e00c0400e04960401030220f14003a200320742480340d583d12071201c0c91030112082d016440d0085a4801104541010b02c103c40440e0301c010304013154288005070030310b0103501c01c007400d0180003221060300c607000341c5650721140900c0c4c004584503009003000b16151201100d00f02e21a03080102d288181131180401e40c0e004500c090018010035003410b0000400c0c2c1e0f03903845100c5080c45402141404c902c40b101c010407419204035405182424011072454900c00e0720b610b20b9200341c0202c0028042ca44610464003468001800214520545814242e03450242900090610b50000564005003c030015849040758116 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 921720233 1250 921718983 921719009
    0x1c0311030f27010e01120905060108010e06010602010b0303090607150f0e010e010212010909051510030201080105090601021f06050301110910080405070614090303130317070c090509010e0307080301 87
    0x550b080c000d4215200c00880c00310b080c0704406000795102e02d4108404018000c400a0a41d225496180c075001090b8841851a03450705600c0b6000d040600c1701d5401000c1c240024081c1c80f0394840042e403640110f0204034007810000c41c4803001d005052481c100300c24044001040400182044a0301800441103e94402e6086c4060306210340070510841e8070312a03406801a03202d900b020341030005480340d040d0a6a0340d1103505a1345000e10340c203810aa0290a9030420f07031415624610000d03204220503440b4600ca0301c80b08040044990700450650032400f0001c605a2510700c168950200810302c1e508034540540ca41406040201d035554000c121502c0f003104c4e4200030404680c021211b4250840c2c0040c03407600310f00760400c66a80201d05920900502c04d025501f80704103000400c1c915001804003000c50340c41008100213002c0810138003600380700031020003460100c0130340341d001e52084a84240340c61141d9400000e03031041d00c203500514201c000401031307a90ba0081400c004050340c00a010f40000c000c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 921721483 1250 921720233 921720277
    0x2511010501140109090b010504231504210222050a0f020403150209060f0d0212060102010b031b0a03060c0503191a010e210a050105151c0311030f 64
    0x160301102c00c580d810594400a01d81d040000310300c0039051200b0324034103202061001084007404015200c0740020401d21001c098802041040100210110705030780c10542004140f01030310340b410788030080020b4145111a130401785e20111321402c1170403200c0003030740c0380001401d115940360350040e5000f142490424450b600c0c6078108007007244910300c40204408448051030845140607000f074450703814010801d0381004031040c060000360f40103405a801c41c0340d001039074400c004110240300b40c000400b803000b084040454000b103aa90b2003000080080c1c509045610101691240050b10166602071424803444494602c0600150401d9442a14482500404480b80c0740603210341d1800a5000c903060300b04203070510041d00e00e07049041555030004c80c2441c540400c081c141c91000e143d4100d403c000c05e400407990400c1d41c00c417030001c0c084440d00750304120090306513900c15408100b0020680e50b031480d01d220515060354103c800002c0310b14a80000300712a2212121140500b20341c03988003101302001f0f42 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 921722733 1250 921721483 921721499
    0x1b0f0d121103181015080114010e130215070c030c06020f0a030807032c0c01030e03040e1e0412080105090421030605090a1a0303031603052511010501 66
    0x1c4101900007001c1c0900001c1c008100d185000411a02c6038026a850714001c03480d1401520b21034031049020107030292040105000034420007104c2c100000004126505007428105541005000e80c41d614202010417015551084001307a051010100a1541c5001c00d1030000a209202d100039100c8800c1d178a00000c14038001314200c000711003460041c014408007941d056440a03406400007080580e10550300054010351b40004200c1180c41000c82c1001c42c031000c001e4585604030003901d0406d4100080202c20f01d500000b17881c20340f10080a61401c950f141c600040e8854080c081c0b001010480d0420303c418005503141d904240c01456682040a80e01c960510003e0002618020040302801720446690725064845079001c0c4000d1402080103681c074030004401c0780c0c0c140c0d0500d1102d82d440c0c0d080e056290080340320710280c0c1d0342030780510b0441c80d0181c1d4000c03c5600c0800c050b0145621400040c504000142e1107540c90b50026a030510b040141e00ba0051107400150245900c40d071800001040c201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 921723983 1250 921722733 921722741
    0x2c030c06040617041e06050a0e0a030c1401110f1c0504030e150903010c020c04180309150507080304051e01050112030513171f1a04021b0f0d12 63
    0x35086880780000b0101015052080c20001082640c5c1d03255207446840c000d44503032403d5a11a0b003d850042001c0c00c10b0000c201c1140d000440300403160740150022400607410140d05030a10340c00a00c045100105044154050078980d1070703d03030b441c85000804d0903044840001400302c20704180000e28000c00804030150803900161006400307d65050b4400d440d918101f00c8040c0e080c8005855641080030410200e030940b0703400c2c00c4250250f008145003200e5414035200704241ca10383c008900710700210360b0700d011307100c2c2041d809482c111f41603420988c01c002d4082c40440e202e0584c0000010f9491906040a83e20354488029503401560070b0001d00380c0802d014041c82d41600e442041203444051075a90990782c59205015000300126003490004102e40305001010b54400d69101808000b44001c0708c960417420302e075070303d803640c1e514107644413403404001980110215410703140141e075040c11440d004c40444035445841e080e441510008200c010000c00d00741c401c0c0000b80c491a03075064030900c0600c152 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 921725233 1250 921723983 921723989
    0x3020a0b06180c091f02070501170f0f1f0306020705061f060309031b0302010506011b4101060f090209180717010b0306011229012c030c0604 62
    0x285040e0011030b0810440c9001480304881c01045d400100c40b0413181040d41c03400c1d1401c0728002d40c0007003400304400d50300440d04100d40304c03a0610b02440d40c5019554030a0169020b40f41c002c14035140000143c119071201120703449a814004903003600d907540e281c000040d43c88503008170f03101c0c018400803c00c00c580c46445552070143c0301254003c401d0800d8000c500400d2445020b800308019801e442884044c06c400c4001003e001e0350010070715103000000500740c803880722010031203542d141210f0804126088440031892848440003071107660010065403801c0e072503400c2202d091464010546d0404415444101100c000318201d0080c15034030078059007203005455845801890f18605000003031240c1030000d502040504000004124002681e80c10080076000580046800801e228042da081055261003140d060300500181809000700a01845070700c58001c0907200040d400c00e00c50380144111550001030440c4a0060301280141080103010010346034040d01a090503803915040c030350110303019 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 921726483 1250 921725233 921725269
    0x40501021b0f1b06132306070c1e090c020601080f07030b06040c0c050706050705060c03092d16180b0109141302070f120801060c0b040606080a03020a0b06 68
    0x80081507007583c000350500d400300540c0581c0c03c104981c0503800150218010381490720920103d000c0c05102c03100241003050405200d1b00c000e10001d00000e09803070411059a10130701e1064000c5881401010905200e50044082941040080d511065002401904a44060084441c07071a1078280040d210f03005408050040e0380c00300c0c00650107040580288052101078074101c903030445d09885580c2031615a420040c00240700194600500400b0098a90070905840e1102c0c50350a00000099171003008020000c150020710055501aa0194001030440e504080a840b403103040c0428168030711015000d42c075002048651684051202407140740c082c070f01c041c0c44500009080c800318a1520401c050000c0d03000d00c3c0308682c3c80d201000c500181451502c502e140d01800040c500d02014142c85030f00001c01040300c40360041207526841444151016000201201d1903111420b225025000320b411070310061050039101d0007090303400550220628060300e9407480c561202e400308020081d05d10010700d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 921727733 1250 921726483 921726493
    0xb010207060e0d0323160c05011403010603090f020a062001060807060815030304031505091b0d08160b0105012319020a0b1009180830040501021b0f 65
    0x10009004800709101e00c0f01c0c0c2c050042c00348200e1a0305c0d05860307108041c2260507182d0b1003010f0003040a680c3d41c02c0e01038102400e1819140c85c12042450b9a8001441842c08040e103d181d401d0a2040c03c1e076400ca010b6070064010521207403640f20140901002c80129040c803002d0300400c0341301d44010f206003400c0d2010080604010740c600a002c69150101821805005001c1014084a40d9003080140011489100c0c404ac0329088650140e0807a44001d20102c002d800074008220607050380c00f85e400f0815411184a032010005050981c980d0103070403a0881c0203035400c1c41c00c030103200700c5d560340c9412035600b60b031041c1540c22100d007000c4000750b10010f424000e4005100d460304a201070302003c030b04151b1520403141802d0040c1c41c0c401100c1c8054034101155644500c003400700c00003501130b003400d490800a41a101003402d03a9a001030344210051401d146c0211801030b24640c0d158882c95052840240c070840c01c50400d814070314002e5200344610030152001c07a51420001901049006080e01c950010f81 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 921728983 1250 921727733 921727759
    0x1603180303090c0b0703080f06060c10111c0204080f19020607060f1a0a050105390a0b1f08030307110313030c09110f0f0d06180b010207060e 62
    0xe006020b418108440c410040d40010034454038030009440e41c04d000e81d03078045941c00e204020102401d006404076028440801800b580040c1c0001c000300e004080704000108150303200b0300100a4001d16884e603010058102c03140c083c13035040d50003410035500c1d9541951400c0b038000a484e9070b25140c115401d810b0703014400c0c2000c0549400b0001c0c054040c0145000304030041c0b07001400d41101c2a0384803c0500d1181805075000b035041006100001d41001e080c4107140c4205040300c0041c0080340280c12002c90740303199507000e081c90100c0500150310303030400407110041818070707060140550072940020710350000080c03030041ca0309030340b040c00448000501640c610348134032000b02c400c281c56040e1014507100811840e40111480c01442c0b00440c06030b01038042981c1450781031400e4138145200301400940600c0b0200103055504203c4508441858105a82d414148210005000719610017010320540101000000c10550403c0180c200709a003070342d00068a5400c2510071649140c0c0d91b903000204100c6c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 921730233 1250 921728983 921728987
    0x4080318091b0307021207120f021f0b12030f0301060e0d020901061b02031609061a091c02060a0903020f0a060818011410080607020307050a120302071a16031803 71
    0x43d40c01c040f4501c15038008003281d1521484d030307074400c0c0341c212600d160b440c2d0b40c0500b0a80c40103200304520030034806403803070840e0b0b8035607822603541c0805542c00d440d58a000041d071076658100444070007800c3c03806072516208500c849600c645c00900c1070001240320304189110503d05001141c15035a401454600c041c0d0238124119035581040191540c1d0301d05500d006000340e5802c0180b0f01e07448000c0702210515034141810942581c040d58000480310780d10f10311091030240b0b000240c40c0d0305002910303a005400041c0c60f000000a103284000780d0440340004400718002d0303002681100340c80c000e4800d030213143d86039002e02462441e24490b000000c1e50190124040203107200700042408038410001c0341e141c0c040344400422120039244900024248001004410414080d040c0c0c001b4a03400034500b400110707183c40e40c983c2034505004200c040000c0d41c505006002c2c0d0b040e83d0203590826040d8800030f80311030039800c8081d8241e83c8624550a0f42d40d040128074882e0103148040e01e051070304040720b02d12507601 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 921731483 1250 921730233 921730237
    0xf03090c03060f0f050c0a1704110f01021606050d0b0904050a02091e012d030f030f11012301050418120c080c0105161412091204080318091b 62
    0x10015a07a11000f05403c4c403543c43c02024003840a01c05030342e44d58031070041d014000103481040c40e0700c0790340c5060400021603101030840311035801c2959610b00e135085120040b418851440c0a0401d0084032400204140340c0c40005807203c03510a82c401c10101c4495420059803460485000708581d02507069207005080c0b5014050304660b040000460381080562030710380501c0c0076007004c0b192030200d1285843c1c12500c4c04001c08000d0820f80d8120075a42142c50308070590340c1c0e00724050140321101d451144424840c0a46010340b40000d4020402444d86082890000d407850403029686400c200006c1100d1410f0b103f20f1140d2809021342c071454200d036941d03985081101c10101014005580090400300da90a00248042515000000303110300c2c04442d54006059001034000c100540820b40307131480602003007200c1c1081504000c243c4240c0c2c1e4036922034544903000032a008000700101d00018041c20000160100402034245000419054410320500600c00c0300c420303032071451440c1c031030a000ca00840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 921732733 1250 921731483 921731501
    0x818030c04241401120c180e181603020d0602070204020a080103050601090614010302090a180c080c070c12080423040b09060a1e05041505010f03090c0306 68
    0x10588044a8141000408036002e4030809014601c4900b61940381d15007021000024069802e001c1c00710564410000b0404418105040c513455514012800c0a5020300540c07c85040000701c0c21010b10780706e480112400005070303a4401c502000c10030250804030b000c20100c408031000b410244030030381f0316000c021114012a0301520026420070014015032201d000501e10080b140e10340a0055241d45042450714005030300c4070700e000e450604240a100f0b00d800e00c00903882424a00540c48120703513400224159000da000b044c2588255492201503491500181d002c40e40c135445040e4165500b4441000c2c0340304a0000510288003014241701c400030400f54040041e0180c40e01905084d22001e48a01369004003130070307550182c10604c5418013450309008552b602481038035528840c2c10309402007186924079010b039407164a0204140905200103051403001040f0052083c44483c0380011040c0e0000704038010640010405104401c52034003d00a100c4150350100700219941e14603106c0c8801809111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 921733983 1250 921732733 921732739
    0x50d050f0c060c070302160608040b06030f0f16060935030310090f140105040c1209080304020f0102152212110105010603060e0f060102010b0d0b071b0818 68
    0x44407007100488200a250f02c11184410f286a5440b01401d01901d0050300c03842e00c080040b0300740d4040c010554400e43c2d03507401544c08600000c60707489480009082030341040da12441d501c50440d4003e010a8000380781c0d000001c081c0500e1410984a90040365540f00311300840b0072400088242c0c28024020003a03001400d200964561490307078a00c3e050506690080d100d181110a08500138000460688a05050a40009410848141d0241031b20383c654105105003031140350b5959540305a6401440e51b28941d5013040020000701085191041c2c894100f039a040e0300a560781c1420b064a5400004e80111464041c4600300f40d80c3d5450175044c54154802e01c140c1a59640700c500180002c2814103405003a8500d134a5200000c0741d910402421078005074446000c16003020010820018001c1c1191f8000400410751701d016551440141e002d050100b40d013a4000750840781c0c003001d00152415050040d0303001d96413400b6035801c04101c11601244020050100d20013000540c0000d100d40c0e5810030420006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 921735233 1250 921733983 921733987
    0x150302030a020d0812040b04033c230c060108070e0c071b0603050f150d0312090b18370c030b150a0b04061403070e0409030f12050103050d050f 63
    0x41c0c803403441c08030140d40440c0c43c14000e4083c40101904414a403180340202104618403030705070881c5240c264407021080c0014080009070ac90080c1c0700340031035843c03501c3c1da140d1107102002c0c503855038030181c7c0700300446a0f041c0504000820050030110791b9000301c440c4d440d02d0204913104c071030410f6480c0d0b20104044460b01c1c10005940c85c1404d43c10107850007040181c030001124548100310440010005015000060a09208001e150303071342c130008000310390075140150010454121070b8000b4146407401400160121003000750071680a10341c51b4030003072164180c5002c52200c407d5095104e004240e203603503d0302c5440d200c00d11411890101c0e001c0b540601004100d0030b03526118107008520a84540e40140780640ca9103045042c0b0404080c024100c0c0400d60340740c1490031200070024903030004100d40c180e0700040800d0016124490b903066011008208004101092901802e1000141845404910002c45070a039109003071007a0380c120794001000e02403104030a481250554801301c0f41802400c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 921736483 1250 921735233 921735247
    0x151503161a0d0e0a0b070f14031308090a090c17100905060310110417030903120f0d06141302070f030809010e01230912180f030604030210150302030a020d08 69
    0x1000068007245c0100c0e02178610781000b100c000c08030100d2083d558140505030000c1c03000308100c40102c950018803403050a0406017a0f02d4183d48500c241c3d58140d07480b10b420307040420383c0400d582c0a40d100588980b205202d841c6c803901c0d160074014013140c1c00c400002d440c1e10b08001034510394000035805800141624600c8000c0f0840d4007c9481441040e4190500420b0620130060190700b59030001c80702600640c1403c50b0000000d5503907001002004441101160000804000c041034940c0d08062541c00d01002e0b4854481c207400341d1407900260311890809440e451401514400c64100a400c51220103c140c01b5032000d0b2101c15010740604039565070307141000507520080c81545441003046c541d001301585c480c500c01914010161005800b9005414401c4104442104444500700b1120804081c8090a000200d655501c41b05041d01402090100020541e000c40d590158058011080001d603130f840146043c621070a000083d055401520500c2c05840c0131303101004480c0c8207885a61800d12 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 921737733 1250 921736483 921736511
    0x1201270207030309060c0e031e0303130303180b0f01050609010f270b13060503090303040f03180803030702120c0a02130e0a0308090d03090b1503151503161a0d 70
    0x1512078000516820502e10487c0341c1402851f29209c500d15148024450119030b80d9120b100180c20f0700b04501e98030b001001094080e41103002a4000d0603881c02144940d8200300941040450300d2030b207090003500000c01d0502e40401514120720042e503951200340c40140058800c2105000d1403800f20b00d80212101d41e081c90102448041d00540c0481500c43c0404000d090008a00f600302d14184182842044600d58001080d251b020782c00500c1407840184504081e280b05541c0150147e580c0d81d80e920200d40ca540000c01503010b00320940c00c51b811050140407203840c82c004c2050003c2c0e550404868072000d450421040e289032031580000003a654554124180f84c03110307030310045010500000070098025030034809a020703003441c2d0600f40305201070341e529000c092800070f08818040c0c07010200144244c400f08842c1d0700307681e900d00040300142000030000a04101030105107100384200c0000c210a4440c15045004031890416005a41c00444014a049400014084009603520384840085134 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 921738983 1250 921737733 921737741
    0x703081005030d030204060215060f0d0c0308120103030216080d0e0a180c121503021203130311032b1b06090606061d1f02160b120127020703030906 65
    0x7405a41300140c1e00c42ca090006810060100040501c1c06405000c014403515444607040850004503042001c00c0014940401011034903040030303022104c00710b882c400341440340244074181c1c1d02035000c60b00411610140c1d1040204240180001034112a140708040c901888031a0601c440c0100345056180e220f94000c4c0a480304034402014a5407a02024902103400044140700f2112100c000d1000203074804c100605144103100c000d014151065025903404024401c3e200c9138010301e0440d0403850303030302c1c240752607640510301081c0d100340a141c20240c03000e032005030050009204004440a00140b03038100362600503100e111101c545c1804095100002c00c544611080d80c3e02c18040012542e0502500401550228540e18000d003100302c0425095503030180000704501740c0c6e030300500b091210303158201d040000980004200c0c03c1e815101140192500001d000741e207586042d5002143c1c0c2c2d032520035600030100d121480042080b00d010040d40c989503001050114080c0c03e01041c4458580d450303508607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 921740233 1250 921738983 921739003
    0x3180b0c0102071406131e020d0b06040b0d0203060f0402061c0e120403020117100b04080604021f0815031c050a030605151206131b081b070308100503 66
    0x20741d500045550421581d108200280183d060080007180f800c04c070f05161101340d0040107482c040c01e04140c81014851416490600b680c05403c0a1b5400c07480c0c501074079075a00a0f558284500d0070104c900d406810480b21a079400d0f9001002019a9101e84911000700e0394050000c4c1c1c3c001c2002c02c101002c2d0084050a100d0240b00d50b030b0000340500100b01d03820704207034240c8400004440c04100400250b07034052000c141006003411009065254000c541d541d8034115844045d511501203000590003001040b0349200da402600d8450400003c03400711000d080c5459601408150040701140105e5010b103400441c0f0b81000d0f04803091074808031034040b11b42d1410b44009000680000d9041d00603645402614001c0600742c0e02c19130440071003584c100090281031030300c240c0d0b8420b0000043d503903581d00502c00070810041e54100034107030408080f54107415000c1d81c1c030782c08901e4180110301306202004207880e801d60403050f0b07181030000c40d5030110b030350500141000800d1042070201080541d800e202490704 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 921741483 1250 921740233 921740257
    0xd050c0303030412030501050f1302090a081915060506031b0d06030b1e01030512071a01031101081503101a041b02010e03040e01120c0902030a0510170a03180b 70
    0x511342803440c005081e26416001107000d00c0f140e880b0707000c4944900142c0c42c600c0c00204800350312602480c0200d51400e1480d44101460b12410361108006c1958045c250140c0b0b0040103120010462509070700c094940b0f911070030380c004104100103050074a11861858007150540300452802e041408d1440580b05150000d60b0503c2c418820302c04403007140b100c15011068900038514040d8035544a8544641a41c0d41714808013000140c00d5080003c001d210b00c04200b840400208596100c0c1402d04400d102000d00b41e0200b00328a01007103800e00c01c1e1000742800300004001b003101507401e61305000900aa800310511419098624071483d643d2401240b03507610304440740241501c05400c2c024255049ea402515040d04200310501103103041d00e0240d815104400b07900005100d403450120007082e10b5a200384e42c40392010042c001c080e4101c0e0030090040b03501d01403035034200b1748415070100e180c0d403801c03013001c019440360981c403001074040c100a9464841d0002240c02080e50f0340d004480030385c00b407031030104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 921742733 1250 921741483 921741503
    0x302070314060a0c0c03171f180c32300703091703130c08011b090e04020103050907050d030203070605160804300201020c010f11090d050c03030304 65
    0x51405070502c04c0800600003890000b0b0700c500b00c3d4802030600703c0d07180c6d001440001e0b00000140036142c0c642e0020084136111103100e6055946012400d281c0c0b2203900605003090500202301c09185c854445000c00800310048507410310607010079001000b04400920020742d1090104101c1041c80d9501e040246000d2001030341c101000c00c0a060340100000d004406145c40d01c0e80c402c0c08a90002c0840d454168254400d5075661100c6030344101016004a0044c600010003001080c5024103400180c0101c40a200802050303540c44415649a803180c090300c2c181c10000000500590700c02e4001139040700d1900140c2d0304a03034880c008604004034250082d00564000030b81c503400c00c062845010b5110302a800c844040f1400000c00030710b01c0e0b0307000e0000781402080740d10400d00d102c0c00b8110440d1042c4004100c40040d940007401a0207500403031203560f042d51030410740895810719402a03a0309030507500001480c1c038040701d041095844085000340c1c0c00788210075500c50a87c80030402140250b0294400030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 921743983 1250 921742733 921742741
    0x61c09230d030e12180406080d0207050603010b0a0e120d210219120b09040c051008010b1b010b060d0603140c0f042f0a39030207031406 60
    0xe468581840d940300105440c14604640340c10010404e0a000d03480d13018030035501c1c01c03d1030740d43e440000a000020b138414074009001450a10014854019050305c0e001c0d5503480e030350f0b081000090700091050203088901049034051051046451110b000c00081618030300201b400482d600d4042c84150700d034041000c810540c403030840507000a9909110403c01540780580103135580481c0d4200c5122001400f001c08024001480541c10807001d5070307409095926207103482d06040d11050030511440c0d0180c026898006402482580554186c448241c503061804511000d500c261040e1442d03560074655030360810703000c0c65450f9401020190b01c04e02001c1031140c15820006224040005550070580c4043c1104031542c485a001c120f41c1c0008540001780070f440304007500203203804008402c00a00890355081007904540740500300c8821181e8035007106c038076080203132801d08651001c514121ba03101c00304141005461411468541d00c00d105441c2c201390703243d98015a4501051100819400c540e00700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 921745233 1250 921743983 921744053
    0x1b080309011505030703020d030909140601030c05031b030c070812060102071d010b07140a1505090f03030619050a1d060d1e02011e260402061c09 64
    0x1200c00341031801291481d1032a140009a683c0e45c140300c000e010b09a100d20041c103050083e0030b090010201240c00384003c1d41c2c640c80c800c0c003134a0105e034401d0119280c01d102415543c8601c060780d01c1000060341080c807186a0501e00101d50b080100102000c001c00c000c4000010103100250107334030404101e0f5601420110000b80c00e010082d0000c1c4000700041207002d00341d000d90103010f81101c1144803c19030324181c03030405416000b04080000440e1090b0b40c2c10408100b822611030003500700e0098100728036100d00319040e8540185224540e4607500a2010480e01e14007107143ca8105e020785817031014010354038070216654010302e6012007205c611121804042e040700001248c0c4c04401210720019240c040e0392000c014088402d01c141c2207130401c2900c40116402105076640242c21101800d145505480000302003070b00c044681c1012403107401d401d040705984030203194010f590060010307040c010901c12001e04210440582c9a10325100c41d80c00c40810102c01d000461142e80f6480c0c60004240c5400b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 921746483 1250 921745233 921745241
    0x5091e0601050901080a031b0615121a0c070204021303020405040b07030e0606060313050a0606330e09091c03020315010e01050405040236130510030609031b08030901 73
    0x205d03461b00500e4a03100004e5020224404000709030141c14140d101e20f0910710014544042003003403480d4450001301714540038050540c0300c184134100c84d60110031202c00e4550444020b90300c029101e00d007444140018503180c0c02400131000d22003400d14100b03a40740c001500360342c000d49003500d00162010a02c13608561500500010441c000000c0c403e90418901194441c070004210301c1002c2071080c2c031001004000d01c2500742181c3c1142061001c00e864620071280215049030303500301c1c000c1203240a80c850080c402d030031302440e100b0307101ca64141c0c3c0594140b007101103006049600da40031305040b1303004094540000b00e100c80031540d401601c03071410b090409070444900388c80b54144007925544c0b2030300da07034890708980c20390b4004c0d02d016880301585a21011045882081d00c3c2e983c0e0541c0680c0945102e111200404d81b0b03008031520203401462024030030440e4020ba8441822202855040c00420182d40009040783d10038034041c6400d00c4800420809018041811544844001300344a2540400d0207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 921747733 1250 921746483 921746489
    0x6031605011d0a0b1b190f030c0b07051b07050306010603110c0712201003110c03040816210f080f0d0c1404081005060102011d0307020406060e1305091e0601050901 72
    0x1c00303914820140c05105600c44080007411030300200c7e004402c00d4442c00c03c1c1c2451a50210b4042080d04240030081d20980200342911498403084c5001500510001550412688090f0140c81c041c0d0078510100d0240810515941404004000e80012910b003004240c000380f4018540c400742d203001d8603101d1580301c11042c1070148001003040c1c40200c1c0c0e030ba107081038482c503100e820001101105108025040e00560045450f0360002050000d90034501055210501c0c0c407c03044980c0042c3c81c0c024407131000b06c214010b40345c59000d0101c032030009030f00c460200c00707040d00a0500600b0005400c1c4012100d90004506034191078481d80d030303d008036802054100151001c100a1402e090034580d002c0d99501460304c0130b02a1a4550001c500b40da4001c0d44040e2140b5281d00250b1204c1c4207044a1990301e500680b03040307015529140d000200544070b450360f111520f5008004180017150707640d2000150130094962551400344c2c9558400c0c41910142c603000ca040040301400b075a40c94201040fa580405038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 921748983 1250 921747733 921747787
    0x90d05030913090308070f030b03011d0d090f17070902072306090c130605031e0d0305040c060f121a0108090d0f0c110405040602040e06031605011d0a0b 67
    0xf100920000781c008811a40c01006850708101d200c010000c11000f038442015007030340552a1414a220440e054500c1c501c40c450050708440c004094075204440c0c10381248076601c0100310540040c40040440c0040c401585862011120340f0f0ba2102c10b203108a038058001220790743c25045c161610620304007021143d602c9088042e04851a20301911a10b5000504450f4400c079921050030248030302c203910840c050f210140841d29515500090de101f01c0b191080348160907c5000480400740d44640503140c8590790100041c2a90703803a00d070040d5104c6069154401c140034400319006003454042c400c03070709458446a41c03001440d2503600050308071480680007842da9081500340186140e0003024840c5160058034001074440c4040c2070018140581e50003041e40282801c00f81b1092104a4001e00241c0304136035041d00180c0c68200816a03909081e146161400c032550f1400c2241c0d41c00307101c0048a0f98003400304240141d91800008444c2c0c84290012000f03101e000c01d000c50524541358800700152030030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 921750233 1250 921748983 921748991
    0x30c04031a240402070501050a1d0c010c060e0f161406030408030103110604080a0302101b0c0602031005180a061a0315120a050604020f270a02090d05030913 69
    0x144980780d03890340032040040c2e0507004040408040d0303d03a541240c039480d42010003000380b802c2c6100110060300c4041c085641c2c030041d070640d542c00490081001007a442c4161038170001191541e503214003604072142d102145005102c074404040c8414024006040200513007166a0381c00c1800711500d20b0b4540f095140501418810000015011401c0340d040d01d42010040313454410401c00903603c0e04c40c5030000d003811f015804600003019000034600900d500c90000a001c00300400c010552a001c0000c24003000403a1061040040350030369004541003010700115024a588400114403010503404460041c1c41000c82000f410038078900c10400500404810545070410342c20309800d060001500f404d5102066a451072555590b48a03d01c01d039003c403605484207510103081080e258401140e05030f005500c00c0b45500090b18101040500c071020103117001c14592202c9081c0035641200608292800c3d508100b020050f81d152100c006034188207400445d81c039041c1d2801d0207045141000308500031810 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 921751483 1250 921750233 921750241
    0x705040b040b0d0908040609080c0909030304030e030c030d05120c03010302031e01200c06010e091b060c0f0607030606020d050319110f04030209060604150c0303060803030c04031a 79
    0x60300119012102c0d0490295203480c01070704900c00400c10408010400640040d0014940d0b400021100480f10384800b80d8603101078507400d00c0491041100c2c4005690820800503000901440d2015042d24010b4103c03117600303042501203442d060078500c01501182001c07c4c18481561129a03a65210350704000d01801c1d9455580032035035910386461303070419242020183d03207a443c07003d5201045800600320f41200e08010241c10a085500c21994460680151400032803801c4803100054010045640107103075140c20000300311010034169510a0740100c0400c095025001c08100e0301501010001c082c01881c18194030140844d40940d0040055400c41141d0300c48840c1c001041c0c0340c0c000d40c010307801181d00714580c20100c0140409240700c0c16041020403600d920f10120b1003e070060381e1090340ca07041907858210800c42280242d01c100c0c0d0413080d031200c0450707a25209041c40030255200b414041980c41d02c0d03161080c19900304855100300c4100200c2d080041c40081045c0c1083c40c54459640c03001414 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 921752733 1250 921751483 921751499
    0x61e0305180d0329150c1005101404050601140906120408090901080a0b19090f03081b0408030904021c0501080a0c06031a19090e03090a0803030c030703090c0e0f010608070504 77
    0x4100d140c5803100d44000f05001d00840001d00c0400d407c0300c0740140801462416114048000d01c0c1c40c0a00420402e8501c3c80c044641032a200780c0c2c0c05000144c4a41aa110000100302c0050f400400420381014090069036114540e40320b03030382d0085129040303150b100e80b208000e0000c2c1c6003050b0700c0000700343d00240a800c04a410f040869400411112221002e00c0d00c9084d80f50240c640150001c1044000b55850001e250744910590b00912103800c03c001c40d1807247d15840e2040c0502c1c058405035030410031221503285819401014112954140c25440640300710b155030844a00341d10480d01d079005490a4010041c41040f2400640082e0500f0417940300d000700000703001c0b0340c440f11950049003009080c2c105601c02030705400043c07a21006c10b1100008090059803281c000007520350107540203401c041050348020041d0307841821010b84036400c6036142e00040b0040c0151260541340341d0550503010901c0ca04048010744181e552200841e580e5241460040c85018000c014404104091000784000c030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 921753983 1250 921752733 921752749
    0xe07060509042d060602070503030717070f020607080702012309040c020c1207080610030807240501080c01020c032a15040f06020106061e0305180d0329 67
    0x441c090710009a440003540445a03070200403c040d10f03100a40c0340119529a4070703a08030000f44e464603425204c200d99030390141a6a40503c2c0c000902d10183d508103149607074454805807a1160040310f22140070540c40e000304105620800e4152403a03140003400030300755600032682561360304207081800c5c102e41c0202c4d0011454028040180e204940790a02601800d108000c10030a00c20001d00320365034103400154036940d8007014071401d40e450150100241040400c1d59900e0f045070342002029182c407000e9aa051926104080068440800c20306480841d00c4141b090354080d00c1054024242000544006807500341106051071003a8055406914000042c109003401d510502004602d44010100010340614400344190008003001c54000b4200c0d100311200400c90b10f00303800030452a511040c045a03040041210410031000788418070b5440f510a910959211350100d060b0790302c0a51030231404d400c1030b94034840d400019844192001c00309980e1020000c10000c90461041700034950b10201d00c2c07507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 921755233 1250 921753983 921753997
    0x1060f080702070b090409050a1b0f080309060f1b070b030a1410092a17011205060711011b05040603150e160c12263303100b040e070605 60
    0x43c6d0307101c551200070494200403000b241c1d6403222048107030202031142c00345041500c2c071821803e600c00e40c0340041d00c00008402c862900d907000d800246031814500d20ba0714a0b500c02074986410401c0c8a044c00c3c00071400f4481d03000905a40c01559503a0708082508005651152140c15500d809110a000300c200c0c44480020844510035808101c80c1046e115465244440c11007418408916200ca00301c5203038040e80c2d408140c2c80300d0303c00c1c903d02c3c0d0b222504190b640d068010010010f074070440c0460315042c001c070300350100500d40d0000402c2c040c1c1710403c200030b196802c01d80e18010803004142440f206e034042c002c014401e00d00082c00703a0180e2601c0400c0c0028000900711808a09024244202551141300042401c03900030b0b01c0052403010951740108a04001c12441c00220a0f40802c4110080207501c503a01424002052490400710301c200441b003e260555242100650b00819030100c4e24140b240401034600c010000890200b07180600050784c9103600080f030b0581210005004450f0400107440341 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 921756483 1250 921755233 921755239
    0x506040e07060324080607110d02030901031a030a03020c0a12020901050603040201051e0301050112060302031b040618200f030a050c07020a030b070e040b220b0901060f080702070b09 80
    0x2c0c007012080088840e203400d031130400030501010010420310740000d00d0a004002d240d9469007030014072540c4c551078212040e00700c4010781041011059661181e00044084280154108851544600001d24007017001004a02580041c1220340e01132900c03d040c20003c1a170040c2116400c111035000800810050085501c102c1d400310104055900c141c0076500030300580303e4451034010a40c00c6850590b007091180d0790000e00589440c0d407001800f40030321011298081c00802c02200d88000120f070040404507200d802c03644e038080016003054411040081c0c4864183e00140303858040704612a540340b40d00c0240070201c1e0030400005240c1c4410704581e400a551840082d15480d16030410901c1d129642019500c00a000404002d00c00001415801801a0744070409c41131000b5050006076080894119403000c2e00442100080c840700080000c0782180141c00942001208001a500e03102030b00b21400141c881d44d0f03200c02894103c2c081e160010528001094198078000291065200c0d031540140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 921757733 1250 921756483 921756491
    0x60930080c0903031b07060302130b0a02120310030c05060c06131407030b06041b0e060703020f0d05042d14010e030d260603030d0b0a1d0103060506040e070603 70
    0x6a10750045040e900d649100809481e0350300030340c0584c00456010301650802502072a000010994060320031600402e00d0440030131040d80c0344c22201c40841c0c0003000c4100035402a8a50144010158001140f103504c105030b0202c1024154181481d00c140d264100d240103034020040c00150350300005509501100d1440d1800014510740740004003607403000001010f5101e522008002c2100d2502d10501c40d88040d60104041609a441d400203070980407614804900322100c8507109003442002014000e000e40100c070401c0303403901c411500d414004681180056004a002d00546084964600b04044680381400d00c00b5030103904440d1087c400e21032540781c0400c916181156034094085282904402401e560540c0b030f2040300030700050110104410b50341b45449600580ba0482d148803401078001400039401c01c520700d074910004100a050042c3c0c00302404400251003101e254102c01c140e00d86841c2c0850315403451810000751080178100a203d103040004081c01c2ca140012808115520f03458081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 921758983 1250 921757733 921757741
    0x3060a05130b09030d11091f03090804080607110a0308060607020406210c080106080c210a05010e150408070201081b0408010b091e0f0402150706093008 67
    0x400841c0c12481c010302c0180b90a00308059400040094401500c01003014032040c0500354035108140b242001240e03000c41b1040901c9250710a60007039440612950400045405140e20b40507055005588400d55952159003000592980940740b001c1d080003076001044803009941d0064100a001032146000c1c540100d0b40e40c0035552507411690013403080d41c213484a034000064400080850040040c0c0b1082090a80055140e00502c500d10444510f83c01808091408c0d20800c881c22000d601c090850521071941c070b510016080c80b400c000e882c8148000a9140e4032061540c0c01d200410503a2100c649180c1c04000100d4200d9040f134801c00d0b824a007041d4180d40300342c0035506001b129842041100000b00c2c2c0442c00c0181588114141c9000700c0306035146540707a9841010090656080150764030701e132404175480b440680c002542191006003404030345200c56070044a1508604d500703480580d121001c503001d100b03924404480c1504500349880201e1504000c6807a04180c07007401034200b1070701d40d0000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 921760233 1250 921758983 921759001
    0x305030a0915090c240806131112010f03020604060302070203100e150f0705040512031603050909070207060f0e0a050a0b0a090803160609060906090606140103020903060a05 76
    0x425650740040e00741514101860201e00038070040100f00d44a084203200450350401703520340240d1003a015030240c0707900c404a00e01100d515102812090300311030080424200c009141c000c0400003401c1518240c0c550100f14400000c40e00182c0c40181d02c40d190b034034207002503150311080b50f09440c0603040c0941c1c0c4102a01c040380c034042c001d5643c00480d81c0703407040d0074500210100c0da80e8400b8900d5592451581c076190402c150355502510b0410221f8002c000420640c00d203411103116240313900040d242802d00f14149000004082481140042c20004000681d8a442c980391900f01500c1d1009204940c103000c0094210418010200f0522040103c08012a510070180e0f5002d0007000d0b203400c1101c2e0744c48400360702e203400281800c0c000c074400c1c2c200401c0c100e0780001034034211051941c280c14201e00da80c8480000304a214425581d044e124808131000c202680206444503200b050b00060143c0f0b040201414031200c20192810940100300c4649149c0c3c0024015070064504030340090640c40321032270 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 921761483 1250 921760233 921760241
    0x100c1e0e09070e01020d0302090a030209070c060213061b020109030b060a1802030a050f07080a0207030509091006090506041d0709081002030105150a08070e0f03010e0703022b0305030a 81
    0x180e840380c4810104142d4940c00042400142020303021560248036440c0c054059008070307685d0340d800c40d1041c0010405403503c001d0041c0c020700b81d07081c01d4071100031076221101a42d104800071442c00c84820001c015030b6501c802d069070207600b118403901413070245034002006c140c0e00d44406041440c8881c00714120b0342d20721410500802c2c804040c00805009035040c040a03400c1100e6015099180c007002440d02d107501e03c059881040c041c2d444192070391f540843c0c44002e40048400b50304000d814000e040d80ea44400b0a140d01440f82250b0007041c2501d080002401031f4059000b55003c0c00b400d100801c50441041b0400380982036000c50540140c0e03c034941126002c0042e40400c0c80b51107280c42030705100540768000d5050780d20070340f1108240206010810072500c500c41035170000400c0b0000040340306204400080362800c0081603100401800400282501d41202032005540c0098a08004501d0106c0384100d2980d19070038030710400000e0340e003010400c030b008440150901034000005928256560301c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 921762589 1106 921761483 921761507
    0x10906090501030803190605100c150c0f050708070b010e04150207020f1903050d11060f01030f030c0303020d140f18060615072102100c1e 61
    0x80e0312411b00c0c4030701107848901e0346e81d11010800b96214512205107038820f0703807443c110428a00784100c05141b42100d88407181d1400f0207654140d504461901041b44003400c0582e2102503508002d9100c1c03103a50001440e1720880c2c40049401d5166960301e0340114007550100e00c030003072601080001c9209043c00030754080c0340c449014131680381003030580e10070604801742d0312980e80c0d40e544ca152800100400e003801040c1e084280240c07800c02044410b500c0200708280e100d482d40f43d500c7c0e400c0c00f000100005010010074100322014140681c04641e114600f420003001a51503c803510703251804113451304025103100c60007252181034a080c19160050343e130005031140f51035100400000c8005502c880075107210910484000c224110740e000500100d460303c500545400c0c001c020305140c4603038a00d01c10f191a00c640c07900016802664034913001c4404c1406010b80084d800c055501c402010 = true := by decide +kernel

theorem cover : BRFrame.Cov 921582733 921762589 := by
  have h0 := BRFrame.cov_init 921582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 921582733 ≤ n) (h2 : n < 921762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
