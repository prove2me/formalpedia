-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4598
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:08:06.893978+00:00
-- url     : https://prove2.me/submissions/37301d45-a9fc-4ad5-ba3a-d0286638c621

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 826798561 ≤ n < 826978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 826799811 1250 826798561 826798571
    0x40f1404061409070308030c0306031005040602040f270213120b0a050a0509070303032004030f060e030309120702010e120105100b070f02060a050f030c09150a270902040b0d 76
    0x50310f0009012040701d601c2840242165500d20400a864100809444d0107014001c651607000300a48143c2d42708604c243c100586440c2407609441e10300030560001c038600e00700c0300d4001045004141e1811002c401c62400940e9403005080c1c01913085c00c42c3e50001c10298a004105000c02c5040711003680b08002501c130800c641e0756480e030100142c65040d01c1c0003001d03420034101480030a1007504901a401c0c00355504245104031310710078600607485a4815290140e02d040c0ba0720400c909030142c50144c054a000450544c14686803031510303518814001a000d11002030814110390090483d5107140e030008010b400d2000501200b00c0c0a410f0840b0903d51060120b080402d0b88803500d000d84100c603401100a00c01d49040c0d600780000c6620140c1c45c04184241030040082c22210031000318498402140e440c0e840360340280c180100115685001b07800031000780308600b0102e40c014800440f15040305e81c202012003100307403c105801107507001552540e000090110700d0707200d100b005000d0807416000c2000707 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 826801061 1250 826799811 826799821
    0x101a0901210512191b020d0302070f06110c0a0e010b090a05222a270602070e0f010303050319060305010f150509040525081519090c05040f14040614 65
    0x52811341007110b85608171801c07214040541800011120380c0c610900455602c16150f070703403032240e14255902ca0700014a40648000101c03606004200c0300c1d100c166100384245082410760055042c0c14041c00d2a081004189000a85d46020041009180103010400401000d85101c0307820380d0240b103880321341410302003081c1003041c06400580950440494505004075540c80031103841d41c018151000e500401420501c1b4440b894013080014000c94004128061409440405050008040350503040d840c034010004250404102c980c085141480c0502d6550a49103203001085075400160689d841c1c03c15880c3c11000d90f80c010216544203440d0704400a81d80c0080040e01d1004460040241d0400a80075070b0103c02c0826490701c00410581d82e0240319185c0700c050b454913100340030070000c0d03400310024402110520810b200d1a815102e40078454a140ba80301c1e0402d0400c00d1007040d00507951031f05264062540d69000703c044000c41a50f004882c00e1904001c40a0b2000103125000c014518021507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 826802311 1250 826801061 826801067
    0x1209080403200913062903160602070b070807050a0c21080a030504050a21090602010b100509190305150105181f090c02101a090121051219 61
    0x52003164000b040c083c12580e9490a8120700d041440086900d5619145220361184120740c140400740100340c40e40101c02070f40c02c10186002000b161043c0340c800c120a0900c42d59901103400307004d951103541a2036486035140b4000d1b00034461100c014002e8010110000208008081c0c04021178401501c0184c140d03903a550000031540d48080d009000300010411084040c0c0070b908801d41c010700030130584e2012403142e1280207407109000c401c8900c0058103086010400d4004102001400710b9100130001e00b64110b000c03a51424a1540d1201402400304030ba813003503680e035a40512401440d250300c4101d140e480c5031150741e400429854000440741a800410340d41048a41c414075401c40740c01034511502c0c0d407510301e03428422006c40c4c2581c8044e60400450108400d01a0240c0120302d94010410580c03882040d0084400c2d0740f60303010100200051a081503034400c400c003811b6950110058101ca0810002c1d000000c1c040c08001b0014010102046413407208100074040d240a00e02c501c0702a03481c400011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 826803561 1250 826802311 826802363
    0x60306060503070b27090703090b010603050108060708042a050333270c0907050a0c110303040807120c05041107080901020f0f0a0203070510140a1209080403 69
    0x34081c0580140880da0f2003840f41c03032034071070940501c84948482243c08030208461b400c04451107008070792200074600800140048150051403c0e1404200a50502e130f206600e9400c041e211008000070b42002c40d040c0042101c65550a0043c51500b00090714441d82d640124800c0d03100359071080c00303034007040380f8003199503401641081c609802e180500f01c0540034040342e00c0e0025007000c80d2980d00b84004103016410f004000058106040286644650741c000c11000000062200c020008140b0940030101d4000c0d602d0030005a000d0b40501c0c9006018000c03901d9801a0303070040c1c0080c840c556000422171608044161014016414081030903290010310090b07580f4241a000f00340703010000302020401c03d8010b4404d00d5014415200300000c3c144100c0c3c6007203410109450107030411604a01145010007148001307003c10b5945c50112035010102030002084c6001c050500000083d520340c00a03c540e140780c00c0b501484000300708415040c02c00011300d422500088454403d0140d2a602a0719007040e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 826804811 1250 826803561 826803569
    0x3090f06071124071110060f0801050702070608150d020d06091401090f0206160c0e16080c0a0f11010c17130f03030c03061206050f070801030b07200d0306030606050307 74
    0xf500306034540080454008803042d07136107003650080300d020140070395042c0a8000140b403201c101e5400075040c000030908440015005000355032052808204941e0088262a4410068840e05800ba0007400101d90704100002e03000354002c90f000c0c046420407034150700911005004210085941c40c41001c0d044c200e42c0d00d0500501218074a0301d50f80b005180000c0100500300d081c030300300d15040c41c0aa50360907008040b034101c120b8200104007046a244000803200d0360182c0d9502c0d0000c16070924040d0f4030641c2c0702d00b450541c20440c1e001980420340b4000c80340703071200900b1403000b0014003071078400040c508100030781c3c0f28824500b460045410171070000080300856400410703080b400201550700341c00510b103035030700a420305403100c1c00011803c0c400403080740f080c0e00510000c15070f442c0c910841c81c0302c10001000d01c400e02c0124001400440c07000038600790f005029041a02c0b061841c0030742c54004481e015480803583c031400342e034800120f0340364020100300e910490b01841b0490702c038403c2544981090003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 826806061 1250 826804811 826804873
    0x7020601120506190e030d0603110409021f26041b0e0708071101090501091104090c061409060a021e07180f14010f0f08070501090b03090f060711 64
    0xc0800e000c02c0b040781d14510b852104913030019118826005041c01e5400249600c80c250360f84190030010310501444044401404650030407455550b81d0010303e10003480001c203120b000c020304400070b07003c5c001c210202000103002030341142041c0741c1c9079803034038001e08480c2110f2032070010811454a42401d480041034900499202e0481d80e250740c4122035401004000d4400c0048103850341c04414800e10410054074040c1001103811070b0a410190075000c80c1020050141e45010807000c0402c40e5605403000341c0e48140342c64031192005020030892800340310000c03680301c04002200004560005940360b142d06120701030818011101c0707032a9481e04110300c44d804c0a036980915110131004260312170300a03400e01c5040000c06c112942c500504155013600091440c8804d01424440d07103130074180e868010f1403d00b000f0410ba90815000078890540e600c10145c2c0c0200100104000b00401d2005214007481c01003180e02da45000c0300000c1001040e14100c480501480c42e407442004200411081042c0f0707180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 826807311 1250 826806061 826806073
    0x2012a0816060915060e190b0a1a181509150f13090507110d0c14070b220f030602031e090706120509060414070902030f0a0b0d050a02011817010203070206011205 71
    0x70b0f2040d42a23040d44816011404a6118060101074184408440e0001c0d01c44030f00b0518440c01108864105100e101c0c110f958604001e0b0041c00c8520310103090780d150010140d02c01c0b03110150302644072000c2410300003141c041c007210304d00011942220005c10041c0150344800c2010754400b44101c2900000b500311850009266000e0010b40504501c83d44192054030b01d541c40050030081c00fa0411324580d81d0000c0c0c0300d03803102d11800c8502040200e420486120628103044024812002d200c010401d0380c0104c00031f038500741c0000c4030300d140d03590340310301d4002920b000e806560721a22076000d02000708030187c400714158440361042510800f801c60051085480780c1d1141146035071180c48550300d030300c5030305d1002c40d80d0b800d01c2c00a14000c0401050505041c2014640f00c1309035014540300301d000d41d08004104000c550002031342c0c40c06640a0030044454a0300e107440211b0300403280c010080300c2000c010103100ea007405500851003040d00d507080da11207036216200045c6144a42501815943c065 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 826808561 1250 826807311 826807351
    0xf09020907030504200a0506132903041115211b0f1b030d0c02060a020c1f180510060812120919030c02012a0816060915060e 55
    0x4410052600c145c000c211480726643d440000d20300c0d0344414480b181459580004209114a09400d4101c014200c194041c4021050f80e5200447c0401407020b03041368080020074585807a000c0100310760501085401c0e550301030035001c0100180c0266010703911a143c92002804201803030043c0a01c2030a0050814035003210810700d0f00a80d00179120941c010078050580001682041008051800f070700800403e0b826041c0602a09207840204045041e03030040101d021080e00100d07440c0085499042c0a4401040c04001e11004000ea034188040254650064400340400000c0518104100c0383c01400029143d00c040c603200c80c0004010a0283e10a121001c401010303107107141d5200c0c1c1d80c1d400302d806005007144003141e4101c1d420010307808125000541750965030f01c085a030310002c29482608d4465800b2030000c020340d045041c009003000101041840c070541d08041c188280d9034024030244401031081c2040700a1815100041601d20b1405100259208840c85814412040d0040d880400604 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 826809811 1250 826808561 826808603
    0x610050609010809070522180308180f0105100e1312140706020403080a0e03151303020f1204051002150c0f160503090111120703210f09020907030504 66
    0xd000081e15000d03083c0040350944580302403040f0545503407104c02c0e026801c08061803c855230202d80000c582d00d29100754001c41d03040390400f508040c2010282201803400b1032214241240d20004003030300d50906042c007500152481d400b40940326044481c519985030501c001f2211350020f0340c0105841185a50b110395207001d40c20f09400d100c90418054075000301c7d41d44140032070703003e41c02c11280c0750000318a082105130b11280d5101c0403081038004105002420034003c0124400034884950b0364680e050f0501014405c0c0400840b0b01811001c8600d04851441034200c642c00501583e0b008002e9480801c1649100240043c41044c2c100c0340d041841e2202c200803151307944244050882100100884082b28801030101e031039240c0a0805036844007014000109032282059401010354003030001102c0000f5080121000c603503050521581401d02942c009240302d441034940d040d41d0b40341030249000c03820745400a460441c0300700c80c0641140c0d03816100790100d601c1550040d00308032000301c0d1507401c680 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 826811061 1250 826809811 826809827
    0x30c0804020904140703050a08180103020715020a11010216030f0206010e01140f060a18140609062d040302030706050a121d0a03031d0105060105030a0c0e130509061005060901 77
    0x40641305031703440c183e1a40c441e81d141a1a0b00c2c001c40d010340000079803014080a0500409010401b443c0961900c41c180c0c60300701c001c1030104a0305c0b110560001d4601480b034042d000300e00a9a40203c020764890611880f0003140182e000e0040d00415207541c5c0320091148017040a038141c599a4440f40c1180c1d00302002060507040c0742c244c1a820000c200700800840c0e8506000d810080d50f00c3e070300c00d00d840300c15400c1d441040c2e00562000c1c09c10183c00c091000a075864209aa09000081d00d0341900c503200c00720280c148030344d54010100c6a801d01899000b0034907040000b40103982c000d0b4201e0320215901c0a044a4510034100e80f100024400781c40070010410507001005801181544550400b0320244180d0500da11444200e0200e41c0d20505d002078151841076506403006402c0007041507141800000c1c0c654400100b1522016580b0003820312020300038a8680c28102c030141041c01e40030b1500180c4002040305480505092094030001202c507803200d200c10701900c1c0d02034041d60604482a0066072130079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 826812311 1250 826811061 826811093
    0x601031118061c020c28200406080703050c0105070b01050907210e07140102030a0507051c0c03021608030f0a03110d0c1701030201050327011b030c0804020904 70
    0x2c2001621054518680401e00842c02200010b95941c03143c0c0300035180407168070148145500c1101020080aa040d510802c8507812240410011018000d803031070512605008607809072a09501041c411f03030002d00c3d5419280300d41c0c21194000c40040040d10b45005458000348000c0344400184403d05040303c46035001074003410490603071080c501d940003c61209000d4405c1665580342d40b4200c00004004005c001c1850494100d409681940001e48a101d0798071183c0a001000a090007040010042c03010a02c41171402d4108000804000512400000d041500103228691486241d0403585884200725200c80300258274001c092a036a400ea50003110003c014961b50b540c003a411200408020010080c201c10005064408a58060601c146460721305c410079118900610060341c0003011a600091807003082a0014508003141800b61035107400d0f01969424460b0030f4039405441060034030310015a44003031003980d011004c12100240304440280d804407038140031a02140130490222049 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 826813561 1250 826812311 826812319
    0x60c06090f11031005150d05030c0703060b010305090d080402010f05070c2903010608060d06090f1419150b0109030506010e0f1521011508030d050601031118 69
    0x11411030784a80c01c01c41d01004040e42c0c014001a502901450240043c4244081d1940d08020780d080880d8060140c804080899002d403010070800800e004041080e1008803a03100708443c040d54a071300c1d11401804226071300502107401c0c40f02080140c80040b0b04060811465600c0492517a1207400440301d81d03868805203828030404102a0001c180881030003000713090020340600074001141e48924014200e06200140b81000b4030051041540c00303010960041e0b0100c500b19039030070303080c148900100541c40000307004c24103081c54001000440d00e11805071802d400b003030715946a001160705403011100d01e0018105140321760580291090340d07100714001d400600d0000441c0da12680d0782482d06800b0707009444091501c50070800750080c10508e06601c005514800368110b185200072030002e02c03e150101104000c514200422000d0940c0034402c0400b0b4043c404442551b203c0c0e4143e00c135446585045155400d103400141154080d008042404c4042d604440c600b0400000d0048454030101440381c1c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 826814811 1250 826813561 826813571
    0xb07150c050c03040e01050f090402010c03080405150109050712020f0d11040f06080f070f0804021012230f1005090a240501110705130e030918071b0c060c06 69
    0x78142d03040003e0000361141003a88a520750510080009042401c440303035210700701480c10400141d074401c3c0c200f1400d130740c9428150015101d524103076040c0007102004560311990807000041200a64020600070141519000c064400e6503d100d420b0780700b204c0c09210a01c4040101ca501d85103258032600d03201e0002440282060b03160007407540d003070100d90301040010340780c1c0013800340d401c1074041071540295803403d00f02070481003d0005071040360001d10291041e2420750010801d40d00440041d142c40f441c14000b000b0351100e804603504d00780c04004900016420240000702c0719108044014010420707031300c3c410f180c03900d05010003001d610010f150f018001d40740d0001a00c4c04c0302c45040d90a0302d4005010222109081200040c0009108400f0008541c4080400c22080e180c540c4000c402680c9881e0104903214806131075490342c460074020340c1d00083e4844903508149a80440310f40510660342d00c0740780d0030141c00a002e8042100d05006401420781e4042009013600400032071500511406002c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 826816061 1250 826814811 826814827
    0x2070b0903070e0411090a0212010b030903070b040309060906020f0703060209190603061409131104200d11030915070c1a040b0108010e0304090b0a26070b07150c05 72
    0x81c09003010354007140c881030180314a03c5c003494280d58030f55201c0c208401c110308001805080940c609010311034001d411724000045815a1018001c4801e05508180f514105081500d4014568000c03031180380b000800503107011a50610105592504015a6000b004041c0c25030311010025030068820a9000031440001d607802c40700401d4076002045507480c0050140d180a0825036040c2c12081468442d5680001300008a03040b0b1400314030b491741041d480c0c0203000c0101c001c07500030105d8100300400b8040160000310b803450171000a01c6108441c22051205004c4000c0622013400b054900e248550400380808643c20a8004800d511900030b00c0c011709140080e4413510322603513845007140741c03419540d405c01c801e01c001100041d00401541e0300800400c080402c900b5168051030146800705030f04c552102010b540d40c2c8a440001d40101c5218088001e44418010b0151301d65015501c818040c58600249105410003500d4141e80c0100200340b0754050040d07102e0040030a501c0460600c907040c803000b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 826817311 1250 826816061 826816079
    0x11030f010b03061914070e01090b0c030d050c0c07030f15090c060503070e090108010c0206010b090a0b09030a050d1119120e0103092009060a081504030509030a11120d02070b090307 79
    0x6d000e0001610f82d140c96003140400100000c00507044600e1301c030400c0140d03880441001040f540e03815a041d10000300e540325800c0c406060b1045145a108903c01d011011081c028070031017591401d446050b049007070641c821240b20540b0f0108c0806000040d81400400c00e040c002c000465011807549860041b0b002c004c000507144010a80114941e81e54480400002130740400507540580880e200f40d03414804241c0008040c0c003002d000e4521070300c0002c0f0312507081d914100007807244c00394480301381c500107030301c04600812901c20786586107000d1190141001200d41003441e0000c4260b00440003a04400201e0000d4038800b003003010a504042e60b4442160224100c2c0c00045030204a0b420747c200c074104820104014110003500161003001d8501003040961000910001d0940d25420b0348080c50380c40e0305042e5114020f0415450f01400b95074074150812942c000304800d4114200c405c102c611b13007016089940c038800a4000000b6903c0140c060040602d900c0251101040050440788490303280c0000c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 826818561 1250 826817311 826817351
    0x306050106080603011d030328180c091103150111060127182405010806010e0c090907030b030709230105010c0c0e0c0f0711030f010b030619 62
    0x400005181c81081c0b02d0f0901d000e005802142c1d10101c42d00e4180744c2d0503800c841e02c13440003400340d0000c0780c3c2c0e5079450081c04e1800c2043d0b080c0c1101c1624100520a040e401404180c0900c50040b42c0010907030a012500e00079038402c0800307001c00c1950080c2181d40d080014502c1440007074a05051046413001020a0002003060038045d054828100095198a80c01506602c5640c9481c50b100ca05062960801c1e124a0780101c040c1a0403146049803490700c0204104251100f0804a400c90b007820000b041ca103134001a06c5040314011042e6902d160780d031458202c1d00740502855198400c0740d4002045503144030b17800c1984a6880113054481c02c60317585100e081154941d0071100320105940c80c1080340303500310801e900d0051000f800c100051031406c1c1e5410f02110b02600503140c0c0350f00114081842c001c860010340340d0b240c0c44e031940d00c3c0ea2070f07040703041000222513840c5290388a44116580022095018050034606210103401410346844180801c4141c5100c00352070013050f990341c244582a0012b0340b400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 826819811 1250 826818561 826818569
    0xd1505120d110a0f061a060a0903051002460e03070512100c031d0f011104051804050c041b02070f0323010609060b131a0f03070903060501 61
    0x81c10307108580c03a8042c04003403401c25000519003000303010502094809052800d03841e0720980c0092841da010b00904080051b8022440d04481e020540e403940301d030080f03540302c142d03800360044a007002c601000d082c041e4418040c50004894400160b40081d207400c11500c01c200c0e4050814503060703160489240031030700c807071001c0a00240c04800761704d42c1e030304041c44010060178064900400076200d01140a607296180710507031004640e65640803201901c01d5010802d60a000010300f40f07103002501c5c040c0e40e03400205280c12419464419003648400400c001c98003140d0000c1c10103856007c60010b00016018014010f8949002e0002946c60603511480380d400e0028400d069941c03803404000c0700a1410440d500b201d00f401c404084140042400210803403009499205900280705058010174054a0941c1c00502c20904120b80030403043c41e00b00c003600c000300c2c5250040c3c0300c0c580c3e40e000441880c1078a0803904180e001c1008059581031131070f002150300c074000781010031001d582c2e40e03521003c5440981c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 826821061 1250 826819811 826819813
    0x603070c020a0504060b0346050721020a051e070c080d021e031201030336030206031b1c1407090e06041d0714010c03050d150512 57
    0x140c0462804500b00d40103003000791820045030307082c00e007103030f506100c0034009440c3c400c04100e00e14907001c08002c5c000d9200d941080c103101040c025601d80200c07035103202115207109042034005203446105000d4400701101882491141d840f00800704e0009600005484040120820601480854203010704135190340c000601a43d501c0d1030b04000740d081d41c158025040c80d40020000a040030b9002070703a034800013150903c290000d88a080700502c0c51251440d10940b000c1944000803d05802a100700121031243e40c0202c00c80603a0300076845500041020014441d5a00c1814805400c080c07014661001d000d03540107044800403107502c0300c1500a10050005d0a2038051450120b100500428992990541c00d5201908050001400e4031540e401942d01d5140003c00003080da0fa240d41044503246000139500a4070210725100070b48401c10760040c07461002c0d44001000c450352041054030000360b0156240c5044c141d00a2100028046600c1d14114084404001282c1c81c1c0d10040e000c3c03003c0752100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 826822311 1250 826821061 826821077
    0x10090b040815090a030512180607020721020102030f030705070f050703060f291903061a06030106080c09010302070204020a020d09090605030c041806180c081b0f01030b060307 77
    0x3510441188000810300f6203150401888600000c1d0894182d804111004010240e2607548208542c4a80d01d402d600914502c9a2801d200f80d40e80c010401c6000c2d62076810001c1800340b200d1400d4a042444240002e005078002c006082c50143c040000d541c01036810f1401e01c0c41d05081ea19028049070b080e000640f200d80000d2030420402240d07105241c0541c0d841c683c20b02c03000030412002d4403400c502c0c1044603280501000144600d41e95100154031010b04070303600c560134035141e0420030014140b80d0700c100d8803201855515451407070408140c03812510b01380c3c1c4a1415aa81c566401e00b0b40c3c10080005042c1070b0240004401603035540090005a81e25034010084da480c0d1020040c010000390b4803522819182500503c07641c1c501161120b41110160303404620040316111200e034100100c003020f450140b0f410030445000703561040041943d4024001d0300450754986c442180c46e0007408020740710f280d01241c41c0f01c0349814440d42d070041e0400141400200f024804001c6086503000300d5178280040e642e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 826823561 1250 826822311 826822333
    0x9130f110a1e3002130e03041a07050304290403030e09060a030b0105040b22020316031b0f050c011e1404170310092301121110090b0408 60
    0x3106004000c28200e1850403105032640c500a00410f28503160320303a209001e0710040c041d5103540c549803685010b0003008014a950240c101c64480d0440e0041b40d1400e4400307a20540001d02c480142d509040d0480081e503c0e143ca07100220041c0c421460020141400001c0801d488480110190008500035126444140f00300d01c10001902c2c1d0081280f4414240030b01c06202040c40c840749141940d80541d8001960b07107840c1c0018003845416030714441c0001281c0c000c202c640342e0741d0300914012041403401050361200e2800075016101c6151000c2c0800702c0c05690503540900c1b950413007807000340314140360b850400801c1c4100e003985c2da400300318585a96400d1300143d07151058400e495007600d4080c0d01c0e41060906542d9481d00c04081510544090070100c08074046660500102e0f00070301084d6010405031100d9880d40030202001d25400c0a1205a030740001038080b60f412003880e1180c0e2100440c070f200602c030001c011030503481d42c4401c0c0c00c2014043c00400d1b004211030050029000d440c00401d810041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 826824811 1250 826823561 826823609
    0x70803220819060f0f06090c090501080903030a1a1314070f080f09120301062109080a031109031504201c051002040306140609130f110a 60
    0xd540410115840b0220408050281d01102180d07503601c0349021407800440a96000a4140c810790181d03400e180100005070501071780d100e8030940c18980c448528042d0f5400041d01c442800311054442900200001400b40d501603112400a00500103060381100d84400414507480034030103901a425038a036400d9000b200141d02c0d09a100c00340e03281807125010320100003008401c025000c80d070420380b03610100ea40c001c824840740111050000a0310380725a035800b402400d9400d203500741600821640e184561160041c00751139111074201c80e04511301400e14034110000c201c80c1c078460703032100c00600080980d59410f1200394180049180c04440c2401c0c00c0c10003100c00314501034100700c2c0380360030305507e0360350f803200f22055402040700002c0355251005424601e042a030003400034001c0760b01c00100402000415804905030520300c0c40f011459665100a011103123800751031b09c9481140011019000032440300080300d000d07108469151802400402203104540a078001502503000e02c08901840c81c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 826826061 1250 826824811 826824877
    0x90406121401063c030f0b0a05070207050105040b070204150909051510060807090911031e04020f04090c081902010807021603020111010209031c09050f061b070803 72
    0x5081440503840000c10301030b030f203d9604c402404402c2a41c8403064020a84400fa44000219003200640040c03083c58513012040c2c010803501c7c00f00300c902d04004200e119200180b01415104180c440d030349854208074941415410040c01282c0c4561030300003404042c00c2a24000300207114100020420400340c6c64031504041100200d100781b4400c040402107545044040602140c880c1d0a06004940342c00030211412000354014078031007130410403464806070320a00214450003210140c4039000806c901e61080c001416107010b5442002c00d1010320080c40c081d803165055138410421501255601c000b003900b4210b1540b2441c3c0303004042103826043d56040300170260701c43e80c1131001c0c140c010709010402d0b290081c18040641041002000110000000d43c100d131544a4024220b44420698101420800107030154440c000751041c0300010352800d20300801461810000c0500d81010701090b0f110744000301c242401c040394400c44000060401091000300455122410009035080f50340e0b0006020301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 826827311 1250 826826061 826826069
    0x19060314041128060818030c060c0a050c070e011403031c090206071a0106030e010606020a0602090303040f171e19060b03031b011b02030a030209040612140106 70
    0x2240c94401c00c400955466121044400129007006160040e00039140c0701c0d1200c410151070040d080341c0e000c156603400c0480a807140700036050025040d00d50541141e00c1c0d00403802d41384416030001001c00c004a2860010304892109450840d0520804103211031810f8110ba1000c030991030294018015600b86000540c0d40e034500360300840c50554a402e58024400e54451003006a035a01e041110855880d81e00f140c10040c0c0101d0010840008040307048a2881c003072040c94007091900c84142299007042c02010300700c80e0700b81c001e07104500807030300c60101a5102c6100e095050008010201d83c08528040c607102822104c2d20044295801c40c1d4124030f0051f07962183c1804030410540929901000190480e1b41240c0d40a202d030960799900c0c01c900503007818481c284e807600011810600d04035540d500782d00c90b0800d0710000d010b402081ca00c520f400d40700003112007006070420880d000c11240079400800f00420003800000f4003070303524811060002d0204804461062001c1c1054404a5003401184058 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 826828561 1250 826827311 826827341
    0x61e05120607030f060302150a02010b03012d0f0203091f022b0603050d1d0d0305040614162114160201021c020307020a0815040b15190603 61
    0x1140300d403482a0340c1e428005054000301601c41e001249480d0b1640c000000a42c4d014004d1442c052207030b5005a20f54114900300801503280c0b81c201d540e2031405002c2c0ca000d01820b5160b41645840141c6c0910b03410446403100c2c50000d440b03969800f4510028802144204803500c090720700c240022440f8040c1c0034070240b10f10302550040c050010300c402c0c1c0d88614015000301009506080508e5040000a8030360342d071000d8514080c2d40415000c041e040380010345100114284a04203071995420007814920400700600000c1080c0b005208803801030400e680d100c003813802407500b0500c012034040d10b119102c100c2114052280d1340d02d81d0808080d940314605082075810440d09111030401441118091b5200c0e010500560483c140c044da4000d00c50702d00d90758950f404841414080c0e002c065501c3d4000c403022401040031400c001a6008040360760707100c080015159907400c1c0c80c1d0382c0b2915082c00e8080e00d00c0c00710401c4c2c800c0107101962022040f001c24403650504418503490a0009000c07200c411102101d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 826829811 1250 826828561 826828579
    0x6010b0705100f090609051e01020f040312020f010c050a0815030c040f110313020a06091503200316030506010504060c0b0939040b1309080c01061e05 66
    0x10000b04840415440c1c1d0200000c01110386610540a4803c074900500703514030b0014410244107010400340070350407280c242440d207a800d12000a080788140d1096402c205030034001440051101050300b100020b01d84121071301034000d195a5403c442040f084080442c6000035160100340d00304000e06c0c1c1c1709007510b40c01080e0035150030210b07441c0d45100c15030501c142d0740d40c0c107540c40c8940c0300c0d400300c15100d12281e40c154892400d410b61201031407103818164800d000c0d800000900900ca000d100c01540e001c55040c0e800000062030540103040e0344c00304a10907038224450403108001c20300140d48595503440c100c0c11300307042c003610280444102404441c10048100001e000c0c460b00048a072070040c1d4009402e410396540d64143c1d60a100d1060042403403050845001c01c9081044d0f0319508881250300700d040e0000b0302c910100800c90755054091074222440d40080746040f80340758082c5504030701945425291101100800e82120124bc00400c0283d5406800312601000b0001e088080c000c10b40704001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 826831061 1250 826829811 826829813
    0x1d09010602150406110c010f111c02092e0806010201061a0705100e0318030312040f05150a0e0f0c010512130503040b0406230301050f060f031806010b07 67
    0xb4494a0b800d0b044624441d074000880c0800c4500d40c05480b0158080c2c800644680105003100e010b8696112142200783c1040e501d0415800000f01b01c42c400b0071044c0004900f02404110750000c3c2d0441c0317407059844500001182119121400442c5024285150701c42144042050103401280c0c042c1199045a24080b010300424100000101100d40c4600300140c0341ea10fa450003505d002c086100302c4104c2170a1031361052200030000094058030407030201c3d00181c07000c02c00034155240600c03007001c140f1040740c0010402140d000314031414210702400c00e0f0f0b00920301203412100941d40941d600344070035a80b405030b420303811028072400d070200a003c03010703242e44c00b00d050000b019400390280c5400007640706004180204840c0c0c00450043c0d50200c01da0351510380d0b808c030f185080c0d00325105010209044600040b6904010310303000d040011003195550459003843c0c2448080ca040c040c1c0c081c1c0007a010000c0a04005004000c1c43c80703004160800580c411108203494201441a481100b03030700c90511080b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 826832311 1250 826831061 826831063
    0x60d060e180705120307020301150f1a04060f11060726010b0a0516050604030302040f050f011709190605041103060906010326120a05152404151d09010602 68
    0x8843e000c031610010011403252141c00c500c01c0c00002581076113090720401400301d1000e03c00c0111051140e072010596540c034008110910700c0c017602c0a0056040006000a9000e00d04241045607640f03000c0c0a9245140382c04d82c03802d60240d03402c901141c0310a8250702c9505058603840300c1c0c21f980c1c00d0903500030351404082071618003501907401c0c1403202c003180011100708020029280160840102c4442e42040c3c180135000b50b101d802108000e54101c0f4020a150820f220342c603c0d1300006039105080400c00550714441d070040540349058601480010707400e2419000040d42145000d84400551820035140c00103c0c16042e948041c0690440d40400c203014001282290442e41c000705440341c8082c0034020100350399042c2d10300702841d10300860031030b9003e140022194400c4400d80410040f0b42c50701f03901140a01d42c0034a865901c07207074001482004815005800c80ba02e4140c128103428182c81e9031150390100d04007818100060116040d00a120002d070140c0c6031071801c2a119110340b941030000003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 826833561 1250 826832311 826832323
    0x60e070e0a080729070c03200a0612050411060f12100b030103110102120703120b01080910150f180f0501140d170a020d020601151b050a02060d060e18 66
    0x2130221140f80c13101c0d071001d9540401c12100d050f94842100c603007898880c9001c1250301000d284450741000c410700441e02c1410070101406c00d4500c1501c5031110301050a0024014000081084900052002d0307100c6841e21000040c2c20b900303000010f45512410000c214160140c00144000d48446218008014088102e0202c0b03041d41c2e001180c0006026002c00140e24151500d080c140040900194103028198001421440d10030490070601c03407200328800460782070314180c6040c01c050300204084010f40115901c400c001c08490040403c08030340d00c040500a00c0a2540301d0f80310303a41c0b900b661040d0a4024420804060230f518002c012950405000c40e41e050340c5c500101c3e002d2200c102800741400140060600c00c118102462550788051201c000d40320140c640000016101d4600041a444650451408150b00550315001000c4440d0021444c01c030640c0c10a4a05d40140c40315400540c4410004000c490b54141c1c0110b00d8600d088907030714440900a21881002c580390424000c4902c0102e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 826834811 1250 826833561 826833599
    0x1151d1021060612030801030b070f08130f02060309061905010b16030e33030903070204050c160302010c0f0302070f0b0c090402031005150c1f060e070e0a0807 70
    0x141075403030240d525022008010700c1d04a021040b0104204804155020b40524141ca21402000c45103499a260944a40f8804407151002c2005440002c02c1c03000041c402d521441e024518141703107000315030080780176648140d611540903002542001110f080b10450000080785000b82003180d903241140b452481d010706440c00d613040340c0040003003040c184582510801118002c0c11600101146164445410b04400208103041c15840050a40f40c40d410103591094250394061454007001e0f500704401081c0007084080c66a80c20700502d942603040300d0308201c400c1d2284e000040c031036000080103486c3c03207024006181054010040c180c0080d0140e90610301d01a44036070300400c0380d1540280507055000da010080c1e089440071007000b030920031600d001e4085460690b8044050810b1440d00c4205109035a28201d2a510010607400c505101450403444c903030050030005203040e11400d0320b00c4008030980d803000005149506082081c5803a020050013440c8800c002c0040600c1c2c410040444642401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 826836061 1250 826834811 826834859
    0xe071206020a0e04020c1f0c09050d02010302041701020a02060f160305150612010914010b03040b04170a0c02090604020415050702060705160905010e040809060c01151d10 75
    0xe007201c8202c2c00f070710075858000b90040c425501c84086100c0b01c0c2d5075104000303100e40805241c400c1d1440c00a943d01c1050b209035a46d54407080c90702d04103410300c822544665030403410183d007000000364a015200c1d051507a1408140096555005141c000b442c0100140100402c03000f28001d2102c520162090204d680b8050300f0003041c6903940d58030411001409a9109412050002d00c90307030446408c0d5145070503564110000c000f07080903403040c0d0646c0e41d801d018040a180081005c070300440c00540d242d0340d10a1141303c512009543d240d481002507003001c9d1144012407070304008401145030a405150340b05034150b07411410a032030015a0610510400c4910302400720020320722065484110440700362a4000b01113803101d4440310044035243c4110f20a5900507071070040080741100103030350b0941c00340380c01c085103a00706070b481010452250700003640c0d403e040d0760322409a04075a05826440005048401c1c0541c03030781000c800284007801c401803610854400d00340046c455411391459045075007140e6070f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 826837311 1250 826836061 826836067
    0x1e050d0605090f0f030c07150c0212120d0207121106160507020307030b061005090904080315040615030b030a050a0f020112020c0615180c03090a0c080606040e07120602 74
    0x81140307800d1020155990340603000c0d88500184c4000c001009241d480f08000488001e1540e0300385501213002513141440c006140031074000f002d480c2900303c010409503014241c4100780c004d0480e00c10741d9403118401c000001d0300030408078244040d040f0769451a100c182072001c9401000c2c069039031501c04c01005229070100340b00060070094454419a60021390140880f0900c5849082c51a220704c02101c0301880360b00400d812040192186098848444000d044105c15883c4e5640b0030b15079820040c02000c0c01807004240050030303503817405181d00504140c0303030440780404218002400d584141d42c03014080c1e030024007200b0001e10001240b446c0650080c20300420012503200403a070712118a92100051800401c6a40c10080003241060042c3c0c0d00001c2c0c0003801c1401400c0c0b15100c443c1019910150312401c0028400180c140700669005c400601910103503102039451603010403840d004002c440e4010f50801c070035801d15128003401c00c2c0c203800052403c80d06c2c160740100c240f0a01000101200d4003c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 826838561 1250 826837311 826837321
    0x102010c140c03091c061805030a0509040e010f091211060109090f02191e03030e0415050607050303100506040f2c070c051506060f070203030f12011e050d0605 70
    0x3e009072290340030028600c0c146000400c828540700c02d22000706490840c0340c266001e0a4512440600180301c0e48003016509003c6200d505596680220b051690880d4903010444031021080c8207901901d0800c88000404142c00e00309207079a002040c40e62000d114016440b240302d0000000c060703045501140e0007190800070b500c0d02d00d10495040c1e80007508405505003085c2105981c98000c0c0944031100c82404104030350707000118000e05c0d41c0c48098040340755484043c40c0c600f032540000c403a0500d040c1d940e04580c0d940c2c0001c2117850340440300a490940000c401c0c40ba4801040640e8401800211801820700f81032100740c0343c0c2ca40c840d10810501044051642481d894815070141e0400c04119490100e031401070005444000030301002c9031309014500f80c280e8060000d2103854080e18000d0092800c00805401d1160140d00c0460103a0f4188028040d41a0145001e0001e144c64400d5440f204000e515014a450410045003a20600e01d03a0701e000502258a805440c01122500088003080e00d880e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 826839811 1250 826838561 826838563
    0x216080c061e2e09020c100c0e060921030408010b01030615050906070f05010237091202010c052b020304050d2a06050a09080f0a06051f0303090302010306050102010c140c 75
    0x2240d000c43c1074140003051900ba01c050215100001002d200d0052205030300d6483c0c2101d142c401524810760003242842f00c0021803c0c6200c0f0051440a42e0050400c60805107480514503001513201c500169111842d11005513454003c00c4c0c024140d1001035860180c5800c0c01034040d0044e404254001d40700810101c05200d00c0001d4070b040c00c0d81040c02150b465a04144d005540300a0042020344e500c4150580e501045003449040035425150b0348078220740b07081035161000e20440b0381003070341007080c43c400e0000450740c14080003640d041041c1000315801e444518000e460b440b030700102810b54005010422842e11040e00c22064980c1c007115446a040c0e05e500480f64148420181c510181c2e07006d01301056940d0000014032a804440e103e444c0001c0d0b942e0a12035030303101d000a4502660304850058000203500e034112030b80100e141485680d203450103080b60030542c1038940c0141d001500e40c40c0d00f0019941c140c49800050407081c4000e00040042d84030280480c0061000280848400a0342100300c0030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 826841061 1250 826839811 826839901
    0x60e0d0609030507060518060417070c090902211b0112020c070306050a06120b0606120c1c020f07141207061505030609100216080c061e 60
    0x5401041049801c40742e041c0103105402040040b5907076441c00010a6000003054003803060601c604004107820f6440f6500c88921103011100032a175068144400320000701c4030a0b00c41c2c0a04603010001602c131181c0c1c010010000c1c110340c09518076014840d50f00c1880600489e500b000c90782000e04c1c2c1803c01407000d0040340d0303840840000442140c40420360800c01d890204550044900962090000b51075000040c070032103109100f0a072420042010b0b901c0007441e00300313441d503200b0704c020062420407011017213078404113134120303140d5030700200018900701c01074500901030300c0d03e80d05a04114105800414868100d01c00d1a07006055081f0451848148040c02c2200000c185c440303800175030300d415480c500b52002e0480c1911110410801400102d403506002640d94420240407006092041c0302c8030b5103000941c4a0507403120f140c41051000808903404100401101404400401151078440c0080a80702c100102840d101c081100500c100ea5140000c80c0503d4120100244031040340c200314024109 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 826842311 1250 826841061 826841063
    0x31510030f08091819180201030b0a09020406050d0c03061a0d1e020705011a01141b011d010e210a090807140907031103010306050402180a0e0c0303040e01060e0d 71
    0x190141c14a480d4583c0403011301801401c100315090062a010003a0300c0954040595080480d62030009040140d8820f23040021280005061902e1454441c2c00030401da0703001e40c022402140000425202d1003c0d24410200c02110741e10f42040000d0400c1441d8010001458a88045404c00b04650343d5186a81d8031440c1d11107560b1040507000c001e200d003250040c4d08610b2042d1420351a05040740d202ca0303221980400710010580d1503900165042568031a00c3c0c201401009000c1c207200c0300345e95140c03006d01c0f4454460811000100e01c4000300da9034542581d81c205075903003094202c0280500600100200f40320402d0101e58241e45403141000308a424a003164400683c9200d0758400003024580005000503000060781c00d10420b95134400140d099904080c106001c180c0c08000400124025074402500f05100030841c110580610121610b0b1a00a0340c0c03804e040c80c1d0729080641c604000b00165001400f09402842c1032610308104100001c00500c207803018080000c0c9500c0b0746d43d4605a20450369 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 826843561 1250 826842311 826842319
    0x105042904062a08061314160c080a05040e01090e2116080304031e0e0f01051c0e0f010911040c03140f0130060903020309040e0c031510030f0809 64
    0x4003a0401030004c50140c5202c0d0284956542d02c2e0306040403402000450351750050300380195180d401401841807854130800003008030300c3d28200006050000200309014255503182d8030707103003031040c3c1984003041a40803020061420752030141e440c40106e4205544140b83c1c03040092403006200641c2c43d07100303080c00214aa001001180f080041050140d40558060b90750180071130b042c601c5400c004042e1918500206040d203a80f46074038030b04481681d0502c1018502242010a0840c040e01c1c000a000701d9043c0d00b030745400e400640000c04000902201203d20000e1081c0542034690541c110354480046000700c0c0c0f00c00d071856815005e60005410307582400f0b06108180340c00c55111010001c01e0080b08070151588280754140614503610f41c0e1080031440c3e05450340300041d9529401400810307000c83c20b42c04180146012542c403442944100c0901c2c80103454540d161408141c1400c565802003076145001c401030040000a00c0c80c03880950394000074400d00e0400d141880f01c00307401b80207040c42c3c0c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 826844811 1250 826843561 826843631
    0x2150c150405121219140106030e011512030e0a0b0313030206010501030501030b060907090f0803070b010b07080f0f0415030f1503022817010504290406 67
    0x15200c40305424030550288040e226610000707640043c007441401ea8541c10819100c01241c544411304040821080d00b40f600015140008042e95000c1e2400340d12220202e40c1d1140300b504e02d0780b02802140c0d4461102030442c84203d061203002021804040c4001d000c110a042c00780b030142c1c44400c0e180001c2c3c0180030b0070326200e1402591303600e44d440006004400600801000080f80d5000b40120b605a0741e001a4290040e5101414032003d080d00414440c1004094500091400b128822110240003040040d644e00d1a450408564180044c0e1048a0444003088040040399500e829145006508075090fa592000c4c4083c00302540243c0d041204c030303004040c0c10380768240d80640c0720710201201d04006200c22000c9200d40c2c19580c481b444080e40011040031181d0f0409440d10030104055400c801210742d0700c0d100d03010001c1c100c51079042c1241aa5440d0240010310103104410b0000341010048500c0c1c80240602202c0d8807040500f0080809841d10f08140c80c05420034003070740307000412148040c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 826846061 1250 826844811 826844833
    0x1401120606050405090c15030601090b0c15010e0a0c1806110a05100f05010b1608092202071b03170913050a09170a0512060f03030d15050d0f02150c 65
    0x24656a04e0820a485501c03100d00c407c01c1c01c00118180c034800c48050b1903080e0003502c5c20b40c1110032588105403020140c000d0200003440113a405c001e440c060304114140101a1900303000d60710450300d00300604810b003d102643d408981d43c01d8071451080c3c0d5001c0c6400b8002024140c0580d1400428202c010103501810030791500340b01302c03a40038418100f00007000344010b980c1e50285000d07900c10182c50511215454203800041803200d030080c102160702502106515001d608104030103607090b00b40705011900020704606100c0b480100980908940403018002882c640e070f2091400d41e40720000002d9040820031b9012583c6209440e00c0306001024180b02529000503c1801060440e0046075000150b0355080e1405c2001010381d0b00e00c4001d0780390185401401c084454428a004200b5030f40404000c50361440d58400340003420100000c602d0200e226280c031705030000302964681006024004031001200410010200c0350581501502c1c20740086919407072011040c07041d8140300005104103140f40c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 826847311 1250 826846061 826846063
    0xf0f05060f15040204031a0426070507050103060b1207090f0b1b071404020d0b0d0c3006021303080c0d02011103010b030610030f09060c020d03140112060605040509 72
    0x30b10492031420030040c00c040d10010070040703000d20302020700102c194940c1c44c114074070118980758100c2d0140c21031003032500448140d80101034a500e900c0c60050300216100d020480d0800c00f0001500302403c09014a07070030403100c01c0242c043d2084c000b80b55004400803800250140101e64050068007001404668480307503452065845011038100d40e4031642c5a0114060000c100c29050f20440304010416088400030032019400840305a408240d60700c401c800c1940d620407010f201d4038440e10603040c04914000100e01c0c200165140300307213040114804441c0e03c9586038260b110440c0e0103003005031584038210450384c09a410703810042c0074080000746202c14440c0050041107075120740d8001d01c0081009010410b4a0000384603440404c40d040c00814218501094215442c8819140011380380c00c00b0444201918200b100a452159440c590103100a606000d0074905811504040c0102016800940d0000505204a4003000400c100781020010030741c00c901c00800707008000b40490b0030003000d45 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 826848561 1250 826847311 826847341
    0xc03061b0210050708180c091e22150b12030409180507090e0a0f0605010501080906060117070c0506101509031713120b1b040807030f0f0506 62
    0x1410261284001c55103030b001e001c3c059184101c40e40e07650440d82c1e440341440758900311124252280f070b03401403140f121043d459042510380704080c400c515031140e00d0f131000380364802070b4040c18412021240041205410b04022700341d42c5c0c0c403648529120510302c9179200000081c00c030404020b600c4441c12038a43c000950000c0a40300361080140c0801503074101601d03804000b03c030031000a00a401c10401001100800d80c0000784c5403890314159100c803050303607407040d0303c81c40c41007000c948540d81c070070040c041540d01c0040151700c0480d0f40020041d5081040c000f904003020104408040101d01c00003612040c401c04809603001c0e4050100d070303024142181c940d10f03824614040d200099000d544614030292040000d601120380003075200704014080319481060b5407008030350b03044c0c40c500b240000582c0e0f004100100c0303841d030003050100d01c81d080c88171100011b00c240d10f04621074068103105c01c0c8a0b10a020844500702d0381d002d24041d65041d024944000c4403103803944081c00798051103042020703280307280c491 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 826849811 1250 826848561 826848611
    0xf10120b040b0114150f041502030c0114010e040609050102040b120609060603191515050d0c08060f01120e0d0c030e010503010e070809010e030a17010b04120f0c0306 73
    0x1c400c581e03212600380300d84d00c503010296940710180e4011421150b5206009190031500380903170394a0b181d142c198100080250300d0b43c0c00300685c4001003442e200d030420311506604d4003001d019030806503d441e0813080b109070090009071800c1d954030411000c201095044400804c1070300c2910b616000c0410080062107011146107000f07050740c03c0040c1043c6000c82c1164400c045810201041189442882c2c0c0180300606904001300d0350b09001013034068502096020003403043c7c3d5000d5480c1404014803042e01c000702c07a50014800d0f0036041c00705940d80c040c01d401282c0006e04e040011f0460b181c5803000540580f000c4a005030242251904540751301440d507182c120700a8881000c0402d1500044540748002d01c90201c00d070307241c0710100d2101445540300640250b40b040000c140d8103142100d0034150b0780b1406107600845c140f210001100940c20413064014403908550314100303031038581c400400d00d00380b2500500c0c0103a000380950800401040ca4000746411110401022010000d01c02c02d8641e803000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 826851061 1250 826849811 826849823
    0x50c0f160810090503071b0b070b07030f0507090b09010c0602030c0304050d020d0504090903020f0f0325020607030c021503160e04090c0612060305100c170903030f10120b04 76
    0x14032082c1e142140207840e186a07000d002140f13416055110b0b88440044218501b4240d40c2a00c0300180360000e88000d41034850046043c080142882030020341200c4205075803044403800c040401070401c0d00418440202e03000e03c81d48640d91401200100d4840c903194000501280c4040140004001d00c0005903100e00d00c14012200c0034409508160303a184d80004074a000039004200901c6440e666030820000a84640110b030044105011001c2c1000d0300d4038482d04955001017504040380c0703400c1c29141d10141611900724000302c40b507000310b801ca2054103005030a101c680780c0b8000071502c4144c500c02c0f88031404561161242404030243c4442c2e04240c0100d4009404545500554a07061040000643d844540300509030300e441c1d4143c1d0b01003501020350311110381c0c800b00040400c3c07051007411224044c80400159045150384040d003080f40702c600380c41d9001c2c0c0b0a0100b1411240000449411681c8030300d0f541400d45d958800030008204540084051520b9000c285081090b010000790295104034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 826852311 1250 826851061 826851073
    0x103e010608060f01050d0c0803070605100b0a1d010509130903030f0612030309110d03020105040516031524030f200a05090405190b040b160c0201050c0f1608 69
    0x90785155445206540741c0c4070700303d0464010032203490042141c00700948101012200b56940307582050642c2c000c0802030350401d89400402520000340e6070544040c000010929040403e4071344010148280e1460100c490300554948001c1d0b40e00900541d0b000305801002545141925011100034003140386003100031a04040d0417201002180c042c040580306148860740b0907070400c1e181240074041c02c00040e200b501107a0045061600da508003184064040d8001041a00b40307440e1580c074151518800e50503425a40c2010300c00034480c20a484101c1c0c82815004c0780941d1041c0f450901403503031004d88400c13a16105000410800300146501c010f501969021168800c8910007408100c04035030365541c01018000300380107500d0a0503055401602500403911070754409018050100610301095541c42c08100c100001c11400341c0c90907620403825000302038220308602001d0502c01803040020b05100300441d81c011a0707a410442118004140310480d10b40010100d1115003000c000e01036102d95000301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 826853561 1250 826852311 826852319
    0x30d0c0b0703050408120a0f0e0c0a090203092d030403060b010f02011103070f03021b1e03160803040305210106170108030d020304080c01020f180f103e0106 69
    0x2440b86a10403500508010304e410701c07806c121518000018000e0514075552850343e03000400c0d911686500840b214000d0094000c075504024101269a01400c1001d004008115500c540441c510260310344070128120b1082d4100b016841104d03100c10700d0240c504c03003c6400003e20500f904030325006242a00d40408d0b0341d010074012400d07100743d5880c1045000c810000300d000c01d4894a961509691585001410420047c1c0e840c1150320060030f0382034403980050825296080a00121014440650019450014040000c4250720640c0d900039090003004000202410300076000c40e00210b840d0302e5414000d001d0b80c085910810028024080001c451342e030081c09406460f4001d5058400c01002503040502d8100841e01031f50000340119140d410070300945200f03143c01d00180c01e41c0c0c40102a281e07111202a02e11034042100605414800c0700141480e064030b46a030b0019100c0c04096140503003074403540721207494400c1c82c168007082c1d005400c10304074107580700048004100d8a19480081c003c40340e807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 826854811 1250 826853561 826853567
    0x40306090503120609101505040801090c0501080705070f03200f010905120f0415053a020f0d0c050c120c0d03020405010f030e07030b04080702100906210b030d0c0b07 73
    0x101b15040e520000c5036080900540200052004100c171036480d1003072900381c0b114011402c0d1036032604111030340300e04210240310710340e0030034001d81d4012164940701d4186401511960561181001c020f4140406079a0b020141c81c0c40d0b00100d22011150402c9076003c40f01040d525000b41141070068039a03014a900603060813000e00121220064141c403100d0416040454000c041030000000038107000080286801d001009130400c002c008403e480b104044902601c44c00010a03001070314500c0c0e038810404203010701c1a50f03080e10440c01c030724600041c04008a00d8242d88612809140c001d440c844c82c2d442c4101d081e0003c1c002d05249109c041528418410282c0130b038181d000324090203010400c41c21010000a120b584590380c001544811102070650743d0b15114014001520142e81000e0000746400943c188018040c0280c3d486203000382140345440d20003050303641020504a0703040406001d11a00080726004003800d104020192030403040700040243c030403ea0301608540c8500031100040b040e43c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 826856061 1250 826854811 826854829
    0x70e04141b0328020405090706020c03010b0607110112020f04080f0715210507050705010c0e030c011d12030c160b0304020103050a020d0903092306090d080403060905031206 76
    0x58007034000c0c070500030004207030f40300c600d260750510001d8502c0c09256000f6a80d40e000c1c19010704c86000c090002a800c0002c02800e0074084540607001c2e031b051030310740d100380c0c1c46810441e000075402040c400005807880740100c0d02d00f06100701e02e540d0b20380041502c0900403071b408001c2c01250030810440e0144926910b0840c2c50381000c0c424031200800da005000400c90040c0003e040c0c404200d0700040601e020042118121002030701c00200055001c104079041220902c6010100007590034038a10308401b002c0001c0c1d6541001d900e1a04010040c08030510380241840c4080300c202005050100366460001c501d6680e421105024070305100700c1ca145175402c00c4081041c1c080d41c0c4c1c103030310980c55603030f6980043d0054400a8104104035508006000800040f841051802c03486581c030241ca00d40303881c9001c00610034501c440f4030541c442958203007456031280110b5610070400e0341c00c64400c03840c5083c084542e0107180d0001d44000e080c00c038600c00300301000c00203010000300240c182c94240c03208000d01c09010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 826857311 1250 826856061 826856113
    0x3070b0a09170d031d0313180905060114150f1e040f090504080c06130201120e1c020721020a0e060f0909120706020d0617070314070e0414 61
    0x14120b11881d4030700130300c241c00c00c001009628140902d255950403105103103038000944154510170032a03040c0080d0603c07914a00f04000582424030a5600700e448003a120380041c40390f84480c8100c81900c0d562926240344207509199200040c3da210b040c205201c0f11183d01034200318102c0710710583d05900c82c80d504010768041d00c140c651805d0b40181404a80c400030b080c0030b03100b603a00c2d00301806031100355041049540e10843c0c070041c01c40400e003118070014260860306c20007100d190b070030420b0000f0300a03000101d11041c808900624010881c0381882170b0304205842c1c02030400385041c00101a0910b04851018600e24401d80d4810180d960300c0c44a40407503002602d9540d03000a000450200078a807510841e0f421074902002c3d50100b080c1c1d0480181140d0110804071021600030618080e0000d00788280c1004043c4501d107a502e00346282d840302d44401050000501c081c0050700c000740c01010420846003c2d09401044200c14202810401e407124401c2e0307413401070b502c04c00c0380d07185000c41821002aa26 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 826858561 1250 826857311 826857313
    0x6010306060804030507110d200f0f010c060f0204080d0207060c0c180b1224040206030f1905010f05100f091a0c06070503090706051e0a050903070b0a0917 68
    0x191540d80d800c41712940b080e8030079100c075010038003060560365904584100c00c91140c014850f0941d010300040e448024407200c214400c051595034030003542c454405031251450240781400420003d42740c003030010701d21501c1c03140c6030620105001c1100c2e84000307a88481070b00300380c0840d42540e54440301200ca4414611008044030030280081000b41100c0040141c0b500c49450b02044031400500850304440071308410200560004010010f000c900a0303581081451002c5911150726054011075020f00c00a4001000d1101c4036000803200200d500a045240c48540014801569521180c2e134409805008151040079641644210280a0100c260100e800d541311031400914010a02c5980400040e41194442040207194540b280074441c44e4410b240716226a9201d081c6501d0007450402182c00c41c20902008000d032030b031440203108441012904000c100e50b6240c0354610203d640e07000d20304403036405204100f40444c2541c1508064544003406a44001042e55212049101c9102c2c0384422016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 826859811 1250 826858561 826858577
    0x20609061e04020f0d05280f11030a1a04021f0806040b01030902040207082203212601080105060d0807080f0403020604080d12020a080a05061f030e060601030606 71
    0x14148901c1c001d540140001c01601c1d0020108001c2036155460351720444140d0001e03481404000386c0d1407400ea000b01491b080c90201c01e5440e80d0f43c0310f024992120060300410500901484075030382080380480407a480b00440071052500340387d003440800140c4089119a0028503414820360610280403910f188507501c81149413030b40c00501c1b0040000d002480e04041d1281024409a121070000740300440c440d4000c203680340c1840e0300c1c51442d00070403a2045a042c41480e020404141700000d4901c04440703800700d042c103d4600c2d49080e140c01041004c000501510840c2c40c0a0800b50b08842c0d604a409010081c03101c1e694400c104444040400801031504800707014460110f900c82c8003901030501403c60952400f82ca0340c0014a55801c164404442540219006680d0541c02441c0c45400d14640c8400e504014842c0c10207003040700d000b4100244075658400242075561803107070784403e62400d1060f040000010b404000d001d046c1002959609100b514041401940300b88241e20484040d07a4550751 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 826861061 1250 826859811 826859851
    0x40b04020c060402151e130801020a080a150e01060302071103011523060f0c010f06230a0905070e01030b03061003080a0302071209030b1b0901030f09060c09030302060906 75
    0x4054000710481d4043c402c414441919182180114800100010084035494100c1047c1c2c0300d0415409402c1032489034018071001110b0303500600e8550300301d0f140c2807011800800c4800181503c41d2591b101015000c1c0709000083e211b5015402404054001d02c2d003003064008420516003a1801a4003020307003030070440300c00c02c04025280d002443e511408500d1a01c50403001c000103040d90801300c4001501c01e0006141d40d00003109201d8143e2500c41c5240900c0072070310300b020b414940c02454407800400c6510308080e0100e650381050560150207503040030059400d0103a00149140d10070f07021240442d1130043d00d4540307480c00140c0c0340d21a812203075071440301c3e90039681c44004940200e0120814903400740302800c002201d1020b9041191300030b550310440e05166040c5480d4a030343c060002c46043c0c000248440124245204030b60540c1400e0902082c0e0200301c01c1008000d007405c1401424061400010108542d0b1213400d203c103ea009601304c41e615105c00320171039101d100a4a25413200030031200a20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 826862311 1250 826861061 826861069
    0x20102060a150e100e0703050f0c090f090705190804020f1009080303041518030f260405030306030607050f04051c02060304140d0f020705130b060c0c040b04020c060402 74
    0x3a10b01c03a20b04070a1403503269108040c2d101010181c8114220806086080c031484290602255100308586010300c540d04203020034404d8000041c00b1100075290004440e081034941c1800510100d01c007400040701460142c40042498101d07000030b400d840da0440b0f401d40724070300c12a5824003d5400812044046501d0340402c10180d20114081081c00088200060050001e1018512075401134042130004140c10f0846021038240f03006401141c50905041004654050301e0b60244116900303142d803000b98803055840035003031b0240a80700361003100c50401c401c201010000c0c60090009800315549500c8a007001c2d10140684c0e4680801683c007880208418038001489a440d05002004074800041d241c010900c00d51040790255081c0721119820b1032074070010441d40040700f51501e4030010389c21100a0080d00e4100300d00ca818458121005c02c040c2d500515400805503503401000e00ea41d903078544940300d448110080c2c2d0184110300e0015007800c91b0806000300c502c00fa000070007031b10456039181d00300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 826863561 1250 826862311 826862321
    0xb010c150207170313060615050901030e1213080622170d020c030304021f23041d090607050414040e0a23160303230f1602010e0d020102060a 62
    0x40d10300d046860207900f103034070b1640300640c0581c010682140c807002440c01c05030117880c8030744e201150038201944244002035206040c1c1b032900100346000f141c5024916440c40c5404405008070901e035a000503a145612000e8540e00122003500e815210075607140c40c1e03560300a07004900852195440070400e00000380f4000c209482090340d40c0c01860a1100020307000040760024aa0501941e1002060205525150030075450b0304504c0100b03501098000d580081c0800703500f0000488030805044c1103c4200c075140d099030041d01400c18050801c101e42100c0603c01c0c4400d6440c0c6199004140100f030310b5902c160f0890742560340c1c00c603c0880c83c00807a414400103201c0e554052969004500c0d0080c0080c1448108201c6c100c910510125000300d0b000c4c540b424070344000311015020461003010400250000310038600300040b00500024804c1c100626079951040c10100c41202d1400514421140b145920401045000b0b9a590300d00220b00700030302c80c44224103500680980c3c0140e0020301c0034a00340d045 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 826864811 1250 826863561 826863563
    0x1403030f070309080303010605030f0a0522050109050f16080a1101050d1401090f0c02151f1d16020a02130c0905030f0c01031515081003050616030b010c150207 70
    0xb0302c0f41c10b82d40c189850941e002a048400001c5001044c03104070383c0e204107015005642c402c001c0180d4108122404800d0300d0f04d80c0488120120600b001c02841700a5025440b195040070650b17220740b1041a407607440d506201040130b808102c1d0080880c504400140708515241c0c072809941e4004c01d00340064840e500624204015144c562556210054200c0a143e008004912021424038052541072040d43c3c0c070300450404644c450150b5169803c0d90542e4250402d0803d04440c181c0324003032001442da80120303001403100d100c4103028cc0c03c50400384520705104001c215480c24161400900c12a00c44880c0b01000e036001a8107103554801600560206954640e0350921504807682c03140841e042250b021406c882640141c102d4174100c0d6051b005105c0241c405054400250f0305116a05840708200f410381d40800c00000c0000d14034034090040c440285400104807011441d1908003407580e02da044000400003030401b0240c0c0c2c5039500521200704550340c401009580d041c13460310070718000d4201c0b0b24 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 826866061 1250 826864811 826864817
    0x203040b070c18090201091a180303043f03020d0e01050405042a030203040c03030c061503051f0e030a050904090209070c0b010506090a140409050607090f1403030f0703 74
    0x70b00060a55088103c2c00d1401e540d404040340499290001610035004c0790300c4580d0485242c3c102e1441225030000702e898040c00c1c131400c24401480440030902d54000c82d0445c07100e40d064100c40300181408254844821042c807101c90403174410822103030200c10703400c4000502507440003005283c694040c0d00c0e820072807281071411906190b034541c0000c080ea40a2403100302c2c206400903010441d0104100100d00048490609515500b41640d940c0303454001840b020b410000440d52410400406401040312400421886403902da101d00309191100982001c0c203602406010b9030106480741400b80504003130b41103000e581061203000065455600c200304080e8041d81e82d102e90790040e03884503161805150700d0364999441000904c0c01001582061304458402c180c2880710010307658a0781c0304642a00c0c107003600c40301d00c8900705000c18003801d240c09004200e40104802c001c1e09170b80c884103041c01c48003803040505a82c0c0d2390b40c0740c4103480715005850a03016081004501004a5203a00808046111345 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 826867311 1250 826866061 826866083
    0x303020a140d0e15090a0206030a11041401080a0b0307090b130212070908070f180905010f320f061306080334020f21060402041404030203040b07 64
    0x601c1c80d0060384484207034942107584100042c40c0700002c000720103114204001241c0c0c0d50a000034010355407031000c44000d1007200300100190701198103402140c2a03503190f028298486454a29840c40c11008080c1c041c0028140d40016a48080302d02500b81d8915000e4003500410741094003180141245c3e10100d50000c030300e080114900f607030310701c024035501e551a65080290300f01204014800c40c0140d0080c101d43c1d002580901a10035031015100072201e5000365000800385108002d0040c000c15a000741840d480d205803e0000d4005401c141080140c01c1d00b110aa96641c0c1c011103504400302070eca5003c03210440014090214141c001074105070000c10305240304640c03d41c00b00c141e40541c0c109511035080031592400540159800800c05603004600401007050701b8a031450300c00243c44064801d0314150818041c9480b4a011a502c0942e1426a241d4021804000f81c6e5a000283c1d001c0b40518502446d00384610903c90049008503856805103150901e0301074280640d4011540980721400e0b08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 826868561 1250 826867311 826867337
    0x1507180b0a200616080412030203190e10050a0207051902030c06040906450f060e150f01020a0609050106170d08071e26011e05100c0303020a 62
    0x41c0042c07603440910070010015890710710000b0b041011580040418407188905110010705031202c1c0300d00c981281d1600603103a98030a1480c840400456011614081c50300589052070640032940000c244606441884a030311003100f03004c102d00c500f00000e0880d8110082603003001121181a00202d0300007412600030004d0784001a10703550060307000710303400c0385e65603002c00542829491782caa6a940d100560b90b4084011800110180344415110420010a4041ca81402002d42c000740d0702e80d840380f0040111a854200c002103104090356901000083d0001c044503070310b04581c030110070b110107a025103466082c50355484041d0130400c104030340c1e035500c0d48400702c1c1d8640c4483e90400c245415000810020b400c2e05400317890102d025040c1c5003044500301c000c8016481850b44104028150314080c0710b00b402140c0e1001465a05014410781c56040301c000007008400301e000110003c000740901c402460761401000840043c0c54010408683c40300380d041c001c03c4c00380d4081c2c58800010b04111840b0548 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 826869811 1250 826868561 826868597
    0x30c0c0509090303070f0e0609010e130c02010b0a05030a212102071a06010e0d0c0305160503100621020f0409060519060317070c080303091507180b0a 66
    0x110303981d003103c3d8404400c01000035448504240c99804078204401401041400710b520341c4075400e0264184003d0303c504103215190412908144c00c90707414108205406010000e010f844034003a118466030411202091911b40030820207001c83e4401e10f00325075842e40d59078070401d0310642413800040c003601400e00c0c04001800240d6007907100040000680e0b440291030710090f01059041070b0900300b070050b007c0000b0360341c0081e880c1d480341d8022207003521111800d2625914062268100400034015416000b1031090191002001daa8080742a41c0a11f814620380c202111114030404400c50000380c0f02d01360707001e1401c0c0c01c01c0c0900c1c0060041e01c0d900d1a243c02207030903111401004c80700c4a0b41c4804010f2600c43c100210402181000b0781840114a15282e00020445c3c00c07510011110000442c94104800c11944900401100050380d8403880c041d0210398540d094240c45058903184080090521031040b081c1ba100d2002c10304011003154108201c400ca90740218480c502801740d400c0410081c442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 826871061 1250 826869811 826869829
    0x60806151306081807031509080d0506030c12101109100c11040b0112110c1e24070c021504090f2a1d0a0b0a0f020d0903030c0c05 57
    0x80e02448024454a4030b480200b030745200820b046140d52504840380e41a080202c0c2031811687c0041c05940e08110000d07000005140340320005121241c009401b912031422500002d110b42403c40c152900c403071658090218618040d10703040050f400c406002115440b441d070241550400381c071402801c0c01c09681c04200101a02d40404011918405079081002004045054400015103045c80150112800640350360024800464400d44400032000140414001d9800b200042c0084445111044082031100803812400c000d0a004180c00110010f203403c44003c0d03414a0100324448541c2d484c01c0840d541080200120380c000f038003a0726404000301d0307034028101400c0b24680001c3c0b02001c140780d9404039441403101001b00107042c070841c0c00e5100c058003214003262a40c180785000c1e1201c01401020b0b501c46812943d0300c1400c0000205d16805079802070320740146035480d13035407428800e1441a652031010140800005145030006e000091003604562045486031032810802615a80040d108117 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 826872311 1250 826871061 826871077
    0x1104090317070201020a050403080d11070305030a0c05040609050603100b0301230306070c030804060e03030124020f0d111f290d0f0311010509010b1011060106080615 73
    0x1000241caa40340d4a0000a486820080d64002140f0b06509a00040c256016610020b49640d4001c90350f551030f00c01540100c0c80020380301308090f90b00c2721545000b17019034209071503100040f07140080b8056414025403c990a841032a11491b00f000e185c4000c004899200401008128003000000a01d500d90903004e940a4036410008440702006141184003e002c1a1642c40c0310380c1c0410140038034107400241c120700558040c6800310340c41d9510308143e00500000c00095131584400400051440c140310015400d804a0605030017280303011640c00c1341e17101e8015881154941003c154000300c07178024850701c19160380341c0d0150380c203d0298584110003018407010058100c0c0c1c4820007981003100180b44c070590b03268051680743c02401100c010401c4000e80c1800144000a480c41e0791003414016140c50048a100074020701c5686008004180a00005c6800c0c6026401ca4600d00380440c1c0101c2c40c4544103418900141001e80c81d0410460781d80c54041c001582181212101002140410004140b89 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 826873561 1250 826872311 826872317
    0x52104051c1b0e07022103062e05040e1303170603012403050106150c03030b22140a09020114030414120301030b1506070b0403031e1407020a12080411040903 69
    0x10b01c4c01d030a010b41800500d10b01d5451070700c01d0311441c1c1040098042030380c1e00302200b61019030850680012401d00240c01449114025001d210b600901c10360000046c408c0c0c0b00b82c07541d02c40c15900c60103a00208204000c5008021503902401001102c07410349045030f1156008002081046405424070b80c034041c4603104d612095a4050140305011090107a28001c044420551910000c07988009010901d154030041c03c050320348074400721503941d18110101c040140300202145d171000d0f2507150001c0c03121980000843c241d101c0000d0016081344580c0524980686410424a03e0350300c0c004000c2d4030042040307039110010f5102c00c032808000c001020409000741c02c0240c1e2035056042c0b0041d01c820060086580d41c00d81840c00803207465a500b80c811140e403068890143d81c940d464180d02415400d039071580b4075090328143c0e1f0282c0c0515042841c81412010301100d207034541c0072040743c0f913007031065024180c24405620314002030701c031310b00982d446070084102804c04951240003500703581e6400019000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 826874811 1250 826873561 826873589
    0xd17030a1104054b0909060f190603080d0b1806210a140f0105010e060f010c050705150901080f040c05060d0b1c0515040221030706020403052104051c1b 67
    0xb290074139208480e08400070b60018aa1481d001a408202c000020b04040f610200c00314041c034409c1c2550000303405182d12a512644502d14440c0910003030006044040c80798100a805030a2a00305002045c0246409003141a51440ea00c0489640040c0348050413018820f01010101003100c0342c03c1905403032400005080000c3d10045c62900b5114103800c900b801c80304001c24000181d80749145018100800c2c02d11a1080e000c0e81000c5042000e42d61049401000389240e41c9000101c000c0281154042621407200c00e0f00d8440c40c0b003034640c0c012580200f030082d004409025030700d40364021b0040030210030804191507441b5804a40310400000ba506404401903640104100d001e02c00c10001222407090041145040d40010b031400d448040618000040c0b40300013940d0840900c11a02c156400c00e20035559541c1e00d141c0240c0e07074111100b04818000483d00714040215140c0b04a4040b0ec0b0002e1240c600104488030135015030700743c00c1c8100c40d49810040207940c83c000d42d60007140184a901c490980c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 826876061 1250 826874811 826874959
    0x708040605031e0105030c12010b030109030e041d070506090d05030406030f0e0303190e0a0c030804060e0603090319030f09051522110d17030a110405 66
    0x503501d4941c0311443d40c0300008006001540b40020300c1d00420008a404c00c0b100f0748801c004030300422401400702c1d01075080a00304014180c2015004a007100103070780802400944011000c0c20380c01a10784883c0582080d501080f00307291500140200c1c9000511a04405e0080d41e201861071f0300c60350041001c2034455101007240d0505e88244154003034410061443c43c41c00b4010f1111051690100380d88a5903620620b00600404000b0780343c010758400140b1840e5909c0c0d0512a1031604180700310000941d032103400900a090540680b03000b00181401142003c1300b441e201c00500e401108048205a0340d1003414500840d14040c44400034054005414000d88000c3d503240c8600c40103114078103141040306400300c0580f821640c1b510300c5410800c43d100d4980503900095407459070403400345c07502c854940c1c482c0c22841c920b07000354020881c0b00c60400810070b500e00c2022040c01148102a44907021303d4a503424020809180c11b000c01c1010345007030014084400d0b454003210f132201500845d030a0a041e40d0303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 826877311 1250 826876061 826876081
    0xd0201030219080103021c02010c060926070b060a0b0a1103120705090103050c0913051302060c0d020f0705210718090c050f150a0e090117060f01141005070804060503 73
    0x7c940c00031144151072480000d800280c03401f00c112500034000c9a40d4400c51090004d41c085220210040d22540d010b515140e950f40707001c54225410603070f0608290300101c0e0051506203008000c4444011b642800e01c0c80045c000d1f1400720307020f855804d00340020807243c5890496000c0991040006444141d01c0d41c1d26007000404603480100407011403d010001107000c2e9440010b50181042a01c102080550300d56501c610685042400290041c00210710080d102c0c5021407400c000c04442c0c1d00f11180000e41010540c0cad41c29191040715000094030320b5021540750800601085075030386c54100c0d0b4510342c0e180070060b01401030325a018941c90792000c00700300300484120131500510781141c020403051402c0300000e1600d50080744034544080c0004515406900500f2401309074040109020015a0f4a2110241d01e0126100c012f9117030090000140000b1002c81d000d5040c1c40001c24500c1851840380d041c455000d0502c0549e505020051102200043c00344000b0710291107a65a9140c6a0404140d10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 826878561 1250 826877311 826877329
    0x90d140d060521101e0e030403021302070b1005090c1809040510111c0917030f060901060309031707050c1006060305090f100506060c0f0a1e020a050d020103021908010302 75
    0x41c1c80050510080a002e200b02d241e55603003418003c60001440c8200c1c0b1103147c81d41c0b04540c0003d400c86103100c840d031607002c0184d01600300079000300f401c52074a5031b421710b600801e0300741c2d8050154400300d0b400114410b028003e014201d2200605810407c0c1e03c6000001044144101d60450b120380c400c088010300c011050151109800b0350682803030804619609112580004100d842d2a49a480c0d1301041030085103018000c203403018a039040d542e0304040c0000c001d018011a403680c020700d07080c8c000090b01071280c41590120f0390550390b24000d512402000502d607040142000c030400005012107010f010081c81001001c95800e40d001404074901100602920401400c40c10260050442003448500101d0402c0c0c030400765000015060b6141c00c0022400c0c000c041103a0f10a101c6c080d0550f803170302d2001495104881c02510440003004210b0305000c0c0810700164002d4101e0340200c4100541c3c01c06508009080341305040c050b00700070186036410800c400c0c1c4a610800101054010400d40c1409590 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 826879811 1250 826878561 826878583
    0x1404020f10021005040303021204081905090105090906040b040e0109050d0206090a0809011e03021305150a140c010504051507080714030403140c070e090d140d060521 73
    0x2801031403001c80000039488001c15080c07180d1090716000005c04240c481d40c1280c0c940c1d400105014400c1c205414194802e8110007e0103402004030030140c60b81c5400348042c0c0f1854401651840d2805000200344080408060034168029844142507081e5658030701500150580c0741000150a80007410040e103003554500c2c1050554000606002c652200810940800383e040741c401903a502d1484012901c2c001d00e41d00a066860641d009129069070540052903440c0040c1d200c054195166020002c03003040320b2146085071401004070881c140d0203500400040c00307030035034032a081054910784142514802c07501140c032074010704400c0d1507403c42424926003100441c40c048840e8038100c00007900081d04070000089407400440005c1c209881800c04484849801101c0740c1c54101300ba012555a01040c0600407104c00ca200c0041c0d410800066022041c040b940d8a2203000101030b01c45400c1c40d8401c0300001d138441e880342c00108058485c07011085501c0350b040745a00350101c820441c24106008204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 826881061 1250 826879811 826879819
    0x1d06060c0d1b020a0e04141b0d080702060705030910020303040507031e020307080105060f271b0403260c0a11061210080c0307060c03080c0702041404020f 68
    0x40400401480050300e41480d00d01402c00b051840201c210070189600007050095000c010420701107a251103842145000d45e00c18000d81e580006240344080d2100020812402c001c4020041030601e8904840d20b1514240903005ca68a0a203d03600421500c4d4807c500560b5107a00004036002103091620794016650f150b44061030440c1800c0d6140703a110099444060306440100764007450300c055541a00909560050844c2c03680ba42d1900b02c91f028010031144039208000b4014045841d081600e4807441c2d0b000c909082400030300d50032aa28004010283c10822041006c1902c805049110ba0040c00958098201044807018a10300118641205c0e01c2d0310941800511000c2d104c07520001e006240594000480480050b000c0c01080b0b80740078003a440343c000d001c0c0c1c10510160000520a00042c0d4603000150784206262070241552080103100785d6000450807481503011070300c941c0b03100d5000038506010342e161250f50707000201a40c100075038010f10b40c0c1c1518284030852074415400622400156 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 826882311 1250 826881061 826881067
    0x212060f010515042103020118020a090c0c02061b0601091802130b031015151b0201021f05070905041122080d0504082b11010609061d0606 61
    0x1403200c10800e00600ca001c1c01042045010504848890305584c0500704089803d40301030601203482c1a0b0721494102034025518048030680401e0580c1e030702c00b03406038000c0e00d0b003800c03107107007025010007004854840c0d41000b03941c03c0c014005035034000003000e00e00709851003030401661426403c2c0c100841039212440c103d142c200c051055604403400255040c1e01150160300506101c9401e50183c540080c009606002c3e03021414103105c01584030303030800c0440d00c90305030000e500c031900141d42c000307400d5000011031042200b4a08900200000c441c140740b041c4191041c095040700c01c03003180195541291200b91301c03081080303422b5500c0044c81009000403541403200c2c00410a11642c0340c030511841c0702c11410b0351804090210361a40001005010280445c1c240f050100d40042035a00640550111400342040e0f403007101b17040304803001c098103a00440440342225000280e5038000f018040402c1e55407112400999503059218030350041c8408160b13074107200d0f51442e130801d061100401680c8100018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 826883561 1250 826882311 826882321
    0x70903020d020904020f040612170c060f190f020301230901060c0f0b0702030318060601080c160501110a030b09090709051e040f02040f0b03060c0a051e07021206 71
    0x410040e92003142c058440d204541c0340e500118032000076200313000360041c0c2020b400280c58408402c401c03120600400307074100481607900303405d1450712914030540c4548d0f020401041031502e1804241f0b400c4050610094020381c4002881801e07920709041200c201a070100040001c94080e0000e407005541180c0004120948000061101c10701801490208040b140442e0204459120405401904802c038a4010300e401d94000790f40c0d900071608003201c2241186c060454010004049000313550585881d641c5580e100c20144d1903411101070003a04001042200010610a21541403200c4045480581d07030700308247c0c00707400e8549811380e4601030038040c0c1c03c0002500300402d00b48159581c1c0c800c00f0400d03440c0e032814041800e181c140310400c2002a032007030004100300300c0121940548251410300030489101c60781012034181901190305a0400d4000450b40905880101885840e80c207001d410410000d24034011180007025001c40800b0000d0174100754a40034800b11503202c03825008100038542 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 826884811 1250 826883561 826883569
    0xb07030903080315030307050a1208010f0b0306010e04020d05010f120b0a0c02070b0406050a0905100e09060307150801090509120d0e1c4e090b09031207090302 70
    0x9144009011290b020000c100515100020103401c204010101d0761203802c1030900039103885040d003040b28500e540b501400b4850303001d440624102d41e020040030115601d0102503039801c3d800104a10b04005000d007107680c2e66511071020b00000d09542e50000350719810103540c404800096000000c10034210f0038a0f900051108140551280c5810b40c00304140d1201b0b0000c0c1e1814a05070000c610608012a010411540c00006004421442e644180d1642c2d5076005008051035255258000070360400380c4944203080004a040e00b00030040d08581c0040c0e500da05c0306d10100745400951001076980c900410003072625001ea03507044410100980324050880360103c040303106d50041c69088039151104030080c40c02c180b141d8070b040001d8201c039401241c0800c03401440030100030b031142050720820455015034000d9028003c000320b2088a94500300708002043d685000c03003140c0c5013200e25101c410020010710344d0342545000d03503c5c0707100640c0ca82c1034060320710890400062440c03041101e403034010030150b52 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 826886061 1250 826884811 826884827
    0x1080f0a0204230103050d03050703021303080a17160e181602010e0d030b01030f06030209240d1a0a0c0903140f2d010504020a090c020a15050103020a0b0703 69
    0x25040b5000503001c01c1c8060b1561200b180d80c1d10591201a14030b00000600c000441c0000d03000c4103e641c100000d607115402507080b40101c00480e81040b64400040c80002c24070310042c0b84050303d40c00c000200da500803041c803100302e1044070300301d50711191403030700e0034045800c4418114400011210754110764210313011a40f541100410264100c1400107101008900031340c41080c10890081c00c1d50b4081704640001303006030400c00e185500180c0740140303088051545200c2e12060320341c02811003420345c94401c0d03015071081c441c0d80420001c1da00241ca103045907452400c4e5810b403a128008148500180204403030810400808010045003040c080140c96030b4441400401d0f2030307006401d903901c100b1181034146041d400414001c26440b4210079028a0a01003a200c01840c0c0603400d040700004031070ba212408d942d41507070002e4204408200a01444400350440085403000d84104c4500e040313240c44407015201104a01d00040383d07a80018811b41c203140003824090240403249030f00c3c20425980090800d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 826887311 1250 826886061 826886063
    0xc1e050609132313020117041a0c040801020c0a0c0f0810020f041e170c3006131106070201021c090f0905090714060a0323010b09010801080f0a 63
    0x43d40c1c074120030840c0751a03c0c54184050981881922581c40c0001e50240702c01c100305801d9022a60300c24000c10b110f90380f114040e10031640181064844d03042521501a012006000c88450401c2400003050101c070901c0540455910100203000c005528104940210241e800c07000c1200010316090010600c0012070400100c0e040100507614520b04680c03101078082d80d0072602810010300201450007400c0b603088007d940b42540c0348240102140c5090303070398921803508190060303060046007070f2200302040c1301666002150299204d80000041c018241071080751f2403034450203074008210910503401d81e0300c003a811080d0354032850304031b840e00043d5407101e112186d03c4640c0e0200c00011032242c41814124010400540800c00240d192061039028100458000a051007121f000003880d174015201201203160151120780740010140086002c0c1c051130030314036250015082c52000b00402c24410500801c1c030307481e400d51a02d050070b000400c685010b9010782e0581d400410180180203010619034112 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 826888561 1250 826887311 826887349
    0x4200304060b0a0608060907030506030a1401060e07050301080c0105030103031409040905011a09102702090a060f021507120e1c050c061305070e0c070c1e050609 71
    0x260365610303100015020360094141c01001e040f0000071007540141010703000709421034401d14a583d5201e0100c0c01c0310000c9076942d62562140989001107079480d01c1c8008849110400401d50585a4100e1045040c090ba0b440780041d0002004100c09282030000c04948042468850b01d0765140d03450041c00c2c0e649801780c07400f807041c1c000b0f07141e4456034996100341d00040d4020000e101422200c1c40c2000d145035040d440e503008003003840010b40f0000c820100c1905403200e4002001682400002e09442c2c030b4103c2003401cac171269003005040c10f513940d103203070800040c2010340d0380c81203040c1100030090500c031421b03034a0601e0031410805d0160b82d50708181219588038805000003804081101601d00d45010b021b850014800d0000001590380e52250080242000c50011184241c0b1107407400343c0c0300c0a442c24040e0103608045030500940300c210000310781008400600c5820154103864000240100380e100902c4288003219000288260140c404020310007141d0300d500b080c8680e400305140321808140301c184 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 826889811 1250 826888561 826888567
    0x203040e07020a05010608030a030b2403091014040c0b032401170a0204031406130b0a0624020709060506070609020102011d010b0103060b1c09080c0f1005060420 71
    0x10a41c402c0000f079a116801100038056a6a05c9045035225400440381c480040d0030003040715405d0918940100602350b0041c0c141c080240c45d0703203842c5800d40019010030200e0045501440c844002406030340050f039400c2c400380e200c0781041e140c5060201c01550046034610024010042034030445a040154401d41212a0600410041c0100e840006016043d2840705000b01480308044042d400303002030f00d1082d498500400182603006640e03020898010f140302d035aa02d44200003400c0d802c240e6400c10124034000c40d0f0180c0b25190001c01742003100311551688500c2c0d150794001a41080740200901203094100135150a00c000324145100340140503003110745484190301164401d6200800396407038010400002014a09158040d1000c0720b565030000c1d040003400325005400340102e83c03042c480d011024042e0300120814001420010f103080c0c030031030720612070b119060300203020180c21003141e1000b8000351411700301c200c0210b85000e4a024007651900000702e0704002c0b00c070442e0544105011501362 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 826891061 1250 826889811 826889821
    0x1d0d030804080f1206030f01090206040308090307090c0806010905102c0301020a1107051801230402031008011104060503040320100212060103092001142a030304030203040e 76
    0xd039200707070703d0034660860000a2940c1030070541401e4900605003241550551442d04005238240c4285440207544a80104420800900310100410426802500781d0310582d556503004421108030101d81c6d00071440403c1007055560b404030700034028010480d8080f004486000d0b0081c0b1048000401442c0c0758400c0c80b0079003c507020000351f0740558800170b000399a030300e220810061040c0104020703005c00303100b01c0c1c101160354034100318841c4d0500190b0311005078583c0303440085502c28038000520001c1a1010341c180c0d080e030f1034600003580700c0d000c1000f001c0b80ba07078039003042e182c2121001d04444004440030300060010507800401c880e001501468041548807612000005126030446080c0d90391003091444659007400e90042e04500720100085030b950307550480154103881008900821007280c0c1c05801d200c000e00842c5001d0006410724180081400e0010400d426a0055090184d84140d400c2c41c002c4c04130b40c090318246083c0d002c00286085003451380c3d0103580c80c0202c1c002c486035000d207a0001a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 826892311 1250 826891061 826891073
    0xf021c0e12030a0c031b26071b0213050411150c0c310606080609100e090a021801090b151608070206070c06090801020f09040b0f0306040b071d0d030804 67
    0x85003c0081c203586c842c00e03014030a000b46c0f400300d00004c5591166094203806401100264035944100201d446d4170038504112507044e512190360007002c0760b20200f000002d50f040c00c494880c1a12481c0703e40d0742040601c07900010007071011782c0c20748036032030000d070401031022400000b00e07500c2071f500301c1035500f600c41c0f010300141c04c0c0c42c107010203024421042102e1881402032034139070005130445002c0e031a44a02134032030310144000c2d0442159080303543d0310084401c004c0d61007001d104550240914082d901c41030300d554000742c806041480b800035101e007160014441111203100c1d03c1c0f1103400031194291010142c200400050050641c400081800d181c00b80091020a10803a00003540c0103200580e50b00c0e02e89003680b01c0c440180209000035030f21840102d14400c051003115500f4124443c22810500c4450801c8050098003140640110b80c0700c02e0b440d950380301003100f58011071142d0220442c6142140b070080140d0b009400ea1520b4408104014090340c0300c1c102104500c58252500840720703540c2d0308000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 826893561 1250 826892311 826892321
    0x11160f0b0702030a0e0a0e0708040312020f0c0c09040f0b061c12031b0207031401020c24070305130221061005010e0d0c05130f021c0e12030a0c03 64
    0x90440445281007198466020004003910700c00740d182e01c0001301c43e00c011300484d40321030f0141380110700f8410301250000d4001c40487d60700c1f512920713086000604030540b88003640c2003583c20100e02d000c0491200980750090141841c2c10605552a000d00e14280d01ca01d11800c0078020058142c0206030007092541d19034814400750072000010091144485107413002030421814507010000e0302d003014080350307101203580045020880364001c04400e070861329251811410001641110743d82007103550100071042c004002480304c440c01c00c040c410500341800d84140360090030703802014036240c00c1150042e5410b440c0740304150180d84045000302e000c0000102c9200702c3e00640312505c0b901003003107910000301400700c0540d002030380c6454002d9032003820300c031881862070340060420071014003d10050920008180c890388007a00c1c0440c0041000f4410002ca03032000203041e440e00d40f4529600194006030190300580c100c00002440410a02d0402c60068000586074607052030300d03203481150b030324880d03008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 826894811 1250 826893561 826893563
    0xd17070212060f0414190c0e07090e0c0c150a050108060109110406141b01020417060c03040201111609021905070c03120306080f0303060126130c03051b1311160f 71
    0x15804a180450500c1c94095545100e04403550185200284492b845000641c080b10851180b80d20191a910544101c03074200031022400c074440c0e411485112052920110300640c58110000303481d5041401c10f5040200c142c024054907410546000120382000d401c4408503802d601c2d00c01c44c04400200e18640603c100c070740704110701e07481960003141d114041d0300030021500450320f0262440344455046895560480300342c0914102400010099402446d0780c80440910100703480d00d03d5690781e104030300c580060308060f60455012030001c2904400c80f0a001288075141400380c00c080b40340d40c0b098804901c44c0002001c6074040e581d030440c00381c0660000d00190100c2010358182040d03060042d6580c4d0021101c0a000800303007805504135140245a00d5000710404414030801d94469400d02d074444150ac2c41120307003450150001003c15401d00006965280c800c0005101e06582410041c50512080c6c0800c002850007150342c40c4195484100d40c0c107141d2302c6411820111443c100309940c00d02c4003074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 826896061 1250 826894811 826894843
    0x106051f081e090705030601140a142b030305060108040503031504020405030d030e0706050403050a0303050717010e06013f0e0114010e0a05060a0e060d17070212060f0414 75
    0x1083c8455400d012401300e095440940464025a0b6100540c40040c841d5082072038008810308418041816814420582148094050f00440344040d031080c01e850030762448040039484224812082640c10302441d50404402d1820303082a040c103403500f039128880a003c0381c2c60901c580b46e070001c464a0b6501564014007004080d42d070b8580c1d00b010041c001c2e004000b407080840c014164085201400b40c0141c030b003070340c1d0014010914031250b541c09032300801001e4910018002241c08103082e0b42030380301585001c0c00ca400b402800c03509000001601c90303081606040d0542071100e251014400218001348617495803101d058401074261450706004052080340c410095082921060081207007071500350403101e03034151100140c6c0c1c0e41e0900004840e01503400342c1e0300a140e254100a00903903c0186e0f5003011008018a032540f0305a44c42c522160b994003115281c090004c1070b0303001980341c120314004103003400780058042c0d450309105c0c92901d44001071006001d0311200f400b110704854100600802070b901c81c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 826897311 1250 826896061 826896121
    0x15030a0507090c17042a0302040603060c0f140d0c23040608010b19030c031d01050a1a030c0d050a0c0b0d1b08040201120209061b0106051f08 62
    0x2080400c06400c0c0012008003283c030301c0150413016814903d019100b41d41001802c000c114980c0031207240078000041004c8104003807100403000da82c80c1c4c07042000035482841c0019100301c1d030440103441c58074280c0482c01030180e51803250040c200380b82d003141ca00b02e41c403100004181080c03203025202114a098468040d400c4010441d204011140090090b2000c03034441114a80c0d803404041d881703115101d07241d44400b030315099115070703980660071484145515040214010354103d10140003a00d903c004840d09a4540050002081e0284aa0940418880030041090348642d0100e55604a0100118002d4640c100c442e07050200c00e20008444640c04038050082c15031381d10b0b9880340c03900074a00c081c805514281341c0840d501c1c0000010002303c0080d44426519075101e40040d5102d200c200050003403641c003008412081c0c1e560200801c007600321200489000140b00b8012801c45030150004ea006a0111920080385e8103002050300c50a80705180000700c9607919a644c4210038078500e0540103442c0f940e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 826898561 1250 826897311 826897319
    0xb0319020d0911030f0a1205160c06031109030a151104060908100207110108101703040314150103060b04090c0305060a111903150f031b140915030a0507 67
    0x19000503070340034080c40c81e140d64000c4101c10945c4803600c03580c1c4050721750f0007030460b0000107449410030002a142804c1460920000e4203860003e240d44203800c861031140500d050180715014880c00c40d141d03c5114041c0e0030000d03404003180d5510311181025211070aa100076003007030100c0f508041018406541c07060b484a40d0b800014051240398003805c14140501c80500030180d039a0310075510a2a08400c00c01c1440300300b03000550310a00003500b10b494402034040c000c00c1c071045000c0500414940540155580c07031460925003040445034058041681024481c0e0065548081403c0e055075001400007640002040000740200300000d070003403503180314800c00400c4c002c000c10317aa841181000c1c803d1009090203055840c06204060402e80154015254000824030075841409c520059080703801c2080c0d1204200300e203900240d8801c0321401010300329900006c0d40c03100c203c001483d82c80140d43c1c0320980d00b00001c4814800401290307003641d52598041c0c55a904018108007290020150f401054035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 826899811 1250 826898561 826898587
    0xc02010b21101d0c09040b010524030702070905060a08030307180312080702010b1f0c050a0512030403090e0106050d020904141618140d14030c0106050f0d020a0b031902 74
    0x10325650f540d8680110005200c007070404420301391040303030300030a40186070b0300300010456040714103005881344c0300c0d00c00d0741d00400b40da040000310b0088009400400c18030349840c0000d01522001803809000d000c0c4614100706100700041900d820054604200624801d0032404000e000803660020300102c40844041e03030520341010030980111000e80c000d100c4000c0140510004c805140500a06040440300c0010701c82d1040c50704260191042c1d0944650804a0329054903110f0341040e21300616400100344410180c00000404c001e02014810010319031400c84c002d00540030300b22440c041c0c01c3e00007a2040c40f84e0303110361140140e46500440b6400b5030404c44981c000c401e4070020440081031003210f003d00e01c181c07507a030640100c0b400f41d003c1000e207100f410103101014152500844440348609002c0340603038000c1c4041c05200c40410b0001403044e01e00002c100c0d1000541f4041402900c00101d0180940c0306c414014082e510000380c800e6407601e6441540c144044001c03200302890b840410354941c4604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 826901061 1250 826899811 826899851
    0xe07060504053001111c0e06062b050c0a050a080316060204230109050a0e06150405030f100606080106050a0c03140f0912012702010e15030a0c02010b2110 68
    0x541c2015020b03944c6c00048070070701100c1e81c00c100324500754440f000103003281c9050560302c040310341c00d0b40c140d8100c1d00c8015000300320910080800c07142600018940406410000400f40c02418101c03100c1884500e40718080352644160510595141c2000c5040800e018094049400604081550a00f046040041e1341d01988145103041e0001c1e103090300000b258541645c4080aa414400c00031070981c407010301300209070980381e0f180c122030310061000081c1607400b4006070900000c40030283c4109080021041e00316107268004800748092000140001d076480340503159074541c54100340a40340454202503400e640310f07502452951360001181a681441c103000388c60400000e41e5180310205440c0034103400d8580031301c0c15940c1c000c260b030310340340844804c0740e040c1c2c0c0c5990040c10070300c00c08110100400d1100ca0450070307a9034151030020500048480c1d40c4a2488100c44520080110110000002e403600f400c110b1400c1008045000700d1000308401e004040e04040081400c02a450004080d505401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 826902311 1250 826901061 826901077
    0x50c0a060e040b1e06070212030c07090b030109110906012307060f020301150c11090f06030c04060302221803030905070e04240e010507030e0706050405300111 70
    0x2410240d8240d414189800310f6030440e014611000b44d407005000031310005410040041ea441140070106108152007400105400d0b00e102000c0d288060030060040d003130f6075591040358004e0b8540030320a4045141000c841c08039840440d0b85840503100c00e801202c01344901610610744a03c03100d80c48400781c1d611401000000e118020a12407806c1204000080b03004c2440b408164299412600c0801449407018174402445401e201010303480d0b12004c80c1703854808541240512807010306104092600308484aa1030208407014880181107074046001d03a0310040c080440380b85004401e00d500d01e4176421078541e11415400184520041c0e0400801a0503c18001c1d602c5001d4601c0100e89043c2c0c0321411b03442590401203900c0780c0b4034220456410114540d0707450462650b04c41c4c803482b43d65001e00405002d1203ca035004100a06107400043c18081258445014130030f00300410481a01d0b030b107003c22811003d51b0100203d04500c0f010555012410703034000c41c619446c0585030360f00d1030b90400113000c0070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 826903561 1250 826902311 826902319
    0xc021f0501060e01081608090f0d4109030705150901090b04060c08090105040803070f0209060f010e0d0f050709020a0e040506030a0f030e0604030818010f080f04050c0a060e 76
    0x111510310041d01d0450041d01c3d009014802e28a010a005007d0381c1c8158205901c402150410040c1d0300403281807215007039032580010300081c014003003821003401100b60104a0341000f881c4001d80044481a0340d6060303150440f058000c5903426003543c0511200000b0a80500b000b512000140107503121a40700320061030100d41080b9010540300134400a460541d01a070301c5603900102c1c3c1e61102c1899070400402141044010400407036078007001c0c006865036a105c0e60350800d000d0f107648100564402c00404417802500958034202603680d05c40340250880364162100070308070500c0d0510050f4034448020280851103031820000c0c40807041d80c002c28440070f4a0b0b0300c078034001050908100c10381d58156a000d43c164040703d01078000c103d548600343d201302d02c2401c010302e030500004007080e007580190740107440d10040850951038000c80e16031801300b458401d103004000d800071154040c0140c1005401c141c5190341000011b01003110400803503044690040c00481c080b659560b0081003c501c4140352406 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 826904811 1250 826903561 826903577
    0x1c060302040f0203090712060213060f09060302030903043803090610031128120303110301031e0303020d02070b04120c03120e07211a04050c040c021f050106 69
    0x142d09424070130780e402042c079100540308082c40d011300114100b030200070541389640e0820848000758000903a41c0c0003403078240c807004000c405c5a00c01500f0202030358049001e0500420030013001c00404006c690940e0003078243c1c2d12840c081140a0a50082640400040d000c881600034a46031002d0028620545409003100c5081ea03d03034003132184c011135512000308102c01e005042c04c41403030407480c0c00020040309010180510700b00100074031b000d03440703900c000341c0c94002103500018140d050041001a03680d000c4c5031441c1d54915545c1949600d00d66010f49000c2070070803004000c06200e40c040b40c01c040e1440344295140c5505040111500000742c0d412503d200256100221150140c2c2d0b5203080650552203025000e09402c0003c1c000d0040303203100c00344034040e0b02c03004118440c2080fa1441e00550001d04c48200030200d03e01202c0380d5260350703222244642d24001b0400003407000903401040c40010740e00850950020501689888a1002340c4120f00350007400c100700d2450380d540264100c801943d0380c900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 826906061 1250 826904811 826904831
    0x7030206220b01150e0306040c05150f09060708070f061409150c030702071703030a0e03041406070807081206010909110304060e19031d0111030a03050c1c06030204 72
    0xd100d4068070004203142003100041116074040b81042d4034540c03850602400403205500080d05001c821503003194204520282803002d811314069010000300b010101a25056407090690518000d8480e150702c0340da40010400c04101ea807a065848044d03005e250151001124074140c00544407400345014035001100018003990800900540c0503004608084180d4494000180319940020002c0042d84585000041c8004200009000300c5242d24051516070901c0030400d4140e0380c0900080d1510fa0041c44207001c1000f0000e01c0000e00070044a03c81e03940c0c10300c2c2c5800d0788030740984800601080d0020946420100302612003d1044000340e8404220607140c0360014225131074014059840042480000c00003940e40c3e1282c075001c0c010104440c02486030803205451062814401c8000907691154101450814251846001000d08081d18907078503291105aa9000701240d010815858002040300c08040c00100c0b400000e000e100060280d141d60441c030058002440101d00941c606140c0003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 826907311 1250 826906061 826906111
    0x309010f0f0f03200f131703040e0928030908282102070e010806130602030703150609050a120b012714180f0c0613090207030206 57
    0x10712403040c0c07101501c070014100120010007a583c8036501c511115804a80b1001c0414041d28950700000c602555800599040c0c10b4482c0b1940e00000302e0a016003101982e20034040140c0d0b080e11604035800ca9a950b0b0000d84501d0b1590501c1e42c1000103928082c4089088400120189098000e442d0155080d90b1040c07056a1101607a030941006042613140301229003c140505181b90b0041e400c200403079807078607401000c2100d040c0150002d688110b0b800c00c54060384070342d22801445075002600161400d02c1c110b0300c9070013012100501a03a400000140003034003a070300901d2054100032035020015103648000d400c1d0710043c040c1a200311400200040d02d441c007a8070105040354081401c054603440d1030407010328061044082011042d107940d841d00c040c0400d00c9124a001c000001026040c200001000c0700c8060302111509181c02039070003c0c008080c0002d421105620644815550340345c254103401000402d90804501c80d4000a090810304d9400283d1a0045001661140090141d12520 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 826908561 1250 826907311 826907327
    0x3601080f0606060a051602040507110717030306010c0521130e040f240e0a0c05060309071509031a0a0e03040602061902090d0b010608090a020108041b0b03090309010f 73
    0x1241c1d02400400842d1388003445130000e4400c00415800607490030480b580001c066800841d140c1001454030003c201d000041008000c0061071070243d05443c038202e0400e095182e2000510f0641400209143c0305c08018007001061b01100e0b9041135940304044d0b448480c0d80a9000f0600c1c141c48041c02c03100464071550a80495008583c001084038101e000d5568450404409000100002d101564000784c184800e000d40a20356002030003034514083c051414043e00d20b02d98015038007408043c407c00100c00300014901d02940e0f0341da04a400f024071540001c0b03d407803d1540000740b5a82e0007602c03070545014182c2c1c086000c0d01c043c20061001070704400e8100e030b803801103114074401a8405808a2340384117800f0102c25114655210241c5083c540134081520307840e00080442d00050710304010007100b0b60201c0c0082e005015000a092078001c5600001c00c0d001d009130000c0c060305440c1420108844100fa10344004101c4e040da440d4491510f1a402a01c9400000c441d6011400000300072004500c0752240c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 826909811 1250 826908561 826908571
    0x50619060e1002010e070306021905071e02030309030d0309020307290d09020402121611030a08060f030105250201050403120e0c12010b041802090103023601080f06 72
    0xc500802014408101114000110b01e1055541e00c12180304c0b5008103004500195010740030150b66040855102c035034010710101000c007040300501a04002544641500400c551141c2c40301104414a0000034150300c600c00c00a941803060481d0f00c1c1c81d85425030000c001d010300072001c0d551030503500c011815040d03043c20b640c451403010500801080700c0307521011344101169003c000a1014040d07011800720f80c0400300a0041a0020080140c40703070f0044c5c0320b01e28109480c5050303110031800f5030314182c2d0b90141040c144244000c401c00604680c440ca8640e9028000040c000d03c00b504002d0b6848400001c94014550425034803158280000e0050055901655156541c00b400070001c02e00c01c4011b10070107051010a0140d459252140c0e40d071a0800720f2203e200d03000001d80d000600041100702c410700d2520071585a00b04100701e0140c0e4805060504481e0141c403400c00307141405c080d5003d500b900c0620225120107860129071481b01d00000396050343c0d400c901b1101c6103120702446503920030044030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 826911061 1250 826909811 826909817
    0x1404151e180b060901080a152607060203091509060f0c07090504051b0f0301050406060603230a02070305071403040e0f060a06050d1409012c0723100305061906 70
    0xb80da80035500c90200c0b00d5111f4000d440020f03241c404215000c00e254400d5201082400e4880c180f180403040c45441c4403e40e8120000514500f40b504001075120300986106038400c404c01c1c40d80b0a0720703070810f074100c41e801c6900501d03450382c4008404980b0380700e4100404205d0740d4818a00c3c0071440741460b1040c00d01641e001001040955032119403266411038800c910386d0001002880c030441b03a1024000c6074001e500c500c2c004200581880b40080c201c0e80000c13101d0803440c0c010090392111050050586402000000000d41c2e120300e142800c3e2150710400d0001403c41d80035903400060340d40c01101800a44140c20991603140d10ba180b680710a40d0420360b10b40354080d12600741044484d0045004040713900000201144020700101605000c8108452094440e5122007410501880800314280781001c40d240402080d502c0100d03c5a071940b40340074a0b45608030030754032602c14031895480300190714001450301c810103a595900402030300c0140c544501421017001d250f0307d002018207048040e20781d030359 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 826912311 1250 826911061 826911067
    0x20606220507050d0e1516050301030813080304030809090a0b180714070320010e1c020c04020301030f20011205060a030501090c18061404151e180b06 66
    0x1100400c010000604400d05003c410840311500e441c0d00d000b5010701c800071502400840860041401d00ca040c000d010a142c0d0b82405050140c65800c10162030540360004c20380c0b5140d000c44c00c0c6a139901e42c41c1d60001503103444081000010406400e0080583d05810786144c600e90322000017010640c1d9440c10525813221742101f44001c021089903c00354010218640102c0c43c9542001c1042d0503400b005c41600065802c0b020f5400513407010108498440c14003008225006820311642d031a251174060040c02c1d10f0920140500642c401c00400e11050002002150340303581d02c2ca484a807400001c04120391982d00e1129404e421000d1403030003684002c041c1c4501400c3c9034844011001080000c0a071980070380c0116022010800920a005040c3c0c400c15180341c4040c00c003121101c60a00312180c0d107402c241004e40a102c5c0e4118801400d08048064070086403d005a00f068200b01c00b1b642c0024410559031100d070004001e50312400002c44540b0800c1860640d107400101c02078881a03424190420340070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 826913561 1250 826912311 826912369
    0x40b090f3c0702070e010b090a12032003040e24010c0510110c06070c02130606091404020d0c020616030207050a0206030c070b0702030a0f033e0d0c020606 68
    0x340e074501e680000144180c540c140e440d00010001c0300d100fa0410f07c003082011400d03200354188425120041c00940b13034060b00b164040c0c0c0c0c0041040400481042909814001e040311800003001914007074484440106454542090f01020090071506083c0103945508022501c550080b0851010305030481c000d000c01c2d0402081c2c80001d0304642011448100d070800c121625201d050003468010303074659460300c1604050b80100801e4856410300d45040030702e820020800c02d600041c1c4d500c1211031150401c05074010341d0300002e00038041c000540e442141448134101b401035001c94001c0c8501101d07001a1005591006e00f24101d0041d0f032801401c40d0b001200200c05490568060341d44210300d007000c1480c20605940701c07604e820064076000d015a001103030664410b50031160714400000d1900e0100429204800b000541142030b880707206400c40b00184c40a500008011003500d4040f000c40070743d6039070b0150307210b48009100c0030b0325003030060185c00003284180c64110781e20804180c2e0000c40036008030b00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 826914811 1250 826913561 826913671
    0x207090213080f0c040b120c01030b06070803130b100f0909020a05060406030911090c031602011b02100606020606130b06040504060308070c0b0307021902040b090f 72
    0x90100d1a072030101c481000030301c92030200102c0da0308101c0b000250031405100c130140419103848084a41c8560848a0040d02c00c0000241e0254401824a4041110200794002c00d600d0f01c140d5001416034903000040214601b1150104c964a9101c2c00d00c50340d03d940d540c0d0400c20100c1c0365000f031b45008006910100151884d0b178002c104e0381e6000601c01c03a03820740e40c0c40006044d640300c2e0f8070203c0400e44a506100500801b0a5598050401955010124940580505030610009001c0c454800c5006144100a4401d5010381c0c4500c00c280d5030114013401006000e0744d43c01e0f40d613016a428a080040c04a5140d10200e2418001c0a000d00706040101c4055100000b821178580c64541124042c84005602e03038580c02010300540c05080b4855803007065040c0800c200b074640e0481c0010030410424880d0150740007900456400707500450708941e20f61480003c020700700d04005142c0c0204a041800b081c1d00d038140e019030146140c419181d071349125a079a5140940344c00810310460081e003502820784000c2c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 826916061 1250 826914811 826914817
    0x5010e0303040905091005010b090105220f060306080c040608063904080d08060604210602040e1008070f030f0302010b040c120f110316091203020d0e1002070902 71
    0x20107803802c0c10703114000a0200e642c00c913481845548030b40b03403110860004d0f1040704d016040350742d401850f0002ca0300000c0c0440c414201182c50030400218000303440c10201c211100a4203610b003e2421a640c0c641004003d0105c5004510990042181c4c0000b14a4944146002c0f9100c03000075240315903400310902d101c011012540c81400e2041c003165258580e08050540c0c817450001e2050352210304140107149040c1c00034503400c003488244005d10070a0b69801c0d007034504a40ca080003030101c82e10081300c00036035481e000d0801000503001081c04501c2400f0011034911458441408018041c1d0300c8000d15502c00c07042c8100e02c00203442d100c0a0010074031200c1c0100d07042d80280000f04140c480500800c04031810141f121000421040b001400a42a405142c002c0059003400b80710310100070074281250301c0b0281c090000801282d0000741d1890094125030700910507040740c8a200c0e60f15040194481c00003044100020799504074890b01440c10484035090707020300358000d103965400c0c00321500083d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 826917311 1250 826916061 826916087
    0xb180112020105160303060e131a130f062a0e010c0201050c061509150f3a0605010506030f060d03030e07120b010e07020a0809060706050406230705040501 68
    0x3010001084640100c00136500e40394420350700010003e18008842120501c0a880d455030a840d0782103100102da80c0c0c400d0b051208881d80000c008940310480414000301e4400d4006060070185101d02081c0004ca500c81d11b008450b0b9484001202c00d4030120907810125050030001080c01c03410358141e076521403015031006502c1810a50b180c84140c44055103026011640300b030028400121100541c101160f0840d00042c40c41c90315041c00c15900b00051103c2c4000b404d650150320b0051418070a0b101c600da8903040240414002102c110b075283d04030b5840c0204900c150303000da042034000660fa0070030404591043c01054020310594a6007010444142002d80c0160105503c441d0140c80d0b0303690502c90071b001401c8860000007200214600b04080c0c541c140c2c0004248841c010802010703507000324070b20760480d51120b4090341d125031050000d44035025000000d003c45140400300802c0009a070f00003e00c01c4100052003d038201c040d0400c03507207200100ca0180004e20300b48820070007540103010301028130f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 826918561 1250 826917311 826917317
    0xe040e0705090c18130905010c0f090b0f1231020f010302090a08010203013c03080a05040801330501050d0c031112010e1312200a060f0b1801120201 65
    0xb4480c2c00c130024a510102c64600400d5907034580c40c03502007000910512034288400e050105e169440c801019203a941d15118008107000001481c03d0010070010480b045800140136000207414904a804004a111003002c0a01c04500911103280403600b110515400d6008000c0310203195540c00440103500310103000341e00051a210301150070700d028000346010301403541002404221405c42209191042444031300f0902c04036203900f450703d910f114040c0aa03604210340e155203000d0400d081350315100b641d12844103540307007410600c00c0c2040350080407402d0070011b030b403014801d403070b03a400c061100181d2003030b5400700b83c04008002100c499038200c440404160708000a00c1c01c00d0541210b1a07500403801e0000780b4084200602c072485115030743c150020504a20500d031010503613210f60a240f0002d07929018800840819680c50500e00755100b02007642c44103a03a03226029281c4031020f01940c4806903d4070741880841c0300741e070826000118203030070040003e401036440d01d084101140c41c80c1c0010303410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 826919811 1250 826918561 826918597
    0x26072102090106022109030a0605100f15030c05121501050c032808090307030e0d08070302070806150109030f020a030b010305060702100506060910020c100e040e0705090c 75
    0x159072103034003190082030f05030050000401d282c0c1040d11100180b41005401c58818000c5202c00d440009070300071140d07405800010315031603c107000704488139243d21110f1221381c025004188140c04000c50f0070f580c41c1c80c0d142400400e102c8035040d110760040310000e034414007980e0b0010b5417030000455156900768060500381d00d004001c515050855128007580001074502d40c81c80c2c0103150703460390070500c2c0c503000e890005400e00384003c3c407548038454480040c041001850070a404e566542e441c4103a980d1f40203441607a280c0766898080d444a28a200e11005c5000d8100011480a406881c05c502c1050596441c1d6000382103944010039503c103540140d030400c00f02c000110000350000e6045010b14000d4005125501d0903060091400c0c0811242c10000c9040030140240e50711550305076000c0c41c1048501c0c1d0410300c80720350203e141803625a043d9a000405102c82144260413080961707190782c0c20340d01403108401c0e490b00e5a589240910605400040500000344080000009450b00401400504174 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 826921061 1250 826919811 826919813
    0x80604060b0d09020a171b19031505060f0109050423310c0e0403030b060a090509090703030f211506030f05040b010510020102090a0906260721 63
    0x41d400c40e5020720103007a60f65280c0001c0d0f16040300361900408060004d540c18003800d0740a5500d40340c500d81d8010b205010780d01311001c241d0b60491000c5000c130421003080d07001c944d20b041c0300700c4440c1c0c0ca9100950b60f42c64000800c180c5c0c10175007404840510181c590103006850407090000400000d96261100340401502c0c0c40980b0550a0103401150100c400c0e06c0c494880c03602c2032080c610344030141c003044410507a44138005100c19a0507000c4a10b100f04810741c0d59100e090070b038081c110350405a03a0084000802c0407040360030000c030005580040e0340f4968142d07a5002c03940c0d569066404081c1c0480e03c41826829040e2080d444e003840a010701c452049402083c0704502e05031423000080050402c0203520a101c100e9041c452240715141c000001c0c400ba041c20303100d00100134018000d41340225400c5801001080c001d4040302c019540140c100c5031402c1c0e8900c03030354004186a0250344002024807180c030380541c5807640c40d0504004a03402408010703107030003c0c80450a00445c290700c00e07a4180180c0d20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 826922311 1250 826921061 826921079
    0xe06071115181002040e0a0c030b0310022104110402030709030503040f03060f09020d060c0203090901080616020a08220e27010c0503011e0b0a0e03061302030a0308060406 75
    0x28000e00448480360b010a0075220503d0520a01e05844220148140400c03c50f40342021074054100041c030340000740111f10034800310050310348000e003e50544690203100c0110b084a500030400d640900383c507480f54040c1d4154807004404291030251040c0d07101c040d0f80c4010300d0140d0040d908140142003086000b0f80c0c0c2da403200d06503049644041c1c0089454001001408150300682c00c603002000400c00004225030700082c280007a41c0c1d80502465640c1030900d41c0c25000300200e6000b41c5000b080e03800a5170313441c5c60981e9519170442e0340d4050b031280b980800344058000076546a509900081c41400c000030701980341c00c090285c0304080d0501241c0c0400144882c1c0c9042c8290050a410800b200c014121035601e6000c0d6400101c0b60500740e2401c0c80482e40d80740d110051f0382c195490005210703103148010b081c00200c0d030a9030f080300101c0c44000440a42241c0c0086413010090701c00c0d400e441c995a070701e8020070003890340c031400650190030458100c1c001034400c6100c0c42d841100200005251500c5050f0a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 826923561 1250 826922311 826922353
    0x20d0b0d030309061d06041407080f031e03010b120402030c040e01051522050c040911040e06010c02150c0a05010c090810020427091205030604050a0e060711 69
    0x39408039555520f90401e008640c0641400d0200906020038503400b2500710a0340d9840c0200068004c0300c082c0704814007017000b031188a008086020031100b6580d02040c0c4a516944090380440800342444000f018145901c819070b0f0407500110355040c1040c0c1c1125100d48004c0000700100d90501840380386071056501c610416001b40980300000030310340b42096161018142c040c42d103611865403040c8030034047c00581c8a0507001d44c0b44400106003510343c03480e1804640074135040998583d0800c1400746044e504000900f00b10b03401b0783c030700340304c00c2e01c9550066401070a80c400c080e41088031a20b02c64540b010010050210401000498100e8001038a0761421502007507030350000103010a00c100000301c410440c40264030308c8200c08519003883c054405038010109404640c0345070030010184c515400da907011094080c0c210202d0740001100c0c02d40209254421a0110b21807840d01c0c02180380d00b02e26102c0c0840b4071414900901058940f10000d807008211540490284d108200f0107d034079950200302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 826924811 1250 826923561 826923563
    0xf15050a1b03090b070f03060f060c12110d05070201051b0705040b030c030c010c030215010e06040e0f0c1522030b060603090c1005280210020913020d0b0d 68
    0x80001d00d031600c000e64600030118021204101400d043c000400300303040382000b5411401c6410100f0400749101e00503070251503958401090400c91410008591307802012618101d440750400720b840d170104980680e00b100d030b140c6039030701e440c0e1000350010344541c020303401002610b0050404c0da0074002948114187c040000482c001c1365004141c3c00c00ca40d0034980185020b1900442c050b01500d5200c1001c41c0c1d40f466495441410440543d9902041c107009122103035181009a0b0f0800703640d80c6445100d00c0d41042590064095480c4c4810b1038118031000c10940070500d1010081c1184100410800c0034030f0b6a02c2040d590f0b0207000b0001c6240042804030203500d80c0c030182c1c0400d0055442d41c00d003034594540040ca40c0340192410020000640c4000c01d0031241d25400b01c466440c100840e010454003805030001e141640c410b80684c0701c040c035501c203089220344076256003150385401c14005244241e01030750803003e4106800041c0c0d451400b505402a080440a113003000801948480c002000342510b454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 826926061 1250 826924811 826924831
    0x191e050301050108150408031003140f150402060720120c0f06070507170a020d1b1a0a1110140103031202090f12010906050c0d05011406070f1505 64
    0x810850900380540c9004103a0b803000b03000e01401030400703250124402840203261490000c001258520055004405140c00200b120840c0c10007443c070f00d68940c0700c600600014401c04c506d003207120000c0340070944200c0d030150465007010f103255641e513081ca9a410506000722000300e003080d210740320002c0444c440c540c071070020301d920102c1d4014021036038240c409140c002d000401205d0301080000510208940625400304841094030304614180b070203000000b503100c0d080c0914001131080410076070f400b12a84c00d042d12800e503559000486103d4861401048006040c040e40b50704a0042d941e04c0350215482058440780d0301c00500300c80c102c55130f807902d0b014200000001401410340c010780119518000320011807500710050005101c5030358100ba01803007121070400134500d80f0000e4120803200f0b640401e0601c11420088607002c500c0e001034140720203591600707000041c03682c40c1d00082441c800010700203a150070b0341d44c2c44000c015030f03549034243d0b40400600c60444006240d48606480381c100c0309 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 826927311 1250 826926061 826926119
    0xf0507210f120209011b0606051309050c04090506060d140114011e0b0304080304020d02150309100204031703061207060c02100e03121c1829040219 65
    0x650050b100d4000c080c0b1003550148140300320342041e600211020a510440c0c2141c02c0340800f1407402d44040d088641003103400808080104004000940100d40060b00c2001600c0094443c9010b0108030307014158013400503408200030034010b0030489100c3e5601750180b1913040e00b1094081115080d5a05080c0781031500c02c0c0c0303000400a206655030300080010042071048407503403810300100e00700c1c0406840038100503c0007012a0840d55480b0f0000816070b0f0203007121207840d00b1003a039101aa04110340000c0c65002d6040780f8220403200388216400c3d6513000d903070f82c8213141d441c6554230541d0b00010300250708910380c00d2241103601e03820404107005002c10341d2510602040d0303105012074212080038840501c0041c3c185001c165501280c0c041e42041e600c008180c4aa0b02401c5030251100b86c04021030a07203103810020b00140c03c040c560a1a0076000d50726891500355203000746000c004a02c803030310300d4100446012a00501d0907149042c42d00510408100455489010b5080d20500c0741c40032410391003041c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 826928561 1250 826927311 826927337
    0xb090604030212070b01060e010c062414060708030a1404110310060e0f041b03030e0a05030f150c13060c031101020a0905010c0503120f09070b0301060f050721 70
    0x410a076280c4803015031185043c443c0030b6645564048041c06001f040c41000c0140e121182d00c2074040c1d080550304030f2000d01000000a0580f00c0300c0f14250048118480007004c0464815000a08036400b448042d000914000c0c45403501540ca1300040c0c000900c03a0b4a41c2030013121041640c0a2501a5010b000340103081c0041208040c5030801c1e4078480001e0f6401d29000700040402c1e648900c0d8451000900c041460369075143c0302c0c1e0352031011200d5101c559000c10000c801cbc145d21045102e0000c00c03d646684059031500d04140e510b5501c480d4a085903485015030b88441074144000c41d41044225010728103000304200302e081900713919080200002e0110800c10241540701c07080c5005010a80021464080042030040c026084c0b40212410320554490400c00c1150130011106000c015030400c505d1070800c41c81031102a24203503210015031099480100b041c900034412179040b10415258504003010030742c41500e45400402e41500c405841c80d140b20000521000c2c2025032007007651b5160300358414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 826929811 1250 826928561 826928563
    0x2205090f21040905071716090f080303063a060c080f131506080105040201020708073c0303050a0207060c0f02120f010e01020a03050a05071413030b0906040302 70
    0x80c140d80c81240400c00810150701074140c08a505481280c4004912695004026a05042e40e00c40c107540c4d1903141e01c02c002010b000c0407440c0000d00705640d83c1962850b5502c4101d03c00c140c06000340c40389904100302243c500d1401555a02c020614510448049801650340004a0205841f4000880328079102d09040040ca880b0361000030109040c401c07414208503c803c002c00e034000b01220a02d9007084410001d01024031040030b034400404405208250b01c0304980350181101392406c80c00b520442d00c0200d8a1030b4081a52029078000c40858180080d81c080c10149400341d0040042d5000314000b103c140c42c80c03031198010051070281d02c4a40d0b440e09030b0407000749048840d03400304080180380c803186d4000801c03902c41c0808080c1c04a0f1a0401c04103000c0c03207281080e40f10f0510826035880d1603803080c40b500042d009450182110f480801596035141b12800964404032403900002c2c1c01d1400f8041c0002c0c10308042d00b10321002c07003d0958a60f40780d9913100803280e4107856002e041e6008008100070594 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 826931061 1250 826929811 826929823
    0x1009090b0114060c100519060f03171e090a050607050c1201060f030f050c0a0e01230d0f0c0b0703080109050a0204030b1518071709010b06092205090f 66
    0x801610f0040c9008150000c09888007401801a02e4007070f15400440c043c134003000c0c8419600e50110300c1c01c01000d40c1c1c0b1000c41540b5009032208846407410940040c1c00403480d041514159510404020742031800394050302d4856001390641c9510215054010400380c84030b10203002140d21601c010b1405102460400881c00b10052030003206a0401c00180101040c2c1d101c3e007021030340d0000700800103030b00d0703031804500340380d5418602c1c4e400c088410000907465860294260407103569040d0040c468040403080d0301301e00c2c1d00e00c94072600482c080980c3d1002410300c07185014124000c4041d10072040d15020211441d034000d01e07060700000e0403803006024007101449400e8000a06c40700440c5094a10354a42550b100000c10200c0c0c1c490340c4c1d11285600c0d841e07625103092041118400181a86002280500010046034810080710502c60004440780c03814440c84802c10300c010703c0c445c10840e0102c10401500404000b1060031900245400d50040d2a40500c1e401910b026000d48103280c40024907502d0300d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 826932311 1250 826931061 826931099
    0x21305031c03090809040c020a061404122d020106030c0503010513030503090309060d1b1403010b1b10060617060a181b030f0b0105030c121009090b01 66
    0x5045050404004010162041e076498001c0c00d0114656640741400c4e00c0b00d000d420300950f04241081e04100001c1c1d4003080240c5402d100d604108072207100001000c00f40d54040314000d00b80c004039016185958081d0f501302c2c06c14400550303025155800800b9250701e074200d0406801c050703915030505108002007121308502505042e0001c10051904c4442d005401c00529400380c24042c00202041148400b802181e41108001c1e000c2695401c2920752980102451f4000034814000c021006114920030320f030b480959282c1005076070544e400c060400200d603000510071030403910034480040d002c00041c0042d01601d0014000050300500e810b2001d404640300030710b284045449801007080650300c10690310305966500500d9015008603041050040900d0500c2203c0250000781220b4402c3e859040110031520b07920301841103060000055580c0d0000740c41c6030603146814043d02c500c0660f000407241d444205504089411030341c5020500c00c0340e07410035007500d007218603030b0040c440343c0311241c82c00c4842 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 826933561 1250 826932311 826932313
    0x2e0b03012c0d02120405010f1101140f0a0515210111030108060c0a0801060c06110d0b040b100e04090f1202010603172a030f04080a23060f04020d140102130503 70
    0xb116044c0507400040c46103029080c1030141076003690300c495100c2e00c5083d0428601d10001c20031103155074555050500d04450444038a074403d030010f188800d050207502d0080400c40081207510040c0410030550301013102030503508880d01e58810642100900541e1600403900c075841b1360b030354108092203052102c001c2018103024020050402d0305c560126509044510620301140c10201c00e1501c14003418500c015008000d2000c03d20104011407a0f000007040401110100724001c400c00c01e00a40c554842c40711004243e6a0399480f5140c1055040840240d02c00c02004d400081d6507500c070021070240301d501030b0051303544d1141481003007080c0034016804501c80c0b80c440d05003101c1502c03205400700c0d00c0b84002d448017041604440c2c0310303104000341e9640c1208900e60588864032407800310b540e002c0700d60082d12203420405000c600009012449004e800d40503015000070b55521101141c1c4d04030150042b600401c9642c141c0003c10b0398000d140e8001c805000025a42d102843c0103010030381b950740c104c2846 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 826934811 1250 826933561 826933573
    0x150b0901030201090b031b0a08100e06031209031c050c071a0703050a020c030f0a0c0b0a140f0409050a0204170c10180902040f05032e0b03012c0d02 65
    0x76070313004003c150842e40030324140c0c0c2d501c5d07031817090a580e10044c07004c0ca07960340c4101050f0341c4041900025030b28401c0100503050b8225550340c40021307003051029180309030503820038654509891050380003014114005000c641403e110101c400c501803990050707500c0003c034081440602284248401001003002c9001c408075524206101141032180b001e00a040c040c0020351500014020301c0355150b1114000e043d51000c2302e01d10900b41d00c0c1e49480a0071038604010300d801041c2e069040301902e50b400c10350368500c0342009800c1402500c6600589030507129040602001846103418010148610b1001001680345e41c5420345900c1141d210f0b40340c0c08014ac02c5200c4542d81c81cac0b600e02d00c0043c2141036144c43d01500810500d8a0070100898008000607400000d01003070f404080060101214805d0701260354880740d08000081207800c900d18040716004072502c00107906c40c290402d00000900030000a40c20030007601180e503c40c03c90030780782082260483c0c1030701c00e06414050030029040754005000f03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 826936061 1250 826934811 826934813
    0xf1a0a020c190201020a020d1110050301080a1b03050106240807080a0b0109170a03110703050304052215030201030c03021224060d0b0f060f0307200a150b090103 71
    0x280b1407078a0450784903956501a42c9005585c0f00300600c5900c036401800c00c1489020604050200c02600141c9074080c000298005441600c43d01c101d9040300d80030000b80c80758101d140c1c0d070815020b8895800d01180c880310400880403640c2845010000c0844640d50503202e04180f034103402d00c5100d0400c03072041c003081c6000c1162258001400c0c50340801644000180d01d20312a0040e079032800356030403c101c018038440301d80d0800c000019980052900a4640021100700451002c0d51003c0314000200613030070904c02008207044c0004003142c425981c41503000a110040c00c0a4103c0d00c1c543c880b109910407403202001556014414422805100d2406601c0d2488ea625103400110340584001c24607909082c4910080a41446100404a0090103160b4818440c40c4038005860302c420034a00c601c2c042001c5c01c1c0c0d580f07054400c0310700803030081c8502821552040320a549040302010b940542a6070b4101a01402d007080c8410910544500d046190421b0600040003c403040004d401d030260b001c00c40140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 826937311 1250 826936061 826936063
    0x41508061504060c020f130c08090c1c33090c060503060a03020f030f03190f020a020d1203090203030c0102180f060708160204050112140d080c0a03090f1a0a020c 71
    0x4e003050340c040e1011002d8104490115007003150f116120b031030480c50040310305911984403804274000c6003201d048035103c003640310400c0300e400d83c0d2982e51605068210b010b80005843c1c0036070120441900e42540c2c0020000310b61107001c0400b208000c072400c90b0350320060001c00c800882c00310040c0440e480d02504600e0504081130001101d8080039100d40d13604503100d41c16540800030f0460001d4088103603a1200400314040036810f144014520201d42014103040303090b440041c115001e0341c0c0040c290014481140c0340c01100d503000002c14810580c403004040096102017008000e0030046800060b621818a582c0021502a804071a4072031106800e03822071607550941541c0c01c03513821200442d40c1e0200c076841c60484107164180250441d0801c1c000149c0d1014195042410502886c10040540d0410103445d40725a03541c1100310201d2590000301c2d04003000310024002e06100b500380028486610f0715044080b103d200f100b1102a941103a409002c4021186095048041d0003029820f15004840d20303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 826938561 1250 826937311 826937327
    0xb0316051f08180a1205040e09030a0f0e01021603050607020c0d0c0b0a180803070209010b1c1104080f062d041b1d0115020307020a14040204150806150406 68
    0x542d43c40c400154103660b24034800d02420715183e5000c02c44041001380c1020260490f00a0712540c2c0e50507000f1000289811808422514005940c0d550710195131030403032003a2210070003606c1c418110b1180c030701d10b010807091001e1400003850042d00104241d1411100003481c200b6482c11260054220000000000b0405212031094407040c1784000d48a502c010300c1103865490590200b002c0c000141b20000e0b4101c0044000c0c41a64020b5404891503070701c4180444543c03061a020807080f4141c042d010f03150540684c0700900f001d0b24044201e1074659a00103062030300c0303c414403d0074180c1005042c0708000301c1d440119100192a02c18000c420b88400e859014101c0c0010005400c00500c0504005c19aa52540103009020002e8408502c0d82104076031540e01c100901800301c8081b010486000024000000e0310007c1c0d5000f005902801d0821070540f070800d241032041d9800940030700c8045080c1071441070129541c0c06581e10342c6090b1814804100900d0b503518120203100c5d004201c00e00c9210360103400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 826939811 1250 826938561 826938571
    0xe0f1e06030a0e0303100603050f040f020d030912060213050901050a060e0406090219030b0105090a03020d050c0622050603100909020102100c090e0618190b0316051f08 74
    0x10301900da5840c001d150026122000340d903a941d010000030440801c4000181d50140ca4060743c0402040d0b40d00758214400c104140d40280840c0001c0e4a0399005140c1404038142c541e12915042440c1c643c0c070201d41d91041c0c401c1c0011a8090340110301110120041070303807440208411070764150254500f501282180740c040c00b55a080004500d400720315503c4079000328004250075170085607190030344c070f942c0a10303860f0050001e0002400d1a0791160340d0b600c40c0301a203844510040454001038550780c00c00030a0390580e002164180a4401c81001c26921880540710a4000320a891602125100801000d034900d40203a4450781c004d10602100900030740755a82078400c0c002c000a05104240010f07440e090200c005800c0312410300d00d209a050760310004120403070382c12040607451a22804204181081050a00454055484001141364810701081c2e41c030300e400103a0000b43d1343c208101081c00c02405e000c010080c40d2000004006604041001440d4a41c446440d640c141d8141c0c0d00040c4604400b41c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 826941061 1250 826939811 826939819
    0xa03080606180d0609060e010c091404150807050a09090b040201030e210415030603080703050313080d0225120e0a09051f0501050301210c090203070e0f1e 68
    0x5000c91412400e007000b019681d00050049140700003a160040c007400c4500011145c00341420013410b01c8100500642680c58060785440c0111030600c5400c0d43c0c50310301c40160b6a07001d80c580210341041884000c403840a400ac04000c0e010b043d05060520050101e00e5106550442c605100c80000c038506c4410650031560910700460a6a900540d980c507081c10700c04011840c580301c041c7c1c0e100c445888030041c000c132003000c1c0c00d08070009880d02051301200d281c0d1001424800c81045000300082c800c200071644106552020b81d010340c003548947c0d070240c02c41c100d05030309aa4009481801b00112511100c0c12407111000f510701d801050f6514001507405000071010700841400c40c0b6281d035643d402c800d01070a011141002540f4185910042c0280c0004a0154030300b00c0d2000070405500c2074040340d05840101001501c4114032801c0343e940c100a640050340d01d103038547c0000c1214030031400254040e46480e504e2500482d035107400c011811081c1140607100f080c0c040400c108607465403444580b414801c0b5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 826942311 1250 826941061 826941067
    0xb0414010507051f0b10020304140103020c03070803070219050d0c030e0325061e08130c03080912010b0a05010305100909030f110d05030a180203010c200a03080606 72
    0x4401a10603001d41d690040181c000d604e20b0240d00c0b6582c0d00e08904800304c0b03040621a407040b843c06e011680100081d0303280142c00402041c003c84c0c02028601c5d000c0c030818900146000710700100c40c2c7c15500035000484111300c1c000288401954100811400a402040ca2003c4003400e035442c42e60741c5a9881c407040600609820403400d060040b400315005440140584140a4403008400f0300c2801e000440400c50356a241d002c600c103813142000916426507828900b84005a0301c00030b45082c070004100c0101c0c41601d0980c00000b9686104080003144034072070564039848241c0c10000b0030b8000b8814030840340c2c5840f45044290740d42901000441d003003030030300103169150040c0d6062068010380043e1843c80c10100e000e410181d011a0000c1103103e56524424942581800951500f000c0100d500008100780042941c5030020750018014148100c9581d81181403640800e0968012003117200210300d04d1441d564401ca5490100c00003910444080c0c01d22500b1643e021f05050310140c0842d029078008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 826943561 1250 826942311 826942349
    0x3071b030309020418140a03091e0b0a0e0429041e0e030a081320040e0f03130b070218130807150e0c0307090e030f1801020c09010b04 59
    0x342c0c480302d0401d40203801800448400055030240d498000d0003180c0d03002c0d261000e10202580810711102c45035141d6100e01100f40b03004402e4041420120b4600c480e0881c54100003640c0395000b000309000700c8641c481d4080441d0040400c4101c0f2140d226183d4440c540c94646d90004804004500607050102c8000816404030a40c00d200d03070390211914445545041c22281c1741200001c040c200d0600759980d0740103990350300789004560507480c01000781a2800b142d82800444a20000c296269402610005403621b4070b8042e580341195085094005030000602c0154010702d00011002508410040301e140c18007035804103075440c4031001a8060003803d0b07808184c0c2d080040036203000480d00011269110310f15814002c88240340c10140b1080b45182c9040c41c01212008202400b04541c01000b400c142803915610038013410000914002a000400156403024901030150080035501070580c0071280306400003901d400131842c0014401d001c1c0d00010801400305008450580d60b0040464504040c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 826944811 1250 826943561 826943567
    0x1b0503130b0702030c070902040e07170712090803162601090f0204030507060201020301060e04090809010c02060d0905070e010e0c160204020904060306020c0d0905060720181b03071b03 81
    0x81c605c96012503005000c00000d0345242a00644283e42003401041d1064403515401e540d403180d044c4c1c2800a800300000080c861500407640c081440f0090300010071450b603540e5450b00c0541c4200c03074950716a801d080e40005200d91110ba082d25041c20081d00c110505030390194200c05810501c6200307a001e0b2122050040e070b4080d90191002964094100e803072040c1c42d500003034041d40090161000080304c0490300c006a01c0d10340260b040854100b030510340761a452200444104034440816030300140c00b00150b602c4041103104140c051400b800250441d54140b4429900e41c40040e80040e04000c2880c040c0110760030751808803680d04081180c04c07050a45544081000303401400501940540740500003c140f0065800400402c6502c005654110482d10f400395400030321750142c143c110301c05004640c0002c1c408000e1112482c0c0e42c10703500060305c96000c005440c20942d175000503900c0ca40e00041c049400c14006202d011440451000c9055280254000b083c8000b84060707403408644005200080c140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 826946061 1250 826944811 826944817
    0x10c20030403240c020d020609010209010503070806010c20010212090102190309090612030e150405151308281e031205011401140405061206130f1b0503130b070203 72
    0x100f0b2102484a0590340030041c0d1203443c01102e40000d40185d5001404488042c8215240303480161286410740e02c3e0003000310782003003000b44036230305014443c9c40481c00705801da81181c4c0d8003158281100c4100e210100020709065403801c4e00d4030541c0d014800001280e8004c6806111070798007a80392402e01c1c005080c103d400c03207403d500070a0034518040000c41e40305c90205180000c0d9000e07441c0c0440c04003144041c001020424650030021082c140014030551901e01d01402c101190700c0300706800c143d0801c0d0482d501d0141d036444900d0b41d070b1040840c2009140b5a0b040700e0501440c0b338004456603030540c0c4444954800300e0094100200c000c00c2e9420400d0b000d6010f000e44582070310740800c8590b031a45142480d0020100c51980030a8803d09140000008001200d06450001e040305040012131035440158040c06403000c0e5103c0c014200c400d143c1001d43c8540780c901e103041c40380070540d442c091488807196482d500040007006810010000079000f1021843c2c046980142c0b020717203a66aa9100300d0030341c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 826947311 1250 826946061 826946123
    0xc0106240c171204030e06030907090c03140a020406090b0a020c040221040b04061a01050f0c01110f04090605010905490c0501020604051b0a03080c010c20030403 71
    0x50040303044007001101480300340c41603100351141b2040540c030340e040003ea0701003141c0e094038070340c0070000520094840782c224980c0f010075806c002c03032000c41d810042000c0f0380084031950301d81034340071404101d5198000310713000c01000030703030b05e031a1401002040007501e95902d807080c03038003c81e00021002142a03d113202003205601c1100401903a06081c0f0380081100b0059400341c61403400d1200c4d04640300541c1900f1811804e050315050301d0000241c1c00390035240c004c144c0c5903840b075594171003080805182d04000c00c100e4101078401543c0f18104002441104d43c0340d0401030407c00c1502051105440700540d140c01c14107405059551080d5a8041600740482401002c0070144052842e00c1201c0481040c050154400c40750003004640703074801265604d1040f10050138a6000c000c1c07855141c54200c00001080342c1c0a05001c04841d125100c1030501d034000075404c0102c0c3c0d03480d88a01d40e40e03a4401030b2102d0101051070030f01502c2c81c3c06007031582e0f2409030380000345c0800c00c60b440402813000c040903288022 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 826948561 1250 826947311 826947353
    0x80f10050d11010e0108100e04021f021c2303041104060801020a03051f0512030c030412020906010903030e0f030f0a05071a0a1709030702150c0106240c 67
    0x1480c601107011496a0030124042013130783c0f8000007203600a904281c45280a00103141d071191a1030319000d4140d41c0500282d03003000c441c07102030b4810880b130041c02da84e0b011960020402d03500208441c260f80014180144101704161900c42e074056804040308008070726102c0440d8494031642410b04070748488903c0310b41d01070710b004d6002600d04419000782080d45140c1d00c1c1044903170f4990409200800d00c2c40700d00315141f050030800703200b1740c540b5841031040c050809084034240101860281e186a0ac15048104510b030381b46c218808602d03242c28040d90090007868148617161135aa00902219000c11030244110300e0241c000d012a10200074581941d0788100440b0581003660800c181c881d0b10074054015581d068032186081280110700f00d51003454030f941d8017294404030005580c6007840c0130f000c2c5c0810740010858940960b0750350b03441c686114040300340a0365071b1207415501400c441d0340744e1003800100c145d540130f603000540f01920014840f280c1c2c00c110310b00440340e181026407002084183c0041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 826949811 1250 826948561 826948579
    0x140a080c1b070603060b0405090106030c0207030f11091501080712021215030f1507050706060510031a01020106030c0b21011401032306120309031203100510080f1005 73
    0x14052001540c2401c81c2d41c65101000021b0701c3e24448405071050f4040d10307030404220401084218844da0089090424034816a40310946070b1740c90000810076138106450001c0c5503a089074041c40c2038101f00b5003100c8100c4146194079058400601012402400c0409100c101d003041201c00da11601103982e41d0703c1d420003000c207910b0000c07a0a10310203071044115000344074421140d10b40342400105281d402c1d103e030034030521a50f6240b808940d40d84c02040200e403074030b07101d00d40047c50f034440620380d00c14280951804204010000034a501501e21160800e046a040c10800c002056120000303009a4000e00300080d03803040c1007a40407007400d03011091f0264203044c00c0000654911151110328421200340c0e020300940d1640d402584c003841160b80b000054801210105802d450020710420b41c2441d00c009072130800c08020b0009052682d05a000388000c00000704010354101120088009800212110044694041002007410900410507580c1d4501600480c420380010700014000704402814030a03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 826951061 1250 826949811 826949857
    0x81510180204090612030503010b09042d0b011b020d0615030320070f090905010609110d050c0a2a06110909130203210d05010801051006140a080c 64
    0x4000e42c01440303038030581403a008021a1404007400004002e0303815039111400c59082c00c14980469000182050380140d65241098101524510590f0912190005803c00008003140d26003a119510f804504020700310b6400e03085d0000c80d402c0455065015500920319001070304e0f0040c001c16038021002e819114202c0d0010400d5402000301c0d1240700ca90008401c56581c80308aa80d54405034000e4104444144000348554031090744410303c13803409500003148041d940d441e50000c5808044c1c03032103400074002034018040c40d2a40201500034481d460301d0361401c030344000d0007445400c8034151004c40a00383c00c0503400c00c0c00098446040740360041c0007000b0f000d4030481558031540c80343c01c5441c06161904000361020401001d004000e64001d4090102640810381d40c40d404060107602d49031a6006202401c00030000784a4540604150000022030342484a00030344480911351000c0708001c88146031030241113070031003541d404401a040900c43c54441410511060188032034804540ca4103101c1d402d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 826952311 1250 826951061 826951109
    0x321050705011d070e06010c020f130606030203060a050604032a080f0105010306050a09021008060423010620030403020906060705031306090f05031f090b0702100b0109081510 77
    0x8040200e89100301ca40503582c40ea1205c04880342180d2640c080b0782511048005800e040b1821a01c203900204107440c3c181e500070030a41201c1060f0032540020354080300304035817030030418074050107024102d800d1400d10380307559034104500e1504ca4035007401e280342210341d40d04503101001c134402800400050710324400409a11a00a14091000359400c038107004c0840c054a9451049940c520f8016150484000a09401383c91080e0b01400036504240c1d11a8100c4c0d030101000303880071500110716041c1c0071552400e0700040c07040801310130003c05a91458005c0a04030300c0041150100c1e58141c9000141e90350791000200d803400303018070180c00340c0400600c1c100c1c441d041c084580107640d40e584034007801c079072104041a14407495006d0240c040d07014030200c45040388808a014031518181c100407461043c1da588140a200060b114a00075a001204200d0041107602035442106820f2a0400b4034a1501080903a100c84542d03070514013102c0d41011402d4910102c006030082c1409004103916684014440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 826953561 1250 826952311 826952351
    0x370510321005010c081911100b310902060f0708070201020d02060601020a03030b0307050d031706010503040b04030c1403270a08031209010612080d050907032105070501 74
    0x1009100741034040070405600032441e00d11815048003059041965055111307a48502e401044d5090000f0b00041051010f0f0403c080004075100c1d500104844020744140200303400956a00b80f90384105a49211098655032441510803840301c001040307055150011800c0b0344182848000410000511481840742403401031000600c01c0e0308035180c2e400c1c1c1880882c0c842c2c10a80303140d40141c001075241d10100b44290852890404d00a0a0b140c2d9656144002203884e034550030110041582d1300e5080300c20a01080d06554840700038200329140d0725007662043c0782c2001c014030050134000d101c1442410700c5102c10080703200c14912412280e0320102840720703c402c81e660040120f403c01040307280012034104040340108403402c1c407000318207000301d4406000200f280140451a90340d030f6414001450031121400400d0342d8000c1042c030b50386151010007074095950050a0700c0c2e16602a0600f000003135425441c681c40312130702210760740c2d07100c0040e00704560f20b01c01c0d440060810340c20050354044544003403a0f5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 826954811 1250 826953561 826953571
    0x606070f08040b03220201200f0a030810090c0c0b130f060509100b0d0623040b070e0f151804050c030108061608040f0602070537051032 60
    0x3420f540c1c3c5c4840c810703115494412800090019162500c00900d86107642a070540a900380c00a9468804140100514245041c0000d400062115040c4030005032110303100c038040d0460013800e10030a50020300141010400e41c6004244010147c0000c05091302c80000340030840d40300404561f24400c07420300b0800341c007064800e84224041c04507150400c541a03c101d03e01001301404030b039120081512401e00420b0310071400a1644201c0e2180b034580b03007407981d20a101e68800e4614044c981000c0c0700041c104002c1d1001140603641d181980d403040d503220100d2010703200c140f912b0181c1c1c03810785040c00c17070350740c0c00580b50547c200342071806024522141c400510f0590300018203c51b6141e803240103854407108800c0081021072601004100480d000e480d0210400740100c2d0054a48406d0f9a6000d1030102c0200115100301c0d501c80c201011454801060511420403400c0300d40d40110641b01c4076140c88002036101d1104e41e460801c0d86641c408508580440c42810349041040184a0303c190001c0004450f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 826956061 1250 826954811 826954831
    0x4020703020c0406080d09031103030f0c21040b0d050c04050307080f010b0d12080402010e09130b0606031b070c03020d050303010f0f0e180703060e150a140606070f08040b03 76
    0x1340424241c1300083e00e10100344441d910600c0003840c0d40c03101282d490800d840f00360940020002603080e10010002051034058507401010b910311301031441d111601d907101140000c07038000c000c10011000c42e501910300d00c4007a2500001d4644442403c1c0c3e6641c4a207038880758041c01282400102128082125070166811000a01c1200740e020100106180342172030003040c00c0ca40c00342c40d107011481031110681c0540706040c101e005425000010f100d0342011102c0003410400360301030004104054000c00e8020b00c0a542c0b090940c00c0c29070066509501d41c510000c8a12400310700c2c41c0600c0203441c04200115000742095103848807a0902d2a01d90f40240146403400105440000f5903080210181040310f5034504944090340782c02c240803413040e19060000030944a8140040046012885031060581800d40281040f4034005c3d4114552580100420001443d110803095511010440980d00901c101c1c0d074290380c0c00c181c0c5440032190a80840c01707092030101080101394810300c00015402039010344 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 826957311 1250 826956061 826956071
    0x70207051309030813030906180509010f181401210213021905070f0b060d050d02030a0f090503252301090806090a0b0a06180c080124051804020703020c04 68
    0x1c80c85c039407000c950704e10040025208100400a1500ca183c2c010b0210f408803032521600c99942d00050440f580c02c1c1c000c4201c00e01450000c020407082c56a4884001802050602c4400745c1e00000901c10041489100181503000c00c02c040800c107580900002c6540c002c02e00d12480304a074401740f00030340001208200c607055403100160340c580104152050f082c0d10180520f80e01e003581d5586291403a0160241d070b01b1000c408001c0b07000440611005120340100e41c011038680200c000d009000761047c002940c140f020441e000d104da51008102038409200082800345002e48440381146003610300c0d0f00510304016031400340034000c03208241040d08a40b090f42c0d00d0341d4079500d42e100c690311001c054904d0780341c07580413507508000244104a056880f80c3c00d071000003030b01541c81455040b02da03810071009881964948082c060b00b0f40000009015107060010540c0006070261000080e41c2141d9030a4140440070070302c191144a0304120350400d44000d40159203030343d002e10b00655140d1295007c039128070300305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 826958561 1250 826957311 826957321
    0x608010207050c090f011a0a0c0812060f01110703060c1b05060613022a1006180608031c050402040216030e030d03020901020d05160204060f2111090702070513090308 73
    0x117603140c00e060703c007071814080881c20015840c68090340f01c0e9408400f07004007001ca44004c640d0050203040c0500e8140040b0b1101c0c60090100045544107101076410700000b800038250101001501c1802c0d07c0d84040001106d5200c031100741c5207a62901341d001c1c60790704440c02000401801081040c090030055861007140880300c2c1220080e400307520351036040c5000b02d1104040a40c40c4154000d1520001380640f0040d10301c0e412540d0079103a5a4020724080004079036440c4810100744940c200401404000e1820500c003c41214200703100503a003011380f40e88403404181555141e43c100d80562540c0c2d419120f40c8003651401030504000a2200c6200c0c2c01480c2a070760303016019000321030481c60168040c00c0144c050600c1602d194008641c080e482d503000d401f080005840b82c0c03083c02c0c00341040c0c1540000041c0f810421038011803000004049080821074058001030355030450a0380c4090071504030742e0b2075503540d80c100c0c500f840e81d50203036500c024507640346002d00080d40c4c0a501006e001303688540440c2d4038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 826959811 1250 826958561 826958581
    0x3250804030f12050703300f0606140a0e012d09083f0c100b130c090608040f0501051915080613080d24060c0b0f07030608010207050c09 60
    0x45179000f0380440c50a080e600100700542c00e503980c011903140c0c842007100c41035400319030440c0c0c04a40c01c802d510f60390781d0062009940283d60031485280d0b1070300107441c003801b500004100c90119011a41032001004401600110050a540d031809400c58079992800040400400510791441000c105004000c5004d0907000f00715002c0c49940302da181d804400c11881c41c1100914442c0b9070380505042014044423403002428040440d0001403004040b0340340d40c21008000313814680c440030b540d41e14a040c0c01d6001c41c0b90000100005c0fa00e40f418001a142e40b503007030055800c014280002d0155191100b00801a04030100141c0e1200110308104448245000721f00d1520410303014600007580280c00260b80070341d00345003022015100d4118a8100108404814152a446502501c00070b0054010941c0c1030b0b106a0f9440c01000c041c03130805810380003515002002c541c05090700c0d02224181c0c0005000502a400c044c0041c040311000310b507a41c00d94201503842d20304078400035104103084000b282d48885 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 826961061 1250 826959811 826959817
    0xa060807201b0612070e0d020904060b09130507051e060d06140301021204141903020d020127020f03010608033c0d020d0b09010608040b090f03250804030f1205 70
    0x480107283c0801303503e6003042510032200300485170354003222491503040103855540c010f030b004503c80c010100d2540d1000d402c00c140104002d00465112002c0b0101c02c002c038100140d1441190004c0d100317001e880d25950300da0328201c2d00146a250f00f010b0006041c80121100d030f400802290001c8002c0002a810f00702094240d10403e420001201c0d8074901080c08545680140d007000c11041341201d580085070981e9800f800c06410064002da000440222010342c1c0a005141002050008640d43c0041e9003005504070f03400d2500217402440860225002d58500b5403103400900112000c07207403650b07030b4a00100031010a41c00c80a000c9820b02c8907050128078450f01210000b41d41005050912080c6000036000f9007001c203040000b0b60300c0380016a170a80760030039018040c0509903108642440c2c98141406010406407816405600142440070b000f200801991601030482140c0300720401124107503a080c003241c0070301800700d400004001040011100071610101d00c20141c1c040403900191701510940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 826962311 1250 826961061 826961077
    0x1090204050315180a050d020c0a05090c07020103140c09030c0d05030306010c06060905180105100303080606070c0b0d020705060a0b2b150209010e0d020a060807201b06 74
    0x107404015912070703e150810416501007210010010b0031143d84e45218613015600c0c40075649500103003160f45445034180280c00000000369002d0f889140390002280d21244010500c840c0410003140010440e0302c00d810030070905008080c4202d40d801c003e800d4903815403040c50400d200384074807100030801703092000f4907460300e40d0044051030440d51002c0c015075802c4107642088800079a58030020406560134400d1038043d884610b640844040444606400c40d4070140c0310785d01414000f0020400281d220848075030000c0b06460b51500c0702ca1a01d0701003c00c150702c2c0c004009010f0041101000d003021035000e0404540528200d0340316440346c40418040b524014441a0450500019098402c0d18400d24021401c0c403507a02006800713080d2030b00c100b507505250314556495000208075143d983d0010341482164021102c46c0e100c100f2903030024480800c24810305091080e03110004011901078100c51003090b02100f207510004c0c80d41001c5648440005000c10508104450f000710103060045c1611410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 826963561 1250 826962311 826962313
    0x306040b0a05041707060203010303140315060d0e0f1014070801051011160305120f03060f011e050c070f180b03031c020c01050601020a031205040f020d110108010902040503 76
    0x254541e100c208010b00380040007076440902152261400655200007480c5203809590011384950551134010800c0204c00c8000c0c01c8400d0602c144128090410054000050115003a60f6036142c8a402c200140c0304c20482a502c07170081c0840003002c0c01e0b01144001148841080c00c00c2841108810724080ca00291104800104a0801400a4109003030391000c0c102041c100301c4402c21072043e4042c6400300e08600300e800c04142e10402c10800504202c40c020b0450702000c2d0310305210180012003040c0c00010441e91044d1504091001140d02400607000d0141c6030b0310010220f01c007100e0300508558008170070050140f20700380ac000f4510304282d03d02c50990f0300c9820650031070a41d03204004050a0090300ba240d0501080207600c4405112200909441c100c0790b4001d6160b07217082054600b1207200a0005042d900107600c03007800681d105484100340040350400288589580c1040d41c07a19032201c1c4001e400c50b031100d0310281400882441c42c424004240c0c0d44442030780c5c0b100002c03826800345100f0b003501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 826964811 1250 826963561 826963583
    0xd0510200d0f11030405061b0f04060203071506061b060603052a010e0a15030b10020106030c0801090201171329100803040b0d150603020403020a0f0f0e150a030506090c030604 77
    0x1100c0c007030b254801c10b401d9400c642a081275810120203d0680c0554000b00144e80002640c01c10044009041d01090380d80d402c041050034075000005c1c01060103000b21410250f44482a1f9007008480d612071405113420100300d5943d0b95004050103a580012080c11101d040e4004110516601c0345241940d0340c8005000700e1009031800d070840f400a0414039042c02410f484548000c1544c135410300605000141d50b0000c643d540c5941440c0035030300100d8000e1003050341030020b1500581d1f0403003000300704400d03c4401c103c140d544810700c24031010a803480060500e4140c0c0c0400c001c40c101d100c400581100703010800c0050b5201c5040700800038002e80702340d6889800034081002804820009441c03900782c4202c02103002403070416115800d0704c154002c4c00c0442c4d4041010700940c1080034544002d807211700e82807008281031148020a140d818895418202913140005108094900d44810121006031501e0300c803903264035156403030320f5044a80c0100b42c8200030b6032111929001a415004641004464031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 826966061 1250 826964811 826964821
    0x111c050103020d080705031603050912030c070614070f1118090d180e01030c030c05100e060906070b04050c011b0201171302030304230d0510200d0f1103040506 70
    0x1175004040b05480c540000d001c044c1d95000c6070b11344040e04902c07035951241d9030040b400800404086410850080381e00c148815150a02c00107840c00a407291410511404040008038200030f10aa0750010610030f05035a4400800072228443d9060510859031211861144041d01e05031540c01c8504460590284000b80074a0340182440c0452096503026081c41a03240d503c1603818030001c2c0d20885000403800c40c01c009200c4e01d4404480600001c0b030301d00e80a110310101c01851011480301c0e8a12038080001c06030820750301d00003144c40050348040410501e20b494180320391103101506910780401c015050701c1030340300c00310725401d071005605840b21002ca64020241100d0418000d26214030b0341c001e44039410260b501000500000c100305400c418000c0005c01201d4542c0881014240c0191a250403040c0010b0001c0f8540c1030390f1903600d0700081d110b65590342c00f4880000800f8011413030440011031078940003054100c0488051019001e02c201010700d40d420090384412500a4080e401100200c1c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 826967311 1250 826966061 826966073
    0xf1f140c270a03050f010621060203090c1e040506010906090915210303061d0f07020a0c1502070e0f040803090c0a0e06100201090302100b0105040801111c050103020d 73
    0x4402081948404000071039010301286101d11a0b400c2900d0580c0000c1c2e101a41321001d0144001400610394100da8081c0c403400618415940b0100c01081c0fa600400010781d010801c00c00c0303003045040100044510101c00da8140788010b40513070514022428200028610750150f082401111056a900c80501d8500300c0b060700209881e0aa543e0716440b44040041c11209100c001c003080c500101210040f1111443c003d03003216819405036000c0454a441410701c3c0038549105a4411582081c510040e40c0e5203d0403800d29002850040080900714800700d1030001581c900e010f451129000c0342d81c000d40b1a41e02e241c0d42d150072500d1001d081d40d240001400281303518040e50b003282d00c0030115140a807070500011000d280c5a08200254150841089001e00c0e00300e00d60422501c150000b01320341922501c0007912803241a08090f60141c813002e00007540d92150040758000c11803213008021020125151004da03901020ac1da0740401b100360481107158400d03214042c100d0f90b0050400c003041185030b6800c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 826968561 1250 826967311 826967347
    0x2e0f1a040c03061d2706070309060e06010e070f0912060e121603031b0914060d020d0f06051c120c080309011d0c090c0c0f1f140c 57
    0x2000802d5151640096200e41e000d20800c8042c07420b00f83d00c403403441d15407500d14545202543c18201141ca94040b0701810101080c040d0b00b0110340d14004c110000079041000c041c00c0b07032420400c4644100300c0009840b1002074052030286000759034903400121304071421649440c0c0341c007071601c1542c01d6516110008a107a40701c504214040030645a001c41140704680c0d003500201ca0510480c1c0d200c040720400c040c0d05115042c0600e490f241c00d8122101400700003049405180126404107580c1c4401c441c01e503a035003003510000e118011003513607114180f460542c040d000d5407120800b00c0d030400e503020900c0d140040781c4c081c0d00107280d4031014054036113403501d000540100c410001809944207503440410001001113101c0c00e44080081100140c010258560f19840c0b01c503449e41e40c11850340c01482c1d564442407141c00441940c003441e210312030500f02908142c44018160894861120580703052a00310a00d030551800040003004a0000c0c040e160828600484820307000010420000c2c5001e80b5001c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 826969811 1250 826968561 826968581
    0x30a03200a0c0e280b011b0b040b09010f02070804090e0a03140d150b130e011206020f0c031303050c0a1809050114090c04060b09010203090d052e0f1a04 67
    0x91344c40d100c0307480c5510303c04003110b860076a00915226003e6003510350304000080b400070410756500c0100c2090391a01c2c480044050300040c000740d002c0d00401c3d001d40094000c044000d03402d071800c5549000c81c1c80c1c411015409886051140c505021109149030710104500f18131640648800f844180c0061044035680c1c00010f2150f0321b1a500c16050382c080340b0124812003c0c00c1d01000403651002425081b004840076540502038004102d40140104441903c4020180c4ea11001c0940c4829591200b2015405211544103481c0b00200d106403c2c1c101400003801224058020355040b540680d0500c4140c1210f40250b41442100c030803210440c81f8240d22840441e03014000009201c1c44d11100304200080a4400c07800b07170ba2080c1c4102c100c505d0180306000050441c0f8056a14010381c03200040e4480c01401180c80c4589403d05425042c480d05201000142c0d5100c85c541510021180440c0c0403070003001e000b101142c1c900b09074640e10039420300c80e210440e140c000ca800d905458480c1044090800041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 826971061 1250 826969811 826969831
    0x181e2d021011030d061e0501120b060f0705070315141b070f08030702070906080703021005040f030b180d1e14030108100e0a0b060d0c05030a03200a0c0e 67
    0x14840105000f40080c0454864281e404a4205e160001042a40c4807080002d2607080c440c40e810001170307070030011130781c0032803040d540125503d014040001c5e4240182030704949040700000d015001c004002c0cc4040c181c9104000090031502c401c02c480d0202d6a20301080c55a225034540800c48070815040c0240b090110600c11514101880d0b841552140701c0c1d080445200b400031041c05856038040c0304480117000030000030170415203408070003030341c43c0011322010740140c850840c48030380c039486001110080c182107400f54400c150b0b2442c10300300d41602201c040b0a01c1079030100c00c1d2180c20000c40e44420000b51951050b41c01140f401c0c502c100315641401540a2060010303000e5080c0400b0000385000b811520090020700652680c0c403010b845240d500d050542d0044101c030b0000656000c051074200c0c005540402c0d401140d4613024001d4801074008aa26200e09102d40082652000280300080140040b42c0c1154021540341507070303003c00031001401c1d1810184240320f100ca120103129840b4111071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 826972311 1250 826971061 826971077
    0xa110d06110c1501050d080f13050d0c0302010315082a03010c020703050c010f140a03140a0903120b0609010e04021e030f09150406181e2d0210 63
    0x41509541d980312403410b0926800c81a404a403030a00d503032016004103400c2e225105104000d96419119208581a5000142c8041544956842d13207203580c002401c0060402e207808000c50405910f200e080348002c90000342082081d050140b0284500d8044441e1a0020f04c105400c07a0707005404041e01422221400720b10001820389030340d09014030252030002e50082e00200341542451030902e064841814140300101c20680c0b8082e911121283c1c2c22201000e00545680f0b0800c001c030b02802c0400454020107500f1030521055001541c403058945110b074a0702c0104803580e010f9041694000044c8a40c004000c0c07010410550243c6c40f0044240c4009100600d0051519503400f081c501c400725044008101000700010148449802a04025513000070804206112581002c40740024802840e5a454500313030218042416000c00c0309503400f04845078501c0e00000308c102030030f101c1c1000340c1d80392101d044501034005405044c0c242d100090520041700070b2043d002d04c501c808450304804100f188031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 826973561 1250 826972311 826972331
    0x30405100f020702030709020c06070f090e0103080307020c1909020d0b0a03080405030d0504050306010528140a12050307020d140a0501090c1409010e150d0507080f0a110d06 76
    0xa4070503500001c07030050300182c6035107440c01850715020b5039802c124401351041000c2c000700140011110b1740051545060324010320800c0044942400c19407205020030400300001c0100a010f90165105017003990894400c1c500100070420050b44803140302c0e2034001d8440e010b0024131001c1c0c008002240348800c000c00c81e0200d03c030114a4442c03e5038415030701d41d10003060600841c9420300400c3d4032110f0301c0c90024245420440060b07150041840b41a2041d00c11001c40d8030280139085807403c1c81c10a0402d00088555a9810401030110001801c0c0c40f621741004045140e5200404203285260041d0046040c80044c6e403e00030441d250000945000c94000d014041c001d06c00c00004c00303554490b40000c01d04003078624259408003a01c1d0013080108846961561190319882d941310704440c6003115161503602c0d24514415610b0b0310411850b0080003d0740c1c1070b8140400080d085003128107aa045804804070b00c003146840784220180208030021032520040d10f40f4044081f440c0842c0540c2c00003030b50040c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 826974811 1250 826973561 826973593
    0x17090d350307080709030b010e04061d0d09090c120b0d08030a0c0e0d0b070305060a1208090a08010c0f140d0603030305060405060108090c01122417070b070305030405 73
    0x20505003a80e004004100807090364003140b010b40040d11410100c60203030841e0b0b00c84010f90014042d004078590044000b909208681d0042c4c1301841e501c145084112695813161030715090050014000b1a04280d00081c0404a510030031210490f0790b91358060396440102c429010344600541d082d4003090036180f0001080164004600a24480400181c0400b51702000340000100c000c107207104026050001d00030800a0042d56132120040c86e00041c5075560100298140c00300c0e400c001005599400c03500d041000d10001007190a40440d460310f10702d951041d080c0d0a075401c0d94611400528113400d400303802400b44e1140d222070880d50440ca8188280300c0c120700211045030303005a0000742c031802481031506240c41b480390091000c1c17900400e03a01d000e5002c0e03640d50410300c40d818100500c2c00d41d40803400c030701940910000c3c0c1c2c0c5049070710f10600c00041c40c00e0007180d16010b00404c920344041c1809011200103403044c00c5400d07100600c4d003000c4090300d09a030f1320f4000400a44141c017811140c1c21690384 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 826976061 1250 826974811 826974893
    0xf1505090601080f03070f0803180d020c030f06060102070e190203070f031a0102060601050f25210e010c080903071e0e060d1212050703060317090d 65
    0x8560310080c2015032424169a240183d01150b10156800070446080410890302222880c5600325288540e00d41781c4202500c6100030594001085005015003480d56960110340380c544003030100c0c1154045a00a40c3c0c10b52182c5082e503259015a200034410001e0f0500740030b109038002092000c0c014046003001c0c0e02130507a0b10896001c00001c01604510400742e41610030018030610448840c042c8031840c1c000030395035482c043d0520341400030210359400f03205003540c00c41c0c070562080d5070186000103c95611a225204520080300c4030050070b98000708003601c07014404c1d0700001c1e80d5540c4078401c0c0744000649084807800c030300f5074034210100900700503034404114490003001301100c032451160710865914210311994200e038035450850f038140300542d40c50000c0d9034078964011000c40c003c00708215013501e10320f440c566650481424501086100e9815a025008890245000d0740b040c0341ca40500e11442d01c902c002d00e5a110304005045d4000c29001e8100490710612510b03105900740e9042c080a0000c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 826977311 1250 826976061 826976071
    0x60e310903020d120507090b0c0304080102040305011508030703020634020705011e0804060b030a0c03030e041d060a051b0409050103050c09061c0609080f091e06070f1505 75
    0x40c0c007610f0300c0040e45074030400589200000c103004210506001030010000341007481240d1494402180140d09640c1c107004850080c02c42e039000b15541c9136603180c1240600a401d420f00103910311140c00042c0008080f08503040154140c0c082e140c959a01e107150148a100031301501060580a04040c4090080c001c1043d24040d8940044c00320a16040006040c010b509600110742200c00822128180d08100c6498210f90f01807004200c0420840100785044c0255201070140f01840c00c0000506402800c0084402070581e4240010200d840500e1151412401d8080c2d240c1c0c014000618203008c26405150001c0c200000440d07001c3c0c01c12b0f50307000940c00035003084c1c1d25159208010020420108503a60740000150344648051508500081045181140e20307044038203d61904010071200703511101403603900481d203580b10040398030201e45603009071118a010740150000310004101c0c07440c80c2d9440c90b0380201410301d001c0b4296540100072030a4402184d0041d02c0b1413401c01c005815000c0c80c1d01ca4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 826978417 1106 826977311 826977313
    0x81801150315021e07060606140a11070b030c09010e030f37030909051f1e052715060a0311130306060807060e31090302 53
    0x11348100c5046410f1a118484840c4140341040040c041041c0544010802c2d240c907030600b5981c03940c0c50703501d4401035401800342c00380ea58801c41c00f07031800711003800541e4442943c4101c036036010b400549414400e1880800d0303402055a110700d801c544128110010159100100034041c1c0742c01c58180c110b034800540c07000110042103111003030506403001d8032200c880165541801001500f490150802c903900706000304079003100c08445282c05554401501150368030704114405590140344000412124411700050955644042500f0083d0b01c5660b18210380c0c0b03107007001c0d01c100c0401013400407000328240440c41241c4844064400c210700a080009214484200144544c0500007940f1130403440803c0100c01c0004940164080300c9424045440440c0c0314007041c0c8454880c03203c41608460300584145066201d04c1e50460007120700c0101080c081c1114580c1010340c0d43c2514181d003d = true := by decide +kernel

theorem cover : BRFrame.Cov 826798561 826978417 := by
  have h0 := BRFrame.cov_init 826798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 826798561 ≤ n) (h2 : n < 826978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
