-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3890
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:07.546+00:00
-- url     : https://prove2.me/submissions/c482a8b0-41db-47c6-953e-748222766e0c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 699460431 ≤ n < 699640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 699461681 1250 699460431 699460457
    0x20f071a01081615210c0e010e06070503070201050f040905041a07030501050919061e030213020f2a0d03020310120f0227090a0b090c030709051513020a 67
    0x2000030768201c6858a1200c0c901480340302041d41c80114410300000405c517203c603c072a00e44521301c10400d4601254450b254170003425000146188801c0e818540501801c001500100d07400000759800c4503824600503a5911601000744943d0182d940030703000440c20310052000300304501100700c80311059120307616444e0b601d2004c110162602880707011340000a1002081104c4407410050200e58080782021078015a40c1102011501c2d1652524108104000e8213004500d8004034001c2e031010301c10015810030843c8400144544100202c00c1d00c07807a114109100b2401c040a4007004c445d05c1e071002d550042080c804058065030040b04c03410506100c003100030030612900045d103101e05400c1189484c550b21203074280b103d841100ca078112a040407401c092000840701031001489403a0600140c5041500ea10300038610701405007000005030000f01c0c0b1080f0903100040c0030320841325903440201d1152604c0c3d449007920200341848503005801c0c907060303020188094008000e0100650785a00c092824 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 699462931 1250 699461681 699461713
    0x1e060b03011a03070c1203060810060f06023702040903030903032d022206050d0609020702061204170a0503090610061706010e0a031a06040b0310020f071a0108 70
    0x3c80e00781c1c4c0490003402001d03010401d03000d10b205c103115982c200040d030241c881d0203440c0b074003c1c40540d503500300e03071564001e00880205402c10801040345000810807070f443c03002d0580c44001c01d0303d03042400600c1030001c003000e01c3e100c110600c143c0c4d4018000b0881203405040c010007030030084100ba000310b81406201e1030a0a00c012200e180015a1024460103002030641c490180d40710f508540080d0407204c500712000c5a40520200041200307442e40c0c1d0360340c5041d44c00b8605507145503201200e0b00c4e01c1071009001603220002103a410402e10300390074180b03588511305031155911191400f4042c50011800c0c0b1081504100118001c1060400b00d400c0740d561b010410440c450b142c060035000070007044128010202181040340c000405061444514100b0008114510555072040e10205c090b5a0560746100104850380c0d081b8505031010b104000d00c00c4003003640c40056405000b0140e5001a12000c002041c900740c45109034080a40c00d4950f040d0380c00700088503000c2c080c035034241c05804401002100c0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 699464181 1250 699462931 699462937
    0x1e0c04060c020d081308060405240a0c12060b0d14040807080c190b0f061e010e030304030c031109090a02210a210e0a050303030105041e060b03011a 65
    0x2581e54606055200503800c0c88025803001d48203c0e0b00100c20311210141c40042c4000c1c02c054680d110007003403185040d09265141140c00b8524020f00d2280c02021060140c1d48022180d115918030008a40d00da03005604440b4032440040c3c0350901da01d1301d03070040741c41115130006010450901006200303407070603e0815010400250340c0105030100410085c3c00041c880300182c440d45101106480078034059850341108004500e00441e4207011900c00c00c491002015810385e00400b00760b07200301020305d0a131001c20296600200c40e81c140503400c890300d01c036503404104441c0990b5012041e0110316039245454199400440090fa110351841130000d80490700028846000e95001041201d20701c825000120000140c0e01925490307004d88a00580401d0748480311005640b00c1c0729403444c61002540c00200030760030543c1058820285e11108004540e0000140c9056441c1120b0000d80f1a1000c0800c0038040d022088400350b503820100e00044540101c0302840c100c620458400380d840407803480421040c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 699465431 1250 699464181 699464189
    0x610050a140f0d020a0b03190509010b0a090e07120c03031b151508012a1b060c03020714010e06070c02030a03030e03090607110f010903051b01030b06031e0c04 70
    0x81404402490758a04907104010b03ca0014000e5060305444d510040c02640c01211035409100d00745040301060846d034800d9503802510035008000030850500000c2c400401481190112600c0e016a41c110301000c2c04040028500d51003200c40400c26031400c002d01200318801a0040b42e000d19078440c51a00782e15061070b419606c206c483c070117a604001e2560082c1020f50340040142105140412422401d1268451248250241010186088841059400d600018403003040750103854440a40100030035801100da102d000422900d4100500314000d00610f04088d041307030b41041d40c003040359006510000c4401100010740e07040c1d03903400000395083c040b1524025010780c444d0391102c000c28400d82c002070200c1e404009407840c1aaa00000644641107002d0995401c04140007609544c500002101800c0c0303803e00309200101e14646603640c558001c616802c2807080c1c18034008030168402da110210b01180204030903140e0404c0c104031070000c05200519000a00a14003081d10941604140c0d0121 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 699466681 1250 699465431 699465439
    0x180613080715110a1b030f0305031f141c050601030305030108070f0521011e0b090f070e0d030e0a0b0a030c03060506032208070b07080a0c200f0610050a14 68
    0x130341c05644542c4d0a9040c181551801c001e424000300004501030800022540a60b9445440303040401c1c03600301d40c0e00003140c20302a038002003004201c08014420729100c001400c95548009840300450428801c504102c010b080d401034000105c205034002000c0c41c10303100729804803101d01d9204c102802260015010742a444600c1c3c9101c842c050b01c810150644000c524800402d00c440031028940041c1d24546510713524940312030a05500341400703680c41e41c0c000310102444d980c0e400c0c81c100140c044610142140d02919585c1e0440c01454054091404400d0014110000e1959079a0b08130140c0d40141c49404000ae00b010920546a882805003409490004005602c3c64451001c103102c0241201e10108507140c0040d00381007c5520840a031550381e0054881c183e40c0d01d0300c41c1e40108600c00041c07158409a1400140040c03480d400200565190100598429680d461000b881d01e010100d00740b802ca06d01c104000c10041c80c031300d0604071003250000d84400b072409403560311041d525410001000d0304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 699467931 1250 699466681 699466693
    0x330703110426060c0a0e0102070e0a020c190510050105030a1208100b07260c03070210120f0b0f030102070b06040b19030302010c2318061308071511 65
    0x140e00c001c0c41a4010101ca42c08012908104102d405030500b0811942c0c403000d000089002440d5075000140b07440c08001c240b000d881c010307041107160b42c0c1c1c4040160032100140e40c04507001e425010100314900f180d40c500c0c071280079101c04600c2c0c820340e42c060020344001c0003401c20000041a041c00100340d03404950012444401768910442140c801000620032116403000c0034001801c10089001803030200e0107074a0379084075050b0384469200d48641d2444100c1c0d060208408155004080103491817280e040312054851407001d082211070480304d810b6008264544113101c000c01c01e00c0e9100d070b0304d41034084e240c54420800b0303d001c00d401c0b0300600700c000d4106400000054800c1c40c0c2035000014107100280f880c0700002000c0c080c121006816001200543c0d034442c41c45d5019900310801c50080c4c2d0303401010020007008581450b440d405400f0720100a10082d1800071100d50300c600607507414400c00080d01c0039882c2d41e00d500300d03901d42c050321466140710981c1d0380101d00300d4810044a82c80c03140020080c04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 699469181 1250 699467931 699467939
    0x90b01170d0e0d0f05191b0503120f09180f07090b0f07030e180c2d0a21051e090c0a03120c08030112031106060307060c053307031104 59
    0x2900800300c00c000c0700d190181200c920040c2c2c264525000c80140140c011f05070601062458000180064000ba44607134040c200600e60038240100700e0310600c580214058859008401050704a1681c11201d01d03000342030000c00528000d07100e51103104103841d41d40e1070203481d40d540c002c6030140705141c1c1680c0940f8007040703a0001300e03000b501e12000200c03002c0c0042d448040f101082482800e0292100c1d806244000b900e0701c44c00903121070a0610720240340016988074407214280b200c42c842e0201d28020b006580c402c54044039210169032800f044500300602007440c3c000c3d80e07100c102022703165136200514154045403980000080a4081d6000034004042c46400e40d00d40d20a800d40c114610020841c40c0400000083c1c0c103100618020440302074110401c1d400c628000d803d4613100d02c4401d10360b90188081041594001031648211203190400035072040d900c0c1445414030071039070400b0b0000c01c000714040b5580c480d4001078582c980d1105071070440540320840100c00341c940c4e400c0344441a400500040c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 699470431 1250 699469181 699469193
    0xc090c0711010e011e021507020a0516050603010306050c0702030114010510090f12020616060b0901080f06011707080102030123030706051909080d0e010f0311030c0d090b01170d0e0d 80
    0x5d90206004494062200e034105811400c411901440140c01c07440e0b600081040c00c00c0ba168a0400d21a407105001d400c0c04081182400144005017409407144003150004405c602150880c0c2c0e0040d0092007100340d0115244141d140a03c5800c1c0500d40e80796605070303524418290714050b2040712102d90401460440c0d410b81c0c001c601c80081c1ea0154040020000c3c00c5041d1100d5042c10784032300c1c0c0c0418030301500310800142400581c00300703007590002201c03c03402d402c011442a05550701071101c0c0c101380141d140210b18102c410f4110180c0c83d8800000455030a100c8200c11070136501300f20941c52006850024503488000901c514008928280300c02c01003000100b5030007000106519200b114941c5e40d402c450310700f8401c69880c0f00412180c2941c5c18282d68032513641340c3c00d40360070308043c001100003600c01c0040e440018801e084640c404180c203002e581003508060030a031742003820400c055031580070544074400303140501c0500340308240303910080030302500c1c50307450a0324001c2482c0c0c010b5040751a41c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 699471681 1250 699470431 699470477
    0x6030b0a1e090c180501050108070f020c1203040807030303021e0c07090f0209090a0f0b030303070c03142b060e0708010e04050a06060602100f0b0603180c090c0711010e01 75
    0x48400801028010401c0f0840d0391040d10b0030521380d032000c101d5500d4080003425480c03002d0303c0002044072103111194287c1d0001551124200305541c1d01d05546030f000d4854bc19802960407050440c02114800428550300d90050401c00d0002030010054010b50500c031155803040405080301500008000c01140a5541c03100d03440e0f110f40280545450a1070000034440032040b80c18000042d0f640391640010002c82c07060540e003041c1a0025442c2d4100004040e03c441c0074041c0c01400c000070202d41500c6c84058030b068402d102c0020701d892080300354980c0d002842c6d0301101c038494805840d201d00003640004a1a541d03000341042d4450780c0441e42401480320400e103009205170740606c1903541d0b0348009986031151100411140d4090f0000d20401304564080e28050600b00c80b0003410441c00090944d1b5280440703800081e0300c00e064a010341c0c051526410449521601e60340705170000108035000c85034000410802c0d12031200c60214070b0144005480d17aa0012260302d00140070031000401d492419200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 699472931 1250 699471681 699471683
    0xd0f0302070f03050c1501290906070c03030807050304030914060c0f010c120608100c170702030702101d041a031006050a0812120601030603120306030b0a1e09 70
    0x80035250088070784650710890005002100084c0d80018100d07444002030003400ba060f10124444078140d407401c402d008406028101100002c0c2c0000c40d9400c0580003c1d08070307210041d0281401e0349641950a103000d05682d03920090300499050000141401d204038102c82c030859064440d0f030003182c140110b0010034007001c805950442c00405c402c02c003c00040108843c481484000070581d4810804004c100203d0303010004405814090207101c003900200e600714031040110b034005503504980408071633001602403000000d00ca00c9080c002c021394084020a00300f8000c0d207651401191000d41142c031600c0c0341a10641c0f010400703e00d240c56141c146c00000054031a44040c080c003001c4d140000f804c3c50b4ad20509024440e0340e85000300a0303070900c00030f628000e011182c007400286100106180c041d105154aa2203c08000d90000b10543c0c042d48c030400103180c22031403caa0103407128501a0091520340026542c500f115000038a2100c098042e00816090007200503e001c11141c1044000d040d0100e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 699474181 1250 699472931 699472937
    0x80111120a0b0f3307050a170f280e0d0b070504270612020303041202131a03010f05160c060b10170f0708400c0503070302030d0f 57
    0x10340200c01d03a0360980c400d45130300c1510340311585801216500c00e403103200c0080b52009900d000d02644012603c0811113540759901714041a810b152800340684031071240382ca5004c9024804a031520f510000b444c00d041e07400904480320f03a0f0003544520140c40301c40035490b2040c0d010102008000006402d40480c2d13170403030100e0416600300b688440f200001020300d0b02112012031501e9841c40000c5200b405807500400840f16001000b551a4020035203a110340d0140010504414140e00d045444100700044015034803002041400d003481c200c1c0e880400039086051080d802d10107000041003551041901a0b0259040c0c090304030951501660036000d07008068174490394409a09040307860329850b039040e05403290b84421000d8020b0311590501d510180c4010032030f2031030200b0000c4154003c00110380120549007507040003400c040e440c000015044103602c0c0c41e01d0780a101400d51031300a403041c401152241c0003516506484505160b038405191002a50540c1302c00c64004103603000e002c2c4508840310604d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 699475431 1250 699474181 699474199
    0x30501211109010909171908100503060a06050414070e01140d11031b1201030f11040903091415090132070606050103051b09060d05040b01080111120a0b 67
    0x500002d4000109a01c42c05080c1d0301c610081e030402c40c28050003840d22400920742c500340b81019040b10f0007207a00105510900000c0004180c51220490724003004110080c211039140c03400342140c0001d00441c0c031416004504182c08151000e41e81e50240d48542c441c2c0d500c120902c5000304c0111002c1201d81c4c40c0100d040010031804445400c10b001b0312400072481c030030655172400e21060030004010b81a0110602907018003000c020355038160a6141100e41110021b00508100c1c20f01942c0f4007002d62055611034540035a40007096040020b4604485d00203441c484401445c0c2c7c148800d000b03e1044142c0012010062070a5660003080542d04420050500c0c085028424541c050480c10318151b400c0070703a0004c01d84804014480c0100005840286400c1c001c5e803d050041240c84000007620710480703140032a6070350300d40d122002924032001020405100d00e0a050401030204503003801404104d500303002c18030030000380700800c0f00c01c00300280d0503681d11399070b07000040d90050480102d51544102c0003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 699476681 1250 699475431 699475463
    0x2191715061e070201020c0604060f1206091e0b0307030b0406090f141c0c0b04020411130b130602011509050601120c020606030601080c18060a03060204032103050121 73
    0x200d504441c403090b02041c1c241d40c1c3c2c9140d00019140202402c00948110010001405440c1d0b111036041d007008030a04003049405006e400000103480113801280ba140c1c0362081c05890440006800305010141c24000c01002200d41c050584507101c034000034090462402c0800d000032465801843c071140900141c406424143da5060a41e00b40207400c1d00556000912a10320403486d00c2410384111203604111403901e80ba9030750660340ca400200080d00c5a0350b42e140b01140c0740b451000304c03403d14481392006e042407a2251041c215a41102802886021403c2000719000740144509110442402c0314045803d140045c017801400c0300400c164104a569440359000c68150300894131034110b16009485c0b9450880b05161400038164030022042c0d2112000c81c00c0d9499a00c06034600041840702160550355590208070b02031601e40c0001c1900344005030000501030030324082e6441c4901ca01c2105820021100201c003901c03404e000384c505609603107c0c4030031001003405620800b50700c52001c1c88510b43c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 699477931 1250 699476681 699476707
    0xf030a05060f19140a02210c0c06011d3103030501081b15090d020a0b04030b160e12010f11030901061a090f0d0c0303030219171506 58
    0x3065031051414a242001e20004071100d07103806840038460b110400c0035038282008010303090030207410701c0320f421b5002581520f4480c480340c84541c60190300501c40540d00380341d9981c48440c1c0c0320424400844c0a003030000b08000c150031529054400003400c24000c151202c4142a03590000c1d501403844981d445110298940541842c140e44035000780c0300001c0340d42c9052032450400c03800c40c5051759503100003241d43c010703603540d03d00d005d46104801c4400e0391915020404185000c150080c007135400300c80c001001410200c044014001d8a00c03030031403100240c81e404070000c0000352428600c0d0200e060714124901ca0304000095480c00e00c071650011801085a92001d800c43d405030980724400b00d000410061062002d01406006000d6020f019042c0c0c03202d178030340840e50b001d01141b2074415611210112101e50301e000c41d8802c51600070020428107503403454050002c5d0f0255103600c40000280c03500ca00c60301c0c01083c8140135041e104e481c001c0d40d45e0f101045104440808594943c0c80301041c4234403401400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 699479181 1250 699477931 699477943
    0x1908090304092c010b01020706050903030c06040f03110a050304091e02031524040e040507150306031b060f030f020c0a0f1a13080c1207120f0305010f050f030a05 71
    0x42003440c155090385a283c494008103038180c2c51000140e0526111880d2664009541d600304c40040c03518076219140c0d400002d00754419445098054416101400f0901c1009040d0525191103521140d0407001c0701c40c010f94a4a5503100c011303203076810900007000044040e40140c0c0c41550f4544032044910100315840040b03030401c1d500f64140300d08448800307015090052000d0781010b0364800d001d280f0b00003454a00418401e90081031a24096500410100a01000400f001e0580202410011209640001e00400d03945c44252085a1440d075031004051484007141d0a2318440d0340c5a80080481880c141c010701001c00309140391550821601c4103d010a00c0303030b044031070f2142d41000d449011030300f8400f1000f0030400004042c00300302401d00c80d8010414011001c4a83e001e00d1f215221800905a1410590000d40140b08054005002d80411050651900e861401070315508503d9240c0c01003202200c0d424012003040070f0381c10a062180789042d483e2101e84002c02412144611032503511030b401c200e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 699480431 1250 699479181 699479201
    0x30f03250e01031a240705010627050106120903140307020a0c09020f0702090a110d061d06030c0d23010204080d0219020d06091403030105030c0105190809030409 71
    0x2528941c140c04980d0380c14000c0c811158409001100b1030201c520000d5405040c1140d0308a81000010110314112045070a43e018a0b8010000f002819a282c51041d0340540c1134004040e000c1c615445420300c410a41308a40c10f9588030740e54543d15200580b2078200500082c032041e828044a06429107059820300c00852083e0410340c0078002020013880c0504600d98590400400d190052014604001c0f0400c241c924054048130f841c1d185445d121ba10030000c03da10b0354404410140020020a1901030750460000c4030b00c40078002c10130807130302c50032040c03410700a8441d294036822203140d4981600d00040b03085400da0040004002c41c4071400f100c100314001000095000d6500481d081100a00c184000303e40506140040e1081001610524441558031000213210740341c4078610a0070b1000c1c1d41d00009045500c480c5250120100e508260307a20f8000341b00704d51082c428660100b060307511450030380b250b9503486907048030228540d050a80c0c0c9840c0003800a2240d00c004d000002d0110f8860082e02c0c440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 699481681 1250 699480431 699480437
    0x3070e0f033301080c210a030504060809150f15090406050603071710021b01020c1614130c02010b030a03030905060601030507120906150303030b18040302030f0325 72
    0x40d11014079141c80000500448400302d5003580040180503404a011851414101e600d00030400000c034060b01c0050f03e0b003201841314410040d10104040d00f100041c4103981d1a81c0300c48103640c2d1045400c681c1c2c0d008030042440320031080c6c1d0104c0d000102420105410110008459510480440114050000131075003510300700d440d8414405581008c0c008580605002c190b44d080d45050b54500558450780210804100c9a000a40e083c41310702c0104000014260a0002c1d9581c214040540d5174a05245110081d120200c00c0c002940c440c00b42640000c0d0303070700501000f0703528503141344510080901860480c290754881c00307100d605a80501c4120100b030310035107000030025000c1c10420b2404100521f018141441c05080c00f48654000d0b812108100300310002150307900051800a016091a1030303288000750705c0c20300110805415030081e40c039606060b142c8400c1030743e840424920300c400640b006000b603042003140f00710f88260140119400301034456131340a590250b80c1c105200c2200c85103c6000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 699482931 1250 699481681 699481723
    0x10b0d030c0c0f05030312070201110d0207120f0c03112508010f0203061807270806060406030305070b100503071401030c080105010906110f0d080108160b03070e0f03 73
    0x1040314500e03215014089480c15103c101d03080c540843d40d07034429441500071020036540005e00c1c1a100f508a0f0810f41c1903a45156102c55129102c4800303508007240c120f03810340385d01c460940e41d6481030308041050489503803164002c0410b5182600c080c80a03054890703080c024800b150ad0340e000004009804001000b60745840646406841c90031241da002194100764010070610583e661042e108a850540c08030380440381380c0b581c5400343d42c800d0003600494041c41903400003c0040030030090040482c0e1000c016070300c040d510601080b00b202c4081c000103000c03d0080c000d070300c0820a2091410f0348010500048012942c03524002894441160b01c10002d0a0040311150480d5a00d401080d40701c0c0c682e030404144550404002038240500e901a0340304110b403004021901400c100600812581000d090380c8000c0110440189072000034003e0303020910039142e40c201802c0b00e17011031204903002d2807011415030311016030840e1001e040e1202c25901058042e10040c8aa0b802c0c030001c1c4c6544010749510130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 699484181 1250 699482931 699482933
    0x501140d0614091f3503030a06060e090f060d0804140a12050607050a020c0405040506010815070f0c0206040e0a06141c02040c05130e1b040b071202010b0d030c 70
    0x904064001c0c2200a80c1484400b0700341d0307040140140405495080c40280c402c4c040c05c0c4840d115403000c41141112003078000d603040c012110040015405204090014040151921002d84040d2500300241d500080b1080014440c01e4408100c5d82d0070041c000d00c0c000382200a516245200d0300300e034001003040000d2035040f20315441c2c101d1144004000c1c01d031102210080340d0321526210040100820203120b000592402d000748280010005000002c104020a00f45402d00c20358440090240e40081d2203800f620000d107038020302503a44903440c541d69581e80c0d10300f01e00b0120344146500c942260030110901001c50400c628440c444c0c4200401240040d01c9898031b0102c05a480c3ca02482c240908000704401038044150a6081045034043c0c801007161100c20740116a40c1c8207646124104110a540200752804100c3c0740c10f0040b107201c1050320f4a042d10b00b403409594490703481070843c3d00108001003000524040416510000307280000900043c005002c030b425014290001c800160081001070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 699485431 1250 699484181 699484189
    0x3060405010c03050f0c0904050606130806041e05030d1104050a03083f0c0706060303200321090f010e030903150702030f07060b0301020d0b040c0e0a0501140d0614 72
    0x3940140035045c0e8000c24280000d48190900c0f451041e81e00407520f44000414549a50013202c0011f01820890008c0c81d03500c020b083c1d21b90109940840b001001c1c01d55010384c00d03241c450344055840e04100a03602e00521202020b00400080f0341400c801042804000748541d075201c3c03103000a40c01116401e0f43e445002c00102c0a0340111400807002c040306800d04038074400501c4c401186914803070200c01442c0c48868a0f81c0e6540940da03402801d250603c0c0300030003003580c03000c0324a0f5424a2051310114209440301c0054981c0076080e40303503010700f800702506a003144d04802155040f40404041c2d4800a0140c0d07040350a44090000d061000d50001800c0491401c08104402c07212690203418035550601d104000e4503441010320b00382f041e60003c0b0f5460107002080e442003244810080c001c43d1303221040d042400107048860a1148154034084c1064606030044a45c18417407a0010462401d80381400300650b100d03c000e0004c1200c51005101400f107008007849000090091102c000949100101c204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 699486681 1250 699485431 699485441
    0x507030b09010b03070e21150c09030a080a030e0a03020f0c04061d0402030f25050d0209041203060e0f010503010c14183609071a1803060405010c03 65
    0x4035004403101d50041004400000550360032080d5446c000102030541e10025802d21010b2070040801208500c251010400025407036109040346d004d50742e900e0380c444a0f0001305000300a00c2c2070300364010040000014907240c0040c950103069040006035401c1407440306292062042049025a00c1000c603041b58000401c22174102e444100d400340481400c000c0c60f807035408050544100448a400045011941e00740174882e50384000d002100e01c0088225103001140c451001d0b031205000f002c0001103450b0501c0040400601d0f00035005c00010388551340ca281c2c1041e0200920010107a95180115100e03942e4104070380241da0240b00014a0f5060004140c2141d484c1401d840c01e005030036628404500510050707456183c2640e800540c1c0d085803030080352406c13000100e03014034028244002020b601c040139140751050103a03117a00105a40d40c1c0041c80c2d503200b4600418102c00041d075800c410001c00340000340710340e0700f504e1210045040007101080c600181641c0841c1c003a51690226502c203a0b061080d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 699487931 1250 699486681 699486701
    0x6061806050f060705030d090c0b0d3207120612140d050301061b1a0903071718060c0709020c0a03020c010c1505090c1201062102010e220f050703 64
    0x5110704d440b2140da02c4a560748558581484e10607210b00c036010600100e0f40000c0700412600ca0055960010400c1030f81c0103102c2c081140e0380541d4440862140540b400c0d05840688000c0002c0c08415260710600362071100003a40c840310021740b55000414031401e900e0362a42c00c44c1c0306091207404507815035855400d110320340342c00b401040001d200420941d640301d00031001030780b60007423200c0784c50f41c01d0b00301044000010000d0040c00000301d0709010002c071000008104050082451030040080718020368654481d2040040408019500e024440d140100052914035082021500c4060b902c042c04016a00442d940340040d4110000036010b05070184400b00707104a007464081c080483c540d440301011040c00c03003208030b13860faa50006001020200402c04452000a22110101e00c4020585010301218010300740b10264005580303003013a09141804c1f183d03c2c0e0503120080d02480740700602c80c900392000b0444a90340844c2c400304243c04094418480301290074030010565180502d80a401c2da294000c13 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 699489181 1250 699487931 699487939
    0x40b060c103605012703080a090c150203040f0e060108010902190c020102031209030408100e0a030e0607200a240e040e12030412020616050706061806050f 68
    0x1030100c0c1d03042200300000325007181d42d881250106203d05095005041d08100344802c415040d49042c0b6000001030014004c52107961480c5050b50303906005d005940004e0310042100014003001e211010b007146481e84910386a04c11641403d949801c1c0c03820080c140e500034a01e0b664004180301c0656844507216014000c681429446e024420116610007520001d0f01c3c4100b100c1c0313112910031603200380300312001c542090081a545007440b040d6130b61650b019218154040c8200aa900c0402d0102c5c0038602c40c08400c14007400380c13100103440a40c1e09004940c01150310281c1004040001000080b0952000780c44803040c2550220368418081101d00d140c0110001c2c3e02d584c1c400074104030448480340c0c0e520343c59250600022619402190103001c00202145c1d0341e004804d03044008603e044003552046001d1000b424002901c00000e036220306c002c2d41d046181080c41d801e001c408a01440060080c030b03101308000210280d0721140d00340c0d00790207003011008103510760b18104140c0c45d01c0040a50407100441d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 699490431 1250 699489181 699489221
    0x601050711040b0402040806090706030e07031a0a0e0d03050a0b0402070506070e151606050a05010b0f130e13140d09140f04090b010602061320040b060c10 68
    0xa1150920789000540746441281c9440030b002c1d903610f4580544008100c9502280c5560408034041c540b16a55805000c00180c90203001d100c0c81c00000410b00d08680c0c120400144244490040c00c40102004042840c0e4a03215140c03071088103010060310200b007490740c0e00015942000310140c81076422450350700d4400c1d0700500080d00800d030041001c9401200070b080501c031075404000403a0060410003440341012a01040003e140d96006e540001d0083c8180c000704403e6a03542c02c554200c0d08203000308040002c06020051740300000740001c00f40324a0250081891540c1e6040040076500c0031500452140c1c01040e602d4100035800102842103481d66000e008082d01705907000702030300f43c98802d110142402c02e0005026488a07140020012000b030000e114858213400c028051b04002e00c04d620040c4103a0000034448642940c210b401d0719840304110100b803079a140780100d0b01c0d86031448a54001e541c1d1003003182d07954644004006003a404c0d009086604404040002141e001907a614560250341d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 699491681 1250 699490431 699490433
    0x120207031203050f061009050a0b0913090519050102072405090c060901051c0606170a0501031a1503071e050f13020f070b0906060f010e0112051810020d0506010507 72
    0x2510b0704c254081020340d90324041e544843c50444400566030f22980d00030380300c100c02042a40b40301009121600081d1640b000c00d00e400010241240e14241c40a08a90040031078045604d205410250b5030f14090000582052a40d03100d411107a494807030249008640c40320035060b20b1a050042a81c40304941d40030b2306c02400300a010842ca0711551845904000001446943e4401200d45140d0f5040d81d60b14100901d5407940000b0b0188810303118801109001070001a080b6519030103440e042e40d0b4040710342405040d5400600c810342e2006400c4080c0d0b0040a0315586d4141c40c01c110180040c8035400702c200711082403c54001d000d00c420b4000a005162190107228152900031138042c00d06040c0000603038494081d8540b2031680503d0740d00408070580030040c0720b0381c80d00009000c1e01991044030151026450800196000c0a47d68040c0b40030485001004682410383c4c0d20080c0d10405020029004d02540d94503981010032503464034640940c04205020006060311960390300c0402030811070729010701 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 699492931 1250 699491681 699491701
    0x305070c05070b09240c070509011a031e0f04020906030d091e1203020c030d050304150c0203090d03020a11091e09010b060c010e0d0504050d0201120912020703120305 73
    0x464003400f40800f800107121036460b25079040d1900c00c0400d0030a420303449904a1407585859000114103c0a8441d610000c80c452405504c09d80c1201d41840515504110b103406952180c0c000520107400a0017011b94000039003002c124240c0710b04204514031342c041c038181c4100a044400540401c0c0a036000f07044008030250480c04140680b40c29015005809c002c90485a44402c070a80244003003401210380c5800301a0009102504424100e09481b07003d903034440c2c2118540000c5401414564010059a50721034090f4859145e00c1914810303a4540205c49000ca00103c003007020440c0140d2010030020140051100308a0416000300e981680c00e051044558800e01051202500c3c00810b40b0041070700040254032451000201402c0140c603104031300c1c0540c1c003c028505c14070403d4020082210b20b168480d44c200c0d01624401001d2004641c02d64004458440c0300d4000c6030701c05a6903210f0000403658800b03039128032104550040808034103610f454802549010110801d150402c420b00000e180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 699494181 1250 699492931 699492943
    0x501050702091008070b130801151509150c0b090c01200f0a0b040311072702040e011e062a0305130e0a240603180c150305070c05 57
    0x501103600c0e002a0f281d802c1c5402d40840070b84d019164510030300c1c40c0003030a580000003801c40c04d450891840e004c01c0c0d560090600340d48290700f04002408094400384200c2d056034001041e4059a840d000900a8403041c8040549001c0841500480e855060220070000033321113a5900c14000130140111503403040c000790286c2001c1c00060000c1e81480c0c1000d070100000c005105407100a182100c400c0426805e00c07552408081d242640001c00c8a44e1440407039100003414412901011b8402c0d078510420300325088003100c907010b00380d01160208000580c4c0385881810034003030031110f44200000d0882500b070249901d1650b01007828048442c000e010300f64180708501b510110664044000c1c1c807201e25045805109500c2c07200d03000d44610101040800c141d04201c0e00c00c0035000000c000d40c040240c4c0b0400f2040d80f01d40141c0f4000c46036001403003140d1080e00b10090324425803050500510055540d03404503091034002c0b441d1040002029410070f81e242c0281c0d07800180c20b08125200b01c003151500ea0700c4074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 699495431 1250 699494181 699494183
    0x6070f0606091d0f0604233703091505090d0c14100518010309211103040e0415060f030f170301120f0312090c05182a13120201080c030105010507 64
    0x20030101c1c450030020200c1d160b0703505a2602e80b0a8414a51032180d105848600c1d0341c03e4140030790300ba003c240e9031201f2380451040009815440341e80409241c640840d10b015003042600042242c140814a07454460700d000f5007040d4817410890320940d0402011130b01842c1e4001e0003d10803000c1005072150290060200d07a4801209068182c0400800c40181c015020841000700810034a104142c0345500540303a42204004981c0c511281c8043d454100d9501c0c0035a02500546080c080d0204002851003e4881d420344030703042010031541c0d40e92401d041c654036958400d032429041e0141a0301005680c1c044525070f05407802c0f505086504002c0001c2560f0040900148882a6940a501418019600305a000b03440503070070701c0038a219151680030703525103220340303800380304c3e5180099880716440740c480d441158036403082d10062003c601d034000d441102d40702086032490304105604100704600e000d003015243c400f185800c0d085843c400103143c928000c1188400780b40c1032005210580c1d011045981d22 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 699496681 1250 699495431 699495443
    0x100c05030a0209010201060b03010905061002070501021506030118050a0507050a120b0a0902060d020a080f0739110127060f26180604050c06070f0606091d0f0604 71
    0x14495503c0180c3c010001c81e00301180031000400000b901410304d8100910411040d5560144119042002d0742c2e5080705000717040c0541c00a103d5401e250400040302c0307600007801030020441c110f45c1e81d42564104440700b02503d1035040345100006000e800c02c03030703800245411340360aaa01442d203025020941d14201d0028603080f090004201c00e07911542205d1800ba40040c4501d0303940914554002c0250302400d50003000c600800b0001c0c1030302c5040f020030b0303220f054036460302c640c81403512921004030502d0f0510100c0c0e58103500c8024403451106403010243d148552488881203828100150080d11589000205002002d00da03c0a15000b500000704650340b81c2441600300482d011305594814800c114502c20580381c2e41c50b80c1c10700c40e082c02c1030742c010200341d0b100b0411184001c10f501c0e00c0d0441100c020f0081d40c4110194041c0b400d08000500e5000d008408840070f030302d01c07581c0314800e54000703600a096064032a600b100f94482c08c414510800ca000c4e0008080c415543e02d186d80c1c403000000d001800d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 699497931 1250 699496681 699496687
    0x609052505090f07120501170705040603080d050c0403050f0703020f060705100f020405041118151c0e0a0b10060c1505060a120804030b060a06170603010e070e09100c05030a02 77
    0x80d140c003a19000403586101c00c8140300a44c1c49803042c0143c00110382390708000b40700f8298000303020700b0144604000c0e0398014016520b841c160702c206602818019100354410842000000701241051000c00c1d40c0c00c45080c06403984621f1401082050003002c400541725100802140780010383c0000d08403013040c43c2c0000802d0880c0900881c100034019588402d40040c00e1000a8034000b01c610000c1504480c20f0008481c1c0c00e41c0f030418007603150320b035803034101e2092003c226075550403c60300c59806e2070103d0a0408140704032440325650414481c60003ca8840409005200c0b0492400e1070a00241c4698900503104a0050311640c040c81d2181d030108101c03950750b00c04105c0300e80712502c41002820314240001c017488050f1402002e154440d100540f140b2901c01c020130b00c00d03e02484584100e44140c1d0b214404a01c50040d0101b01d4031029000d40d505640c1c41c1c1c078072646003409102003001003401c100115041c0c07404003081c2c0c3c248401d40c04098610303840c1c500701e20409a04441500e0f001440310300010b0b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 699499181 1250 699497931 699497941
    0x1031b032703021e0102070804210609080c0c090c070b130b04300903080307030f0c26060a030311121c0f0c080a09020a030609052505090f 61
    0x520303403012500e0703254010025803201450780000d540d18101294080c030b080340c000350711942c0d400c07800b40c00c20041c24100100700030825104510947c16401109030711010030700c1e68990f00d40c021a202d61100320741c03c0b040401e19082c465400d2000c08001030003516400701d1440c2000035031007136100d004401840c0d540804003003004050030700e00b044032080d0712684e0030203541003c0c10107800c1d403c001c0704044901c118043c0e003d45040390440840740f124a141d02c600e42c000c0c9c116034501c1c40540000f08850100342d56145010140009401403100001c0756484900b0103184160902e0401c2540c0c0021261415119041c0304264640c0f10845048075010719084103031043c480042400e1690701040107030403000201f03014100d680c903101c01841d040d1030305900704002240780241009503104080a20080b03607800000030b50b03d0b41c141d08014007031440208003158107916560303407600303c0d841030400380c503158803400400035001d081c40c51584901078a08102452240f8040014910000087c9034842300020440411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 699500431 1250 699499181 699499211
    0x16020c0102060705041802220f060e0a090b040b03150601030b0103063f060501050f0118170a0c08061f0308070f020a23040f0e0a020f0105120a0e0c01031b03 69
    0x117184400034010120a25480c0b075010722400d4140c0c01548034851481d800015850301607032664200710bd003d003024a405191a4083c03005001030b440301a0807a4641c107030848136640c28000c0744070b19072100b1407905070781c180600010115a40d03101e01e1814146459000d0183360100c42030110404220503004005046200c400702c000c82c1a10350b810384914807002c2d514200301c0e0325004141a100b065590132120202000119000784007056039070500d8402e0700017804811442034082038a032044c041101d40550666565034100381081e40070074603d82010b4240078030000c1c2c03040302c003071020540c07800a8086400c50f1251034591041590040c852409030300180d04540303c8111510040503102d1003001950840049000004283c83c501d601c5140351a0314105410580c1c4204c04503051580d00900c852803450f401c2c802e400d070894000c141403140a106000324800da40010a200d0485114081418101e01108616040a400850b4107250030807440709907005807901001702841c0309260100f0490307442e00c984 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 699501681 1250 699500431 699500437
    0x60b0a0b070803061c03120c1e05090a1203080a0f0b040905010c110105090a1407270f0c1d041d0c030c0301150302010f0e0916020c0102060705041802 66
    0x408221403020030180c050280003000340d40300300400c2e15004501c1001c0d000c2041d000c050504001e003c101d8010f80561045016030003400118070b2420490345500c00038440c02401502c9101040c0054000110122141090110500200f000362203040c0b103d101581c005d0300801c3c00500307400029581d030070000003842d15500700c1250700300c02038020000e03517040d420b20a0103446200507043c00b141405030030000081c814850540f145502c034007e0025903a466a80582002c3c0d0000350301c900b48a05a0041030040c1007230001a0400b5098401c0c8042c83c80302480c001c103540d06214880680e51501440c5040c064005140c1c4103020814640b0101201d214000503008204071071404c05841400400c84002140021b15001844012000c43c1c0c091006034042600b40d4510455414a48558407030420040d40900440840098581071600714511340c400400c0500034100c0ba0104401e88002aa003811901403209040011081c8013070300d0316150600025000e88181d104d40c0e030b070f030a05214283c240c2c00a0390741030b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 699502931 1250 699501681 699501689
    0x160207030f06020309062401110a121e0906050f0d0e01090804050a05040b030c04020c0304080609030d05010e07021e0c06120109060f0602060c0901030e0604060c030513030c060b0a 79
    0x4041e1611960030058029002100c05100e5445003030042100900740c8100b21104941098000031000017030f200440b1a0004000814903078841c9249000005d0301c1412018007058059558030788060711485c0d00c000b03a00d0710308100818803076035480500045501008a80100d0900700f0700766074030511194403500800114402d15015403034000c0e03030000c01c0390380c1e03006000701c3e5003c6071411816921041000219030040e003000d641a07100d1003041c1c00341d0078070790081d02803803840900342c9082c1503941c00b03c1400d10204030b4001649410000301c0e144001d10a12560780908840c8403541050724154401039640c84d502e2410074190000090701898a02c020002040140320240c00c0302d8030745000a07041111100c0030b0203003c41150030040082031025056074050101c545d0ba80c002d24281c0c1381c10350080c42c140e000090103410503071111840f041107041003180900a5100340000181d2181c0408003c003141d0001c0c000c40022011407200e2804260300a00281e80c2c25008200064120759003000912680410740c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 699504181 1250 699502931 699502943
    0x70c0809030d1d06040605031902120103050d03110702030c13061a0301030218040201050a2303090c211203180d021e010216120c081c200316020703 65
    0x1022140c6501014000c070001140000d03c083d0b079902070030054a0f0045004000005100340005414840030110b852648d202c40300b00140360003d00c0005106540098205070b50580c890703072142c03015551500c91050015a4444683d0400410780c0c0043c1d226101d00403070a1083e014070003546550281a03000800824003100090a0709212083d10b0283c0d0b082440240d03c500c204a42c0f090501c640000b041e4401e0364140d44862411608003800d581800000303800d501180120740c3c040800c3c05402c03006601840152005000d00a101e0040103040d00e040c034441506c80020001c240c4006070b0012700005034000c0070341956100d6441004044100481d02c1900c01c551203400401d10401d900420b100d2040304440c00d0710600e807904200c1c0c542c03d0303200d5003090302c00d41c02410407000041404c05036104031481051414032209040c41e142c2c00d22a401060743c42070048040f00b94100310003218418030070f05010035403480c0310384030052940201600009101c000c402c1000740c40b0b401028802d00150000d590700107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 699505431 1250 699504181 699504193
    0xc1314040e0613021215060913020a06050706150f0b070602070c0f03150b0f011d0d0b062b14160605120f09070611031b010f140f070c080903 62
    0x400e50581c0b0400034044c1d01556003a08900ea00c1c11000c01c011b015115840a0900f060b2260020f001541000402c20844000315216120040ea180210140284401c0d80c03440d44035480307070a14804541e0a00202517840d030b000f00c402c004640500d0042d40c2140d05c60804242c8030032a0741080c00c080e02c03846100506074480304c01c002c600e00d040d04c1005d03010f4034040d400020b41544845c85901c2120940400d00b64082c0740300c60001c256610908000c004a001c181c0814080c45222001c52050543e0b0401154000400420054542400c00340400059101780080700c1c41241c800e10803140c4030515502408040d0080006101d4901c00c00004500c203200d01e0f20944080d81d80c660040480d04841044880c1048141c086042c54148048450060044c0000307880e403e0b1a080050301d1904203400c0031101070005200d03092288903000c0c1c034140501005000418030140101c01d000072902082c11034250302820b50280041c014014509035808002c50034940f0050301a130422918502680206940c54403500c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 699506681 1250 699505431 699505441
    0xf0207080a0f08100302061c0509011e0207020d1103030f0a020f070f051809011b090806061903060203070c08070317010e013f08040e0c1314040e06 65
    0x11800501d6a000140d03103041c68070801003000c940514040c1d40401001e100d5420900241c601100140441c4410b0b072038100d039410781e10542c0c0d011b9800807a280501a5547c0b0802108204030702d40c600c8134a50206001c40ca0810182d0008513008800c480141c100300305442d40c2c58240d00c1c100200e50032403400c040c1c3e1a80300c4c40740c050004c0da146844560750b04940100600069000b2105540a058400080c10343c09406451154064600c0d001080e650056417500d1a058001000001c11000000039030b80e5100d402c2c1c01e01d00313580e12344140613041c540520003e0003c0c80c0c08040d100c0005081d40d03800304d0050387c1d0b500d90a008444032b40113908040e00419000854000301900554505200d94aa2080303032050b0784e9542120350b24400912031842401501c0c80d10036a80c101b032461040d021254400d034140e80b030800541c40e103140c12088000320b902c00710008041c0001a100c4010b2a80304a4980700719203045048112920203110350320510344036202c240b80403c50b5a585400c50700c008114503007191341034508 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 699507931 1250 699506681 699506693
    0x17040609081c0e0a0209130c0302041a0a0e01061b030201090b01060918090b15041503081b0c010207030b06041d10110c19050a05030a08220b07120f0207 67
    0x4940a40ca1403811000704a806001305040d001c250f0010030441499544e503003000a61500da4200300c074800004030000c001a40e071403042450a004020000c0b03c0000d40f0360503c0004031481c1c100c11903841407480100512503010300800300c2140f030000410035004a6150a07409808100c03001451308504c6000826400d5124003048100c076520950564100103202c66032b02103509071200a07008000e560001060700310403418100c43e48c040944001140c0c039002c41402e4420700141c000311580740e800612102103460182e04201605140e50103000448402c1001039681e601c580310052040517482c000407aa90341d10303408400e82d0094000142d001034000d049541d2600b49501d4014052840d0901b402c2c00d12103544291201080320200400d101c1f900c0750392000d030719142884101d0f05442286c00c0400010802e101a00000e981516070107100c1c04c0031110000c5580301080e0320300301081c0030007420f40807411b0b0421007a044407075800c284244801e0881803c024014500c40103c90600000340c41c010819 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 699509181 1250 699507931 699507967
    0x105011421060402120703050709052d0105040c0306050306090d02010f0c0e060d020c030c060402010f0e010807140f210f0c0a260106021b0406061704060908 69
    0x19040754090032a2005103428a5403519503141d024255001c0340002d00142000781114002000355011503410503907030380c0c1e80343c500280c41c1c004600302d50300c4005020003000880300c9550545e561040042c4042050304204524400500c98544240d446039414141903000f40c0c007450203400d0160a80c2c495142425030296102c100108850056103000210071403164140304510b80c000e40d03a5500d04041c0020020400742c0e80004090760180c5d5420021031842400c100014400c1c6000500903005505e8140005400b110226003420b0a100c7e043c519194140e9100741280e901503404c0c20041d243d22544403910304030f401440340c1d2860003034000900050307d81b240103600c414004000d00480702d540d941040150318510035078414004420031302103003010394020440c5070412140040500c10f40d800e8103c040982d40c00a034810360168015203072414001b00c080103800c14444050702c080c001c8500c0c20b1030041030002c003144c000a00900c034001103010000c04d5040701005a030002a49030f00c403c414110155811 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 699510431 1250 699509181 699509219
    0x1120e030c100b1005071502130905010807061407030927151208070809040213030203011a10030e070f06020c090a06030c0b0d0212070504090c030203040b070c0c0305010501 76
    0x4402c112100c0c09003072050103001080d080203000c20b1a208640301c0183c0c0c1c180c000f4035003141c0007a001408585225100d00c050115003802d2110001c07598545030900b01203c0040e0002141c0303800204060001942002138200c042c440154100d9030384010b070030300300c1d0041c1081e0001180704140d20405054980715050022628040c0d803810130010f540008009550340062043c1003284a070051040c020030706945c05800d940b409991050b1401a0b2580060100d9101c12410b6280a44214040c415402d09201c2c3c000007016589095410070607080028144d0a85090b41d90105901c81e61120850401409584000e04100d0140c4412a460b09806074440d586580e40d94080c022580001780c000c041c900400c0d080720b401c410442c2c100c1d8241884151191b000c1d51031941c00c80d4003000316498112210308400d2040d1703070581c1d640b0345840c00d1581542c04c1e1100b80320151300f018018024000481d4072222116007060311402c19485030009450321009800d00c0e607101811551906000040300e08603070707071412045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 699511681 1250 699510431 699510433
    0x3200706020609070905040f03260a060f0605030f0115021e030903010c140d050a0b030a0501060e0a020f03060d030c020a1e051f0309020f030a0c1e150e01120e030c 72
    0x402d48401088045900c116400740070140c20238040000b003030050b1560640c10000d60f0900030200c0d03040001002e20101500e501d5041d56481000308003141b4220a03030b01c050410391500d80d145041042c0095552041030045060040d0b505000aa51500800c003a8640e41c80c4004000003100040c82c90380c7d140d03003204506078007950900c40c01e10701c418450007962801190040a040c1015100b00c415001083d00906007406261b41e04002ca0240e58100010480584030320b002041e801c2c1001621030749100054090b00b2658014400341000715000415294401e03000e03a140341c4240310300d04044410190350b0b81c000c4c0d080303000c1038000306507296200d2008a145c4003841a24910580c4d82050103403013104881c0240ea2501c1c645d11004116102c2d80040c0c3d41d0b030780000c0035240d0b580190070000e41003e000c1002121700c448000000c0140b00351807400c24840d4607074201204007061500010b200c04060898014040104001902c041e9a000b40030101210700000420800754080850960b0748ad0b01081324403403d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 699512931 1250 699511681 699511693
    0x20d0501050d050325150507020706090f050105071106040b0c0d140d0504020f090a06080708030a0801052407030c0b0a0b150d0608030f0403030f050f040303200706020609 75
    0x1d00d0400040482c04998003038025441c02c040345d1049180d4008801056200341d450301190700116801c080d054140c21842d0301e0005550812400107440c01d0300b25806032040c403a2084003080103503403144100044650030700b00903540b800030385881007007240003421456000e03d01280210b400048078010b019095800c038200c80d0030441107141554152008400d41010110070800f01c0e000c01a02e401c456080391010b011b21110b40184400101d0300030f02100c00b21801c80c1e544030b0411003c601008650f0081074904c0c055464940f1160008040034014040c00d4005c01d21500000300703d5031401031054502503800c014503250344031460014103600e1040c0050ba001014179002c624480d01511600c2202174004003500ea0340207850201480d207070000e4403140e415a685880c00907441e0010f000410840c140009895a618198540074181e080c00d1420501002410b03c650075058240e40304407000d590301810101c103140c0f654007003042c1306030f00500c0d941d405001310100001c50580008005000340e407000309580b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 699514181 1250 699512931 699512939
    0x2060708010e190e010c020102030603070b1e0901021204090209090a1415030c19030b0c071e0c5405221a16050a030e01150306020d0501 60
    0x3030814400c1c05900000d8840c100410a981a00ea400103100340041c2804075240341015140c80c21241001c0424025035000000c000491405000310030240080341d02d103d00b485c00c01105082604019003800654400014040c0d000380e00030081024042034030b02820341d0f50341d21001c001002e5001901041e0090390301304003040082e8454010b0100b01c104d4010001c80301c2d0350740e1207116405c00e190301405425002c4d070711411010b902c81091000c5008108182c5c03090313035403540c074003224003c600074031070f2180940a01c01d00340020310340780c01190721080d0110302801074036041c2420030000345203600c002580c540b01c444808401d0841d4484404420000030984214501c0e00c44d0700a0b00c03130300e100e580340d0001400300284000180c15840036801ca41322003603005650031603004206070b2415154065550704401400c280d51030000c0441540d0110f200840808000d90210001e0101e0140031480307400d140c1c4503c0009008002580320070042c20744170003500a410b17030702d04200c03000b541319101d030460a9080100100d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 699515431 1250 699514181 699514187
    0x71701180f020a0c0f0c050621070804030909051035190b180303040812100f030308040311061906050f0a030813030503070602031909050c060f1315020607 68
    0xf40c0300100350703110382510072860f80e1401c58820b815842240c1200f51080e0114040e01c03140d001d009051311003030b40e070f030701c444007400051841280040541c41000084010840000d51205c0b101d0100c4210180116040d00c1d01c20300c6c1c69180529030840511f20b41f540c1402034940b0f000c0c44845400860122002841340b942105a03a25205c00c1a02070501d080481c8d24840010190388180e50b02c14003000c05040d13401600c2001b030f4255441664152400c800100d80c030120400c0a4403070300c0d006803d14074800707105442c0284060710309840784000303400e10950600240c1492700504811340c5031a008025202140b13860244070020b50041c4004019a500c1c215011599040181d1070076008c84000b841c1043c514a03582e6910740c035030302103803c0b040d4103414100c0c00000118100090245c0c05d1003041d015840780381c01010901e0302d40348008481102d60400c0e040390046030010601144082090b910540d44142194005890344901d208248035a0389030000040c0f030b01c0c0382c125501e18040e010303420340d55142c40b025012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 699516681 1250 699515431 699515437
    0x18060411180c041e080a0506060a061e0809011b0f11031206100c0f200d2d0515010f081c1b2003010605030d1205071701180f02 56
    0xb1140700442004107000240d150031640c402224524040c020042d00c612041d414080c4c801c03401c60b001d5002c0410710000346041654180034040c43d00d09110880301c80607141c0781a9038005225018010070b180800c2a4140c00c2d000050320121090302401744502c5a034008003407800c48415100001e00740b030035045680001208541e0030400003540c0d0f24081d1075242c100400d03583c00d4038000c011300100c640410001a0710340f80c0d2070000c501500200341003039582002282c845000d0b0154074400d0b141c0790714460004040454030314003528240b01d040100c0c0700006240e01089801040980641314691000c1c10b0110450940b6060b6071043e0f21044445c0d60700d464840d81c076810007541303e800184c2c43c1c12030030f50184106070801440021543e8a0a100c056845035204544142066400391404c05101c11303407410240a0a401094154024020081790520007090302807203004407031015031164089691f0b58826604000d00841000e5021041c0d40d5644a0748103c0204071545c2e0700f0141401348800d2411030a00c01c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 699517931 1250 699516681 699516691
    0x60902041a0102010513020d021e090a0e190f12052205040e011b23220503061005150d1122060e01050715020d020a030b030a08121806041118 62
    0x4070202c02c0d148c60b420404100c2da20208004200004441106940c0d0b0b03020b000b9004e040401070000303111410310215401d104a4100300034245081561890014002c294180c140b60340104100b0007840e4142c00485503841030a0440c01c0e2020410882000201c0c011582000c5a02c125070070440c0300952540c0d14240c0f0307001903c0641e000007000ca1030401d10300910200039200c030119210300035003842e955107009a0300401c425014072203a042c61b400201454041200180404500521480c9486c005203c401045400b5541c0075a60b00450b4541c1f0061101c00c6c0c0d10940301068040c0108a0280e10705055a00711010326429004154031540d010056140c0d0b01d01521035569646002084c80e6006580c3c80d448500c0440b0300d4507808410b80d560305001c4c8082d000e104150036015a80702c000c042c008043d0740501c06c45500c81c1e0014070654002456803c11101d10b100381e5020203200303688035584034085202d04d428004042c0505801c20003003242d20341564480c024110307003a00d103191b4419400d5600a01c1162 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 699519181 1250 699517931 699517939
    0x5040504020607080a030915060302100201090809011d0306090d0813020f01030507110a0506010f0608060303041e0b03070e0a090b011d3d050705030412060902041a010201051302 78
    0x410f10101d251040203101c00300080c2030114205205640b5402900f10203462002440d59554080c0118036003080c5900811025100a21420003141c4400359184074180049040c80070307090b0058580b2403900401e154050005082e921145800c101c02515000f2080302d40b000030703883c0c5001030b030000c06c0907910b400a04e4014145481d400c40380b034010340c01000081c1030702041c400c241816503e100400c0115078000340c8140040e22095145c032003d0003006040703420901c2480001c43c204500c680f00041520101e0f491406404440781c2e0f01d54485442c0042c0e07800070340951100100b0041e80617005921a14501801c0c2c40c080105035a801d5a10201c2e4815002c041c0081c06003900340c0ca042041c2503442c06810f400810307025100742024804440c0943c5103641c1d400002d4a60440d03401a00001d481994981c4a400e0041c1340c2407146c1e49480d1640710f10700070901010a01c41c01601030154030f902c0b01240310350240040210312204515100f00985441003030b40150308101c009031400006211841209074064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 699520431 1250 699519181 699519187
    0x6040201030b04020d0203130b06041413241b03020a080415020c0f010f0e0613080315120309090709140616021801091401240c12050c07050405040206 66
    0x540114041d00b49114465403094082c065510502c040340700450288c3c0b5200b4110200420300e107014120a00018082480760f8648881c85000c4a0780d01c40d1154080301c8526001006207281c5001c3d440c0d4503501c6401049008200600000008954022018126807613458911815a008101c0c140d104404100001030110f101040014070000b10044804c0c010034000342c10900c100e040c4501d4003d0b001444151a91600d450100901c4203200743e41056014034080d00c410326003080901c0180c0d4014000610090740040043d8100d03400d26400510b00400400d0306208000c1240066075a0b0003410040b40314190703820204a507a401a1401070444075100000103000b4444420460190050303070100d5014602c40003c0c2c0d00607510300390032030ba0614001144119030750410b032540048030b100030b07908101e56420b500180040e61803a1b0814041801e206140c001414030390701c0460b030b50104841c00414804402503054012504100541100c00d000e0b0304444c6130a942c2c2d4100025a0806d94010b50049020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 699521681 1250 699520431 699520433
    0x1a0c0a090b0913150314211305030a030f020d18050d02060d0212010305072310030b030709020301090b04110f0304030513080c01080a0c09141809010b0a170604 70
    0x7601c8502c4005124090183e8400c0140c1c00350359400c100752106a13440c400c280200001c014841492680000041900e0050640c6600b21060403014902d00494003081290325424448040c80141c030b4040c06403543c0d48030528025280c4600204590050b00440c140601d030705200300e4804c0b003a060420035050103a8900024001c14061110003680c101c01c00300b040c940342c111140004d007a070041d88074145d11650b2640c103280e410120b0a81081401200203903400254030440d011504200f00200c0c2c0021401c00072039020b50003811202003842d0140a9040d00150310b02c0240d02840c121802e04001f07102c0c400da44400c0008555064500d011182d009100440c10000302c0d6000d940e1003442414000d00d0045860400220f038100da41c0081065030141c8400501560b00004050300500b00200c1401030000d2414060010182c50040418408407062014140e5403500281c01100c0740c2540c03940d40501f45140c110f406010f0522000e80036a5800c03c0c0010344000301d4800006188410018015584403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 699522931 1250 699521681 699521699
    0x31803080f0703020c01022205060f09010509040f090609140f0601150e0616060f092102121303020a0b0c06241f0f0801080a0305071e1a0c0a09 63
    0x41d045004044d42444140840c2070244001c26a01500601d003e041c0f408100d00d185142e039950300158040d040c1808901181031082e4181c1e19401d000342000b031345624240e0007040040c101ca00100d5800303030510300da001c1400341aa03c200d0300103002d1004140700500c454065586c3d001603075940f64840d070000d4010000404111500100480c0c0c925003c419001400c0c0000d03070b0742d0000b2451847e2030404003900720402c03c01b48904040821590000c1c0240c02c555122031419214441c0c403a03201e00a0380a581d0800c1e0720034045016002c22200d4040d0300d0791200401400d402180b400200d01441400f0404543e102144094854144840c40204515a12120341d14180741d642c50000501003200c0403002a155200c4401910b40485c140310039400701c0d9519030062071245250418020300c941400184034502d0082005a8034a8150411a0b03480384c00d0b00c0c01900c048483c885140c5003d0703000e44440d080203c5150f002c5000340c1c04e0329240d03038070b62101015074000d44142d02900000c54100e41d800c0000c601 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 699524181 1250 699522931 699522961
    0xd1721130227040b070810050904120233060a031101202a0405011505090105090a090b120d0207030f0312050a020d0e1b0405060a03140106050103180308 67
    0x454150180c0000c06844072801060b4010b8804440341031402c2c042002155000d01d0142d40883c00c02d01191000e07242174003040d00f416018102400c2c1c0c280501c0703480d00d458000c0000950310440d189402c800b007480000c25021001c010f0a141210024040204030b40c1e02d8503498034800d494021741c80c03c558a80d80001940da540c89007502410000c900b2850042d00501070002e64048074040c4000c9052080814a18201440c01c100c201d10441c6003a005004002c1c64030310303032941c4000a060060390340300c0e0303c0010b131a075002c0c100801d5440011a60701080c01c500a42000c048100f00352400d401d078465181740c498032a0112400e140060740081d8080000c25164a0344a85e2140a81132583c48880030140c1070381601ca0442d5444140c1e41c0004006045895038851103444608003c081d00c40d541c42e50480c1500b441c01040300380d10850310740b404100e96035078800c9204025a0702542c2003415940b4220b080d80a07045030b00c92140420301d0720400022680c0703a01500f819555041d5512001d07681c803968820100340d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 699525431 1250 699524181 699524209
    0x30f0c09030f190b220219080106120c0b0703120f02120f06010f0203042402010e19060f18060507020c060403050106031b1505090d17211302 62
    0x40300e016100360480b0410700101c41d18540401e034680f0404540d0421607044a0b025220780c81322110f204204050b180703220900f0382c40c41e904807040c1d40c9480194000c061800041d4001002551810000068440f006001c1c2080c5521414884950594440744899070340160500500420504181c15003401181e80c003180c1c0c40c2881d80801814001d60310080418503108070303811070703011902205002e070940c1c10000404684445100551403d406c14030b01d0311040300342e04050420840b120700240c1c4c001e4003e401c6640002d24000845408039203c4040003075070209a82c003034030010b144c181813407040303001c82c06a0111581b0b50b00714182d01c600246c2e1400b00034400241780e83d0450207045e503201100c0e1754900091000b18042c0300003040711411400d10518100d010550b828200303ea08604025040740780a880c004200d090910988981c07034080806c0e600c440e0000010201000e4030028241070300c0110140c00142511740c0d03e10f954050f02035124411070701c143e91000201c010054008010701d8586040c02c501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 699526681 1250 699525431 699525433
    0x40609030306030c06030f0b040204060e1201180506010617010522060b04081605090702060117070302040f0204090f06080615040902031c080a090b04080c03130611070506030f0c0903 80
    0x100d03a00d854040c00f104c05a08148000307a00c4071302e6903808102e00e0042c0d1801d19030898085140030301e0311101600e1401109591401450a2180d0040074402948910f203074580c4502c0801142145141441d11000c0900820000c00c4401c0d11810700b8400c84000c080c1070b03840c050002c0411a12408804200301c110380c03030440d5420b40391107010074001d0140015000400c40b0030000d280404491030401c801c0c112540000d4002c0c4100c908110007554001080307411a100340300c441484007004800c1508280703490b00065007141c00c1c50391b481c0240f12503a0080080741c94940c0204042d1042c02444000c2d40d030039100321036403507010b44085070800d0308076120420700000c01440000c805109030702090420307480c0c200c40200103ca00c031007409502e4000007035550090f0411010000d0982603a1400420240a0005404410040b80b005000f040400496a101401c9040d2040311540c40034020880303141c402000707005018100e400200e41c103048041e00d025081d8001d0320400e903aa074800c0e00c0340e1f5800c1320300900d80c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 699527931 1250 699526681 699526691
    0x3030e030912100b1503011208040e0c03160c02090a0b24040510080f0f0403052101030c06111005151f031404080715060f08150106080601080406090303 67
    0x6590b0b00c246803400414102000761140051200942d01212010310b0031a002e180c2c90225208903429120450341510300c9845900c01540c09030074086500e01880c0c02c01c07421629510284480612020041c43c400c00001c402264426410701c0121002c81c05050000c1d007146103900400d020b02c6075038000d0000b051003d05091224030301039031070920b0160704004501203003200160a2010303050400c80009041d002e8245091181030544400740340f80001090124980c02600c0403604042c41340302143c10712500c0840c10203100f4a19043d11850032402c0c170044400c80e800820001c1d42034002c5a06400702e1030b0038400346c11148851107d401c05000c4c000d040c3c0c0012650700c0510300603a0b40750800304880c65a80e0000c50645809010040c00b21522804d403240000325107410407001514030412644180c2e8404101414407801d40d9013400034040607000700b50444080394012588280001302c4040c0d125400010000d642d0362030006030340c411000e441150000e52001d001030040b441c41e402c1140c0462003440c000403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 699529181 1250 699527931 699527947
    0x1707032d0e3f1804060f03060e0105010501030e03090904020a080a03230708040b1b100c140a020c1c080a0c022d131b1e030903080403030e03 62
    0x4140b1591000d020140ca494402845000c451901d928000403292202d42d040c006165080074094014a00010b00c0b001a08081070600d03243c60304014002c1000000c0402425140d1402c034019200011142c10f45606c0c140002442d0742c03203400303000b8010700e0060140d844c2140803010b01000710310042041c3c0e0407402d0a18001010b080411821404030300940e034507141581449002d403102800310302c000d0801d650910948000c511100100e5080f6004804465941c5000c450442c0c00d0308840c43d5400140d000e51254102e410785c0c10340112080c50407079900c0040001c564004a049030007000c2c6d0311001a80a10920b010ba814922046501780e12054803010794480b44c0c0d0384500700b550141d040180050711500c01d200031802c00c02c410140c10304400a490521190b40241000c1001074040040d110b22298a03c0600d0b501113903001949401c10301d448140c00140840c070141c0018641d640d68120032850b80507003400311b4440d2007141050703a403503994501d498640340c030b0071400380101001d50a0240003c10000c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 699530431 1250 699529181 699529183
    0x51309050d0206041b05010207151b05030306180108030904020a050c01020406020715020607020c060a030608070f03110d0803010b071406090a20010e120c0d031707032d0e 75
    0x1c25000c0456004001ca49090325042d190020352500c3c0507101c0840c41c0060106030380102e84c00c030644003054019151030740320704000c84012003000b4034110007000440e112000d019011005611444040ea420001c41d01110a0341c680802e0910440c1d400e600248131900807132919070028001c4040f18a002030034151080d82150881c0c1c480d611400150b40300030020085040210071407002245140040c141d14903241201079115165407492500c60000020200002406640b2040107040c140d01204c20383d6481d0000740c1300c5180940400d0340c0014001000510915051160140e5117502410721421a46170880041050b00040030403980d0215440c5180f032103030410000d0701e2085400000421001c40700f070500701d0994664600d290108254801c4076103070741e6046241c48265100954040403041c2d0340c402118240402c0622440c2d00c503000f07031f004900340340d07000790160110820812000e8581e25000d00a50461f107900b4618400841002c00d03088188004418041158070b400c2d5020800d465880191 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 699531681 1250 699530431 699530443
    0x6060a050f090603250f05010c0b04171908011a070317060d1205092128050313081b010e040513020406120501181e0302070e010b09040c080f0105130905 67
    0x685d05d00040c0d81c010428881c4000910000700002e0900e0204040705444150440300c00410181948699182001c0084440e10403512038503e07140c00c2450002c0c4019005202c101d00380301c1d0303c0d03205250000815001d1440c000319803425600d6242c540203001074440a03501c1703410040680d03a005072403044080201300740400f450720482e41e554545a4030004501040202011440d9400861514091080c242e80e00055070701007040c2020821700c2180c032000c030b041f075244c1c4c1d450a0042450001182d240c0741c800d440b400810a80c0c03007800039501c80840d20403101c20395240042440740001d025000c02d00441c10135610141e08480c40d1840c080034903200303130041820766520b80e100e041c1c3c80b019400d8540c00e00c0820303c01d00c05c000201c40060440341503191100141c9103000342c803412541c01140250810540204061002000050b01c0031810f5a550040d41000d070b00018642d500450400e051318001901c1a00c4607486401d6081544420740d08250500c10100034160061899940d41c40814011034420450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 699532931 1250 699531681 699531733
    0x303180315270804170c13090213021207110f0a03090612090209010b0306060c0607090f090b10030e1204030f060b09070c03030c0e1c0506060a050f090603 68
    0x85865440c0742d0054400e40c4403103040141160510ba480c41c0058280c204850455240364100b52100070710121041c28001107480080c1e000b48031340c404405a402c6a0004140c46000300c5441c94007a5018001e00e0980c0714294949400521382c03400142401c3c01410440300c0c4200c800d048418418598039400d10781000080f040c1d021942c0210104412036000c4030b00400b01c2d496400038407500b00035901040040c04180154030310b9080c0440040d9641d141c4106403041d4032601d00844581b410501006000e00f0010302501c254440101004103140d50980030b50140b4400241c150056070b0748416044000f010141c0c5069240d016079031044003138660440280000d0350082e00040ca810021b07152803808c451030009100d0181275000304100c60140c101c948200400d03018140426070442c0403204503101002d080d9080da1081012038241000e09110001c104213500c590202c40481e2204020804000c14603c1065030100010100d0307025402c14005d040e410210160032264038811000361506243c8042c11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 699534181 1250 699532931 699532973
    0xc03040303181b0806090a0b0f070c15050601020d030e060f060103021c0b03010c0809060a020708070f1a010504050c1b011503080a0f051e090a080f010c2703031803 72
    0x3401344a070002c103014098201010300000c141d0f20f0001da42d218440b01e00280804007105071040015000303800f640503021035960000391a4003452820f01030000134541a01c600d40144944060b0f000f91a001b03108403604203000b900148055681d460100c1d500200081c02e0358100340e002d012849070307810101003d00704120051404200c600c40c6406050031a074142c4041420041c0780c60074040306940c042646c640260310f810001d41d80360001e00700300105200e0400001c0500388031101c1d020502429850180c000c2c00342042d813000ba66610800c2109881c4162140c1280170740c208034003002007a04820090b608003250001054042400301da82c031310700803564416074002c03200040c0c925525034401d520841c600c96600b0064100059064046281c40020b40003407a0728200003000f0341c060784c45000346030080603203000700c50020715441c021601070843e0102d81c2d008103080340d0205441d0f000301c6044c0c0f43c0f46440c0398800302d103440c0f40d40c41c00c407003a400c40300c264803061101140100c0070800d50302640e82d190250755 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 699535431 1250 699534181 699534233
    0x180106020f06100e0606030406020c030403060218090403050406051b070806090f010501060504050d020301020d09061b1409040c090315091226091207060501080706080c0304030318 79
    0x1452075400d20200030300c080201c20072890140003580c4440200c542140c0d06443c000d0700c0741d4a601d0020000d1081c4601e424080c480481c0000802189030010409030080c5000210750780d03404d5043c1700b044201641e006012070824030052180341d2058000c0c0003070100242c802c0c420ba41d04415220f040044a801014858009030200004441c0403c0313109000c180c2c02d40200300d5581340c254000e20501603405018030900301207060308150344e02501910031141d0720032802c004080340d9107091002001540a64030304048100d0390320090354018440282c08444c200740c4c2c9894080b0020810004000740c80300d050071701c689548048082020141482900322844900042d2071220342024040340c0d00c038020340c804104c02081d6400c15004c0844082075000d1410410708400d48845605030b00b001700b442d17403141459902140e82000d00c00e690300164101c901070030940e44280d440707000884041a045510044400d0700f00080b40009100b0742c00b00c0c44800e0b00350350b0803001600350360f41e071410b880078000e4030030a522100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 699536681 1250 699535431 699535453
    0x121805060708040b011203030f15050102070f0308030a05090a0506010b090901050f060a2d030915050f01180207120302180307050a090506031213080105010509042018010602 76
    0x400c00e00da0048101c0c00d10902610b00b540e0b4071340e180041401418050f030300c50000801010f0003504580030841c9402005d006616090300003d1408007184117560051094100016054400c00401c1040e00e401c00c014910b182d542e446104040c1201400c414034500c41c0c40d9445020400030b1011a01070415841290381e0744500a0030000b5030362040e0032035441000f200305119450f0303132100129042255242007000e002d4081c4424200c8681c0b480e500a06c00100b46101380c5d01d0035a040e84802e0722144034002c1c5510540d25000c540007141e01c1100d10342c900c05900c00041c004da11801c0c000048440403201c3c09031400303042d552402d25200c0b0440304000840c2e000b041d0300401a0703c5585219070004190000c104035850030700000e0000c0e03032910403007401c05c0e031351030108407581c8003403040070b030610710100c0b0303280d40c0d0400c1800051206103140b05912055107414008591031520580b018061500309956803840c600085c0388a01440d55500c41c17980c030510131000840350740c0e42c45100c2402002d550b0050b0450142c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 699537931 1250 699536681 699536683
    0x6021b0d0203151e010f12021305010609060207080d02030406051b0a060203150409030806060d14040507030c0803032a0d060b0405121f1523100c0c050f01121805 71
    0x1001c44c0c0c44950302d2901d00184001e080080f4410200e40f00d100425041c1e07480b6001050008840d000000b54aa0900002048454104440e00210f400d164201e445030b50341c1d1050305444440a004400050b08100070030001c2d644104082c00b5400c0c40350582c20040c4440102d201c0c030704506120125400d0307802004000070042c11541d10b00e50b51fa0103076004c0c40080e0181d03800600783d88008143d0f900c112000b00b1440100c0103a42d210306070221f442ca040840d00d04050a0440d5584001c2c40110340144c0031038004510614084140c2e40542c581c0c0e001007890001501c544480a07401c07162101f921001840302c07061500240c00780030b004005c0303403400c4c0765035609103800e005d5944116150703064541c2c000b07941c1c07070740104501060f8062000300103000074440918035544494081d0903800010415850701a4003410307034110202c0400e981e02150146021803102909440c0c00d60360707041c0a0130000310440c040021f400c005008009400701490031500d000b02c80b1344c2c1c0c40211501104044540d0351124118020840c3c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 699539181 1250 699537931 699537961
    0xf0304060c060c0c0c09020f070602041202040b0d0c0303050708090d06090b09070b03040b04020a030b090c0f0f03030d05092107020f010512070e0612280606021b0d020315 75
    0x10f103490581d091200540710001002e555105e00140a40d00240c6944006480015201c003294824410b560301c60369012454100c0c80100f030246d1250b032a00130500481d28203400070124003903200110496031480d685050380c03580c00800b8180e900e00420481440d450741c81001009003141f08013000a02e00da100c1c104184ca040300240380c4802c60740701403010300240c04c1340c2d81501e80c8586e01114481ca00c1e940c0740f000c55640700b6907920041c42d080c0c00400740180910b001c102e1840c1510705545500308920003000700b0141002040f802c80d0150000c002c0c01810346440e0b0481a404800907080391202481207040c02c00d14402c1820100c50382901151220440c6801842c403580b62000b403030306a08001c0c46141c0c107032400c44041c04001c1404802c040d1582280c03150010b0b81d06208054030340c0741036454030301840300d0302e0782420344108145181d003246090184058440c45080d510342d40e0090000804019000c02102d003c400100d9008420948003001642c0c01c00503030000c0301c0e200c40c0094071f50800e0b00001d0700c014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 699540431 1250 699539181 699539201
    0x8070312060b1b0a05012903030f090409050a1203140108030f090108040501140c04050f12031b070302030303250c110423070305090c091e0601020f0304060c06 70
    0xa082810420907411000b0035603003009001500c01c2c003400c0c03a5041036407030701e020300030000e09070750074183c80d940304c0000c16106030003901e45806e0170440c11807218101500c922491114081c1d0860034000e410040c1050307030014007a14400c80c2100d2100041380c869030600f4000c140c0d00d50000351100c00e521111000421002e004105400055042c082094124030300ba0107103808060400140f01d00003018850250810443c61244503018423660400100806203903015000b00303401030884d40c107101c0c3d40d030038980708000c01c4511840145003005140300d001c603280300d410241f402d428401d0b10004400f59400b0b1000390300446001d5690f82c240c103c002c101c0181c28444607112000d2011a84802001c1810b200001c4600c04045034009446641d041c0701d1801810071400c40b81910341c03001c00308090150940d0040340148004002c0324141d1100c0d004214601000300c0c1c5070b200e14110b0b0340750042d442a1320744105400400500541d000c00000804191443c1c00c01da2040d000620941402414458940326400181d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 699541681 1250 699540431 699540467
    0xa0207060e03030f030c0d0e03070218040213020a050c010e010203070816050f09150a0e010206150d060c0507020603090105070905100f0c05162310080c07050c0d080703 74
    0x644a44001a03102e00600e0380e04546400c002001841b14100201105c1048903c54020003154410320400f640d2a0400d04c812401003960400701d8a80071402e4030000e05c901c4e8000d29000040041c4240138002e03400802803082800401e21113824400400e02a41e11810386403800181c507841c107240000d00410002d41032090002c880e4040b82400e5502c4001c44100d0401c19000355518184500400c11000101070004030321800440d81c805025800320140c1e140070380c240c1c21a502e5031148031031220322201072002a41d220000d400003c0000f100c640000b0014085418a60706003a00c6402043c1710398001c8440e0506030b551141001a03d5410482c1300c00a800266000003000e6102d000240c0000d070182c0e031240074410b000f4007001c1040800c01c0b041030100c0805000080060b901c4900c0c0c0780d0044412100040041c14144291082c146140901e004843d40d50b507000160320b401a80d001145d0140003360360500424000800e987c84000111008030305c1410341070741c0d89503a070400400340d10f0b03080d00450300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 699542931 1250 699541681 699541697
    0x30620040303020d032309010c030509070503100e21280c02040905100e0c010e060a020c100c20030105070903031d0a0f0602031c090b0f090109170a020706 68
    0x300c0c0e80040c1c40c10359544c0a09001682c0d10151025008007001451008000000300303040285064042d040b80c4103610306510b092000c0e49800d12941c0c1ca4103041e0003120703003562181803003010841d5107070032800700c900d8200150707242510f11260018030602110030340b232500440003c10300d003214040200c000c0d042031820703620101c141070301c0c0c4001c0100315007250281c86030740c4982e510014040d00b4440050020f00f075003000c0080c1c01c020141c1da40c880071400342c154003184020642c48030301d00b0003104940b0b0700c8056901409908205904201d044406070030a02d0030461742c400d00e03000160300300403164449003000301102070200c803080c2010b007500d00040540d4204884950204002900320031440d0003d1400450303c0e4101c4004400700e050310310325038005100810000e2001031426004801441403000204c62007031945102c46100c000e440221400030701640100300020868100f0080c03c07500085031a0020a500303001d500c031182c440308030313032600c0040c0c50700010601d040da40c0400c01b1400a0200e4181042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 699544181 1250 699542931 699542933
    0x5030f07061707110a110414101a0408070803040905010b07020f0405060d1a040219082a060a02010c09050301140103110a050a030b0402030d0509220e01060306200403 73
    0x1d051011540b1100c005039100100d42e0141c0280d0084109418000c11030384280d40c2c5013485001901c8281c0e20b03601407032600c040e490b079410f00c08403203d211314004031034080b01510741040020640000c040c401c0c060b44050202081c5008180000701c010f00e40d0900079a1140d082c400b14408403081a803050300281e00c1045031000680300d640211340420b05c120750000f402d51341d46001c00c0d441e080341040100081f180e40d00710b14290704421100ad000342d000707603183c2001007a41d070032000220245028510041e070203c8003c0c0c1441a50764208654603110158291080c1e04010205031141c00c0107000b00d025035101c40c4c01034040c940c000032010042c4401c0b8024400030520307071000c946a810600025158144601c0e24070b809c0e8542c107a0100c02400050002084039580303050441040b20300361001ca10900607180c2d40a4a40c3c40380050302c01d5010000d190043c42c85106049511181001d0f045560a907154440185520750030b104a03c0214001c280c0807a90401400c0c030042c16600c0045108a42401403000380 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 699545431 1250 699544181 699544187
    0x3090b0c0a0311010f0603140d021f1a040f0212310816150e03070308010e0604060e0c07060608010203101811040b1b060601020c010c0c09050702030405030f0706 71
    0xaa031a54150074219031001c40100058054480030300c0c1801906e0074620004200454180001d54400c50380c0c0030303510001001581240c8030001e51204681c4402440bd440d4920107160b48460035008000f8482d03009040b26102040c241e4540e09034030800b03182d000c100c0305c0340b08441801042e032008880380c171440507009180e940030304050302d00040100700040c51100340030400d0752401c440015003002c401030100c22540c070b00030f80c0c0d40080c51180300c030301400c0c464150445c210000a948007a5032546414469030b0034400e003415100002090580d0058a43c400028080c3d81c0804081c013500c0c540071455551060740c240f00302520a554450503080c3e10410410841039055020b41090350248024a46110301814180c0082d20344c5290000202d0400180041e00c4103102004042050700c0c180c001101ca12101c0c40d2540307c0a0495001d409a003040c3c00654082d8450241c0700c41c000d01c00e0100300c5510f602d543c0324000301d07035003103030300c2000760b400000d092000e4a03040100c10904c0080c80000c3c104607003094001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 699546681 1250 699545431 699545443
    0x60705040605090d020d08070213051003240507020705012006070e120105090c1f140904020c010e0606120601080706050a0504050d0c03110301060635010603020703090b0c 75
    0x10410102140c10405640c41c40096481180c0081c8500d04003022400c050707c81c1d50190004a100e03046040642071081118054a80703d994900520040304c0e10351f494943e01800e11980d003007035110448411918490103032240030b004061035030051085a041c00009045158046002505002c0c54031a9140070310000500303c2e881601031810780714421044010905030040e4920203441c9500301003c01106800008080041080480322203503c0c083c5101303100040a1215444000148540480d05261840600404040030042c20040c90403041d2250b450844940c84552003094100d5000d22038103291400c90600703036001001c0a030005500d04444113a40e1030b5984140014801c000c40c2c4403001c40d000320161002071602800141e131540881c0382130384c40920240002c4807014856010107996042c144200420780f4040d4507142006030a5001441c40c514000aa0260003d0f40b0340c9000201e112030070045008101680b8090b03100d500f40e00d4058a660300b00d42060500c80401e01c5041500e080003c0c0c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 699547931 1250 699546681 699546689
    0x6050d0804120503090306040302101104030f12050904060b0304110405010501020a120309120c0309080102030720030403020607150509011a01050c25060230031008060f040b060306070504 82
    0x41c0d86002e038041c0c42d00600394040c407405c55500d402480104024550081001c01c48034a188504106c03590140310940c0c054061400040c241303c022490500007d0446460f00b01c249110b81052814541408005010303500550000303540b0b000040180310420070248607403a803550003110180829810940001d50326001c610014040040b030710300994800303003e82d22841c00c861f00300b03114548042d014100a003220a46500c1200050070307112000503120b50620a03680513034500e603a900c0b41400522041d03541c4a401c80c580c00300b01d010401c000401603860710010045a0b2007044007030640e81c4031140c2c040131180020500c2e181079042401d10b0600b00109501400d030302d542400c055032a44d84030303c400340c50030102d00c0d03110b628a4810803070501c800100b076006d40e080303580d15822a81ca1454205119004060000c9800c0f600c2d07601c0c0b0703105a1082039420255601006440390700440d00e54a4100c40d00d0302e041510310070b642904d0071040c4010300104061096004a00b500103115a04210360000c140e803103280310f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 699549181 1250 699547931 699547949
    0x20c041b140708120910290102010204080102071209080d08061002030d1d101406060c10091b08060f0426030a0219111c0314090a0606050d0804 63
    0x141079200e00c00d000141c0c2e5003250031168054680302801c4410151400c140d84c1c81160340f04401c03c514002d41c1501481c2d034291000820f9883c8541c01601c0004e10181c92641617065540034071011481a000340f020701015406805a2800c1c4020910301800031b40c00c98100c020250840c2c45892800c07904020026004841034402c0150319944040407070440c06a044840456400e0040c0c40401e840310444603240d2941c0d4100340d4817a40048086081190303803600501c00045c4c0001c000960074500500948402d00c0d01e6410341d5600c007144854201124101d0f8000c03609448401291855005000044800740030003200034441410b1141d60001c84000c0240024110005043c005102c200341840010711200d180c003809869050000010000e134000041c5010b9604a861403144418824100e032100c000c0d40401074800380e141c8004112050b42d61103071050606880d080100380c1d4030100d9180a00c5036a510002d0720010300249022819030b01c4a0b844584030701ca0207803080f00402c1c410310483c0c003101d412030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 699550431 1250 699549181 699549197
    0x30809040605060a020105090d030b090c070201090e01122001020a02040e0708010204031518020a06050c011b0509010809070506160c0510050a0219080415090906090b01020c041b 78
    0x94005005441c160304200d4110341c01290703940865805400c018003d11035102515411a400c9004804403082445000e0b840400b00d804181d14000000c001c010300b41c018074181c40c215888180f252003640c4281e008440b00668060200305025103120440c0552001d0300100c4913189581000039562810343c00084d10907550f90380035038400c420800c040350090500100964071039599041c62100382c049400c28180460509400e414510003000c03110140581c000c2c0a040194100302c41101c083c0c1010300224025941c1d500d8003500140c203041944907521555440036500d40000000404910002d0305160f001d9000c00b4040c40035642e00c0058600070368403406001e400605134104809000504e910850f0008410040d14000aa2020040a00d070a01e5002c844071b48289042d00e03560515000e8000d00002000c1c002030140b10160f443c0f0040e050303080d00c0c0a54440303803944604001ca0b05140c2c090442c547c1d444040e007100d940c051001007050310084a00304480d00c4a110510a0308011103240d0b000c00c4105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 699551681 1250 699550431 699550447
    0xa110f090d0b0a02040603140f07052d0a030e1c050708040b0d02071a0403020a0809010e0a0602061602070f0302040905070e160e030f1c0507080d02090103110c070308 73
    0xc0301c009032401d411a0780c00c502e5041068031500254000e00131500028100903110315101a00f0803458010000184a00c01c40c3d510008125907540020803424404ca10726064034510070f03403c40401e502c4029810f642c55450200c00c2002d000c6981d071142040da15044038070300c1201641098040b551000131410b21564803255854414528880c0b6002840d50300c0d00450071107036055440e8050000e4078400c80b500d80d5401c00201030b081300c070780c011207000700180e010181040024050f00702403c5c9000040c1000724131108104002216049960031440050b40640104411318008121051500410340090310280e030802c80c03d06050300c400d0101900803a1240c07911001c004041103080000d1900c04503180031820403100c1c1070340e05000e0081100018041c0c400710b40301440c0216107041050f000d5001011400802400d0039150101d0b01500700500c0f60500c4607d0215a03e82c0050109100428005980e0244880058220750f200914821010300900081701c04400000715141503e4019420315192a10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 699552931 1250 699551681 699551689
    0xf040b060a030c090504030f021605060918070f02070614030c1e0c0f0706080c09043617040303050d050901020d0606020d030606030b0303040608041a1305060a110f09 73
    0x1082d03100506240c0700c2000000c88401a60000d4051440b9907a13103082e2840a200803130351013200f0b946c001301907a80c8200c100320303178546007005204000025201444c90640c24002400111040310020042611300c01321080c0075505101c50405000035003484a6210b076904600009804010441205004000780004000034009120403c0d01801924583e440c1d014040d0203444080c00c0b50944440d1041707403c00b090050041c0e11051044044c010349038101106041084003800c00c0c0004000400491130600000b0038125881d000b01d0340500100d10f103018186c0ca0848809203142e01001c0040c0400c0c0300030f1001036409000c1754a035210701c440105194440d8186c541c020301c6403160080c50207240490008220342c01280901c111281d9031001c0100301e55840042c1c094410700d400d040d038560420081485568016029990803500800e81c0d00d909a001b481d822112050695040d41921201d041c114100300c010046d43d548142414014003681c604907a040304280a00103814003ca040070a4030415511 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 699554181 1250 699552931 699552949
    0xc0d080403061e0606020312040f031806090806060d0f080a1701060807020c040b011b11060403050c1c052d010501030804090605030c0a050402090109120b0117060f040b06 75
    0x341080040000010094980f40142d001000000141e13080110000d1400e002000341c5a079004d10705c004607020703920350b900c2450036142c00e0001c4040c4400e5820344070645c0305000c041d1000e0070301900c1d4402d10364241200103207404002859588200c0300a0644170004500d510844200c030f41c042d08a60301d4108000d015036900141c0030040904507442c0c000081e0306503100441c1b03030003000e00380c0944801c04500810300080e46c018440a0303011501100c0381c401c0304040d441c0c940d0b0303c1d5070081d61368015850032000001c00d954401d50003a00c07241d2000c81310250340c0c600320501517510b03481d048000101c00d143c0e0340c80c107031520900308406190600401c02a02151103400d80007040f41901802001340c0e40e12898481c0c0141c001e4000d018010707181200c04215424005444031040700010580b0750094a84800c00000c1d601c40f2207158100b2280c5500014401c1c3c03001540344001d44109a0421103605000d1030304d01c9480c6140385158141d1040c004c0c0040d806e1300c0000c140d049a009501215150b84d0750001c640001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 699555431 1250 699554181 699554183
    0x106141c06241509030210030b090c252f04020304050607020d020a080d020a1b080d0b06040b18040b190f05031f0507090506030403020102070b0109020c0c0d080403 72
    0xe05040b1000582d00480b440341c0c2003000941076504525880d159003103140a6030351046004204155020320152030900481c0e48100c003586030200e0100513a001081c2d01ea842610618100340010421050b14643c01040403611160041c0380c80d43c9902d43c0d11a604014081c0c0041d2422440640143c1510003425030003250782d08000e001035580e420181f80154ad03908044175544014083d40c0c04002d1048c0c40410311603035a1b90082800350a0410514031000294403005070501130080400c050b90090a0344d00c065a28140101e15054540079481d40307280c103a408071181a407007524204420701445d0100c0c07054800b00b0801860102014464201040c002c105117001541c1c0020103520000c0e03030603820038001c0143c81d080348411704d040d0380c0d440915170b035070805544030218a1500b01c101241c005260344082c0e84910070345040c100582ea01c90209005a0090b03409900607500004c61105124000e1611030040001e440c00710729081c00100d8031511100d580d490303c0d124500d508040400e200c041c10130390313000e9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 699556681 1250 699555431 699555443
    0x90c03060f06050d1b050702011d03071508090c01120e01090204020f04090b04020702090403080c071506171219030b030312091227010201021209010f0e0106141c 71
    0x10503100d102c00b80941c1c02c04500a88903d0410f0103030ba00c0c400c00c600c001c0c1c00400072519840c0c10700105074015900d0400f00e18440e402001a1242c100861b94208040002008040c2c0d00140311654000010240240241411032540c0a140381200030f036404800b020040182883c00126007051b02040d5014000c01200130b0750050002c2521492840c203d001441112240345080020000302804d0005a0240b208040e500c008a0000603020074010411517038060451968540743c80d09643d95010b044502824008a090342d42c0d001340710700266004418003410b100c0e0010000b03004000c40a1303071030b80304441d103070b00700100901c00c208030b02d900a0304002124440282602d4407808004003441d5031480031104195548a07100701c43d803400c50740ca82207171050040015005600e41614450346141440540d1050441d9420000f1740000c50520610602409500700045455000c140030b081c10342c0c40c0918022042e91401e1400c01018510f118156080141911290303100c0001200144010004010140032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 699557931 1250 699556681 699556709
    0x80a2a050c0a12110703020f12030d020f07060c051204060c14180301051f060309080f0307030b012304090b22020904140103110f12011d100c09090c0306 67
    0x200a140d404800c5203c0880d41d03801034071800e5031442591100c0b54800030350404407841080c0090700744440b00081020000781100e1030540081c0080c03080341d0003689034080500022641030104500f13070282d2040100145032440c1881c400740c03090906210301030002040d9682c0c43c0c80c000b91a84c01003040d14a4140180341060301c1d9400441c924101000032028284a075203424002002206000d1040404028110002280c242801400d900030160381c10107076a212003c0c0100c0082d403405800840c40341016036400700300e002020001625010490501c03120400c510f80181503210743d00c8040d0350444180d5800807888102420100301e0528491454810401c00d43c0d1140c3c02d100708640060104850503182000030984001c102c500103002800001c10016248141d8a594a840100059220300041000d405007001c0000075007100c0050800e601038408a110001d00340505020703001e030b0700040f0344050140480703540d001001c1100030b001d4600800c0d41c072101426100d100364080400f0302566041c003030b2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 699559181 1250 699557931 699557933
    0x2041107050102030a2406110a02040e010b0103110a05070f2118060215060103051819061109010f0c06060305060c032202012a051c080a2a050c0a 64
    0x4007030740c411030302841780500300320383c0d05000100205080d0f00b80d0390006010341401d040500841d030340200c1c0031040c0d10030700c00d0b00381d25009666075210b148410001c5c4c00000980d103810318005015241100300b07824440000f030001d000706540003001c4410701036000d80a5428403805247c44c0390021182c52101c2043c06242400e00d406940101402d80141c001140d1040303400d0b0768103030403640c50040e00d000701c1e403030405d601c00300b121035000782c108a070007d4694030741c03640c46409010014070f80040701d00f0080c03080402140c040306001991203105152820390f11703814501405000064060400d0400010410035018009003e01c9002d5000d64099a40942070769098140703c2144525608141c640c0194100e0004000750411b122a10101900d0b40c1a150503012542007071103000c502d032182002c4048004c011b000c05000030010700c200c0401d010103010070380328201088002406403000a00c4290068640300300f407080321418031040700c502821122480d94200e0200d404441a02500c41545124400c0c130981740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 699560431 1250 699559181 699559183
    0xb030a0618020312030c0f0306031c02070609050103060b0306010807020a0501050703060311040504032102160501060e010512070519090e0a021201200f161103061b03060d0204110705 80
    0xc8018002c50031284c03071402d81020422648401c0e035960880b2941000074150561080026642c040d80090035501c84d020903060a128402002c4104801038000800a002039a00700d401170010300000c0c602003096504055400d41940b101406841c14400c1030000201110320801c000301d1000e41c004000d00250501070300c041c001e41054003007141d10000003141614181023910cd103a100340e8055450504c03d80d6000c940301c0b100120369607007440641d0204011011520119842c103211813181d000047d64524006040010a2060700f01074826148042c040030203900010b0508180c1e002205c1d040038012104099041c000c020798007400400d4200b50b5220703001d01d40070030000c480d1802070324000c900720403810043c2e0132200001401484240c80a228403500f07128080a0405845204052854100540841d0315050281201250150300d290704008190405010464000803050491840c03541f081201203002e000080030710b8010710b40340111806540eaa600000340901041f60b6450340e42e000c0e82001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 699561681 1250 699560431 699560471
    0xb040b03010e060907080a0506130e0f0c04060b071b0f17010c0f020a0305220e0a0f11070201030911041112060a03051911090a09052e0b030a06 63
    0x203415103101040000f0102d042026041e44203007000d0761a41c0c034603501d020064000b80800b4007800e402043c0c0c000e08055500c1c4500c90551403d07140700003050301c1500603110342e1800d80c020381030f680228100724003081a100080240c881d0313941d00020b80700154218882d400850445503001c44465055010300003810301e0602c521843e040380301002400a007018140c140d42e000e008005441c016444015610086403045001e03000b800743c40001100c05090000314a5040c1e041900020609200b800034824602c0c818411018003480f1640305101001c3c4800c1c148000e4010204060705041e120402c2604109601d0428403800c50000d00c108558004a0800d403203030742110400201c1c460440000c00c035140380c214130b01c004a9074024014140b1821b0101c5061100b61a001c0c00c56602000c180d1b10002c55890081c030900c01c501d00d40700050200f400341007881c5451205000303109642c90b2051a4000700c45428074208500041c1d010114004504101280c42c000c2d040700302410052803c80505c113003400080076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 699562931 1250 699561681 699561689
    0x2070c0f0e0a06030809040e0a020a150f0f08161803050606040e16030602073009060503070f11030c120c1509101d030c0706030c030b0f04150b040b0301 67
    0x40441c580d03031142c1d44001c0312150300000c0c018490038003004003e854560040700d01804541c0940360340a90325400b05070080825000232446020181a04607015070011100c0780d5103181c1e252102d1100c84002015182c420090f101c2d40c01150040140701c5160f00810403a8140c84c08049035110560344c0f401d10a8580c0c2013034652611441c108450000940700001e0300d0640d0191042801000358078555921000303500c03041080700c8030411180b000b0041c2412001c0982da100d1041c40c214000ba115040041c03d10100380c1110051003414400e012007654400c0414465522034100221009140304800d0701c0d501909803c1c0007148501140703110382101c0c060107840c03070300f0054085034581c4012151140711489c04881c1e0382c0560744101c480d0640c0280360741041e1000c000d61180320f44060040e440450035680303c5030700120a40e00111040184a5140c4207280308950030b0b01e42000259501e0300014140900c0d614258455a00c40120b00701c0c2e50040701c00310005100f00b100701c907170300c1c0e42e5111300441c150002d2203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 699564181 1250 699562931 699562949
    0xc170708010c0f12051e1006030516080612120a02070513020301081b06070c0e07110d170a06050d1a0106020d140c0f0610030c1707170102070c0f 64
    0x4090015010f003410b28200c03510b648420b8008030201c00f0f1440105801469115078042d207403201d540c4101c10354201030065481020510140e82018805006e90f134000c1d05038070031042160201250564041c0d03402d6040b00d0b0480c0c03498824410551260f141c0307851b00c0784410419070006001040590001038010031101f0949001c0714511520040000300c1c0001d2007081c4043c0c00c070185001d2006840c8000e440603801c0181114140340a079120200d600d50b84e5085104a0100369080c0511141c10070012000c004052008100c100070303601005018450904070341460780b2070701c0c1c0802c0700c25000e84c00c5030b00036000213412402e28801904020350102600e018060710410110f0012405134804500f65418580b0b58482c07d1451800c00c0d8910000d03441500062103c0c00741e00c0341c40a2100060084500030350341400d02500080c00c44c1888a08460710340d002c140740840c0b580300c10244500210b010801c50b06c1314140320068000108001d0301921a004004001001092000c60907902145400d0140c502d004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 699565431 1250 699564181 699564191
    0xb0901060e0a0c050307051315030231050d140615100512010b0d140109020d0c050915130f150e030303040309050402031003020d0f03080c0a05070209040c17070801 72
    0x126071038044503d081c00100004a0030400101600c1c02480100110b100b404400703014166503520303442c40e140310400890002074000178a828040860032214545c840d83e64010001b4100104404609100780c2c0304041c01003903100049801e00070782052031580e040402c400d443c075919055400114500584003040c0c0700e00840d81000ca5200d00c900299032803040c01f81d4443d840c6074201203001d4415000790312240070680d200c00034040c000b0200088076008000b0759101584504c0711542c0071064480c0840c1d140c04102060024108a660f90300343d02141c14251584150f45d90b852240d001d0440b082900311010480c050807001a280c1c4110014070200d070310554410300100c1c00441015101e00c0207076402380009061400500441c0f41030343c021034102c0c0049403015221541d0341c1c0416055406034201b80c0e0741502d260000003e02d90413513101d5610040c00142c00386402c2c00c40001130428041c0010103070180c92104005010850804400300c058605081c0005400e03550146003591041140a41d102c15400c0c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 699566681 1250 699565431 699565441
    0x9060f01080a08070f120c023a29070201052212110703050c0f040b130c090909110f06040641030f130b13030c0b0901060e 54
    0x854442416901d0010182240ca8141e448010964000d180c060784c401c081c506407007001982d10a40400320300f085860f1070038202c03454010410700c0710b031680c079000c03544030403222440614a130000768918922074040304001d201f48604185981c41d444950b031081c04528003250308c2c101040340c16940d104131515030013403042d40c0d22860030007826890360400400c3c0c20340d540c2c400400242d180301ea1001c4c1500a14140d85291450300849282484c80c1d8019140350304485030b00d102e14106000b80e0b110b40a4103990602c08941801e00cc00c0030039061040c0c0450481d51039160807042c0344110302e8032000700303110002401140342070300303180003025001103042e4842d150b58024050181000d00a540440310a500e403450100c402c0c0324035984180d50496074901a0841c85000030000c07910702042e02e01d00004420080d143e2800c0640303c040901b001d13104030764242c54088002d000400c24201b8aa10071040682d000040c40c10345819580b0480c8004004d000b11541020015429030550001c0103d466031209c40940c0d44034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 699567931 1250 699566681 699566701
    0x305130902070f1515060f02060c03010e04030c0305120c1c0b090606090a0308071410110a0c080d0f020306040b0d020a0e13080d0b27060103180b0a02030906 69
    0x420100901e03541c1c6501d07409004c0f402101d024075064141100210741c5d40900602c2d001030303000c5504070300003090441300c0352460706a04020156105e07020494580c82d40d41400e2104600490003040107013000110103040082521030f1003034405c24025888502c015040c11030012505410502c070401d80b000144840000030212030243e1030072030202070110a516107607034050015076031102042a03040840b000d400030010790b40000426506001d5181c6840c4010940301c400d0400c000d4000038000a410522942131040c0c0080490b070704081c560130504101847c41c540002d40b40034940b00f80341041c0c508407240d004200d0a800842c03081800f183c04010103200322041100034401085c005e50000c031030301414040101c5d0140d01c5a0024490170035250350b00f0701a519608598840c2001100030307a204c990035001e90900c0350028138040389005034041c5042071030103245040701004021904158540020006641c0440b051114150f04a101e4510a2802800300c8000c1c2d13000f6a407000451140308001412192 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 699569181 1250 699567931 699567937
    0x1e060105240c0618190803060d0b0c031f08070504020703030e010e07030312020a0909091a040807110d0f03080c0f18030d1e030218060a0f11010e0c0103180804030305130902 76
    0xc100307804071005c0c400e183c0b24030155800047c045608807100891a00204c1c0603100c0b0346103d00d03481000d40740e8038546200c0490401c00b03001c41d8500a040c502406011604001c202d20701a50300a407001600c030b20440c01c2c21006005540801140c41d4600101400c01c82c4c80801c040050300d010307890383c1d050044900c44d948124031850603510001a013080c003e004d0224135401c243c00003800f403c048107d01c510158501c1d10840c2c00c1e54211994800007954404100f003a28074502031543c11110a600c1d200951583c0400c0c04083c00c000741001070840002e00c04904d9003086c1e910210f080422261200d0390055030301c084443d030000083c428401d4078260381f40c841c0f05d006203e80d40060003981304141d131403804080c2d003c0d4100041141c0007070181404441c03280c5812014000c001d100d60f0f209007009160800150400c0009089412a40d060158541c4c00c034900043c40000003000b0719000078000540b10b107030f00000b40090402000c00800060000525a10070090b00c00c4480c0440d41a01855840d10f02d2000ca00c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 699570431 1250 699569181 699569203
    0xf0a032a05010f20010c08040506060904080a050c0f06010f0801050a052725090c0201050708011202010e09070816030209012319020f1e060105240c0618 67
    0x20f6248402c00102910030300c0141141030800c04000c1c0e28440c651651070940700780c0c00b43c00c0001a40c134410001405002c0002903007091058400b041c00c1e007000e80701c81c1c10038814071840809010002600c05110b800c2000b400025003122415180b055846504c080d00d458130b203106820440d07081c900441c0034505203100307080c090341c0e064014007814521060304140e05400b03681d40142c0b074001c01c40e8a0308035586400036100350303607000100d01c00190f0401c400c10302107880500f0302808580c9000d040001854104200398195031041840e41a810010720040703a0761040d54004a41010b02c0000303100145410a04003401108110300301c641c0a00c000758201c00328020711525a00140300610860740f003011031300584030002420703d4400d10308650303044643c076844550800c40c40140d01003070080700030703c40920074880e0008115406120342200d0321105940c4501c18010940b0603040d200340f040300034402401c0300070000171188045449220750fa032070580b103850445644440000041d2602103840c004128900c5403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 699571681 1250 699570431 699570437
    0x3030e0112141f08032101121106030a061d180303040308190906020703090503010609020f071515060306030317010e1f080106080714030309010516020f0a032a0501 72
    0x682c1e965401240f40d86143da141890004000768081092002400200100321154502280c03185100200584010050b17001d07581000854404100041040c080c540c800801220307a29101e8036040096801040103900c640141c0410000301c80b44100c0c000c00c1144140440b840001009500c0070034141c80e44422500100003170012000100110076003070854100281049000602c20007a69540c0200da124110a6021403a040c40401062034240240400350135003640943c18104440008901070180e004002d02c0d1805104400c4250266907005000c5808002010a8030a54403500540201520700050300000d04010027403d2409048004a04076840310240c03840950b41c02c1e9404203401d83d1024007404001d0000c0001840c16024081c0707001800082e40900381c454604a02c049100c1c025580d42d83c02038000303000e100f400b607070003005480d80c0d0450301041c5a0290124800603002c5800745003c1680007000000200c18007a050b00700c045058074001c250f0240c00011950408512005d108040c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 699572931 1250 699571681 699571721
    0x11032206090e0a0c090b03040f0c0605090102030d02070602130e1503031c0902010e040f021b010e0d0c0f080d0207020907080f0627071806030c020d08041a0103030e0112 74
    0x80f24550b405050751469514211300e4031521480b64800750f92042d9407d0f1500b50503103460805100c0340f16688001032807035003801442c2c00c00c0d0100103522401600c0740c40380e91a038046400000c1c40079680454441307214201a0300343c0c031626000c80c42584d0384140d91808200000c2c201c658070302d0900100710303605050304203102980410180c503400094070a140049040042c5658402c0054a4a02410b101d0500414026031070714200c0c04010600c07101c18503001000da040803040b4002d040c2c08900d02d510344a05250000040b00740e400c01d1104c103400d14600420000002a6a041e0f04281b98090501c80b0320890362041140c551a408842641099a40d41d0540c3c0d810404681a0f01e08100141c0031000c102c81c000755a4087c0540d40f9030030500031540080401e5801c0b007a02e00d940030614000e0040d15103410200201e80035884029641d4032010200002c0c402d80c0c00c00f040c01d210b68684c0101c4a10310b10310000c8030380d60312898024a20060a480c1c603011808122840c45a00c2c3d00340201140c1405103085890 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 699574181 1250 699572931 699572941
    0xb0c090901031127010510050f070809030f0d18050f090105040c120f052208040b1c0e011d010204210c1d0402130515040c11032206090e 60
    0x100800f10b44a0003588110401d0100f005501d4600d00c1d0a00c00c1540b581102c0107614000074008007054210203007042103c00c000c3d000c00c00784000203a40c010b54010b040703070351202c982101203454841c1c407a0941c0c02a00c69034554070540da904c2500407440900640020421594540c2440342140b00045110740c84011080144250708240d0b10801e079072404d51900070070400320700c2510812550318442d0840c0c0e59446104000d04124010400180c01a00c801c0c0c0d42e0b1f4501042c0c9402c40107014500807880b0711400081c101059000d001d54100318840c80c000208406500300c89128002c2c5884140c00c800e002d4580c4040c40d079440188251021603040c2d00c0da50900845401403401a0220808111103842c2d100202140d09042403403c00a40c2d02a03801031181d50810b40104200c4d903920041c1406100e00307190803c13400c160304070101aa460340030345e0b01281200c0d0380c0b682500c0d440e80c6084208034078400031401207408a40b0070f04600c5407050038403428071119101c103004c41d5070041900451102021140c0480e03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 699575431 1250 699574181 699574193
    0x105070605072106091103160e190e09060907050307050105030a14010807080613020a0302060a0c2f030a02010e010507060e010617012301060309210302070b0c09090103 74
    0x20b510400d02e10301031441120015400242c034103003c0040d4034456030342c04c085c024082c45204100f01c100444880908510385502451141d503180b20304401040780031403808580c1d45588a401411100410300111116200d1404080700032040315106941e1043ca408550a0900421410113031000070713019100b100d0074400199643d5001800b001661551138184503070203c206c40c11107010b000d4442c06005010301e03010340e00349407010246c14002001460303800c0d10010b030794124080d0202e0303605440050b01e549150506550a55a00710302804110405d0401419807020500d0340024134030399804050916044000d050340c4c1c640c6500000e0120f203009a03803606640c082c0c0090f20080744542004580310104800090035120f051f0300101c0d02c0800365035800003925080c0103108090030881e00c1c10300c0a81c85001d445001000c18850801416030319014fe00c240841c00c0c1501e49459004000312220381002e400041c001e40c40b0380b0066031107040740340c04620428461011a00380800003403101c14140d0940c4c07105 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 699576681 1250 699575431 699575441
    0xb250c0309090216060e010c022a12010b0414070f05071505040c03060f09060b0316031e1b031703090304090c030b1e0f0d080d020901020a0503031603150501050706 72
    0x1058013080740000240703581c015500034041d2000013113066524204042c1c80c0203012102c0410310a465101e0380503820038401944d011203c22a0003006030401c0015050040040c081400d0b009403c01000d81102400c0019550103180c3c5503440700100514080200c038203000b101c20003420707281e103d00e410005890a400070f9400074050140710203096600c0d503d001c103c2c2c103491600180e040d2540e42000c144410f5200b25011020f01b500074104180080c100041d0396100da00005100d8518084000d144004950112000c00d43c044c04200c200c82d1143c07980780500f0b0300d81c2300c100c43c0200b01c5030803200000282d200b50303401245c0c035000450605050104c0700c0050004800d4450400d41d9580d1801d4040e030310704800b000410011001100f80162003020b1092610140c001b00c1e02420740e0003401c0c0c4c005110a02125800b00000f100141c5030070490b00101d04008980002604a104c00303c28008485c500040c1c1c10030241058900700120071108044d80000c01c00c2e0303c201804248140900c10204006400c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 699577931 1250 699576681 699576697
    0x50403120e0d05060f0c19140415030b040b0d020109030b0702030706020f07030210050c0f09150301030b2208161502040b0a08100e1609030b250c03090902 68
    0x200c032503141c0c64080490107010081005440035441201846903d00300c0420322900f01141140d51072401034081d0304408402c5007400207004000101101c52940080e0206403005806000981c10a0300d450703c078020301602501c40140e201e24501201541c003031910200030107080c0d5040e110042444d1864650500c8040c00500c44010750208102060015001c0d100400c60407040e054440c0d11035446080007440d00428080d410059032802c2d092128150b801c07810303685c0011600354000c0e91030442802280c005180c4c0040d62a16560100c0040204810328941038032030382078440d042c540702c0d0094809000801801002030001681000074080d188552003141414901590260b14044009013081c01243d00c144c1c00f045a194011590704c20f0340750301050154219904c0e00301010030604042400f1440300b8040e11001031008003030022102c1a0150f20701000458115840300003900d00b0341186211490240700b01503050a004c2011043e10b4000d0719250403094050b17841c541d0301030410000c00000e60001e01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 699579181 1250 699577931 699577937
    0xa27060e030a030e15010602030d0e0a29130201050307050d0b030604080d061a09210d031b050c060601050c0c0904060c020105160f050304230c09061005040312 70
    0xd0610300c4503400c01c010b00b0820407581e400110309540205203030500d440d80b046858100241c90042184540c00000d075102c0c0300c01200000780e01400340700500d14046072840b00401d4030401c0d60300fa60050007e04800c0d5004110a289040760b44d0310006801a900360340f00d0002d020900610200340300a00c59405408100707080200003503460081800646000d00856049502c140c00040c00d1040c15054043d0100400c6070103a148104081c0d1050102c15008061466004010703030075900b108026a040025040d83c01e8038140d5070f07003485641005001c1c051040d288000042c044c0700d42c0c690584501c00711082440000094030701c2d03481e030900458640c1e0045c58414124800e11040291541d60b01400b01c0c05a8450000065420325207000a42900c1000380700c01484000306a15072186a041103601c0c542c00788501c1d00c82da030703a41c0710714100c11141d41c003101c2d04a440c0841c4d10309400c502800140107120700300840b042442e0f0342e203030f404000b00e43d80c0184120001501c2888200001107904210a98002d0181 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 699580431 1250 699579181 699579191
    0x5030a0f0f0c030c1a0f090c0a1409060a170a0302160510030e1e0a060b09040206030a150f140a0e01230d05061009060f0302060316120c050702090a2706 67
    0x54214109170829500468040380c04800d00a0700c4100300030b10000f0320030640b0341c005128a40000005070001e0b60042d1405954114009000c0d5920402030401821180b8000c181d601d9041c203069642c1c8c01c0c0c4a0341100584107903c031035403a417104401c001c3c0c200c402c0100301c042c0c0c400c00880114040c000035142c1d44000d00ca640094112031190702000041d01d10310710020044d00301c442c1401d1098508a0740c81070301501055080c800940c49141c1203a030300000c44c0c40040342a566158094080005950000d0300d0441c210101203201c94100c0e0400b80b50500803200750101640740d401c41c40640a0a100300c00e4615001c410395488171103000d1076080e08210040c40744101072070342d4039a6420254100c40c112000c6510100038041f10041c0d206410180c910b41000310381d26800c0d43e011800a02c00034103034000606230030340768107000c0c1c1c801c041103c0c140ca5418000d0200510000003c0d0068110b840704030b120301c405400207009041e0a204800303144010a40701c0086501e031743c0d5404290000036206950803030f120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 699581681 1250 699580431 699580463
    0x60507030327030e1009030b070e03151906050108070c08040f14101110021b070b0301060f0309050304030303091704031b140307140a080a05030a0f0f0c030c 69
    0x5000a42403804504414449030b0300203260060182c8040d4010038421111200c0303603c038983d8042c9007103068940c401d4039211903468241c0c1c10b41c1c0900e80b00400613454130402c400c80024a0803010240e00070b04075480c05121076a2082c0b1212709440381402341d00e0001d01030b400040d00300d600c180e921603055801503039040d10381912448600380d0301c100e5410034030311011100c0c80c034a5141045130f002d41c001e03c0c041c60004800e18000e0400c90f00c4890120320074244680215140d03d00c3c0c010014440f0040260204030744060759600c10215994000b44030f05001700705603c410360f080c0e9000f4041c400c03440740d004001e5841c0a0855800741d00500c0110001d81e9800d03011074550894500b142d000303002541c00740315090600c10070201c003070000341c451b41c1005c1585800107400202c0340c0c500046030420b40c2c07070094403600307490042d5000c07036030790700383c03a4400b444902c00c082c0e0f12030902202100900e2240e800d50389070b041182000304156400002c1c141140c3c005810115000040ba20904c0201019445044403e00c0c10800b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 699582931 1250 699581681 699581711
    0xc0c090a020c3403080708090a05060c0d03150b042903040302100b060918280605030d050304030c06050702030d06080c0102070f050d0611090409051b030a0c0605070303 74
    0x1581c0c1c80401100720100c507111646807030401030303c80321064035820071542941d4410500f40604d500051680c0d1010840e2a0f00350707030700c2c51041e029100c0a410700f6201c1d18003810f45a0380301c440d40071407000b1919000f0305030134442464020380281e07010b0015451500b440d08007403440b907450182c0343c000d030b9401c00314000d100d56004000550149000350300403d200030012085104842042c00c07098801d20f0708018421040d1105610703108880303002d00401442e81c0c0c4800e540000701d140c600c000d0309661000c03025040070b04442c0e0701803810740c1c0b015030841c0c07115003000c84280d0b40c0344010b403000b030f021441080b41035000588a03006140e2080c0a48152807d0241030a07091094541c1500300031082d800c0004424099641000311800900114040129440c600008180302d000c0b86a000303010307540c0360300082c0d420b100c080f03089444115024204002810782801c0803070300c404000c5a00d000c01d00f0511050303441881d0024030300060340e81285008010b90301d441d80a6881d540003140440900d9182e407201202c03400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 699584181 1250 699582931 699582943
    0x902031b030618040c32220c031512021513260f060c09010c03090e090a1a0c09040b031509010f0e0106080a030c081207051207050c0c090a020c 63
    0x2c03140712074800f10f070304140311144030310600030591902c25030011110b81c1b00940c100c000c01c680d8106680c24020728070019081404c1d042c01c0c0c4450802a030070601c2141150b503160b80140c8000d81c0008071955202c2d00c401c010008414419006544248482106078043c11803100070811100a80c01e14054655a840c1c4206a4802000d0b4028181640114259031b00024040d100c070300e440d0340780a000da070314014452041600034681d90314100880c0c0c05034041014000e00c1031201030004030f6410030740c0b80750003920523944000284c1c0442e01c490a508003540707085840310340580500e003040061403d02c00500706110041c8002c4650700d138580320f00c0c08480d0b180c6c0400c0c80360b280500ac014002140ca00c1920000340305442c1c1040b04e82916a1402002f000b001002080340030040d81e043c40c02c866000203608000002740203c40e2141c0740105844140300c1265085001441080e071544442d610b075a403450340a440a0156044d100c8140d041548000901c1c0f03030000364141d0000c400303c0b0040c1410490010a0300c1e10b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 699585431 1250 699584181 699584183
    0xc031f080606130b0108010915081605041404030507060c17090d020d1103070b060a0f1d1e070e061b06040b0a2306030102070b070201150902031b03061804 68
    0x40c001c04188051803d0903001d0744115018610184020441e00000905d9440144075440e2010341d190181219240e804103104001c06484007103541002c20b049030041e0743e407410311070fa40c462032800d0a46000724002200c401d1259425884080c1065030540710300e03014102c101e600344100401c1c9040890b001e030100d0451409a5180c50090081040c1820040c5c0340c2220300b00d0400a204280d02020f41203400007044034291948201030b035401c0c0d120070003c6031481c4040e410040b0380108407800803829604280d4014202d024034114000036450720910110105945480c40444101800029444a008684e45540303214041c050b24601704001c0c0b0492490b40300c4201c03408441c0c21100038403003445052201140c001c03480030010403109009241102c8507082c101c0c0350110b03081032600000c034075650a50542c0c00740c1d500107031074010700d1500c2c51000b8002d028078806510300e000b0284012406410034070907607200301c00c02400703c00180c0103441d07483c2947d007000742850b81c4042c044a5481c402d458100186000e0703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 699586681 1250 699585431 699585433
    0x40f060f031e170c0d050301080d0e0a08030a02030c0c01080c070803070c021e04140628080307141908090d02060c15070f08150907020114100614120c031f08 69
    0x2e0741504111905043c5c040e40c403042040302c00d0005000c040300109030038501822a082001d0742c04103ea02003012019190310400c5c540c000495070b400000d80100040031049040c0c01a90305614800006480015040d24210a003200a018400001d49118010358009905003010314196120b079002409200f028000205601850011811f46040a004810500d0284883e60700c03140342800224840983d041d04020449158119000c00d120042260030041c1c010790040d01ea079160281442c41006103140c0d5030b0910f9200d0300980804c0401c4a440190f2111341c092205c510b070203034881c100081c82c0351400003130303078445820002500381c0b44041041d441403d10f019007810851520b2034000e0401c0c00c06034402c1c414450a4020052a07205501c03542c80c0e40e08040321a41010b13210740404a00409045000810014031982400510803505a83c00221481e42d56000740c00e03148500c103400340c0d0003412903048056040f00081680a203a030b5019682c00706161007201c5220002d072100402d21202980070741e03e2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 699587931 1250 699586681 699586687
    0xc03030209310908070b0414030c0303010608010e0603061f0b210601090e06130b1306030c0b07050c1201150f0302090f04052109041406040f060f031e17 67
    0x49900c0303041da10b01e03aa12800c5800c214140e11a01d03030b0002ca1117032100003805141143c1c002401c100091090441000844044130340351410350b24480d541e540280500340c0451500f0000140214107480d030188074000c050b003e000e558882607111505265852070000d03406020f0f50300844c1540c058406400d200d8102c0c40c006600b0290030010030b0008001400391410803030307205014030100d0300c00c90303115802c02001c2e50624114100846034200404604a40551080c200e80e64021040d400da0402d400b46c1e8014015039507500c0d5214030090283c400d0500c001d00c00c1e04002c4080c81c40c0d1a103070704298018107030400003140540d00360002a0052409402030740c19407146400920550800480c0c0507888044c00c80400c1007400c10f519103e07900c0300300d00c030410f01101c00e05180c001121040b81c1034402403440544180040300e80c43d00c07101e071614400c803009800f6904c0c04124402910305805203100b20f501c00316503000541d0071034480d100072003a1808003529040100c01a60001401a2050004034140ca200300b92 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 699589181 1250 699587931 699587989
    0x19060b06070605040606050616080a0c0f0f030327170904110d0e0102130b03150a080f1006030b013f1e0506061c080c01023103030c03030209 62
    0x100700da000f43c10032402840c06004640e402500049c560b101e0940011140e5210781d0800c05c2110340500414006112200b083c04030380400c440110140c15480c42514284200701687d424017050035401c1e60301c00c03d480d0f21320b180d40340403c0103a0100b4211407000c40120b40f0f041d0408000c0b40c15180c41034040304c407800f0002502007011101d849003011100591009501c1d003140701a940403440c01c01d00a0741400c40e000004141000ca940e1f50280c21502d024228240039030380e4114190325144002e141d40340b03e010340f4000b030078200401c0c45810180c90348809a0202a400d122104140c40600302518880f2a44108030006409444030041d203982090003202800b000540707000e14046844040c16801d41440703400100c005000803c5c0c1c240c0c4404180c40c1c000b0906038a0240041d010a900d6002e800c07010b00280c680300c0410706400512078039950340d910a0240c5d08190f0000c005550204166104400c100e070144002482262050862802440c0260074142410005880b102c0d594a21710500740821800746 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 699590431 1250 699589181 699589193
    0xd050c040f060806030d030e01240f0501140d2003090a0309090510090e0102130b040905010b0c07090906022203051c050708130b040f0f0e0103020319060b0607060504 73
    0x41e01410407807401003114184000400d41d43c12109004406054030749000d180c000f902580421103a55200c1007101000c11f00d5880c2c2145003819010f29074640c1c4540001080b40e5000e01680c4055007401442e07140f821780303110725600042039112600c4100600d9032007400249100040658020b00120000d007840900d58036000e40070300415400401101d0030b10041040b0040c0b50300210084510700c410103d5400300d404144c50080c800c07100e094041521400003c2181c407191009401035400a550800c0103980b01c125411044c000c1210000d050b60141c48103102034841c0d0340000140c04d11850b00981044010b038480e03c0c64641e100d00403403411240d00801c209104c010040d580c40b0400d0780000304540030101078014400d210b50340020388010310000c0e2112000059040c0d400092480c0050140c50729160341c110000e00c1c0f564841c2d41c204e01c224003004140f400c2c020302000e04a90340100140185404000401c0701c11950080a94610740d0760070080d81140c23206402091403500c15280010a131420b45042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 699591681 1250 699590431 699590459
    0x9060612020d1812020d110a140309060d02030a0b040b060a03020703050f0a050c01050a1a0f120111070c050a06052203021c4409060a0c0302010e0a020919020d050c04 73
    0x8401001440d07c04103070300942c0422a5981c0503080721030741100114200d81c0c0c80c514070901300ca4540200c0001064460010035074061405051810f005000c000704401c104002c0e80c0301542c1840d40100c0400c0b900010074043d600411166100b401c0a034105a0b883d000300d0500e8105045c240082800018061889402840383c41c0c0c2c0000c05071070030030070500440b160214080d5a08a40e500886044a0f11085036441c0e07001e88000e81a540001c1c8010904100800c51581000904039800c45508201080a2600600c40001d81e80310b03907185414005900710401c88001a1441029603010075803000c405602c3e0800c04105204212900f4034100380a031509004411041c0206e0315104070f594681c103610611400140d92107000211144400e041004049949219030350f105540408009010001550014120500c45000750002c00800400c1d0080715103940074160009e50200201d80000c0c803d2460380491140202e004d10010b0600300101c2004c4210740f070603690260700c403001080c01c000304018900d80c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 699592931 1250 699591681 699591703
    0x5070f0305013203010e1c1e0806210102211303140d0e07053f03040f0b04050301050603070b0711180709060909060612020d181202 58
    0x204950b40c90180601c0002549a030040002554a0368618078641e80d80c64071906401d0050080000c4a200e0b1403082d170707400010f00d00204004591702250303800d500404881020901880908010b5a44410300301e5200c0c40003002507074440d040a480100b0542c070600b4045603170340c0d075100060340c444454061400640c4004004103041000408200c00d060811351404c3e0080d80c14249105410b07203034152404607004102140c003540e45802100c0c0046400000c0c203104444c000e683d90f044481c415012400309040300360120400c9254081c020315000000007108080c0d45c04803050724107041c0c40b01c142c01ca050381c0c1a4001d42c000c00000c05c051145150038819543c020704101c0c0100489440e055650200c1c1c0140c07030380681086c61501e0038505603200e18132561201c00900000c10424509220083e101203000d004010018005540200b40e40c4010321410042d41c1040c0c450785884220213900c000694449000c100c0003030345541141c00300c0c0c3c4592008204140c0b08020b0a4481142044024035110388030170 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 699594181 1250 699592931 699592937
    0x1c05042102060109201e16081809240a0801060603020d270312090218040b2a031801021c0e033603060907080712080a2d0305070f 57
    0x402649074000301c40c111407042100c3e40116400301c0c181d1094202c5400b480c0c47d078001d41903a0b04050f01c1080818030041401c0c0035010403403600140500d0038864415001c8403407032040c042e401308440e0681c41c0501e4040070383c8802044501201d89825100c1d0a40d40c0d5580b207200800c0d000308661891440d680243e0300c511600d4004c4803070102c0300901d11220056459005818401200546010303840207400c80003038250041d050001c0742441040300f008511048400b41c4080c800030020902d9114074101c00d050307140511603a00c3c51076060b140d0510b110380c00602024180c00194030000d00100c000e00180100c2d41d004840d040540034480a03034403c0c0c4109a032452440d420070018003040d2149103000c003060024061809100480240c600c401620181c20b040c0d41c5841084100840d6250025989059400c0507050307401099680301e0030720b0842150701d40101291003d011030012140b040c04180481400350f01c14011004001c400418554201220480000e4940080011280d0024030300500402146 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 699595431 1250 699594181 699594221
    0x1a070213020c0c12150613090c0320030111091009030c0303110601141f120f1d030c0c0f0d0c08030706060605070201020c06090609040f020403060c02031c05042102060109 75
    0x58840f170700c840340c0141250300c01c0055070464003011440350b00c0f508403103600c81d2190156a490307050200003140074201c0254100302c0b9184060035400c040c0035645111400100860610350148108969501c51000c43d2040010502e00040403c01c400400c40066000351606180a40850582402c00c03005810800100658107108601a10f0b1418081d1300c021000c1d03845801400d48100813204240c60a545100302400c00480c41e40e02c51107540004030411030024080302c2421208001c076240d0007242e22a45035030304550314608803410404094400000010100f008107080d0b1f90303400b0800402c582100345158800b00b0b4040030400d140c4680b50140039103081207410a5580d0340000c0d130320ba0940d03003c030703000d25800308035034010740c45d00c400303a03050230078010810300c0000824003210009404c10322041d60310783e00300744c400b6081e94004000c81d45062a4010160900600780e110940581406401210a04004440c0c2000c0000150260082c2c0c0f11581c00380205514100b40e00341a94002c4902000180c04c2c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 699596681 1250 699595431 699595453
    0xf1401050a02070626150f2704060b090702010507090f180914010903020109021c02060403062d0203070f0503071709030c0f0307031205011a070213020c0c12 69
    0x1401c0c074211849403400030a096000b11045281002841c9035070311701c1c5961000d209681c2503420007000606405d4074003444101c050300410400480500460309124a000c00504490038102112540035008003004209810a007000c5901280200c58180051355160240681141d0041009009050741d8409503d840e0400c3c030440807040e0b07640e504107050707940c0e0040d8004000c0d641d4a000580076074100200600b108908010b40038111080c17040f48220342d01d0b1007603203003800840000364445802900e075504150840c0d0301e100003000d0f03212103c182c44c8815032800c0d4410701a80440d5803458810240582c403414100780190940300510f881c8030902100380100070007240d0240c0c2c07540000b44910402103160300c40030101400d40c8240050304c6243d006400010070b040308000010328403180f02c0d50707940d12401480304808080300c500780a2049025034074400407910800c01c40150030700600080c250341e90420340611000c104d0703110660100540c0c0114442625601c2e10208002c07a4203105005480302d0210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 699597931 1250 699596681 699596683
    0x7030819140105040504110a0b0909160e010c05010b09040c050f09090d270f030c0b0301030203030a0c031b11030c0d050303011e090519050c0a08010b0904090503040f1401050a02 78
    0xc14040e030f038069a6203200141c02d0061100320116031040242440c455151104485581540462031440c024400c14010842c1180d240329103101000d1199a607480010308440111100f46054805a9496488114103019030390303682c00d00d9004603c00c9440120203441d0106001000350014440c92141074221b04010b0800408580b0401007105868500218076030410000703108030000d040094100642031000ca108070701c10100744256400b0789408020242d44805540b094807007404020b40541040c46101140b41c0283d0740240303140d1090400d0000c1d48942a203076014070704e14043c00ea036200c00385400007031700e41814040c400801e04240d0750209901c4841e16611740d80d20061041d141002d000184509008022555090207062900024001c49c104070120107881304c8280c009140341c910304400b007001c80700100e0803508901070302c1d143c0f41c046a11785105003105411404030507411130344480b0498005070003400100b028200d209030018482c0d0030140c45405100b484201c403030500204110b1003111b2a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 699599181 1250 699597931 699597971
    0x50601061107090203090f16120326040317070f0e0609040b03030c0f011505031c020c06040e16110a080705011b110c010f0914040e0307030819 63
    0x1074104044088607080c00a460000075078481c0e092144040140412140081000411108001c0880b6520100c400d84d01d503140d1480e03c150400361000040f51030010340104007005800c00101d40c40c84044150f00d804900d00c4000b1582103000030745140640d800145440c22098120780b50346808900401045006480003022000f070a210b1800450030b560640d80c1c541000240c040043c0640751a81c1044156a940300c4184140c901103500f42050550184841c003000011144010002d12001240007081c991100c2003503150000c50041048149c3c5688940300103100030070715800d076100c0c17514101c37072140b40c5030b8402c60142c030404c0401061200c21000c00902c2050441d046881a139444c01705291003401064406030304040180c2c401c02c204c030b419400a00c0d490030340007144192080c0800d800e0044681200b80310080c0042545d010050100b040d60400402001c00c02900011380d900141040c43e145812041048000031148020400c0c42540c0c002041c412084d4501c05000901d41314100d4040c0c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 699600431 1250 699599181 699599189
    0x80a021b06160804120f0b0f07051b0c0316170105090307170d11070b060d021c03050c060901050613090c0306050a02070c06030b01020c030724051e0405011b050601 72
    0x1680c0403440b0020311403c102110020701100c00d82000845070340c5020b8405011444040e2042c60300c51000820b5a50360140305031160b00540d4803a80350206d54070310200c2c280c0300541401c905210300864500300e0b4500300802e440a40d031403070217415403520702188007180c1c00d00580400c3d1240d052109006010b1800002c2e41c455961007000141c8641d030300702035001180140d14101d15114201812440295a41d1005050725802040c044a060751a40300f031040401c800360000390810010440800e44254520008680f54480c0c0380007850403880010403894801c095500d070559954070340501100b483c10a0100a01200740301c03090095102d0358a41d000010f2041c4006007120303403a0710004131002d001e45d04444d02a688095a07a801c1900c803000100108080a038050140c42900c003100c4540ca800141d84040b0360082e403410814070000d4aa016281034180340355010700c03d00707100c1d0700c2c04110410040048100b524a2060f1030300d01d0100010030f40c8507400350b2341100c100d00440c4600031407030105409041d6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 699601681 1250 699600431 699600457
    0x103060207080c0a030905040b0102010504022d04110909091c0f03020f0d050f061c1214030703050403090909120c080903011406042a03090c090504080a021b06 70
    0x148142c0c00c21405070702c1002110031207402105150410582c1000d1440151703078003a42c0400100001c00010380c00c07164251401b9510001141b141d518500d1150b03500002d4540944881a142c4402000701d020349041820000c103541c00462420400c0c1407154070682d00c40e0164004001010560000d00020b07008008000104901c14658021040c0070750111044040716100c180d507605000d0300020003c2c28266501d2000850305000f16580d803902d0002034001c000d0f01c040300d0340f03506070f9070b510520322802c500303043c07820300c00c030f026030301302c03c4028107018622840c81c0f500d0104103440d052070300400c030700103c0d0020780002d89084203203804140b00784008001c465042c1003a407424101030a0003032460040104040e40740d030800102c00e845011030181c45000780c905860a0100d100c1e015402554140c40141051801344c2c0585034000c02842900003840107800703440c3d40066143c81c0c40003201070b25011502902c0310240054104d0b5460b03810071403401c1814070b11800e07070808203814000942610800240c40c4c44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 699602931 1250 699601681 699601687
    0x162405070b0709150c030807050405030d08060414040f03080627090a21120b150d0f05070c1b03020a12020a09050906090d0801030f0825030509041a0901030602 70
    0x600580d0144082d100b40c0c509800c1340104140c000b441001018003c50001e02c020f0046071a05003d14140c2d02034442c02401381c0554081500c0407030b82480018505940540c40c2c20400392411a1011390a029078020340c03002e0713880740701418050200000501003a0090048141707110740c010001028508094284864922076141d40312041d1803c00340b9640545014940e90415020b07852400e200c030400d078000d841c0c3c4240ca00419024200f101d0208520360780100c90380000c5003240c08240e00900088445010000b084003458032584200c0d1000c942090104e0100c004010920003410501150050907142c0240d055045a0120390341e503596202d51420320f07200300203480840d070300e00c400c1074050245a07804111034500001d00742c0c4c0e0758074280c0321042d950007095031618800307124a091030f06882c3c01084d454207040d800d5640c807a03558001c0c1848020081d4400d02800505000c2e1031005000303000c2d94400d034644000e04c007000115a11580180103046c2c00c00ca01ca0810744031000e000b41120381100005072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 699604181 1250 699602931 699602941
    0x41209120b043005090a0b1314030a05100504021c0213050a0b0607320309010c02060d0e011a0a0509040807020d0c030503040801060b040608060d0311162405070b 71
    0x4081e001984864440e416043e542030900b984040134080d0b10900712401e080380c540c2d0b0070549495105503044030400d0040c112040c065139111140c051300141010b41141c100c45402c0e01c0b0141400000001a0559601c44017884250300e000318000c402c14005000a480f0a079165000039a0020940e5006003a95299000130b00c0001c501d52001c20b0307802c800340c412035440c0780d20300c0d200b03480900800440302d140080790081031442030304c100d54490b2026684010342c984140c000c010f544a1031681003c81e4404800c11149480030b000e03000f041e0030300c04600004214800307121031000700c1c0030009110303c1c080d038000d04c010400c40e510383e45401d8000b604540266035550442c000320b400c06c031003078034040c045600c000d50000030890000300500c1203402d900b0080000c66155541400148554450203000400e113202140c283d00d800310300e4040079840303400c0c81ca151000d050950b508103030551020800b200340b4070204000000c03484241c1405036101c9080700007034503020017019203180540d08000c1e04100d08030000030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 699605431 1250 699604181 699604223
    0x80d0e0307090e03090406090225230115081c050717030103030503070810050f19090e0a03120903020d11010e19050c0a06270509041209120b04 63
    0x140540500c0209203c9240980701c183d68a0384183c290f07a00880c640318000034030088034402d03600418000d0084088a8020540b010b0b507050a4102c19110803000d1114040b000d964041e45124103004c0070000300f83c6455440030010100f903d58066151303604042201c1052005d1241c1000c0051540e0506d40d40303610550800d245000008107549401903000800070092503000030107940b10398400d40c1c1703041c2555218861071b81c40c1c140300c2c4651030304141d46200d01d00c0580307050704049403203100400d102d815450b03403540d500b800d907055151035400c1608621450020b259020032000b1010312111000c0c080b42c1c1c1c1d1a94020342e20103c44020000300300c04410340c0402c02e0020340080041140d00c40445000300c0701c002d000c05c1f0300c00368000101c03614420301030030b00030500300002d4003400c031036076a01e81003955406040074901311840380c4e800c401d4941a0000214aa41e1765078a4039010318003034050b0704041c10012070050000c03201030300000b44003480300e80300e080082e500d0b01c412030740326a1200210203909410b0f0f801d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 699606681 1250 699605431 699605443
    0x3150103020a0b1b07030303051b0f160f050a030e01020f070b09010c0f060e0c011e0c11010201090b090708152e050303121609030201140c07030b010e0118020301080d0e03 75
    0x1300b018011180c00105060349038020034095407400100313204690000041203070511503001e0340e18400d101809401028950941008071b00c41c091720762034481e40b01c81d0761003d0134030340010403ca02040d10b03008a46c0055074100580888941140014070b5840e051028510841c014048018104141007142c2410411031691020105600803002d2060105044886480d42c030743d9610b642c00a00c204084001900408402c1c9424105940300da050006050b2a04450030000c050801d040d0364807624010000303000a5802445101160f0181c41074500b0150510300b841d00400c50a507811555800303001c20600303048240c2d02c21900c4045c00c003120034070b051400b100440c01c1c0c0c0d1010b83d041c04042018030b242c0000080c00b61103040a0b4807021000000c41a003030305c55503d14013010b8000380ea011000100800b0710700041403c50b02201c00c854100b41d89607034805a00c00c00742c20010383c1200703a030010005143c07010121900c00d20444425030071581800d0f0410354030703900e560424042104030a00700c2901d403000e10070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 699607931 1250 699606681 699606727
    0x17100c0509030312062b020d060612050a06050603030c1c03060f0602100b030f031e0f07031d0108070e01050a03110f070c0b130308030a0f0504060b03150103020a0b 72
    0x9a035111940141543d00340001100c5c054000c005282503900c00b40314011041c141184569402d106840c0c180d0213001000100c61790868003150364480100c0d140c650341c03e495146500c25001052900803a1804a050781c0c0e01502e068000d500900000c201245c004c140c10310920806194003400c030014800403405000640d119a00905511201003a0168003250004003d80a1031040c80441112420b041d51140c0e0081c0030b007100c0c1c000b4040c2001c140704180c512188030410014440c00c0c070078420303103d050b2903110060403400300768007a0300004112040c441c0020010f07000d082ca04170714600741d031010f000c1d162500c2c04503040060010b110030010b4002e9200c6d80320511042c220944a4200480c01c5e041c59102c0642680c0c1c0005801002a21038411412a44801921800c3c0011285140c0d11100140c2014148010082d1113440002e511105c901c60035124501980000c90300310102403c0c541018071061861030049050340050002d611007510350300440d0031454805e6610100b02e501c8108410740960 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 699609181 1250 699607931 699607933
    0xb060327030f0a1e1409100905090a050402011103040602100c111204180b06090d03050c0d0e040c020102090904030509040b060f071b080a08090a0506030a0c030617100c050903 77
    0x20b8441400c030360021441c41400c190380202e800d0704098850070340f81d080004405d010044000c001080c2141021894900001454104030884030340740c0c0f0008200401c100c80d140704540c0d9540c07c0105541c1d00081e003005250020024516090170180002d442d83c2400104036a000e484128a4000520032440b2040e20740d05001074894010300303810076260560051061501182008002240c01941c62141c101e410704000c1c841d0f40340100e00002e1103800003180b14207809004c2c06000100104101b8001c8580b0248d00b580c840070208840740400003103502020701c031404c40e0710502102c3c800d500c821820640094060400300d8480b80c080340000d01820701c5440c0240c10010100d00341c4801c0342c940026001c582d2260418000402c1f22184242c0d12000c0780c0304804055002c69949800b0070752220040c04a20310141c05003c1c0942c90345c0120702c0b00c3d44141ca00001c003564810b216020702c0d0f4988215001b03020300b08100d40a840061820725511708403100c24403100d581d12007100c58070902420450305000d40180c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 699610431 1250 699609181 699609187
    0x601080414030a030501230906091315021c020a050304141009050307060e01090209042d1b08011a060313170304051c0804060b010c02040608010608010b060327030f 72
    0x3c00402a141c284580700c0f820001d100d50149020501074000d2031060080c20109242d51803604000c00310102804801c3d03c0e52807004148c010a106c40c02c0008445140140540c1d148401064411303c0b051580310303816200d1050001000f0b00e60300408590b001500042d107800303440711151100f400c00003800d1080e01100c2c54001031004000000c00601042c1d40164000c02c401000703125030303a00343d0308501002980022607000040005601c500c0e81c44045440c50358131107040820406020f4850449101650824004c00b251040381d281d0b11020340103003214800901c101040d00c0603c01c0c10030500004148240710101c0050303100d0120100701911544c100b0110044800900c041c0c1c0a41c0e03006960a0f50175002e504400d05410210b41035520203481241c3c2c42c0406130390b50303490300b00003004030085440c10003148a5024025a40d90302401025010640c00064110724001a441c00c5882c4488070700d00401d000d10808c82c1c040b504040b82020401c45850480d0011080c40c6c21a00703500c91040c0c075110304c46002c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 699611681 1250 699610431 699610447
    0x207050c090703140c040f0501080403020102071b0e0a0b09071b060204061701090216031d030a140118020a06030c05040e0406050a0c031a040b060d140a060506070b060108041403 78
    0x240d0000e0a00b4032407841404c182d91503c803601341441c40b407406076440c10308881100304081e5126100c029801030007440010309141d034039031740e44510381810030302e00e65591600001400030304001d103003107500318030b0300141042900c8010000c0b800c149002812402070121884030300301300c0c1d410313002a41100d44e80f10900310b65940c1c82d101c015180c6800350840d001c0725802d103000450352208610032602d140000d110b41c100501c0107650f08a1701c000341c6170000741150035030501241c400d403420099804180e1190303641c0d0b0900c00b41403600f40d0071602c3c141030346200d50594401c5400581c56484080d000e03600740749004544400300000959240c85135a202e1040c0710100750400050204079800a0b00074000064280840ca071117500441c00d58980c00b08490485c1c0403040104454036240d4050182d10001071324040c05c01e003c4a602d5001c82e210014620104407600701081900822441502e010748000c80d030070f90410b02c1a85414070300702ca00501e054103100e003c001003010700c60400c01d5040d026000c9000c9075911000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 699612931 1250 699611681 699611687
    0x180a020907180803071a010609090207020f0303030a0c03050703201b06040305070204050a021206040c120e01050103020f010915140f04030503070224070b0402150c15060102010c120207050c0907 85
    0x404001695501c080484000c4061b245000e5070741200c00c00c0d640e482c0041e06106401c0004d6000302000c9074024416841c010250300d0500286104101602d070000380e442c03240310040c050329001010300c802c040c901a009446e261800c09049000c14050400030344601c4400c940640c8511040c0d00b01005200d450100010594448000d05106100741c806000a4440c07031815000d03030141240e0800110710f008005000b506166101141c3e4050354644107050780800341059003200e04040c440d01669458400502c1941840040c1d050964000c0c80d24264031450060081d40c01d03090404003030704010185101c42e541c01480c074180d0b04068050440e56981c1c075624035085a4907400860128010700aa10170b91040198109071065a003403510801450311241d96220442480020801c80e0320029400e00c2c140820310780782c09484003107291802002c85403400d00808507101d07402095241162305141d000b00203158829000d17902c0d040c001402513241caa2500c4e1060410007412811134011a40d441009070003a8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 699614181 1250 699612931 699612937
    0x30507050f12130618050103020903100c05040f0f0b0319110a0f0314041106070c0e0a050117031c11091306060e0a080a080f041503090308180a020907180803 69
    0xd04041a002d01039507200261407188449617030f03402a2590315410003095001ea002820802002425140c81d007072030320150b07011940000e004000140000c41d042c4072888141c080900900019240110200d03d80a400c3e0aa0700c002040d1a00a4100400c000380c4036146030022003010040c0305c081c0740c403078118290007001d0b580030714a0400041d08180b600720f090b04c1c242d070074140259040000341c003109407034805015159005020854036034440c880c0c00107500681841241c0a1084d81001190355450044002d18000d000482c1d41104c0e0410040c06a040c0780720708428a91032100c0f100400c24802c1c554403414540a83c2e0b00c82d540080079141c010541203810f601401c103a43d6103446004007540410180404403d0f64040c0c1ea02a0340446002408900100041c0c100c0c00180f010b030510707143c1c46890280090151001c441c1c042030f2901000b008042e040360303a6550146001c0381d41d01c0380440c80191a5a15140e444010f40201301060115150758418106452000303080f000c907404250380c641615030790b07074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 699615431 1250 699614181 699614197
    0x105150a1502061b1e070c08070e04110103290301110c1515030a0c030203060705160b09030c0f070806070507150c171f08030301080a030507050f12 65
    0x40542030000c2110103826004480041d055070040400b9a41d0180040c091a03182088000844090142d50a24030290142d554441d0010344c0311926920285015110310f49643c1150034203400c140c4082c401d201c1d8070710100d40d00c5030300118407107804000341005070018050600043d9900300440d1010900792032908074914800303815002049030581d28408030055011341411000c1503005002d5003079a101e2a0400300390852100707000841030220310400a071904c9040c08003240c011105150802c15483c086c488207070b00c0001420070030b14000d00a500d404400080c0e6070010316500521011030b01541041085d5060b0080c48400c44101ca2a4515110b41e01c05aa1044400314460b01001039452486102a81c1805074003500805680702ca540607440905449100c900c1006070181d204c006a418140d2080c2c003809401840510341d1854111290300d000b09a008a0346950003080104158640040c81d24280c40c1c16150280d11490285492030804040d0104014241f04080031041440c102030b00a040c58 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 699616681 1250 699615431 699615439
    0x12060b090105100203121503240c0403020607021309080c1e01020a050301050904151e1508031914040b09120604020307170a05152a0901030e0f010515 66
    0x81e0390720020000c202c440c40b140240183c01c18030090352604107444c91550002c001520420401078035102180c0703441c803440880014100d52a945410040c0101040c50308441000d0b14603282500f503402094142c840c626000780940140320364040b44920f541e00010110b54071005d01e56076464003c00a540c0c0e0a1031140304211002c40760b0149510030740510843da42c004071a2290740c15130380f80c9800c000c00090010410b41d4075502401200342c5040c0a03110f004140c0840048040a280d1400c07180812200c12100200c000503244000340841342002040c0d0748107442409130549000708c28002165580c2c2c030b1280f902e00254001c80e011403c80b0ba00c501414030072400341c0d550411000c1c80c054003540e6017016a400f07501904090002d1040e5240d04d001c01d41c0c5c0d044428215001c0101c40d64803a031909a2240161403c215034409100040b051101c0b1a201207510900ca100f00d04905480d003509031180c41d91140c1495680c03d03a5980021041c4000c800d0040408020009440c000c1000400c0c40d00802c162480303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 699617931 1250 699616681 699616699
    0x1501060e100c0c1413020d020a0f020c01090b09120307060f182f060d0e160e0c130e1603050610051e16151b0f0e060412060b 55
    0x200c41d11039440b0100c441d40210010703610318500300501050b040310780d00315078114011000340100c03140d40340014005114061001682c0f040782140082c0118141020078046400000c0030044a0ba0700c04103d6050b03d1104880540d11103100000840007281500003100c03e000c0441c982c024000c3c980c3c0710503007481b9000018040700301440c00600303500460450040901d058a0041e81c280b42e80289600b4160001c3e1501151581e070803000a0216081101c608000c1600c0d2010038210000521101d40c410910362001820141010503003010482c00a0981c119440085400c0510440d0525008001c22001c0c410094504081c40c034032107040ca43e1103421011906280c0483c8090511a01d0418005c49a584860070042c4810074400b070528074a6045903184001d01049044120f991007010003036110b401500484d40d032800100041c1c2e1081440000010003480900106d035400807400d141d88c40407407806181c207029a20000d622401190410a981d00200028400700b240340c0e03100b01c110500450741300301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 699619181 1250 699617931 699617959
    0xf17010b0d080a05070813080a1109060105090111100c0f030b031501090c090314100b120a021009080304060906120c0f0c020301060b0a03230702031b1501060e 70
    0x2005101c1000042003182c04010060b415480b42010b0003050b441a0210341c9410804034098642c0f0716590232440d060f03005465414100004010584015481500c010400789407950010341a0302a0900703007814007411601d0a418090280044036100400c10340c2040301d0580030303100600c020510515200464901404d90041d0728000400c04141c881000050600d81c0c00c200d0910064108a0103a100784140c00c50084005440c0019182e40c8034140402010500001d00583c016a084011514010001140141420200401c2c00d603a2071b0b070155100e09202c0b00b40201102c500070356501098190102043c00714030613038840c804008540f85030380c1d170070700b0161204a4441121400940300010801c100100c000c40b41c0030700c2e242c0c0c0c52140010b0000903500d40da510510107541c01034085000085d910044441c04c1c444120548104424070b09901c0994038110201940c0c1e0b1090240c03a103c402418280b2841c0d0800421011810200b5032104001550307544001034810307140c6c08102442003e035510148 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 699620431 1250 699619181 699619189
    0x6010803040e0a020f1c0e0d090311060705030f07051605040213060f0302090301020331050a030c0618030806030106080111090411070b0f100501091508100f17010b 72
    0x20103032030300e2414080d010f48890400d000254480c04003d900350000380721040380d0551038203001c04050134044005c140d400304200960b0038007400c02c41c00000d020074098240040361f00d002c21080300701c009441c99035030ba840301d007481451030090305103440301401c0c0021448200300c00882c000f100003c04030300b000301103a103540c1004142c0c02440038076150481c1035181005103a10880c0d594543c001c03039080c0140341020780c0002c03a0aa902c100d40d20a00341940505d44402824061000f6002180d98602c025181400ea65569140d1500c0b0001804102502109070300340004e80c0d01c03560303041d11030103a5005100010715010b882d10305c044403a235101e035203403079000078041006004010390200a80e2400d850042411304001c001c2c044d82c0030103942c00c81c0a001d411700240000c5000ca00401c42500382111609d004102c2c0c02c44640141c114034100031a40e0001c02805c8898000c40340740001da03040c4015039a5071002c1c042c404400756480071402054406001805400e4203201d4508000b0305030003444500d0900b03041c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 699621681 1250 699620431 699620437
    0x60f1512090b0f06151206090106050a05040b090105160501090605063f01050c0c010e01020a0c0b1504180b090f06060d0c050a15020105070f090b07020604120602070506010803 77
    0x500201c22040c00615503d9446a00540c800801040704803c60882a06441c00c2c2d000240341c0603d50554800f03100d0546016001c0900400300c1e8030345140340600700740b4000c204c0e00651041a0305e101c004503107884142e0048054983c0b5903020701440d04000b20a0408501034020402c0603106146010081000c07811305880e6040c0b0200c010a07100c1502d12070788140385d00c0d11001420711610745000080f800c3c82e00020b0045a01400d45d000e240c5850300d103940f440780d084a00ba07108805181c0c0c41003001080041d0003d5010341190340010304020250345d108292490302846150466019150030028071100c158900102401e85c000e06101c421a0340b2060b00e5503560f0b8a440020840e5804080080c900c0e1501e11040c000303580c82299548c6c1d0442d614008036103104041e800540050010010307074942d1a5092040d07070b600c1000e610b0203081d0700201003000f4100c1d5042e40510110310b200000c080e415512000120360007000085680341c144c180f1403d0110013034101c001c00311000d01505000144100e800003c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 699622931 1250 699621681 699621683
    0xa2108132714090c120312010f081504030e0d02010e03061f0b090f0f120706020304060f03021303110d0b04060e06010b0c030901030b0a120311070f080709020706060f151209 76
    0x2050085503440130170044c4041d07095101200e00c01008180140320040d20810700805000410b188094180354005040580324003000c1c0c50001904100408a03611641c84540a1002e07180fa010503001d5000485402e5a6040c4207034141c8078070000d2088400d0007188480006000740d507410240b0761918400950f600ca00309040d40e02450004c0203000c81e01e0440e41100e600030313006010200a64070059403505045c400d03809040035070000b103002c0000c0e0345c00841d120b4075401030f03203401c5151006520b880f07101c841050202600f401e042182800c0c06032510300b030b130503841d58006072403540c01e14061800d58042c05006211038014041c55000044248800068070724040c41c1002071805c014109004600a00500003141c0c0d110b815840001824680303480050002c50099441001181c0a031440510b01a01c1d0341c00040a000750403001c100c205004103403841038803a1410003507600d002504040c000350225800202c05031700321390700000c0e0008620300040c19250081e11400740360803040103200c0c00c950400c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 699624181 1250 699622931 699622933
    0xd050a0c06021c021b0612090c1003022106061e03190603170313080304030314061c0807050717030c0601090501030f260a020c0a210813271409 63
    0x2c12170821740c032080b910102d10003001d40480c0c100711003048a0b0010400548130250030703400c007240420740c90411b440402ca040c240ea007002c0d0302d42000060b403640c40203c6c4c1c903d4107002c404c2000104002e5641c120031100d4806040401003013010800d15a014558819200c0c03031803030030640e8909881c1500d14001c19046031303001004500501c1e0104451110b99200801900d8031040d1110b5440008000401450003540250b50002e41c52240b09169611841c000d0702452140d00c0500200c684450030000c804515680499031a883d15550b01d41546003010035000031504030780340310000c180e2220000292a8a43e40c0c0411681c0350703680c0d941c1c428112002030002500051b2a100040c01240c14451000030110303000540240c2e50068602c2c174452604540704001c010f03002981503000b189402d0901402070600141c943c60045a0f510205050001c040002043ca807404142e807145030300d40140c2c44c03004060006102c0e030710b5103071800c0300c0c4008081c3d030f103100410382d00c0c1c540c074001d030398180300c8110780b0400c0610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 699625431 1250 699624181 699624193
    0x301090b030f070f060c03021f0f2003011502010b0405040807020114030712020a050d06060527090406050618090a060f02091003050c1b1c0c08070b04020d050a0c06021c02 75
    0x4002c540c03084a592043c0d0951151401601382c649e06140403040401001c280021080309450104040d02c1e02001103410022550280300c3c0d080e09013204480c1180c0c261240e020f10240c444070b09030301510112280e298058a80020081070000c200001c00013940300360303601a50440810012082030106648002c0056203101950307490f90800d9004040409103030625034202445018400c007601c0c00c98102400090300030a0001190505548459680514071041c14101d40d00d034003c5086103200a00c05403019840b140802e6841d11000200d02071104009d800349554a40340c85103a030307581c0d43d040c07049840e80d14084890300b2030780880c400d40b81c9901d002449a0b680000102040300605805040000310050401032059519068100205011035110142061800802c0d4002c00e641c8011340c1da8042c08075039010344d00001c009070100c5000c2030740802c42e09810348941c00400c010385900d030700080081c840e0154040c180140d8601110841e034040c0c0c2160038018904185100c01700e000038100c030243c4d1040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 699626681 1250 699625431 699625439
    0x90706021f091410061202130504170304030f180e040b0a06050d111c0206160f0b0f040b06010f3c050309010c1b1e05030301090b030f070f 61
    0x10808103040280d240d04045006100c0c1e443c0d540300300700070074070054140e0700921810040c580d460241c080140b02845100343c11411a0300405c90b09481e000045851941e96000201001440304c000e00c21104014140c0d600d030b04e010720b005072003440d0044001d004100c4002009403110051045d00054404074003150b1104c6d241ca80d1018401c2e18003034580b2a40544488005c551a2202d18155001d0340c010b0f03804264000e12581803103030581524401c01c5402032400c5a410168a9050403941c2020032684291514030845c18071080c0d544007100f0081c0013104000502c40d515005000d2180224042c003403034401522080010b40e03030440b0142c92400442c050740000104a455820b0403214220080c201c0c218503802010f03d80b25041d85002c05c400030400120a01c1141e0328244103080084c1440e0808200c900c0425091845e440705c0fa010007001e815a956202250191088000b41c1c201ea0200450380c8030350f1103280c920b005e400a000038070700034420003041c403a024100090410850710491010042e0b0350070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 699627931 1250 699626681 699626713
    0x60e0123010c02031c030e01020a020607110106050a030305090f030f0c01050a02010603050f03040e010f081c022d0d03090c062a0309090f02130e1008100507020609070602 75
    0x4462040c180440c0403201e902689003405105e14501c03100c00984200c0045140180840f0194480520640e105002d5050308030f400158040c0c10881d40d08100c80c0100340024001c0c05860190002c60300801c3c0c199001080580183c090449100100d81298608004000b4907a8400b4080c45803200d0380c0c001204000d055014400405003010688008240e207a00e80c0c8400f40707048411061a4141d42c0000740c100804080404d0b02c50241c203e078051545103c0c03609420990300c40780f419000365032a40b030071030003150980200500443d841044d04060010f800102c042104044584072000321030040400e03020f403c03440303032013000b0006e035014095818081c14003c003198551130004922041042d080c982c84031248218101204180c401d540f031300c01150802c8104d1083e11644450418040d0040c0407005408840c40500030907544010f2480e10540e0790000002c017907a800742e00203010790048621f40a8000441d03048144500c2898080784d407940c0b540741c0c1c03403a91200700744150780041e0003860415260001e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 699629181 1250 699627931 699627989
    0x17070519111903150f02030405100b010f0903230a0606030c121709010e1801150507121404050a0308030916030c0308030603241801050c0d020d06090903020a06060e01 73
    0x31407400045c448205030071070310072680207542c00d44180c0d004480c1c0000c0070520780a140b592000078a0b00340070310b520440015284494030b000081581d401d038070070495200340c034140070000721446c131003143e4030b44249042100c02004640415500018444070102c1c41ca01c080003084036803944503000f0072000341070b041e00e4006600109442030404c0041c1005444d21766508680c448000c2c2e540c4e9008585514045010f51030041c08071540f002d110041c00848003051440c0c403030b5803415241d8103100f0528500c05060a9a510440d00700581c0300b65034000200c14480d80701c2c081d501c214000c1c003c949442032a1404051030f20f07814030000f031920803140e00610000300c0700b2020b1034102101500300c41c694910012a414040c40e40030b440200341e0804000c00440c120a00074890050010703030000c10803030070906d09407002d038481d03100d4880d0895000140d18262503456070003c80103021a510400030071600f460002e4640002640a69143d4100440400d2818250508904a5040c6454100300d903282c80349400641d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 699630431 1250 699629181 699629213
    0x8070b07020a09090b160f050f0d060b030901060303120204080705011202070602030115080a050705180604030623070201020a08060d0f02030105010603061a0909010317070519111903 80
    0x2016484000030161098058142d1352071140010034030918042810032100c02070b8414850800401c0c05101410b15003040803240c80c02c001c011a240d079451400501000391099a0104040302c5c000001c00800c0003041d4411410350707104e076030f4880b24001036807003e00503402213000d0f400701500100004c00c607170340c000d01004851107030800015081c003040f520b400301282c100340c0c4454012050f13421151015039112065585c003015400041104d410000002040c40c080d000c40502c41d058075699440095441005030b40c001c561180040c01000c0c0b445c502d448070724000c3c07600c0e80c220000c9080850001801030003900c2640449a4411619584400c204450f582042d03d080d50040c180041000c0503890038055a40640140c0d00c0103e038152814400c44002c408100242c0d41c02a820301008026965042c40241180d07040002260030114513411030180d0f20950302d00401c18418604a80641011075211104140c01144015081d009040a02c6240b400c0012407816400e8100d1090002a20000030340e0421 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 699631681 1250 699630431 699630439
    0x60114190f151205131b05150921060408031909141207050c060306011b0b010806010e0403050d0e0712030804211d01020319050c06090708070b0702 65
    0x81075a4840800000c0311070740000501c0440305100e0314000780c100780003400d507100800b420802880c4c505020200540c000c84001d0035454110f004584d4448114841000f520000b05030b5240d00740540300d0328100c0e600440607a401182c11a9880c0d40c01240b0081689001610034003602c6240e4995403849075581c0300811110358165a2a500032a43c05c541c440c0701805845260403690890002c1103040c80d002c0310b0440055031110810485000030340c042001111044203840244e101c0e2070719401a50784410204060300c00c0031041566000f071000c04a2000d049981030003d41e22141d1302c406994510480444015020a03410841003080c076420754010008887c0181c03e0360309071a00d0b501010700c0203080c210f098001802e1241400103004c0e4034120b41c6042030801584001031410440007500421084496584102a40a24038050f9000f40125007545003e01416810b4030302e01e04016029402200b030503907891052100180c3c450742c0008242e81034683c07200c000e0600d149003412844d4240d004001c200d801c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 699632931 1250 699631681 699631729
    0x60c0809030703300903090e010f051e040e031209010c08070e0315071206090207110105160b0a0911030f1905011506020106170303060f12160801021b060114 69
    0x1900900d445a811540c2013a02c011905209a00b00100303050001d4000c40384045281004010110080702c2d2107040710f20507180d55a400000c1616001d03a4070b01c440035a6001410b180e801254014003000615004d00500510f0b4031507100e2025183c201d4100d0700389071010a200801040045016000c50005040d004040310f095564402d007070b043d04541580c03a480070900341c10703285050090501440c0050100300600310b04018581e12548030084075070020307505000c000034604202c01484000c40c481a50815140316190030a14822401004060402c0d210182080500c00c4a450302141d00301401c0d0240d80185000c1091403031118803606c035520211000c1d9651800101c009421101420003850b081d000010594030b024040310604011100d03442294008004204940e942c410701c1d0703401004242c526024550001c801d05250048002d400c1314982c0010400081c0310320150020900801500d80006c0c03040302484020396100780a000d0b0075003010351800e05504c6401d21a41c038a1281c00b0010702598 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 699634181 1250 699632931 699632987
    0x108010302210a03020c150c0a080a180e070e09040f02090a0902190510020616031509020310050a0503030a0215100e0f06092412030904020f07060c0809030703 70
    0x1181c00d0b10043c080340540c002d120401a20b1401c884070760500e86207038490500d092908200c4544801e10380ca0010640440030400b0640c00c2d01c24034480b91032068500903507109a0708c8030700b4902d5103401100c04100080d00700c400c00c5118100140700070b01499128200303403d101c01d1a07007000181d0300001e250420140d40c40c01b0001c050303174906050f400000010420041c3d2981850706001003007100000d60404c0d98803240c18003402010514440030030050605d40042d6030360000195072003844551340103da03282e001100f4484000038840340c04084480441c4c681d8241c0381c1d6581403545070300031824601d002d0781055624003034194001c450303d64007450140c1901c420584420004140d4202903c001c000b08801508011035818048075094102d8a1b14040c864482102860b01c000340201380e0060303004800050f031503001078400704160344941c04024015926414010138106c0d658001a6042d212941820001900c2c2409034507554000e034844030140d45000005d840a45614168481001c592091204201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 699635431 1250 699634181 699634183
    0x5090f100201151d0105090402061803100204080607030501080d052b051e071b1b0f1202010e04020c03120903070c03030809060916180e01020d2009010801030221 71
    0x8080d080904c1005000c0f414011000140345050304901d0081600b10b0900c00540c1d40c030b8054602000d04038180b044005107807000319040c007259013414104580040780115842d80040f42c494030804040d5001c110300e84e48e80e607480c3e9442c905115010080b48081120030450104c40c04100c021144190415400742603c0c50b030075049503021601074802c5503c0f14180300d01400c0f1901481c4e0460f14900d81302d905103083c1d030342d140e80c84150784030000c04403280f14245000b42a032502d5844018561b2a0481098a641c1e04100341c543c100c2d85001c0f0f0010b0500303544040b89141130300c261912948000019070401a43c8021390381802409801a502880709000540010300703e0300066011358801e0b44c1c0c90800341400700180d4500000680005d089401564204061800d20840da02c1155001521842c0311060800b42000078208000710440a500020310350f280c88180790014060b03a072256901e48060f400c1515211043d00801c02c3c0c2c540003500c2c0700c00401c0035150400304a80c00080701090005203034031a400306 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 699636681 1250 699635431 699635471
    0x91204090e25260309010c02010e03011b02070e040b0f0601140c010923060403030b0609091006170f0a0b0103020d0c0c1e0809060d0e030c10060605090f100201 70
    0x449048990756080c0103042c01080700c035810f40181c1203040f607951440d4150a0f128020b81568504128051a43d00190781c0f0400800b044020054020070010900000c00458401c150901c5c0c0c0141c81510380015200c11140c4000e03106a41000030750f943c60b11402081c21010b030019040724104402c541c522040c0c04a54001440c40d0881040000348148040c680394054403884a0000000711942001c42d4240d00b010840542c09541886c001415015480000d1028083c1c151041d030054540c10420485428101c421000c0c0d4040d0f0722054098810080c0b040c0c0208800c80d01808000703c01c401246400c40180c2060085c100141005030401d4800510541101c0ca81201e80c00015811882a01400905403010070041801403078171242c840a07031209030040c4603900d007890041600050000c0c20010590215558a000c803064030390328401001019950703208490521100fa1800c400016424001c0040302c4500c2009081090101090001c214800d0b00350121039040d0f548488030f210303408a0309490 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 699637931 1250 699636681 699636733
    0x51207050910090803121f0308030906090102070f031b170304170406390302060405010f05040c1511120a02010b0f01080c0a050412060501030209091204090e 69
    0x10309900c6808840c1000440346070b6030903035800d01140d0242800559000300440744042c40c1069901c407541c860019400b50880141036084a820040310044200a4100002d5010743d9034034084030565181c4200003400c0384503001c0020560007007001232400080c05400d071000c004205051001c03801544d41c5451401101000300011302e01c1002040204005001203880c0701c0180a00390b0a0906040c91405050071b50300114542c07082d810343c403102c05c2034180080300c54200e000c4246e8a40d01c150b401d00e000b0b9600e00c41564100c0d95942071180c0e0b00710804040c0300d014402c9800a048141c141d04e000e4210a04a07d184511810020340c511070b24400364082081031290050710703180c6c503a00d6080c858001d00f143c41780d541e207a1080401c1e02c030044082e039003e41259084032503200d00651300c459810003690745104a6008001c0325121000300410310219038440c41c101c9009031078103c1c441da140342103962185804687c00d048110f080c0424048950150710000d002502802124015016140c84001d100d05182c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 699639181 1250 699637931 699637937
    0x10803091327051e06061203070501090503120f131104091209050111070b0a14160b01170c010c060203130b0c04032a03150f050f0106020d170610051207 67
    0x9a00301002030402404404d603145204000404900041c0c140c1c0301c0e040900b1151050080c00d04214645605008903480150701400802451005280880d00c90300a40700304254039280e80b000498614801d40c0d061b1140c1024030f0aa0345000c52962120300ca54085001142c12075074440e05100000c0742c2d00a0002d0202041c0c0712100c2203407a25000400e091004030200200f90040b03c0200100c01f00c01d010340e8804400350600d10040c11496400c030605015101e221441074000004503414404800700185c107907600744442100788101442115030360555007a07031500094942d00c8400214403a0340c090340e004001266480f02444085c2c548802d034040070b07500c5080558001804000708005103100d0420301c1c0208950715208020740b6aa07030807180c00c0f4071010b000e05115080b000300c407a005074009022681000c5040111781802d19050180d948240074400143c800e50040c1c00b44940181a500600451340c002203104d0341d00d42d010b00508442842c886014414280101d03030701e9000501c11144a80c0f1195 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 699640287 1106 699639181 699639251
    0x10605011b06020c03280c020d030e040b040908090a08150403030509011e150614041a0c030a0810050616060506030703170403060b090108030913 64
    0x1350007416602001030880312446030914150301100c5103a03840008020b034000e05076141d5405a030082c0d0f00031746001c65440000c1c0f16aa440c407030410b0150020901c03a01c0000418107450741f2460844100c4000325034043c5c43e00b0310116030001010324000800303e880003140400740f01100504080c0030541c6803400110028400d40002040f40514107503e40b4100711480c804000f40484e151809010000040c0081c407603220700d15006204181698852508e407426104105140780081290100340d01840188602c020501c05001918082d40702e20140c3d203007505000802500940003e84150301c10320003019800c0180c01c0c41e460305940704a0000f030b641c490703e000901d00140d50748000e040001d00103403a2040ca45041c0a4800c40f8800d650030f1011400120802c48411340c00d020300c560b03942c030500074002c19103402ca5080381000c0305070301c0014164218955500c80118840ca006030000c030a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 699460431 699640287 := by
  have h0 := BRFrame.cov_init 699460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 699460431 ≤ n) (h2 : n < 699640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
