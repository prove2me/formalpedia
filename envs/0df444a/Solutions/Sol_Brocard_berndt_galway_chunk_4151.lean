-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4151
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:43:18.367164+00:00
-- url     : https://prove2.me/submissions/88460d11-2fcf-41b4-a774-1e4839c94bad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 746402877 ≤ n < 746582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 746404127 1250 746402877 746402879
    0x80301090203181b090a091e0201050c070e101202030d0e1f02160f0b03040318090203250509030c011d210105070906050f0304050109080c0d08011706010519 69
    0x1500c00c006016200032444a9883c40c43c3c0d4844c10701c07125200007400600828200000d02000ca00c6400710000604088100d00084038981e00042c0d03924460104c145001e0700c2040400154101400b0049000307480104410146640c0c5012800465a0340c0c4c00195154001503510301c445070140500040456020703104490f4100c09104581c860a002081000582c1100056500c0801040b81c00d0f0041c1c40c11900742c000f403c0c24105c500020b80401000101400988110b0710f100e2855581e00c2002010703085025541e030715002e411040c400a41c1520b0040d409015160910751502400a4500310f06001d0b004080001f08280119409400310845480c94043c0e0b1656100d140c6071a00c40840521140d2120a68a440b00348141d0845200612803000c200c1400000c0c0203030740c0d0000c01c0382c03070101411561035125115800c01c00d0040c012210000e109e08400148030802c00c001145001d1042c2407070b115654030f603a03584c0030802031200ea602d942c50f26400c060018000f9144c048980005110030402104440d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 746405377 1250 746404127 746404171
    0x2090a0b07061103160806030706020706050a090306060f0611010c0e060714030a030902031b0d0326010f090c0504031106030405120a02010b04111e1606090c140d080301090203 77
    0x25803007500e030703104614090b540901417a60031600302c40e0448000d034018085103203072800c0252500c11600544042101c00101044140c0c0f280e800350000d5a0810f000b000301039030303030f01075100380d84514403485020600130207074415031100c10b1090388401c840a0b100c84d29000c20301801c01405501030b5104440904031211250128441000581400801038800141d5401c040c0105890510710340481f032080708201e02c9a0480f52180a0b06240c2280d050500f400f007050690070742c01104803680c5c43c003003c8030011000022100c01001c40342e401c0342d400d0207003000000085081120795200e180006018002010460000c40c1403050045500034058000e03a03501c45181040d0b545980c0c0b10000a0300181c2d140c0303051b203482d490103102e00c041c01164040c1c1c5510b490321014104c0c5910414603007520a00a01017492504a9850b00b000c00f0749642c8400304120300855898400b080c10712501034003050980d1092080f0b600d050038100c034812a07410850702030030350f864001010003035800144000d00c8038200c07156042c14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 746406627 1250 746405377 746405411
    0x60f091415040e0f010b1c320403030c092405090306011d010e0f061002011b050318030a210612210201020f040302010305060f030601030c1802090a0b0706 68
    0x243c080507003128443c1c20240f88010f214001a0069200c460303040001e03000d80320440c900040c40319103104c4045103a524105069950300422181c0c400400c4c04004c424a000003000710702e43c0f189100e03850400102d000c01104680115039030251100b1240c0d1242006103141e0306d4000c1850342101131510398542960030300400d080c00707020303070200b01d820520000b01d58001e15503d40240c0586082141e000161800102100894002030700c824000c030701c2c50031503440b2280300303400c02c01c078070304c414000501002948840140654001c480b480883c5d08464103140c6008404000c0b81c80840003640d45407005c06008400c0c000c40030b420714000101c580d88a00005100440b00000e80304517010703940c07400c583d102e001004d050858034002c6110840e4410001d81009801400544003500d13028a0000381a0741c8020111b00803101c0500c005a05205040c00001000940561041507400440c1e60101003007031640041d069000324488698040540082032084802c0304001e400d1150091078041601c24030f200e00031003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 746407877 1250 746406627 746406629
    0x117060f0d061d07080c01020c0f09041703090d02210a11150c040e060415122405070207060203090a0e0c071403130b0f0d0902060705030a18060f09141504 68
    0x3c4039401290b8200080c2406020b600f4848a0a00140004599150004446402104529114401040100d41444018010814a480300484803940e03400d19800385940c529400444c00018420340b1105400c0144080f900c1024101c3d0401540c01c0c01303203c0409848000f030100034440303148501100d82d440c981c07a400c0d41e14043e503401800036039514240407100b40a240c00611190107a42050031080c0e01c3c546405071790f4120343d00440241c940c0c4400f881d0003400981c01107049400e40d640c440c6040118030325035000c0f0740181d105408030380c0b000351b03a88070503600c03130140c0144654020100d040400c280817000185a0344480c803d80303014680481565140d041402883d4014016800846e102000f59001d0305100c026180c0c5881e06d9051610149940b28607201d0310106166041e1030b41d034544110344609080e20703102d50b0b00c002035035203034001380c500200f018a031501c0818a80c4081840054400e008520700801050280ea4008681e0300701954642801c01c05113400e070f040000c9603a00990480b01d440500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 746409127 1250 746407877 746407931
    0x3030d1103010302010f0305270c0607110301060f03030e060d090807030807020f0f0316020a03020607140c010c050c0108480405060301031e0f0305090117060f0d06 72
    0x540780d5045000042c10000ba001c1c1443c103051400301840710010500142280b941840941003032400e4012550504202c0e128076502e401c030f880400d482040010518521504140c198000c00c01c10390b68512816400d2610b02c0041c001c540c0d4175a104005051000040000002c0307039002082c05509030740c8800059000440c10380c0024480c20600030b1142c0d0600c00000a16113031001001c1d0114005003560300c0e445000d03200340030070280908050454550414500045030020082900c070842e5003410202032407414880c4010703003d8100f45590540c040c1e0a0710743c1032078000e00140916038403140155004d4034041c00441c2a8110300040c00300d480c452104245000c2e03180780c1c00903014240807a54140b50500c2c80140b82005070180f0061080c4c3d2540e03016641100c0d04075141c3c0d41d40d00b014007007480301c1c18261600541201009810f231410b01d908180103002903082070343c5445000d0011200c142c00340034140c4629a10250084c1200c41d1482c28070400061a40070300c1000034100004200c6e80c01c841807501100f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 746410377 1250 746409127 746409161
    0x1510020f070509190504061407091508040b0a050709051908070b03070c0308070302040f0e060306130c060e04110c060619060504090203090109050f06010f080a081803030d 75
    0xd81100c202070181e14001d200030307501103400c1c1c10034881000c007010b40c0c2c130480c0f00c10a40daa40041c1c01d002490300480c40008121120100600300101e00400c1000c0601036404070004a5502010017071080c0515840756800a014904a403512041300029100207000c0e407042290441d000b2502c0d0f41c81104240c81100e074540e840001c81c0ca003014460508181e944000d07c0a40244204004075400c030041e02080748c5e00d8a03007100c1903614454290020301490308124240c8503001f0020601444000310356000d10021011110f295590080d045051080200c004202c80c981220030840d1034043d1800c45440c00d4001c20215804490b00d5203202103800903800001076900080601500d810200e20114044243d0030000700058102440607065202c1ea11501240300c1d0b0010019071905001c1d4007030081c081d03105058802c5d206000050350b41d103013000c0c0251210000582e000041d180e2300001c0e84c810b4107074002c915505060114940720325a070038602d203031901400b04001c0c12a5806a500c80c00000350344010392 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 746411627 1250 746410377 746410393
    0x60516200411130602010513110a0806161b020102100c0306091b030c0804121b062a0e01020a021e03060703060e060105070f0b090f010e1c140a08151002 67
    0x2240d4110020703900c20b5055914000c140030310b07001c00422310b014441e001544110291601c03804184501c50329407010200340101018400c80c80e109002001c2c0384219680c44501007404003c6000717101d076560b41c0090140c3c1c4480007071140130704ac58021b98104403071410b000445680d5041d0100c203a9032144810412402c0380a01a000d07650144034009a1500c1841c0240385460700d6030350307101c84503a2250300c1c0084c8101e00d101035000002915482102660040f401d2100e07000f40ca00080c0300180c008110440300c0054006403030f400340705091100a200050b03008100b2401541c0901c0351302e10340c080a04051041c0c0769884034003a01e0400c00c00c2c0c0682610f83d0b00003039081c60040640d1100c0805044217040140401c000c2000c21500c02d01190510b0300464141442d8a501044070319082c1a00041c4d80f255084c1000020880c0c004903002d40384040440900002142d04d0720204c034030072150f00c86032001c5a0f0510000004e0342c881d500b02507203c2840c40c1e000801c0c00b420f600040201250034912401a40441c030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 746412877 1250 746411627 746411647
    0x2071208040e010f290d1b030c2303060a2402070909120e03161409010801060e07050711040204030602030109200301060f02071208090109060516200411 67
    0x14085004040301000c540396030b420070000755070645841d00c0003050705c40701990b40303008001c155040710740010920204000c1d20007101092204400b01034000c802003031614100344c40e000d00480d408200201c0c0c9180d0202218801d4401401580000e00404c1d040341032020041103040c00310061003107041040e0821a64140044402880e20071203400102e1018244a1504000780c14004101c1b9846401d00703107880c0750311940020070315050340c4001d0840195461100060001a844080c00c407114003a2009500c90382c85804031401c2e211184a03840c108000b074400140618820b00151804a2090010300c024100100020b02680c009810a0350b045034008010481c0034941d214020644007610326021030054400a000301c0741c08144202030510000c0001e91f61114070038480f12018041e030b20a00700d40d480042c2031080c030303982040051a020400300100880d10350f02030350503680000d520f4502d41c61051201da81d0554204448080b07541c07552048894041d06a803940541e095080403d10300c9a15586103603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 746414127 1250 746412877 746412899
    0x105040c09060b0904090816060f0e012c07080d0e10020d0207060f0c0f11090f090d140f2205010504050f060f0c030d1a0f0616030207120804 62
    0xd07000103405458036200304054441002512041c5004480014000030340741011f0a8500c41c111400d006002881c82c00320800c01c070f60344403078810b00300324108002c800082d080c200c1c22901c1085a01c2444006c0f6142541441045811280c906074a01c060b10034099461074494078004c00c03900c201000c00e0007100b070040ca40c00d007502c14405860040c0700a1210264110010f074540b40c050150700100004d0018078142c442c00303070440f415444c1e4481d8501e500c284941c100781024050410482d4800c0c13044030003040580f0340d003505090180030fa00b8043c02e2241c2c003400c0152508902c403010100d440c442440b400e10100c44034005400124000506070341c803142403040c007803500781c5280c0000e4140721040c4402d1100f03446103001681c100c0e2080d00d41c1a95150510812038190041006403480e601c80000c58040000050300854a01e009015036050520b000008005900380300c12001d5811210500c00241c10350540f0102482c414060b0042c2c501c84c9131981c3c1852018070f6640416101c6880000303040241007904 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 746415377 1250 746414127 746414129
    0x105041109010f0806030c0d08030a0c050306090a322a04180b1203070b062d01111213090606020706050714031b1605060d0f0603050d020105040c 64
    0x56011a107002690400682000c0b000c40b041c03002c00005000050345078400700850a00d40d04001c0c101180b004652402110a5100b1542c1c4000c160234200c0d0000c0341c5014005403402400c0061402820340c0d03610742900001c6c54892400150810703290403000340041d00201d02d6003038407a10380e003610281c94101c070740c50440304510145802020b03100045a40321010300f02514143c585244401c11122101024480901140b0074450303440042c03116000d507a000004021312602c0e226002c02c85850b41d801e0100186201c038291042080c4c001000a514450141e42811200c42014104110102103603401545014540317258120707100b4002031a1502030900c4806c1c1c00c0140b4001c03074180049030501200944883c0c441c031602c02841404036256042041400416211641440459840e441840102d0100340c914900254860003590508819104504016000d0340c0c40a8003103450041021051001020101c048800300383d980c4001000003001406000342014403940089041c0c100340c100100e0400305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 746416627 1250 746415377 746415401
    0x30c0602161e0308061c06020a0504080f030c0a02091f14040e061b09131401030201030b06070f14150103050102030709080a0c26010e10180c031202030702090906010504 74
    0x210b1081000065482905141d10200948042000c1070098514941c01e880e203e40040c4003c4c00415003071002e60b8818007410807036a0703c0040307909001f240e850603908da1250410b1035456410001841c0098184104602d80200700b90905035000356202c00706c00c0d6000426084244804400c0f5402d801e5890f00780601c442c42c0c2d1545028112500b030211550303911190110000f4035900c0c02065081d05581c0300e510308000084844000c0c0b060010b00044070641c141d0900080307000c28600044501182001c1c01996080780e401700303080c0f444a490b0786a03216440c0d08021403000c244103000300c4940c0c800d990202140214030480000da2070781004035001d00318000c281c2150308584d00800c0c042c000300e14060a441c003280c1e190321007000c90301da5408280083c21707105d1540c22410341c21b0a02d00c80040740c00080c00b250b4504694010409250400c000c0d00c0d4500405001074124180c890302440030401c04940304c030a040746801107074034202c0d460780800c90f00c1c2011150100260440c400400242c10680075800b4040c1e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 746417877 1250 746416627 746416673
    0x60f0c040e0103110103020f0d0b13050c1c0b0301090c1a03070906110313243e01090c090605030c060703030203060a0506031906170c0d030c060216 65
    0x104004501070104014440640a15032070f01c10303a59641d01030b50403540840001d04c0d0741581d44114120000141108010f80c5024451210201010301014451140500c0c9640340180c6400b00c2d18070b5600520f0541c1d0345040d02a56545103107640c65409101d2054058030504850910916103100340000b00440c1841000d407040800402100c0c070b90001075282607600605104581c20381101d0003a145000c0c1c244409010200c81801241c000c20742c65505407000e4600001004201d090303802112a4240440001d02600c3e060050040740d026803126a60754403095140009268442c100b21400d4421040701a20207030310403803040c000600d2500500d001341006800814040510001165951184200107020540e020020541a5a50840d54401040002c04140e00c905003000440345510f44604403442191a00030700141c290000349038540100c0a0074040c20141c3c412170305120718060409000c40411000c1070382d101c00545184054424031901541d500c1c03140410f444c226000094011070752880b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 746419127 1250 746417877 746417879
    0x180915090b0a0515090907030501081603020f06071b12031202182e031d0609030d021e0705031803010506130b0d02180f0105010903050604060c120e060f0c04 69
    0x14035440c0341c0e40200c072800c1d40c544441308040c040c002002e024a03841168441301e10000e10080541c1900094180d038991410f89000002075220510065080d210003074005200484500e003615280b00501030403406041103040544000708070401c004442d40044240309076140b040024154000c451560760081c0e00000c40c03030210602903990f103000e0140461b52040112100140c2130f40c10801040c0d21414074075400d000c14051448001c8c0c007802c03102070142d441e640080701c0d6110b6a940083c00790301032211500030314900181516030001940c050f441d210910803181c00103000e444281c400a081450151010719150101070a11848400fa12182d45100ea03052506016141c0e035441d040040b098490355000070000c421001003000404042e02c06940f1030301c0d543c1048a0000c1c00910684a0080c500c1e10442c00d0380ca130740040d41d0070780300b5000241950344464000390000d061350f0f02141c10320340c1a0805502948411601c0400c1d41ca407103aa5851a4000b2400d010030642c0700d00c1181c0d08550100e400034142 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 746420377 1250 746419127 746419129
    0x1a0a170c040e03283b040f050a09020108100506030103120504080d170c041401030e0f010f0207020f030118060203060420074809020c03040303020606010e0a06030903180915090b 78
    0x3106030b40010348941c48000e005105c280d480358000c00e20515a40014040fa180040030040108007103103050740410b12403c0003600124000941a0075070710f0042c201b43c1103900f140c68150035211078240081c18000d0070440403c1c110000c0284140c22107050340c079640040380c40340c0030441450014040d00b4020b2010b2109020890b4012104c8491020a10380005c1725107045000c180b41441c9829201d420303501c2c00b40d80d400c03102403e40080c88414000d4529140c24088101454200c907140441001e001128807030602c001a8243c00868000d00001c101281e482d0070b141c641d5842c60b0001c140001c9030b07000090030340100403440c4030b600083d4100c2d03000c4d0f02800c2201c14081001707492114050140c56a010100801a10b2a40010b80501411709003107450300d901c0041c00d9078a6101d400213901500c03403440010440d40c490344000b02810400f418a4802e140307405403c1e0301071304a143c0b0031011300c654903400403c3e071801442d518004058002000c580f40c0d4603543c40481e41c246541248040906041250000e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 746421627 1250 746420377 746420447
    0x60e030403110f150a0f11030304020d0f060908120403030b0d080306060f0f180a081f0c0e03061f1202060f0901121a0a170c040e0328 59
    0x40d1501c00c0d101c0f09461800c0100154040f2904910240742550202c0c1201040c0d511604003861074129440e811003501e0207651030b6a84c2c1c04120b178025400501e008440700001e05843c0011046881240c1c042030b09040f5503070b420394981007000071103040c20400d81008189940b601910141c1c000c29120b12a84507620740340c0003580c0c48003c08050013103000003400c90b04030060008a41010054901e03060f1a4040444404ae0282462240600c156100800031918a5001c80c040b8400d11034100307401c3e0003c1550402c04060101200e0220a0040350380003030050707440a00c0010711689044144d02c0f800b5107000688250a01650000c4c41c22507010964100141c480d1822103030392042104e480d90f00c4542c00b00c01240c814041000d90b07103c0d01c1c104082480400000654078504150440f04c5044250310381c0c2000c280c1c545038017480d07522580483d04a0f8001d040961141c0c03a03c0c0352032800c1d00d1900798400c1d2140d1306101d05450364442c00c2040071003503441603809440d00c0c0c1ca82d40540903852a11000000203c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 746422877 1250 746421627 746421653
    0x1a01120b072106080307120801081906020d020a17010f0303020c0613051002060f0c0702030a06050705040b13050a08010b06030f090307060509060a0e030a02030a050f04030f08030103060e030403 85
    0x20074000b11a4204540181c402c0100280c08600e00090040b50380780d04140c0d80720340103440119980b5071103c2e510080d00740190300545c10b03900d1400090900d55420312640041c040a9034050350407581c204004240007ca41c0000d1041845980381d03040c1c12a140310041c1213000303050344240074a0040003c14000030381d01007182044000103c90381a2655203504605900d002c240c0d2045507c0840c0c1604180c1180e00465410700c51a810041c3d07106540e2065102c1000f80320f0100000d40c15004244006c000030855849550041000d15201c0d0405464441072001940120f10107120703401401020032080ca00100024054510100280089100e20000ca5968000540482a0783c0040c000194840d0b0081050302d01ea6038104009004d1414000c801603141d1205507151119a424810482e403030140000844e290034000e0303070007186407035420381c0115942d0b046115914100502044008007181c40e100c0103440086c05017600982c0c03940365141a50031126100c521250a40003070004001141042b40b61b02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 746424127 1250 746422877 746422891
    0x20a0906030908090301061716060806120c03071706010b090a0308072a060f0c21020c1201020c2a0f0d060c02010b030c03031e1c091a01120b 62
    0x46082455860403c03082e0160112140d0150300c0e05c10000745c048000d02d005000e4075400130a488070401c0300c0c042139044c02c0217170250201052804003c54070904105031a1041001c66005851624000da80044d040c4000c0758004002216404400d00282d0400c0c08414010080b81402c18074014801012030900c2105100c050001d0802042040900c09d90340025142c0f000794410203d01b494070016030034801c4200c1d004020000c2d14680410a6040c0104103207069141c0002c0b00e108580c00e01d01000d04102c00907481501140554005400d107500e0b1040c4500e81e02180c20009600e030b1000280e020301e03000807043e4005030404400300100340302003541d44a42e0004001d94449441d000400c1c08941600003606000b4810b82c41e11407100c85d1550b040d0320040e50320b20110b0560b24041c1c440810950b80b07000e0642d060746400ca444441701400850f0100a0166503041d5001050301da00340e913000b40440c0c000d0344041d42e003045005009481500c00c580c1c841e003d4030500f000524403100c0c0352281030345000014600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 746425377 1250 746424127 746424131
    0x80c010c020a0801050406051e0712020a180f080115140409030e09100f1403030d05040201170702030a080a2d060512010605040c050306180408040b0d0203040302070801020a090603 79
    0xc19034480c400c0c0794020300b610000a0240307080c2403070000000e000032502ca5240e07807a005078100c2c1d2410b02c100c1c402d000d00c0ca10342d110f99070121103050040080d07011241c03600510603503460501070808018605001091f510f144180d41c14503044900d82540d01d054892162000c1c0c404051200128201d60f030046c203d01500d001841c289289416605412202038556202c80304808223701d0390011200d100c1070f5482c810b000c24101d541c0d500c1c2080c920320101c41d1380e43d240d00700b4060315098841e9035010ba640280149804054a85861501d24481e98113a800d4401070708001088041ca54100300880d4200d03004150421042450b071211903400003409502d05035249034444d2802c40000079030002e00140c24000c282040c16204820304e2030081c8100d02c41c0b98051030030800050755560180042d45e10074000604900c0a410915400c4c00c0064401407049503403000521000c91841e4100c009880800e003000401070f070b60304043c100a40f07401c409912291031a0f00401204070130f00e500129600c2100c17414200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 746426627 1250 746425377 746425397
    0x1060f05190210050408090a0515090d0c170f012007110d0c060201020c210a0c17070308090c090c090f1810030212010603050d05030c09031605011107080c01 69
    0x812030070102100c40307031400f82d41010148000d1101c924000c00605c401290044035080d5645c003401038061099004c00d140340e50900100040e42040c082d20013110744501000d9480301e484110307168001c048240c0c018460303404040010345847c8244203840f9020002c02e40c0c01c4074011164081e201c5403041a80041815880d41900192a107901648440c2d8030741c0030441c42c04454a03024000d00030b4104045007005441080001036000340d405420f240c8612a19240501d00302d00042d00380d407284100001201e804a03101103a1480b9404a0083c0c088a4425034941e01c550803e030180300c2c42d00c10340c1240e91f44201c440d0b20610204088210896407441c1e420345224503070703442510000d0101034809049580c0010801e04010082c003e0b80d048905481c4200c0b044255000d060355041d01725211343c040140780354445064045058028005164800581c601d40c905c1d0408420100e81840d11800e400b10910504950902c41585c0001400d502c0c1c22252000381041403810340c0a5641340c091341041c40c180080910 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 746427877 1250 746426627 746426677
    0x3071a09190203030324030a0b190b03070e0408160c06140309061803070b0405030a0201111c0f0e0a0f0b24091806090307110a12060f0615120501060f05 67
    0x5220340c0300a001025210f1108d22170424200a5504413550707440401030382201500f191481c0b00300201c3c0e11000e40200219401c00c0d0100000304806402622500014001c410b210301e840041000840e01c01c203c060345540ca0000003600211420360350842d625000c1c03041200043d170002d6007552043d5880716000f507043d03030075202505612a4003c041c102030104000c20061043c000001c0c98a0304055008002c9882554551035550085c401e03042a0650700c84c0c801c50600300340307030048180c440d8a40300008000581c1e055642c90b05441e01030446007074141c088041c2c1072054482941c3d5010700640c1180b135440d54104c000700e2414400c0c04071030740300b141c0d40004502070401c1403101248010b1040200c0340b00e41800c0780142d560303401410046515140480083c02c03281000390100040305d1240352014200d032010b54a0034003806c030f50000891010f40d02c000015403581909141608161070352142e81e012080307201502c040d648160001824400d4968402d01c3ca0759109044070780144e2090295409048403c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 746429127 1250 746427877 746427931
    0xe040f11070c03140f030316032a08010608011215020c2b0203040308040909210f030605060c0c01050708071b051e010206071103071a091902030303 65
    0x4100d402031034802099030010044001d41203410740380681d150b0301c25040321202d07655448100e8049100c3c00d40003800070450140c1044e4042c42c45050ba41000300d004c0300c1c9441c00d10145c4030820740240c8000a90b06c0303000c40036900702c1c2509000d040740c0c0c81c00060a40c14000708101c0c0c1c0410580042c4581d10210401d142c207016503041d02d008507682019255210b80c5902203020030302410340c1d0b400b03611503058401490703640000f0032141241c1e8045440f40c2480c1c03070015210010014180309507940c02d04546404030503090303818000d141d11aa512405001000700c2e80081c00c654070394010a0140300c0c1006800c024580005014202000910f485d43e65003130240b42001c0700303004945d40240a02e410318500341d00840203ca800007602d0040c1c448103894024550700d816021840456039000d60415404510b416200d80e03a4409105007280480785011226950f804c8215124181484045c02f480c0c00e02100f12003d2002c110341d03810942e019a00440641c00290701c1e440050308520380d1010580c00100c480b0410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 746430377 1250 746429127 746429141
    0x9081906140408031b0702090103030813060507110c2407020d060603210c110105130b1c0c0c030f1815020a120c03080f0a0b090a0204060e090103030e040f 68
    0xa882100c620703003001d1a00c1c0d00383d07402c10b403951541161049224120f12221200f07803017000790018240030290f40b07107407410b603404030010300711802c40b86040d901080401d049014a5025001541d40c9580e80c03082183c5242c103050901b070029200e102025941e40740d0220401084802d04003242c80c2c580e850701c90384002041c03842e603040000c0c2002d05000d0f0010074003900900d490f4200d10004640100174440b4842214800bc4d8105c3c010404a00e50150720a1075202c0d00140442c48010707880a91040c0e02c2c1c85444040741c1150080741554845001ca40161000074001e0782c0301c43c0c215041503030148460f80e60191100c85140700e41d10403c0722210000d500b40e40344802c0c80c0e000380591003140350710b882a03100003510f4000f0b01c0000e8440c2041100560140e0b407081d88071906d03580c0c05a1382c6120b1515034000820201001400d14200c10b616128840b126a4680800034000c00206000582e95460030101070002c40100402d90300c00d207900001080403a4003c489500c420070202c8000444d10003a00080c2c00505407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 746431627 1250 746430377 746430401
    0x20d17060a05030a0501060807090e060a05040813030c030c0b07170d0b12010c0305091c0c0602070b07230412150608070b04210302032713060905060109081906 70
    0x1340d20611301c1400010f6000c682500c0c1c2c500141d44881d910f0300000300c10b81d1001c105060240c1d0000c80021460300c0c0940c00550028442d00c5964508070703142143c40c0700407080d504140c444081c410001c000b00708008a440005008102c0010f00349811a110041c481c034030300b0b0318000002000152b054004055601c03044607108020840c0e4500d03600c50101e9402024950354003c0400c0c50701c0c01040350803100261400440840c032007e00c04001c00d00b1011911042881000c489458080c04507078001664000c9407032090070142e0307891446991805508010900124032490703210820801880340442154800b1802c2e6081902c041c0f50901c00d0380d20070004d1140c1c0d8800229801400c6010400c448010010f02c21a1582c0304010540510440d0380301c02e4003008400200544e004200000c00c030440b2060703d0071801458050500236035140d8021920000c4019055610310303982e21010700c50407a0354411503410102c203203800302c0c0b40390905817819540c500c029400b0200c072500030017403020400e95801131209545 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 746432877 1250 746431627 746431633
    0xf030622020627041506050a050403081603021902010206041202030d060b090f0609210703050601060f12090c0911280207290d023007020d17060a0503 66
    0x42d52110749025801d55a000456005903031020b0f00203841d0502940501740c445807a6459002d160050a50f40b96100d906120144541448000b010881c00b10181c104101c1c100003401081e43e60b4a13000781000c25514603c103009200c074920740c0150760700007841d0703604c40d03800442000c540031101c1c016803a500840008400060400c0c9003c02c2d0715801501611b101c131402e40b408100180180100300b040c1c0100c2503100e800c000c0c00340d09450100741201004100f000200155800141c41c0e03140d050600b50240c2100011030a49902c6c00e1245600c801012a45501c0315802c01c8034030043d95604000e490139204c1d9005403500c4204c00c864811580b001c480d2010711a5500211820b400e010b80d0b4000c480d330303011400c058003030782d440080d40201e40c04890442c0611b02c0c820003501070000c0c001c10380623000000c80c4201e8903400d0141f41c004040d04880d90124200b0000b007004411450704c00110340100040c48101190010b081c00d071801900141d200041145000d50100d013a5100c0010030401c0e9030710341c41103074144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 746434127 1250 746432877 746432887
    0x3030c0f091002010c0807030c08130c0315051b160b1f080f16060504060f0201021207030905060606041202010305090c060a0906030509061e07090504050a020a030b0f0306220206 78
    0x35405601c000300030440c5d0344500c03c03030790b0f2040c10950403200e10b60b0a01000c1070811002038894402c081069450b01c1c07003101c1c40c000ca192291981c0e00401e1340c00d00100503240e65003040c0070040c250114661142184200c00501e0407144540c8c25048161070180100103a80c10408070341509855060140d40d41c1c08840c0680105940b1091181c0c1c45030302c00143c0c00140910b81410b241c01d0804440102603c0a0703440e190b160610b8402c08407001c21004400d901155400d0000c1007401c080c1d00f00c10703070181c4002d81d008a118046404c1540c14640d020f044103101e040700300000c03c02546071448401010b502402c0001e840e54805900c2402d00340f00c0282103620520026100510b150404480c1060341e031740d80c2c1c003002241d0b43c04405aa44000907a41c0c0e1088030098600996101e071070b9844103030711564514109843c0c2c0d5a0b50042400c0c3d64082d610034003220340100700082265032603c500f10041e04221190b050840a090129031941c3e00500041502c0007011001821420326444003050264042e000598130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 746435377 1250 746434127 746434159
    0x170304050d03181a28080112061b031a032a030102191707021f050a2901110610140303071403030615120a20070b04060b090903030c0f09 60
    0x3d900c694511a0090310031010512100b0b4110540700710704400c0d880da508148d083c80b004074200200010100e805135110203c085080159258901291180340c8001c00c14a42c601c0185001e1140d08541500940c0b140000510740000c680310608dc140f5a000c5030310704007075002c020a0291107100c9003042140304000d0703101ca01e44e6200104100c01207120702030112540300d01004a0b146c0c0c0131901100080a104443d4181c54842c0d5401250032140c000301c00586204618200c903003210744180f031450440070311041940c007541c02543c542201480301d0040c250901d0700e03e401113034244050041000441e03a0821000103500c0030011101c64a402441c8012640040050b0300c2d03580e401121600c1c003514820090f010304804090580d0b0030990003d00e5104144c7d60b203400f0000034000130802c00c0070700c0391403a21010821100720040c1141801954156031070314003400c09a09030751002100c9809045000100040100c000c020b0b07941100c00d49003525500d094080750041140107404203644e00c020308034030340030513 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 746436627 1250 746435377 746435429
    0x21090b0403080a0e180a0c051b06090708011509091406181b102f30071203021b0d080c0c1009150207050304170304050d0318 55
    0x1e000b00c542d4507203134100d80b483c00b400400810748400000252688001c10b61003011500300d0b110f03801251521038180000300100103203503491321950311202c0d00100207100300700c0d00c28000c0c80003405142c8002d0011145808900c0000fa80c03034403825441c0d640c2d680f2280104240741104880d0300080c01c1c204c0b250740c00c10000c810680388294450359120300c80c4566201c0e50100005500c890f6400040c569a10080090780a03140c030010100e01a96041ca1550303200d80b44481211444042c043c0c2e04010640c1410100400082c84024007070600c00e030300503608403c0b00001501c211503420350b006c101d600301d151040a0540280c0a8220030a0608012200c0141120f9000400d690700288941d2900034176102c1150340702052054000b01d80c003a400480e4401d40201c050340010b10303101e114503003081b160754040310711301c0c200d0700408021030b40c50b040000e040040c0c03000020030107220b401d003401841c03070680b0340800100901c1210310014148103507414040d40d0040e210425400611034070f500392400e81184035071404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 746437877 1250 746436627 746436637
    0x501270603213504051006080a0218010f06051e1602030d030b012015130c06081608151009150e060702061c090b011503020721090b040308 61
    0x8001421504111003d01d00c004501e686003100050145001d4210281110480700040042c0d039540f1880200d02c94510440c460b000080902d0300140100c0910707841005450362041c510061940119001840101c4c4072a5558080b601d960500c0303981c55914658000c254100c88c503049900210108100503203440343c00c00b40420720720850a07246105500841502210080040140041c00039240030041c800b44080400c1d1000c045030440b12424004014002e00b43c070220b604034540e500d0704100f10108000c4000d08000380c2042e0400c40b01a01e020406083d00c29510b1803032504000c4008082480710309030070341249000c3d40242186135507000c152400b80c001e00451264241c40e50b155907035841030b5803103241c6401d4000c0c4020700d114a46400ea8007000380e00d411020140700a4039030102c030080704042c070303203d044c82030340c41017000030401c0d072410104281c2006043c0140c818175004000c1000029030304103c0b00d5000001c5180c82615683d083c03404c4030344c2c00d22500807910790840000c000c02030248280c040e107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 746439127 1250 746437877 746437943
    0x92f01090b1e09010215010306060305061b070605041416060801060201090201051209120313020a06030b060a03151a0d050705041d130606060c150501270603 69
    0x14440d035a10601401e41c49000b00140301001907410603000000000001e00c040b107014411151001c2043d41413a00d0140280c0c800c07160a41d449408004001003809002e9009030480c42d01c025591080140701c8051003003440007000039903650005010860205a2001200e0032070003201d100c41c003440681c00c4108511700032900490071502c00040c02620501400301d003140d041e541c031428043c0da035550045201000d40084031703c0c0600c610880303400440c0800b55214031500ca400e003203880301e140148030005040d50050301c109414403040d017840d87c45090803210010410b00d4001190a010000408000040d0704001a184102d1005c00c10083d8064060800a108000d0822058035005004c0e1000d104038854039100b2a2000c440e4052003030452410717603000e41c211400e0080c40715150303544d10840c2c80e103400c2403012400360089102070003101d849014a5024201c000c200950402e00c4400344010041d000f01101d42c0000000b6525205540200c401181d002642d00c02180c18081d0102d98100c554600e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 746440377 1250 746439127 746439137
    0x5060a0608070602070303120b060304240b280302040e010c030e160b0d06050402160b130b190f0f0b120619020a050702030f03030a060504090503030a092f01 69
    0x11401c4800072440d02c0440d0000e400904419145079001d80d410401544810201c60390b5050b0100c10303450f22801144102e00c10074400b00a403807001c0310315600c400b031415140041c0e0310340346a00303003681c8980c5440c01010010740c4d44802d215405454884076078602d9000250880d003400700011461380c05402401d81c410709920284042003041e41d2480e550600c2204807400070701412800c015a1003d030303000784034006c003c080120306240c072074001c101a82d001031440c4100d02044000f501c103020340c1e038100c5900980c5103040e2020300c0100f9250100d8003240035000500d824a80402aa40300d0a254400741c10180008014448096100001401407043c142098022100440010046400480d8540c4564851444401d100000130327072460094020900910500000b0010310025039000c115004054614000665403403030048402d20030baa0180d4003060003076040c1105280011030200940760302101c4924002089203007800c0008180e00304428281c5810594100d01c440c5440443c654480e203c0e0030b0301c2e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 746441627 1250 746440377 746440379
    0xc03070b031b0915030612070609060e01020a0302070911070213051e0705040306110405040e010e0f160902032220090402030d0f1e0206010503070f0e0415020706060305060a06 77
    0x801240361041c000c8090b03001072159000c504d00403036003000d181c2292010704461104842000389138642030305a04008017140315504200440c0d503110800940f10071003840500019459560041d43d500c0842c05003014a945408414a04400c8502507030b051030303001017008040d00f4041c242c00b80104010f41c0c080c031030004101c5180b01c5040c0d006a0030b501070601503650b1840c1929607100c40006215a1206a100010820000659a503540100c8a40140c1d60000007000c18036200c11502e0801d2010361480a504640000030300f101d40704a9440480b8100d406c0540e8aa45a2000995011200c0404030000f06e084039048184081d0310740c500900b010b42403040f6030220800c010041c1c02002254003c0d030603401152034141c014070501000c10840c3c100c2c1014255028040c040181504c00514000016882000108041d1404021030f0300182000e0f1f1502032554101504079400140042c005010110600c041f02c1100006a04032050640c1101c42000352545910f01203032958000c0c0d401044a0f03040c110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 746442877 1250 746441627 746441671
    0x10b062a0304031a061f1707080108030a030b120a0f0303060f05060720030303070c031b0c060c0f0213020912010605030d1d0d0b070f020d0206040809030c03070b03 72
    0x41142c040e00c2e000441401101c0d0b0500741004403440007410b6540100b0040d10112418000300d83e520700142590712110b0805100030f4103d4021320004042600700800f03c00100035848010040358048c01c1e00d4030b070120314140c200c004280211401c141036061403003003900c1c0005101c1c101e440000e6440c800d56040c080166106403140c0c20107007034000d003503024004114050000d60900b030381c4003524030440c144c0c500340f62103400000c1c02d68204540c084003041800c8000b20030583d07c003058070f01128002c903080441c0b082e1512003129030041ca000b54030070300901d00d0b03100050002052a42048690050400c054181403e134160003a4000f004070500521002c42d40090000301030080ea41903030342c00740c014241e001e00814100d84990b5102c1c107030f0499550500b07641074651150025040131501a184140c4182041c1e14010900420404110211342010461440c0c4036408107a0a8000d90060f150745e464056100000703050020304104c00b58584a90b450024131808031002440c400d0040c91002c1c01b483c06112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 746444127 1250 746442877 746442883
    0x9050613080d020702010c200438031623040c08060f0f0301020f040501021c0e060a090e0f01080d02010c080609100807180b0114031305010b062a 64
    0x150001c01044080c07246500150481d406020800e0051401821111058880e4010300c0c203901e00440e00b41c0c4e14001400c0407401c29000c0e142445214195442d44074084d0840030140f0000e2a2075440c09070034028203d802e5a90400ca0030101c1322640984c0006141d0300c08401061403500e0a0382c0b0b41d00c804d48040040070b0b02c0c180c403403119440b5580d1203440300355440908001c2d80c1c001224505034025802c0c0681c0718951800d1010381240c000e40d50445640e01e0803c8006850b101c03100c00c20541d464880340c00024600c0e0f0000c0c0d29000008241e8049880f000c003084281c48a452641000300001c0b440c004000c0c2104039068664121208007089d1190701e01d41c404103e090301d205100e440045051a0042159400d1280c003035984400d150060031001603c0d015028241505940320140740304240b03141c0780c3c10503606e10a6242c00310302420460308105018442a0f80382c003004186050b01c0b10b510f03035070409210007900300a002e150000c04041e9901c00c41c44007440e94800803904040200d519151500000c0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 746445377 1250 746444127 746444161
    0x13170604050114010303120b01110102070303051f030f030e04020d0e1c03060614090a1509380903161e0b18060a03020706021b0c0a03020f06130e0a090506 68
    0x7540c1c0b140000c90449007d0005441c07030401d854100310303025000690382c00d401e20207403000a1099501040e2820101084010754904400350100811516820800144510189103a1782d5050910440707200360303800003800034001c0c1d4144000c401e003081201102818017040c0300c2c05600d85080c00707082046c2c1c564001c4046641901071507001c1040e45091480c03252408c0c0c050314800701d00078403140d0500d45071100e0558281d0481d0310040440d400d86428840e2000100e908c19816043c5d0400c480d0610103c2d900c000791051503805006120720004510440740c800384000c0010740a64501d0a50150b076841480b940d000c007440300c10080e40380c00000450544145401c0ba240781020905881521003100c04100942e1302c496120020b1507401c004030b80010341103001500003501c040030b1140404d001104030604100c091a9518468844402c05100580e24281d808205540070768049803140800c02d034003101450181c001c03410f203180007000c000c003a00050700008107551141c815142181c50700320a4041038142 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 746446627 1250 746445377 746445383
    0x22e08070504140f1207230a03120302120432060f0702100e1b030c150d151203030608120301061206052d0303041208131706040501140103 61
    0x1080304000d0f50480312040d028942c0b00030403412400884d440080c0e40d00c88005071508894004542c2000006540044099581800700e842c24039400c4800010b8054960303400010702c0300c00300c0a03c41500c24826410754004810720054030b00c140c24141800501036403c01c1116440740d0410a480340c00d400780030852129403030003000500b015110741c5441031180310000e009008500c46c6080a0801044901882ca225058bc0b009401070850205040c25004104540507011790f203e04e00064403500c9a0070046241703925a0700161300c90b0074221580c1c003c0e0024036002d100050320410080b6011307006c1c00a00c1c00141c0311351000c0004135a40e690041d10f556106d0403514020341c0600040081c89e00030350107030710014041500010b1540d01d41c00010884010038030680000140c000c1d88090000701c0c10139850744908110300031410607181070051304111401c1c0000410b0540701040081c401980b80c42100041d2086004101405c00d60800031395550304100d80586041d0700300480d8200046507038210034180c9030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 746447877 1250 746446627 746446637
    0x2030c040b01050903031303051009110d21120509060402010f0809070e0c030402040c1103091513060c0c050f09060120070f140f060a0c050a022e0807 66
    0x99800400006140610440d81400380822051070307156001c2c030052201104560800d105c503400c500348989030158201a9002c15032404032110301060800307030a2114000119a0240d68446500d0b01d400030742e81030190001101291103a0502642c0c03c0802c0780c0a402c42c0202c104170b0740e5178500b0300300d9641d50141c1e0080e011900054241e0151842540134507405491602150754095883d420540030300070450f00c0c00304030301011003808114034041c01842d0354042c0303030328005144030014140280c40344111154148a81e4515404941544512003a18241240c1d03018203006035980d020040c012191421048542c9500c855000c50036141c40400d2003021200500b41d42e01d90342d00d000065800000070a0391500060302c0c1c946a00c0503110410a440103400006004000540341c441000012004ca42c6491300c900c1442030010f200340c031080144c80b4090b1507441d0150050b9218100315007003d400c240080d400801000d00ca80d49030300da480c1120703001000c043c1401400e1502980480d0425010b41c0c030000020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 746449127 1250 746447877 746447893
    0x6050414151606060e010b04091a1012110c030c1006060e0609030316031d030106080a02040c270513050601081503070905191107080d0203070504080d020106030b01050d0203 76
    0x20308500b4650b02035100300700c00104603071110340480c0e10440903402840041e40000701442540c00034044d80f685101e225640c0c03140030003003000249500300300d1082c4900300280c400c00d15520100503001074428207203000d0f0150380c0b28881c120184e00c0e540469001296481000340c2018014031303074441c0d041100c0132a40d80f020b51070383c020200440d55100b0119240c4c1031200780104000211400400d521700d42c07080d03d4502c2f0901c07410420380b082c1ca000b80c180a1003645000c4082141d504041108400c070359046800062032461701030141d406000d00d800d0043c481d8003244400000c00c1900340404240c403000c03242000c840e03442080c03032803d8580440350180003404d6000801c0030310103950140e461950b00101078504680d1648800f000300c60045900c08040e0500c44010303c3c0e002e00c2480b03286020080c461081d0b16108140d2189080d1313210304007400c0981540007001a102e544074000b0b68001d0000070f401d40c1e02c41846168000e01038105801301b910803550840001600e4640501e44405140e07002e0064540c00d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 746450377 1250 746449127 746449147
    0x10801140d0c0b030f040311070b031305151006080a051501320d050a020309031617030106020307060c0f090605090a0b0301030c08010b0303030601091509030503040605041415 77
    0x405100008032000c010b4804089681005800994440c8000d0781c100b03045460541070040988104c045405001d401c44d40302840b007490480203e03540030280406c00c82c003d40340ca140c03045c41c040d00400c2c00c907028103c50b002d0020481c4541c100c1011905196211200c64030b500500000700e0700c084c0c44d00440c04242c48a0f007019540141c00c025807078651649052a036045e050b01c807440304c000302c03411980718120015001008042602c03820360800300c1101c0450071440c1111200f56030b881071811460519070525174004c100f00260b0a010256070b03010803016100d5a441801956a81000e04101c8641d418080d920075442d2007004035104d0000c2c40da40c0c64035014a019001e1310b40741c2c00b880301540c00003010360700420340301ca151008500030361140c1c17443d0001e68584408a401c4a8804031094440d400400c18030103280e03440107004c401e44110390711280300f03a100000161900901c6034801411400007180014217590010007520841d1011b0010b114a000e4035400c00a4082c40380b2030029068a06000507010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 746451627 1250 746450377 746450389
    0xa0b0f090a0603050d02030702012003030606070602040503150405100c080613060801051e1311060c0a0204050f07020c03070308031513150f0902030610030e030f0c07031101080114 79
    0x62541d10000503680d8903900c1d1941800791042810b00542d100003810011540d22035a820500e001e940c8200008100c5510742948904c0060038030f9200e2000494039130240718007541120700805004040303c3e0758800606100c0c101c000300312025134203406684032005503222113002d0b511121a03070355039a4400ea540c05080203180d1095031403200456903128004500807609108040c01a003680900c9542c5140c019500d000003c0e0080050145441c0020f40600155604039200507c0800319002e82d201c50584058030b240401942001e5031203070800052001d10740c003002c01103000b91001d5007a01e245a00f06405d140e070f5a4a07a00c40204000710410015401c52450710340248142030080000c402445c0103071b009001d5605c81c2c08210103043e0300342c40420018401000300e0004241c417000541c11841c00e00c000541040c2e2034803441003450b80300d48030540f281b0414401c81d82c0200e4454440d40c0c496680d15051560b95842c0c2c04101d4401c0e115840100d015805071000d103040b40c0080c0c0848064540b0034060001e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 746452877 1250 746451627 746451631
    0x603060e1611010906050c220602070303120e01050f09120c15040302010e0304090f0f09260d2a0816030c20011406040209060a050711060a0c0b0a0b0f09 67
    0xb03000d5503269400800602c01d805024043c0c04010713451510340492031101c00f2a0181042c5001c9103d090701c0e0300f0040b85402080000c101c030340500b0040c00d89503441038401d0280c0b0303200c030415105500e840c00708071024803211540d5004854040484482c04541510b0710018880e2000d445d003254013600d524070415140d1080550701900c640300200300c4000b600107203861034210303070800178280341c4980c21203003011000c1c0320f0f0b500761102d030750000e001c001000c1c3c8817444a10b0715440c1d1840c4020b403221903a4001d034000012100403040f035030000c0002440b00d52003000351001071440581d005c107512491035160340c4290340c0d0f1400303544480100c0d40c5441d0034502c290000c1440d64411000e006404080c0b00d4503811444100503c0c50b00b250000ca030905031030f0b0041071403d00090500d442030b032041c00b48180b1512248107840c0e0801c03a60030541d40d903030082c0c100803040110b008401603001000290b030039000c41e4040c1e002c01180d44030350130010054499a440e241685e80d944401034011242c01500d0240e842c2240b2026 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 746454127 1250 746452877 746452907
    0x10050406060b120f06030d0806240c070509060405100b07050f1204080c0108010326040b070525030803060f06091002161a0a08060102030c030c070603060e16 69
    0x803002c0d81c1d51191011500059481d5066031290001c1100808114415550020b021030103400c4410042c04050003480380640000c0c01400c9840c5c0c0010310300e0181d016101a1003509001c6034580c60000c0741c1c10740c0c80e0b0290007118040d90111001c500f0900b40340c00b90038010f8070b00300005031000d03041025281c0c2640040c00140c40a11549154220410f02405101409035079004401c0d075881c2004003007807801c8284007001d1704004000c0c00400218800301c56039041c0f80801c441400030040304042000d80da0281340c20810032000c00150190400c10f001840e40710080c0542b8442e80071151340c0e041051710001e81e20010701101c9041000500310324005049a00b280d50040045040541e07000200d070a1505500421015a0160792059110100b0001c1c0b00018441038400d00c1c25000a502800e0b00d5006420102050100d8000840d00303a0b80244142c2d8014400c50003125141d180e4600401e9031801c152150402280c5070400100790900303003001300c1d8401e05003c3c00700c2e80500c2c0e00003821503259005034484 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 746455377 1250 746454127 746454131
    0xc050c07050f03071d010504050c09130203071106091b03060c0904020307030f0e1501090c3507050d050a090b150f0a060e18061c03140d050414010203010810050406 72
    0x1003004d511400200702c0b5814100c120543c5503047c101071108403440503000c000c41c41010310200c2129a030340140c2880d0300c450b500b03025031030b51a8840c050705d46040e01c0c000162180030300c40c108008540000340304404090b25403484c85102048034140342c0c036903a060716490701040003003102c0f00300c0e803c10b03400a603003000d00c0d45000100d4413007668240c41103c2d0f4090007140d01f40c00606c450a0300301002591036025205480080103580b140c00c02c0503250a11f070300740319980504640030020101441c200b01c607800c1040560a81d4051400910090007540818641079103d8030f0140130504800040c42070f07141c9640e002401d86105d031551182441c03400030342c80d00d0701e901101c10011030006803142103180004251646510126180700700400600c0b0340070803001c000c170010900822015541c2c8203c100f00e50380d100b210038200c0d007841d81030131241e03030f035034000205260140018040000c00ba5640058071440c060800021900302c503100603070a0340700078401c1107966032001c440e107021940c0315400942c10030312070800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 746456627 1250 746455377 746455379
    0xf12120c2a03060a0c0c110607061401091b0c0b060a0b13030309051f080c070c030c0512120a0e01030f0c17010b07030807030209010e030105090c01030c050c07050f0307 74
    0x40302209007407448061040d0004030924451424200040d40e00800800d6060050580220005051990400e006402200c0d00600304045844440407906242c1e000101803000d440040d0300c840d1002420f1040c4004149000500400c83c0d10381c0100c1c4101d1400790342c0d80e440b03844154990740040c00001e080c0d140c0c48288110006011000c000003400344c3c208803002c50320898a9820301034540101d690040c0e0160f072050450110171f4110680c00d0640403020708100b02c054494440040c0203000b40c2d04000c1400c201418040144004c42406030103c1700d003158100460000b02d0019038a843c40010140720301c21050002100c4103015503c040705030302040c900060141760070081482514041000d42c400700c1c15003004420188802c1e444280504210b034507407480d24906540c01880c0010041c8541e00f0194007040400f07050303101e07508221000c81c005000340f001e8280011110303121100e01041901182c074250851816071b000d03100b542d80070354505e0045c2c98141d2a0205000181e851049415130600503000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 746457877 1250 746456627 746456653
    0x2606010c02101709060709090e03040b131a0d0b123012070e1002120d06150f0e0d0308010515040b0d0603150e0307021219050c0f12120c 60
    0x10881d44500c141314001c02060030010409003a48515130401e41c980b07811310070006032482000048600307c1e0b080c00141940e50880b6007079510414165081030002181e454007498804030a03c020f00441e04070300c6020411207044508004410030351184915a64100c504840c0c03480300003036210320040071192031120b07a44588628980d0141e04c1004074100b003070000c0c1c09124183e580000c0c54483c04806560500b01e44d08500d5000c0c0d6116001038007034000e42c800251001c0c6400c203680119008041c41078001108609090004d0070000d601f42c0820001070344031983c0306039842c0100e921094540c061715600660b90812040c040000d403048414004403408001c00038006840000501d0701400540b400199203046180101c00c100000c0c10702e0051a080450300c404599020080300c14543d030440c1c100100f580103042403400c0089164442c02c183d08800041014020b02103107a801c0c0803811195051252402801c204002c580c5501c200107a50011f200c4003024a81d05000300446500783c400c0721040d1700141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 746459127 1250 746457877 746457917
    0x1503030c0d030906110301030803040b090c0a0b090108061e01050918070f0801050306250c0510021c060f0303050304080921103305102606010c0210 65
    0x71140000256100c00420901c061842508064082e5086039807070355141d034681038400d0101401c090007074000b580c0803e010310002c00400341485409400407a40d1551641c40f4082d41d0407402e40d0350b000c80d081d130340002d01d286000e0300010111400418241048c0350002c0046038260010100241c0050402d200c44040140900754240f113001155200c84005640c2c2c43e004002c483c1c10380c03003540298802420b001e4074075900e0b6102d0300e21201007800501d0b421003003441214882500c17080900503004400d6512810703900c0e600108038800312014600078520055020344100c80340c1c0c3c0310741c482078a181c040034000248150b00542d0854007503e1000e0801a03400c0010b045460211002d4a40125010010345150410f00001107407948883c000c004040c10f0b05084402e1130105080200b250380e0104480310185000b6404401400000c0c021250500044101800c01c103901c000304800070100d40113107940300301c40c902d600e8402c0f24180e50751102009180e09104646000e070550b9001e010303460700c2c18440420b907a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 746460377 1250 746459127 746459143
    0x9020a020718021306050a1d0315040615080a0f0303020f0c0d210b030a03050c0709022d03070e0108041104050f0415090b130c0f12020301231503030c 66
    0x8001682c5244284c4e0324061520603134401810311000f44828200190040000b907003002c214500315461a203003c0c0003906005c202158022078203128070602090003695446204178101007010103108a0316120983d41d25140c4000050041d1046480c1c000000c2c406d8005d001e0b0000c11203840c6041c420080c6005081043c5910f1100020301c60b240861010118400d00c4081004c2042040188071210350201e600c45c03202d50f0001d401c0c408005200310307204400300500402000d000c3d004644420b0020701c01c0f61640b5001d010328848a00110080301414144021213000d0303112900d4481c0d2402d2034400650310008000e00507502da00d1b40414920701900c1c0d03030154500c12800c2c244144a14035180c50b2458403e13114070f1031508024031740521100000e825072103158100709030024041d412079a910b00307021110860f42128030003042812000401d40180031405072128400c6000b80902243c5031504640400701d40304003141e68a125020410400c900c0420544041c4098160b03850650080c80b16460007403a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 746461627 1250 746460377 746460419
    0x2a0a0801020c100501120b0c130f08100213090c0903020603010e1b03190b04060503010618060e0c03070e010207080d050705010f0209030a02012a080c0f0c060409020a0207 75
    0xb40e50100200901c0100f443d064a07050403c0300d03505114500445110b849001403a8000070740100c0c402140000c20750344a42c1c10380b4200012a911005da805000086100d607c070385214204038011160305900a40300240703105c08103100c03a28a8000c500001e090803501d82c00c14030080d0140480541c541c180154042c01c0c100d404000b41c0e060503501000c0381040414112480c0343c060082c07040c190805245c80c1e02c04140c402010039400440000940146080e0340580da241d0b203410000240f50801c0030400c00100200300e020442550744414108224504641a0242560403c0000e403100d015a440c481046010b01c121b803100c54031002502c1c5441030818440c40401d001190810800009006120040d8184003066042101c0140030a0303448000c1c0741c0090504c00500344c0340300c1105181260341490401c040303030001c9610507401d014050345d004101507031003406507442c04200504002000c031160840034080628092900807070000030b410070302e400b01c1140602e02001410344184203000300c0e0324a03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 746462877 1250 746461627 746461631
    0x816120603032d02031e12090114220311100e010629030c031b040605190305060f04150503010e0f07060807080f04150510060807020a052a0a0801 64
    0xc200044070303e00f45442015551101e0140546006056000c000d44000303034802c072017560780346180c80518a83c6014103404071480805000410100a60540100180510a00c8221815101d049a0301411129501c1210814805102c14800644981c4800c012142010250340e1050300900016007590815140e14413140c1d1905c85c11310005071118049001406005680805c0d002109181d04041c003008185082c0d800340170000038400381114a641d80d80303180421031075680310f48940000e41030390028021601440c005055211805010780304240c040c0324000d10704101ca004100400000e04104010144814040500000c080c0c4090042200701752035400070308000d2541200003450100141d01400410449106020380e0740d41209400d0703004078610711158155550743c104042046945210941541c1c6490104443d20361320090300303400d648040d61148150345a4a1040f60345101a0f140540540c1080645882a070721080c4c6081c4034019041004039060a0880060518000d591010151365 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 746464127 1250 746462877 746462897
    0x2030f060306130b0c090a03021003090b010506040509161818110f070632040b10062c0d0503041a07110d050a06180c1401081612060303 60
    0x440e05104450b40400407040c400d0741d0f540c0035281d00b00b140760007a140c1e00b10300e04000f400c0c20880d00d40b810704001850b0003030080c81c0e01685082008000f8189054281d840001041c00400c01e4a001021281240c100402c055200c0c0c403843e04800d900a0f030b0b50541d200f40302920b610b81d004e000061000718000c0a11174404400703980c038541c50405a4042c1e000d0382c100081c1c2007001400d40380c290b800b81c0d401c5a402000010300f4030304061180180081180e07003a503c401c010400c6000c400040e10a884c800d42c0708494920981d11000421103804007207004e8074001c58001101d0b801d0302e41c448031003007244403170700080030030020b0164000c14142c01c0c03030301d9040e181600001008c0c01041c0d05001e0025003a0351412045141c0f06545d1100c0044c0818004120305c80c10300c101c41c0d4800e0210130052040d4981e0004d00402c450148041004100c9000d28421100301e0160032000803409544100d454001806840390f03d991f54a41c0c20628840c01110300100c00e1000912814286a9980c4106c1c40a1407080d1900c0c03030700c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 746465377 1250 746464127 746464129
    0xc080c0301050a05040507150c0c17211813060311030f060606030a091406072a0206030a05090703081305040e061902090d0213021e030906040b1902030f06 68
    0x2d500000c00b800c0140e4100800d03c0001540042c0c00c004440d80d42040c910348962400b0b0899004c8502440580301d82600d00b4080781e4900064190070381081c0f110102e915065507480b01c0d00c4000c4012400e00c840030f00512080c400d80d19034510b006c03240c0d50300406146141041103154030440f8007540058a1102d1443e10090880c00c08010604100b0000001030045141050014443c0d100007044001d1198590f0380c0d407010040c00c01820f40c50060848151600380c60042001004900344804546000321841011450500d040d5040383c85150040c0c86c0c0d503e5552045c0100e00601000342500445100d45400000450501c901900780340208118002d0368515080410058810555007040c0a03005101400081e030540c20400d480e14003440e00160700c0300d0600d00001c842800c0c164000e50003000058000c00120380b17650040c43d1060200c0300c0781c2c200c07150403c0e50800d40d01040300c10000d40d40c088004503010503d0703821440c0c0c0c0850156004c80d500003500c40440103903003055650000303020607807085c130540d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 746466627 1250 746465377 746465381
    0x207020a050a0f030627110a091e090305041802030a0f06140d06110a030518010605060a03021e07060b0906010809031206210615010311040603020d06030c080c0301 72
    0x105800c40b4480410350030a4041d5180342181d22008202e244e031580ca014114940d125551131403411820815441903446c100030245000126940e44a0b072161440482c030140c0034416220040014200030701010005000c103401441c00744026010700a0910000580000c80c0d4200070260070a040b01507180d05211a055094070b1a1880b640d43c07007410031106000303408052400004203203080b1807552100038241801b100418a0048461481500052024034a50180c1040b400340e9107a403c04581e40b007207c040c582c22030728140070b4076500c003008208130b4107054826009001c1000c81542c480c0480c1a98040d05d000c039503c180d03000c4480a4403910f2414003468400c060641c414028204000545080c84107140c51b4032403c004071000180b000080b4031302d0780300c2070024210725400c1754a80d0a043e0360840490354500c0c0c200d4403803007003000600000d5825407107406004010000c103480507080038140385058020f074001c0c03030811000315a2100000041240b00801c5d0780123002c08c0f40034000282c855002c1c142 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 746467877 1250 746466627 746466629
    0x1a040e0115110309130f0b10020c01080108011401231923150a020a020d0b01080f030901080a020306030a0f080901120504020d020607080d0f0506100c1109090111030a0207020a 77
    0x54150030900803410903448817410007240e00428100014102003500720000185003041c465030b008000f400d00e01c400e076500010b000310b42c1e00c02600d03555107603aa215481802d80300052140f88118410000400c1780140a51a15900e943e02c0b80e000c140804458004c52400100403414401040040300c3c01c0020b5400c0c045d9855080b4500310454042e8041a80481c0400d03468640203000c13020700252151650703200b84260004aa4001d100360b500c85814109402c10203400c0c000e90010317006051a10f4080301c400401c0780c0c8800d406031600c0c00295240304040c1c0c02904010041034050040d5240f03000040c88a4546200c03c070b00c1203540c0c5448100f8040018200641c5040f0b400100346003006000c09a982c50302c41c1c044841d0704554060744d0302010700e00008540240111822001c0c20508020a110090b4100c00d22810040c1e8510200d030720754640403190700f070b48001d01401c0102845030409590500c0e8034055408150304001107044402d400c0c010302d055104a82d42031400c3c0d070110b420000c62070302c404904 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 746469127 1250 746467877 746467907
    0x20a0b04210e010828020409020910050c150604061d150f0a050d02280602150c12071b03021501080309010f0c020d020409060506040509070f1a040e0115 67
    0xc2e2003201c0c11002030607840002d01604200d1794005000712111003528860100688030703440035134a03070341e4451465010790808003805104002d40d407440720405108030291900030001c513004144861440705015019880500038680082c2c031410049484003181d42c1c0d0700314140a0078a0f081252801d107103085440915980c460f8441d0b00d18585c0e06201e59a41c3c40310720305445080b2190401c41c0b2551001500100200b090060351a550030b0803041038400801210040360495002d4404020b45600e04410b006030866552401c44410301100a02048444410f50710641a040caa510b218a41c5540c20f80c000042004a005078070a48036416a404040000b40c0101000704c000c5003001d0807100080d007580070b11840101000244512030301555609100c0c680b102d900a041000036107844d040a00141504450b400e00545c24600494600b03100080e0510440c2c401544030440c09040c0005801c07401c41c03000d44800c181c1824400441e50303802a460090003004a07943c4a0483c81421380060045034891201c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 746470377 1250 746469127 746469137
    0x13120806010903020103020315030a05070806060409080f0d0b2206050901030819260406051b04060e0607060c080921041809060c030623060a0302030403020a0b0421 72
    0x100403640d810450a900303896090030b01503202d03034400c0d51030f000c4201c291010700d52501c5001150b01c04d210004c210701041c1c45034003080c0e8005650343c806100a0310990400142040000c004100071038041e50040c001c0c807803070707804042102e40318200022a4040d000307a0060901c0f82504d00c0071420305492040170300030041a60004400d6265840303201c03641c00f481030100005400d806060800c10310881d10030031101d0800d80c0046007510b000c24006400c580444003128800c0c68000030600d14a80c0d1300983c0c46c42e544a100ca070785402c1c03c00300201e9001c1c03107024070103411640a0141d00c00140303c85c01400e0302c004d080c0d44c541e485858031a00c164900181c2180245009a00c1481610b80c0c02e0040704860640b900142d040f1610350b51204007034003c0181c0310000d4025460001480c1c44a64075410500480f5007110b40d0000040c200c1130001c40c0b0000c40c10000358050010499480303524004d4015540c814046d0054074114019620361b6070001134100c0782200e00444000340001254196044072104208a10308 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 746471627 1250 746470377 746470381
    0x30138090906040305070c080303010b0a090e060a030311031c090b1e0a09080d0c0f0e15030a0504030e0604090504051005061e121f0b040b030d030e010b09131208 71
    0x18090b00c650014101030200400003880a0034003041500000007020343d0400c4a070740703607500d070100c18154002c2d441d82400a001c51000199541445d240139019140042802484a00d16074080c0d40c5908096012549800188801310302080008110f040c110903440d00460300c841d030761612000c025002081c590800315021600b140030203003c5881d652210b10740c040020107800c141010700031809010a003c002906114844d01140d0b8040710003140e9003000d03210100c0c409989010446591101c070108144851b0500010300c0a81840d0802340d00140241003c200a01114020840c56401500300d0007a031034680d014401004800c00c00c546151809074020000c3e8108840090010110b01288480d010300c1d081d1441416074400f1103040300080c1c001c00b20b500300c2c0001c100b9100c074030380038105035030441707180011500150405000f02c1c052510010007903c0260314028003640242400401c00c5030030b640e100142400d41e190f000100380908081d000401d011034551614013054100c121010080100c07441c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 746472877 1250 746471627 746471641
    0x50c04060e010905100b2106061c050a020c1618060b0304080c16060e010206060d0507051903060908180307031707050a06180506010e0903031503013809 67
    0x990724151142600081010384840d0220300c1c0d800001c0d0014444a00c000658000f605919000300c9196001c83e401800e455940e20304000542c041d402c80d07400390400b8611000074550f0160320669000502400043c2482400341045241c0b44046801c0d605010711400244190500050307400c0c1c84440080d02440502e041908000d224000500000c040c048040b4455002040500a43d0400b90103425201000da80c1d402004240907021418140580115000314055003800000085610b40120081ca00c19140c241408140030029114801e8001c040c000400082c07407901442d401d60380100321403502ca00725841c0c0b010702c40a42d00c0f883c51103035009100c10000114141051b400501040c41e441c2c2c0c90704117504010f410600700210040c4094a8010001c801185000441c00f00038058170455110382c5e203401c40304d0350100066a59003125402400000c03907903070700c2e038a1180a2410140000ca80204082e03024056145400b85204401c80928803041c2c068014951380d90010000302c50300c040900b0104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 746474127 1250 746472877 746472899
    0x1d010b0a0309022205070905011d2b05030d05090114061e0a0803180d0c152106081204030309030212120f0a03151410120e0307050c0406 60
    0x1030410040c552501524015580c641200b040f00d02c003215001c2944881451a500003803030300322100c501042c2e0703000005c20380b548103103c0b002c0b031824490303e2528030400c54420403107e03440450344c0302400c00000d05d01401d41ca80b00e28285000b00c0c42100210303180c80c0012101416601d0041122109030301d043d5020210750920010213070040c400760782da001c8900d906540480e00b0500c0241c1c241d08020b5121001a42d148008001c2c281284d4000012402020313140400112000103140a0807010201d0024484100d84000c01c01016840d411300e81111307580348803420100c40101e080c01d00102e9403418200840b200038441070380c2d86410b18141078a01800c1d55000740c42c1032103600020b8016003483c54580c0d0205410450002220218100306464408552030f119956005812041c0000c0c18460700d2003410003c805540d080d2500f610100e1303420350801040c000c1001c030880e100b100f048548640044d100030a403003406403a00781d0401840e5618480d003400c0e403a101b922020039004500d0600c0c00c01c03c8403100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 746475377 1250 746474127 746474137
    0x1202030604060b010210180b060a0e1b0d06060f0e0303040b0a0c08040504141e040206180f1512010f05091909050d09210203030d020729011d010b 64
    0x40b01000968070304000040b0701c0d10201d541c0340c3d2122480d11000c10391070b0491343c02440820f40320702c001ca0a20f0340c031407060010808852140881840c40314010070350281143c00a181c59104000102e0304050111082d4000d0392043e40c040c02c04070b103805401d04034103507000c000c41380c204005500843c601480d10640c01114030070702c0505010007480b160f0100400c2241401c07203005280040c818840300f185400c900496410959076000c2d0042484603441400349003c07a10380c0f055800400250038111031080758180101024101c43e0b2140a0036a241c0c1d00d0b640e100002d9080014203c941d548481d502704000d034a000c0b040e0400327800c2070b1884400300556030b15610510380c07000c11004e02003030f0083d0f0142000040c11050130007c015006611b10304d000c5560004040d0202c0c2c414550010155020911030700c07800700c0c1100081d406403c03c005210b81d59882c5c2e0024000288191b0300e400546580380c03911502511021101821610408010840341c480034152003080907408200c64100d500d0821021090300c18 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 746476627 1250 746475377 746475383
    0x31503060601031509152d08010c0e060307182408040c03110303040e070503070f050c0d05130b0301030501020a0915021c0e0d030e0102070b0909130609081c061202030604 75
    0x9030040d0720001b00360006c0171401402d484030ba0700011200380030405221200340c0ea211015425070000000d42c100140240d0394280c0032a20754000450294060120f181d01c001d02440038007008500f6000410301140011000304088111000007040c21180b2425100c281c2c00054100640c81082c04045480305ca81002280d900010000258425a022a0950050307078003100c440d4408100300200c00350400020b510400199540c8100c1d828002030644160040d0040c2013007030760095038207018103801200180f1102e1000c1e4484d0012070340d02c940004603030344241c2007100c2903500401c540c0d4519401c0b9201c04054003000c0c800084407204401c00943d6009420003d0301d14030703c4800d0f04070081d800380b440003081038406000c000481125080160006280c007944500610460300c1c00100b40001070162080f100d001050300845840c1d102620801000900085d6002a65010001c00160f080c0008000307240f0701403400303407100b00e81d15090780c1111138907031101d13559102c0c13004c43d10f006903000f16000c0d60080d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 746477877 1250 746476627 746476631
    0x50a060e130b030c091003050c0109030302031909050a0b07020f030708100b0402090d0f03020f010605060417030408070e01210b04510b060403081608031503060601031509 75
    0x1600c0080e02d054141e40c0003031740000c0c14100b44558440340716441d105480c020320441e10600c2400004551100840c40090016082440503450142c4120740c645c40348091440d0000310152070300000f820544042e440a20000c8002480008608001050780ea182004501a008113494040d0442e110910301180031101682c4025500a44d99154182c0c1c3c40a41b015040c5040203500d0300d40310b810f51840600aa0145c0b003162007010280d00140100c90583d1000340c03403107060901d80703000b940400e4581d4418000e2400140b0000c20070040c01c1003084000d100355000d01c82154035000c10401e117200404110030107003900140c40ca000c640780c44c2c00e144d00103600105135030401c5110101c1042c18803a0300c04a0000550190448040d03914440806040030300300f075502a01c41c0c140f02900f4003120107148050b41c0001060004001107000900034100407003800c60300c01c40202c801d544445481d401210280d51030481d1100044c0b481c00e00700141540004282010400351400000b00c000c3d02d91113201c3e00f50126 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 746479127 1250 746477877 746477891
    0x90904030309060501030f031209260705120901110303070503010b0d020d1e060f030c050409210512060405100902030c070819022104090209010908030d06050a060e13 73
    0x10710a51042d003040742c10003c10402e03542c40c0c1c07401c1001041d41540907000140c0015a8240285840c490242d02d0f42d8400fa80d80c981c002e4154100b0a103c8450000c42682035060140c6030204505019001d80030940c80c4110303669141040024015580c001d201002035031040c810407170155041411241540c10500740c0c10344841d0580303c0200a07215401001c5406410942102040e5001018210890088810900695445040d15407c14040d48806450290f800d2001c100600380703a80b00d00503a86c040e0690382d20f0000c0d0f68040706c050300c0c00c1c100b06d140094000110040c50401443c0641e4201c9411542800315040c001800c810001050044401c0c85d82e0000100f80201c1405040b9a4500e52100b402616103203051603504451080d5100700b03015014040c0084008404d825064440d80c0c840c2c0111418517080200c040001e401050209050008102010032030344010400703001a1001880085011380c03d000504c85002940d43c00101030281d40e0090707108603a41c0008141c402920341e40001241 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 746480377 1250 746479127 746479133
    0xb090d08040504092f090a0c0203120708270a1202190f0203060a02122a0f13060f0f0c06060906080a060e0c0f09060a030b1005011202040b090904 64
    0x18461036100941c80362034000618100700c1c182128080c8210300d03241001103c901050205ea00d80000185650f000c0c80d0180001d80508555220310401d404502c126410400140c007a0340c82d1480a603046130202d500001041012652100d0103c030000840350440b0400001d407a10541d900010a0300404800080041e01ca0040c4200280103041d91001041204003040d4208031042d4825104240e0090061400160300304a5500881e0002c0c503110756050601d40e22005402c224041464000961403038568011031051808000303021b4018076030012507030307400d202803003881000303400c0d800202840006030396901195000040144070100d54200800c290640b458140010b1100790010240c1d01d2814101190038003000684000045c4a10400c00c82e0344c82d44211583e550461000d01e652000b1020f6048419050a508498000501911a06a4644943da40c00e41000202c400340785681e41104100103039a8054690860004001e400310302d46420030203600c0c401d104140341c003030203440303410301003020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 746481627 1250 746480377 746480393
    0x109060912022b020f15091e03060117010506030a11100201180f05150f0a0b01030e060a020a0212040506070803070c06020d020d0c180302121509070509100b090d 71
    0xf0340060981c000d9a08000c400b606442841c1840f0507030241302e09150f81d601c1810320f54808240340e521312105ca4207003884602005002c0304582c103807840c078492100001c0f03802d440402c03101e40a800402c00d1110070100010b1404d08480380100060720981c4060300400214108042c1070f10380c506c09440145141030fa00a00ba400f410b25008011013900d103111010341400504009910703c01d101e40103032002045112400340540c2415113034609022244d2003c0b8210742c0590b400410011418100401d0840600710a5424070004407440e5006c039800241c00c07203000d9030510101a04030002581641001c1c00e100c04100d95020f10036008282c6100000410b1a0340d0161001150340c0d540034078291b590703c000d01d654502a400c40710204000074201004090700b03134050810b091a1650302e0030203035072003480c1d902004030241041e417000f031303081c020344030040780c103168910308180f14075002c10082c05401d20f000c0034006c00071402080c803020781800010070b006400040d411202c0c000c000b141c03814440401c074241080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 746482877 1250 746481627 746481649
    0xb1902121024080601031508030304030914040c0c020904020102011d010f060b0301030203030715061802040e1308120c04150806030105010906080d05071e080d0b010906091202 77
    0x3210806001000381c81d6480452003020703152540941c11010012106491000940c2801c1c076010070442c60000f180d5500c07a5100803070f07a0b20321100b81403290355606c0d00e0a065a00075503040e00001e403101000d104011111440c49200300d81620200000189184002d069241c1c2c09070081c81682c007280402c003568400d41007101e0f0b5a078800384600215102d0f0000078001c0c0b89000d02d000d129810458001000598003007524126900034000e54900300107030b6a80310540c1510551b07240c4c4940c0d00d0502103201c440850300403202299001006039100d041100711005400020302141d000741d401040240020312a105880e4204108156800030741c444015410460141e5000203080b000400b411503041980704000500840c01078000300b2450b600d8568950507070314507014046e002d9015245400603030b842500202151070143c09514840e03a400a4004030540503000d061351914800718000012202510031072110003001d0a0035035805203410030103002c0e06050705c10462041c204000540079504e8222203c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 746484127 1250 746482877 746482897
    0x15040504020a030c12031d1027080307020a08010c050f0c0708010c081e0c1e07020406120b0a02031003021e030a050f0706020304142101050a0c12090b1902 68
    0x84000c9840e1070000c18481858030301600000c400011801d45400c6051f260074002038050103500343d411002c402900d0082d400a2600140c10f500005121817000c64610784000c0c22400300a10b80e56400c034010013113600c4264100c0521342c0d1400700780c00b0304680c1000c12a1540886444041d407203c0000100ca41050150307880000d480d400d100d50003070001d0344015910300c0b42c4200c1d80700000300c95038842e188003132040480b462506480d00b04240824125444d12200794042400b604510300446a404902a182d00e68400800303403d0b00c10b520010042e40a50041c0d0180c4405000c600f58501f800c0c2c2020386c103040d0310019002d5000505110b84074a030f2611a0100f10001801b10740c07a182091404079500d040c0c00d481882e250052a0740400e4851000c4104e40072222061105240b40e40100d04100443c00481044100c000320b00c0581e11144101780074492080007182d00010300d4180324070000d014120f20b043d42c4024107103840d0072800091900000c0320b802c881544940001c0081141205000b44192a919 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 746485377 1250 746484127 746484143
    0x40e0a0804031a09190615120f030e03061003020f1512040c0501030c05090f0109051e0102070f0806040f02062a010b060702010903110310020c0303150915040504020a03 74
    0x70090019411014408051024110f003d42e50f9018102e92540b81100483d0365003041c5005410104142d50800d003860411450310740d00180c1d0f039001145a00e03000a500b21462507158111805168101e904495410001d801030b02c541c0c50726242c421b130360b21110b020080c1718414a10541015440e501c0301e0510141c980f02c0419590525030000c1c0c4e240f050102c031708490500d030703405000c10954424022440302c62516210305003013081100802034840e011004280c1040380f1a00c0020743d50362210083c0c103000000c0d07080d26a0641e6158002414100300c2c0c0c2080c4004504844100300c40710b40040c0e12035010380c004501c4c1120601c2440010340e0383c4219614880c0e840d05001d00d00010b003603602252204030401e01300801c2010605014001c441c090000d020380401e100182c2040071405030012070070204001001d641d102c42902610703008a80200c10481959480402007004400d0340b150b40302c561140c00c03200e00c2408d14100481641c042002d00c02d0b00d02440e110008901191160804140603613800080b17 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 746486627 1250 746485377 746485379
    0x30403030f110a17041403030f010906080a0305040e090a080c070914040f240f0b0f010207081011040e01121e2006070b0708010f08060c0405040e0a0804 67
    0x4020003400a101241d0750311464000140e00c0120032a0884040403c180c0319490391440803589204030000091090703d090382c0b2903004146020050000f90710685541c190b0308565410f00020408886542d0810b0005511103006c40001c2a000301c180d03001c07070b02d0944144c5030301d6445446650502640f9080113003280030101e40312030186800704401d0282e42c1c2c084000c11120403840c40d005445501560080e1254440c11140c401240703107200400101c455000d000d1801044803a503110403140d80b0241c4104c600d075100b8a0408a203444480e01821140910041607110b0a1101858455401184031102140e070f80502c1b114048080060702e0007042c021503003507610340c0e464a031031401c2017080b0012100f03600002c500004a0885006080ca074541025440826140d100c200329400e41050b103849502c680107005010006003080031251085a0356500c803516949401000c12100ca865000684507402140402c1040100c0700d099900302c0d182198085038040c041c000c414140006624044c12075100050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 746487877 1250 746486627 746486633
    0xd09020d0c0b1c060b0708090120011409031207031808040f0806100602121b01020c07060e03010e120906040f080f0d0c1a1b04240f050a0c11060304 65
    0x2804903507400d01c40074a08143c00e0810310045513858002c98003000c100380802404100c1000150101d0380040c10403001d008003400e103801003041443c92400070f9130f4507031410003014104450400e4002e0702010007141046080440c4603050a00240303200708050361550000142080448820444c0d50025005603580b502e84501081c941941d000740303c600d1081c440811000250361b010a022100e00e503020b0520440d0040760200036600402c002c502c1084080354410a03000284010300c100003449000341203140c40c202000c0d0078254505e96145c802c0c0d03d0070300464860740011402a815128460002d0b54070710341d920008030316000d03a400284120342e40c8280031a10010025500041240c04011204400e000350f400300d80c3c4010000c00141000c411050f00f012031030030711040b99001514038036800190780e1030304409201c0c0e070010b5014400000e91800c00640c000b5000303559101004003072400c0b083d4007a2030f910117841846029440020454030070320b0081400f502c00c024000c0140d004216642e282041c1c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 746489127 1250 746487877 746487899
    0x6120f02042d0509090a120915030c1404080703060207052d0c0405101509031b0314030703021203101208042310050a0e06040b040315060501050d09020d0c 68
    0x42c0b000c0319041c228140120302c91038580342031031055220703030001c1441c1e0480c4e42c3ca4a00541a0703440503c140540b401000c80c03a8100321041c2c65a90b0015a400514480548001082d8804028241087d45810071051140c0c2c40c0224240040e6900f00c18096501d17251454441d24000460001c0c3c4290300b46100b0382003104050120000c0180000411180d94108800410044234010341b411842d081c11120100710884445400c2403035900a800c1698905580c0c2d226030101c06a104400d03600c003050103501344200b00c084030345480103225500085003041d150366400380d40e4044403403031025903480220008030000301e50308008016020068a0102880540c5010340c0560010301170851103568450680001c191240f85064441000410b0f251001280741415540c0d0303880074014404104010307402c280b02e030315450010401400742e60166035403940365092001001d074042d107001034150b043c00020401c50303920006407080d45001c0640041c54152510000306007d284042c010283d01c00d50b07100049a2120b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 746490377 1250 746489127 746489189
    0x309030c02040906062c01060c03020c030601141903050c04091b0b0712030e0c0112110c24010b0a120b041806050711121803100903140406120f0204 65
    0x50f036801032150b9400c5404106d01c00521480c82000c80020300400ca01c61081105e000400e001780107803200806402d0210b410710400341c000710100c00e181ca01c606d1040c05e0007009504112101c10804a1103801c580d00c41d0b89441820004d2071155882c2d00c1010140000640241000c0d40240c0300d40c01842d50700c0080c01e001d074000701c00c140c0300100000004e008040c040c0c024040a6446403001d08074146840c001510400703440030200d03440341d694410355010300402d40010200c008111009011030040d5602c860001401c1e9003224281180850042024403185000c1c0c901001950030154051603008100d480100f1080e06155805420840a40c041c045408c082002d0540540010b020650f1102c0c001d45804c4041d0b4108041c1d85e200117019030240035950044d2525114003100d4858095500f00082d18046d210303540e04003803664a203c0041015000103c03190300c445500c07010703420680780c80009000d95044070640000240c5503a0b0000501145034111070242204d121010307840020320038452000764003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 746491627 1250 746490377 746490389
    0x10b1201090b240108070e120a0209180607030908070209010b09130b0105040e0901090c0b0a110c0a03030e0a0801020d060f090b21070806040f05010b010801080d0309030c0204090606 80
    0x91001040040240704000f00c110020b001101c104040840b00440b0b0390340e0001c10f0f030810031103071213200b0401c4d03a01c0c6081c2020107108000100b038441580d00410001820291603040541c035001c46140704540041600f551002d140d04000494003031500f00350031248100817000354071052260002c104290130381c3c00707800d034400c003994074904104504500908903001e06d004076003c184140b104000c1c0140344511660b01c0601c3e40c0c0041a182c0182d501c14020b0030300c0742c100001d29480460012034903544010703494410410700300105100b10503040814440b064600002e000c11054090390701c5141c95100780c500040607690021543c41d80c40e465140001c120b90300502035406041903002520329030070b001d10025000014402c510b00680c401000c000320501143c0308a0354010388100040d008030510246224034080c42e11980039401602d400340c2110340d840c8415060100c800c5c01800307042400600810880d0790303401d000800402d40e04054070307a0440000300940c07003400c0081c0300c800c0180c3c542001c02100c127 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 746492877 1250 746491627 746491643
    0x50904020f0a1e02330a0c14030426070b01060905030c030c030631060b010e01030e07150201110f0d050606070f0b0606040b03070903020a050f03060a0e010b120109 72
    0x1a030000c43c070803111811003000005a100c40b00c2040b6102c810300402c0d01c4801c0000740b104c10101d82d0566140c1000c3c04a0325201007582d030341e0000c1055500510502e00c0028661182840d40c41c2659641020103045501500d0f04120703482c0b0102d14001c0c0b4412a805141c1103059500c1039a9100302c010715401150051901a004204000106040016014082e82c60040140030300303980303803000361a2410030786c00c1849441d500380710f1400b0f60141d450180320801e8010714021849128980000d4215682f618000b8100351810550092890020800605032022a81c01c0d246040d10a44104d01501402c2c2c1c0710300e2605800101c003610380351054010702200310019400d00882d61264100405d5004180d0301415003400d00c0076031400152a17465007684803000600050a10b074541200041c0b80c1c1003166034002181280701d0a006524002c1901d0009000844141e01d020807c14080303621406e02030241119283c0780e5601400b044000e41117030260400240415900c6d00040b40350324041d01d03010b40c0c1071359012 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 746494127 1250 746492877 746492897
    0x603051207080306060a020c090708071b03020a120e040c020307060e030313081c09030309150218092205150603030901050a050a141c05090606030d0f050904020f0a 72
    0xd1140c10650742032680000005085035601c4041c0a002d07030189040c40214001c882e08081c040da130309000d642c010089690350700d40d1480e0108000e0800b42c0040040e8200458046e545400290700180307440300185d000c11120444039070300c0d600b41c070b010040d5017505a1103410306a02e54060349e4000041c4c14004d006400a010101015024075243d101c01c0d41c03007070391081103401d4140100300d00c3d80080000150145110b801982c120104030100c4882900850000307407030b010b00b00c09020440d40c11032103e410b686021840c0140f20000703c0a8502a00d070b0550088100b5000142080f00341d041290384a4149004800320818502c1e15988038644034900030700b00061840420700c2400c0c00020b07210302160684581c0c0c0751400180301590b10307800c46d030100c104028420380032008070000312014151588015141d20144900002000151017000b4030f0170040354031940401009075400900e282d146907603800d02c10381c0101c000c1411222445030300c0c00a50460300000b18050311f007071120000c14000d400c2d55500700300a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 746495377 1250 746494127 746494153
    0x1602060a0e03390306011215050a0b03100b0901170c040912020d14090607080d0c050405270604051308131401050a020a1e0c090213170a0f0f02060c01060305 69
    0x1050f220724001e0701540854010f00040c05c2942d030035a0142d01070105441e01010510b60441a240e04588028070280c40e80320503481801c00f00f05261402c80c100000b4414400c5a2020500d010414800c011901c40345001440c45030800f4080c400e8208000b030001d000203080f40c1003405c04000540c10920052080341a40580d661041c1c14440e115043c1c100002d152034511020001c2c01e81040b00180e440040400818121008a11418001c1a07080d101c1d507444502e13010800040c1d900c0c10f0341c164000d051515070007980f10290b02c0302c10360198007240c0000e62034685d103010040c20f100c1b0b0100240480030004002d0784403c10141c0400441e08140326103aa0a80c042004442c83d005000000300542d00511042e4001100001051000c41524400c4072a6090742d4031141700001c001c2d4068985180d0010385e40d000c91240e600349502401d010010041d4128566429139a2250300200142007500c1500c1004100100d1104d054095900100b00f80e40343e110000d80303035008100d103100440301ca10413205600c40d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 746496627 1250 746495377 746495473
    0x7031e1b09050d030804030c08251211100f0902030a06021305061204020112110d0f1401061b0309180e070e09072706030804090507051602060a0e03 65
    0x210135455070b03403011141c8555034291120740d52090119000c400c144132a03800303005a10415070127603d5055808503015064249111030460603519a07042001c6a03800e141e00c48000039101204031101030740010700000c2002d07203500510010100079414000c488021003801019006050008482da00600c5103564850400820344a50f014242c031010080700007501540c003411803492424008278012030310704501070403002660f1112507080030b4596913a103180c130b040510f482101490040c0a01c0c3c10415410524080d2140c0e25201031090001168107400c410540f240380004000d0088100d901080d100501c01c2d040a003071780a220312014811386100064105549404500502d486030150404908111084c4c40260701006030050201044400300400c01c0741c2d200303040c020350154501540b114200b16a80f000e03110082c044c01c0c02c211050000d901c0780c0014280d03840545a04460f21503540c84040019180e1451451205506014010002051031340142e2000754001c0d445502000c1ca031070880c80118 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 746497877 1250 746496627 746496649
    0xa09050103060e07081e010b0c0105060a0e012601020304060f0c03110f09180a0b1c030801090c11070305010e0c01210c0507141c020d020607031e1b0905 67
    0xe1209183c0081100180030310416504030a50640c03900090302404920190302400381e220680d51000003401811442c000e1041c06c1c0c200200b2103402110514003e0441284003040c02298442028406c0120501d01c8004a280010f44024001d544a240c1410010002e00c000309568510504206204500c40e20a1150480b901d901050107030800701b410b1704040160300422800c6410070284050030b00360702d40641c4080d1003000d03000310224a15440340709100a091580300850b00c00070003000303040c0020b5008081c050543c3e00d102400606d10481480446034000ca07903400001d14040c3c034001009006043d0003450f0343e0b41200c8215407005144000456a0829841d850b00d08400150f025003075100d42500001505500c6180407418061035444000400c1665801c41091398000c0b90086010540802d2401c86011240090f1008200304400a51140d80040c1084101035031449811910102040c8020030b0791000c48040040400b0414044000c8500c41c400e0700119041400003c0e4a01d40100107032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 746499127 1250 746497877 746497889
    0x241e0a09060e0103180b090705010219030c17070627020f150f0408010606030f140f0603190309090b06070507090207060b09091c02030c070e18060106050a0905010306 73
    0x10008030301d0860100c4100d0441410345040546890000f243e500180315502c0e00f1501a42c1601041e0802d8143d42e49001c1d0958041c6040d50414544d02c5413580c8808a030103410364240c103010204445d1813a28019440050f038120000c1c01000c0341c0d03c01071240541c0701941c6203040c4070742c0390154001450064440090b8047c001d45c881c2200380c8140f181d0810009c50106040e0300c40806041120042000d40507421681000d501c9a66840b020802282d16002d00544600c1c280c00400c041041030040035860400104140701c9080c2c490042081e54038204400105e60700040c5900c10110001c1c0350040c070b0002ca5100da5400c0c5400c00c482d0100e1032510303504032001582c0c030000504145181080d6075002c0d410410080d22000c0c0d50f0640c00e480c0da00d5031004039200301c040b80c0103001180c220402c90902c1e464061100c2c011548240420b9481c444002691402d40d2482c0c42c82c09955680c00001c400001c9500141001c1406600000211103070032030042c00e207480c0d294449030b18058a82e00110110f4409120309 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 746500377 1250 746499127 746499137
    0xc0b07020405010e1b0d02131805060616081303021011061501080103140705060a090e0a0501030c12021504090c090b03090304090504061404050606011202120403030506241e0a 77
    0x116180d038008001e4668914401f60034466034001e10300c800c1c0001d0b4404281c038207d00034910b503400e00e01d01c82c0f25840a000c685080c00c0141e02c103031013026000700d00c10003084a00f0000e2120003c03400d00d81000c0045500130041b200c07041e03805070010064a8a000d56400c00d101c2c902c0072607604002d0240c001070050040c0e484909580c40c6444440881030303170010f00540c0b40240c213804a01070f29030f0802400c01e400c01c4e40360714007000d181c4000513a40090040c03505c000c15260800500000f062070b100304c0c1c100d071104135400c040650940005218021100118000300301d0028001882030f0490b044540035100544030610540ccd0b4400000d4440e101c1104c0c0f10704d180d0410401446609620f90003103801a008000004030310407900d003084a500e105803801d41f00c941c881c03c00c05c1075540e070100e00903142d8012500150301300100042e080c01d454402401c01000d041d02c46002604940760081c174080a40c10211540840c50380c02d16903030440c0da012980d80b0041048803444c1140c1c4030302035003c8820844042e500c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 746501627 1250 746500377 746500411
    0xc0a0b0c19020a2a1a1819090b19030506042a03122f250311011e050711060421140d02060105040605090105091807030c0b07020405010e 60
    0x70880c402e4446500c4c0440c03a20001000c1402050a000e50100e5040030041d10742e6401440490001091748140062050600e480c2c801e01d8070f003040018400300c50400c6004540c114401000800c0c03a13100c0c590709002045030300c41c00814000001501030003280112031001941c031540c0354004020034014405030400124440420000381001c0582a0a01030303841d081b00c00e04020002000b00b040342035038140310300c00750056141c0310000900c500182c003003402e110451001800700000c64514800d100c05040088410134128269006a0952041e501c4000c1030602c100040c0d00003401c1c0c0c3e00000c101b611480843d0340d800c0d2003803c054084605964080d00218041480784a011800c0104110210390540f80f802494030390050810400c070307004034203030050301c220b604020502044440d1680041d2280e0185001003045403246490b00da0003102040182c400301c07161000d03c1e0301d003001a0b44014609000300100041e440c3c440e1b006401103c1c800c0b1011702c41a640d941c242546000e050b581c080c040280e000c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 746502877 1250 746501627 746501663
    0x30503010e04030e040f09120e0d11040608030a0906020c01080621150106090321080601050c010213060503010302041d03090f010903170301060206100e06060c0a0b0c19020a 76
    0x240c150b84144249410740b20b0a4400c0040750075280c500140d058a56280c428030420400003030740d0103002420f10300e4203107541c01c110000a00100d100d5240036004d1298400002490b0319160007400107450701000f101d580b03880400740207200c1d135041d218601c018020300000d400d480d8803480105000700001021280d201241840316881c00b00c203448007048511940048262000342070403903500030100c5407210300304030345141810000a92940d07030b12000a228501d0b41c90300781d900a0034083d0080303020328215844456850f000d900903c40c030107a02c0101c1034480400500181d00000550507248291420310860300e6400358003401345007007072000c0304680091003030050a040003000200301040526050003926900e44801e040c40e4218030404095410000040c01510f07010000543c02c003200740813600d02c6910b41001404421006450203200c0d540004800c030604408000387e4249580202801c030141c02c003c81e0340c0e0106c4d4441e2000341000300d041319040364082e00100d006514a600040303c46c003c100013703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 746504127 1250 746502877 746502899
    0x605030c070606030b09070b0f121009060312031a03060103023007140d11010c02011413030203240103020f060408030f0909100b120c16051c020a03050301 68
    0x100155100c000911810000c20500d019410065010300c1c0d07000020f0030444800d42c103100440e004110366001c10450034a1005484040316620b000040001b031180c0c5625400040740c140c0b543c003607902241849004801d212098046109001c0355850820420916815040804000c29141940758014400410140c180751001c121034502c9a41c9103400c0c51040e4100700e0000303030201c02505055100c100144220000901040080038040715089102c00c001d9a5102c0105d034020002810824480c04034421640151414480d00304602c03082e42e00c9d08010304130215420003500c016442485010010203c90381002c040c0104516800c00f0f40b0002e80c2541c0074031460744c200c21440350300030200f0000054031903402c0c00030300f4408010200e00c942d100c01003010809100006044800d06842e1440c041041d0300f01801110070840d00103070100e440e5500c07803c80507458000d492150a030040c00c142580c042100100b44903118098605804000b1201070f070b000c0369100c41461000f40400d10400040c841011071b2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 746505377 1250 746504127 746504131
    0xc0606010f050d0b060904090b09060606041a0f0706020301090c300e070509010308040f0b0418051e151302040501020303071b050a03080a0e01050402030c061305120706020d020106030c060503 84
    0x903007039501e0420611b0200d0111004440103540c048003000c20f200510b28140052608010111580303810141010540348907865244e41c11012441e0020b030201c05c0007030300300549240e140c1010f0300319181c0d80d41c0c0c290200038060050071900001c00e034200d81d0404624201400d03440c0b103031502141200c40d00b0524802c00400c1e0a444e202414450110009a56921111054007070b5124182442d01d8521b048902d000885558009801440701808203120124070545441c501c1a40d8070000305080d04c2d81454012490354400a41040d02e0f000d40412019038251405400c46040599031a54000000b1032030400324042d034050140181c000f000816100c1c0d00c24203607011901c40c0ea07074204504100660390030340b0342326801d10220302140c1c400c410444080c00a10070600c0582a04000b40081d2410703a00280e214002101304504c04c00001c1002c0d400d00900105120180401800f40301300b01c806941065034914840c0305010043c8241210102d440703106000d0182125800304407500710500300744045d40e07680c01c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 746506627 1250 746505377 746505379
    0x160e0306090d1803021002010e120c10050703090f0605181c05030c0f04060e04061202030c01080a14010e09160311010507110d0c08120a08011208070b04080c0606010f050d0b 76
    0x3c84400400566207542800100f24055000010320044a0720070500709901c442404a164000f80b040c0d210585010441e00304c005600b007400178250345d407010254000c06581002600c0724808440c40401c0001740d5003c94050b01d00d59580aa04251450b80107680700519286171079016128098114054042c20142d43c00041c0ca100003420861807500290554026921003000190b07940611011410705104817005031596512652180f1a00d4000c0303a51034103008280750400c501400090a83c00242d405451268084030300c0310a01d503503030050034405501c01d450248441c0039440e00d1801c1c01c0320000d09101225031090b002c481c80b8400d00c0c0199003a4008980c151100f40c0d807507203031400c16a111000d52032124410200000d8950804000038a0181048801591064200206000136800c68a0581124442da0121068450610700301c4224016840010802c0c0c0b82d02d400d1100704084a409424400542001c031062503803010011070341d444c201c450110210300d04002c02c00382d40b01c15030440b0404081c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 746507877 1250 746506627 746506667
    0x4030c03060b0d0b04031d040203071e05040f030b061507020d1106070b010803070b0a05060102030706092604090c0309020f010f0e10051b03031509091005160e0306090d 74
    0xa10f9413034040381e50008030340c102c0001c2c84400b49a001c0300d0b080700c40d05d0305240381a201107007186410300c070142c445440781d0061800e071000c0b61007401c101c0c2e00c60000c44000c0d01d00c5060180302d1030b541b480d00b4000c5a600f0380d4000c0c487c51544002150041c040c10599411507001001140c000d0040d480d1042808141444141c0001e410060303000407400c44003a40307000780300e00002190b5803421070070003050392000500052038a500b4201441166a17001041d914400c1d003050300042c00281514000340141951750f5110450360126141551141d03603980940219244107200b0b1046e885401340450449145c180d000354002040d2903200352551083c1003c2c1e8100786181001a420780085000500d07540c010300e09940022000201441c40000000c2c401c1c1030110035500460550400c0d00000401200c05081c8038024407142d000929945420843c000722066101800c0006023800c6907103500420b040c0c125130000c070303039282c0f441500341c100001e03800c2c03180620318058240c2440182c1c040301c4042c1d080c0300c401d840ca1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 746509127 1250 746507877 746507899
    0xc03060c13270908070308100e0712021209010c120c050d0506030a060e0d020c04050105060403080a1403100905070f17070302040503120915030403020703030810081506010306050604030c03060b 85
    0x2489501c43c000c01940a4160261540660716008041180c0101800072064000d407041140310310303112055810040310b0030a0482004214601d20081c0030395101c01030100f400340c00f070000c0400c040d0300215032445076958521841d01014a44000c1e900802118400114108900c034024a016482650400001016150001c42940b0341c80240e0380610b0b00c40b11507402602406000c15010461039041c003030140d609000943c50000005c100c0d02440c44003402d00d02c800500880d00d00d104240c1404983c1500a410791241403540706611149400e0041c0e901c40c0c0c0c6080f000c9001c1501461918410b0b910030750f1880380c821810310100c0c890480150140045c15003d00010545680510001ca240315441b011540c41c0d1400340200302c4943d146076807a8a40007400c1090101280d408244803043d00c0d0103003404403090b104c4400082ea20300311a48900824061508103452005107142104e008190907601440815103030317010050716115601c00248a08000f480c1000081e030603402082c28400e0041100902e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 746510377 1250 746509127 746509199
    0x106170a0b0607021018140109030602030c0c0718060b090d02100210140a1b1205070e09010314070f12020d051204030f0b0901110a230c0c03060c13 65
    0xc65041c5e04d10304d021680210229114604882d10700340141495201c01158001410020304170819502018181c541c0000010310100c0703101c4110396148202c1e000312002559100103420380c1042e002090001c0303504001c000580000040b0540b02070303010081401812041c103500300305819980d109420b09500400c181031034107074920b02c60303c0c42ca0103030407564880900c2c081005a0464801034075030811012510440d01180398058120030700e24810580025558880d04410f99244503100c1c000c0345e010f48060004010000039002138000142e1107001c6444454407890038903004e0103903006004902d483c2110b150301524051000621042c003178000e8520b9119603a0b0100c1d46c030b80c85900203540303606541071507104200320404481d600260740e5000304083c08078102008140d100e40b60070340341005000007000c281712040030400d00b00c0703822142d400c5507200013004505407544018018a4424000c6034005070718002410f0071600c0180c8015142c146840c1000f40e40781e85030080440701100071920660385084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 746511627 1250 746510377 746510389
    0x41d010303200f07090e010f050907210c06030c110a11061c0e03040302100201090b06040b03010b030a05060a1406210f0f010504110d230109051c080106170a0b060702 73
    0x78085da00c00c042081d154030040d507800c0d41c0c2142540316030b081c90070381040302c410710100754a001e50704079160329008200b810b84a0b0b689506071032005014201e00000026295416600211003803559441700781b250b140203c51a03444511400c0080d101e22401303140c4100c149498001010206201e428001045500d00d09140403a400d0b0800c01146074000034080c0305610384141e0040442c40c0c00d100902c24084c0382c0d509c8208160020341414065500d51889450640c0c0a40050058031005800c43d429982c043c140103981d0001941c24400c900c0c5007111005000705c140204a00c6010040c200c41d000798184c40b03c2c9034503c049102800c5440c001c0c0c45181089000c18018110b940a5a00001c82c0a0801d0704014000d0010201c80314071402c015400341000034076032620400c0080c010f040342c142091071101d200d0b026000982009066014140744040ea02c07424604c02c441700801c0f0750f9200360a07030b01d42009844c101032080c4401250380808001405045658100c250500e402030704140c140700066010543c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 746512877 1250 746511627 746511629
    0x30e0301020721032703050918101a0f03130614010b0403050607050c0a0b071b140f15130c1a0c0607140a03150b0f041d010303200f07 59
    0x183e4041080000c43d900381d40350041c03983c81254140c118000a80c81341c0e0000c60191001c0300201402400b041504490380c03440307142040300041c81111400da1428460881c901d04450040d81880300c07591b4515403816003450144c131041204460101c4c07650301d51000307880d1080c112550485a44d0740f6a807182c0f842c03d5513820800c0c000e1020700c81070b03500d82d820351820a0400c2c80044c0400c013000800d004060781400005503a5906980142c0841815101c024046603010344171076074180d80d41002c0c0410010020048542d4550100c01019201c0407441900035035207a100d0721b030b4000300c01c032011004540000c0320030410034011442030809a9985544007003242c0c09100704514056400400b18041d04146814031149134080038525000e000103110030301043d41030080c00940010941d40c0ca901c0058440b11101301740140845104080d241e00f0300100b25141903005004001088805242c1407000e05040c2215070f040c4d0b0340c55202c2c0c03660a0103440c1c10038038810300558158a00d10410b40d4071400138506102d114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 746514127 1250 746512877 746512913
    0xd1518050c1e0a02070915090e0f03030c0705010e010b0123090d03090302010f020d051905270a09062303010b12011d03120114210607030b03061003030e03010207 71
    0x342d11203d00642c080d05002480d44502003036410090740d1911120380d540004203070740f4002400966403400082e02481d001c014884d07203c0522000040c0110000c6000283c110f00d8401e100a000150a10803100e0a03210101c4a0a01050b0070701d0701c078200003220356020749509005a510b18200b640070b400051705800146419000301e0032004051041d03582c80485981c00c1c014500090282c0000044024140c1c0704099011060126402c1134040c603038421421601c035100150a91000c010780303820750345d11032209122107500c02c5651245c00610b50303200c1d000d80e078100d503003014000e042d8803140080c1441d8215600344040e815507a9481c860020391ba4041d14107010000c42000081425080446280301d22031a4070904541d442404440500511a21414103403014010b00c0144481c1050108540400c40404164240c4030000040e84808001507054440d1000d66011710488141005044d1503003405d540d40c5a104111010038004640540a12015060b01500061a102e0301d0303101c1d440340d480440c040c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 746515377 1250 746514127 746514187
    0x130215040f051002060708042307030b07021606090e10170609120f4f05010c02030d0804110a03081b060907170a170d1518050c 56
    0x38407440c03c03c41c0c0700d81000b107480d0006001c1802c0102001d00064002031004090516605100f402c21a56024040710040d40c041114210758403403400800030032040750f5001c0148213a4281d80800395100c2191001c48003035485170303c201070910801c240507090090181361500b00580c1e00159441d9150f20300554045030030007822041c1000c610460400036403c5d03012048120900a905c0548180d40480b24810f4080c0b0315280515401050800c10111031558800074003000c0003000e101610160342c098052220841c0b2681035600ca50055800800c0f2600c00394266000c02d080c4a101c0d40109480d80e0440e0183c11b04030007842810000440440282d04201d03044140800c034032031880280992103c10b150140050040c510b095140f040d41d40342288211003035402c02c1050920301c00414040302d0540c1c0e80004484002d9000740c040690740e0b0780021806890b032072070024810510004101c91400340c2e081080f09115841d0b110b484000540800740c41417030614000c202070020b0038a40da0300350a03e02e08500035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 746516627 1250 746515377 746515379
    0x1507050c0f13180614011505030708010e1305121e030103050a030c2901180615030209030f030406021509010c0e060d0209030d082d130215040f 63
    0x10050415080e6014a405800c040c1160006030740c0b188050b5000030010407000407150401c0344555941ca0004074050880c0e0700d41075000b0a294403031070009040e110303188070044100f040c1240031582c0303104c11203040c0002058800180010780d12248159000800c010460f0504800d07500d450b401c1254015541c8410040000d612408402440c80d103103c02d0800b0100710f055600d141ca03100e454040b035007802010490b40005081c100310000f00c8000d03912060081c01c51410443c85a00e030b484080c28000c003540c1060710310f4502280e0417180100c605490300c0b00041c003165800f0490603070207900000b40b8640c1c1405245564080c20000308040d00050407140d0003421105200c050000341094050000b51241e414000d40c08241d540014815182c0c01e8151400c503900c0c00705113000701c000c2c0601510980c2c5401100e0015403240d0744100c40900075141200c2c81e400c2c12014441c5a5529585c003044c2c001648400c400240038821600c00c0e00ca401400502003031042c2a0035010781c40c265001d81c000074004040014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 746517877 1250 746516627 746516633
    0xa0501090b010905030c12150a0209010905040e0c090921090411131802090303030f04060b010c0c0b0f07050304090606030b06040b1206031c02010e012f07030e1507 72
    0x3981d424000a0030840000c0b0305180110f80c4410a61076100c0c040c0c1c4280b100081031032010441b03a44842e074014845155410800300c050080d5100851032400508200000b040c00e2909100741020040c0b03c40040250b000d60300c0030300c41e000a00404071b40003405a200703441d40e1341009a0051841c1d590081c081691044400c04100448040201e070311701840d0305200783c0910303860f5110060246d48e0040c9500c0c00344800201400080d1040b2840190036000100034406c00924ac0200765008520500040c0700c640345031001140c004001d5000580444c10b412410481844600000d015800079044039524107415620341c0c40c42c6500503480401055500c020801085505201d842000402141c2e603e2410b0314009004c6020700800c1c190102a507542400708060b90741c1044828000488180d5400d81c5443c40320001c0e009040802640b00503500303040d006180c1a080d002ca045105c0d41d6000380d205d0f0cc01c0d00111a4225801c8508220280014040c5040d1543c1d02d85a20400309a2601c806607a5070b40c0b545 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 746519127 1250 746517877 746517881
    0x4150807300f0908311a0403231b0d0b04020423040b0c040f23100509041d06010e07121b0f02011116111512010e010e04030509180a050109 61
    0x210a00c101c0d00d9410f903c0c440c0400581d25064110307030400e020070b40c81c8020f140541d0750621580c2c1c40109003150030f0710180c4510741d80043d0200c43c9e030250001c1c0c81886c58601903101c59242c4c52107120360301800f915101c0d00025044039056820500243c000658481c0c800040034620342000303600d116a0b91004100301c00c21400100c00e40c0d22104180a607420301e440c043d800c403000c55580c0a0550100c0c4100c2c1c0f01c091150003811a4081d00200501d00341030304549940150031640148010b5000314102040b0344440e2051010060f110180c5000400e001e80c40c5c440300b034420100c00f03000c2d001080290304403151841c2c00c50103aa118080300c1c1120030040d03044042e0150000d01d0400c03a003029a4140000700c281e0080b01020703a500c055280807aa81c1c044101d20b00305202d2203040d00c441e0b62082e050ba4002c050032070a50050018107031070300c009945503600d8240d581e040580034851540744406030000540040d2041d405404035a00182407500c118602006882041d002200d02072078580c1d40381c0040140e580c140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 746520377 1250 746519127 746519167
    0x610031113030813120c050f030c0a0915140d02011b120e04051e010b0a020708060108030306190b04061809020a020c01020615031507110304150807300f0908 69
    0x404480000b804031b030342e420054003200d203e880d21918104c3d850b007089403010f00c201c5101180043c006d030351607074481704400011300094418484842050401060140d1078640311500128010700d905150416070f4011030300380e9601450074035030b0390b201d1403d04005652010150b4008a0580f40c0e10014002e203001c3c08202e56000b1301068031460b0500b501101c550000e0308481c152050701078900d41d030303c001c03030810791030000d26038844c1c4424030881000240e0603e01202850260504031100008a0302c02402d00c14440305074041c00d000d100d0100002c10040307010b50404503c00312a82c1c0b10700007859880c5800d5040340c11503035074070303000d078010b030751071040969041c045140d101410041c40d1462010500c0030030f1b40c4541c09100e00180c008100040750500740500c0003200110300d28411a80c0c0d40b030b15034003802e00d286c074203031001400305403685c0105000c10b014108a0b9400141d4150404c9618441403e04074402d0750504404180d658510322809066814065400c0c09800b0700d14003551408141d08503c01d208007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 746521627 1250 746520377 746520389
    0x7050106090c0c0b070c020415120b0601020303070504150201110c0a0314031b09060408010903181505030718080d200f0c061e0a091401080610031113030813 69
    0x3c4240c000c0c00102030309405038010040e494075a40c0d03481c0c948041401031110007400c8c040303900812000104c9032400c089449250344540345030a5191141e00059a990105840400c08108144828007a02803501e80b004da10000c0e620020030078a0303510500000b02da1114000d407132141c201514840605412030985546510b02001680c514506400d0180e120b8403a140d41c414040000218041d09a68000546014280c484001c02c051001c3e8540a04140080600b014049102100c00a4039020500400c04d0029840d00d81524595420780300b111a01405541c0031803044280d140824034007001c000e02c40c24007044d5210b20b4600c03488400b01101d2039a504840c00c203030742d20040b800d0310b032010082130025400000361090382d00d59221716900782e0304201d5550003c4041030701040340e0740710661001a5000702e811410018036400002801100d0702e1508039052900b11a541084100f800d11039800300500c284213036446070400c140014441c06000041e80706031102e010100e944501c1e0446800f0039801031070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 746522877 1250 746521627 746521637
    0x121504380601030207020109090609050103020916020607120f051f0f1203080414030a08071209030c17160c030c050307141e0402031003050c0a1a090402090607050106090c 75
    0x544403104022800d4000c10040c10181c0120303502c000c41e40540c1c213403400f418140b0418800e00f80c80c1c46418000340000d110070b0380f0400c04a4041303483c10444000c1ca40c02150303035901070961550783e400182c0c0e500300b003401841c9005503540d084103070011580c0300301405185c00e0038003400c4042000000e0440550590080c080c1d0184d50752040050504443e118450311307034035041042069131181440000c1c00300da15080130103804005208801254041d40c45485004152108144100360081d060102d90701c00740d0040c04640c05c48090408189000440b510000015403068500744010b0b141611031410454100d80840060b4030900401104011050103400c040c1c00610010745486071070ba0304000c9000c6070707900488203c8240323105800200c100302484c04016209560742e00345071070030070402c00c03070b5210aa40c0d5010782065605c442ca8041021812605e03c1c3c01c100210410101c02040140c1c072072180030742d000c0e44c2000041c0071038660310050044940501c0001030300d50300e0300c1c2131401951a12a43c8204100f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 746524127 1250 746522877 746522963
    0x10050102010204291201140a0b090d0b0c1306050c0f0316030e0a120b040b0601140f180307030f1506150302030907170c0f030c010e121504 61
    0x20fa0a12101c208070004100d480800c42082c04000d02170310642c107666150700c0055001240c030302c150070620aa0743c00103980106d14146e1342c0d0f82042d101e004030800140e00c016000550f401050000c5201038100e0703c040d028900d0448101302c020082a00c640c4035001182010501c4c00007280184103203002002c80101851800c00008840140d52101d00310041c144101c101d14070703010341c480303555120160490301c101129120407400c18101c54101198103c0d8a40469800124070b54802e10b0b44a1040d14602026803e01308410703030301246034000e0700d4100038580380c0340514541585c04109000045000d240d04480041150516190900041008401c031030705003d02041146e00038800420313003aa0620340140c41c1c0d03d6081d189410320301107601514007140d09030301081e10b560300482c0c1d001c6040d80440c5c0c0890300c40854418191100c00407402c142c0031071000d8440e034284d4140071500803007142201054602401005128414000d000d840a81c0e4000c03d06004203e4104810144d20501c4865a07542c203c030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 746525377 1250 746524127 746524139
    0x3240906030a170c0312180a020901050d0f0c06110607020a0b042405180c03011a1002100c0323060a060e01051314030c010c110405060d1a10050102010204 68
    0x90000e0b504018240031150241d611081000c2050b40c602104031401e03295644031801c0210301004044c2d803c3c4000c4c00d120b4000900741e4100081402e8620b41c0540084c0b9542e21b017400b04000040d118405072500a0440c00c200006802a41424060b10003503c0d00c03494061200e030083d02c3c001d0010010401e6500c40c03c5c080340451910250b007a803141e4401c021702000c000c02070301c0424054140d600c1000f0682044280b150103c4408030000d503e0403441c04545030031032007004160a84174007560241404040ca5250322445c104520090307100030040c0119020350400041172000c99140914120000eaa14000442c084150107a60a41c074840c0358240345160514800041c0d40001038071500051081002c21151140d002d4025600300300040c1843d81c200c2036813101060280d0380c2c480720140c03090040140c0d400c007a6000340c01e1940740300d0b00482040ca200503144280300c020000070300906c0e408001c04400c2000103550007014582c003001c13a072076a00b4030300b46445550070484075908482d055900500c800c4c008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 746526627 1250 746525377 746525383
    0x50a0b09030c0304092a200d0801120501020f0301180507080702030901030c110f070f0f0f0b0c010b120a030305070219020d110402030403020601140a150c0c09020324090603 76
    0x2541c45c1c5400000307403100e8800e1300b944e840e40007114680d135007a4016030324010240c1010001044580c040c1201c094a5800341ca4070303807200c00d05082c0c2401305082900600c108105503508000c0036125100051801e20b081c0c4500c0c0c1e1541007640050040500e174904c0001d5004c031801581d401804030b0400c0c0c6034900340520042c0d00d03030083d160b00504040d580d070143d51001e841034a03840b03c001d41c10030696150b1501c0c0400140c44060500072225081c149100002d008069201d241048907803681041c006c0a08164807480141d02150040000d90b480c0e03901070859a541c03081c01d8940e101041e004001c80d0919243c0503050343d01c01003010080d508240071504030701c45a640c107540065030440395500242601d10703100c00400741c016075483d000352000c02003004042d0002307501410303914a000e688144040210401025070041c3c001d410340000e000380c181a101f03004c0c503131010310588184810841079403200d07140c1040ba0001c4418204068002d08481000c424584015002080c1070341c05910b94a861001300e0383d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 746527877 1250 746526627 746526629
    0x21507080a05040f1203020702090105190510050c030412120f090b071e0804051912030e120a0503030a06050103020c0606010c05030d09050c10050a120e010f020304050a0b09030c0304 80
    0x381e03a20307080080e04102c0c0102c002d00030664403010807000220000c0b0010000e421044040b4020700c00d040000c180c03071804040f03c440c1c0e40140315220007003a04102c144024130500d040540d0a0060602501d4042c280c10700240c400380400b0f102d111044140742c02d0020b01d114502e070032a8203110000059195032640080742c034003a40e00c0802503903030b1800c44c0c2c038054050b82108000e22408075103c0c1608030401c4810001881160011640c10003464803030760007003d020916108d00d850041903d906070000038080d110092140c10018200700c60182003d05d041d0401c440030358200d6250f04004100700f0003140b24484c50003c2c01e420300e000c60811110002c902e5587c0070140c1900c0c1400351501c408420080c04000319100401c03022014041c01541d0302e8002c0ea60712212506a10981c41c6003c103100403031003038040c0c803014403241d5624859030700d20b05080340040ca00c2d024040a503549a128180c0b0144850000710b000f1880f500003072446241074200543e8416000d40300c21403c0c0c1040003000500203001003514 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 746529127 1250 746527877 746527891
    0x350a022d120304120b040b01150e1c02030307050105010f15020712060605180403080a1e050405070b130806180a0b0a0f0609020d0c0305090703080d090b1602150708 72
    0x66500704126070024558000c0d41d00840b142d028020482c4200850720400b18000c81c8280030981c1c069032200c0000b481c44141450340000100640002c40091a2000c42c0c4800300e50110300c0400d01c01c800f40c010074115401440180d8041e910b03080100301880741d00300b04100820112072606002e21800740c009403a1207451085055940002d480042480001e500070300082200070708d4a020409441c024100d1035a003181d003a40411001c0000808510841c082d20b1709012603156550001000ca108010007814060b10680e024400d4040114001c1c0c810b0340100542d4010551081031140ba010b102c900c0e04400401d200b6588000101c81c0c0d090081c0010520b02c41e682c0004144074564400403000000e1a185004c3c80c425400d01a0006400d60658002c0c6020016902d091000400024054055038800d582c0ca44c3c05520640c1c007000480c640d00c01418040e074030b40402188040700c41c1c54800143c0f00a0f102180014564061880865010000500060301b125540c4206107000c101c040d00c444001081c1c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 746530377 1250 746529127 746529139
    0x906010e060a120f0c0c030e06070c33090f05240a02030f040f0305100e060703020c0c0a080601060f080405120304050a061109190807350a022d 63
    0xc43c1c41074581c000d001d100c0400603040001c0d459400380100702584001d402d80208080c0300203d045410507204a803000c07500309002061071072514210014115001100e0440030032080d40219407a809c5051042e903038261540c2c1c1e6900c240c20403080044011790f5500661040c03124004c4410740c20058208401e841c00c0e07084820340c440e03402003000d07070441c0701e03084014042580c005804241c140d540340c1e019060b43e015000f100c80007035000a000c0102d6064148400031540010001500e4501c01d400400412884c4000e540010340c411000c80c3c44000300340c02c0311502d07412003001402140e5001b040300c40340e0003241c68000c2c4507090a80f180303a2100311304080d8060000c1d0000004090240c2040b072080c006078003400401c00c0c1140d452001942c0e0304240305e05442514014402c01400c00003103107100070303074960700d025090240c1351125955600b070254462240c45c14628400b4840c135100050030008000040001d0000000e00303104010360519500c00c081100071100c0410582030845031a01c0705560f60035511 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 746531627 1250 746530377 746530397
    0x3120f0b090403030e120c060f01050d0507090203060402070b1005030d080c180f030303040b070e010c1a1302100507061104030f02101e0c12020106030308040305031306050103050c0906010e060a 85
    0x1d001d00b00240d13010031b802140c0340010000507000300060041c1c4907144003850643c03c1d0b40c840302041030509540340060000d60080c2403c0c880070945030300450304500024401440c0801a0355a15003181046503020000072140d06e0811050500b40061103016085180c010340903d40780410340344900813075112950508800c0c81c0060107031200304110010b10030042c1280d1b100d252a28040d0030b2801c08a41d4000003031a0800505030035405050101f480d26409000c4815810341403c8080c41c40800810a0800007440c9620a026803200e05e14030340c17403034071554515548070510304104090355101070810170726102c2008100701065062000240c5903034112030140c0e0314444202c0c22940c44041e00725030310000c04d40c0a03400b07088681100002d03881d14070854241d848440381602c103034203c0d8134520018000c5030000b03001030002842240111350026030b075241140b0078680f40e1076050803908260004c42e00766014007801442c03407401840041c0c0c81482460419010710604000c20750768060382d502c500c1807241a0304 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 746532877 1250 746531627 746531651
    0x140706060909080304060b12030a05030a0609020a090e13120305090f032a210a050d020a0302040e060a080d0f050409051608090118120e0306010303120f0b09040303 72
    0xc00001000848410b114402c0e40c2e04182e000c1d076005840c1100d02c0c611301182d03001141008158900d004a814000c2d506000904505a03040c1e40001c01c1084070720381e18030001c518404188054004c1540070b95076654410704160442e54580401340c40700c6a150140321884000981500d18004401030600c2c01042a4445070100b40c94203140d00400f103c0350102040307440038200f20b40e8100c5c0290000c08014040d4411034403166417126202c202102c4402d18100d00340140d103a4010091540c60007034a00389240801d000f14020807030f08443e441400098000808121918204001e980c015004840e10b00000386410308050380e8407400300d120310a00c5401c15803400454000c1e0103540003801c1e008418083ca28000d800d824592030340c4402480800c0100c07000c182c04c0281441070070355141024004c0da032241600c0c1c6404500c00102c1007600c041105115400c1c2c0a6141400f546000b54407a4458110301070501ca500d03c00d03a150590780880003440c20103000e0441ea1502c800542050309800c000480226502c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 746534127 1250 746532877 746532881
    0x30c020a020a0305030c0c09041e080403080c010f060510080f0c0714060106020d17040b0402040924110921121207020d080606030402090907051507060e0d140706 71
    0x40000e94040e40c81c1030000300b0b10130044011b21508422605550301050305104100c1e01110544001d840c4101d88480b0022003506200c3c040900345c003c000541c20716590741c1d40c4181c0ca51000804c0b000b165182c5c00a841000c103140a454080d02040300d003c120b88490090061402200500c1212002541404200207120007030031180419007200d11501541d0314460030341d0303907011b00f0322404006214920101307903940c0c41132441c070011005840c00000705468644615051030400f410036a4820b9031079494200080e00d9441c040f2943ca442d40703441610140c0b810303102080b58003200c5c0b01150aa001c00c4000c0b119680c840a500c1c1e064800307151080501075488140e46000929036036000014030000d200c22103801c00304a5680b00e00c103203170708845a40c001020102d03095240cd80780c0d40c0d003025092010a0042c9001161a40c0c005607500454840759a144001400702c06500d000c2002c0c0e080000d402d90900c241405061840c60700040181440490f03c20014001180508803880d40100841c640040105039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 746535377 1250 746534127 746534143
    0x1080609040f2613030c060306081e190b090c10050a110705030703080d06091509020903010e060c070b1005030a0201120207080703051c050f0a2c01150801020f0703030c02 75
    0x403140f654941d10201c1d0a844004180d000a54682404601c0051a01e03c00e020320820303142c150000e03049480100d4481e0540c0e8044010042040c0608201c0c100c01030324200d00e041e0444e000392248105405c001804a0a001c03070307001d800e406030b025000011007d50f0000c003107440c07441c0c10340f924464501141c580381e8104000343c2c01c05a814081c805001003446036900c00340482c0055220200f01031959600e001c0c080768502031400c1c2d20001017650811846070305501500801e00054004141030100314043c5003007000c00c42da010f070204400b00f001c0040c00290314245501640c8882603010050901d0002030f95401075480080c1080461010035481172180e40540301d41c154001540ca40b41c5255240c06020354001c2c9100c00f41e11801c624501d00c1e42600d50150368018000c4605542031a02e8055603d005090168580c002d041001c06040d0100711200c1b020300703141c01e805400018150780130025014450039030392000c0a00da0061141403550314010007142c1f2040c3e454100090100601101a8204044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 746536627 1250 746535377 746535443
    0xe0111030f030f010605070209220b01150210061a070302030705030a09062604060518060411040b09101e05060d0c0305060a2106020913020901080609040f 68
    0x40030400c000d8040001c8040d602070451000b00801c44d0707032030b032004440170701401a01a41c01a0180003003110f061a51840c0e0104039007043d280000034800b51a201074003842a407241244011600340140000c2d418085141030480d40001032165a00c0d103e40000c020180503641410340c4c0700003488004141c02041140c0c0626400020750b500d90106440140074901c80d48101e20200c2c259803120022400103e800d4031901b10000b0700300340d40307031280d4549600900700107040e0891410b84841015803220100107462060344150390b0108100e4418003840184c900f856601406046035030280100807400e40c0d00302007a6000614103501880340a0b198064014180d4082500941d001a01c0d449660039a004460303904003a440c28445612980e0504c66103450074401d400e0035010f21b078204080080d80500c4100305a001d160050706104603180010b8070581c41c82000e03512664000b40e0710803030b543c01030040380e0f200004807404002803416494200d9001c1c1d2040d0010984240c820500811600180500701c010003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 746537877 1250 746536627 746536633
    0xd1113060f090e040b0a0b0307090e031b030708040303050904181506150207051c2306060306010e0c1e0a0507050c09010503070614040e0f010501030c0e0901060e0111 73
    0x940d44001038807081c10724400200003405000c012880480e920302c01801544e00c4080001c0c681c0c0c0c0c18002d00000c06259481c01e515006502e40060450304a020718001d00d042d6401840c0e40c1ca0110305c0e03d5030136500680c3e440340c1a030802e00581010a030100280c50449800d410310a66078078550000074020301139403d81088505a081134141405080da10885808014440c104030f0a621a84142000c408074207240d40183d00070142444a81030181801c0c0f40003508646c4184401d00326564040855146a9a0464084601e03d00406c210041080d40c0c2c00200990181001d5414003181c8580940000c11207503031402c0002e4820f02030712080304641080b80546200d1a101c3d050210010000e0340120310545151059845105540c0381008a407412160001d00078100d0700c0c40e02000761000500c4802c034150b05982444005484000e950040344660040340c546440c030360502e800541224204804032081000b50407903d41107480f108103440c103581030390400c610410140c00040341d282800703404082d4140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 746539127 1250 746537877 746537879
    0x206030106120f150303020c01030608190c090f0c1701050105040303030216050607111005090d140d0510030204050c0306180604200a080705030403020a060c0c02030f060109060f0b0d1113 82
    0x7030f424412803017501d10950a99500b11107043c011401d50303409014032600e68101c080c071003600f0b0414a4400d10100e06c11083c0c1240e40e507803612442e00303d54261004c104e58545a2070760710800d1768880c640400c0f8100d20364004c145941024002001c0380603501005003816030008078026540310804201d101e15911030201d4000303150600c40144810440c0501025034452070500318814410f41c0a4507114001501c01400c643d0030581007180c64402d000ca590f540e141041125001d011000e0040501c540d03400802c400b40d0a2441c810310041703440c01026038007000c1081c403d2103259a11084070016202c1e10f5450b152080c0c0301c03980028000c200500443c5547d01d0f500e01c00c149900316510280220f00b269459120b0a0f0341c1c1c00105844500c0104d030010010303040a515030700022010b44c8890484507052414014081c0194042490b10075001c0003010158081001040051b41070700a5001170050440000b0410749491081e00090094bc54082101c60710f6103042e440ea0080300d821307100b02e0300356807500740006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 746540377 1250 746539127 746539151
    0x40507050f03091e010b09040803101230120b01110a060b1504051008150a08030309060108010209150f130e01030b15010516151b1b0206030106120f 65
    0x60001e05000002c0c40100748014005588103106d041d0440034040d0104546584a5850713103c141d000500d529804a07c100c004141c0020041600341c0081c882c45a1852640d1265a1203921590b02c8030941144034130702c26189109035004d106110311151100001ca46c441c0440d005031181418100c800c5080c0c880d04044c0b0b024000070b1703007040700308120a60b813455103c0d5000c1142041e6108601a2036044175544240001c9503100300e09050b0b2240c21062040500c0120718005450310b43c440d84001e5240e4404803d0040ba81000d105803801082d501c0000c40c13608000b107012411109013110000304503100450244070004210b0304079a5900151015400f160740c0740c0407a031000620a01082c0c130440300840024541c4500039040c54070f100230513103420b03046c03100e0030452100c80191104201c90741c40016183c0324980c0b11070300800b0301d191030742002107100c5188910000d00781101c012910034a136070b8420500c030168607808105d0781542c160b803078101c42c052276154029014108000d1100701c11031030002c003c040d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 746541627 1250 746540377 746540383
    0x2010c0b090709060f06080609041103070b07060c0c030e04110c0109032721062018010203070b0c09061e21190c030e060405160f03050c040507050f0309 67
    0x10f6032800c11081009076155028101d0520090245a001c515582d0105215141c403412103540a2b1282043c0c40f545400c00c3d002c41d0510060750300070b0008410204400703040001900400d0b800441500c0c1c41c400d00f8100b03840081c80b100c0c2d100b100900481d9103440823540d2400c034a003140c00306554a4020b004041c0700d072074004d001c88bc41c0c8501070320b00380c1d66400803080c2011403240001103590500c40020000f101806503105012103001c1240c0c200e5590038060603001f580d1300120030244604030a00e84940307440c0c01001c0c03240c64141907070b4119002002000c0001d9010b4050941045100d0406030702d440320803012440e01d04c01e46c00c01c408081842c0001d40e1102070b005005101201c507410700c3c01014840c1c031004503805031003a10340c25142c09400000c1e60404410380c1c0301c07181c0c01509180108510010403c01410000252800c0c3d401d60840841e040080c409140407030003c004000f14031400520f140c80e1640c54426201d046442613407a03802148030144600240c84400c41950004d9a49080002106075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 746542877 1250 746541627 746541629
    0x1e15050103022d190801180f0e060f100506071505040212070f080c2b1b0e0406050f0402030303010905040c0f170c0a0b121e160206060904020d020d02010c0b0907 71
    0x100b201410307031a04c0c1861040191604075282600c0740c214003800200650041d00c911340740c48420940c0c07001500a150403c012042c0101d105c4940e110103400c00540000c0d4070100c03a000305006500800c50540096035003031818402402c2404000740e50b8030b440c800600700f00cbc0700c00d00c00082c902c2980700c0071030305141c99407030750040340c0141c0100c3e2218642101444102d82107501d10300d0355003116840c7c0da488070b02d00450a01d0f1203441030205001c01e040032481010000b801e90088401016841c0400007080310a00c507a50300010b2070400e040071840e050b40040d55a00c0140582e038210794407100424101b10a240c44803014110f040d001102c6c85c0c4d121700c3d90080c130070034403a0f02c188030348034044a1000a04191755250103440900040d43d00c0e08001d071040060044000e4080f08026414414040c0b600c00c400075500d008203144030000980561403880246040c1d0041c3c08940705004c1007040c1700041c0c3e140e080d540c1855a05031a2051000301500050750280341144014000340c01000800c00c2d40e49012070424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 746544127 1250 746542877 746542897
    0x30705040e0a140321010f03150b04020f0a03060b090904120e0306071115040309290705061b09090a0906020c060f01170708030a0c0f151e15050103022d 67
    0x2805c0b2074150082500c0117a000e02c81c2c1c120301c40ba1500e017440460381c440980418503083c0f2401240c0c054809020078102c0e4090000504503081c0800d81280d010b030706005900040c03442c40c0c006400d2800d000c000410711040070b4002425661039290654116004500103000a64010706480c020701d4a4800035260542090a41c42203000384064400d040503400e400901035509030380e0700c00d00a130800c000790703000d190701e00115110125208800d803203040d4040700416281e1700c80e4018103d64108516480d000c1040c0781005424007078107112242c5580c0710f408125920074031105002c1006805401c0c01d100a00c03800343e40c50a2402a60200400b000c0c114a20130704030340d090204034810821080400d40c44924078000c001c0b55400802103040e485200f41209d6001c0b03405803442005042d019524031050b030040c058582800703038480c1002c032046041e149002c0706242d00701501717104619070001340c44071100b10f600400b818594007080c084d8900c07061060b0100d4a01d080d260703100a20680c03036860502034201420403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 746545377 1250 746544127 746544157
    0x310060c1e2303190503090a0f06060e060303040612021615090b0105060a020705040b06090310050910142a0a020c030c010504061d031606050703020f0c030705040e0a1403 75
    0x38403814900003046604e81c41e0440c484105809003a1803c48a90340b002d010484d09201c1c2c600c104000c20f0590a81c492400d2203100c1c0002c0c2c280c030302014624244002061107120ba00148010040250001c0c0041110701803104010707a10380250140c0b07060140d00903001303001014400c809105c02c13000740d444010240e0103101c0204250380d90780100302d01885100103280051304000800c002d113041940141c0500240281614241400040803e244c00d46441d4180c24441d116418402090700600c62040341c1c61a1803403d020305180022604110f21018001c50301040702501145525409202402c1c1e110ba0170340d20180d51201a264000e43d41e10741000101c1c440d00403140f40c03404039030040040350b08035849a103c07000030a0041e112200355651500c41036401d40a01c5001414407a50402040040c001a07202c95031503200c01e04009140002031f54018065521403191800e8645d400617105040341c90440e00815454610a0701b18184901000010b2211104c10404a10440c1c0800903155451802c401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 746546627 1250 746545377 746545433
    0x90a020d121812171305040e0106050301020f13060509010507140a120f0801090204120209070e090a0603030f080f01090b180f01030308091b01052215030f020310060c1e 74
    0x400da12501c105881091008141c2074200306c43c1c14540c010072075050303425000013015a510000719080e40d0003207145e07003580b460000390b2815070301c022400c0c18090055032600c40e0800c00c03207000281c290300c00c074100940343c2050031345103e10100040141c40c41d030303607070080005220803040100a04030100b1401c0340400315080384004141c03c4d619100f610100e850410384036800d808150203104c071241c0090240000c101001f503500e00d040d26600000ba014080320100041c181d0301d5424024511803c0640d4081040010300501c103a81c080404d4080c1901c100050000e4030288010002d01147c1400d046181040300f10b4041014070110b064609040300d0198450031030507a076103410307651600e10b00e40d003207006014403503c2040b00307501c90300c050136404294040516120308600f007100b200405541c0309000406000110100c0c003681030082610481d1450019411400c0118800c9030080240c01000d00b009440000d0310184800e2103200f140041070f0040f03615400c040e42c20030031000b191290004085100500c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 746547877 1250 746546627 746546663
    0x3516080f19060b060d0908040e130f030e03070e0108010209010813031d1519110a03020c0d02041413020406050f060d091514040b090a020d121812 64
    0x652407440022901d50050001010340d5030703500816241c00c1c3d00790840424030030118030340a58400c610015003e40c400c291217074600210009010001407014041031007989c01c80b000603440d02507041c101d940c50705004010036040d0010030f11b005883d51040080c08912400050b003000194010311140401780d0321000e0075640e10341c1031040d69083c407400030001030303d00c104035125a2131000c18101c0200e00810a14034420407031744654154004104581e05da503422500000c009410a003242d2120038107202405c0c07807003000c0d10082e4440b045500c2c403a000e03046101d1350300e04541da82d601051356001d460500200a00346031102209008032a9012030040c2d14005002c1041e250609516040c40320003484a46050602070f46280a404411000c44032072080041c000c00082d01401561403080401110740f900b481c0905224009607405403c0340c3e001e030820f004c10301c00360716454080101d5542100c00290892650351b0122030a0080300b4000c00c440c8410800480c0b002c103100c4000c85242d0051450f0814000030310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 746549127 1250 746547877 746547883
    0x80610020304080307031d04090302010507090e060f040207020609060c1f1109040c0e0402160218041703070c050a14011a0123070f0323043516080f 65
    0x1005410f1998401d2082d6400a48100c081d9046400400304507a001465800810141c4985400441c0940d444004102185034444444001413000420b4a5412308110020840c0000d0700c3c462180503640000d2101709640760001154003c1c01d01401840d61181404a025150340f10314a01030400b44060000c201482064058500302c1e24100f020680f804684904000040400700740c6034041c864160045210703550b803480508030354102c0340424007c55070b13584108996980355040340305c8803014030740910010440a100c484c90134188020166541e459109042d14507501c0300c00001d00a00c1510a26000c20000c100c2d581214202c0000901501da501c00403c1690806c7d6000c003400038000f9100c2107289041d070343c526420039900c040781500d0300c910303070322880a84072200c0001c1e40400caa001e0341485c0810700460750f01c48003013000040d80c20700e070504a007695140d0030203400e040000d0030400f0324860401c0c81d11030400121164411034121070824041c080750a10140718814942c0180581801020404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 746550377 1250 746549127 746549129
    0x28120209060906030a0b0a0c2304090c050421060506030303040f0b100b0f0405030f0a08030403050708190c1101090f0b07030e090a1b0e0609130b10080610020304 71
    0x510010495803200700b80003296000524240d40341c0300300c048180104500015250065084030400305c4d40c0358400001801c15600e900384105080300001843e000d926014050b00e05a50360703c00003041078500042e0032101d500503030304070001c58080c0c1c6482c0070b04d14010034a002075042c483d040c02d106a6642c1d0b010107031070b40011100039024441e64001b2000040690703151691100007100003001c03043d201d41006111303030000e1401c5010000c000400344074501e0300300440481e0541c1200282082461561880740501020307000030148003000c01c40304200131442e01501c51401c4002ca20320104400500c0041202d01442000c4c1c0752985601c1c0140c1d25944038801441c207440300f82a010220518115500b140c41e030100300d040e410001c4d0306032101000c0d41e9101010303005800088012400b03012050b034600d6040c181004982c1441010200d001054644005031042e100c070443e15001440d44001c0d07400c2c050183c08803840d42c0805040792000c44590851501406000250340180a0340300d01c4200381e80e20f10503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 746551627 1250 746550377 746550379
    0x3061808181905090604110c0a05010e2509090206041706101e0506090406031a0703060f060e01050c0708100e0105010e040819230304110a140103021602281202 70
    0x103400c00280090505411a44800300c7c5912014035015009500c10300348144000202e915944403e0464180d00c030422100c54031003002c840329280b04d01e00f180081010401c1e88a40c604054880c0b040e00d080d5550001035030000c01542e24104842403a0b84c840e262281d0007181c0b00390041162140c04110584000702d08450892464201d02c40c5509120401c0050740005000d190302036258980880010142d840f4107101c044900030702203540c00c044130040c082d11050f80224000c2003013460f040100036401000f00340300c50400e080c041e596542a540903401c0622079000010f140c03141c01d195050548903507000d0308442e038140b00200180e913207401d80040e04580c20345003c5c12190082c030940c03901038070b50104031040708590f06000726030111000110f407040019900b00700442d2000700c1004144180c54500310b054410840b062010716040000b00050281c241507a5810144e001c1b0340700b292a1700302c00d5000042074004181d08020b266130136050404030ba200886108800904000040020001c04031403501a4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 746552877 1250 746551627 746551639
    0x241501020c04020906070206040b0c120c07140301330b0702030a231c0912032c03010207060b10090f05040b0a030219031202120403061808181905 64
    0x140790400c11000c1c0d0000c921403039010340200310742c0e80140c2c1d4000051004004103826244c0310000f800006041510700001114403010802c01c030800340c4408184001511000c1041001c00400c4a0100c1d00522030458100605201c1380609603880081d9000d015100b00c0304005020040d0b203850b600740352400f80600007905079120f00c10710400143d12510b5100b5520029803182048480d01148505c2c01c040c58050354540d03032118220010035540003c4200207020a0b8213042d4498003182c0d4011b1040000c180011a4400a425181109100008040f091400c01402551503070041d0a24100610707240040c2481100055104c100b0a030141c0c0101045503400308080d0b428610b00814070014066041640c0e030b00ca4080c0d040400181d45a0190729822100190241d01e90383c11460310310482c0c0700c3c107280b0001750f502141c0c0c811440b01e800b80c2280e0590b58040c001003000768600800c166503c40c00140204100c9000c00c070743c07580c0c030070b0b4a02c00070310101c0c100c620599005841d40c1114030009280075003030b007200b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 746554127 1250 746552877 746552893
    0x2c03090d0501090f0305030103030e060903100506060904060f05040c020606031b040212070302180603010803160f05190b01061d0f190807030204110f031605070524150102 75
    0x100c0c05002148406014100205145145548980b000c0000070400c0740464408001401031507445100001814001e8851918029500000079501c0000b200e20b034440d079458034001131240d100c44060f681c0b544e03000b62007406a140c813454040c4441401c1d0003610b005034908041c00c0c0e0100e00c0050354502400700603020385801c0f41c4ca04107000d8040c06528200390480d808100303a8041e1030820220302d01c2640d139640d00584a031602502c6030722a102d1013a00611030402840140074010000c0700310f807101c0c0da01c03010088204409181c0055411448080a0218020641d01541d80904080100300d890310810341841c0e40c2c2e8803100d040d42c501c80120814204001040b8844031207007850502c011000c10024400c180c0c034681510000411384054002c03103c0e0303400c520020400c506140c084c0504100020f10040d0400d01040d20000b05400000c1c0f0080718021050140b5030103034050f8049804150304142500c602c030128203034031200451282d048c1c0c0320041900d07000410071007030180036000040059019189503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 746555377 1250 746554127 746554129
    0x1211040b100c06110301090c11011b03021608070f030206010f0605030f19051f0f030b0606130e04051c0f171009020d1407090b030112140a062c0309 65
    0x40c0030300c0484059969041c501d04c0b05004101441c001c2401da200890045400000207100b41421900100700c0c4c1c0c14120000d2000b4507132840e00d56012114680180c0381c0e410860501494440340b8009400d800c00062450240240c442c8404409400b035022950315998400038105002010b20038100081c60900c040f0b2110030342d8480041c0c104200c10310500624041c142044220f0b1000c0d07464040c8000c091196000030301d613070310b0702c4401440e85d080b4001103d461915642c03a104c0b00103080d43d105441c002100421100d481c91030501a0860f01040c004078a45443d14a40d01c5d07081d900d050400854086035500b18500c6020031f0b0800305200c1d030340c4441d5140d01d07449064448001400b401c2103002c9400700440c0b00801071024283c001a4207201056085458407c1e03820450040c090381d080010380031007444a1503a5070100c0b81107410307000c100b5940010a05022702c010352604203c01c41d074010013030312609000b8150400302541c850416982d00f02420340c007141030304122500802c50990414004605c1d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 746556627 1250 746555377 746555387
    0xa020304060b1f03230a0c0512010b0c100e0a0b070905030f030d0510060906081902042319030f050a02060c030c010608031206041e061211040b10 64
    0x424414600812040800c500196074603103000b555200000721800c01030f00241d414014201c42c1205502180703200c4402d6244d00c010030400a040046072038460140440d9280b251048880100c46420100e04558541d2800c8009500004103000e0900c46c11200710b56030325044c4104845580b545008003c0110240d403103d40302107009240720180002d0310000180c644061043c11300c1107010f2405544ea64010421074022184090802d031201d203545182402400d41082401c8191392203818125016946c0708492107184440081d0308001c18004100058000c00c40f55111a80c1c0e580401c01112030081d2105010380603011740c81135440d07180c0c080420000319a1044407880024003174400d80364240f40540200e08141e000c4806000395501c0003a05003507900007807107a9800741048a02071440c0200a031800b2441c0c40000e881c10384119036820400c0d95004400304480e19645003803000340b007015035910b140d9214480618064981051040b01240e8a01c1c1510816000c00f40080c0000c100648607601211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 746557877 1250 746556627 746556631
    0x30b010803071203110d0917030a090203190302150426090102010b1e0616020312040e0f04050d0f0e12061f23011704060501210b0a020d0603021c020f090c030a0203 72
    0xc08a240d23003850403c00040000841c0700e0241c2140c00314450702184185841c01e00d803000030400d011006911500000d0b800301d0402d14400ca030216034031203922142004074071140000440000e10075220101901d03001480701800790544260000c201540e60030090117600b2880311043c00c21021402442603062030440c024181800210071800004072203640824036101495241000000001c50308100d030300e00c00c10f51503602c10302004049a050034695102d0f580c0340d0703d51604000b1312a00e418007480c1309104081c400d040190080c8005000c11a4402c0d90b03841e90b40c29204106068010302160102810000c4504c04440141d540001c201ca01f08025110b4203c428902030704000c0c1440318000340c289e50b80181c0c1d000e140140780000341e552400c0c15a95858000c510788070a0300012140d038401040c0f0410303905610a850b48805642d85940c02d00100c001d04090704002d41c007103c61551110801000c000005820707100341d03803600314000724030704219914000f190b80b0b1250f1402003000440407801500515 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 746559127 1250 746557877 746557883
    0x50f04030f1112030a051812030618070c120f0c0204020c0a0813081c0210110904021b01051e0712180302010506011215051207030b010803071203110d09 67
    0x40d042d911480000780c100480c500301040150004018040b800e40280324554018607500c2440d40320560001c0c03c15113070390400340248000000800041c82603203400c24017a000700c61b15080c0000b82e10b010304020b01400c0c80d0000540f801c0e540d092000600314040c60310740c51910b106407140e513000384040c3d00b000081d5002c281075400c035004036a010400a0391000140200c40b2010a500649900b400c10310740c40d006c0d461480402c9008075019282d82244c0101c1e507000e0094922101281600074580c806881e44900301242c3d82042c4001030140303010180c101004cc81504c500b000744195100d101a640360701208081e50f004102442e804100b14600440341c0402101c2c01010125840c4503070072a544880050203021f50150b510703181048039660b8803120010010022001c20040b9940303480d21030580d204180280d601030030000ba890b00142074100100d03001154089910204e07584c6032803241f501d80d000440d044419010382c0d5140c0f11000d002e8020b030820b4500b0f0380449070407e00700b051034101410880d2415 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 746560377 1250 746559127 746559137
    0x409021e070302070305060a0b180a0e10141501090b22060801030506060a030c261606080c03070206070309080c0a030306052d0402030613090b01051003050f04030f 72
    0x40e61950a100060314141e80a9005811903600d5401c000c2e003069001045209020b1922040840503940c0206004045902071070065140c0c0d02c8484007801400814228001d6100e9204c44440c1941190000e02404444224401c401d8450b03d000410100002c201c850105901d0042804001d84c0000901001c04100f00341d0b0b401000c0300310715079000325041d40100e000600000010700c1481010413695030824810b42e00c14818130b2540e181c82c0303000201c5000b400004d0b84003140010401204034820b40040381d002e015502500c144034000112109030b4402e80c0c2c0460146030000c3c0c120345190341500d2094055401030040f55a83c1c502c10ae00a03c40010201d500c11018400d0440c409c00401c0083c070704610907100080e0325420041004a10350a01040c0104915090242440c51190708480c42407014156409070312900e890000605400301c1d150080c08040c640102001484410030695040f02c00548000c42001c145040480c1078810490311042c2110b60b84002c940000c3c801c0c689a21401264500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 746561627 1250 746560377 746560417
    0x1809020904030e2704120c1a0a0603150f0b03030712032a0f022a04050417072006040806270d0804050d030c08070c02220203040c0501080c040902 64
    0x900d15004d000107664034000b042440c100802c2000030780c1c0c1a2114940c60038000b0345080f40d581c3c0c00e41803961000021032128641800706020b02140e8100c01e000d5507000c0104d00803003016585a1000344000c54014500070700300941d19003542004001c4031745241d00618180408006d8000940141920a51140602050f1503101600684c85100c03108070300405c3d40d0321000c05911800092a00450400a504490042c03082d0001411a641800c4007010183c07004146c9a60340d0070509a60620b40103007407171101c0001b6016041046203001024292041000300c01080165420f000d00d0380164080c0c007000e0b0f403121006c2102d02c03400ca80508440c1440d0031190b40d0000c0b01840d058140942d0300ca1120200f402070782030208001083c030416041c04000d10301001401500c03400141107404c05000e48060120320b510a40c2551520041c1028446208000e040c1c0c00440000100c000d50040350103480d5a01c02078008a06507202e480710034000c01e0942102e50802e800c044c4514029801440c03480419180c3d516 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 746562877 1250 746561627 746561659
    0x9040506190b090d021509010f05030c0a110307021c050607090b033d050f041119120606050702010e100206070f051b0f0d08010b07120201140c041809020904030e 71
    0x3d106e05421120711005803120f969900140c40380108070103110038020103004000d0411b07217440980d40440104e1505841340652841d51900b14071854801941000d408003007a546c0c0300076080f01c910942e100340c080381c880f07550300d1208a80990807402448007403042040401c024850b000c0e2100320b011401100300d402003c1018501c100f0140460744441c1806103284200070600d0300c014005d81584041d902800b10403103071240b2940300d00c20307030443c0e52001040003450b10340640f0580b0300d40b54003c000d9208020164131101c01034819003100310100d0014200450b00300c0e090425401920003a01d017a001030015444000c0b0603142008a601d01d541000404e100322255840b81050100d0319048480281600c40320082c0350700d0400784140360a82c00d100e5041e00400400d400749048460150300a011038440314042801240544505410215100c80000a001403500000000c00c103c3c0c58002d00031011b50120013031002510711140b03020303601c0201d00f00058003117800350104c042000300040000440201c0d80c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 746564127 1250 746562877 746562889
    0x60d0b060f0d050d09060302120106030c090b0706060e0a0b180c130306061d040b3408010906080c0105070602070618082215031a030109050309040506190b090d02 71
    0xd41920f85501420b00c03040865000b01d41c0d000605a285001d618104640122040b0141c1c18400d4100301540e401c011003c0a00c01c2546c24085c1010105030b6030b41e5101c2c4d041c524043d090328043c41d805004a840840e45406043c0310303403a003041025125805000301d030003001000c608000c0558003804420844003801141030070952000c1c0d032080c400010094180008000210302d60500c0c084407240b95424800401c0d00e02200a60001680304500255481465854180c4200007003088051407840c11940c1c01c2d64105d0400d031306a4039110401c009096030364802c15540d86044982c5408a5000c20116012500390380061212a008010119400c2009100c0d0300d0301d040f000700241e5001d02d02080368500d140c8043c0b501f40482110740300d042c815504003c280c11042c0541c1d50824140b580e650f07410084060f82c2090390005001c020002c0001200904000391240e000740f42052080e880c00c40041d15a00d45250b03840000c5401d17840031a042c41c10b2000300040ca80c0650802680002802c0e11100140ea0f03e07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 746565377 1250 746564127 746564149
    0x1081b060c100522051b010c0b0106030b10320f07050d030b06030705030c0307021606020f010608010c0507080a02070e0c09040b120d03020d090506071e0206060d0b060f 74
    0x4102c00107400d00d4035130701042e000501c10090003d0316542100210100d0070014414100b001e41d00d09620104a04000584525144490080c8140c0e50000005a0760790540e01806989a085d1204042c2c040d010008403200d40b01c000340c0803002d004205c0040d4002c0d021000c0140c101c9840045246020002425084581c1007508212803590059407e462250f526000d540c0c2003c1d4241c501034118188410301410900000b02122101c01c030100010307440610800c60506420208070303c51203882c2c0c50300c000a40701c0340e0b000c0e00314080e5800c2c51000510341005129841c1046540c2c1d4915040403030320b5988817041e80c800c0e09810b08510903444040f80d20801505914006c400c81111a680d070303c3c5501c00e11050300d042d01c10349403145107503401012202c0b10104d02d04038514001d250050341e450614503500010710907003601a10324819102002031007508582400382841c00901c0c900c0d4005030603035040360780391400c5400a400c0010310380340000103081e45190070b0b0820750040c440c40d01d549a590224204510f1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 746566627 1250 746565377 746565403
    0x1909020607150c021009020d02060708071b08010c0518091e0106020d0f050315040f060e0c13171f020c1605100f050f16021206010504050c0301081b060c 67
    0x40c1d180f11003666901002801c81191341c107801802154440d800050000c0440c0343c01a00410340003e0240410250700f0803038901e51b034130001c84040c0d440030000c4034004404a0150700072a41c42c24402038205401402a600c51043c0300000300b188170800c2d4140107407070101910340041030105038440a0f0300c40140902501a00d50b581c000c015410310000010481054000a001030003010030030b102c0c0d41104030b1400015043c2c2650007060440090401c2001801e0642c00700b054a411101449035194884000300841d000c501144074005864034131210308030074060080c0101d40e121011400c44030494074409156510040d5006003082100710059040800f414000c1c4148280e0510920a52911034501e0120070400d1900d06010920000068a54401c107a6505800304001c290700d00b440000c2044a030b111640540080c07070401c0404c1c1615942c000a0242c01d100d1400c010008000c85408000da0b81201c40c0c45009001e58502e046090039201c0e9210041a08a00208192640881c080040c040301c014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 746567877 1250 746566627 746566631
    0xa020c060a030e120a0807030c02031b06010e2203120204050a080a02030d180605131e090c08070f1d1f0305010807060905011206121103010e06190902060715 69
    0x55070360b070340340c1044440840301411319801e22a5606882d800343c0c1d15a8400000c1c21b00050080080d90f0517407440c000c1c01500d060301c08201c1007540e50032101280d25412658000706001e2140c40f03d011075040c29403103106010424104041c43c80c00b2070710035048040240680d40b0010716054585000c1003080419030880c000d03682c0810829011424100922180700090703140c1002082040d000391084d00302e80d8030501081110126100d03244c00d90a010510051044800b1040c00c239902d500d10100c015580e101e904038040c6041d00071481c560103842030078070542c01c0e590b851a015210f0f00c0d041c2c5214800140070310410300d0360303941102d25407100c1c14503146044104500c4100260b002c0c030000d0680c1d0050b00b00740d009800c47c2408101d4690800d030b062007039034400d003407070141c5200c44041d11009041c0c55000200000b00c41542030240f152520303071500f8940041c2e00a0120400115001c1d0b5542c42c01e40f64010746d80c5260514601415082e4806984144000e2034036151081c10707290100e51100e14425002d5542e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 746569127 1250 746567877 746567891
    0x20706091a0708010e0c0c0f0d080709060c030c0807110d060e07081216031b030c03030b0f01080115120e0f0606030706050d0f0f2a0306050904080a020c060a03 70
    0x40540580c6603884030242c40c0140302076040c0105c0c4812540060410700720043c0100702c99151800602803042d509003a0350840c0c0b0034180c503400080007204103555190205181710401b10700c07035100d04141d00382e160701612150000d25481c0d40320b410a900521050383e0100c21008184002d588a01811300c20902640001c60140c1c000001103003014034603480f020307d5601904c00e03071140416000c261204014420b0f0b00006101c1941803c0c1c540007069a1141c7c00d50008002560800d50010b440e00c185a019990401c507200c07458003030114910348445091301240401004020a0f00702000a40d10358416250003443c0564032849602583d400281c1c51a040d00042400c00c00d4980400116038043c40131002070074840d16004020b00148503012446503890303101c520300c20302800c068100e4003070030030b501d102086184e00680b41c0d00701d2020312440308401c011544032860900c2c1e110b40240070980344000c2210147e0740740c5903030b41040c682c80300a600042d40507540300360440d556401c0c0907000c010f1991310b011401c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 746570377 1250 746569127 746569163
    0x30901090303290d02040e0706020d0801210f03090807140301051e0a0e1f020705010e12220902280f0f210f022d0f0d02070609 56
    0x15a81c00c0314540d9103070000c80003c4080b010461000b0b014680183c80d5800c0ea2926030002ca4044c0c40f000100c2032a5103c4d586001800d45d6001400e0005180c00d0381c1c4103201a40c80f80160721041c0c01d248401411040d840303541d000840d000d00c407800c110a11038100100401e9990003841d0070051641e104600c00f281c110b10389034040c01c0c28050f1a902c01c20042c83c0c517100c0d0003032300041c1030009000341800d80c0380c3d5501c0d108a5803010007082402100a41034200d0581400802120400395000748001c9805508240e000780c1c0b070000004079100c00c04030822031141402c02d07000c0544110b21b84006c100b240c0040040c0002507000040c402040100c8210342060400110041008408007145140c042000750b015404220355501c0012fa13102070005203040c10340042c3c1c8090450b400502041d06100380e61604065071680300030380d401080b11030405416040c0c4503c4038041c0e0b150714502e0f5290013140308010446082c2c00d4480c0c0001b000154030f10300e001800d154090f11490102c0f03600d88400c50b007558a80105c201d036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 746571627 1250 746570377 746570381
    0x71421130201180609063905010c02011b0c080409020a050903070b1e0304030c0b150411041a220810050a0510090e0a080d14060d082706030901090303 66
    0x70040364020f041c4030a4584040205510380d548104020000c900b9585213030702d036284403070104040401c003030b908030036448070340b2007828001c0a80c04840941c0b900c41c07001c0c0b4460060180340031888408030043d406c000c1c000b00030754000802e00740413a681b510400000c144407004d0303c0948811340b041d030b0780d664940c2c101e5014945010361503049038490000503c600d00303000d19182d450107402048031000303c0c2c032170302c1b107280a40d080c178035040005000d81c81080400044160000348000c1c0310700101c0f0203121100014a460000e842507001e1002d05c465401040d2185400c824001c1c15180560b5090250383d0110602c0b0bc01d407002150818011038005590560a461041c09516040f0400315070030805800c22101022402c0001c1c4140001261546032000510f1020f014840c05180c0104482e560b4160a0704502e005103604080b48210113a4000880d5a80c1444124000e18039031140701c1c03d15004510380c14041c1541100c0c6035180d142c2851650500e640c84210185000c0e224410000c501c006251070042e00b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 746572877 1250 746571627 746571647
    0x11503021e130e190b2b110402090105030604050405071512050705040503151b0c060a050906090a11060d0c02010510090b01090911041a041508071421130201 69
    0xc03e00c140407050000c48035040d460858814501480041c003003c109000c40c44110304038200d8400404011140c0300080940511010321314495884c2c04607000b0359408210032405110907240c0041c1040c80000d5403810b042e03110a40207070064003120303d1150b07520a0034264220f00f460520001b4900510014040c2c114010316800403000d0420500f040d04140120369950080319140d424804110040382c01e070300b9101c00c500d0318810100300305136441c8920310700d1070b17907401c0c0c281d13090072080b0701d0800050100900490840d0240448101824030170203542c0310144111881401c26a002d101000410400b007421f1043c40321113095038001194038a80f409403006141d01e594003000d0843c0c146401d81c0410ba03407220014082d60f842d0540060009200100b14015000725000011050f2400030480d004810520181080310848050607179074080080c0300310b94401041d0303050710110f00c1a0310307a500100b0001025100c69058820340c0b8041c11410f82e82c0012405081d69501d1304c0444404071102556800f1113241 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 746574127 1250 746572877 746572889
    0x21c050702010c0c030c240207030905030303041e1a0f091b101d100504030c0f0815150910360b0310021c050a090308011503021e13 58
    0x150300c855004e840e4840700740f00181004003070200c02d410003c07000035003694034190418404100040c109001c001b9480000b0039004078a144200042519002003282c2c03007940d21600840d1a65079035007645200d4126054121801202c400350700417010001c0a40c2440798001c100c00031440e042c5020405e05000d498401d1007400016400c101003135840d106901c0c1c0c0d0b0790440d0301c3c0841e950031000380070703a04c44808607141d07a600990360100c0010762170380130f400352060342c0c01006507a48540d0b40f56244038500d00705200d103034459080001d03809840e030b64610015500a850f90b080380c503181064400150b000608984256615482d4042888504500c008580507466200c160490707481d80c400360701e00f540d01c0403a088415651100030000141d102808a942da006d022441075441c0c16110784014102000d0185481180d460200001c211251501902050039011340300c102443e4206101c80403840682c084803c00e264003040562001d0814100c0d0580101a07004020344403554100f241d040420254005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 746575377 1250 746574127 746574131
    0x40605030a02010806060d110f0403061812030c0e09090d0815031c020c121f0204140904061512050f010506090112020a1809140609031c0f021c05070201 67
    0x20010303604488031340c1d0048000c03500720b6200c3c0701c50300148018080b400b50403000d00c140421344022010101c030240050b24131030034041c800750440443e110796210071610301510780301039004580c8a03607019a0120580d1000351821104d5807000b540480c48018051f9401a801c2c1d0203131501501c43e5078044160368000c00d18040c01c041184814001950302d482403c0c0c1c0c87c1c003200c042800c80100b0340c0208822128120701401101219007009499030700d0b41017100e05a1501c070b114841440d070088451085405440c0801401500c4104040900100e150000d00c00c4540c140c1d00e034680380d10005001c52040c0146004c007010b6420303060b02e1401030b00303120980c1c10480d0181e04141c24080c0c0f41e907545007520f040d90b52440c030408143c1050300018200e10310a6100140902083c880c01c440203501d82c100c1250180651600c014110002c00c40d1940c0300c8084504c500342c1c0d0030501000044a040f18448440c411032510045035100390250084200d0303000c08400c0303428100c406940c1101030070600541ea4000528002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 746576627 1250 746575377 746575393
    0x10180309080c1305090f06041406011410080603010905010e0a1709150d0f0f0509160e0105060a030608121201080c0a0b030c0d09030503060102071a090103150905040b040204060503 79
    0x3c41c00100a41e184904200d489400007280007100b088080d00400c2d406040710054100f40c1800020700f00190a084018000c80001061150b0441e004050303d11005d41029034486010408540f0450064580765155407900c84640200700c1c240502c400036403104000d080b5409061602c040620b445c401d8142c0015020301c1280342c107a460b02081d8800c014103403c0c1903580e41c0c11080140c0203001c5294841049454104c40c95400134440d03210501c641d10b100c080b0b46140b50000a0322040c41c540780b049600010f91240184018207103c00500b21405640c00c0108940b9100c629003030501d00c1c0065a441044008a032401c07011580030440303801010004060899841043d0108028950340d010381e140140000001c0342e44400b10070104c2da4401c1d10020104001805480c0082580c2c0c410b0750312500500c0392131000b08a041032141366514070a10104201d240144907801034020f8500e0b440e100051651040c00000d1a2030305008091140340b2840c510f4107107141910401080b40d545410890080d400b90007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 746577877 1250 746576627 746576629
    0x60e030c0a060c082b05071d10090518090724200313141e090a0905070e0403140f07020f060c0d08040b130201020709020c10180309080c 60
    0x20305142541c86074a46a2240c0903030b420500c401d449001d103214905500417014030000403074050070141208a0942c240860b1721a02c600302c0f01940402001c05800342d580e07529403040d00d081180c600aa071850b040180c04c442d614000140d642d5250008a0300b090a03d00800c407a4490078050b14002d0102000607002d584500c101400a6105030300111060040c0c1d90200180e9240036070701361f0785248412044035030760903208840544a0f0b4842c4a0b20f803007405004c024608030f141281800d41201200d01600702000515001c012450b18090179040016a541020030089241840008003808100029000034105450001e080310030101d01d08001c0c400610030004011382441c00c0b943c40a40443d20703990f00c00c40d005c000801920032021481a50700c01c0c54040c590680c0c200e04024440d901413403580e0415600c528600c084403070341400003030058100c02005e002c40d40807580941001035414080340c1e94a106c1104401c00c03101c58503600038000181c1220041015400442d48020b064410b001d481000e07080e01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 746579127 1250 746577877 746577889
    0xb0c03030a05090309040204120209060a0b0a08041419110301090c140406170106061101020310030f08040e04031e030b0f0f01030207150b0915010c0327030309060e030c 74
    0x241007580340c1d584400202c0c90402041044d60408440140119a601c0d950384a114203104541000c0f8080c0d82400009000c0385051070b01a0221684125103500c0c2c4160800700304d034059030081003241c139241002030028009108102c0785080b08070001010000b030020342410211200c4080c0441c0c4030743e0500700d84c040020031800e604002c42d4803401202805081303107000107001d403040c0d030030046024038400102d40002405400c080c04071b078601e44030022076042102d00302b4241c1c03008460740000d078214100c080000541100307113084444d0164001c542002c1c0c5a40b9204d48840c003d40341a0001500c0d642c0080500c1e510317405e078070302c0982c00d03007000c003c09000074000c10200703d1403091061044009001084241c5d01030703011180d00c154402018560226225043c000900c840702d016402850030000144a110500e1504202c101c8140c41d840441e00d181d903401c5440848042c0455110444e00c005105944c001c07030f50440140d80309484001000e0705101e00188409580b100d414440d60200018800c81d40f00d00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 746580377 1250 746579127 746579131
    0x405070513020310090905100c1d040603020f060a050f07080a0e0915010f0c0602031003060b0909070e0c04261009080906070303140406090204060603090b0a0c110102070305070c0b0c0303 82
    0x507032408250710340c41d82041d60038140d1107880b04000c0d80c01c0c03002718807031940e00c0480320000600500c409441c0001a20610003183da02e400002d40046e008000e4454a1501d600074085070400c92030144e2601c01907185802e865003044100f1951a41d000c14140741d82d40d006180d402c140442a02c90005510b00f624003a020040300c2031940d418000c801d00f0010b00075100c0da814039610740d04404155078908080b1031030208601a4031099a41d50301d4034220300e00610b0104052030007001118002e01040d42444101400e07503001a0680c0c903800010070001401d5010295001050203400318240c413104800d80e0070900f000f98141043c640146084540c0c03001a2540b41500c1489805481e440e45038803d0345000d1340100310064921050940710700402c410480070303421400d01c4a01c2a5000d006d481c0d0380d440203805850004200820350031540c2c0000740d0420703560b404825a900e4604c2e010402041030150507003282d01c2103c040e8002180000d20001f031022640d00d1500034209024004c0c6800018240aa00c80c000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 746581627 1250 746580377 746580389
    0x15032b080f04120311070b0126061b0d0f0b090108060712020d0b04141816050f03010f0f02070506010b0f0a1b051f0f06060203090f01170405070513020310 68
    0x85030f00b007042d4441ea1082d1016200e00002c90780d13610b1b4130f0500c907074240f0b000d00c2440400300368042d88518100041815240c0e0301b6104c4001c100c50744a0504401e58000384403c1000445021301c4110504c0b0145d0254110020b2003e50005804661000340444418141c0202034903a0100080c020b60710340c00701200d402c0281002c801a1687d9032981e1000141080b02c4003694800d041405503000e00303800c0320419000d914222130b040980c00700da0750101e446101c41000500404600d220800c039a0618010108007941c0060001500f0312002170540203c8410f14010340c0340b280c5c042103010420404000150141c080b00c0d1906003840c1001803c01410320400d140f88040090700c140c00c6549a40a009011a05a111050b41e000401c8007039040e9500038a040d07410052400d050095a409015200d07160644a06602940c81d1250140078803205040c4031072040d041090780f540c00340107491011034050003540310b080a041a00d10340020030042c40d40c81c0f0303004000c042c810010f00c80d240b0648650300c0c1c12290 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 746582733 1106 746581627 746581643
    0xd1d06090f06010515030703020d0606050901120209130e070305070b09090a09120f050930060c030109200706060906121a15032b080f04 60
    0xb60038498160041501c6400c410000b80c0b4200543d44640a42009460440d2100d91401180d00c240e01ca44005100880c0c00821582d105044204205203900305506054010307000603111008450034034541d6a5401c4001804401805260020b603040000d4440301c9070b48001e54019580302007031451084180f400060303500e420f1442242c1c2100e400c4a800341c85c50100003025038020202000f000c040c08001e102d4000c40c5d1f9602254038080c3c000340301c0340030422000c4800341c1c40007036220340d117012098005070100041c2000042c01c1e20304403040800c0100d09400c00140e124000798003441c0b2156410000540343c400d01c502038004004070340b0440d0b02000aa1b54400d410303182a00005402403804581070700c403c482a560003038140d08401e251a10009501080d00001c0c541490445070f0b08004000608244841c08220054106c520182c10b04003181d1600700d060f9125650001d1005004003 = true := by decide +kernel

theorem cover : BRFrame.Cov 746402877 746582733 := by
  have h0 := BRFrame.cov_init 746402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 746402877 ≤ n) (h2 : n < 746582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
