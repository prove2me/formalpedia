-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1746
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:31:34.532617+00:00
-- url     : https://prove2.me/submissions/e42aba98-bca0-474f-9bd3-8282b1d811fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 313848920 ≤ n < 314028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 313850170 1250 313848920 313848937
    0x2402060c090418210e03060403020706111603140f030a09030b0705040e1014030f0a0813030203070303030204140603220314070b01080d020f03030115090b0304030302131406 76
    0x9031400098419401c0031100304000e0900512008402c44040c0c42c0c000348554096241e549142d45c5406030245030382c0d80300a80b40140541c1184805020040c030910f607074070b02c103141c100840343d00d042c0c0040130004124898100390340d000c540480c003494180c0200a0a040402881300441c6445490070005103401783c07a010041508c052180452460b91040090720017500407640000d0080c01c00006141e801d031101e21446040c4d00305418945414070b00441c3e003503419801c14000e003003004000d503500307400c980c40700d0201e40025000303103008809620200141c00141d03201c1e841c0183d546080081e0018003000c040341d840d1080000f04100904500921050450022a4038651040792024501611148080e9100c2c1c04070034004501d01d001c0c001141001812904110140e48500c6d1010600700d8030342540e00101082d035402000104a12201c403140120030420074680001c036551194114480b41d481910217800007500400e005102c02d40c20107201004002e01880320145c1000c0101140c0c484c050340a2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 313851420 1250 313850170 313850179
    0x10c020f100903030b040f14010605030c16020301060b0304140f060415092f0a12020607030c050c1305180a02030601091d03030a0507080c03060a0506070204090c2402060c09 76
    0xc0c0c2c01c040c02a0001d51a20300e00a100b404407006030741360203005000c9040d83d1466454040000207480d8020f2003200d000745141140c503440c0103611489150368103a0000300b00d07050b40d033b00c0d0b01c0024845460380155000314450303182c1c466800001c02c030f87c615000c03440c85c80310801d400c14024000014030f1910705014480c8101c0020030380c41c40c9414240d41040415013510b05019002c0e105820f0152210310800c0564401c49401d409141c4450000d810030003010402500030380c08200010201e8095440c40d01c1261159041b10550103400e070201e121a4100e43c000b1540ba5100d8003808031a036013110112038140940001810341404c0d9400013a554001031050200c21940c40c50010200320201c035840d11000d001d1000c4035528206540340200802e8101c0300140001c0c048001310f11128601022a8041e0100806e140c0b003140c02c0008104070390b400780000f00c0c0e1041c2c3d81c0c2480d4000500414004000f840064540c004280c00b441c5100c6403034074800303038400c01c64204000704201004a0010f8401c84038050300c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 313852670 1250 313851420 313851431
    0xd080601090e07030e0f33041b080d030920090c03070513030809040605060304082b0905071502030a09090b04060b0c0303011802030717040501020d09080903010c020f10 74
    0x203c2074004081c8110310310320074042c041660b0594400001c032140e041803503540c52103580c10452511416414101640b0a4440e000401724021030710703080f900104110401800501140d442c0031540c981100701e50a100403a032150708a41c2400345800c1103141c0c141c146203554101c0b813000c0001034401d0600401485115501002003641c0710320030700175a81d410444104c00d20b0025182d08046540c0e400502d5030794401c41c113002e00440c4a0a000301074070b004641c005541d5040c03910141400c01e0201071074440c2201200c0150302201d1003400c1d0b01580711201d0044001d4800c540c20301d612030110102c1030b68420b00790b500802c400c10025a02100700303402c031400403900160000d04080080c000c1d0803194400d8100c040003182c20703c816040072000314101c4134400340c070803072042c0c560200381d05034002242c000c4040342e000c810401c000380c00b1040c020380c09407142000600e00404072078071000711a6040da0035140e9040206120f0b2490030f091192034040354040c00200914040070b2401c03696090f07030000b100159510340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 313853920 1250 313852670 313852681
    0x3010e0f040512070f150c0207030b0705070605130506090105060a090e030f0403140d0216091e0e010902190e190e060708060f0405060105030a09021302030c0c0d080601090e 76
    0x43c06500c4a140408510300c0d0341d000345041c05602590903800980c2c400b085030700c100002d01c545104080c12040da58019080440c0340d9206c403284110018480d0040c050100400740018840740705030361081048845001c020400d03414100c1c42c15100400f200c0c0b271a0314240c107102907503a4007024031045a00c0c0c0000454621400701c2c681d82180145001c40240d02c50118002c0304200b4401d1603a0b40b42c2014404460711840c0840b4100e82c3c07560401c1e00e241d06003c03604c4080c81600c2c084c0d00860b0805440410302203d0340c04074070511003101c4600082520903591107805038114548081d503401b0454040c00450f00550800042c0030000038090302c0044080034540e94030030440c00720381103145e9604103c1c040c0c41c07091030100070143c00a0403c03a01a4840d041d03040b13010000e441d0920401c5d00841040c0e4a550a696491130071100901043c94103a03401814014507507201d14043c0000d600c1703010244015a11040070701100391800c0c150499080901c2510001c2001d241d901400c1402198200210040c07640c851 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 313855170 1250 313853920 313853923
    0xc0d020d080612120f0403052401031e020a0f050a0b0408060106230c0d0801051e040f0608160e0c04030f06020706020909130302062202121f0902041103010e0f0405 72
    0x41030513864140c0c030003003074086200000002400c201e0b40214141e075030007001481020407013a4040b034030248006655005001041c6402201929006054103c1455211540014103088060b07030140003845d170100e20070b2160f41803511318600100540442c1707a05090810001c10344901d014001c52040120041c04855034500d541d40c94101e00c4460001c04e40e4680e0f96040740c5880c1c5e040c102800000c12500000000c2c02d05181c143e6000040512880c5120307040c2030400c000190100c40c00340040503468020218649009015441c01141281c08040d48117141c5800000842e4004200c5100240c0038001080811081100380c83c510f40e20010040e516603852900d80028000e40310600d81110111b403c208102c0c0c82151002d281602a0f003c0b034070300b43e41e51440b0f070f0120340c00d40710390300c61640005501070010f0424544105030340c0d40b86800d403400c0301149240715214809400b5040401d646403d00c040560809100368141c5848840049203550704286142240000c09011101144420000030f01401310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 313856420 1250 313855170 313855183
    0x30702030412080325050a0e131103150301060e0103060b19080f0c0402090a0605072d0c090908030606090a0305100f0b03070509280c050c0d020d080612 67
    0xb981d020b00c40c106072007814040115003084885c000d61041490200040a003e8880e80305400e54983d03460346040c00b00b1400700c80503d000d21032a60403d01741c40b06030f201c01500340100c05819002d1804103460386051001da01c140c1ca800c0103114080c0c4d143c40ca040c40113094821101e4152a00410080b9000345400c0208600e0050300d41040c0c1c001442c103001054500002ca0086450780010b800c4a00c001c1c090410401244104548954040d088100030446c99000d03401610844d40900c4509a030b851089a403c6440e401084407460202390118010040080c3c00781800c0103040c00e81001c1110860b00d540c0c00c200b03440051310f4144910b0f408108403910355503000c044005035600070203561000359140c800001401c01646507500890406c1901e013283e0400081c1441144d8004202a1b9551580c95140088420310103010001610001c1510052085402500b08100300c650710305550744001e0440600300046454401c00f1500312001403a01154844400b03a00110304640404464a84035100c82c030b02407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 313857670 1250 313856420 313856429
    0xa03050a1412062716030b06071b0b040f05040908070f060f140c0f090307090509150117060601030b03010905070b030609060d0302060c1317060a0c090501020c04020307020304 77
    0x744005010b19040300000302d95405104181d42560700c00b202d406010344107083c0203407030f00088511000014419260000115402c440350f0400151000c481d41c081040d0354080c0d402510f10420000d403420187c52000e248000421580c2011801e19003413a4034001c5070302d02031280750302c41c6403110020414441014103c5081a6010801a03c81002e610f001c0d030161844200d4407030550f02e02105081e503c07008410381d601c40e1840c51040351900328500d01d40480e642000505580501c150080401d4030348440c41414003405004006111101c0c902c4025080048140c0108150100300306103c094600c0000c1c44641003442404c001c07401c5c0e401040440d004003100342d070103815441020030004550080310001c0d8042c901c01e07036003c204c51fa15202806004646542c0090041c2e1140e0005400440c1c2000940560070081032440e14480d964000045007041a048944a540080043c00945000c5200b001c441c0902410b0604503286400c001070b45644000340400d004540010009a07030a1091003150b0140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 313858920 1250 313857670 313857707
    0x40308061504080d0f0816050405271e071d13020f2d09030607030207081911010f0c05120a02120709140103051b1305030f010207050712050a03050a 65
    0x64500290081413034078901032050214851b0b001041c1e801402c0165003a000189894041c90f141c5094103024489041d4960741090030b2a09003180e03411610418014002d03074050008103d44a100c0c100702c016040041c05203030030310044000050b0166901da00990301c02c4002c03581061504041a6410081d2242482c00c4e02030090020342c0c065101008091040c5403444885010900403030b50074101158803a55151940c55407111002480052094005040741c2d84200001c1d41411882089801c4d48030008444002040088182c0c00040d40d0901c5483c000382000003080c0034030300c0c030120b01402c98494060845a0b202d00080090151411501140c0d181c039254110f806140c50100c100910200d01070107600d0b500d030300420415a440d8402d015060003400140003151440b1140700d001d6446605c42d426a1061200310940082c0f1a9414411403240020303000000d030350748410b480c01c41d01b4070100340c1100c0511400301c0c5030f07032021400c001652a1002e41c1420107a0307982040400640e400c1900014120b1030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 313860170 1250 313858920 313858933
    0x10b031e0703090c0506070309150e0301090c06030f0b0108060d031112091201052809050a0b180123040c2c070f0e100e0a2c04030806150408 62
    0x1c050349644030103038280c02050702d810010780350010843d982c401d0440140005165010900c80c0900c2111600c0b0010f07224103250b02200da161380400d0940302000001e80320112808010070081f03401d40101c0b204a80e54003410000c00701c400e4006403080350f0241c0200d006840840a000800d8043ca04585840101b1011201c108400300920245a4404035025000340c2d216040305008480501a40c1d01891035160b070a1140000080d8407900d00c43c10110700c0343c20035106c03100d14002c0343d024480c1982d01c40c0500c0e0800b0944c64120301841c240c600b50004268181e15018645071a0354803c2d52125080006030800001d075180c40c03c0a071109039003900a429151200521031401c640c400101285034248071104000b1991880c0080e40c40d042c2d0140b1040128494070f4110180c2c3c42d208e04400a0036003a800c09011204100010400d450580e40041c9000725881507403034209180e45c000e101c45103c5202c1a410035181680d0010b0044401400550080954407505102100b080701907070003915403441103e18 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 313861420 1250 313860170 313860181
    0x610021c0302040b121e0906010311130e010b0114090603060d0c080d0e0108070c080a0f0504090c020a020f04022109010b06070501020307090f080a1e050717190b010b031e 75
    0x38081c5c0305030f401c081904000b03848118400c0101e02c00f244504114009050180e00e90745807030407450704001d26aa441b0501200d0007c1000c240d00c00d14070302c1c10429000007002c1901400240009801421016840d5001e10901d4001d60354102126031180003514041e54482052800c0c80c02d286040d0810003190013594441e402503a0f0107841c00701da020b03003680d54202039104c400701a0340c28011200054000f50081106146185c02140703000c00c801c07181d250092a0541d10f000510440c0d000d40340c03100040c0c005000100039894425401d030000c03802110210302d0a0000001600320700c0b0421000f5a4440c4050b0024004600a52080104200240c0070301d43d120810315245000b50300480c0c500000c01d007038440215080d81c3d104408801d65500e040240504000c42e184d9142d4000a51a13040c2c1c0020b1901d170410016030305100714401080500c415851110a01440d6400c00d5808007050070000c800c0d03045a40419840c0e1459811900e0046045680e0b884880c02d0800c0306210b0300f0301e030716542c61503410f101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 313862670 1250 313861420 313861447
    0x60503010b0a1214310305030a0e07030c08030d050108060c070311030705010507030603050d03090803190b0604030302010204170102030c070b0406240f050f0303040608070908150105090610021c0302040b 89
    0x3460b40c0112845c0c2003c141041d6090001c03014100c0f40600018003e0000402070140382c1e111a00c5141d910088907881d035901e81d540c008842c100c0d0843c80082c1c0000c92403941c6c03d41c060080314090030383c1e003001c0d000c64501004a40860b00131000042d04008502d4801c0c06050300174000c0341e664540200086c40a0301e030286000d00a020184011a0103105904070b00000f40e201c0d1141c0c0c0401a44040d80c03600c1c40d00e402140c42c0c00a07542c50384c0504402d69400d03501754184e84a02c014001148660005601c07a868522500203424003050711000c1c40c1d00400c1044030000c9080111212903600c05101c10140d21581480c20003020065120000b00c0e11000c035414085281034903220440d03003072541d45040f0310303120700500450789401c0c07a480d41c150b4414001441ba45002c0c0c03181036800403045c40c002080702d65030130040d0320304002506e2010a55800307030014042400c184596990050302a11141203400418200039521072024240142d07a804000c1305203061441303501101c00821811959079200c5045a1860 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 313863920 1250 313862670 313862701
    0x1018080f06070e1002060604051005060706090b010f030b0a0515091e01061814040e30090d0b0601030216050c0307060c081b01020708041707060503010b0a1214 70
    0x78404034044001c451200d25002000e045101110f901900c4951960002d000249c040648a144000c0e0b8190010809454030b101420105000e900041ba02c60b03800e0810031418401a0020039403010b01101c1030010560511000703402c880b24010016880d41c4400c00c10301440c0420382d2550380070100d101406288291000781107041c0c008040603010990740c900c01960300c03441e030b03668001510b40c00070000c000c441248140c403101d000c07010380089000c06002048600305001da00818910003080301c04c0e6a02c01c10b000c4400301d00650400c140500e4a40ca140004800003241800140307041075000004615901c01d40603115004001b0b00c20f20544100d40c5001034440318000c2c01a402441044000603007903208a1a500c1c0c400d40200040d072402103c5c05050309aa401407a20307540702d41d02000410002a48000100020404103441c600c016903d10001ca040014650004c4100170007032006010790442c4a0450b24030a43c14102007860440140c52040030f4041b040c49208006107620412104988481c840d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 313865170 1250 313863920 313863931
    0x201021207180609080a020d020f0303070b010e0c070201170403031113030302010b0301050c0f0c010b13050106080a092d06090c0503061f030b04020f0a030602271018080f06 76
    0xc02e01c000b0345883e0304480484032449030007100d502c01e000100143c105a16498015400506103102c20182140440c1c03035039000340300440d00182c400004106450010039520f40051900b07590519040d03540c1c000030201c2c881e410110710b9654000c0081030070036029504c60a005008000440e48036450803051210b01111440305074095401c09283c0401c615042c0700e0b480c410020741d02070600b4084181c400d0f031510341060000e22010340d070300c1c0343d000703001d50718404541c1c07007454141d5000c0754075030400400a01211f40900414040b900701070300d020000d40340d00c20070109010794500320320614a01d440c40f10362015401101038034062404100109200100b2102c4061300c1003907003290f540b92140c030310820851030740d20740a5142c046900c0041c00042d114046c03d036007003400102040c560303818100000f06000100e900490f9030681c006004440d070146a05400082c4c0017050401e0b030361045440c080b4a2802204841d0001c01005281d0b410a0301d42d40c032100350240030548215101c181190f02c0740c9940e590280da0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 313866420 1250 313865170 313865207
    0x51609090203031617040f140d02090615120c07051603030c1209031e02030c0a080a1103031605010902190b0d050702030405221b021506010201021207 66
    0x4102004a401003900ea20381c050002d40c60f008540060b00e016201408048440c00655003440c0e48450b0941c3c0030300098451140340605082ca041015110b00f41c4151005002c0c0b0010325244000d65145030300107a000805403030f004005c0c410140101801e2165140c1d0040e00d1014206000840040f20041c0000921450448028101008400d0350056a41c0b01c0180020780340b007410b400041e4000940c20000d4014101a8046500c036500c208090010007007050b480300c0094040b605500d0f0820058400b004266204040c3c00d0074281c0c603e0300d559158101038044080c0c280c586500b61010400c96003030013a03590181d42c03075070700500d4105c0c06041c541c40142d01c2501a1038469203c407400c900315100322198141194a03110606d445034024110091000040d07000611000485841d00c00b24040021405071801d42e200c1c41c5680b92000b2a003031410342d8507205c1d80b10000c6510b026000509040c81d24601000c54105030354050040340684114200609521044024030a900c1c1d08184a07801c103541001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 313867670 1250 313866420 313866463
    0x11030a1a150c06090c102604060e07090c050d05100512061501080f0106031a03010c0e0102100e0303071b0210030b010f08040b1603020c0f030910020a0803060108150d05 74
    0x2003416505c1207203503d0a90301000856030807085500511048124844c201d0f80011319900100d1906420030381240d090740ea00340c654480401d84481444280003502c821101004141004100240f0b00d01030b0040103400380b1740d81c601051101c205003540034001c0c08000c0159240d0150310000a40b00c0c1e100362480c04140030900500c440940c09070640901c260b101c1003d00c206070b864150110041d1a0315400e207601c4920b4440c0a81e2580c8080c05070204560484e00e640c84141411030009190461183c4034801080c03a00080030500c25020007120f410020501c5e2015051080461200a010b20144029130140907d0585054142c158204042d5164243caa180003c490803000361041c00049030f00a1880d80808009490400e03982c4140e858005a45401800c24040d404003510f0b0400c007091260440d4804191801540380861141000b0442c52001c2c00a1040d80c0da90388606010213000107060010320030008041414890106264410080c41c3d080569800e040c284e1b106d08040c181c0c0b0445c1400328 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 313868920 1250 313867670 313867681
    0xe031c0f0302070305030a0902011209080306010e01020604170a09080a05210c1f0b030105010e06030609031309020a0e04090f1509080702060c0705120c0108070311030a1a150c06 78
    0x91007910070142d010f17201c2926542e83c050420f001455400000c0341444040d4401c0c07403a81040f8410000402d03c544242a901e046c44d80000d002424584501380c1158080b200700b2000071654079034405c54a591030001521094a0032041d66102001d07004040301d48501c0d43c2d40c8060050000d100208010054412814880022041501840b51030001c0c2c400ba80308000030020307501a442d0030000d00e062641d00040d0b294812001a082d03a0382a0300103100c1040580074040985001c0c8000e03508642114025880c04072000070600f480101031060042d0b02c0da0103e44072070710901503184401224001402001020010300e81400000d0071024160b540720003400c0e0664158502d0301c62980b0b000d030840306c500d04220003942040416444244900014058210300141d13035102c3c1419400c0900e0041c002e816000203c03030004051724001007041003014180000d180100c400c10080300d0b0003c0c1c0390200803030b9120302c030245000c4441215a45582000014180081c04017040c0b014200d488140003d6404a460341d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 313870170 1250 313868920 313868927
    0xd0902040e0d081005091e0a06051203030405060109141302010c0f1505060a140f130c020d0809030301050109151106090a050106081209010c051f0c0f030c020d050a0e031c0f 76
    0x3c6a89000a0031801e5142d80150210001f00798002e03a44440460201e480d4004034030308200780720fa41d0049034404030a00c0100701c0e05010303035070240c030b980d40e000c0000302c0400c440a10b040c040500000c3e07100c1d00d140b090300d041d039104200e940700c00394008000d050707521000c0c507010261943c040780d100f142a2030b080c0481d55602d0030b400306004852103000c110f00000700d030408100c403000b00c100700e1503408520408147c0c10320b0340c6d0380504140c403c141d80183c03020100c002c0019000d401d000b04a0100c940042005001d135030b030040c2d50881681c1c84036035a20b000e0720100c0340955980e182484c03035003035500c108410400030050000740b03200c81a1090009200e1190399012050b0350701e68814642c41b0707030401441840303807075489180154007160081003128000d288142900c0103901500c01c0c807048a94886001c0792490707030000b01313015001001d0300e000c100c94400d80c40c0094850042050b4203003009400103200420a03c500e43c0e121840d100101901c84000c4109190b507483c0442020b00004030706120003100380d4900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 313871420 1250 313870170 313870189
    0x51c0f1202010b22020f1603170703060f030308090312040b0907080109051002130b070f0c0b03040b01090e1e030301060f020601060f0c0309120b0402040609060b0d0902040e0d081005 80
    0x4403e05014034840714110000c01035000160804040c0c07a0030310041910801e101c440c203100070301075190707210982484049e1052240340182110103050600c0070402000010000560450750540351040e055180c407068641944104c44030340383d2a0300d01006220522030041c1365240291550800c070f85070141c5e2480b120b0300345c0700c1402005e405c90708082a03614030300c0c10b01d4000f00b07024103e0700000c510340c1d82c0743c900130702568000072070656a4440000f0640100a00304481102a100b05001e032030031860543d45d9203c500700b0501130000b90948500c50403079607840c100318482101c819001c4143d890000d84114a9030390700244070b55400990310321106030301e007030012800303034140c0d243c595500d2401c05040800380d5208024801c00c40c108000351000141440d079211043c0aa24461458041b80303040c140100320945100fa0050030301285090410402850702074126011400f418402140110840c00060010034201e4441455806095140c40280d648001a248100170071131980c0e5110392120140550742c1c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 313872670 1250 313871420 313871449
    0x30c0d410406051008030a0f03060b3a18050c0d02030d0509010224040201090b030106120e100513060e010b09040605041b06030603021203030709051c0f1202010b 71
    0xc108030124012444980085510620800c0000400b542d1503025916550102c0352140004c1c041c0059003070020b905016220007480074072400b6091450210107107032403101850080c100065004121000007184444800c59944018001c00000180c035540c28185a403441d81180c3c240504001c0b29218541040a142d02c01c0d0080e0080c03401c020705a034150b9040e40440d040906610901040c9800c60004810020b50315568558200107401e00b0300c00507040c044650400787d41d080043c8010302980703520003a2443c80820445021510321000300d80301d803c040e42c5111060002d4180410803074812107003a0f07040346041c4600c0c0d0801001c1c1d40740c5c1ea2942299407010402d6404a000b03008a0040752070343d0825a0024041c032021103422042c100c54a1101c025a405a000320351580010825880c0c50b0841815014204001c3c43c40c40c035204100810b8200c4034020f0714825030b000d1034101034558010019050665110320728810f881164281a4410721500300c8440040d801d100e02c85086060895200e03d451 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 313873920 1250 313872670 313872791
    0x20408070e04031403040c050f03010905031e07050115061805030c06030613050421110a03050a11060106030f060503030c370602040603060b03011208030c0d 69
    0x1103040c06140c407030312400580141d0421012a1081c819148001c0042d40070b507101d0300c03514850303615041c18440c0c03420701560000c0c0709902d84a404000704002100325510a184090840e00d0340c0c042040b9009036005103100603003190b2806c0758040820300d0141c014400e541850310340910100b00401c0c00143c080480c0102d90b01904003429403480ca0800501440d08a480106800d042580c001290400c0f20812181034840c92088003040b0303588140882d039104a0251840c4c203045d6140448400ca6690180c204000c0801a0015800307a155108600c0c4203d403800d024161259035a40d144020301411407080320036600c601e40740b0001202d290010032654504440c0029005215486602e0481002400085a0200d041240302d5454400d540304015440e03200c1c00c401a1180e05001c0020125540358000315006070b800c00051044449600310f02c552250b0003802c9541e43d960b0120b0901d15070142c090341c85007150400e130103121581c3c130400c1e61440003440c0c9500180c0c150384a0400d902099510b69124484 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 313875170 1250 313873920 313873933
    0x3030c0602090a03210e0607020d08071a010b070201200604110301110a02030304150606080f090312070c0b0a06050d080d09050609030a0f080610050901020106090c03020d050a020408 80
    0x4620703402801000600811001e511992038450f4890100003414070808508100601c20300c4a81004110040d640141d031624244411a07001c01c00702038030810050701c46c4102080340010841c9400c41c070f103072480c181e89000c1c060796950903421016030410b41e4201d0104841c0c0250302c030384c42e0910000e0305403c4c41c210000d111f10344554482e14544041100b4944d0103540312840c204608414900070811140203134000c60b500d26040c1004654082c0d210b980065181c20203004000e100d0b4820300b40d03501b0200300c001d00e100301d481d521101403441c0b05040021048034408010000c01070381009100c1009800703403803c0b00c44ca07624000c44408880b9240201544200000c20240210300080003a01c0c03415000074001404980c962502d0f031505a0843d120040399000265440c1d038117074011540c44030700c1c03014244100d80c2c2c00c00200103400000b090304088108403000c280100c250380b007500500020805075404101d440850301c0010080c1d442062441d41c054200008a15544120710840342202c075a04054050b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 313876420 1250 313875170 313875173
    0xc0608010b1e091206010b04030c0b0406050f03070507020319030305090111030c0c010e010207080702120606010e011d0909011506021f0b180f060a08010b0109140324070e030703030c 80
    0x100c540022401c650401361413402c0b0b04800d202000380034040c10312507045585551440c503045150110b20b17040854a60010302c0700300702c450781010a89441911000c9003540303e42d01d01400f19000d016600c03000e503142c800c40403850b821624a4104482d124083d82d0140a02d943d81800c0a080c0c1e00740e004001d00c801e50400000c0c10321000c0380e01a102e1284024004250941d03507200007030998101600a03100c03030500203250340462404007408030903502e1403030142c02249003040010302002010080c01d418403090923411001c044900c2c0085000090081c1074203a10f05040662038021303c10010000d00960060f100480c0781c50001440c645900f0180710b404203c074008001c4080508580c4c4c0103a50030151424420302c1c1e028100b00310610564104182450302d00c0c00808214100d035aaa000d0341059240203440c00a5913800181700341551910307644580244007900200346014040707070302220f070700246400c1d00410800030703480780d4020005a41c4005600e40d18100700342c2c90340943d1000030003040c1070707109060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 313877670 1250 313876420 313876477
    0xc08190806092d09070905150414090304030204110c03070b0a180213090c05030d02100b2205150d050115060509010f0e04110f0c060708090c040504060906090c0608010b 74
    0x7a800304040080d180c0d4176a0754020001500e1040d540c15904d0b411034040460030382040e2040000c070101080340c61840742080d8600e16140c0c451408003900442c4c543c0440503411a4810803112040c031508102c03982c0788001c3c10804090481a1000c03031000b0308000c00414100721420b00c000140d90000c100304ca40b02e01d02480d4074010490200111002a2409800a12079405021030402e00340c0ca80c010b4165070218013180c400f1980010b141900ca0a60120b00704c041a121030b100c0740203a40103080024140d1200c80c6403400124200300706641c8a800d2103480e80c04c1104c1034000c0c520301c540042c150280d154940c00166114010301c403166002401c00340c0b00301882031107080c0204840c00c0180002400e4650004030180b6640003808200c6a0f120004051001e00002c00c80c40f81d0040f90f92601c0c1010380ac4c1003802503120700402c4e8040d031080c0e46420205050155175444803110fa0f911100c10400350266113482d1521520510500c0042101d400c00043c80404480807288900e440c0e04007034070843c0e02515a103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 313878920 1250 313877670 313877761
    0x10e0a0f0611010b0d0c03140102041211010e150702090c0405030c280906080607020708120a05040f09051603091a2e050a06090807060c0819080609 65
    0x803040c0d0748808130a0000e13100e101a01030101e00500051000c0760450501c928181001d25401c90035030b104100402075500d06c52868964503600c0461600c140f281c040040310000d10b0740a05c40e910900900000d11000d0004004180d090300c2039440990f180d4a00380d00401a000b541304050301500004e44680440c603083c0d00b110015074003a01c01110b1440844511480d251144d0403240e4074135568074051100704420881c0c1680014107200030600310741070020361500e600d040c481d1031200410229035841214026000d690103030001088204403d507462100300c3c080e16040d90308403140085241801d02c454072038042c604c44a0b0300240c0c2c10030303000141410b0106a64000342280740a400c0c0030b4075124007607450102c5441200724103c0440b2114103000c10401f1803034055100d03005020510b2010048544080f5425048861900b005003a0540d54100b04801e8454400c0d0702503400c40c3c030f2200f16070381a08141086e00030501905c0c0c425059650030310054600e6442c0042e48004270700301100c05100f00c1c038890701 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 313880170 1250 313878920 313878947
    0x11d090304030501050f220f1211030304081206060a1b020a03020d05070503060c0c07291b07051203091003021303050a02030c090106140f12040809010e0a0f06 70
    0x1201d2409969403540b6084501c1a203200074418051070901c113055034110030403c0e60484150444683c0b040030740d1850b00021044000811007080140042c44040c01303000c100b02402034071800d513a500d280500e840e10070740d800103d940020810150110340c480c1000303810341c1c0c1c050790b10382c40b000a50140c506d108104c0e200c440e442264058139826000c001602e43c00110208a2711036401040c00034245003c050070000001e00c40768840c41c0c14458112a0321000903840c00b100c40c0d400c1e05041250003040ca403804e880d8849003003a021030f8002102100c60701390617000741c2c2c2c00440b4402d0310b0005403140b080084032141182190800c0d80203000c0384142d0700e04400e808080194a0a005103800140c0880322590f000651040c1c8080d04811222400d5003801e10400c503078101c4c1220b09842d02d604005003d0040820221801c042900c00b155449840300301104035100c650b0030310400021440d02d031900c414a54021042c40e40040c1d04c2c80c40b11407060401ca000f040981700140d40111f01c0c6418610103c1c0c042040840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 313881420 1250 313880170 313880173
    0x51309050c041103240102030a0806030109140321070c0b06280305191e0f050601170c01021516051b031e0a0806010e03011e0e0d0305011d09 62
    0x30301c607030259910700c1090502c0303505019003512803a000d05120f44180c079014614010800401d1684550317a80070044498600c098146140c1944501340400d006007605800140704010310340040000c5000000075106d40c4040603a40c0c11b242008000381c012801c400e85002d80410a40c0d00358800103013000145a03403144d005482c1070340d1183c1c010700548041d039425149071100d0b00c40c00803d10901009110220601c400082c401580300e8882d41e6000d440704c000040118004103034004142045000c103c19250705400078200c8203a540c4858451264402610403284144600190108194000b00e80d0750f003131040841d00b41b4025070b0f0703030414206a242c0c191440d4007006810480d0700da4540c1d42e41003c0515103003501c02162203103090303810080c4840440c001c941026a0030720480a25a90110f10668450420f103004100c959506001c240900059400139130300303041000003060029401d5028014007001002210500c2c0c10500055080f03d40a018891034068003040d00201c004c07000805941000c003a10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 313882670 1250 313881420 313881433
    0x61e120209090c0a1202040e040f0f150f0c080f040305090a1e050910291902010506010e04090c0e060d1709090105040b010507020f0103022517030105130905 69
    0x30005007401c0c40840f65a403000901043c01107042e688140c08824090000d0f004500e49428420402203075a40188020007030b5400b80303034074802c00a00041000f40140c5c40319000203204e12840340f039006000c00c901a040001c4c500900003042c140704801f001c0c011110044030144039201e90f10f049809a10062459400249150380010450386030800b402c0b00e016410040d17001c150800e002c000030484041d0540200c440e801c1c40600c00c02400c031000d14031013240200001101c00141144902c10b000b12110302c0203140300703054090303880c0360107402991040c2000d076100d074000d6600c2c3d0100001c80e010610003401001580c80e0500c4024400748040303801c14002050300e194000130345d8851b005c28407840151400028003156429850602e90344842c05080202e405000c1d00001e04002819801101000303403003041e28184290003a4003a60484010b42111100d00d0b20780081c00c03c00110341c0d0380e104000c54000305034150161450080b40709903410380700700600d5581e1a20703041804070054107484030155814085d64 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 313883920 1250 313882670 313882687
    0x90b040e151c2a0b0417060c160317040b0a0c02061e0903040b04032001030219031a0307080a02090f100e0a020c010f0603050f0c0a0603021e0703030e07061e1202 71
    0x900074100203180e1800d1403035803903003840881b0800044a00e40345006600c00700501002c4a00e520a1f94a080511420740580b11014102250074038104900c201030b1611000a01050020001401e44074200d481340a1101403924017040743da42d0012141e2021000000390036882c1001244130007178000700018112800d15455807458a96030307005500c11120711004840016180440503044820003d0900f0114241040300030541100342010f2403d000b01565481d1494400e00d60003012000326a01908881089841300900ea0781c8174180302c0143d114444d120002604811090503091255044950303140c0221711b070426103c170f140c90180c0324a400b036400f4070804031018002d1140c01074035050700202003a80b501c0d50505606096001041e0041e41c1c00c41460351856441d40d0b00643e04482152500590b200c040d07600507410054041080c2c1c0680000103401d0051541c9604030302030300d01c500810740d6161983c400003541c40141038103c2d802c03c46021130b40c42607000c0c054440c0c110703a6041803901615100c0741 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 313885170 1250 313883920 313883993
    0x1091a07021908070e0603030d05090f160603060902040503070b07030c061b1e0905130e010212060f0a0806010504110403062a140d0c090b040e151c 65
    0x4a120303560411604100300701c50f6a082201c1c00007040c0307029002c8014100306c40440c4c3c0781e03c6200035a214841d11000414a910b03401c21107180d0032030130401600d040701d4401c0c854441040c030f50710455000908103c40400c04085034809ca43c202c40e0001e0042150a01c0c0c0348a24034143c0068400f6814410204000d0003c200780d8021000085020042484031019011000d40043d403a038a942c005017445c0c03182000440d4009100000b91101154034038400794804a2200107031000215400320340d400841d20310405076505040314000c1c1c01c2210100e6030000d5200c14040e94544d2032184410a912103001003041d41029444801003600c00641c141c9025140e4a50105035200b560881e82900358110914001e40d4121403180404007103071500b01403402680e009004c85000702d1a2503030240740d4400e40d02d0b0003540a1001d4100414051900ad42c54035543d0703030000003080007103620160b50003214040c1e0400d031800001301c0e2001028064120403a54441e00d62400d00c0045a1303405061100c402c1e984a10640c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 313886420 1250 313885170 313885189
    0x50c060c0c0301050f0405100e0c0a0f08010b03120706050a1512020108180d050c1005010b0d0b101205060d0605180c0f0f01080a060b070309170c01091a0702 69
    0x103260006000c0306507403209160071200001c086500c180864028440015804110800314069014010a0350100418124200301e200c0c024030354030806500700024501043c0d6003280845414900030000c0c46090802d0585400c5000101952000e0400c500000504141d00c9036030020170804c800217a485a107000b0108811541d0002400901e104090504541c1e00008055000e070301c407000705c0084000c1d01020381c1d883c50141d080200b03029000c2074001c8154000c0000c00b020288070700b001c0c0015650344c05e80d42410307440708440401d03444c2003401100050400c1e08618024040d60b640c0c6800d1084008002e00c0100030242c8240c0d400455903407000041105401000e009107078807503420301512513009040b0b1400b10328003407550003011001105c10141e0749500780740c01a0308003070a050105540740100e80c801003882e81c020030032039000460444140b55001016100341da6298440030319400301c010240342d4138200c410181d0300060344008e0500c011000560340c006170f101007890700ca0034410700d6800144442c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 313887670 1250 313886420 313886437
    0x705040503152a0409020a0e090f0103050f0a05031b0a02030114070e090118020702010908010c0f08011409070e0f0a030f0204050105010c080a032d1e15050d050c06 72
    0x82c0c034081480000240300c503070760399500008084100f40407032000302e814030f0b409140b181440d90b55000c150091501e0140b021004100383c0101010018613010150318280d90080c003060b562403003415131032041c112000850001c1c845e08100114184103240d143c0507440000d4040d80049402004440001600c0074001c145540701000030034034007860848d00003031000340a000d2103840750010000410201c6001a116204813100313107005691000c49000581b00e510302c55004408943c603020000c01c0150380503035110700017210766803009001d0b41c0c0e03050b6000c410b03100701d51542e511102042c04204e08900030144841c280e240a042d90100785a0040010f14442050307105540800c00040e4200c00c42c50b1610500740513210908080c41141c0160321041900e02030701100406243e999100d01d4001201400341c8a02c0c40000011a075000c0e080c0d4010501904c10041c500410060400c0c0040070303145207000e1054040280d58848403640d01c1c2c401040b18250840c00c0555042c081d507400c20b00f064464030018a0140d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 313888920 1250 313887670 313887703
    0x21c0503070627150f1104060c02030c01080405060f040c09020d150609151110020a050714010608150408090603161b02061b010f15030201021c0c03080705040503 71
    0x1c034002d4041940c2c1e1070006a030f00c41000c648540310001642084002d25034440760b0310004103040c240d98241c004007032490b880500c42c01d001c100040c0b0982c2c00100d0301242c501c00c1e8295a44181101c00544510406450081c002e07005030b4005080e94490303040456201e401085240c0390726075107124000490b4405030f00b1150140d1260b01c918403180c2c028040c10024070191802d03000c12490581c104050358860b660400030401c0c03800355803282c24000c01132038144110482c0115580c0c541d0030b030080c1040c0d116250846151030400820307007101e20184581000c907825403024081c0300c4401c0b0740c480a00d1000030000c498102c010300002c0401e07201e81014501c41c1610001400303072407400c0030015081c291110740395013288441c00c00507001a00e881096855480341c2403140c050400281c4011030140036408000701d006840e15120b8542801c1141070b54044034000c0e0242e8112580c5001ccd0350031491607054005000c61203240300c02c0c0000e07106039000d0354010400d24100342000e4480c3c1c0068106080c48075202d901 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 313890170 1250 313888920 313888931
    0x1b030201020601050306220302030d020f0d0b0a082d01060806061e01050f0a02010e1f0c02060903091c15090303141005010503130c0801150501110a021c05030706 71
    0x11035804001070b5001d07043c214020070407854003260408807031550303100c25580803c192041c4020940200103450410003165002d6456410307001900d11280c0101542d680040d08059941d4614140340c1c4200050311002c0f005041010000016080c4102810480c141d06031040c1802442e03041080c42400c001e03190031806002c040c1400f0080000740c641c1e14400c2c1c043c20031105900322050b0380105c2154a4002c9088007952180b8240a003680180a5200e61001a0107450181d280c42440e4500e002ca100782c007903004002103818401c0490b52400100d4a060b003650040140940754544240c4500003201320780d101103995141c590300c9041c90380000c4030b2031200356102e136004810990103005a405010b2001c0d0040f40625001540b100340300d405100c1e2a0601c4800000304610748032000b92020038031f4005035851015a900d030480c038020107500d24100e400f12406031000c10f880d07120b4404030b40c0310410301d4010092000c1c00e8017042000e04400c44140c0e42d0400c10301103440058400d1014104a07402614000340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 313891420 1250 313890170 313890173
    0xf0f1b0c0314072403091406070f021605060c0a12030c0206060d11221a040c141903090f030e010905030f1015050a030c090606031a040902030a1b03 65
    0x2032850700c10b484640283c110100034460a41300602c0e000c22121642d41300c0c40895005281134000b041c4a1a0140003c4910502907d162400240c05801115181c1e111020f078100309904984031048983c0840c0551003080b03040001d8940714000c1c000d1414444140e40841e0f21541c1d41400d484480081480402c0e26600100f000c00d40511089502090945070b83c20701d10110b03980e46030030700d40401c1c0c4d40c1d100c0c45a52010100001880505405154003403404110011602c00501c1e801140003c601d0b00c0343e402d2065000242d0f03c115106080950400d400d80e040011407180d41402410300d1294600700342d0340d0b0700d03650041503925440200f541c3c025200c00100d407090400040080211340c109a00a511103450034031181400070341c0c40d0144400c40000100d070031020380440f6803051281c0c407465219541240210034800324600340c1c011103080c14030420a6a0740c500d000d50a4908103551a00824004481031a06007402d400001c802803000702601d95803440365540c01101b41984000101c0114000f10520 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 313892670 1250 313891420 313891433
    0x2040b0307020d080a1a300c030708070806010b0c0a1a01090c08190c0c08030403090e0a050402030d0c0218010b0307030b01020c030a02211002030a0f0209010f0f1b0c03 74
    0x303800a003100d8040c041500c904031b030320703c81c1c5207620702c481d018010403140c10344021700e5503000310340c031443d9600401d9103000a203001940e034900e8480e000c0c0c8240160000054851030000b00102154541400381034580e00c2c0251100f200c0d04040f017000076a024a40180300081d06210504ca950300d045803c420b12075041c801d0f040c080340e20801d8800144501003042c07040d004003001c103400803443c0300b000200380a503ca0000701c411482c0c0107001841d10b00c000c4188400c05070001c40100a0314001800c089403580c032200c00400b0758034262000394060f000311048141e00c0c0c0c45500c0424880380003504000407543c408070840c2c1010001d038807c0c1d60b619804001e009016916010320045054248020203141c003205001a80300c090401000b840383d540317003c0d10311603020604443c0401540040c00c0d00c5c5c0c195444a55003001e588111a24234029141c00e1210400900038400d8900148040c4d680c08003400c41500141c603400d1007005d4810070310980e070070f05408418000d600c4041c0306100b900000c25944c41d61510701c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 313893920 1250 313892670 313892687
    0xc1c08040c05060d0f0216050d080115030f06120c0501020111040321021c052101150e0a12050102211e04030e270f0c0f03060402040b0307020d 63
    0x400210800340008160007848030416500c2c00c0b00c8280d504d110141000300100b48a460142c1440d00200d00303514a0500c0f03409003264140203409451444000c0d2000310fa0181c000d000e6500004600150380280328400d60101c956620703c088001050ac1e1207046a01c181340c00607a00f207030000d030041400d01095a080c001d44188050180c0310b94106401e50b0744241c00d15015101030800d160008002c04000c51003000343d990110782d140c402c10141603100302c00902640c0011842c9030201c440d0120080c02c4d1200c50a014101c034070040a15054100d0541d00300d5a50182c0f0324401d61004404c4404520002d0078600a545144548001655000c5c00701d90600483d03089840c000e032030911201004449081050022030710002d02d41042802c0e5524581070300c000761008529070b002400001e88204902c01071481c2000012019408801c940e61510b681c604440c1c00c90b4801d0f49240c080c850104d2440c80342002c0c54121500074005401e06031101185c4545801c101c980900580c044401d020700580c210f03001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 313895170 1250 313893920 313893973
    0xd060501151d012007050d03090305060c03150108100305070b0d0506040c21020d02120103150905032a060a0519021206061605010c02030901120b030607180b0c 70
    0x14007001901c050000e009015003400c005824104d00304030088018050021002510f0001c1c0107118048030350400070104421030004980e18030070038011800035011003080d40c1c807500700c091641c02c8050000004441010020340410340707403100a034010001138810710101d009400c400040d1030702c070541c180c94141135800103000240164a40349480d05411ba0240026103190249620750404206801c6640001c0c41141c980441c010710200e55030704c2c4a80c99503400d9040740e00540180303410000391507106c0c044590f088802041030780704001d0444102380590543c0413280498086804000c0340c2590903003081011180c898180340e4440070004810032400c1204490610340ca400c5081051000901d0411072010b05800d02c910000b00d91024980706a42e1000070059000e0000e21000700d802501960329003161f050b940c089681400407425142052040401c2004005d00801320358403910380c1074407080400300081c1500c2c0440031000c01c5103d901c1e0b004110805020b80107091b80f1030701c2580c0e030b10905280c548 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 313896420 1250 313895170 313895207
    0x106090203090c0d15090c0b04030c060807210c020f010509010504030809210d020c010906050108071d0604050403050c061f09020403200a090e0309040b0a06020601140d06050115 78
    0x400d000300c1c56581714500e010480c2000000d641c1c0050411070400300c49940440c4440500103008010030010304c80c0708040307e14644848060b51214401a60384001400c200210569041600c0401030115080400b0342a49801581d40541d03422194030300792982100c2a000aa444000307201c10982d01c0006158807a102c8009004134a142c0c000e42e44030040c085455881065003c03c8400366003640d541240d0907144414003c2040780500c0c60403c2c09002d0911921000b401000030010b406001d588501503d00c0c0340558051280c0e8a0500b040000d107800f80c0154100700e8107000803100350382c04108043c0204070020942c0c5902c860350380350b500080c0741c40d000301c907115005004c200002184040300045c0320100ca9603994141542c40049011741055500100c9124104544100f56034408402084000015282840540d202e034051001405052003000c0c010792103d001040007000102440f0b4290300e00402c100c0390f113006501c615090322020307080301650000442c0c0456501e03030020307042e010380485d605 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 313897670 1250 313896420 313896439
    0x102001020415050a090f030b0a05060301050601020d0503100902070807110f061209120d020c070503030405090402060703030b09041a240d030207030507080c03070803030906010302120c030106090203090c 89
    0x10b589446000c0c0a2500009128010456507851070207603090b407014100e0001c04e20007960b0369080041903982c0595603103da441c54100412050305041c05158452070040e001020349182c0c2c1101280c403584001d110525042d041c0d41c000c21101201c0c0000c141041c0a280300d0ad4442038582071140103205145034541c81524013001c10210303503c0c0e4505031400a10b20312880344280c3d48429015080038600041c000404800150003100c0b140030758080c0034220700b0402103802883e218014569240b082e4040d02c0c0d800b081480c0043c0040c9001c1005083e0940710303140c0480c0b2151040046050848152404c42d91258003551800070f40e4052200740d9032284c1340c2442d251601d028a0900d5440c0e40034410128001c5542d94500401d01d40200166801158428111036840d82d40f00c0c0307415112070440c00840c0c440e00171f03040c6c00224101e000040c0c038080e801540150503146d10303507400c000c1c1c501070f50700e1040e54a008159142010796028401c03c0014140c00901503513a242405145003006003980c0c59510680504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 313898920 1250 313897670 313897679
    0x17150903130e10030f02061b032203020a0905071b0c0303030b0d020d140307050a110f010503190207020d080319060510080417070b070203090a09020f0313030e1020010204 75
    0x240103250413242c220185655122090011611500c070340000b407600b4000c0421198203440c0b000004210300c10206080e41c4400d103807001640c000031018840a544040c07006010300262480e540016080303516810b14640c410f004001a400c0c0d0700306032000341c03002d144100080051580600a4900c8480110742c0c0000400d4141d000510000e400007001d811200c1c180d24108030540c0030003c80302c406411408540100c15a803420b10399640e0010201c0340030380d144d210310100e594090740940e8020700b8214210340b100c0182080410003034000903c1179911000003000600071a003c00001d501508a0141c0b0700f4088100c0079228041d01d440340d01080c0500324059180604980c4004c2e01038000c1c3e404404a0301e01d0389030200041c41801010400b50090300184e05000e400d0f90000028407141c40706860895505558080e040100d0096803841d080c0d200d420000215184040316020004038404e04141a1111610780490042008042c81c203001c02c0a46035204403248512043c984070041e81d0340298a0107050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 313900170 1250 313898920 313898941
    0x3010602030a030c020c131d0c0604030f0c0f030b0604050106050a0e0609040f0e030324010c0807060e0f1f06050a051c0b2706060a17150903130e 64
    0x40d090b04000705a5604440c01081e0310903c809290240020008200c2000000440c0010500c56100c0040c1c080c0300d0105490499000c140000d162000401560415103162514415041c4082c421180760034100340c0800ca0303600390514000030b140508452411841d2140602040b220f041e040002441014045201500c2d8861440300003500103a616a86803044031010a004d01850160150f200b42404c424072039144001019520845a4040c51a0300e90407118500b100403100039803881c00034400a17218400b01e54600004c2c040144074290002c2c00d01d00005000381440240714001d060390b040218401d01000c04942c622402c106804030412001c0d1803c000990003070070074410039002c1c245520039090070b00b03445092600c4490700322201441c80d190421940d500c6201c400008a00c100c1c401c60112062103001034030502c04c050280c60403a01600305607008104517010b50034500343c1c0c4126a4405c5194550500b11401910240c00440d2680100d40310342c100b1190039004224050f00f01c40030415022034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 313901420 1250 313900170 313900177
    0x5030f0705090a1802060a030e06010e0c0316021903030605010f050316030519090305040e0c031302011103160803010806160c02060d0b0607200406030f060b030a02030a030c050d050301060203 84
    0xa600030009404020b4071030084c03600340000c00070307500801c08140300200c81d230180c0007440107d600318191a2a683c17288420000180181d03246288500280001808044a0301800b10454800e0045030903d1002c14002c0c41c02d45004c0b0421030000c3d884240030404e558001d07031007210112041c10a54107516050000d455200040288401019240c0d404113120752140103455000c100f910a042c041c4001a041c0600203a000340329101175800000700240c00c500c001e10603a030150320710140400000c8055001156099600520003001b030004000350b100481421202c0d0021a1051354041c0e225031415101c1428158010207600301030940d2606148565401001c500d401075045030b510751100d0741c0c682140001e00b030f0145902c0d0800c0700090305d8000c0c000c0020704001e982d5005460414450801400d101c00d0368098480100070800007d1042c2c002240c0341c00c1412a0b85002e8202c4007128031070707000645803a0136607205801150ba0b0844460500c43d0a0001512860315418268903651404100a5481c032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 313902670 1250 313901420 313901431
    0xa09090515041b15080109060e06190b0412110603010e0c0a031d0606040e0706050a080405101b030b040c050a1206050a3201090e091203040c05030f070509 68
    0x280280040d04015204440382003a010260054980f51303151188a2280002d0380140c4000c0789203a4000124141d03540038140503180b84041c807092940320203040c0a40c0001d6201102035940c0310040c049280054070000c0e00080c0a40c0b4007122001e08c2a09000b00441d003d0002180110340800040c040c0303103186006140c06c420b1451781c20765101090141180240000c1c0080c0101e0300301d5030341e86141a07a0000714076004410440742000002c040810f001d56411144c4596030200740140035501c081ca0003201e1040c0d205004000352001c1c4000c42090600301e0303039035850343d4101e5001030526082255051182201c2044203031002c00c180d0a2400016042e03000b241b000707070100804108003c2c010413076900300b140240070107010084040e4452141c1035403000106a107107410410070000840051500990000350039060b100c0aa4403400c0c185510b108650052000001e0300c00e800d140382d4090150001584118022003511120500b00004c160030805c040260049e0350740005014416030361011103164000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 313903920 1250 313902670 313902703
    0x70603060e040c330309120309030207050f06090306010602071811030f19050f0603010c0518102109020f01030b010806060a020f030403050307170f1204060f0504110a090905 76
    0x500e4546020848403202c1e05144c04010504a5130300344550150440d0703280c80d11031421117200d404003000490890754030700e00290059021002c20012800c20094a803031040300604031502c0c00c0c1d5910003091034004203a12400060b4451071003007042c010045058000502c000c10140320386251100382d0741482c000509044030314103017038000c503000c411912501c1142064983c402d015624191060210302d081c202c5001c0d000f542000600e4038158400c0044034900740c407130503031001c100b40c04806010784a028414081c00380405944008180f00c800402c0c9030240040181c040740c1007a551051000e552031175043c6d58107245c14000100e0140e80c00030202e56000c0303000c0e82c0f0f031600c8000c900710888c582a4020b00c201b07494040000c01005004c0040003d1006502514804920a03602001802c0a110341030304403d40140a000e94095030058401081c0c00038050746001c50381e00d0303040c2c03405022a40190f60407204d0a204610b01507407400e00c100d100b4010200c21404021000c490740b0303020307113450450403400e210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 313905170 1250 313903920 313903949
    0x2506120f06050301090b060f040e0604110a080f0a050d050a0203070303091e0f020306091603080c0304090c050d0c05160204020706060b030f0f0108030712030e0a02030d02070603060e040c 82
    0x1069100320700411000b4002d21107040305003080407900c08140c0d403050040006030030030181c81c02e150050101c456003a000600440ea255110800c590003200c03021350b031000300c3c16000110a0401c02440d034900020300b010748000409854664a85004079060109018003400380c030305580c0e004010385020503003604010885800a1a08420b5008400c0d103042103d88400c0c2c68806020814000d8140144290b049800b2034950300c00301d40d0b5501c0f8140001048102c40d8005100160b864800341c01440c0f8607204890509031603d9060003560811310315080020008106404019424000c80c00c03119500c4c1020351400c8060b9200701c01c0030208bc034020340a1500050403904000c229070160000703061585070319440c3c1c01c0101c18100144800c0c1e410814000d82c400001c03d10b03040c04011030760b2032540030360381005610040c00700b5009445510b661141c0e50080001240143c3c80038070003504040070a0303000e40207860514034050101e5031785811010f0071004400c200000664402001001e0726410401e00e003a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 313906420 1250 313905170 313905191
    0x1150e24040602010204050411040b07031b06051320060313020a05090109050103021207080303060112150816090203190e24060906010512062101020c250612 69
    0x20002600c11418004000003500092056041d8058019036070704607000d01c400c0701c1e0172039100d0583c01a0f024418650f0f6003049031800007070007030902001126110b4145000300c031458860f8422900112910790f0240403004105080000006070303035200c3d86e076400c0741001488104021031a0350000600010300c01c10200d501c40191740c2d41c00c0b619001000c1c01400c014507503840346030300c8010f0182032008034011110115156403412012480d40c1c1560031000c029406c60341e80e1801101d41c1103004694490300c5030740381210f62103250310005850150511000505946400541e409128100da5000041043c0f06205001d6555140c00c2c0103141c0304240600410014280720b41c3d94144506440000d0645e5412980940c0000c3c5001d506441814103d8040107940e07078820042d01c40388582500301c5400d282c5440050a54a0703c4050040000420103c049003108071f00c184a08aa0040c0344a039181c0d40b08aa0044c4055000c000003054000784613041c540543c508000034103007a1031501f00d50030f8541c03200003884 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 313907670 1250 313906420 313906459
    0xb030a171b070f05040608030a0e010e0a090e1f0c020c0d05031207030f1103041a040c1d010e01050f01020d390b0a05090a020111030d09031701150e 65
    0x20404207014103840c40c80d603443d108440040c44502c0380398000d03800c100002034032240101c159404200d150701e946c030115101000454a03544810a141e80c1303d01e001101250696692040d0b20800303055100030f103800040e21110103800c59520300c0320f050b03507410301c0285845907501045880100c207017076907030301c402d4501da11300f1a0540c0654190310150b48500350400031400d0785070b00602150003a461007003014106040c00d078040c0c3d00c41294040c0c8100000d402c1303030b001e4011602c1d050f58482d0040000d001516141c9281c20b070a2044505654410b00b00c1c0001848810207082c00c86005207021210395410311500d4bc0084e44460071000713408240110500c402c085426807485108900020b940507001c40c029003000104550b0090b0300949101300103030002103807442d45103d002c1c0541d0314180100122a1254011100c8011620001600c0d00041c09072491107032050140300d548610035142d503600c010700150306000f03507203050f80161044848200403d02e00fa07003003102281e280d10240c5048501142281e200c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 313908920 1250 313907670 313907707
    0x21c0f09050d08040b100b0a0f0c170702040e07050312070c030503040306020a02010b0406060219020d1e05060708040309060e1807080601090515090d14061005040b030a17 75
    0x1030068051010101d041a0307000f420309200d248130703d00124035174a6a0314104441c00a0703000303001d46580c00300312a12201d030051170301004800040c0703440482d8003801c1d694148043e015055220301040040341e42c00451405000303000c0d034036000c400100341e42850103001a542d030f100d501111440e42ca00042c078006020205025030040c5411008482d40d0355640c0c5000c4c0001d42c803400300c11b8015403070700c000f403400303171402c2d000d0401100c1c1d99031300070015201ca0301c0f900e5146600b40c400032a4401800c003000c0000800d5040c0c1c3c00c1c68000703010b860044514090a16600f0724000410101c00c12001804000000c0c0c4c1180002c416200c0c145004034002d800750b00480d0111000ca50403000d03100580782000040d07030740500e2407441500280e850b030100c035607610148021100e40303007040e28a0b4401401160940c1c20201c440442c0039014240c054801c016039180942402410b48a111440035038060501c51070805010708048200d05800900200c09070f910703894401100250010401d0b0310004e01040d0202d131000d881c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 313910170 1250 313908920 313908923
    0x402090109112106040b0f03060a02030702031c0243030c02120a050705060a0c08090f0d0606061d10030f0b181e0108061303090b0c060a060801021c0f09 67
    0x3000c2001103d001c6204605800c541282c441d500b499104544d60a0049000d00c000f607024004040c542c8030f500b680c0001c5e41004003014110f03c4144030505911010b00100c0c00701c6000c0c203000580e40c2400d10719178105169110140164070588603407408030349514401e1602c90121041707c0b0202440da510f0205c6243c0b180c0c400195028a02c01c94108200e400031038030244041c0300704200c44000340c0c2c030024401c19008428600b8007044082c200c40780071600380c800070144607000401e0048190341520006d000160104001d0700d10b541c1c0d582091000c00d1f04080c0280400184c2c1002001c8104030400260085180e080c0ca1002c06498140c540c0e100c003200d401c40301c0c10401c0140352100d85000114900304800084407031410881846281d040d245204552540c140d03100300d0064034584c0d8031840c0c000c0c00b190081d04200d0403c01c010b00e000520b0041c4202500d00c41d10640c01902060801410160039141d82ea08002800d910412404074000108080350903001207621005c251044009040720050184010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 313911420 1250 313910170 313910197
    0x31214070b06040615020c010e031903020f0609030708180f0619090e090307170c0a030f11070f050f060d05090703030807170c031317040518040209010911 68
    0x100503003082004001c142c800c020607241042a159112a010007851284001d0400b603006609016845d520910740f5402c00c440207030444040f003400008440711a0000203069005800140c3c0c050135014050140e01c0e0050030190003941050025100c000b81445410b071608103c2152030407078402c50301c5150801e160610000c28043d02da01e403020400304107040e1170894400013083c1075404134840c0c0410407480e000d01021030007141405c4041d034800c8015030103250200d1091005001c601010a02000300342e40ca07a101c2d907a4910b690900b101e000d02455805201d0140ca070308205400e0010310b4503c40c0c1d0304200c6c2c40880e08d0202e407410160108003d0301c10f07400c507807200c00e0802c010032401080c0007941d542160b10a998449441d92006000c503080d45251038880c00140d00d40e800704050170723034043c0a15004021180410014101d50b901d0000b8002c2c18106002c0b00200418108100d01c0d01c0040c8560760004004209041d15150703000468015050081c003d12941e02c0381030854004c02481515144d01920a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 313912670 1250 313911420 313911427
    0x5030d1e061401090509010b07081615020409051501021b01031e09030906050f18010e03061005120d140d1104060201062105061504020904140108070602060c04031214 73
    0xea110360140c240c0002c5000c00c4500c10009254104201c801b0304036801540070604104441c0e80340c83c61940101040e081114030302030400089441340204a011b00101c9500583c1e4500d001e0f143c80c161580144954525442c1000400190341c0102c0c0010051005e00340d440b154480100042e001491011008900b45969503855103084000d40c2c0081c041c0d030302a444580d915a55200215410b01c00ca8016566a40d000d001c21001801c0f80e01a04a8032441414080d80315101c52000c00e1410408a50b00303140c042500a04000a0819090300030590304a074014201d041e00710000900080784a485404a483c00004c840c5816520f031782c0a1035806202c4c0240aa0740c41da0703510024007a2040b4003503040000d90722111480952280282c05102d00c0c1d00201500d80d55032109600c5c201c103004281d540ea04143c00b00300701405030342c492241c49010070b6101e00d43c01e444c2d414961450728020603500200705640c031007801d104d1040c414405641c1200d41c00f440c0c0e003014540c103610844603040030102c03541d900306010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 313913920 1250 313912670 313912679
    0x3030b0a15090f0f060c0f0816080d06050f03071a090a0f06021b0a05060a0908010e0a030206060303041208070f05010c080402030d18090f0b090c03041e05030d1e06 72
    0x4009070342290502e0340e401a0940e1030f6900c4c40ca00e02c60358810140858091803100002506040103a81c465003c2e179641400c003580f00c1c3c0b410906c1c92642c08100d4004c0000503a05002d0311513441020007804050703c10422031144040420340d284400d0181840d00c10748800034600109052040340e040910182110036810740d5072000c105554854021b150150144095a2160444826a09003005c00003840c1030001881c000c14001e05602c00c24214007003089840003c2500b440034054442e81e0110075008000190060070001c1c103081002d04042c1c483c0e041000101310000304880c07a088241d4015410a0b5030300f00910382071500d009000b8008040d0750814400c1c02c20b20740c0000e251481076009806448220364602e208881e942e038840008440c0340c0394840c09015a5120303510440d600c0d0401580040e040f0902d10006403400400c44030380d0b4514500200300010404280761f0110940301c80c50841e0420329150740c1d0584c503401210700d100c08003907031030b041d041d00000300c16031140c0000300342541001029101c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 313915170 1250 313913920 313913927
    0x2041e0b010906020307020d0b070509100806011b020306040206030606130914010909200d0c030807110315042009070801030308071809090501020f1308010b0f0d03030b0a15 76
    0x880100c2400300d0244180080e400b4008000c80c2d40580c1e00404000d401e1b890313951401c00d03182001d0039420070030034117000c18078103622403822140c280e18603600c03a00002d29010000410110a4400040c8200504414040180c500007101508260b04036000c03130b107a0342c0d5a0b022a503240034001d036605803443d451800042d441c00562001d8100c072941260081d41c0d0f038035640d1000581c1d070001001803d858008250802140341003030110000d00340145103508032000c0341c0714141020143e03001600c0f09000007030300400300300b0107210a0010f00c20650141000c05015040500c1d4600300800240c0340e5007c62003454100c02086134401415100240170720350074205a013004048040c01d020413404980b10002103002c0c10302620707403c8000102c07010010481409c00001001a1440b501e0032951076400b8409201c0d010741041c090641c01004079101403403d482d000314103094880051026006022281d141c03000c685810f40d00501558250a0100700ba1030900b011410380e110691010310903440c40c200e040f10b400e50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 313916420 1250 313915170 313915181
    0xc060d021e040e0604090302060403080402190e01170708070b07150f020a020f16031523090c19060c1502030109020c16050604030b090c0618011e05090d02041e 70
    0x241510210f1080ea164820303c0f04071112000094090f83c009000640000d12071b414040c1d002d88041c102071018041c841c104208818241c202c40381244100005002180c0c450082d4041426030000800d4520705c0c008050b40c81d030001e406041007030500008c20300d091010b2003004928019018808000c2d070082d00c0a1200250010803100c40180502e503001822118001021a00d1090403aa10f00101f480d5960750092114041c500c0d030000c43d2a0808803034856035240f40ca02c008050740706850f809141c40c0c24118200750548d11500c0c031072180400c00f020814099861102950407030705016000c0e0215040642da44140d400c0c6002e181400040045000342c0b80341c0252104c80c0250089680e4090180c035543d200889500545810440620041020590081d21030340c100c00c4003003da500003140c00d80868019440710f070300580e4840c05002000b240e540d02c1850150481549802c031a010740403004000c206206e40c908062246260300407070020340d078640d44440d5514010610042061100680031800780c0f2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 313917670 1250 313916420 313916429
    0x102071a06100c05070b1e0a09050909070b0324030a0c0f0b040806070c03090e07020c120114061011100e010b0a030b0606070c030b0405160602010902030c060d021e04 73
    0x48004440090450261074002140c0307600501170003c550410028410755000400581c401110444c180200202d825005001c45c0d102170750751045540c07d10080c0b080c0d0020182907580603611900e0100465205081561b42102c0b598800c9422114010030712182c4020040c0c83d1036040c06562207800402401c00184002c444100d11139018450780c039080617185006030320490310141c10500021310312600c107000302210240b290520209141d201d0b5419a40010b0886201d805a840300301c21076920310303044524843c0450500004d1044200640314804880000b91403130780120808800d98000e01d0041d000e0740c4c0201014402c030348000e5240c01441018050070500e8000c1c0d5482c2c01e2860315181040001c46090700c1d04600b080d6159213030750041c8140ca40c0910010340d41e036403800101000194541202501076401800103005900b00000b2074860035049078130035003d40e8902340207880140c50120300c2c680004c00480341c4580b2403000440700006031040c5d10366106610322049502640725003200240c8140e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 313918920 1250 313917670 313917679
    0xc081306120b0f0f04090506010b09090a0b01020a030807140a080a0c0c0b2208030405010b121f1a030115060315060804060932211b0102071a06 63
    0x808200d11441c0803035081044031504010304001400c0281484c40d801d5070a0900134000040e440f030643c4505041c45c80a8000403100d84000074400d44900e1310120094000d0380e10202000f42c841c80c600041c0d601c6070171150040c00c2c041c02000041189000c1c0701c2c006544a004540640d07188040b903401041d08078100e4008100516007241c0c5540c080c4a603002d0700909034804445a41c030348401c0c0c44000c4030010134224440c1030b00c010b0141030000d175142340910b00452043e4000302d40220020100a05442d2038844210154070100d108483e07180c021210f00b82c41d02440400103180d10642c000d11540b2280c2000c0e0316059800e2182c03880b5124036402940c0304865041d034003040f003c8105c080a02090b4220720442c000250100c0110b000315941d80c0c40540b0b000d20030f440b100324000e0304025002282d11020300030004904011000d0105500a10a694071003000c00c1150300d645003011940a007a0052600c40c1c62030740c48440030062440320941c100c070103c076048012035007052012054a00070f818100d903264001d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 313920170 1250 313918920 313918937
    0x3051e061914120f030a110a020a06170906041707020a09060b090a0617010b09060904110c010f0207020d0f0c18060906080313170a0605090d030b10091202010c081306 73
    0x4a40d00400c100b0344d0b03802040050741c945040035404885182e5a070000d0349090140040440050b520b2503410402800652039000c0d0750700e4900b10308141c80078000c0000d04181c21440403c000036000d898500d0a5487c80303554581c0300c103030f0703070000c58079801d20354100c06219880c1403004110002140c0c0600803148044800c00003045e00c8490884241902003807042c103080f00400144001d584013000b6008041010702610700b131082480000d004d031003803143e10b10480d550010310139101003028083c001c4003035a031880941c501046640403642034404401e0184c42d020f40e46142c0801c01c0b5001141900a020f510f1001c02170190802020008104a201c0c00203010301c0c2c0000040c2215005c010343d010054410b11502d02c043c6031503124031040d515404d16420a0103070001c003400265503031184600610120001307000241984030060101c030010f043d20f910441031007134200d01c616800021241580c4802002c40300500310f41c80141e4403100c607148014810807010460000b4400c08080e0340040782c02c5582d66444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 313921420 1250 313920170 313920199
    0x905091305060709060f080606072f12061906081b0a050901140d03110318191212020319050316050301060212130801091202060703051e061914 63
    0x40d01184da01c550004100c406601c54881c5000344001340c0d12110103081d09251012a942e4030f00d40200390414800065403251000350300558408072905100400c1ea43c0541c43c1d905985015503610740144004072a2020fa90b5000e401c06454006500500388603049945840b601c0090b12419190304210502810807070000040781e190005015048480e56031040e014a503003402808600b00101e007007542400096511800030907810401002d100c801c126001d41c80c1501401008184040034a060b00070b51071245051002c00420482003403240d40c407807418030106656000c260700b940505050b80440e100ca489010703c210303800c2801544034900000300140d020110700c10a450f10700083c011040144d010500b00302003842007038002c01c2620091401040d40650b074080319403c2d40d021540c04c54050086e680440381c150f8040207071a4102c1c1240c01c0c2844580381101008a15015803d170444411505402268464884607018000c41001c042240360440d1200f5054401da07c40940143c040da041e0001d110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 313922670 1250 313921420 313921427
    0x115090218091003021c2907030903110f0733050a03060b0307030b03101e0209120f0109050708061302011209020a090c020c0d2a09061d0702031905030709050913050607 74
    0x70000c54090131f50000754441c1d110443c002c0c0303101c02085003401495412461000000c01001901820b1440100070b01c03420224100030301419106040d0fa40b10b0001d0406402107040f600f1074120100900d05162280301ca8a811000b400c8a640704084508000080c080d159505412129081005804813031a5a52038900300741140d08d5040c016405a10303100311550b64031340030b40042002000c01804001955010b25000342000d0100d02403000981d5140c01c0002000380038007442004000d01e40140403985085902c86030045c42d40391009040000c1d110b182550000c503540700030a1260094045600c60f91188440002407a0300e600c5a809407050121090bd9454026a040380c196130150007800080c0008954515202c0400c060b0201c2189d0603602050000c20384c03089800808502200d03070303500121510b440602c008003400200864000300074005141d170f401c4400460000a62501c0d542c0d0380d07188082100c4910301504400c0d400000c09082c04140010408203d031000d01400030380d44183c0340d030403094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 313923920 1250 313922670 313922723
    0x50a14030709090b0f04020c030307090e0705030f0403200a0309080c010e0402070201030e030d0207291503070914240d06050403020307020603090115090218091003021c 74
    0x1800958810b0050100140b141c0000d1004c05002e81807000c003c80040c005420703a08400401402d660020081118641d40003501000424071409103542505098a00400c2840b00411414134484e42030003042c00c2500c64010541a00315015050144408029406882d003511300ca0a0700001c0004001250034040444c02401e0500161900d0118200002c140b20103500888803d905065464440300c510303000500003401d05442031000143d80c1d03a0b40e4a42a60500c0c0750150500e2101c5055421569000407000620740014218480740044101030000038a400c015030080d610791411300722001c4c0305103d1009024000d40203480e486a03040500076907040f58013080c0340c0c3ca81d4003061700380901021590a510154001d806803040d44d181004035004110a42c1c800d640d070030703507a030f54a4140c1031541c0d1f00800002d02806c1400d070290328040280d90100100c51600020320b10919000002c16401c1c042c10401c80700455014004428a128101041c10014210300381912050204513010441908140c800d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 313925170 1250 313923920 313923931
    0x1112010e070e01030b03030904090b09010e010501050d0201050d1b020313150c08130b19020f06060a15051e0910050a1e05070c090506031002120f0702120406050a1403 73
    0x4038002d4540382001180a04120b1008507018002040fa0f40e00d540c44030301460b902d580c01086a8212406c1c01c8050a00710385030540c0985281c0d241400602107a41d5061a61444a0702460710a0b15910011003520041640710010310104100d09410380742240c0100c06003403862002e80e08a0398055440b050102035400c01d0721703a5800210f440449800180111001d4140d034400c1041d40120340d6102c06c0e032400980e12045144a03152407c1140d01240c5030704011140c1c070401a00082d080c14108480442d610800320701405540209902036000f03502e204400ba03481900c2030090600d4503025004411140c4da000e880f0890140c09140882c0081300d01070800c940306e2480702d90300e520404a805407003413400a0584001810080300f000f010010803085120350014005041000455081820805141c2180c0c06a50b030f00e410f00501000045141c2601516030011000001605c5a80c4082040f820318071012000c00c0c25250100f804034a855008001c0e00c0e808030b007a01c41c01c524580d0713401c2c3d51519000c105c80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 313926420 1250 313925170 313925177
    0x1e040c0306020304032102300103150905061f0e04030c030302130b0703030605010216030c050f040e0303010303020a17032502010b030a0b041502030103020a03080705030702041112010e07 82
    0x1000041d10550095030300074000e28214241e0307030080a60000540c100c2e0402e00e00141c0100d0b000c500880d8882c201940f444060340007a507000400d01141d402580e05100c00360040b031420a500743d406042e50003855407950b001040ea8201d103024951075010508414208003490a8180040b804009a11000e401550151912284115a6236086000e0351184002c4e141992012000081e489006030180140e607110340c0380459801e041030002860b10400c1c480307984244403600e00420101d0700700e001c18401c2e940b09980b4412280360800c0450040c04011241040f01c0c0300c004000800d042d40490845101c034414410030070b00e41c02e9501050315900007a2914a00c01680b0310200740c1c45200c072201088044942d00000c00d40d5400d00000034140101002e01341ca16060794000c000410210002c400d0001864031411400c40d411a008582d040303005001c010281c4a001a188050007230030401d0740c0589500600910000140b8054072500e82c01c40380201c072404141e9400410406014501e00f80306045666 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 313927670 1250 313926420 313926443
    0x904060608090642060f0307080a05070c0209041a04122d080411041b02120a0c0b100b070c0509090c030c06160602040824090307020f1f03051e04 64
    0x501804e448104108024441c801d00c8600c0c3c001612100701500c502c1c81d961401c03076101e140060016143c2d2100824800c02d251610301000341242e00b040500a8207601600c650211340d8851400c2c580464004e54480f500314441002c002c104902c0e051000401450750307440c203201d00a08000345102d44080404440785030f0980c656421202c0c442c0842e5a03101e070040742010142010302c0e02090460b00502d002c05c0c802540c4840c1c0c1c60741c1c103804010081189409981061504c003214000501c0d0301a4940010015444a40880c1e007a00c083c4000c80040c000d01100d29698014500d012010b603021403103554015020080000d09200c0041400070095001078084c161240420b4100a0140d206442281c0b0304030400400350042012071000d4009080200c0c001c182510304210401c1e01c0086c0c10303010400c08100340d010090902c0c4080240c411180c5c0c1600d015020804ca07000040881c600e0f44265125000406519072001c0e60581086000351602540f5002c0001c14a40402c08040101c0d005000b100303162 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 313928920 1250 313927670 313927741
    0x5072907060b1005030106090501080f01062708100f0e060a050c070c09140c1309050c070f0b04111512060303070b07080a060e13020d05010209040606080906 69
    0x10802890800e1181200040351401100002d03540b00c0541c024000203100400144280d0f0303007003507101c0c020f0300e0242000c800928041c0c81c22150701c0814020b440c200480c2140c3c1d0720503a0300c40392020307100c000d44020034090703a601e030703a500c0d0b079a284000a00900300f0b08041d10060700c2c101d50b03c1001c01070b0b00c501c0090002a62085000b0b009007034090203440c5603081c20454480030540c41e64103000079251312080440c40010070034080c01c00c00805000c0c4804014104040b0484d050708020403001c96001280104960380c80070001010383c01682000b52010074060060001c000385a850607114030711442044460500040c24801100d1001d8008094034504202a510240d100307400329501950041c02c0f42e10700061356071b50180181040da040c10108240ea4240541da07075150241101620305148002003c1c5455006220710014004002e8014949413080e802403050a404403002100c0c040c01c1403207015a0f95200401801c002c480b01d4445c0d000300000318400c038a003070006244243c0005d00d90100040c0a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 313930170 1250 313928920 313928999
    0x60e0607031404170a020909011107030f05040f06030e0d02030a050a05030a1b02070806070c020d12020703060213031104060b0406140405100f0206061207150e0310090507 75
    0x102d0320200c000d0100f0700c80007446070301c4002c80e2560305040c940603080b1400d95105110120070007a26181491341807429100c181c08a48054400035030700b510707100603888640070041e98980300d213412905240012260102d0055059000301b10301810a00031902c00d16202c03d001c0f6124021248a600003800400c80701804920070009150440a81c800010701c403c2c110803200e64201200007840c000d07820100b0204103e08050040540c480d80c0ca0134030100c40400360340000c400340740d0b12800400043d00301001c1a52280308001c400040c0d540807204660703d1407860f03072990941856100450f000d0b00c020040030503a040c01c1c01844200c6400140d218101820445c040c0c81040645038a1100110305000000d002d54441c250503013420801e0300c80c40701265402600070305041004014601079841180c91000c5040700045210803100f8848040881d95001001221404800d0b1842ca50500c104950b400c0b03c81e040741d0103022854850400c80c1d4040340c2d0340c814040300081c160a0f103d4142c1c503000181d00c2c2c2c05103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 313931420 1250 313930170 313930187
    0x1030308011a130305060609010f0e010608071808160603111207050d020315120307150e0309040e030c010c0207140f12031615020405061b0708150709060e060703 71
    0x800d4403081c14041408030703c0030305601e00d510680d502e03030007482400201c0c148807110342c0c054481d042171203e44078100003980c58a243c0603c501c50410041e82c00103107c1c0f61151038403a200e130300c1e5107403e400c2c140c0e582d0000d541d890300b030000540000500044002503480c06803046526000d510032a00c0e090400c0c628002900320b100825800600500304401a0180c003588015841800e05d0f43c0d542c0130400300302c81030100000280d42d501b2030540c02001100041200c5061240380703d03048074004148901070304615411030291420254019007000c88005078604c021016005100300903001b0014280300c104100ea4840d8a803268400b003079a03411405140c0e042414030441c0e541c00c042c04080820760140741030b5245502c200d1550601c0d174024480801040b061500c408181d801d030087c00e604003400d010000312180704154003000c0038178039084000b03110074051010300010520030707003a903010101c101070b8044601d10454240002501401003c0743d00d5004100d40060450094000b609001d0981d4050708c1e41903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 313932670 1250 313931420 313931459
    0x305060f030c040e032b1a061207110d092c07050702030a0c090203041205040f0b07020a03080307020604060b04111c1509060e090c09130f050102030411090f0103030801 74
    0x8100401c1507640a0006010320711b50350f074800e410707842026461503005c40303000c00340924072008000d854201a03690542500c0c106500e900d01d03d441a11248810b4a50b80e1210315001420300465006104460700000044225000248100f203068101043c0214540881e1000d0428440a030b000c9805148a5000380c030310184058100d8050210948440c510584140e0041c4446500041040b04010b04016131121114042c205541054100004221010558000c51f21100d070045010020b5550381c0d03880b10021900090140d0b96400e1052000307403110001c5500b9030f000350405c0305c0381e410b604051003041c2440d00300b08251030030000c000c40b10b010220045003149218948030341c1040c011400b80c1e44800c0c0200b01c405000502c480c5004c2005900410007030941607039400c226114003050700c6130f00f0303055401008040c00400d0261035280150f28074a0180028107150b10200411041004968404a600b0382c1101c168111b81d0301c4858400c0300300c400340001000214828010043c11008882400800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 313933920 1250 313932670 313932673
    0x3060f110729010e0115031109010c0606030f030503040c080c0310020306010e030607020d0f021c030e190b0406050903160206031b070c030320250b03090109030305060f030c040e 78
    0x1180c2c41020381c0c0c02040d003a0400e10030800008010020100d00c1a958101003400b41810310410052041c0e0071007902441c01c680b414000307540308040410501c1d03800030700555400441086440900d04004115410480e8200c90a00482c0c2c400b0a0707219000441d450260002401803082611407003070300e40690005001d50b414070000c0c0102c008655000d1202600c10425a8001c210b40707407001d540107200030b06001d080c01c203640108540c001411241d5044a03000d04c4c80341000300300c40c410040d45500e010009104050744410b100070840403c0b03003006071035000c1e43c0175410a001c2c40d12541e000e5600c078800c140308440754044495090300103041c90f60145038042c03091074a80d64007186110300c0c036425a01981c1c2c1211807402d410320500030950411110300c40d0f1505510703c01e01200e8810742140d0f441d9807044440c803211175800900c90204640d00d401e140078286418240343c42c2e00340342d4980c502810200d007046000c81d0820b400a0800d041c0456040d50380380c00100182071458081c0b0074000207003030315003886026 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 313935170 1250 313933920 313933973
    0x8030106031824231b120c0309070605030114090a2d0509010506062d0712091a1b01090b07181d070503060109030212010603060f1107 59
    0x109020030b0701c030840d000f41c40b010550306a000360300340c0c1d0031030f09034980b4802984000b03075a5a120b80091100e007644400d502d4a240f030150022104140349018294040040124203410400c0c50160140514006c030b020300c1c221a01070361602d1096409006c00d003d540706404010440c0b02d02840c00a00203030300004985400a0011840000c80ca00105101024000c0d0004842480701c017844902c42d480c0d00010f40c4000f0429420b002e40040e915103c0c8410980d280840140180401c1e03a03450103011881003d07160842ea030b0062460312100b0740c4801d42940000c5103400c200050300c8000380d600c01030303200e4800710400d2424101c2400200015100190083c8544d43c600c0301c1400075684000e098003c03009511000c14030311070040f4000d202c0c02140c01c0484010449028a003200084104d0385803c246a4101941c4945e02e020048420390080e80c800781d800004c200540401c0782042d805501500d00902c2c06010f100908400741056a26072a2a000c003081c0c00c0180d100890781d07115008071124006241c0f40300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 313936420 1250 313935170 313935173
    0x3070e060318030c0d08090303040c06050f0c0a1a0f0f01060c05030c102406020309010528050a110604050c0409020a0e010b030a05070f090510050c060c25080301060318 74
    0x5190013580402c01c06612204440510a81061070240d000d08540003d62440c44d142c0d403070004c581c0251049405010000c41d01403150090007040c4da024a4601e0100ca680c403280d0309002c44000c4c111b03426a1691441c2c2d001150309052070f458120303c500203541d0580d49a928144003260300000040042c0c6680c0014090241c4840040c042d620480b00504070102d441040c5800e2101c11220046400c01a410040c40c1005400c1d00441580e4411500b400c00d0340c0c0ba022001508107010a440301140700d0090010701042441e03400002411005525036540021b2803a281142075881c18180d42c064210b502c044c040781810b2030320350000a01c45102802c024111580d4006102014000ba0415690044d001c4204410750415100c0c887d4070481070700c2c1c04101d040d0841c10241106800d801001e0145418188075000f080c011001c681145110508455640ca82100c550b051034105215181d41c4011410b05403014041241800b03272015041a10503140d64030340340e0180c0080500c03180c42e600c1c0e0041540442c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 313937670 1250 313936420 313936423
    0xe0a03060e06010302100507030c060b04090506070c03120b0303070605072304060201050c03010302090f0603030f1c060e0126010b060d140a0e0a0308040218040c0f0b03070e060318 79
    0x1c0c01d49010340140b440e54154410000c1c0e0141140032101000010712082d00880d6000700c0059155412600001b030031002000401e001d4824110b001e0041d04c6000e041c41012039001c5815034001e4081da49900a107521261098156502101f10302d905500c00c5c451900401c80d1a1300c040c0d040201414001408280701170000388201942c18480344618002c5800c000d00d17502030081c954401c4460307911311718560441c1e00040c02c480010f40302d402c41c0280c43e0300003006500c08204883d40d8069103a407841d2102c0c00b00d85651400c500051003180300702d0401c9000115480b5a03000c860580780c150801011508070310030800a01042000c440000350b486401600c80c07500c400d0300409050074080e402040c00c459851180c1d883c800080c0035624150b00c0c0030301c000743c000d17400b10b00010341c26032620f840901604c031400051402c0910000907600b01801000707101c100001969030030101d521081d1980034245c6d030b5460442d01800b003220401c002c501012607021541c500403004540c0300401190005410021403d0f8a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 313938920 1250 313937670 313937681
    0x606050717120702030c160b0406050d0e1002180603040f0f06091203050106031508030405060a090308030a09020111030c060609060612010b0406021902031519090305030a0b0103050411010e0a0306 86
    0x10140c1c05c00501c0130b14019060080c41c00d040709480c040f103185031500e00000702a01c81c91250804015004c58843c3c0d01200b19008111080c05c3c140807140c1c7c4124482910000703601001d04170402c4042d00010b9040e03805d2403801d503485a81c0000d21031007030703032965124003c0309001c900c0119034030791350b0b241d110000840d2210108480790302d6643c001420740c10300002908071080d41c0e06034410344030340c4401088405030000803201580c4065922585070115044151110f4800b13401c014580c040c0032003000a81c0d1081d070300c040b8109000740c0e500343c04000749401c299228480e249028465400010008034142481e0483d9604548090001442c10b4090081900e0100f020703084030100d030a0002d410040b0b10750400c13040c448070110240c40e540700101980041c0e5a2006400502c01c0403031a08000342500021182c541c0341340304030810a01c03080e07401e0b01d4001c20590044401c01040c0c1d01e8040c03580d00a52280c403900d8840c42d40042e5980a5400c050019903407109241083c9900404030000800000d00c28004c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 313940170 1250 313938920 313938931
    0x150c03050a0f2a12090501090506220611091201060e062706060f0406020a0203070f030b15030c040906050105030d0c03050301060302090310091109060301060605071712 74
    0x6403800e000e052031080e40c07544505020190b003807401850000541a4a034030140081c0d4508083d6410745400903030704042c40b007044583d580d00d058445020f20006400820b0814815000c2e151075950b01d9112510703125440c100c000c80b9040c1604031a000030300c3c40d40081a062a5441d00a041100d1400040c0c501d103d0100844100d94444c0800c216a01c00c286100d508080c046526040b805c14122501d0104140b1882d007891910f2142c0204441e615000d0455000702544881c55540b60b44407100603580d01042103040b402071161000004098a40031041d20540f030f4400908840350711001c5080340622144000c031a45400798011350001da65a03445044440e505c6000041b40a614020801d820403240c804600140103102100100095200b030450341500c0550400580383c1c0d14406c00300e85440b84200b031108a603490a0040c5081c018400000074044108951010456590006041c243d0700d5520646000c03540c14080746000500aa10f010540e00c000a805400c000c403040701110320a130705079030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 313941420 1250 313940170 313940177
    0x6030f020f031311010f0210093e0105161202280507170d08070905060d1a04060e1504181406070503010e040f030507150510060804050a0b04150c 64
    0x41c21042040080004085220908140d240d107200003201a45072115232202e0302810383d403452082e08000221422405c8400040100b41348452103c03501400c0d0300d08000142c6047c1c2c0303003022041c00c941c0f041040700c80d11091904c140a201e4a95a103100c0d1940b48107c0380825400740001d40d01c20760312000b0340f10352400c500b0201c464600201e030803c0c40c2440d005400035030343e40c0241030340c074025103100080103190b080c900c0c40c003e45556100041142e2840b130a4010030360201c000100260400c419400c003803841c84440c48041c2d014200070080004403206441038080036a9a200021254540720f501e10078000000350022400a11200c3c0c2005203c140443c00c48459980c1e800e80205400100441a44031140e41400c500c0d55040003856680c00c0001840185601040c0546508240c400c500359410a9403004590800000d0004007030090b081c212030b030031080d400c1c800002540728444d100300d600035504030000d0403900d1083d4403040380ca25001001030780d10040030640d00c410414980f00300c250000e526074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 313942670 1250 313941420 313941451
    0x1a070203130503070506070209091203040503030403110c010f030f020408030c0604060b19030f080f0c0c03060703060317090a0e070f031d03031f0503010e070801060e090706030f020f03 81
    0xc1d4000e885040340e0480c074042d42c00460f05104a4444108a811302c54044600303641ea5641e9010640c0390402400d840e1310a104044241710030044008007560051b0310a40705e0240e0030301d20170485070f40d4000b8003c0071b03800a62003820080d82c1c1c60107907000d00101003c8090140c6842e840c0d1840c1444e55000c1e51039813509901500800050108078400d80404103021100305000e810002030114040c1150b000c0503200780b01c0b0a042d101000b0303031032046804840241100179180d5408915250701d42c9032072540d142c02401041c3c000742100d4403900c2038038241c0754020184201c00219984141d1140c0003031003c5504005c0f0311001151451b400c03044a4810142030307450512108030000014261051200b0303481d00000c2003504c04549200100540307911084052101c0038450008d5107180746020a036200d03070f1300b651130702d090308040e1040420f848094600d124000c1c0320541c0e45151341e941c040800c40d2464003503003100400307201151294000000d00c0041c10405810700c80344481001c060f40c8140c400d42032000c2001e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 313943920 1250 313942670 313942687
    0xc091d01090605040209030d03020a12050c070c09021309110c0708250f03060209041e0c030b030d090501051c18060c2a02120a030c02120703050307020d1a070203 71
    0xb4050000641400c3e038065041201c0900480e5917001d0003000b140074560007050300c0114511034a644500403247c510140b1840c01d080004102c99800343e1829200180b085c5004a01d444081c02103e00c2c04144e108008900380c50710b20440000c0c43d240e014244000010044d02e80c085400304205070190002502a19032003450054002080d0181400c00703d20030030304401000491806020302040700c0d00040050b07681c8020000090040000000d03400703810701440c286076558410740e4042c000540c09034504110140f102c1081542d504000c0c0100d031f00044840d4400c2c4040c1d44200040c0c503840d00b03103400b61003403480c04046200a49003d0303580c8140e961001c403101010b11401e8010300004030780900348102c40403009039800e07490015107000008010000201c902c1192104480542c0429205098881450041c030300141051702c0548140d1140d900040100b44040c0041f03102000c50f0b0b0702400440c0f4254059003070010415440c05c05071043c2030036500324071000344a807408030310448070307a0b000d9540c98441d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 313945170 1250 313943920 313943939
    0x151a0903030d330b0d2a180b030a09051e0a0b060d03021e030d020f04090501080d080f062701230a1202040603020d03170105040e100c091d01 62
    0x107006030b00940c488103100c201d0880f228544100151401460001c1e5034000500c03000000d4040c82d150010b079090b685600d010407019148031000620b00d41e0740c610f0f08181c5484182030085202c0d000c0c5c0b207a05801040400c0762441681d02c04084a4820015a03442900e00000c184010203500c68200132500010141c49c200194207081c6984504110313041c407804461518000c1d5130f0340c030007141003503c00d14074a44031100d01806c005035180c2600e43d03002075541da0350081c082507107034121b0300c02e0070910750426001082211000ca8404c0328080d01d0380d50000f040d07580c1d0042c3c1c200040040d00c00f42e0007008220110300d000e0401440401c0800ca03003540c0065075454100c487c0c4200814030080e0050495502c0898066515408460121244d581003084948168000100240015031009500080c0f002c1c0f150b04058200307a0003c1c030710b142011580e12031f03a42c40c0188026160310585501c12a0860107074440b104081e40e21900c03443c962450001145a200c542c4d072412030780784000c00c400460f800401008000300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 313946420 1250 313945170 313945211
    0x50a061b210b0d1b060e150306010305150607050f1b0d080a0c060c050703120e0a080d060e182a060c07080d02032212020127030f060b0103151a0903030d 67
    0x90340d07c2041242130940d0300d0756038000034260794101502d076000300c0c0c1d05c2c83c1100079146010740e0040c03041d0307920b400520b000346d52140f9602264000e0301541090141544400700c40e0380c00910080c0121010084030358441c00d55510091500003441084a111350105d22644191140710045451302e664a0f82241005062941c6001512600500703010101e1111a80410030104559000c1d05035902c40c4103000150f4090186600040340060303d040820070a01c0001e02c0704003102c03d104043c1d1704401d0701904840e45008500080d844c604a5004458070b560070004020b00e603400d0701070305a401c00340d00c4405a500b81101020071500503800894144002e142e01c91549101c3e0b02483c504660092514600c03030030510000b000641407103802201c04804c448900c02d04407080c4071886100405a0722807402000b1409907500a8031729a2030030786441c4265020b440b511000c50400298001803900d41540c440982c0040b404200500d070060000d410161410800760910009403080801d0015908040b03200c84032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 313947670 1250 313946420 313946447
    0x120f0902090f0907090911100305060907020a0506070c0807020a0b040f050307080d080702070f032306070e0f010c0804030c0e0603190b060d050a061b210b0d1b06 71
    0x61580381880f00501000034003000301c43c8069404640d42c41d00781440304204061081007500305000340f8081c03041e01e030301d035001c24440c0d2401c0740d05246640701e0703440490703582c031454100030502c0d4060b00104845500a0910007400c071310a402551500c5410ba000c191f04640580c44400c0910001c201401b10868000f0081d01806c002e9004040035442c001c0110360750b02c42050b00c04d041c800f160012450581c406c2c0190700190030310000c007940056482c0b914000018040702c91a51900b50702407444201d100110301c03140510001e9840e40c0300680030030308100600c0281d00102c0d050240300d40c051000903d9200c041c10065000d03000c004078003072419a104041c8103005000702d20a8200c021890709014850036514000c0c0d4029080700d44e140d07920000310b203500c0810390f0007505a128890714901040701da5088003032202d80c0d0080c00540e90600640a80d0802d42c81104403a0003100c01040907464221903111900315000200442c210b02aa40c8070412101c0846014021810008400b03100b000d0f04a1482203c03074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 313948920 1250 313947670 313947691
    0x10506040614030715110a050307031403010e0f10170307020a090e0618011d0d110d410406030b060f03040b100503010f1d07080319120f090209 63
    0x9000c0c1400190f11500d00d8082c00b00f42180e81e1000d444414461200c005c066202c4100f1101c44e5a56030600310352740d410220040380000e00c9011519242e01200068a040b02c0a4000c0450b464443c12660608400c00420120200c410101c000607954550030104c112402c03448055555544540144006540e0b56008542038a04000c3d2041d007125001410540c4a82002c800048407160780a41c0d6001d40114508400366903014880b0900310580400c0210803c202c80d2645000041e0a581c4d03540c41c1c0c414181014042007041042c1d98640503403080080c036403010230203c0b400b1a5101080320f1100240b070f02000c0c08800c4085428003c04d40c140c40340007080d480454040b4180f54401c44c0d008164400100000c1c045850740c4041000468580d0b50030001e818000c00030f0260340c1c41c010b180d50040c00d00365440c5490348e8400142030819500494031809898a103809140380810003000d801c0303149d240c40a054200417091ba0440240740d40e600c950200c040c41d2083c01b1401040d14010801454806854030040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 313950170 1250 313948920 313948949
    0x1509060f0510090905010b09180403020618070f030819110a230714030c0a15110a080406020109060c03020c0a02010f03020d06090609050c030702061f080307050105060406 75
    0x4440035a00104200c810840b05282d8556516004503038440007540f0450800d41420000701300c86540c00050109054192850410402d1040108403001408d84024003d42c00c4500440e2500d003500c0551020046140212000103a07160840c40d403c0301194001d076080900441c0100f81281d2108096040742c1051600350f403d824004041900c03001e1100d0300411080c2d0600d0790030145184000b0b1450404c2100081c0e0b500385553782a050321090590000030b1090040214445161802402142c26290b40300c8c508064044003e2003500d5141006000d00400e2013042401d100081c1284002c001a10b220360000c03528040b82e02d00304046c1c4182d01c4034803040c9401401001140400042c500d0364240e024038201107103030b8003020103900034424030480c0030300c5a042c010302080070002c5411400c11140c000c0b200f000a6518807141c0c0070540400c2d80e400b8016080070300807525224042ca402100641d1901e0134000e42030740c4107015441e40c0e0190b0300840d140c4c0d444104101451030030380300743d0000308800000b8504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 313951420 1250 313950170 313950179
    0x121e040f0b090a08100e0106090213090e0a05070320010e010509240a0c110f0139050c030d02242d010e010902040f0506030a1b03150906 60
    0x40c0303100c40c007608900c510085044206642c0340760180008203005400d48415520301000d12002d0075101c82120401d42c202500043c2d100303203520890b510081c50f400c500728110b0a11031084041c1005010402240c0b0403500030300d01283c800d00003580210301c5686010039103080c61b848101c0c2040c2c1c80e0101ca06009001d00c51002030f0741c00804844180c20222074890a100b0642040a0700007120034140a108401007013194140e60030452145a2902545801106000c01410090700c5024150780600081c0800d01480001590140044001030b000183c0f031078a03182844004407200311380c081030341d480d800581d00704078034141482104000c2c0200d00c003500302d6604007a50034261200260000201416640004130080a0009000221180942d072568031994501c007640b007086003030007442c0000403030b80300004003125240b00b00d500b103c1510003482c01b0986080d04106154100902c081200c40d01e40800c480a000144210014030501d52400103091044404c0d258023981d183d00403030b0b10b1740c6ca020024070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 313952670 1250 313951420 313951439
    0x501050910050a0504020607080307020a120f1205060f130b03010c0e100f021e01061203111e0a06091a010b0a0e06070b0105150d060801020d1127040e121e04 69
    0x1550140c000e0280e555039110003500700c0c0791004c00c2002403c007002e2880a005280c1d031001403044fc1c250346680700d07070542455010a004950060f101181c5c4031170f82d103240715a14101042c1c042c052000f0114000350720b49108000c0783c25500010600303800115144018811072038034085890a000251600320800740740300d076001e56102461851202a82c441140084180b47e007500038030080d04003c00000c402c00c429240203440058889403c103c00c1c01354411140e40303010710300020034120080000500f03031908142c03910f1000300222041560031240d250100e0304074078964107803607000709400304007150366110121004021a100c800300c1c5105003c00c101d030202148407030340500d054410850311101d03d10341c042d510441c548108412410114200080010300c0481036020b01020114603001344220070804200311450b124a0b1100301005003800c80080e40018000345407000b9032000b42c000a0000c15500420b0b12300380e10a0700d40c0d0030f1040300041c80100b55014107010304000500b2005d5a00302400d00182c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 313953920 1250 313952670 313952677
    0xd08042108060414041a0a11040b120f100b0a050c060709080d020a030e0906060910020a02091026030d090506011401080c0f0904090605040308040c0e1009180501050910050a05040206 80
    0x606c030f8803107039010502a013544e82c071680c1d610341014101c03a92130344e855010410340d40102c0134502d0601e01c5e24001840610101e00c030b0038811240040342207801c030306001850a0a422000103503041040c188945040580100180c1e8020b00c000d0702d60134903031031a00f0115890400c2120405d021504a01c200e074000039007112142c9540041281d85411a03614000880c3c1075025850741968052440c0034203550440c5c0200b04c404280d4000d03507207800180d43d940070ba00307204462845007101d102c1541940300c20b041007442606202d0344200c02a01c1c604103082d101c04043e41d500f40c00581c0d46401450040001044000001401880a0034001c140e40b510000e44d0f00f0038000c201d03101c540c08000141082d400d5a681d840600440e40c0040c0c10411803c0074180105020400c4604542c0c5118901c004140920b882d2025071180c3c00310b03080554503d08242010014043c2d5001d046d00f603040910401000076400c0c0031300d51041c0306120060580c1080c0c010f00c50180e9802800b4681c00038a00810b02000d45c585600b00e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 313955170 1250 313953920 313953953
    0xd030b040209041103040b01120b040605060f032d21070807020a031202010c0305060f240f03070807050a0e040c050c070801061e05030d0804210806041404 68
    0x2518a60280800c01a208030300765960701620b007807586a42110a00c01550069014034014156030780c076043e4a008603281040042d10b500441b03000640015602d400c0113900460190090313404041c6240800d1400e061032000b41c00316095400b04590003110782400d01c1e1002c00f0100108151800c01e00d07c0102001414401f00e200c800c009480d20901003c07908481c030b12613014000002999490421001c03421030781d80480015400c1184d20601103100340901c502524009040e022000f0340c20081260070049522003041d406800020b420440205101514403001c954035980d43d2490450030003000080d0040403501844000c3c0807140d045a0b010001a040002c2518001007401c20210265030360b001e51061171409100d035190114075010190031110440d040003401b401030904940b0115009079441c061340350107900025014170511f00c41c40703126070000d0141015407082080a010140e20f40240c1243c400468012800d100b650308091040c16039890070740300c0107080d40c2441d5588401c0704940008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 313956420 1250 313955170 313955177
    0xe09010306020705030f0d021312200a0308030f04020405010806040510020f04080318041a032a090f0610030207030f03050a0e0102040807030c0b0307020d03020a0314130b0a0b030d 79
    0x903002c3c100030b400c00c2201c1810700051001512000d130000e480019500407088180501d941e03070070000c1d42d040e504600e440100e5001e6462040c0c0601941c0c2d840501c0392034190306030b0000300314500001113154400154041d0b020543c85425500c0c1c01d005000c16a50180d008030b01d103a100500b040041440840c07054618450500b0240e5609081c55242060380607941201510340000504072100c804100707115043d5250640e414080301040030000b40c102000c0c47c011580507002452202c0b6050a0b40c1c144100d0300d41803d41d1902e10403110030201f504548100da0188640c1d4001041c4103003464000b040440248943c40d0a61612505541c0100010400220502410784440104603004520303000032500300100c100031501c03540d9407441c0b50745e034400a2006490340725079104041983e48035841264800c0c549600100155440410220001d6003d021000c040660f1040e8902c652250a242c0c14010030100b070084200e14002d05105843c0d00004c0e04040d90140340c05010340058402040d1404610740508 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 313957670 1250 313956420 313956427
    0x3060b1b0c01020a03080c03040f02130905060105150a080c07081b0c03160905271b10020705010c0618060c030c0306081b1206090d120605030c060f0c0f1c0e0901030602 74
    0xa8140c000d0842b24400030b6101d64180e43c0c0514124103940710000711405407049680c1640d03103800b03100d90344250b00714070014070b0300801c03820098500910340310784c1000100142e185020751584038074119401403030300e4150303054080701d10b0505010208104480d0a0302180075002c00c3d0f0b44000048038488580c484d1030803c03511180000d4216094440c200d140c9844e00032282001410344981c15241e003071160420800d01d0804024683c0c034248030000c60742d104600d40003402c030030303042038010340b1404042941201c403180c4912502c03106010403000040810700c40c2c07901080c031a04101018041d602440c3c2d00340d04140c9803c07404c211610b130000c1c030701c4074048003000c8155141031000041500d20800c0304180e00c091242030180000550002000a00a030742e654401c2451b0200b110700909032840da20800b46d0503409541c2081c10740c038042d00148407140106480c40c2c40d2082610f61035091203250441204c05421002a4404e04a0340001c4251040d84c286440c8182c0100480000c1e090341d81800080d00466010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 313958920 1250 313957670 313957673
    0x6050109090b0d0501050c041a04050303030109110403050318011d0a140102010f05040c0501080702030408370f0b01120b0103200a0b0309010f06060f030c03060b1b0c01020a03080c0304 81
    0x50f035250f02503542141c004e02841c5000310101920340e01901c03902e555010701061028034181c1000c00e85003a95002800b42d032560b440d04a149014104c10542111070303400400c0008000b1b82c6c100001c0202c01d042c1c03015200144010000544900b00f1305001d00d80703000409040308555a650712901007540e140ca4200d5950540400040380104440210041c00c41c2c07400f0184428802040d07020800c0720001da851000d25640c4503000ca8a03805039124181d060382c030528000c424100091702c9104a802080c00c0350700242c09041c050106041a80300c140e40c4041842c101c2410b0007001220030340501940c50700d81d01d500d8051b6480c2400480144005400740c5e034501d40080d0f1071140e40c906503041355401032044036219242c00040c00702d54025070306001c0035880d00362045140c00300c034080d580031521103803201802d10400340015001b0303100780261038040507900c440100e1140300301c00240a1040307441d0810b1580b202d00c7c0c0206031a040c0144d242c51306643c051081800020391150101c0e80c04031503284059280e480340d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 313960170 1250 313958920 313958929
    0x90f0302180912210714030114031614210712060f06060503070e09040b0f06010c0803090708011d032209110a031a01050f18150703090906050109090b 66
    0x701802000c3c3c071030380060308402120f91000c4086103018861401c0314942c9035840c041e1200040340d01c00400b003540500c0100303d0500040316002c410180a010383c3c541804005001f00341102c0c5030024914513880300218080c0303080c113001c000c0d5944842c0d00700c1824658000c1c03400b507131503980e4800c611750407108045041c10040c0700d4004c09495002c855050004503280d000241c11904200c518400085001302540b45030310b85020101d0086410001000c01341d115441d100f842ca0500400b294140201c0607400c000082d90a070065108581c41c501411800e81400300c41825150b030001000c50007641145410312210700407040740c0c80040c184150000e64030b10803864910700d1205a1005040a140000041c03000700316500400c6880420381d401c11001c2c900310019558441841403683c0098024001c2d40b85510301080100f1001d45025001c05219981d0b00004106a400b030b45215408100400c80c0000c01d504007a640c8007901218030144022424100000e202040da44160701140c0c0e11410141c2d0651075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 313961420 1250 313960170 313960183
    0x141b010209100305010e1510030506030a12020f160f15020a0507030803010311060a0905010302090349120906181416030819140a0f090f03021809 64
    0x4010b0401458201607160140041000340b01e060f40c1d580321000000d00c0b0500c02e102100007206c0007404882c0c1c81c00804811002050001c040307a415110706100340c07011900540e4454840d1000340d0007401c0007000f80410b00d080240004113000c072030300026400e11001004007824025a02c40300310340c48400c0901a801c925002840e41c02030114000e1503404810700c448840114183da00411040761882e4182090103441d03c1000c1d101800101503c0b820701803584070303030010003000030700030101c5546020403031007070742e0303414070007164511001090010b0b0101403a101022484007906d42030044c0f0310444144050603954420000c0c001250383c800200701041803030b0b1702482e010440700701c01e106102c000e880c0c0340d0001040c3e508a514248191150746242001205400c0191303a800740b03400e8200840b007220340004504010f608414484421001d07074001c074254018101c017111035560900b00310500540034252a07180d4200c404c1081e8040302c28005a00c410702c054240391180003841c003a568998115a04054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 313962670 1250 313961420 313961437
    0x405060d1b0603050c07020d26040914070504060813060207080f030702070b090a0501051b0105130605060a0e130515071d0907171008030f04090c141b0102 68
    0x603459480c1c20024500003060790182c90141e2010400ca0301c49030144140c83c003030000000c1d4440c8201d034105c40045c030303850000d8198540f100c1c02588050191003004070303643c10680041801954400103154142e07010b001468001030a0b0811520f42420000000c100000c02044540901c1c8008203100c200701c4551304581d4034681007004103403942107621014081c0d5205691503170052066080c00701d54200e02204590400200802690b205440d103001528150000c0d045401080490038510f03041c080e00f03000e07881c481d00700d1541840d2020030750b1070004201d0340040c00090049510180510407124030380314058100e4400701099514442070f14001d494020b80e520702d000761032502400e102e44517811102410048480f55200720f40c20156a05202208004031100340010b541031080601c2d8041140400d03401c51603480107094520b03242c420003031071544070b48520844407400090800800c506449104100121440c0101c03444003518103401d5680105100a81c00c030b00110540d24550780c0c2581200c50302e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 313963920 1250 313962670 313962683
    0x80a0210050123030f0c100504121b121203091b0b0408070602010e07030807050f0304031b0501030e0c0f0109030c0801050a110403080d0c0306120b060a05100804020405060d 76
    0x668590f030042808922091551105140040c40c0e907860b45008901301901101820040003900b80c07000401c520810111107034010700c0010800802c968004a00921141d4007664000000400320140c5e60f800f0b03000303030340030402441100d01d07040001000089042201c407520b203008901c0c482203082c8541c02d440c0095901c3d8849103151400515460aa070150007102e403070100b640d03101c0b542c40009a0903990a01400811904006130074000900340002a015203030141c0c08a9071520b07102d84560345150701541064600720080c011b6012003905038107070500540700a00c3c06202d0741c00c403a080c0c581d03182c004c60445032080b2803d070b420b481542d101d031400c81e0003103421030411a0110354950346603000309030640d6992000d43c202020b146000c0308210441c0c040ba41c4c00300d2030902d400d00c3c5e003000711300034890040340030201500c0e40c40c0020641460403007007a08902821101c00c15003051b07001c01844450b44d6002074000d4500514403101690041c0440d94843e40644000c2903039036400f40014002c0ca55a403000303000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 313965170 1250 313963920 313963931
    0x6012a2003150405010509030901022d0d050c0c0a060f030902030c0303070b060406140108010b13090c020d020d0206150d050712080a020f150c0c07051c030216050d080a0210 76
    0x2c1c5810150650050707000303000030007a58498808444e00c074441c1e82c0740140980d0120065820180b2640408903240d28100e444055200003224002c1c100444042c50500103180821510800e00c000e201820511100319900300b0082d24011020f080210449920002d01d1380d41c41041040d514280100c61003610001c1c25241c4d103040900d00458940c5041c1c1c0d01d54021880e00d900803034104c2d403101d402080a107050f1501103060f0f1130310380022403d60000c002e07140b1402040c50009a10358a40c000c22074170031490f4003c4c280f030600c0c0000003441e00c20049240011540010309104030306040d0341081d00d60a1007603808042007a65402d10a181c026154004c0390380750815410082480f01182c06010f1040040d030076214100014460b035a42c4400500c4a401180b401c0000300e2030b210b035000000c114604580b01600c4140e80d8980020720154140aa03280901600c14070341d10030180e0500404414a02c90f8070702c0b904807801e00010508209400c1d07001051041d00042e24118180208072002183c0e003004018801c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 313966420 1250 313965170 313965193
    0xe040c020c030316060501140d0f050115151107240504032307151205040201031409030a090e09030412080f03090714040c0f0e011b0b06012a2003 64
    0x100130b0f5201000c1c3d900615003400031900c461101150098143d008201c004c902d041c03a12921014259a10103c815658a02e2401600080100b202c00142404480f0314260402080054401d41500580d0f5080d40c20207481480350301c14440d041c00680001c3c816030301c030380b00c0105015140d41c4034540002e06803010a40d182d54801c1c10310454a00d800c0d0076442621941a60f910742540b0304031107805140c01060000030304191102959100c190321030700501d40400c401800700c15500c0d00c1002a190b8804079000003e0b080041900300512100030107411512070a0740c078110700c0081c0c4a000f140038028440b2041c04845042c00b41c40300030340e5000300c25856100ea59041c242030441d51410710744644601a150b002c5110002e01d03052040c02107400058407949c00c402c2820000322400c0c0900c003030f801c0c1444401d0301070582001e0004041070020b446401e075075046041c40400981480c038041c206041407120180c028241d0542c03c0d6020700348552200c42c03502c120b83d80034a400c40803400f4494154152044250401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 313967670 1250 313966420 313966447
    0x12010b07030318050a1106120f040309060c030203120408130f05040c170a050709150509030f0a030f210e0105040c140604141201020a1d100e040c020c0303 68
    0x10944240c8082080707210068841c40c50748040f00780a802d64100c6100307040400e0010f0b00d00c40344424002c2c50719203042d40400034508111010f80b000c20746251880208400c158208a01101524403030801041a9441ea03070025601d02c1030908005261400c1e802050070880c5040c02c0e280d01031888011010001c0d101c80c0940508015446003511031350402c1e0703400442c503002c0c01d03442c0f075083c01c0a1190700050391889200c03009064050b1004003004002840000c040b0042d0f10540c0100c030070741d0ba569944a01301c104251400110401140c481c2c0c02c014003890020760421503031428003900d030400c10440301180390f0280034084095001d503402c604055414541c4001035110764400c0348500c1c0c00301c2101e911980302e01008070420030115002501040b0a0191840d0010403601a010080502d00003100141c0d840c1e00707903000745a40303102180844400c440100c280c800c1b07050400805032030441794800709420090a0084000e2420f00541d622030802004520074018202c0e0b840d0040c08072561078034111541ea = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 313968920 1250 313967670 313967677
    0x1e030a1a07030f0506090402060a0215071701050a050f13150f060201140603120c0102090a0801021c09020109090908090d0b070e030a120315030605101a03091f0212010b 74
    0x70f14003c201203a01440c0d2007200d02500d0060161626aa11030b800e0004079804841010194402d10070301080026544485038410045a40c5d60b90b5100c9015210007801401a0405445206003000c2403090b612552805003505108407003400c2206070201c10540108001c220b50a05421074240200f045c8501c64460170456846900800180b90b0451044100d90750940d40130740d1540041e01c03030301d00c03c800090242c4010341c10a03000500e40b0b08006c1c0020000c041c664007a03051030750040f400745000d420b0500d65002030f980c50030044c014100b155000070100381150041005043d030380c50040e018400408291030070380d5000340200400c1819410040c3d804d07401181c1200c00548402800d0410b0305000c900b0106041e40040d0744120038206d510182e02420440003003080900c160341000001c52000c0c0201030040c202e034892648114240107500c0400d140310b112191507146d00700284442d48800013a80c0b42101c002d5288070340d0750107040c5c00d45406032103114003010701a14140004140c40ba10b0a009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 313970170 1250 313968920 313968931
    0x8060a022a1c030e060a0c030b0a17070f060c02042013092018030c0312030108120403330e150a1b030509070504020c0114060f1e030a1a 60
    0x18010142e8160700d045041d01d50b07203049040150414008202c00a00c40d41040740144000e040200780300c0400c001060321140d42e640130080b40011a6500c1c3c45c00c000c10b020700d03400b60541c8040c0f10680c1e81850006000b01c2e2500710028021a0f8078851382c940e416141500c041ca01f20215092583d40d005031030b49209101d06406410f2505181c10480504034030846114404035011070ba5030b0f4107124105010351200070b50040746581501400200101e640e8050000e1081d03200445007260302d95040a940701c0c50002c2454a04000e00400c00c000d001095560020340225034003049149841e00b00d40018002c0c161811100c08007160900b000c2001c602400f00301c400c0392a0404002101c0c1d5078900103154140c402003041107142e120445040c19000303100b0380019901080b064210f400841c0c0c3d400100d07040745d210064000d01030355a035403288ca243d030113110b100c0d821060843d8444200280100010142d0031040c0750305641d40c043c1d0401d00340713940f410301c0f44145c029040082600b80c070760903841002e1640001c441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 313971420 1250 313970170 313970203
    0x14030c071b14100207080a02010e181e06060a090b0904090c090e190803040318030b10050f040b010806040207060b0d060c0210020a020d0c1b060203090a080102030108060a022a 77
    0x2110644038400603a407006c4964610003001001110740043d18401a1550585c1c0c11800c4880c0907030360340703840d281e07018095001d116015003061100c1081900050004d0a901d02c0b41e00e007000141c03034a1764001001e0041c0c900d07060700b107981c1e684e1600000300140440303840249218001040011154402e9001c0b280300ca0306841a109440c3c0d51a80310905400c100c000245446002c1c004100840d00c220a800320421841240b05c00071600c070b0300daa40100b1011a0384000c0208104414001c0c0d0414029511b0500d0040e2070600403005140300180041300c0041c07160740181c0e404200d05003440015040101c82c40d4000e40003a00745011414014050308001c604480036204030034803110140074a100310341d95811180c0c05003045c201c40c244d04071400c0a01100a03100654900d450240c852000e2860000400003034000f56031fa0304102060014160207079218440991060004003c07508012510a42c42030814074010780d59200303d01e0b0070715540481c0b404640030303c00d14500040310090005001100c2c40b000b40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 313972670 1250 313971420 313971439
    0x4090302030c010b06120a020a020f0f060a0605060307080c03090c0604030b091207050d08041118040c0609030515091e060a0605090c1912090507051014030c071b14 72
    0x9109aa01c9130590040c0e1500ea964000360140b002603025140b0303074a050ac1610985c1100881a91800c40c4150041d20150006010310804541c2d9100c0e0500814066407520b0462a00c0720740545181e5000f054140032020010004c0e50440080c40664a4004014405900c1d42d03101d041600151034111014103042c401c12444109403e48901510a01a0f0040080904400c040021102d4000242c422501ca0140c506080c2d400da0311240d04e0704e541d9001d65590300302c603d05400e1003805d12840303a122106000c22400144042500032881c081030080c10b000d0506207440713620b281032030b01c9964500455207a01c40c5203081181c00c0c0c089551801900441d03800c0c451161550200409071605648604e40d001d810400403815903943c0c103001c0146403590030b20f201c1002c400c1141c170068851580040321540c0280030306000a25000d880841e5a0415240100b0006440c00c96890a4403020740502d031800c4012035861b00304504949030400301c09503044880a0903660310305021046100704000e6200320f6486 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 313973920 1250 313972670 313972691
    0xb1c060e040f11010c020d050a03030b01050307270312020f0c010203190e0d02040608010b090a0b0108071b06060e151516021813020109090e030d1a04090302030c01 72
    0x24a411809141c0041541030680902e940b80d00d00b251207000c4413414401c078161a0b0b40969102c03a404424140540c0152442c040c4a20b4018111003018400b14140042030051141d955488030840c83d80412603203030980c4810342030030781c8159001c26500041006c100303541c100c10460b5001c41d910007000c076040221100500c00c41c005a80340d00803043c1807110441503420401c0c030075100300c0c510b003502e5102400c28000d04803950041002e54140d078000f1203d80c0e441c1e881c01c0d51642015680542e0140c10920204050b074041000200000409001d89040246141c1484c9d0341c0e030911001000c00541c4030004104880ea508404600e02c40100c408298107002c0d845050b07428140100351021403902c1044031450108a12030a02c0b036920b600200f0703a007190007210301d10b42a4490001440c010a102001200802c0b880c0c400100a2031040d0000407000c0d00b48403806001980020a27540552800680070800342920645262007541450400354010b081c1545502031580210040c40c260540c1c800a01402400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 313975170 1250 313973920 313973939
    0x311010e01020a080702030406021c120906021908010f0905091204030b040c0b07170c070f03050a022403010501080406020706050709030c0b090102060109020c01020f030a0509010f050f04110102070b1c06 89
    0x449c821070015800c02c3e50b01d0b40405d039040c80000d240345610300b04030b10440e980034412401c0b12501042294010303800180c50003000d100154040c060b54480c5401c03c0c842d8141060b403100c41115104500f556030710755007c621304c0c0340144100503c200a490265440c5c96890901e204400c40a49003610b503003109a20120303e4045510495a009400119104528041d040d800ca0283c2c041c210323000380c41c011a240440c2c1c18890024100085006800500000b05640100940f08101c1c907510f00f0003520061003050101c0d104e4040e40e04586003428036010075a2141030840107031182ca080100710f64980420445002e03040b40c4408141d90140013064072040c1c0322011500039200d00c8442e00d000d6071101004211111264000b4880e01c0c0100b8000740c10011420b02e00e13140d42e001554070041c25500d034020045018424469078600c07507246081840320303003403115209400b5940900050301600d001c0c0e0070110a07900800540000707140040b20550384010307a8000001504580101203481800c1a4000a40c03864 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 313976420 1250 313975170 313975177
    0x40e0906060405010909111e100302040504061410050a170403080901050901020901140702060403050102120411090103080d090c0807120c05030a171b0304060906020105091f090311010e01020a08070203 88
    0x901c11092800f4406141c1005040c1203a00504a850351008e4058566603c40c00c0d00c0b224404820b48026071518242810801542d4840d0414544800c03144003a40403690350030310b14100491642070240d501c0d50100c40c2254542c0e3f104203c022480b1040b0240700c1090703400b518a44c4944080b070b001704510349a84900d24203030b12400003164005443c00c1c5c907400d882e00c5084001d00480d803000b030445240682e0b0355100b60a81e003080000300030300c1d11000c0800c03040c07000c0072160303007100d0504507001a1658116680d07000c2c107000340c40610403010742d03035140780081150301440d003000303000701d0b4049400d03941da542c0300118021036215040703a03051200700002500c0e040024200358a56440340035601107a0350980d004810b60480350000d1100001e110304074698940920003000a030180b6580c0080380790800e50041c2c25210050640c0c1c0e810351040481544c02014490740e101ca51410700700101e000a45070030100c680640d0460203180951038800d01408103101507004001d21003c6440344166036644d51001d0b6201e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 313977670 1250 313976420 313976423
    0x22208010507140405060a020f06040b0f0703061d1801050a1e0b1809190c0603230411010507061e06080d0c06020a09082a1203090f0105040e0906060405010909 70
    0xb8107200170301c10f619018014241c02e1900e48103c8981c506400c0701349207008000d65003074076101c007003c050146000c0551a007550015040c1014040705103010411008400703c0e20200680e0154140440e81559000ca0241d40d4581c0c103a000780450304110304141c00034400c10b01e0709080c0c44101c0c2e10711610141d0714019200f02078401040340d1802c0314414242d00d094a00100300700c0540c0140141d1041121030428036400f0940120304c202400d508084001c3e04954500c08078041e00a150000c2404000240c00700d81d9105602201d420082c100d804016a22030140076030041c6580e0500c641030080609014158080000108084c44103682e00d400058a501f628014840081e14980c40039000c00c0d2640c0050003214254607040100365a1000c0712820070202d03000c1101e0029502c2d080300c01e00300d64249440c1d20050f044500074511000842c0b80c5a6902c608408940182404810302c15241c2c05142600c00030003011083c030020345403444299407140d400725003181c4a14500000407403412480c0c030664207001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 313978920 1250 313977670 313977707
    0x50105030a0506061b010204030302060f27030415020a150507080a09050a150207030306140a090e0f0321010e0103080304060504061d010e0105010e0f07050c01022208010507 76
    0x60700c1e26074001001d050010321843d0070090410a89a103802c0c18042002010a980001030b140c90a41c90001d003807079000341c0000441c080c09406d0004461006070360440306142000290450100c0038200c3e400c60240d42e2042c003486041c9000c0c03402c41500403036881c28051140310118072000e02494448100c0e0350039158040040c400360005010704001d035001c8620140100100c80300c00302c2c190340303031803001b407002c52030890542e0003180305070070190140103140182514912003040c5480c0750b00810380b214603501c6043c3d00e003a2a4101c151000c134080c40f000d090b109a400a0720b68412041c840c0b06150381452100c1c0480c4d0240c0c00000641c0000402c001c1d0613030354031944c0546140c07900d480344c0000e80b0028009550305541c8000392507040d125665903604400c242000414080b16080040d400c40340d0590098442c1040b4008024000e03542d85540f680c0070380716040c13450702d41c0e0f006002d1600a0084000c418203003000401c0c007511007081400524100c2e507070310300248225a2094411500341daa100a0200344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 313980170 1250 313978920 313978927
    0xe04030915030e0307030f031d030a030b0f150c070914150102010b0306101a03130813120b0103120f0f08090102090915120a20121c021006050105 64
    0x94100d0240782000001d41c42c60042521070009807031034115444400b080b00420310001e440060306406000e0b104442c540e9181c2e031448011400c03203040e160b10984d0000c504060341c98135000c4099460004400c4200405400c95408660b49812441c00750710101030014244940032000803041124000c1c011551400c00da002481d49640b403140c0c1d0010f140d194034a06554880e800248603032070400040b441160b400260011040c50004074410369610503110086a44027081008107854200e0700c00107680b030f40503c1741c5036101910300006072000c0d055007242c60000c1c41d5003000c001b401449103400e03050f24007a8080c0070400b0080441070700d0380c00312207010f24081504244018000ba00031003450b640725040200242c07400004400003004c080c003c562503d40d0b07108203c40f99a103070401100b8544901401e01c010405405507032200c4624000444100951110041080000b900c070305e1b030100c1c09040700800300c1d0002e0350092080c01144c03041d40036401c014030030103d030101d00c5913a074040c1400300e0b07006840d5180b8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 313981420 1250 313980170 313980179
    0x9071701030f050c0604081f021c06150c11130e07060809070f03020919020408070f031a0c040902070c030204050712051b0a080916030807060c08040803060409020f1908070e040309 79
    0x648c11032055800c040e00c1d070030701c800030304582010100100f1911040c0000360346810a101c090119220008403020000e0301d03110000003460404044070850022142005101011610030003e018440101e10180c0100c00c0c000034400c1d08a44070718003440c4068191303003020f40c8030f9000e00c1350011036200182d03020f006c01021441040744d051114002400c600300140c038080e11075908500c0c0000a522444003100c040030304006001c5c401450303401080c001861420725090100039031030540a60f004024400e507000540744104584682070000840d8040d2043c1304600e00880003400f01629262a80543c600b05000202e112201441d40320400d101d210500d810104900b00444a41400416404081c0308143d00300640d00030486501c001144210200c540c0d400302c0380381400941c2c801459620601c41d100003888005903e003c150395021409980000300d004072400001c00c0304900604040c0c011802004072068070600c0d410003410b0310440c1c0115001e031507503100c440c1c0382c40b54100d0300580000c02a207014407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 313982670 1250 313981420 313981453
    0xd020f06130e0906040f0b0a0f050702070914060a051c0f060b0907030608060c0a0e0d0b0403021204050604030305033301020f0c0915060d02040605090111011a09071701030f050c060408 81
    0x26041210800001270115440c01c2480032a40309503014405a40503890402000d03c05004c1c00f0b901d540e905070403043e0760810310046400078249000c0c0a00ca41d00e00d502076200740741c0d8201c00114464102c0c0000c1c16010050814500410400140328051000b40c000944050f0181c054031045034004001000f0726a61203a64008941084164070104201c4a04022455032209182c880e8240100002000d81c1850b00c0c01910b0a40b50840700c804005003400104000d984d098103032022a03400d400e16655982e2021802c25210007030f1080002c003054201076024020380800d040b0075001b6401e0302283c0c000f820200c44c0664036456040c44590001c0e4407400281c0100103030a452601c40005070500f410f100c008010203059030401c1c0c0168000a502089245041d0f03070088410740841c0c81c09008210000b4483c56140100303e0400c01c07140200c040401060650344680a52183c4a1078011014100e5840e45000d03502180a0201511223210b0324840c003095140600403201103600120042490144e0f400254 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 313983920 1250 313982670 313982693
    0x50f100923090108030a020601081204061d03061305060618010504110f0c0109200d230f1b010509180604021213120f05090d020f06130e0906040f 64
    0x2010341e050700c5016031000b81c0b22100210b0103000e80d40040c544400c3e041c10020305d0311074168400102c0e80e00c0106084441e40c0b1180403281034032040c3c41c00d504000c40c03030b403469050800d0324a0004e13090300c034540800c20400c51405107508850700c910141c0b501c54072800c0800030011501410b043c101e04a60004109034981507101c20042007006400b42e041c50ac46d200a00680c6d044000c0614842c1d4580e00594200801c145003a20b1503a100e519501355030b84845c001ca1144002400d004000c5c14030402403e84128141c00744100402c030b07031001c603140380c40856005501c070007820b902e4501414034100400c0d5190b024409a81c0c0310080030380500c5070110340149011544402801454009508201c8802d0042c541d180b5180706242c07041070480100810300c0c0400994102004100411101ca60447c0001d42c1c003100b1141c05140490308008461a9400020901380d03500034040d610082c0040c0085245801c6000f80c0103c0c1c002c45802d030032a6880303644a54880340101c8004010002c1112011f00103403080c50703134 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 313985170 1250 313983920 313983959
    0xf0601080a110d0e0c04021b1203070e120c0a0602030d0f0b0102030f130504090602070b1b0316090f080601080f0d050306040504111005030a0b04021608071401110301050f1009 77
    0x48503650f203170f0800403030100d074810130f60f0f421340c011004601103401e5801c000808600c440d43d6442da1071407604210040120610003034051103035094201e4144020f034200500c83d001d01c0010140071038660354800c013954031390020521050303641c00c14144000d580c4c03ca2050302d1011406802861070480400640d2041c0da2200c012111b40700c90810020030a51954410301520b540725500042e558400c4c1d04120801402c003c08914007010034031030300034218054000341c1ea0002c0072406001d0f5480c0d00080143c400100d80d401c20004803240400c00100c440001600604a900080a890000003512265a07c850301400382201203081000440c403242030a5010b154094010164a001205e0110000d103101c4d0390146a00300280000c41409100d461a20400c00b500714203c408500c0c2810190b040c1030a8080024003401040c0c010034510107001c0c2680340c07145040403000007084101410c40c40e0700b03d42d82081c014075008040c03134040152241004600f44860004039150280d825103070150307003070550300b07039119 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 313986420 1250 313985170 313985173
    0xa0e0d0c121502030a0b01080c09210309280b04031208060a05031e0c0406030b040803060616061b0809061503010b0d03170a0b010507110604030b0f0601080a110d0e 72
    0x41d0080044280f01450050405c200c0118480f20210001001c4007806030100d6842901000301c9000e0766503041d13440b5138044032a41c0250020f5007540c030103400d60280102d400d800c0003a5000074039012081c014042c002004040807440b0880d00c81e11165913030b0103540402001c4480620720014024040e88403958000001801d5050258440d00403e041c1000c440300d0420340d00c04507840071030042062004110710402a1401c0100791f00d0358035841c50224014001610003200000466071035180c0c0412a070520b001c2c0c0c1214120f801070381c034194004280c140300703d01032078007030342e00171320340385109400c038601444030754006100a07150b003000002e0811a142070030b0340c55941c8942042440e100d410308001d055000e03854090f01c030036091000301c18001000f08114552440c0c2002504c080c0e8010054070305040d0800c06110901e100744000c14940d00c1030b90130140203107000204001958140c034101c1803059000781d960b111651100503050041e6410b2414210311400244000001403203103a1040010511040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 313987670 1250 313986420 313986443
    0xe0118060b1512070f050c030d022d0403060c0309111e090c04090e0a0203030a0507030507051f0b0a0e150414010e091903050409050a09170a0e0d0c12 66
    0x31040c00042d032000701844610b0b622002040300264000180d004003607544d0400c6d920300360b022030071680c5900c5030f0040800d00340e41c0410400503440002d0805094000340700d10f00c21039011841b10b504060b030018030085840d1390030803540c003498038424040c0c4108682d02000200840110700104584e0004c40b0210243c0c080c00042c0d950410342d80c004155004081030501c15075140e04080044003680da680800050070340c49141d880c001030310f00000700e81500740d1038942980c0b03401c040d213804c503254440d81c00060850b10a240003029480d2112641d2442130080c9802001012240401c1c00920050ba00ca20001c01039114005a50004c40c0000e0f07203a6040010f0000801e803480041440c0a080280c000f2403181c13401c003041100000b0204402922103103100d1b03d8011480480d82c1c02801481103025140b00581c848011403000009504800d00b81a0300c01001203448c140c4142100d604e4108401d4070001442003403200c105400c0113580c04481070b07000084c0c5c07054035003042801c82041c200350000b25480d0714082c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 313988920 1250 313987670 313987699
    0x2030a09061a100206010518060a03060c03051006030e070e0a02070c08150702150606090f060d151508010506030411150406020d0302040612111e07060e0118060b 71
    0x5119104040750703a0380a03000d41640040078003e14585903a0820b00350341c44100107018664503030400145990103130222020a94034103020403204000799000424990a10254007400c9805d42c01c654410408058400706c02580ca54044042e2440d07000e101c0d12a4212080c107001421100b001d06e903103c8804c81001d484c01c0c125682c1c02d180b00c0c1c12580400c1d407580207000c03c01c0901c070a0324005600046c0c9440140780007004551038078140080503010511070348000404c4050f60700d9804030008042c500401d0240c84014420006000d030123400c8500007601009180425821419007890002611aa50300340c6c081e8205003e00c0321700e0340017410903600181707080034103440d5a58418400d003c00c01a8107a0302c0d141e92421130040c1c54002100303c0e201c2030600501040c44502e5018042005450707070a480403e890000742d0032252140320300701c10095528800d20095500304c1c2080018107c9500c15201048411980100c190072604103c03e995000c405418a01000c10442d8002c1800180000e24507211003901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 313990170 1250 313988920 313988933
    0x70212010b13020d0506030c03101e060803090a270f18030504030302060903030420011404060e0a1a0a11191406060406030201021e01060902030703060807060507080d02030a09 77
    0x2c440b100c100150001110325905446002d0981c221009400601a013404840029100c42034061494001c0e96540c403d4962400140c00120302200007900800105490f9440251079030300020038140a244032040001d90034011114110900e401e4010200c01910b0052200c0d0103030051414030ba100030303201c4080c0300c080500c4046001c001c600c01d40b21076039a84c1c41d42c5000f0f0704098000301090410b400910400010420350070b80d82c4009021540b04506150495005a400c508020b5003401c80c140302141c08a24039800c010a54481e40013100c1212800d40d60701c105402c80001c0c0d443c001c3e040031050000201041c0244c00041c0072000c2e41c01030f5014250040401040441011800d03a0b4444d80106003031001c460900403113030806400c0c2c4091001500710740000c0c0da00d640008040720400c541440d40071032182c0c21f50040d4050300c04004199982c1c01c0800c8010094003039405208040d0240010000300d003405441240d1015a00000050800709191080ca00030341000340102c412680703541081c00020791 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 313991420 1250 313990170 313990189
    0x11e030204020a08060a06030203190906020c06270f0705060c1e030a09050627060d0e03031b0c070303050d18060608070f0503100504030311040603141308070212010b 73
    0x8413951100c6251074881c040090307918650b4003000a1501c10402d0211856400070102e00c8207100306008915000c4924040780284107034030f100710343d078010501032101c1450103000d20502644000d00d84008903e0003081c054a4001011380610950712040007003005040000240140c0401c00060741c0300d0078040c0ca0b0403203860003110002e0180c2d0300002540e12425403c0401070001d413109540e03c50034240e034880b0403003031005c40c0d04803004040b60140d10380000341e036200110740c426542010306100701a2054206c81d500e03082551034103403100703043c0f14141d000c640b9001920b0285140c3c8008141045c40e640703090f03038194002c1220703000b90340d100e47c2c1d101c0c1004080c038051200b20f071045400140c8c15140c0a0b61909014051b009010401c400c21410000e940d000105040030f40155000080c041c0c49a140580050041c2d01e14030907c0b09000c03600060240d05030f4400c000034840481c1300d0784955a03a864000410300b9594000b40b1485003440740074050308181c84803490304001071000049108121300003032040c0d030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 313992670 1250 313991420 313991437
    0xa0b0c0301051c260f0f03010806150d08030a0920130c0c020108060f150d050f01050105072003010515040b06040b2704020f031608040b011e03020402 66
    0x40100180c0c10500e410700c034526480f05102d8441c15440c3c2d2181c1d41645520b20701042d01d4074011131040c904c00c21008540d0f003112041c0c443d90307480b02c0045540b0700580091103000d10360b00451000070b04441e080c40c1c0d05161201c0c0182b6080b0380e01c0c0c5594540d4210340000d840f101106985104130000075442041d12000c10350082c0091701c03480c000100b00032281c0c913801e60180b071aa04084100b184a500440c01220ac190309080c00b80b82d543c0d400d0302040c0b000c050350813020b43c040c00e588800e181e0262018001c1c8201102150103010942d21306036032511003a02803003228001601044a50301152828101500c501d9110590060060184000900f074950660740c160700c0b090a924083c0d05e03850309101c7c904600c030301030b90801c0c00c262400409070014080c01d5500e40146140d0202c04010703030300101c4c02c0b81c1d0345000100300f15101c150b0840c40700859002103400106144034071404034285030107418514451a44800d08004a07820000300d014400e007040501204811045070102c0140c4d5140054211503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 313993920 1250 313992670 313992691
    0xa080108100e0606060a0302070c0303090f08070f03080c2401081516030b0d0f030e0909060f151212030a0b0a081209060d0f0906110a050301170a0b 65
    0x1941064280c908050052407a6403146140041011680c2008500160b00250445000d501d5802c00e0500750701030300c102e100c0100f642c025800040708050b0406503406c241c80d1285000400c43d0f1f110b0065503501c180b680210b81c403407101c83c0802c0000400b400700612181b2600e205881000c0100c1076518080900c68a81c3c26500e0b101c1c40c014007076108100884180080441042240b40c00d29000c08680c5961500300003082584030000c50589450700c99014032110760204c00c24201d10790700c1c10010007410384401c42920504240c8040781460b48000740703d9025002d08610125039480c0c03521080750341e00c8808807590700208601280f14454000f1f0000d01d001074100d24903036990340b84c03003080002140c5405001621400c0e50758000e00048800054840c00c015101050303030341c0c0c0d0040d000001c40d24011081800c44803410100038011006280d0400c1038042e20840090210354065060382c4007500817826088002581880100f040804604a240400d5801c1c0c0039100d005030191075030740c00c60700704564840c01c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 313995170 1250 313993920 313993937
    0x105090c0f04020703090b0703030204082a0a140111010f0e0102180a0b070303020c1006080d0305060406270216080703090605040e010608090c0a0f1419170c03030a 72
    0x3070400c54100c007450349049400b103103800300c00ea6010b8555980d0b802403503503103c13005c503104041500940c1102c0c05040b41c18110748244200b40c9400a000040c0c21132b030003950311014100091400c004c9040d4050f00d828140c0c4040300070a601c0115080400310301a8807841d0b4980e00c0707002c59403619220b0150b1401c500000560f50322081c0104a0800001540c0280a1441514200041d514140c00d80390100c0e4185005a038a42d0501c03100f40c500b80c100c40ba840381007841d280002842e90f0b00020344100350340311790314184034039a070319000c01040b00d2041c0b04a0724001c000c034540d803d0800502c0e032480803011500ca0014101030a0380a1203201c02c10f902411941c41c0310000d03440041c15000000b480042a06282407850203091a6104040300010f10410003440401000f01d10749420910841c0c95001c0d002c0d08401103541d41d00b440419541d00b6104032245201d4541111102d8200110814040c1c4040c04203510b03058580407013040310000141d4207412500034403044035a9660240300401c400000d99441204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 313996420 1250 313995170 313995193
    0x5030907030b090c1903033606111c1d03010f0c030e0613080d020c1509061e010f031b0f030506070909150e060f06030103150606090303021c09030203010509 69
    0x50300805c100300508104d51016080001950104e00d031500e00030401c0098480b0301000c140d01d140300c05141e40ca001140030440000c1246d5030b0211003820744900030b408588043d4640d040061a5102200c0301a0015444040c03480703407004166640715408002a000003010f1169103c200100c405001e100e00010b070301c0f00c0740750b9201481040031640000440322200102034013503880000900c01ca42c83d1150440e00403c4801a4810a000a0060400940c90f019072032401c0040d070ba40300e402c11558482c0d409803071400100700000320311426041e41c021040750040030741545c4503d001605144603c01900703404000c00304032016a0304900c0d0007540700790010721480c180383c80c0c003a102d82c00302e03040082071340d03c0c0c800443c001c00f1004900904a926802c81c000c902c1d21403101141061030001c1d2000c1d08884000000020031a01c82071403200200301c4501002019202e0b6002c44055082c0e102c0900141d008104500b444089920002201d41c10740c00c1000364295245d01190a585003100d4010300c9410010300b185 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 313997670 1250 313996420 313996429
    0x403170901030c0807050412020f1305060913030504170f1006050102010c030203150904020307050409081b06060a03120e0d05030a030f020f04060509030c030319140304080301050105030907030b090c 87
    0x643c00c1414207000c1254034250000904a01481c45040d10222035071041e0810740d140c206065800c0301e000b41c80d80e20540c145c404080301030300c4151902c50003046403400084180244c00a00c601d42075041e80d8142c506454881760010782c030f204681d000751501a41c1070844019504101c0e200d84030886400110701380e0319000000e0300b12070445109405044c01082000685450056100e18140080f610000d00da03d45002082c5803075501c2e00b1142d00649001c0040b4148000000541f0b0305010055800820880c0c1030b900740c1c1c0f11281a01d001d074104030a0031050000401107400b5480301401d80c40c00c48220002e10340000c170070001700c400650b0300d0f40000650043c00c9030701d40103060720380704070850640c6483c0001003010b0152099103e54002c00c030011a8501140da014001108191401000c50380c0380c20546d1a034050644400039420f01250032a03080704a049410001c0da4840c5402001c9541103038a06001501c15500007403200c4024004d030f01c0003100041c402c420140c025030500c0002c00c440c0c1c90f0403041c0b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 313998920 1250 313997670 313997681
    0x3040f053a0c300309030c17070503030a0f20060103080a02010b0405061f020102221d0613090317010b0307110109080301060e12010e0c01120e0d0e0105040317090103 73
    0x100007003955242040d10a0001402c5054a0303000c0c928000f00b85240c10200c0b0303140d00300c1d040100300c0c00803400000791b030716130441404107041018000d4408040c0e40308109aa03a1248021440100f180c0c0c3c00c16400d0240a030006440301d01d5101c2c4010300009001c03a446092140981048803006c1c40824a1020a582442030707039000c50003650f04000f2030400700000707107010398030000300150400000307005a8918401e4060702e00480c1c8d400211050074014101c02c0340f80b03217140d0180d402e2440b5240e10000000e242500c1a90084101400078103480809500b11400740034050301c168140003031039010480c1280200c0c1014000d03c2400301d00c54503824100030082912100d480d0300043c1e0382c140001d0001150485080340e0444956040810446000401007003143d64500f0359002c0359460035402c00300c0e045001c10803001d5210240e0b01c84034200c0c20700107588200c40049555103040d621403141d88460034041c2014840da8101410500c0c00d1a40c0e0f541e6900c03d02c807220084e17000f00840403da01074503503050b000c0e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 314000170 1250 313998920 313998929
    0x21030a0c020a0b01050411040806040f0b0601020a0c0e0c19030f0b060a140a021f0903080f15010309140f0c030d03090512030601030603020a0b03071103040f053a0c 72
    0x141000c2d140c25102e6401c481c2042c020039101710342d19a84a04038000200407140240041001c2d520b075440d09050800d40c07040080c009035800c0010700001050356101088115010344d00c590000d204038244910303004081c40062422040503410040402807110741c01103030411180950300401c0140c1c164880380c00f40c40c2c00800e8140182d0f418454001200d40012807200d50b68a814a200e444005880d803c078644041c3c44a41d030340214540f840c004c011080742e0805401c9038080c0d00c950b03a443d12941c864090280c0c0c12140034000280141401015602c29005001024010340e84280940306600246080110700d07850020326a100a8100b015814140101d0300482028141003103e2446901d0781c549442d00c0d0400344070300040000001d501a800b81d0300c500003440d0050030020030a92135240d003205036401920bc050100d1688507601201c2940001240c007550009407054140e240303800180148140085003801280a5070b510f90042c9803820080144104c010340c404254030101e6041400385400250031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 314001420 1250 314000170 314000173
    0x9190f020307181a0301050610260412020c06090105071407030209010f0305010605030f0607080903040308041815350d03050105010f090503070b0d020c0f0d090b13090504020321030a0c02 82
    0x1006210f82d49c0310f030189924403090400c4d4030b0144107a1342485140406040031801440650203001c280180308542104194194007166100360b0340108001c11801907000c40c9000030400c1008400149030b1000d850205802881203500300b60310fa50001e064444260031240c44105408820014890240038484c010074058014002c000c0518051988441c00101030740144880140800d0944104100b110011a00001015111900c5107000060301c0702c41121602410309180c15185011565060302c0e045400b104444000c1084000c245a85034086842c08501410340f1071240a82360f40900ca15002ca1406070b80003c1c407581000005010034000040400401c4032552003849551000a070400070740301d0b50100786803108002600d00c8041e102e4000d00b0030050242d01441210130f1800148107050034072503210580074035161a00000240260755100360031041c0030600700304018440e4005a04240040d05a660a030101260010900d0070741c43c0c0c40c80302000000030044109403e102c3c00d49020014230 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 314002670 1250 314001420 314001431
    0xb0405040516121e050703050102031905010501080915070c060204080c18010812030a02071e03090914130c1a070605130308040201030c031d060f09190f020307181a0301 74
    0x485184007104c8103007881c0700442c5650820024041d0400030b5100465002000b50756078907042c0a003c02003807120398401e16850800e03001003003540c01044054404d11220300200b20b9148006840c00c20403402802030001d1000703c40084000c90810300060007e0104000100100040306050042c92a80c281c0d00814001c4c4042c018440160b020403800081780c40c80c00704c0e68883e203802c003100000784500c44004141d541005103200380e0f40c1c0c00b001140103060081e290b0b02150340ea03032071101c4107880d00403601020391b0300300c0d6000803032182041080f030741d5050040840480750f5880750b006240e1a01e808410301a20500803911344108050303030050a5021540c0155014441e1555070301a005100252000b4181038440d15400c58440c8a907200900301c8104026100c00c680c980c160442d110030056032503c2c500c0c0c3c3c2a07070010fa80000d00050b5800341030030440c5402c0e4180c1e00c0303882e034800182c08503a0403640750052580006041c00d40091904d00d02c19036110024140341d40641c900c40d043c07001011a4083e90510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 314003920 1250 314002670 314002673
    0x12070b0a020703050a0503041e110102011b020a1407090c02150702010207020a03261902010f1506050c0312010e07110c030304060c0c0909210309020a0302060d0b040504051612 77
    0x11305844084956080054582e1124500360f10035480c072a410080d0400c40c079505006114413106a001710504c280c008020309a105407103002c2864000d61041c026074031042a0300005070140c5030149000300300c40d0940751103940714420b100035107240e000460700692080c0404004a040d40c48910303009085400214038000259011500700016840007070080d074505803107000989645114000e08080c49402c0a41c3d642000e072401da8508485041400190b20341070043c140b59070903100c0d602c80008895009c641192510700e00700c1d140d030301c2030f0080c404d1408140503e54802803070200e01c5000e01014540d01143c0d28102c000146449200e041000d15503100d01c5c0c20b900719071000f004840c01c5d00c03154545100206001e08144614400f41d500c43d0300c01902d042c0c0030310244214601401400d1a0103e01c1380100107440c81d00305c060700c4482002a5000c07166800801c0146800c800511010a1960000c02d01c2498100060b045600440781030b995900100050380203980400b5000c405411508200303a0381d41041e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 314005170 1250 314003920 314003927
    0x30603120f120e030702040c02030a021501080606090c12070f0e03060f0106030b030a140a0b010b0703140904091a040606060f20070b0d02120717070305061212070b0a020703 76
    0x781030340e00e82c41c00c1c1da5000000c00c92800b07108452400f82c01402c00d0010300030900c0001d60b80c2d8043c041c0c0000501030203c41232840c204100b00c65040741d81050051589450342d100f00458040082c02c1c00c1e040c40402c1119a40710301102e10030700e10840c40e603280d07420310310310140014110b03d80f048100d81c82a0400010400c582d000074001c541515103501d000100c00d114640424a80086410044c00c0e0840344161940421fa0001d105924a8400c040d0300303002c5e982c0c0c0c002d00d0141d17005162000f404100c9004170382c88100c021030080c0c4540b4000820210701038200c2d072581c01c0c141100584203403248444004002c14041c0500504008002503e0207149030200050010a86400700e0070300aa030070508407042c200a50100600c0015121f8148850394503038812940400039032040c0c546032643c107119000118001d00503518809004c6c10300d00030b04201d0f1388040c011401084018446540001d10a40200403071408115011000c0030308061301ea40c130b07038003410a50492000141203014140c01001400e00080c2d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 314006420 1250 314005170 314005187
    0x40605010c02010206070807110109050619020703050f070317150f09010f050603060d0519140106060807080907030c080307061401060e010f0905090c090909060106050f0d1407030603120f 82
    0x46c54980743d000d948545104072442d0051010050750383d8203008500e003d000020402c20b0086200d410301c115018450b034404030a9004015002d07010540502250391108801da004114581c440c0c50004120950502c07456444c420503100c0001c3d403010440c03d03900d1410404030040c49020101c43c6000c6079850442101c0c40001d0300d01a080c012070010001c15000d845004d461040181c3c07003c160b5565038945801d040030840a81c6040e280004255a10800780701c046c4505802d0755080e650b640100d0f540c3d094181d65030031014046480b2849065400004074210545000150115401456a400c82c1d4180381080e100070002d40b040c4580d44000400c0040d42207004000720307600a003005030302c0540c00f402c141c941202903400389800989200401c04001104001444112021625040340d40c41d01041281c0d90741e400d00543c00401c40070400c80c001c000d260805070541c006641c0020410f0b1115070012a41c05c0d1064994901098503658144200044800703410402c9145160110216110080c014840300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 314007670 1250 314006420 314006431
    0x1140f09161b05010c0219030f0f0e10050a030e07140405090708070f0312030e06150d02041a090601140306100c1202060103030f0c08090402090a030b010311040605010c02010206 78
    0x3041d001455406900550905038407002040420701188a030341071082c00780c540464400c0050060941c0c2c094034028070341540c5049501582c030304050300c110304420359070b0450701c000344002d0180110f2000c0d034a56601c980c0a100300b8040d0f8541740c0322144000d02609449116460304100e4010200c00e004900640d4400c100840c0100c4000c0383e0ba84514007054101801c0d80c12102d07150090340e4011850711201c1001004482c4104000c5020300800002101200e902d03107003814054000401281203c1818034001100140090200202d1003103940004c0071240b004000d5040c9084058403205a40b42c440325a40e03100701c082c203001d440d1413081c803506111880014040c078428054142d4495030b141c81140011401a8480c02c0510010504680650303601d0003440b00304d0004002403086500103104210608a83d5800b140003420b080861080001a421800f42250080e40d80c0e00000085900c01c01ca0034001e501400e10603580c050010140300680c0ca49400042c1845108003030300c001130340c0c00180e559016 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 314008920 1250 314007670 314007691
    0x7020d060908030703091a010545010302041d06180709060b180a0b1204110a032d0b060607020a08100b011b02151315050301140f09 58
    0x6801458030500500e0345040c040d04012001c000c0145003505a400314614902414000c002c9024003030070150051401d02940ba0400b10503000009200e5800d41d2420301000107910344542003d081c071081c07400344081c0c5d8002141d010548010002d6003001d1291600c65074207000d80f2040e80e010b01e0041a82d800d8094034640e0004a980e00202600d0004c1c4002e002030118200140180ca0b500d1460851541140722400348505400300c100070246004812801202c800c980340301c0c10582c41481c03100310354900400a844401031110381019a40d43c8225203000781d407260004c0384035014862100040d062000801d010209894112a80071036448101140d10040494410356114481d202159420809921003801c9100d803002071302c094a400e40058151081c285d9446034005a0003004010504184c1c20103900f0189080785103404001c080002d101400d0610140703001503503a2002c440c1c0c2c202010a071200069404001407002010245402c4140281251002d1051080030700140f0002000382515052 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 314010170 1250 314008920 314008939
    0x10305060c030a0e0604080405040f0b100309050319021c030b01201501061d01031103130c031a0a06090504052e1505090903030408090910051306060906050f0702 71
    0x5007039503500030b8132503122400140c1d040d0b400c0919040626403c2406101c1c400d508082c038012481426216580400c0301c010700c048081d08085400350014071080c0016603040c00200901260040d2602c80b040c0c55600d80d50003409948404000e004014200e88110b008050421074071303090503130740243c001c1001d0b0340c81e04001101014400d03049103010384c03412900d120184800000900a50410f6110320200c0c0c401842c11400c0445c800110103c1e202c00b400841c2c03011050001c03c0d000003951101c1034109200c1c0d42d40d00e1840e501c0e9120003080321454a81060035030400c0003000540c040703d00440004040c5201d050109080c03070b0703540c140c840b40039100002080c08907400d200401c8250070901002c0c80318000701040546214011003e50300c20038041d1501918442d0080b4103400b00001c02c50340700350b8001000d182001d001200f08000c0502c050200d07008100300e203c01185547d101140e2800b0b40000701c2000920602d09200a00b4420035580220244941440354038400d900c108121400c4507070413903501c0803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 314011420 1250 314010170 314010181
    0xd08070201022a060d02040e0907050114070f08030a0209060d0504020a05220e011805010e0106080307150e030d290a05030a080c010609020403080d050a02070c05010818010f150e010305060c03 84
    0x74000c56204c2140d0340c103081d003480204140481c1c0303200bd4480a0342c4000c0b1340031440e03440c04e6241c4181000244030045a80800010074110310245410514840c4090f00d03007040000091480e800000c10042041c0d600c009000031890408254401000152070341c40d40c0e1108500c000c03602142c0400007100e20380d2107503001411403400b0350015180c1004850598101e11241c00d0041c001d0240e8402c5000541c41d2610101d8869400001d40c0d41c201d43c80390702010200e06501c0d188010300301c495040101c0344800d001c030800b9822540660800e0407480c840c010b441d0b40828a0301c40c1d1075014400d10602460041c4c405000303507100407d4080c0a00d0304042d1840d51146080d4181d401404640d1104482c0d0b840403d011040046d50001054280c906080500440d2100c01a038002c074403d02e803006001211040c2d0030000d40d4002d0400b01d90080030380c1548a15a1808042d45080d00d803240014422269100c0103014541e600010300c2c005040105003c504940c11076941641e035103405010f603080c60760007000144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 314012670 1250 314011420 314011447
    0xa110114180a02031906050c1306050d020c01060605072001120e2b090801270203031317070e0c041406040f060207052e050d0204050d08070201022a06 66
    0xd0b086076020f411501203020a1400004440e031a001c1120fa03035081402140b06100c4681c103603180c000c41c000c2c070030290510301502540c0c0d5501515026040719000e1140101400d0288100801003086498540d915081490b05510b210398001841162203021241c81c00f050340c0c4842a4140316001200014881c0d002c803110500c0e0543c07521900e1450b103584010520090f00b0300303d8205000c030740e6440d00c0c20700503229a50b1074207803040c2c40203c00e1202c2e00700c080882c0c802c0302c81010340381c2203001500f90b924010207503104002801c0d850f08052071581c041007a0080088042058100500b03160074106250f00748402964070600c00c0e03105600420b040f4040c4d101e4aa9036400071240240041100940e10581e6044081d4070b803c154400c01c0d1081d000f84415403064000045c0000941149a000700c0014074201e00998203500446441082180e0922020407140c841078400c0003114011440180c60b90401d2000a1070415810707440c0b942c0c1890000c2a080300d24141c8a5800d070703400100c950301e464041780e05620 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 314013920 1250 314012670 314012683
    0x30a0e1f1d101a0a0e070503041502030405011a0d0c0510030e06070809120c031209010b06120411010e0a0b16080301031407051203090d0c030b0702030a11011418 71
    0x1c001c0e6000340c5003001c0d6a407440d070b8800c0b0b402e000014000c3e0100290f0004002c3c9521440c0b1504080d00b0f03092000481503446880110b034024810304025180c10504e186200883c7c100311811034081e03540d0240184031341600480c60400c050104c40913003081005a81e18900b04a031441203900a00082c051619000c2c0640c0080ba2840001001c8919502d0808001410500159844c16442c01880c0f1421207034004081140c00c08244800114581300d48803002031175680000b042c800e0207541c0d9a0351a58030703a5500008119410540701e00c07040c2c50030282021000004180c0086050001da004000c0c0c1c941c840308807110485154505550702e404004e00a0004452400c1c002071400d00b0000000c800c021034041c6a207894042c0d1f40c100c03582a82ca07441809110030a0001c0c14203281d00a2000071541d01d403040d1240c04aa00c04c1500544003aa42d07541c0140d1100240d9613000560030110f003414410b0760100100540d200401c0080c03041c410407000d0b02c401050090b0568100683c2040c4c071203000a03040106 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 314015170 1250 314013920 314013971
    0x3020904090602160b090304060e0906180a02070308010e0714180405040c032a2106060f062303061513030c0510020309090708040f0b0903030a0e1f 65
    0x303540d1003210200a080320700180c00120b03540c0d01d4080201b80a20b1300082504d081ea12103031102228017031664100024000010100b6030302030010582e40c41581d01546806000d41d00715400562616070525014001c1c00050300108014600141000b600704d600c6084650301100600040795034114050700880c030701d88a58174098000d81400c2c00d000402202ea0094411079024040003641c00300b80002440c20f807413601080181034854003034244410040003801404007081100ba1142c030048036501da0061715903907400340d400480384c0d130340400200d43c015900740404144040c0706210398038030101c6a28180009801140140515410098249001000c441e0545400014441354542e245031242c0105094025203010700c21103e502e141d042e0000080d10340803030009010010399950000200c0340f2034001401030769001035810007079000c41c4804000790b000b8560400956602d2415000020903103455092124480d80809003c3c40040c495583d0b50700030a58041c40440c190401c0844ea0300d010003031000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 314016420 1250 314015170 314015183
    0x1060809070e01060f031b14030a060315020406110d0c080901050c1009050706030204080319051b0c0a050901031101271404060e06030304030803071e020a0c1e05010302090409 77
    0x4c0b480c1500100015500d0002d07640038000300c5600315100c400e9a03031155040020660b03c003000c2103131108030300185500000405000800d9656a1034411031503540c1034508040e90741c0024240304080c2c2c4070110004a6003210001c0c14989600e18004041c100000700c00b800030040460002c04a0f0302c00e10031202080806030440b00c8403802000440001e100307244003247d280c86480b80020300140039000b0703182104c20650166040c0342c40e0483e041000c000800002040010030420300140cd580c206c0000c019028200c000c000030a0703c8400e0006840d05500141d100fa0390b00d400410004d6142446120894002e00e441d801542e41c0500b050304c1c00004050720024103502c0d00002c03850f0360010401c00c1c0040000c80d005d01c8655a525142c400400c41510036070f826420404c01800411640c070002c5030000380da4940031030600d201e620f9901d00013600140d10030050f000340000c9024449022040409006420010a004603824142c58801001440740380e051540226404c0801d940e03130360055040d1030b007000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 314017670 1250 314016420 314016449
    0x705060d0203100501033608030f15030111090418050d02010e01051503030a050307090504050103061d060f01050f0a090203133815150a020d030902090106080907 71
    0x8100c0000c1c0d08125145a82d40c00702c900300080350340c0309001d0000700d9000910055080080219071004d50f04120800d06401d994251500c0e0000d414000107521644d421452032000b402e09004098800d8102c43c460742c800e80c1072a0900e2402540e0030b04413884ca0800b11070019800e90742401401c080d61b61b80c440684030303014031140b024a0b1a0190000da1885480d071000b005039980d1501003d000d081c1d80c80d035503905a4024010042c49030301400045401504909141043ca5502d0300081c00303444003601304840160f01c51800d940301441c03c40004070002103030400b51040d46400c8082503c0300c441485814415004000d10341c002c0d44850b8000005030890700c1040d5030702d2a00003201d490650350882c089a14903000000310600151251884d80d811002c0c90f50311410601210340c081c1ea0b560082c01c002841002c0d001001aa641c64240301c030007107071032020074640341c2c1c1010f0380c00303401c04c02d1540c2d00384249402c0400100059840d180000d05461103800c006000f0748031000c80b185800b030a138203d00e07000d00201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 314018920 1250 314017670 314017687
    0x170f0d020c030c1c14030705030a0f0f030207120e12010e0106030b010509070207091d10090309050418060c05071406040203010c030e101a0301060905010519180905070506 75
    0x8241c8040308101941101e034a20b6800341444844000074140c501c605120102d0440001c0a045481500b071503140103d03030402c0110349415040d1b901003056000411443c04c13401c02e4154000b4104804c20040381070850800c4095110a201003041280c41030400c480c1054404681e0b462004281a05c00c03c0b41c000c10010300209000e03402016507000503182c00c0610780c0002036515012005503c00c507030603400b4007409450220700300c0180070298281a4880ea032107140d0714403a001000141b842201100c0d02060304001400c0151051620303401c15800749007000c21884210311641018900258400b41c0011540303484001110103001d000d800501e0018902401d034200c0c840051154002ca000701c0081110012080081e811100389211000c0950840d00e400c3c66240015400032a205001b800b090803642600c030f00107403c50310740d40c2090007030076074440060010381414141c003400c003180f55800b00c94060a18a140b00071041c0c200180a0950b110502981007103400d2084000a03e0040d03c6140c584d00c40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 314020170 1250 314018920 314018923
    0x4061214010605030a051c1202070803070306050a0b0f0906070623060a030c05060703030618021b0a02031f09060f0522080910020106050d050c030d090f170f0d02 71
    0xd030210041198200340d004201071801183c00224107621000604400d515284e5510b120600030780c400c3e0600003840407141030090140000e1505a02c00e03044241c1d82d2070007000140403101c25422940c00f51020000c00d000c03200d1408111207410310860003560725180c502c0c001614602c10b41c0c00091425081c884c100c1f40040400b11b071002c060381c03407088100301070b515901444810800c520010b0700c0f15640e8001001941008001480414003c2c030700820241e8035080000e0a03803101c050500121540000d0440c45d442c118034a130020240004064010300d101500020b03500c2c1c910980c0501c80c03e0700d05d8174000c411440c55200c2c1c418907a02c41c03428017010445042c024000e0000319002412402d220300000c0380c40d1102840a41069800243c26090103040c8003071045030800c8070790a1040d5940e0b0000400e0b10743d200c0b00e500d403441d0703c1039005022850300e04060505110100c0b1a200c01e100708a40e05124107049008040700b6900b40800840d48a6441f482c058a00303c0d0185c0c103c0480c2c0034150304c890520346d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 314021420 1250 314020170 314020193
    0x131703030f130818040b12071401090b0901210e1b030a03080f0a09020d1506270213030818041a061206040e06090a050d0903020f0906040612 62
    0xe405945480342d610040c030820442804100103200d880e080050f449412204641503007410805000099024000300105405030f0f1110303000740b55a8003655007001441030302503500d03000b98020720f040044a898481c111095003e5901107905020200001c0100300d262016446043c0c0500358081c42202c1d0b003502150344131040714040a01c1c072000802e140d0200d080004041c2c621a606580d601280d950340900c1e0a00bd001c09028804a03036181c4496030050703511241c05928050068600804480680d41440c3c2210901c2c0d010106800700c06107101e80045502c10074102d4000006000f590b1a42c10a1100f00a01d01640008000c0d0301d005c6020400107032090640003006c0019a001c00c03a01c018155204092205600d0095020100300100503421048000301600300070054030102d00e180c0300720301d52818040700312103200240d44190044028400f0400c00d81080b06068140240c1050854000c00c1081c005401000c2c002d40801010030540d4480341e104400401e5580714140c01e9400d50300d40340001c0324 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 314022670 1250 314021420 314021431
    0x906020d03060608070e06040b0703120b040b09070807050d051603140903160809030601080d0216140907140f07200d0b0903041206050a0e0601031713170303 69
    0x403030352080588a50280c030400c0d06030742581d140c2c20415603810204981c501d81400341300f40c006209210000343c0903091805807408503c01c1d1140b002d28007804a440c41100d0450314054030403401d218040c1c40036210024020342110b00f901d04944c0656070707040150340d188110a50352507201e02d00f60400c0142550003403d8201000c1c08da600340b00c10030514142d6411520190723041d1005800c10864424000e0040c141480d02c948510700c80b505006801000a04100003644035860607000310b085412844d5040c080080c04034a6051070820690400510040070301c180440c1d540103151060201700c0e050b004502c040a2442c00342c0a03640e990362020069105500042c4003140d1011158100080300c0e050100201c0e11380d14007030420721400701036880d900325916000e85000c659000400000c41c0781c401d10004c10002c00d0040402003024148110b1031401c44404e082c004005402440040c0002000c0420215591802030101a00d41041000c4145000f034031764041c0500e4410380030300600c1d103e0044007035481403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 314023920 1250 314022670 314022673
    0x3020a120b09131a2403160b160f03050403020a0e0702070909030201180c06030e011e0b0d0605040f0c060503090d1824030507021c0c06090605090c04061e0306110903030a090602 78
    0x20800c4d13406c0c1079035981000300881400a0202d01400010051405004212050300445000c40000d4486005002c40c0441c2a00010740c001001c0c003d60400802450040010400042080c0741601d0000d4951140b40145094030761500f1044050501c00d402c003103c80da40d0600c0b0b00d11401d0841c5448500f0700c3c554850b507800710781060000f03040c948040c400c0781d150283c04100b04904112408c0004001c01d012081598060030351940100440c0390b83c49041d124a202d0444118403003120f080660411302c0c0360b0f110204020040040043c2c80b000811500398804071800c08810000c08514071416444080d0000d466002c100642840c9444903d03a040c04000143d440801030380e114080e0498131013600842814007145904221001c03e07105184180ba00e901501d00090407880580d148000c5d03e80546032403046d50302800d8130218a2425110382d200501c0c4103000745a04181003807496007903101d140300107005207a4034070311103041d406880c040320350018004086c4d81c3c0e078121303883c00034240a10034014070006 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 314025170 1250 314023920 314023981
    0xf040e07030609020a02010e100204031a0705130609031e030f120f0c02030304060f0c080c13090e0a020a050a0609050910121406060f011d030709020a03020a120b09131a 74
    0x40527004e02c22603059941001800c030050204000c01a2407480141000003004020481ca04081400142c004042c003019030356410400d00e181060420b6048481c1c2c44041d200c450190b207000283c000c00c02e4402600c103810481a074210244180004103414502000030f5804d2107214070f540c690100040d4401c5205030420003e8004e003c19900484180a000300003080c80c00d4040b49805100002421442125444180005407500701006c20354003440300101c041d41c004000503045150504400b0f02520041e40c2c0c9011092034008000c1401d8228132955020340c0b0420301080c00d243c040c0c003541014000400f000d02c0c01508600d444104180d503950400700c14000d410210f204c5107031480c03000180c90b1050b960214465030001180b40d0b038030000000590706110740d200004044070a400981b40201d03190701c0043c1c80758107202c030140122128801c0c1c010440d1600841c1c0344941d5540d0242d43e044003030035480c10701c450428a0095032000302c03480300d840c206a184041002004500c1e100680c1102d004052628 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 314026420 1250 314025170 314025193
    0x12010b04080607111c0917120307120207020901030b01030215030f0f0711061602012a0c0519080a03060608040b010501081b031509010503030f040e07030609020a02010e 74
    0x205010350301603902075801c07400c0030502040c803030541d003070050755003c06a80903031042810400002010100b41008261004420856060654003c1c039020f00724602800e40e0102503041c0528070300c40100362034180107005102d0703030040c0181d0341030b50b564507406400c521655840341008130443c4c00902c8102d120314040c1201c0d0ba07440d40307898142c0b40680040c2917465440e860718101c417200002d0051204041141481000801803c2001070714001e00d40b070303030100e200100000002820f48441c8894900c0030503540c1d0015460040801680641c0071042c0b50100101c070341458003a040c004500202e0103288c40e560542820720111100a05034403019440402c0200c0d500c0e88107035412003040b03401501846040d001080594080d00e2425400f801d10004c40c960901c1e4480c02010540050b90b000181c00078111411200c0e0600c0d00301075002d003130304900443c10041c030800003240911503802140c0301008160f0115500900907000301004e404031880640d110b0680da00024000c0104041101152254200410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 314027670 1250 314026420 314026439
    0xa0807030309141201090b040302010b010c05030702060307051c0b1311090d060b0301021309050912030a021303020a09050f0c0423121e07050105040e0a051b0c031201 73
    0x1411a58180c4840060902c1c003c0040c01d0b0307426840c5415000034000c060b40000d00421310815407868030507800700f04641400d0800a003120481c0c8039590500c04540c843c2c4e00450400000c0d1140e4039812a205541d0759200c10084a05024181da09180c005081600300d0242c0c4c1580c000c0c4600c00d2003500d01464000381c540398070f401d6854006081d5000c210810a00b81c0a040c855084c05c3c0c2c460145201084010051000c282203034404008030700d10b101c003450300303110620440c00340765004990080208051074088000356258440605038000301070f03000540110080450510a0055800a100c0c1400c80d030b8500405d40640b80c01c5400c0103403015400c2c0007814a9001c4829541510200310005a2007030f654046801c40155004015030700582640f80d801c10450100203555009006980c15a10640105c40075450540c1d26001039040c42020720007403110118030001164000200400443c1c2500d4501c0e08041401c41c540c000d42c44803500040d400d02644000004101101c0440c03211000c1d03a0380d40c010712 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 314028776 1106 314027670 314027683
    0x100c06090804120c0f060e010f0c0b070801180c0f03020904090b091501091e0c0507051c0207060c050a0f140607170a090b0115020a1407050a08 63
    0x143c1c200210034220800810031030400400e82030620748060505805420107604110300850440b0380d01d4442c0144144071a0021600c16035400c00550081103540240254200100410020300312403c1c107100b4106940c510b542c40d840c06082454044029500071504554055120420b41d404107004c3c074a458022007000000b0032946902004031030015005902502915103080801041c1e034407204868103d0303541d03c20002601c1812204103403164021140c000e083c5218510340ea1800d800b111800c071814120300e4003240c600c40d07521075040764005800000104030f13801c54031710000012030f40204203808610540e4003000c2d800d03019012614100301252400f00207502c007403155010144205050b80c02c0324603c44280f186207031a40311114030400c10b2040c0010840c1082c50141c40302d2013800b03000c40040c0e0210810b54030101182a0564515440c01800d03c150254400000c0d08800002d20 = true := by decide +kernel

theorem cover : BRFrame.Cov 313848920 314028776 := by
  have h0 := BRFrame.cov_init 313848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 313848920 ≤ n) (h2 : n < 314028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
