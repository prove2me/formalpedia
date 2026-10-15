-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:34:26.656981+00:00
-- url     : https://prove2.me/submissions/e77917e2-9610-40d4-8921-5d3efa281821

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 737769784 ≤ n < 737949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 737771034 1250 737769784 737769787
    0x70b040f050c100c0605010f150c05030906040e0702070e060a15110d030f150605071b120308010e18061b0c010e0d110d0f05030a020904060e1608042303 67
    0x700c20001d00e81e2886515084002007610301d104d0100403091240c14050329a072200c1043e41d900c3d24050f11176203031449847c1010424110a00000c00c6001c0040e81e00058004190075211034441c6510810142d040381e42600511450030b00042c08404003520301d001e01c60103800030104900b011803201e0310104852140c020072070710218140849500f0b22809a981e141f0b55008074007500440e481074191680c0c040355034040300746010200304c030a4111003201c0e0101d620103203000d5401040c01201124182035482014a170000c9210a000c2540c000c80a50580e411649d6161040d254181405a420303444044503000b42c0c090004164540318061090030f07000185035856103000860b001c59401d503001001c5080e0503521140c211841580c004a0000c0000e04d0300c8020b00358480a0b101c01008030382c0303424440081c4034000011400f54080e60f011600909000b810500c2481e5486503100f41c0900b0840d80030060f40d42d6640f8884106216442c40c90207160001c095441504620980a15884074800740810303d200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 737772284 1250 737771034 737771053
    0x180a050607020c04150f0e0c1603050a030f1e0509010207021e0a052202070c03061401030b0c0c1c03021b1606030209010c03030b0a050612011703070b040f05 69
    0x3003105912031011907000e0714820105200b4842030b00c40c040300f190a10030b0f039060248404440003400e1021207140084e02c1a2548401010b40d2003072203003000840c0012100345200c0207054001c8001d280e01000d5035420401410504604000c44454050315001403580d17203487c0741426020b800140d0020242000180f400365284d0000e00c442e40b01600c072150300d80c034903e0310780d10310304d045a503a800521007070386d40b818210b00c0d120007040d034692205040da45c0950b02090410601c402080c1400c0031310303030082e8104411600c040d2a0001c91009110031214003071103000244c0c0c1141ca110644560030110001003075804c6000d1040e00c41c50030700d000c4100401d80d0078015003003103e1482001d0300c130040820b03010300174008034209200c66600f0260044014540100203185080e64080e0400407001e03090300e0000341c001000d00c00074000c1d000e42e074001c0b90701c62008508401440001d404250480d0f00700d460552884510140290b10b0f03010300761020300728008482c0081d010034400c000d2048403e114a041e15101a07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 737773534 1250 737772284 737772293
    0x15091003230115080f0714040302040504030e090c0f04050f0f0604030f03020c0105070c0e090a0606091d121b10051509060a0f050d0c0b04060f08011d180a 68
    0x407485080416032081c0c200108110295890981248009490400058030341410704810f15000900507200304459150300301c000720140c2d400d59001d941c0c001c205008504003418001e09800504040900c1541b204010a406010041c01c881000307030020443ea06185c40d02c0200110011540b1020741c224145040100b015a43c03d0010001745102c0d04481c14040c0b00c0c2e04000307203004882c0700c103241404402c0014101003000d030003000d0126480302041d400c581d580e58580c5403c1001d40080100243e0401c0404070316501c00d078021084051490f1a8024200441048542e07a0080c8851100590074104500c050f540d03180416100f091207800100c402c1c0480e40c548400884404485102103040000e403034030290b113082800c1980207a01121510344250604215004c0f84143e4800d40b81302d1042c0d143c9441c10010280740100c001c28141000b0b5480d41c0d1f0710000030b40f080c4156040344001400100c000300307200d400f81c10302d0f150824103042944490307610740d900d404540d01d41400300c1159110302200307003002a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 737774784 1250 737773534 737773571
    0x8100e060601020d122f19050909040b060409052a0103021207030504080403120806010e0d03090b03060102070915080601150906050a0909020d09050705010c0b163b15091003 76
    0x101401c035201c0740d847c0d04809242c40003908840605080200c2001104107681d2044100c07034129411200090b4551a240c00090050003118402071a0780201d440358411045000c009401151000007803280d101c55800044089214150b00b03a600d2641d250040303101184242d002550180c410301c281403815449881d4000305d18680c103010000200c0d02d02c01c00040d0351f0f101c84960503081c0c00741c0340310b5100701c40d688e00900f803440765004159007620044000743c01eaa02c20083c910003010759240800050b01000724038160f899140c040c1c00000e11400c0300008107144240031420400305540d803880000c40c10f220088441d54040501841003010500002c41c400003284002c1441c8641c0060004045e41d03149007060820509a1040d03051110004802d4040303100488829813041d04880c06030300d010150303001039412174111319512801207420a51b2a903105811a43c40c2c10303420848096900c6c802c0c0e4807080000010100589078013155090080510a007040d03044070354908418140400e10103514901030421 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 737776034 1250 737774784 737774861
    0x6090c030804140112061d10270b0102070518042108070e1014030a0f02030c0d06050d02211e01090b1012081308100e060601020d12 58
    0x343c1c10700240300031056802480b00c0710702e05546001401800d290800c20325401d000c00c0308102000da00d240000340d6048842c6d0000d009400682445c010a69800c20105005195a1040400e4903c0c1c2046000d0381d42c0001000e204891000b4083e00240450310f2048011180181003201d80f010010680319100810301c02c3c08000315002d90302c0091034a0320034001000c43d001c02d00160300030054402c1d04681d440c2d122441d444003074402c0704140d81e40e45481400c01d0062000e604c50480c064404400e11980302c41000007008920ba4440040c00074540702c078100507a1030103008000754042070032005040007030745d0151260039180d05003068a107000d0b0200402e00e14400415294800c0341d40d90f140003020403484c0300d02c080d08020041909800c2074140035400304a824200c2b005402980c2c0802c800d02180d080c80482d101a001c0c10090340ca00d4000840c80c60040c2c01c02c5401111140070b084000b501c3ca503c0004c007000d0002c00d035540d510315501c603880194014480c0601c0000d074840143d0301d00c1d540c2c05500801109 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 737777284 1250 737776034 737776049
    0xc0f0507061110060303122004030b040209160207050d03170108060a0c140f09190f0e060d0b0403030b041113081c02030418090b0f0615070201080406090c030804 71
    0x42e0065074071039903818101402d04030001185011428070104e5440020b09400240b06440000c203104546c06a0491490060700e00103512400500441003008044c1200d015a20a4a80902c1034480302a188042e03210508020300591003580e04010500d04980c03010b4032140241080b400a01004c130201c602c81409030015a0664402001c3c003506401c280f15800c07d48002d49400c600c0c0c0e001c0d40b01550707014455010380b02041c01000ca41015584c0d191200981039034a00c1986440885e0313034100c1e911024080d44210755030340717002500050140c14a80303520418141d111035154013542d02da940581c020200255100d03041a55035421405880c1c07058014030b81d807002c05a14010191030060342600d41442541c01c05c40001181e01003681040e000030685042d1113244074010008109003200384010104500064030601c0000d06105c08100d280b03c503103000d9041500d40e031401040840c0c1611061041400c000d000030391030b00014020440d654030011206115201490803a6900d40300d402d43c9402a411154 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 737778534 1250 737777284 737777297
    0x160611160318140d0507081902040c030515040905120a05090406051206010b03041b0311090603060615070809040504080a02010e060403120b03011b0201020405030c1f0c0f050706 78
    0x2000e150700240700e803204642c81407100000500341001c0850058070341070740c80e018108000d0a9810000d09104a0001c2c0090404032180502c200d50f10300c540c085021300036030046103400c0780800c40600c00d005052007100c00d0041010000524800c2c04000c0c150f040301555036005113940015035141c0c2c01c0050041c1c01c6a41d071400c0d10b42c070906080104592040e4481072080007810584114401c020980d42e04544412078425102e035200d05014a0000c55442c206604814211001c0100880c64844400398001542c03080101d585202c00d01da5245001d856281c0d001e1021003030344801c91030110083c030019101ea40824140780d40d80d0041000e4038030580d030446801e4400300b905002c07168240b04d8400b101c0c100078010812400c107074902410303d81041591212441c1c80300d500700000c0e00c0035001030040018004054010401c01e8038020b000b5000f034021240300b0f01030002400c3e1613141c83d074507984800c01103060404020182c841c055880c009181780881c0e0b00500505ca02002c240180003502c0145150f850f20b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 737779784 1250 737778534 737778577
    0x7021216030b060406050f061c050f010810060806060d0309360b220b130c030c02010e3003040b011401080f0402040e0f010504110103061505160611 65
    0x60010001c01094140a20b117420700400c02030741c0e440c106841e50070041d9001c035907407400e4505000104400000300300f2054100018405802144031401c0e04940340701d82920040340c0300183c250181c443c02d00c104110f5a1000000c10454034200c8544400d0a2003400c0c424040c40d55400d85025202281040c1c7d4580b0942c1f00c0d21001c041e04200003100342e140852420040c8a001c10001a6610b10101241846c101d002022000b523094079402040c400100429262101d500c1420f1940035290b03140c3d0450009080a0415925500502445030a0400900030b481104202c24410711001582c8103000c0c07444000b02040090301c0c2c0d0174002140107a00820314506198100030213402c0e40516010094100182d090812070199417021100e9005a411a004103c031003462003a60b25101c03003210f0303105455281006010400131040d06140c54013200b80c07818810160344a40005141c0b41c1c2d01c038910302086007004000e4134404096250020513120304400202d11140507400310f810f40040181e201403101c2c01990 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 737781034 1250 737779784 737779793
    0x301060e0f061c03022107050105130203010e070b0d020d0209190305060c04060806041523091b1209100609020307090506090609060309030f0a020a030905090f06060702121603 77
    0x2100301440031a0100c072a00760084d43d00944c1c50410728400450000703041c4451030070b180503804854110f03400100901c2a4100800b0030074551607050000c922a40c0307859252510103801040c0d003000c4581200e4458200300e06914290060b600494800055070313401c1011480e680c0d20003044402c040b5141104002c82800c4d4580140303031101c0500528103100c814002045a10303400a0030f15803050b411345000c9003240a0a016048111030790704001c01000e50592000261040904401003605040764040c10b15161005c5401c0b0b5151001a1410840c01c00c002e0041041c108101c0940c001340a2001c440c00b0002d03a409040441d0821380040d198540c0001c240054036a22642d0540604003c407581171070080d4050000d1100c1c802c180c0b1180c02102c000c4005800a4010b109030b4196860754500b4607035170250210000d44405030343c1400c401240503d200403c1c541000e0380b900f482022160390701c610740d45802007045000e40007a42c040741d2001c40c40000d001a07580038040240042855201d8400b4a410b5142 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 737782284 1250 737781034 737781049
    0xb13060201140a09020103060305030f120a06030201021518060c0415080c0d09020d060603140f030c0601121103100f060b0702030a080913060b03010914070207050f0301060e0f06 78
    0x900031a03041c20300200030002d0b1609402c1d007081c0e24603000a0410b50303e100580207007503242d10140841c0000b051000b0030121130710003448103815003802a10180e81e07070342e9034404696407400f010b1f0044e4080c1e0700109802400c07180140c0c0214482e4169603201201c030203802e182c00da003142d410070110b10128040190390344a41c04c041e107112990900c1c810501e0035545d85940390203044403000d0800c2d00c1c3c000c1203080d911902d940300000ca070401c10034003806849043c11440d13100410906c040521131000da0343e40c1001c02005070340c16200c02c6400341c11242d1070034035903000421461b60301b52661f920441881103203503020000c1d41c1d0060f2480b040440c01441030300d0758404882180d4442804004104030f0348006a8010500c0c03045036604c480d1032502c44500a0124503281568140c040c401d918255002c10807040640295040394402d0005000c14050104a8020408180c0e0315001603842910706000500e0441e103900300c03009000e0000a405903841c11040312020060340c0710003080c0410010701c1300f1030503c180d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 737783534 1250 737782284 737782289
    0xa09051510020f060c0a090b03090a020a0527070311130812090105071506051519050403020d0611192006090d081e0906070e04060b120a02130b13 64
    0x2400f000e450709003c06445010044c490810202e002400503001d41c000e06050b000b6250005a0513202c1c47d05001450760741c40401026403041a2070440011145042c004150f4000b0f510a0a03002c3c55092880c4480546006403050741815124402c4101d0041803101525803008104844580249015002c904081c40c0c4144140324045c20050340d8881d0342c2020844030030a5000000e000000385001c0d00d000104441e03001558040d010400d224802142c030030140003615002820345406030807408082d242840b9030301c40250404903c400c6600824520b074011003000d0403481420345484040a8000d008600e010459004103d501e01b01900d18481500304088611a07a8004c1000d4140f0b6180725550b45410403110301005006d100080c0940d4503c1d011360210251601d1104282c14449183e0b51102000c1740d203100000d00c40c0580007910704d400d00034031040350451a0a1032904013170b103420440c2c5403402480014095000c0003079000d42e0641020302802407205140407134070703001c0307130f682c1c1c03a841000c41d0307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 737784784 1250 737783534 737783537
    0x60b040b0609060f03100b130e010b0910050c1f0617010504031b030c1a06040c0935070e04021302130b07062c0c04110f090a09051510 59
    0x1c2c0844001ea032543e008850580c0902401c1c6602c981d00c01e0f40381c1c2181c201076000b440c040e08020800c51503410b90441501c4c107640b04002d0102c05680c03141c0b2018618024086116440700600002c484440e01480040814103169001e490b0f0000c185c0810b1100d02105a0b041625250360340001c100a40c03800034180c50940c0c80390024002814103880c000d00fa640f403088410051a003000c00242018050004040c40c203901001e08421241400000f21080c442111454011414040c41003d00703482041c1400980d105810b4610b21011490361082034180301074030214502200c04001d10104108101e004020569004206520310381403060203a00b074442c2069101c01c03030040c0302e0114008090b140038001d440c0e28268190b10780060303081c4030018001d02802506080d0003201510889001e00b00b4005003052000b04462043e03032464180011940d0a41d4500c800b0f980500101040840c401d004000751100103260b00083d6031503c10b03503c01c5034800d464910011800c42e0626042d402e100c4c0d2002e00205d080d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 737786034 1250 737784784 737784787
    0xe0409141018020f01091805010603061d180a080d02030103051207050a02040f0f0c090305120c0601091d12070303060b04081b01020f07030c030b0903090109150504030609060b040b06 80
    0x2c10381501205629884002d20440502281076001d0b4400c06003840100a000d03a081038040559004e0710013400d0070b0140c00006810080c020450659802300483d450001c4080c078140380d55000c4d0700000403e034a07840d0070a0740c0500555000405c541c400581000c03010300c0b1005030399514603c1c10903d480d1858034030211907441400359030041000407441c4034039990140e40204e50b144207850040e000700042c0c020300728014941201c00380f007150b11104540c02e0340d12410840303a00c090500c81c0b45803039009811400d075103540030768014882000386400c6001964818207120b8041280000e000e0708012040d180300641c0c00c00480e11005156150088800410250390814135040c1005407442d224080480b1514110140e2580f010b282d03482049000d092034076130340036140110340368136010031185401d220948200f03c250000c52400754001c011107004000586408250515201c0142180302c5041d103498140502400000046021801048115071080a000403800000c6080004541d98409054040c840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 737787284 1250 737786034 737786051
    0x150a0c09180906020412020906030613060b0315041b0609030c0b090109170f0114071704030c08030a0f1a0303041809140309011227030e04091410 64
    0x30080c159406aa004040c52803040c4600644180a090040d000500280c800240015648500441820150700c220f40031707a49074030b5103410180c1d190380968200312104981145000000c00c20b901c241e19402002c2c1c103a81c8910768000b0b5024109004030742c141c43d00911416078070f0311001b0a48402000e000207040c04203000341103840b01246031070f80340900740e50400b0005410146a02a030403400041103080c10f002c0b03580140310741c2d0b5501c131403151b40c0d6485a076003840c2d0701c420003020341001117120700e145588100c80c020801a05506a240260080d0140100c03241e548c004140e4a80c01184035029912010aa0b070031001c1c1804121205145132003141191078440001aa4011003101c040b0703500c80182c100d4442d01058100000c05d90b020740180081c1d10741c401800c820703201001034043e44200344c0f0307040680d804c468000d405803044000c0381e04c0c1c0c02011001c83c25204010040c00401c0d20302a10300818500515400b00e02126424881664030b072809005004101d0400c005400d1a42d1121200344a15039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 737788534 1250 737787284 737787287
    0xe070e2106152e1209081218160f2702030703020c06040f0c050a0e010b0a050d1404020306161407020117010e0402031e0d0e0307051002150a0c 63
    0x1009418405840500c503044101999080001035808141c0040e050b14100e000c2102c51448540100c460081106a080c0c00c0407101e42d031017034070078403500403590174505110300d0605803070341d00c000f85001400301c1ca00780102a203440130801c04078010110110078103150304006540700c119206c1c1e8043c00f901d9034a030000d50b00402510082c000e60410b00e5030050b032a912a00001c1d0042d000302e12184d003007031141d0404c020a00100241c03001f14180102840042146c4481c03c3c05945a007034022403880c90b440c140108a1901c1c0c2c1001440a50b209180c05420b020121681006681e241481d40303104044000901c004d610b002e1110a40228000842c0c9040c040c5a00024003460001003d1403c01712020a00d2010359000c0c144c98500080c0c0310048480c0c0d0340c1c503881c0c484014a801d540c140e01a2080c80c060903401d032601c1c40d0440c4000951030041c4110070045004450810b014402580c15000ea8000000d00b922221544c12800ca45138000e0408449001d4000a100b6001050074000d182009440b80805 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 737789784 1250 737788534 737788543
    0x1503070215250e0a080a020603070f090902210a0c0c02060706090c060f021203010302010804290910200301180e0a060b030c03010b011d01090e070e21 66
    0x6401007044000e9915074001500140140920407a001001840c461209522100740c07403040c841100c00e402241d84500540c0d54451035070350000d402c020200081344800340200181080044249800c1076980d0b01e4a9441099030403811460703483c800011401d072a00300b10b0601a40e0311040e6070404200321415824002c00c00c080c8040b020780100c0d4002260b609100d03060308034501c41d640003020511a0b55075200020130480300001c0603c0103004508000d0402100c6008882c12682c0503943c07405d1a031603548502030340107980c0c0c0210180c8882240e507200d0341c00303e458083d44240d01d00f001410700702008540c001c0a80e07910054941007030840103001400e03604140203403419144e92544000241c10703842c441600829020b0b04201852240c02c2402003000b4040d00b041210040603000d803000320150300245404d030f40c2c64140c4075001c40c48401f01c1002c030700703e1301e4018110014141b510344206aa1210a840c004105070740b8400020100511a0034500703080f0ba041402503801198421001c2e1922070040d207a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 737791034 1250 737789784 737789803
    0x803010b0903030d06032102070b181f080114041b1b050f060a1407090510180b090306010e0403020c060901090b0a171006021203130803010902070215030702 69
    0x58900c0498504032684007001902c0380b000703109a08010302c80d100d05001c50103820024581c4010b81b00300140144051000c100d00084812952140b4241207564400150401c1070110303003034000090f100400c1c1400031240c9041c00e01c801c1d50300c031240154101110b070f4900c00210000e46000350704042c1c08114031040e041407076015442c1490704141006c4106100c514800f220f81e40586144034a902c250800400882d8190180c0c1560f40100501194154250701404007100d4402c041002c800041105050260503203c4008240c50035254042c02414128944034035604680c0802d04003040d400e41e01d007400c01030b580c003518001400e15054a02554008e40e900c00e0350316410b001d041c0114082007503074061110a0090b0031210032094039403d1201000b8060203030715941d0032004040c4030210f2441407082d4050b109840c010f40c050f151b041050100542c6950000d40741c20001c80d0200110303004a202c81010718081c2041960240c2e581c1401d004100701000081d4421000e07003400c10500180c181c000419191 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 737792284 1250 737791034 737791049
    0x140106020c011e03090f03030623030d0f090f14040b0402071713150507060c0e0f2b050706081f150210110c06010b0a0c03050c030706140702010c0c080301 68
    0xf504200c90004802804086100812800d402120802056016000b480581d0303000c0c01c00d2200314a80f24007820941c0003810082ea05504072604660b4000d20aa40d08101403026040030070645aa070713200012100a40d901c0689019410078041d040b40c41d0034068a5400d0000301c03810b508018460729401800ca40740200d503d16808006084200d942d8001250002491051012448003c0314070001d4081c0c0d2001c001110541d10304406025a14040c401d406005071010704107150920003202071100f003500c940d4a041c00504001e200c1c0302003d40389043c1046080c441e9010b4242e00c0c1c41d0980c080d04c07800c40642503183e0150740c807400c0410803200007034072821280c880c0100c0040480300d01c41030781043c0e20490400b46580c100146441d9011032a0b000342120f0b46000c0803580e0503aa42e40c0180c0c140c0c0102c1e4405d00014003030344088000f01e07110345c0144c04101c001a0a4130324080705962004216004051032052003603400301000304a6030280310300d000d0420642000340710302c00b040d6220744091105008429 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 737793534 1250 737792284 737792327
    0xb030408031311060f0421030504090f0914031c02030c160327170c030615011e020114150d02010f030b04020309070503070b0f0403060902150d140106020c01 69
    0x42c18050440c2d1680c0c5030400207082e40d680c0ba45100704e4071595a10034040e4481304000c840003849864684000819100c0d01036031003030700340780c102486800a0212000c4480b03080d600d404424002c5403007010f032100c0707860b814ac00459564448402e00c9003646d190502449820b0f01c140104000a000d01d41140c40c414242010528044a0341c6010ba034907980358014541030ba04944200c2d460740000903400001d9404d0002c003009014140b10b05260b5034030903001c3d150f41640141e80418007604030b03002130030843d00c01414800c20600c48021180e2000084000305e0f00141c5d1900078040305898000c07030564021070407211286d003152402c0e020a89180300844001d0400003082500c1000301c1c030030f0b804a1070b00c4000030000c2d5607070304110b801241c1d641c900740142031090051100000d2000c031482c0446810f0301c2d4aa4445040c9403440d12000c004164425059070851075a102301900c003c0380340300820f4808220f01000402d4815484040c83c4460148c102c401175500c0309480d0040b0707a0b040004c4c2000c41d6460100c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 737794784 1250 737793534 737793571
    0x10e1b12150c04080d0206011412073303020a08130f120306080a1b08060f010b1c0f020d06050108011a03090304050406061211130b0304021906030b0a0b03040803 71
    0x80100c1e2040d1340c06403101c1e000b040c030008445a030124070141291003013405941c101101e6802c20480c8202d0b608940b90f42c2d40f104508002000c075059440306030522000311071b007000000000000e9003010804012000a0b1b001800b03030001c1d40c00c4048c0d6504060b8034034002c00e0b5083c9a81e070344445800000c9000e016038440e081e9a885071403080c1c00c01006008403609480800b4070902e081004038062010315a080b00d134605001c07581513000920144184801101994a40d2a0440740c1c00c00794045c0358a10020100800d003000a40101d015680c109000e038880140d44203e201c02c0201107810701d410041c10001c101004024401030382071500c2e10808001c90855503920307840c1003180341d840349901158000303092150028550740c02401841c042003a00c841480620b202641c0b400041c4640c0b65814500b0804400910004140001460703005102411009240d121184000100300b0349a004900086c2c0791200501a401e00414000040240314045070460610b507981402c01c5c08024121040c260904a51 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 737796034 1250 737794784 737794801
    0x3070b070c0c03140304081011160501060803030708192c01060e011d070f020d260405070f12020a0302221b1e09060305060f03010e1b1215 61
    0x260401941e0010f01840e10800040c4c0c25034590b04240b00e500c5d032a01a00042c842d40e20940e00402031600e0f25090418a0510060791600011111220680c0c0d551f5031000c021039400c1040008600403040c0e80c03641070851500ca980500040d0140441d0801d6a042521204050328550201c1d9824070541b0780c5071a8403184a20003d00502c1c00b5406191021440400010503603a1002e500c84410940481c03c10309586111056510265081220780140d00c0410b107441c08500c00c03101042c0b503a1201110303401c65101d1301000d01d0325400550302031310a134100c6102040300001044a000080140071307100507254103103400140038030002d0b1001a02418000da048900c0c0f000301e035600025013180310f5041100342e0f5a44042e0f04c0300e805d00c1400c640414898204401f848421a40d0744003101180d5440ca24041c2c20042c2c11400340c0b00c06094030350083c0c8401950900760f5402c1c000c84a00035490030082100380143c001c0c249244654400d81c3d8040c495018040e0048c1e00086003a110425402344183c4180d01c82044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 737797284 1250 737796034 737796053
    0x60906130212070206010e07120c0e090a060611010603170c0f0a030e01080f01270204091a100503040c0b0c030702061909080111091c0807030906090803070b070c 71
    0x2200c09a4610010b03500216034820740905015514aa080f5645603884441d100a441021340700d180103d03040c44159146818140c001000c00038161415842e54072211003c910025401d49600d40c01c640c460009220082c0d000303105d00c2d540c40c0301c40b000340b100a1070b54507804400c02e8141e220454889001485c021080000c00012000200c64403c4460321641800c0040c1b06c0b80710801200c0c00075840102080e1203681d0607004038140c1e0f4800c9008000a01c1009174440100150100361000c29000c0c0000110100d140c451101c044030b10017560b100c90656801084040100d00002c1400e00c90280148000308502d1400102a40c052501059540441801891031030140c01402584020001400d2100209402d4101c1c0401c2154840515194403030600c10301f070380c8004400c4924480e042c840c3c0e08180c80e064060380d011246140c101040215a51100e00c90b1344e1104009a002c40c2c260513080254560000420300104030007030146080c0030b401d640f2002045d0740689403804100da0f106081040c03100342003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 737798534 1250 737797284 737797309
    0x316050a032d0c0918080a0e2b0314030705040e040602090a170f0d08070e0109121208091207061109030d02010b041401080601030f05070906060810080102070209060906 74
    0x40b1011a8000340360051840d14503001c0e0200f0f00d402c0002507040c003090b0444410019511100c00c1d42026a1400111000e89401c60f034164008144402c800c5000c6000b0720664040c44c01c0502c0419055035410080d046c2d0103002d541c5002d540d02001080303201540103081e94195000058004165192400c001020380070340c3c0c40790b96000c220490005096000340049800d160781300400e03205401c1c00300010300c0d128001030710400d01060007800011541441100341045210050400e4010f442d16a65044507000b10b011084070b007d50003042d08000103400c006e00603800700c505001040510000c180300c409900400d01c00a01d10b40d00e4403804110764211100751150114042c003142e0880201640090103480800c988074021450710145000720980b40740114107844c000402040e0f80d901c0e640d030b43e8249004a100c10b443d0740c000c040c000302e0038801a01684000b03000355910042c5900b07041110f0090b4080c1c0740d20049403a03104000314001a11100401580304500f00c89001e400d80d42c4001003546601541e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 737799784 1250 737798534 737798603
    0x3020f0303070e040e0a0f02041e091103070807120305030a1d070504050a0911090a02160f03020d110d080601020c1203030f01080d080a0c030b0409050a020316050a03 73
    0x8010040d0150344080003001d050b10480d0240708a1740030500b419141c5041e40f502800820f12074074801e0160a0a400040c2040c411003102001e0b6018200740c00100c945000d001c45100b041000048000e00c1d00b0032558002c2e0498002a06203d40fa0540003101d40341c0c0101c000301032100c00320000e07501d8401684000c0180c0703100404200401101d4400f07940b10f0380c690051901c9240781c800030445000d0144200d00400d544400c135035039a610107800f0000c80010003451802069020000300d145c66a0081002c04424854501c428800400c0e00c1e001c1d0824155148460400404000f00c02c45010001411003090300f680c185581c01d0717140c3e500100e00f443d000a4445412414036024032000210020046220340b1801e105100e09036202c0c10301c0342e100c248149510001645a2000c5115080981c0c40488480c0250400244024082001c01d0039030750919410366094100710081415810309102e4030000102491403080146d040500252010400d40800343c8407a54070141464010f1441d40480003c5441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 737801034 1250 737799784 737799787
    0x30506030a0b0a020c0d020c060a050c011d150903070c140a03051c09050301090c0e1905100303030f141501020f06010b09150a0906110307140d1b05030307080403020f03 74
    0x3c440380c10701039401070041d1407541c41443c01d0703128820702c0400c461040441c0144900d2a020f1154030889039600300f00d104030450755a40c10b8031020f480080c2210a005c1030ba20024148610415075000b400d00c000a0400f840d5030810005c07500000c0070101003001343c41c104c02c1c41c10003d9103010301183e0030f6521038000820724403401c03803200c040e0039050780342d800d0140707680c3d81e144030344d07034071001454240c0300008402403080f0000c1c0b4043c08000212800e4940c001d080701604081c0342e005101010960341c00b03942d200c600b41c6095009005269050107041c030b14440d80300781444846254407008103010380007800d110700b80308050905a0168424080c0e404142000320413190035503105d448072031156000c040010711800140c403150f059000e100b01039982425007034950540d00703413074041c0540d04041e608500340c200d0b010410120b400101210101d185100711240104000e84841802810009008440f02090100307401c12000084000049a61000c1c0515000f15243c56614083c0d1500741001c005c1c4055000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 737802284 1250 737801034 737801041
    0x1606090306092915180103060e0a061a0f06070b0c0a05090d0606060e01110727020c072c0402040b0102010e0706020c03101b030b0f04140108101b030506030a0b 70
    0x600d070712040c0a03508220605071103484481c100300d8517590400300701c409040d2060041002c100c155204000040003001a1030000e550b96840c02d084528032020713550038084c001c02202c000d0030212810320900d42c0c140c81d0729142103083c0c0c0b950380200800416103000b401c800106180c520b03105100b950174070300c0702030040b01c4c11030b00d80d1621801414050080d0000655143d2032005d29600c5509441c6400000c4006005100d062480013414103042e40b01d14001c5013544101000c0c0603060348010441d60201d64040c00d0602c0c14448a907030f101641c0d184010a0746100c0200d40e40c51030789980c041e40c00036811600007c40300c0f00c14006034098000074848600902a0810005c0d02503000f160b2988414012020360b100d000b250f5185600300c2d244050441c041c004002155400180a2390100b84003983c010004001e100212000805940108221b6110007042100421141c1010444c0c11003480b60761030240100031540d410f0711009454141e8503c1003507181d801081c40c548090112451094224820350b90914 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 737803534 1250 737802284 737802353
    0x90f060d0f021b03191b120203090a090204150516050d0906030f2009030a0c062f0a0803040f06090609051c0e060c01240503160609030609 61
    0x10040c041d041030707404031041c50080b103c1d40882210704043c00e55010485c9040e0406044411344003030000e030035040680341114804070f4030b042a40801d40c102d642c02140d59041080911080da69a50300c0010078a0060209100c4c004a42100b8007203085103281044c3c481030344005a0104001d1020003400c640600b40320140c603594400d00b0202643c081d17881c01d0000042c41703034502c41100c426107000c8035207171102d101c864552001c140c0101000c940090441e501d09903151102441035040e6444640401c000010800244d0100c5103145206400b903036200065403110580951194aa15401403c54200000040811842203d000d000e582c214008000d80805032030600020202082c1c103403003034403d031814a001521400ea050354140425503d0700324900d0601e0900c00c568002040300801035407540300003094a402c2800d0b8480ca5401c04403800c401c2403030700040c1424a007080300c402e5101612080e0a220054005000e40c04896004000080c5a19181880042c0b20303040d84040c003458aa1115803107852 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 737804784 1250 737803534 737803537
    0x1060f4d01050906150d03050a03020903060a0506012c0118030b15040b06070201090312033306110c0114070803040c090f091e0f02090108070906050a0803090f060d0f02 74
    0x110f44060031942240c81d896125221103d110304c1150344008101c40040000b8800d0020b800c012005040241c14480304400103030404104894200780140c0c1c1d0710801840e507a1041c840752083c07628020358041514046072110001030740280302da0510400c0801c01d50b52480a000000095410155440392404c20025000501d4030021842c0c3c031407410306510708018070b0113804403003989074140c40351080d10b49565550310400a00307400040600d5034551142c20004180c000c0c00c4400701950b00900c150b000f030903808202c40039080c0c10500800c80d0800310f100c110100002e071102007070b40908207d40500554030349800c280c404d088004100107004020300040007a1514800d05490190409000c0d00d2003800400d81181c0c01c10201400d143d040c811840c60413083d0a01200c0024054451a89020b6031500031031002030081e80302038080d601192040210803564850b22002d06802c44401146078a06902280c0d42e0203134144092095520b016400740ca42c1e907072000c840310b1a144071414001003032803100c0c0500a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 737806034 1250 737804784 737804791
    0x19021207030b150f131a0301020a030f180209010e06060415210c050423030708030c1b102d050705060903041a0a031404080301060f4d0105 61
    0x12482045070506450000200c2100c400003504240f01c0448201c1c840c07003e1304002034029814490746c0c1c52580e26490130b0000b000480038607200402d450920800240c00c4482c00150f807050140141c0c1180b00603030740c0780c0049044031407400d1014502d88810000035428804c1703a22182c407806440395a001901c0c0c0200028540b00f03c528441d01d0081000d10340d507010b4861a800c0346000820800080c400c441074208000b02c01c80301d084211003208481004646411440e030404001c1303038804100740f034400008000c40b0940e071125410040f10001003402055502c072410290074180f00880000d10065880340c044030780e00721880d1849840c0c1c2c15490714068480d81c0000703400c0e101400f440001950360b220010454003120410030460308030355024851a01d107074201e828800c08054541e080051100c01c0354000900076402040c00507682e5140080103030004c03602c030754502c0500c80c812408a40300c040140140c50040640c8141c0c40c8034800708010700000c01c000a88036040060410211801c902055115920 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 737807284 1250 737806034 737806051
    0x40318030c0314060702030405150403060221180c010e030f120a0f09080a0f0c03050601230108060d060506030c12060403171006030f02040e040f0201021e19021207030b 74
    0x304108210f0580341c46903012503901002d42c4c020082001107003466400c0c1410400081031403401c050301e99480744141d80c45001c15200541d48040c041174121016020141c101c440718011008a50480c198903031a03040584100341440b650281854440d1010703c0580c0040a450702030b290324401c3e01c00c51540036001450780d04009111503129003016401803008905807810280141840310032555001d240e240340d031000b106c0000c4003030310000c005402002034074060a0415441d800124031100320680b0142c066080504008100b41480500d4445504400d002900024040f50329650140030030b140c110314540c01030f003000403401500051900414102c1c0900d100b95107007500d070f2a03c00340c0062148015070303402407821400001080010f0203a80902c0c196040c034180941403a50710301681e00542d01c00c07038040c1c0395800c401342000110769050003c4100852404011b03880c030202184d4090f92035002441081c42e4408100301202595180714000300e9072244201110617664480c03614003600b0800f0360b8030340f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 737808534 1250 737807284 737807303
    0x30b060307030c03111f02010b040c030b0904020405060f0a1e15140c0c06030403030926160206070b090313050102060f0c030a090819090e0915040318030c03 69
    0x140103150205114084903003080f02c40c0030480c10350f2501c00d802e4011401c0300381d001502026140440700b041d08008202401500002803008520082c401903594080c461410549400b44550f4141d440c411218bc201c2d40682d030014440e40c69074003181401a1190855900c0300d000840011809054160306003100981c01d0b08491140d902c00202d00f54061404d241000301c0c2d00c60203850150900107010300341d980d02410031102c072800c0100104031f441d8001c1e42c042d40003a0b00d9201e464240803080707400c803016110f0401500d0442c000101d40100d94068101080c0c038000c5110001c4041d561040c05440c1185d801c40c0e10455a410011901344da00e500008841c003403681280000030b01980040740700c40c4a002c14401c1100d8550f81c11074071940c143c1c001001115816510072121021650f4400075003600c40500d200c0390b4008500e88406820302c130321680003609101100e0100300d5644004a051400442904140c0743c040d10380385820355503000b01e00304d4280300c40d144c200004217000404011a0440303003e000302a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 737809784 1250 737808534 737808541
    0x3121b090503070f06050a090509010e072601090c03020f180901080c0d03300c090b0708090d020d15061703180909150f0a0509071a031b0d06030b 64
    0x561903e020744a40c004030b440c0a4010460140100b00500c030700c03aa40e2504a0401c0d0702d401c0000c0b041c3d2420b810202030320707082c0c80800c015941c20040f010040075400b203860f00c6034451020b002e00c90324414040c0c08405070b1920319445815010390151002611521101074803014200d141010400c0d41c613150a1256083c18000220b1840114143d1142103010341034190700d0200e0384013601d0341036160410300c8808074015045508071041c00c0c45501d050f203140d640860b20f4100d090b00144070a005030008031105404221400005400d407017142d11540c0c054070034202c0020b040c000505489003199016103964205294180c0c040c0c1150301510581d8101450300c5500001701006650f64051901404004041541c0001c0d091414002081d4840c8102085480000b813000c0b15001424094442d000d480c1c040c031050040c241a58003d01e0362240c035500003003d03140d03d0318500012050b40c3c50150405100c1c00004114500300c0030502c012080300f01c2103000e0740c50170740088a600a1401d40f00c03c0d6035440c11320010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 737811034 1250 737809784 737809789
    0x4051c09080105090a031e141b060a090b06030f032208030a0f0f0f05030f040c0902070507140d0c140616050c2404030b0c1303030206150603190903121b0905 69
    0x1d001080480d952303410000002403204007000ea000200700524011304c501c010400f0070b01005228420b5842c060b010505008915019941c2d55018214034800e41006458030280607002007540e02548103c0400d05810504e0035003404200d980e5000290030b400b00042840d8001d81181d03403554906025984c41b00c8040e41d0550840ea0403490903030500002e03000f00049406c151070000c580343c04c940611400300380203075540c04d80000c0364441c3c04200c2d1640c201342001c002142d40c07500380c00d81c500010717038076102011026528180340c3e60700f038013584481605444c00144940c45031400d840c190030f0000b001502403038003030824550f0386d04030282c0603204081001551201c828080055148016000c035541d0800d41195585d0442c0302008129110700041071080c040b08042c1d00c08014001d6009401802541c00c0a401c070075520120803249500822040007844000f640442045040500d0100005616107032071900300e03911030351241c1140d0031604102d00044c0c0050a20540144421551101d01722142d46405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 737812284 1250 737811034 737811077
    0xa02040f06150f0921030e010201290a0e07050a121b030e1b030c011b06020f03090d030e03120613050115020c0d080f0f070f08090f0904051c09080105090a03 69
    0x301030140c80c1d51708038180000382c05800f190482c50340c14000816024ac034140780e40c1c489266050b121000c4d4460702c05044180c01c0016611024200a90b030200b094501803401038030314441c01804004000c49005a01030f540e0302e030f9011640131021085c40360300e0486480350080c050702110381900402e010f80400400c0b6074034000960b00540381c0240180c4907400b0b14000560355610b0814000052114008c81900000c50f00d10041041c041c84100150312802c09259983c0761003039048030807007410f26242008404c1e41000096030301104020180e4103003952a040491800c0c1d0203c480100d0141c208000460000a81d00940246240301e6080b01c101c81925006c0106420f410752018010310410020310030059800402007104c50360410310f807441c2102c2e51f5140b82626074814000d179070710340c8081081030181c5000c0c11020403200d400c450000340da007095101c040e240d181d29012031100c3c08601304000440c034000d404040040203640d000b00594035007604819151200c19000328000f55a4543c4003078517085911 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 737813534 1250 737812284 737812319
    0xf04080a03091401090302041a0402031f06050f0d050601090b070501091e0f080901140c011a0d1a06031c27060f080601020a021c0318080a02040f06150f09 68
    0x3500e00c020170b031658003484024981c03105881d8031004041c602c1c101035220390004501600041c82038001000c0061107291140e040d5810800c01c0044c10003032008030031401741c265030300524904000942629003a0041e158001c5a40c04800015000b04d0741d501400010f520031225a405010440c00c581d406d0400003464402c2c824009168070ba50404507804034800b1805030a0400044c10044a140c05401000f98180c002e80c0001c0c15a079103584e803500d1020a4013020298420050ba003103c251005981e502c94280c41204000300385100040010324240d504100304011521800c1c10007084440380c4800400b003087c4032007400b11242c8242c02d4030900d64a008400310451711140e4408000c1001d03c0011500c1100c0906524114850110740401580d14442245020b02c1c404900d9901105e445c6006490f0001015040118080c81e040c20002c3c0c142c089040f41c412035040302c00003942c850b0101310380700411541e00404640c241c0c1a04500040d5044240122040810b03282c406140d82d403440340c0c51008101e02c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 737814784 1250 737813534 737813537
    0x1a010503120d06030803090303150a12080a020703021504030b0609040305090111101506030b01111b0a090f0b011409030d050c010207050d03150801050603071205030f04080a03091401 80
    0xc01c01d4014000c600d400703444440407980003c40c002d07076280c46000c51034000b42c914580507000001846504d40054000c05817070328040d10540c10040c6060055140c810100601508600d80001e040c0b102a2084c8007031006150700078001d40300f87d41d002130100a84d400500040381d41d1441c030404a0442d1524018051103141d250355490b00c0d00d0328100046801049490f122812441444d5804010f03030a1405031482d038181c5d144180144610704440101990401c00c1068140000100040407100000ca0a803c242c50000703511006044c07014046031002180d540302c2100300e8a8050500d8104034107030080d0707400c007070300b44c0e60010040e40c4040348200c01c0c46400c98156055100c84980740c400c0b0301400c050301c0906400c8000604048440e1591f030700700707100000120300203030303503084200702c0c900142115002a121420081007a403401c000401d9580000780610008004138200c4401001750400488003034050400703410762619a5602c03103d03a01c00544d202180812003628010450302c04241620740b0f8200705 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 737816034 1250 737814784 737814793
    0x90c011106011a070816050a0c1409071404320a080c040f1d071e030308060d05030c030409051e25030f1e050f090303010317070c0902071a010503 64
    0x3c49036400c01c1075000080440300da2100340000c00c51001c490713000075000390142d40508012212482e001c1c6613010360f80c00c41007694001c0300ae824031946408c09070315404041d5051907080c088a4190080144c041d40d40103552590302d241c02c03da021030707001b1510171146124001400c11558081704000040183e8028003c00768000c0201014500d4aa003000c00c7c20303000c43c840000da2020040c0760a544100e203940c203201f90303401000208800307040100f0410030040c80c1d82d00f100e101c90565038000c06042010307021521803103420074180c3c00d0003410300440740d0345060801125503541d80e608190001d098121086240502965040d000c00d0000203405440b603480d00201039441880d0046405080100b510204c2c00c01d56605681e40c043c180314810082d005071518242100550351440b0f800507204002c0841c2803040c074100c2400341c925400030559064a80c40039800030340190880c0031005074004e6103005002d007101c1c9140010064841d6006206281c01100c07808018404103122000e881c0f020f208060f0190301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 737817284 1250 737816034 737816069
    0x4090e030306010212030a1d0a0c1505070f0c0801050f090c1504060c0318081b030d0806090c120c09010e030606100c11040e0d1223070215090c01110601 67
    0x11300c400035541f2003a400300000b0044e071440c58425107954000014006640202000014000082c200d02d00601109800215599541a00030074900035204001c0922105071400c4003004101003401000e8003504000700007901d46000f0303443c0001e03401c0c3d5040909000300c00f5541d42d23604010300c1c10000880039400d803034a0285801400c42c1d25007804d00c0142d042010072001c41039020b22080000001300b074040e0082030b800800c181c1c100e114108140b09a40300780d01c003c1d000c09055820000160b400641184c02d035203c0d0b9606940c0700c45900c90320740c82088969880082100354203802d0058240420282d81e40103d4040c10710a02d40d64003c19100c10b40d01600c00501448800d00c540c4c0000c825a1040350120545c40c0c0d07000205040c0c2d9500000180700344c10544e2602501d640c040d240e418032000c1d00d0000c0c01400044103a02000c060512105807422466000085406000700050002c001034610000350034075003000c0c140d40300c124507115240080c0100c1d103500c88150000030224140d407004804a0100c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 737818534 1250 737817284 737817313
    0x18030f040b0d0f090506060a0f151b050a0c030308010503030a0e040507030f060312080c03040b04031d090f010e070504080316020d021c020301060b030f0a0e0f0a0804090e0303060102 80
    0x700080b2808488944800c21015102c81600541071220f00c104000d140c141484010031041c41c8581d000001c03c803809100c1003140c0380c80c44640c480d032000306051400390800c20034070f6520000031200000d00709205a002d517030100003a650f1401b04507800382e502c0405a90302c8000309070b284d1107005101e50005040c0c0001c00c0c0c60345820340c0704075000001da00b80060b1800e43d101d591800d446c0698001e950042608022440300c07504207072420740c0030a460317404501d18a81542d4000c01490040c00c00340401070701800b0a98400b00c0f5141c0380e00701e40401040c0000514003000c080e0300300f4800b40250f001e10b010b414085a4800d0080c0c050745c00b5581e030780c8040c50034160341c8007171001d0703166840800383e900c0b40901103420050380f40c407a040b8134080340c0901110300300070b02401458203480644c1d01c070901340001001080b294503200500d8903000310341140040740c0804170001c100d140c818060740c3d450b09030003200200410080a80001c00446820030020301105ca400300703910751203010444040c1d0168000700f40503080d02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 737819784 1250 737818534 737818537
    0x2315062106010e040e031903110a0c081b030304060c0f090302060d020d0509060103110102060412080901060b0a0309020306060a0609050904060f050a022203032a0204020c0618030f040b 81
    0x2141031502109846007140060b06071441a410f401040d00700047c9000d0718050307080620403505680c01d040c42104800103010f181e0744075000c6032004004114088004201140b0100c94001d060010f41403950181c0420040d26540199003c0b94440d203440c0701c012001b4015014002e1032000c0341c032001c100f00d01d150280304065220246004000b40d00304104000510244180c2d0701600700c4400400c01c075030540c6080403282c0041d204050665200ba400c0000041c6400103c00c03070301c13443d4540280c0b2522454505800f600043e008820000d0000c03400f4000b55030700d507001c00307900360003101103c101d52144802d10050500901403203000030980101070102d804c00700e0340c80c0c2d0468420800043c042410603210703002c41d50191800c07181941c00190448500884120380c2c4007498900d2681203403940385907000b41c091400c0780c440c1c100c580d811401c116120442d40310038207075880e0050810343d503503402405c4041d110340003140c103107610702c0a000c400608070400101740c0704001c00043c1514a4642071842d4201503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 737821034 1250 737819784 737819791
    0xe091503060105010302091804111002160b0d0b03070816140904020f0315070f080f07230d1515092304090503160b2212020123150621 59
    0x7254101c0500390b2008416121b08d88154020385140c0c40300e01d08101044045412441980c045511002d0b10080100182c1030a00480d02d26445655440e02285915406440c64210007070b45402003410000e510b010105500442d150090040500e007078032009500414500c9102040d0013071040800500181401400480320394001001c03904d039240d156070307406a0f6401c2114000e0001300380030050007555070805411500460552200f40840c605034800502c41d40c582c0400349803c1510f80840407405001001b00d5407050001c03401801700d90030115094404001034032403041040019610f08018510801402003591102c083c1100c203100040854003000d503500002a50190ba02c400d400b0000b90104010014864940350302c0a40030090308004000e0b0000901c0c40b1142112500c1b1300c0721005d203550b1980003169000f908011301c2e000d00f5008a0041c07104210b0090610300c405040980c00f812180c42a2142489030f428134618424103040c0005070043c1d004c203d40c0150f00000c2c3c1c2d00d00030114124560b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 737822284 1250 737821034 737821039
    0x510030b040f1b03030c03030506010309112202040905011805011a0d06050405010e0a150b2b29060403030504051e060f0d0506030d2118030e09150306010501030209 72
    0x94806203c000c0c030300c9000d050340118049440d0f54000c104140d050300400f0781c01078090070100060b04294941d196071083d1003040e5882043c1c640e0000c103100705145903604030070350804400c645490300e403103495005001c20f014105602760b00600302c10112800f401964103a42ea10350f0650202c0c0c40100c3c19400c9900180d00380c0400c103072949804141c9407960b101d228001e011800c3c40c2015803c2815a1a08a03580e501c0b886000042d202014844980c02da001c84011414044a84022001508401040c0c082450154072102d0610401720607034207482e6000520f400b0050302443c0c11803254000c024641c41544002808540306100401561a0940b5034804131100340560f83c0d52440c3c2c160000c2c0c069803142c503482c070035158040b528503c0901c0070701c03641d0741c401d40039801050f444042c00c0300608124040070601880100b02a402c020300c204036040b00440c044852000c1c0686891458003134410318a490300c5030302650b5a40d0005211164030b40500911081c090042c105903400c140044020790b101e40c110b940c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 737823534 1250 737822284 737822303
    0x82109010c031b06060302040e013c150e0919060f0207020918010e0c0d0b07110601090212091605010e0103020f0c01020301080717100c091d0a0510030b040f 69
    0x3c80b91070f01d620410b1503042c0b00d030300005001802c5104100840754440c10400ea6070385403143c4202a0b0644040702e65251038000070b006240500441e40c8012550102d900015407800c000440710440540c01c0d4030800d4074176003000c628182e540c4548907995a18280b00030480300d1094050384002c200340368000100e02080c0c090141c608103254001c2244540c00f41c40030307509840c2818504100401c28402c40f00c00184413005043c2d8403c401e00003504c044802c01001d0145882c2c0310224200b24003503c80d01000c140400c0c1510740940e03603420420002e401103030841c141c01c00940006440301e14082032080f5903000a003030101d206401c240044420b5445800c0b400c0c1415401c00c1104081242c50015142c024042400980c4d00c0d0b051410107810034085030b1007030800510001c0c046c580c0d80710102d8487c060041389140022014201081183c5160003644000c5482c00540d403034002400f000e04145120360304185041c80103841700904200702d40f6040c4005041c00600c100400c3c001041c42c2c41e0078000341c1c0646400c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 737824784 1250 737823534 737823557
    0x140d0309120303290a060c02060d020903011d0109020109090e031209010b0a0305010603120c032a08070813080d0504030b0c090a1206050717070807031e06082109010c03 74
    0x180388900003008141c450104d100652603079181c0b400d4a40702409031490906001000765001c02c0030390042581e940c40ad2340d008501c14001e038800b5800a039030280640480c00740c1c0610001c0c0d1074020404440c003680010b41444010030720b00350301c2c010020042118002503181001d0405a0450020f015001b10525505c03000050019500c0303400080c00303035005100000f1564514074040d0f8450b800000e0070310030b00c90030481d08400f1941000a103146107040e1100e020359460b020138907000b19003480c1e03401442e003c80440d003c002d2240c40009020410201c9a40410042c0c42d0504030340e07540100c0c8003003c00140c1c00c000c20710014445100c550b0b081003603a402c0c0d0341403146100001d01e411210b81c01140c40071072072002d0001030180602416400002e81d0415513010649411441322503000209801c050100e80e801103480c02d4401c3d40040d028451134429201d48109044255020b4800b5105240040c801c2d0180501d2941c660200c6a0030270080f48819807500039080c0040d510a0344101040c0c05008085210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 737826034 1250 737824784 737824811
    0x71104021c09051608070603050907150513050603070e0f040b1c030e030601030503070515190225050304090b150702101701030501020a080711071e0503010e07140d0309120303 77
    0x2c21002c5e01c103000241c03d000782000340c010201c810040c82a211548899410004101701061f6094504454501159541140d010300807040e80658041a0881300002c100b11146601a25449032140101e440000088100040006071425420410341c8104040690b0f80c006524101c2e2115003442405c0100c0c580006000203410804243c1c03080c2e03a60b800000d20340081010034006d45160702150040d241080c10040e0318900004001400000380940c009440d0422481104421520317000b200d80d910410880c038500769450341c1061051035000c80c1410701038420b40c9009a00340424526841030281015116001c00c000c001400307070004180030381c00c4218195038081503090350107075020b1000503942d41407030700000340f903418002c040b5820090701001014000102180000854034162440507085109107040b5056400c2c84d48626499844e000ca06107024002103498022504603183c005182c3c951001400401001000002e0014482903802c1c00f800c0102c01c6004481c900074a00002c100d104c1080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 737827284 1250 737826034 737826073
    0x30c070e0901091a150a0f060f050c01090c21110405130b0a060806070c0203151b0a0c150608030a03021e0c0a210212090d1205071104021c0905 63
    0x100f213400150750040000c9510001400100010280d0f9800d40c07a610f400050b205030002130046008100b003240d41d40b814141328405550150201ca402046028064508071000c40c50324400c1c031810f0416194a40403003034025105104203a0041e203d03160b046d603604104001050014440d6400100085807034000c41c0b00c00d10040c1c0300d0324041c0000182c450800004d603203040e00042400c410000e10311308400060324041501c51080940c140307100c80310b48481c1e5480c0c9184400c03806142d00003e0106180c19800c0d48800321141450085500c0961849036004100640f04180610b4070154010000c1d048400d1082d0300903c1708400001506c5a82c8140a44000c03056200715094038159011590311b1042c040705202c10040c0303501d401c4404505205200000e5110742c82d84246c540c0788200810000b9040d01c441c060765000c1e9030322800b0070302898026100130303181c0c0d000501c0a44800441c40120402418640300700c40b4881e1503151143d00c102e000c180303640c000c1c0880d100f00316294020a02c01c0c1c81e41c3c60580c80c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 737828534 1250 737827284 737827313
    0xa0501030b0d12110f032104050a08030907061404080d081504050a0209040c030b010f030c051c150b130e0c07021009080f011b0806190b1b030c070e090109 68
    0x41e203d40d543c03404c01d19024688110000e5101c0340d600200302c00516500088203004e50b8480c11682a6165511030520604240c9146400303050340304008100941500c010402c1800c2c1ca01e640c540c0302c1d020702c07185540c00d503d0240c1e02440129901280403030030782c01d01840229034010b035115078026105900c0c50101e0180c40c4280ca0f4242e0450b00496008250728041c01041c3c1600014030301002800c045a00080c0014103080c403070414183e84102c2070140c1441902182c0c42d00140700040c1250300d070052a24070050402c0c4c80007038245c903c0a00041022609c09003110070310465020210001420039200480829018020703451810003040620010303201c3c0b100020210b046ca407a04480c02e171030a910740d414000e4420300c81c0012791600c2009880361410322030302c1034030741558500f081840c0c0c4d400c404100c05d00700303030141400310f001002c0000841c0e503010380007443c03000040480c0042d50b07901c44030026501e000d5000020b00da5005400305014021540032220f0703001d040c0200200d440c04664482089904810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 737829784 1250 737828534 737828537
    0x3180d05041409071d030307050609070501020708030301061d0f1806130e03190e1c0510090b1803160c0f050f100309290601090b0301050a0501030b0d12 67
    0x30400304404885000400c030142e0064a42d140d0515150400500c210480318041d416617200c40c80300c2d0700e1520100161142246e111044984908003a54a50b40e5008184034203070041c441e8541c0401c400b00c02105607412100c0a4403014111004018141c422101c4c80d114142c210b0014160b2034040e5444940c10200b0782c10a84503040c1d5801d1a01c141f28401d006400180700d40382c03d2000c03184581c84008111010004200000061090310f800202c40100030056150f80c040c1210a080b4210444c543c001e0f603461b03200310102d03104158001001d50030350308543c3d4054030550103040000d030b21031452014106500c00140030349103880d061003500c5908103203280083e01c42c0340b10144103000303160041c6000d4010301000c0768030310150310b111000504241c0b00b41808808058490b0400c0e02000041e01c000f2600f802c40c040c1184103112070907000d81d01881e04981c0c940c00660302c040c00243e40c061030803c0728180c0d8406004040441d08000055001d03000245e10550441075000364400429401101c001008100e03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 737831034 1250 737829784 737829787
    0x1215061e03180b04030f1b020f06130305030a17060a050d02010e03030c03091311031f080109030f0e040c020606010e030a0b010806090d0906050909280b1219020603180d05 75
    0x605000301851a40c3c01c002d02071210490341600c100c20803141c0d407201f91f54100c0e101411008107c000c11001d0284111740d80e000c56944202001300640400a001c04030020781d5803920b500d00ca1a5488c40c0e1000035502d298008021400c00c1c812810075442e0269164010f04000c01e003000e1010100c0e10310f5100c0c51205001d9040804c4494491412070a003940a58102d6414480751100c0f40f0031070024400500488501404603403040e054035041c1c07010800901200d0b00800150f0140e0038060102c0c0034003000d11740020401031a0341c1c802d00e0144100220180340754028101d941d1100019900f020b41145038540c540b00320104000010002400305c0e000c0d1035004080d00f66403d01d00782541c501046100d07590b051007107152082c020540e1040503215242c0040303c1240302a2110710503015040c84c03e070b00c4801c2010700ca00b5001d20401440c2c0120a288005035059100301c05003081d482c4e00d8424620f03420036842c1d00280003601502d001005903802c4400c0d480c428214003000b42c0683e290080700480903010460 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 737832284 1250 737831034 737831041
    0x20f0f0723030a150b120a0b16140a08070f03140708092a01170415020d1407030614042c15040c0801110a0804240c1215061e03180b 58
    0x213103508107140400c001b4005101c080380d65500d0030b03502e840c020287c1d00341e09094004100c5443c41030301411100d21404070300d01c1ea140a005001801d4040c102d8901c0041002d604000203014406d104040e914280c0c0c09400c2c0345501d5000048500e1480a000150039106451080300b41240480e041010722101007010030350520070718009092200c0442e25030071101030074000c01000c2a1400c2d950051414406001a6240000394550001303104554007940c5044403507003084002601640002b050301ca104071101018100b4008100130f407880c0000401d20a010700200c00d00203a0f541c181c030311101c01d52400f5030300702e4100181d081d5800b102c1114240c4011151040801810700213126006680c81c0c00039425103441d60f0000043c0c480440500010940c5078400c2a01c1c11540041a00c1b0285111903c0180480e0ba0303030140041402943d50400066680340c8880c0c0521100d10240d0982101c40b1612045198050500c261001041003d1010141621202c840064420303200c4040300c91845011203d20904 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 737833534 1250 737832284 737832289
    0x1f1218020f0f010c0f0222050603060a0e100207060f09030203190815010c02150408010c03150303090e04061506050a11011505041a0402040303020f0f0723030a150b 72
    0xd504018039010340c40010308000c0700d9a2148122401c15040000c032485c400d503e1012812601e0a400c40720410403180415404080321030700210b0140700c0450449103940c41d415081012140d1088807160280c0c0034101c0b1140b01d200540160910300c2c002d10700000c1040c080600401a11591714088005810000b0810060600c0400101da031500b1032912a8440c9041640c03503003440310342c0102c2c9041c003810301d48560841d0303650300d05100d449022a040b2500d80f59282e041038040c0c10f0100925010038201418003405800b0074040b02c040b20342650319070f08030300e240503414101d00c030019200707541458403903500660494102080e42c004160070783c1d51030790320306910700c0080400001c81c400c9920741e418800c4141080c2106240e210503510308940001e441600c0b54400f415280078000720641180c0040307000000c4c0354010400d41803000c1c0060940d245000c03040d08213074a5000c94082c0c0d00c0642d40d074904001c03c0c1c4800c82a0841d6040c80601110031a144540704e4100354140650003082107912145c1900450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 737834784 1250 737833534 737833549
    0x20f060123041119050426011503060515090912031b030910051e010e0901090f08030601080c0c121804090b06030c010512190b0607030909060b04051f121802 69
    0x1d445d1141c18103081081c4001001c80c038031810542d096060207190030101007075016020f200d09040c09807524594a18142c006414112001c036006025560352040e00d09041d00707402e11682109000e407043e03444034403499440e44c10141c03003d00041848601e108031203076550001c6000324810801090880000307801d8006441008240042c0e000041807c4050012800011819a2004400d0410b40d6464842d010300500c812240030b00240c1c020070040c0203001c0e0450056016100a82c1e803810a66a4550001004e1040d001d480f40d007640121580d5031485002005881ca000e1a61401d5181404d10300002d420783d210b8540a542c0c2140c010103005861804010f613410f8a0002c0c03c0a0b4148503100c501c0303503015000101003682d04460040d0200c00011581d001040341030340105001e464081c0c0e42030080a0703d07c00c2c0070740b00340325182c00004200c4000c0c0750156401c03190010701c0b18074200c0104012000e160541d0024205000c82e0000544080c4080e008996003c04800000c00034990b4900421600c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 737836034 1250 737834784 737834827
    0x40504050c04150305042a0e060d020d03050c01110a0315080706051206030109021f171302101701092f07080c0a05030a11010c020f0601230411 63
    0x4004220401c5646400c40340d540030200c42d41000a11a031b02c60405241c0300f028806081c640c0d40ba4442c407440001c1c5215102800c1e94071000340c8100a0380c51000707210015424000181d4000001220300c40028480c900501741040301c40300100c1d00030380c100c64041d007940040c02101c0100e92142c000000c190465085a0003c00322880103007081ca2809030301415920a0701450040d0341480c01c00a405a00c1c250011003501e070703000e800008407030480713107082c000c9003c2c0104640003c3c40c80703084803403502520594bc13030203007070781400050641c0c0241e070802074600451045d500900c80b01042540c0702c02660f910480c000c00d1104004a480000742a0710b00000508921103018100c0000f141c1c08481101000c2d036000700c0c2c0c0408541d580e41501000ba51825038401001040c6200004a0f000d0180d40040b14480d0130102c030700280034000707910300c0503030700c1d08007410720b1b50b0312903015a004000b201e8a8261035141032690b070651100401264001c9402c0d241c04020681110034000b0b4030171003070400d80d40850318 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 737837284 1250 737836034 737836051
    0xf0209072c060c0a03200604020619030f15053d1b031701091a090601030608071d010b0406020c0603100b0c0c0301110c15070c0b0c04050405 62
    0x107114040d6031552041d9952000c0809407841e00e6620340c4625103490048400105110301159682e0815140081001000c0d580d1440c0c00036a00c40d443e4000000040d0480c0600c0c0e00418060501404e8070103054418442696001051b40b504918010300040c2d1081480302000d401c1e0f4881250b00f440188012170031029440d080048680c441c00440e030f9800a031040c2050070b180190b4204040c40c1c901201c00c8070000c0d5a0f0548a010300c03140342e0800da0040c0c0000b80c0802181410326481c6c2e62035019504844865013041386c55100603014600528102e55299889141410300042c6541c542002c030f03152210507049071400c0c14100c0c42204461140c01055030050074081291842c003410310f08000c0d15100b001d9440c0d40101c8003c400300307600c00d42c400d0058001e000301c040740c0f9840b103552681c801d40e107804c0701a000d4040c2d460300307480380d06261101e0115030b640d03219900182a05003820100c034000c050f00078881c0080040d06c6c01c000f0001043c40c4a0a402940340351543c0f61030b5410310040100b1030b0b81c080d06084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 737838534 1250 737837284 737837297
    0x30c02010e03030a0806060a140a11101b0e0a090c020321100b0a02011d0d09050a05210c030d0c0501060b040f271503050c0604121412070f020907 64
    0x1e100d654405170195200105542468492808103016149100a5080500d0712074011800a80150307000d01103440c00040c050407180c0c000d8140081200f10f41140001040c41e5068828076059203004110030020154090303e450b9030943e030b510407003088444080340c40005810005480c5401d824400f00c4440d0a03082e00b07240805401e0041502480d8503035489655845a13010a040d01e140d0b00030340c400c0501c20403e07034550014100103440e00d61600782c120110408510380c500003107072a080490780c1c1c5054802c0544000e1100d20101c10030b4a601e80e0344414a4141c2c40344000c0301c461030b14188600c00c3c0b0f288841d121032052283c02e10b0030600391142504008903121050004010007040d9544030744c1240c01000455002c080c0000580384c80c899001d100e1315180341840c03040c8800307183c1c1c1c068510850f4016020348050506900070454288101c3c820228268400005080804d485180e2880314100b164102c624240003485003c03125000f070507041d02c03036890441403082541401c1c8040c6920801d50318100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 737839784 1250 737838534 737838547
    0x100b040204150807020f240a2c070306180b0c0c0307031b0506090618030f1206011b0c0302010e010305040506011a22090605120307030305040c030f030c02010e0303 72
    0xc02102d48004240702041018808151054001d000031060701c041d4009440540c50740000c00031503500b2028800c240b444031080021758410b440d21070316070a4005a14140d45a26201a1001801c400c08051040300c0c00b5483c00000050030b1b9110303000c00e0004146050080c00e000e41061000030400034a11402104108220001503102100311384005516013030241c090b000180441d07641c813115000082c150f10481c5e050004502c000682c045c442d10300c00702c041030428a40d044141d140d02a0070000d4410800c00e000e0111480340c40c80038280e0101e410b140241c10390340f200c0407408084003a0322050310041640314050041d07580c40700c0064a120400e082c1400f1608140d92415034600701442a105c40880c083c02c824bc03005003090441c2c86108030200c05ca806000d82d055080b02c0012503110302400700386841c000003443e092918260510017041e1024606020958900b6009454001c0c8202c840c085902d50200020781c1e8035284001c07060181c0d44491111a1520003d003641880d105142e00c242e00c00d200a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 737841034 1250 737839784 737839799
    0x506044215030c0902071a150415050a18021612090501032c0304090e1507090b04210602041d0a060b090d0f060203040308040c0f03080d0504031709100b040204 70
    0x1d0008403110031400699808460030000c43c2030744407d00e50000700b20b0ba1b405015140ba090120074940080460701040b101c0b1800f11784950103141c0d84281e0380c010200641c1003000c118080d1a103024060300301d40241c6440340b442c0052240d0700103504101c81a000801840310261b500203485400b8100c05c3c2002c220b51011003541001d0008242c0d0710303101c01007891813403c01551060040d2001808120000c2c0700480e4902c0e40340b51a100d103200d01d0285403c51100140c201885191008101e41e204905546441e09088101d80120305820000000190215240c00060030f0351004100070001c80d01031000d2070400440c0003002c0d04000d0040703100a03040031014403002d01e0080480f420f9641c21107040300c08482c2c61400f030340c14005003800030b8003480c03002c4104401c0c0b541146030103100d2441004040310307050b20f5604001490340030707002c003800101d400e100180307d2409581c80190418003c2c14012042850291000150003044030fa141582d0460700b407503290000ca900460201c007400321030a5003064104000b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 737842284 1250 737841034 737841053
    0x90c130e0a0807170f0f090109270f050408030402190810020d05060a0503100207021318120f0f080411030a030203040501030b0303250206130303051c0504050604421503 74
    0xc2281001e08001490400b90380141501c0d0000c01c640c07042982c4c0c51011a0080ac0c04840010802142500b06464049507852501c40d0a118503441100c05045131910b07020b001f040c1d18480911111a4412070010400302420000c44554480c1030201590714205051108291390740a172000307001d580b0481c81404550340110740c90040500c0060010303250142800040c81e0786100b410074400c070b1442d08484403032040d1080345e1404000c1c040c03111500e000c1000b00703007140e090641c81d407010000f0f01d03604642d8184a1181c07007100d0300140240d010341c41110032000000e04102c04004100d0250384002001c0000c1c0d47c041c080c2d1080394904401447c100310a2a034051081d41c2d00c004001e400b02d41d62058042150ba450342038a004451180601c2c4419481c2d1501801961240b0084c140a9401901034000041d1174043d072440745502c04042c004a40f0b4a07650000700f921350401007001d40e0000b80c82c08419500c40551444e400504003032a84103201105400801c854000004400310621032000b0b10204010340b2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 737843534 1250 737842284 737842297
    0xe090a03030b0f090c18040207080c0d020a08030f0a0b19031707080d0b01212702220219090f080d020714040204030210020307031403090c130e0a0807170f 68
    0xa40c0c3c461808003c6c5491068008110764050310102d4a0410300511b04050294003a207002200c1c0040c42c809800d030303030320000780030020401101080001c45185140c0821034100070380c8040450f4401c60880000c055502d42501016159000b000c100300344040c0090740c2418000428031203140c1910b54407180100e2281642c4c40020701c0e01d0300e8922040341d02c00e040001c40d00103141041d54140c1c00381c1c6034100c0a0103148011341d41c040c44031412001100f011102c0a401c0315401441c640182e500020b1a400e444001e0340c203940307065820b004000c0104c03140c00201d00349001d01d0382c2d001070940c200069509500003d801560b0241d2061003a02c410380e03000a1070300305880c081c1900e100c007401407000141c080e20850308001c1d0090001d11086c0340032a0004003a200280c42034a030305c450811444a6107180c0d02045a501415501c550130034034a90501028506000c46242004a00c86c00258482071601404210499400b6000a048014000c82c00418070381081d0b416980c138500220200180030a00910 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 737844784 1250 737843534 737843551
    0x30a150b120405070f080a030806150d09020a030221190c0501180b0711031b010e010c02011101020301030b041203090308010506030a0207050601080616080f04030e03070e090a03030b0f09 82
    0x7902040030301c8010000750b0010554032018044a54842c00410340340d40004108501044848002c40d83d0392a14200007840407035011030f01410700301d00d1580800580540d0100380d80080100c0000310141e110101c9201e00c0308020560311003a0701101e5182803070f100c03071104102c0024103070170300000016400001d4101158002d1901c25440c0c0c00805201308400034a81c070103441130100142280411a1a024011030907000b02c1c19a41c440444204004490740d412100b0b40c009040281d02640139030041c200180018010f14003020321001400c01e50382281d20a80040c0d400389007000802040180c902c020240f203140c41d1800744808405507401500041c0103000711403280c4000700000d12110b0b0307550704ada055130f60404200c1c0c2855945c0d107201078607202c1c02c0d0340c00451390300034010b06506a4000c8a6060284034507024688265669841c01c03a50041d06554440d03050191090004068500006c02d07809140000041d180b08802841c01904480300940c16502030200da000c034501640d1281a1207510040c0da = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 737846034 1250 737844784 737844817
    0x5042a03020f090613230105180c180a090603050c060708030112022e1107061b0503120a0b0f0d03020c0d03030e0a050609210406050f0915030a150b 65
    0x200300001e01022501c13a0301c4645c00740307172044460308000003d6000703030001c0c1c0c030550415284c1d03220001c2c489071080a03010315071a1081c1d20b01041858170850003c01480f42c08030401c10b81e0050300e4001481000140c2d02c40c01e070036612810117006020040c4207400d0442c804580b101c0c0390046aa5400489010504c202d26580200c040504250340f00c80c140d070300c021010a410400304080d01a442c9100e8a1030312407010006d0100c00c80c14203105000240312040e100151500341c00400c0b0302c40c40e00342044000f1000c50f40350000f4440e200d0040c805109690090150716004500c055541041c02101281d11a000b403042c0000e460000c04240c0129040940c00002c0e50100c02d10082c0f810107802512004140820510078111220288000400c1060041400130141c07000c000310780024509080c5003881071140560108000c0043e50300840003002c256129456080c14652124006401034092901070b039010480001003020790750751485003480300d4808449440e0400e0508050380490300805951101401c0d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 737847284 1250 737846034 737846041
    0x6020a0b13020405010803180301020901050409150308070309080c10050a0302034b041122020d022d161110020109050706030b03060406110d05042a03020f09 69
    0xe196211240d01030b0040c009010659540102d540d0301e5000903801c01003014500782c510306d94501070007100c1250fa01699810700f00390034503a901c4000e0681211501e40c1c6050000d000000035003c8001e0130003d80282c5480d05024a4900340c0d9090180c00307118170f4403c0c8085103828052603041010b0b1245021680390040e200e554140b06911018069640012041c080380010044c10101100e207610303035020203844148004141031142601c01090b5402030524076004c8070740e80181800c0c40c54040a0010708010140c0600803404003040340d008164288501e50001502100c00c07452000794001203050125034028101c0c1c1c3c0703065000c140030700782a48070140701c20000742047c0680303003011080540c030062048642d45003404010b0300925403110b040f1198080d00000003038042c003030720440079202405000b41c0b4a6548503030f52040100669902d201815106105025500c0b07032520806200318400d65546001402074818464503150703071490051076003681641800144c48010201e84401d405841c0c0c02c000c1d46 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 737848534 1250 737847284 737847301
    0x12030c0304200a0807050f0108010f0501030e0a2f0105030702100e010902120c15070302031c0207140d200309120c090f15010305040f03080a0615030509120406020a0b 73
    0x4611088442c0e029481403c081001c103404503200048030070031034034420030440ba00d00550792030341d00b403203001925001c0500812195019401910b0031003001c10030303031303100c0f40301d96031841c104803c1c41c00c1c0c0315039004404460808204031500114004502403c040d811403802000082d5900069000041410f0f296006000c201800750061240c0300d81c000d10b80007401650000a903611950b0081c05449140c10b0488000b01192540031a400540c15902440c50043e00122203d01c200041c2d1046d03c3e400c1d4200078800c0818040c074403030314200f03203914054906c0c50760803039004001d40c070507095030010360440801d1030080c107600000300c40340c201c020340f415201402c1d00300100303007080a00c0800541080c00c20003044030000750014050b01c01c100c191384c16101045500d004408603001194014580c1d6001d09803034000c617006480c03840d030026103000085499038032001810740c08036040c070311f500c0425150818820451170078850342064041044980b17003014680503000f0b641d00e1115070301400d40c4503500081030560 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 737849784 1250 737848534 737848583
    0x28020d112505100305060406450204030503121006020d180b0a09080706020d09030f0c05030106140a14030309130b0607110102162301050d0c0c0512030c0304 69
    0x1c0900500b20074094a80c3c060140c0070b403004071250342c0b055207402000300d40800e40743e00035803005000c480d0010b4610710000071420070403020b0b202c01d0300342e40ca0700d0001140c2400ca400200003a41c8103001954880a402800720180e00c005000140d240409403800c1c02129030000f64143c40102a142166160400300c000180c0b030301641d0410701c04640001295511250050480380890300c164003118038659540e0001c0342c540340310540c40b4000483d10750f010004641c01c80c440131f9003280180e6800308001c3d82d0700c0000b400c48080798001c440822080c03c50f0040c41c64101240b00050003101380e41c2c004005400000ba80300d2054078200b41c86011205c0ca4040002056070080341c4480000d0100ca40e02c06433414000036102000c0380e44d50061065401d1428460000c040c40800c58000783d19584150b505d040000c0075401c840040b00c0d0410005100d541102d94007401911021041a11001c41c030030010b0030b01d076007810301c9458009510a01041403080350040082202c0d809500150600c50003011054040d241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 737851034 1250 737849784 737849789
    0xe18030d021b0d170702010e0304170c09092107051213151e02150109021b03120114180f0a181b050406060509060c0328020d1125 57
    0x148501c43d0b0700d034102c03078002c0012121078a0016080220313a0b100d0a0072400d0b02c40c091540c1489404c103000811810300354505807200b8424180945040600c04030224816034800c40c0d03020400e030310003c1c100041c040d150666000000c42003006a180a002e926015602c801c10043c030450088001582203110074091140030103000b80c4c031000d609440c038029004003011294001c0020f924071100102d150180009060100481e8951110040780e19210320b40b0001d4011040c82c0300c240715003d9003080d07041e0082c0010900c03020300700d42409443d4100400d54048203408541580180410050220b02c0014948250743c0990728028101c940d588000c2005c0103000c5a5890840d000241030164080060700412010790041c1c952150300740301e81d200c0400007a60118424a8007040080001c101e06017070820007061a401c01a080742e1400c088074201e40400c1500003071000080040c6076051100b01d905000d901038803480e41c64000a02000240301c1380e118a40b8000606103043c01078404030820201d241030100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 737852284 1250 737851034 737851087
    0x3164e0803070f0816081611151017030714070f03060b03010b01030b0d06050a02040e01080703030e04110906031e09030403020306090f0a080a0203040312090e18030d02 74
    0x201da0810900c007500d502030424a8030045102040025000c10f480c00350805400c0301035941c03030390310303298401c18414201c03e0701e00c09420840c1850380103100d40010402050003400c0c20040890916007070210040c00003283d088220f0f1401d5070480c550003100000261101c2c1c54100e07800c0d032000614507a40c1890680c0c5984100400204520004240195a030000d1500d0f00194002e0081341d03400c0780118100c0d60580000c947c044a007074807040118105503c9a9030003102400b0061a05403541300342d5a840800741e02102240e48040c1003441050303400756200340c0b400810340703051003c1c0025042d6581d141c0600c0071200e0041602000150440d0b00f07200510803110b2040340c43c521701c0d0400010042e00da6001c2d00099011f48101c2010030030305003000504120301d04010025140f118019903807a84545c0c0a1001d0301d007144018440400440d6480d406442014060f0302d9a00102c0c0c5050180c11100c03100600700d98842d1180a0000c01d110004000c0301c07200501c101d40103035103251880318943e050104468026 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 737853534 1250 737852284 737852287
    0xc0f0403060606080103150e07061d0405040506011701150b0a030207020d11031605031005060109081504060b0d0309060f0504090501031a01050303030c0702011d03164e08 75
    0x10f00c0d5802190303080c10381c1d0140c01e0001d8114031035003051041e6200b44d40b0325041caa02c200d02c1005014410b94a0b803151091a0740800340314a00007001405440003a2002d440f035412010040001d8803465a101040011101c0248541459141c0d90800d400e07052251903440c08002807418400fa10a50450358450f500400320f00ca14416420080171036600c40319010b00a10650840340840401e080005045440080092440911210540002d010301030003c0b41404008200802c0709101440b5425104403809940c0c4124901030904e00700343d036858860740303025010ba42d00503c0803d51001041c01a507801d07081c80c04030503092503012956845642d2100d0107040c07801e0000320401c0111002c24100c00f40c42e0000401030790b04d507010180c903480250b41d41074208100300040740041d4014001030380708448a9080c07010810288010031b040c068200703145641c840c0d0300034090102c2601007001923071503000c800c0d03950802e50246a498200040001c141c071705000d0030700701c4001075081c40c00240b82146d034000c102c41d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 737854784 1250 737853534 737853539
    0x10e0a0314010501090b0a0506040b2b0507031a033706140a050f16260405010e0d020312090a02030d020f010f0b0f06070f0501051509060a0308030c0f04030606 70
    0x14001c1c4820301a00d000b040c1030480c41b2115242c902d40580603076030002c15403898140360480f503150a03400407400b013003060902c0b103040c1102c000b154405091402902000700702da10b0301c900d00034222244c100e000e00122645074001009030301c0005420500412544035001c07804407121402450034a900f49202c03203040910034150030003255030480d2001074504d401291050312060b0710101521011102c01c60000e205500144403120041c0603d02d2600103418001d29000151a65898044041c14014010083e41081c002000800d10440c1080504100948160f00100750001d489214545890314a000340b80d0100e40143c0090008040e060383c01000c5a2101c804040e01945070114012032104951800422056900a03400703035800c00d18004000400c01c0c0d054004112403904021001d80d14050701400c104002103003407007054040e550039800c144802882504115910400a00710340c000e5111070020800142030909503500440004917403174035850032032441081c500480c2c1c0094509401c04000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 737856034 1250 737854784 737854823
    0x804061d03040321020606060d0902090f01051903121818060f0608010b190203120c1b0129030a061e1109030a06020906040f08060115080411010e0a03 66
    0x14012207101d01800044c180030301014160008030000c051001d41c102100254061824034020305200c02c07100000100c05859402007500c49500f261a00050003c10740148a41d1400b8066240c1041521205250b040e0940c0d0700c0c100c10700340081c40b075020b201c2d440320b0494000001003130384030203031aa0301420300f5591800040c40c2c1c0582264814203403181c2d107030700d404038980340704014450617101e9007028185040c1002c41e0300c5602c204444a80d5046003c184150312065032000c1016000b05001100e2586481c80300340100000300b25503113000841c1e80740032100500700703580e41d40039010210180c0c40c1c5028004138001003400c0181d100c2005000e01d140034084801caa1041240c06284094003e0420031403110300382c4401e0510860214a41c1507100c0c400d143d00007641038004104000001e0030301420240d46a0404417200c1d0789400c405010382089005000c10104040d1b0052495030501d01040070381069100e02c40841030030746c99981000b02d100303803041040c0c5607601500300031544965000142e6041809 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 737857284 1250 737856034 737856037
    0xd0231020705150601170402010c06021c090303050a0204031a04051e0d020714090f0603070807060215070e06030a090f0206070f05060a020315010c02030106030602270913030804061d03 81
    0x10f2403030394024883c01241042d4800c0c003852036880741140418015031201d4005454440f0800004c4038096003c2098134944c200007556184014035840c40440d120021b45805400c0d94002400c0e548002d105010400119140300b48081c10342004481003c05d075111800e25a04103000314400c2401c1c2c0325034a04082c602c040010303240f070301a5101c3c2e0030381c1d0700c413619204104041c160040c07200d81e0001c444070200b4110516070503072503002200102150b0155649104032818010b40781c0c032481c05601b00c1d079201c1d0140d07010700f1003256000d900c3c2c4c5861460300c088040001d031640005894240c0c00c0d960b68110104009406c42c510001d1a0001c02003034882415250059907040c41b0441190340780610030110700f030740d0014001d0701d028545905422410050410044406040b011400ea900d0740d00c1e544000f010801c01c0c0b001b805510070690304801c41048820a03160100d034182c44207405959180104507501003e0000203046d1581407800c031005440724105039016280c40c03013928078401c80050b038900000c0070000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 737858534 1250 737857284 737857303
    0x2150f0f040f06080f0604020315100c20100c0312050103080a030c0e03060117070306090605060a0f05010207141f231312030c0b010602030403110d0231020705 70
    0x2d620038030711074484604483c41c400030b99030021040c1280d070100e6410301d45900603582c012101c07085484d0f007242582c0041d07140d0720170003002c60210342c1030345601060100031626084850101081783c1c1c0c0103c00380000c00d03020b40260202c0b03c02c0000240700c1404041c03013507041120740c0240c00018802942c4074107045090340e00c20050103010078580a17080461034080d02c0d081c060490024082c2102e81e1802041c501d645c04c00040c44a100d0064140c0440003031294841d00084074002e000015180c98144144240102c0582100000145510007008583e03400544d4900341c4420400c4803c2c000030324404541080001104480712540380084000500d0384400c030228525400d00070301b1240706688800d200603100702481d01242e44544075040c018585040c10ba0b12440c2e01c0ba1070480040c4200d910313040c0341c0394001c2c0c00400040c1c000140030414010748a05806000c102190081d4a0a0855002646005044202040c680120807400b00640c01c445403128640360203000c15540c40c2e10758a0000c3d00d448154 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 737859784 1250 737858534 737858549
    0x8120a08071d040b060c100e0708060f070f0c1203140a090c0e180d0e0a0512100b030c040e0604140a02180a0b0a1502070605090d02150f0f04 62
    0x3400544900d00c40d498142120b02c00c0c10800c500c030352010042c8005410904045030300a01c0c100214012150108000045d209070001c0004541c20680840c50403d40107038081da5180c0d0144041c00320402110310156088106070a150014040d22041502c04401d803600181003000c4113540841002c0e00742c0c200f030038005080c0e41d0104450352034008042c12100c0041025017030610109060040b445400d52868010804404901032202c60b0483c8502c1c248a180c10b034000207452014414007400c0c0400340070042d10003120ba45007a4844030341003540c1c2d60264080c02c5103403074480b07440a00d20b403001d1003036454003003001d40240203001b20809040c5d684e40b01624215501420b22440c100025408100c0c41c00b2103030300030a00c07254282014407921140c00060801081c00c3c0d078851584100d0754903140d6000080018144054200a000d103020303003094440e600c18010311104101200349070340ca01114113000c6904840407070100b52840070030000b50061601300c26890b800001d0082c02224000c0140007240d040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 737861034 1250 737859784 737859797
    0x21e07050f0f0715030e01020702150a08010909081909050a1e080a02011707091d0f0604051512030d060906050a15020304030308040f050715030b040902060a05031008120a 75
    0x90782e0516940307004070700c101e003800c0f500d58104c88003561082c2c010308040d1255200140c00c0081503000104c544500341400c2c2d401100010310301003c40c0d0488416030040c40c0050003008800b072075455031215840740e42d20040c122580801c545070114000d64003280942406080c120300ba58440d1555228001c070a5500d846440b40b1030000a0514000507002d032020307506075100c5800220190032440e41d281d01074009000d0091911012412200000032400c0d0780c1d050200040950030610554044602c0181c0854000c07420030b0100552007103800309001d07a0407015200c03611002c8404801c9829801141401e1510500704800082c104040382c0140081d0303002101c03d4176070680e5030160a06c0f0981d10560210240c0c000303200c1000031a00540c3c605920601880d04c06164114075603940742000d52035006071140ca41405403101c8c1840d403600ca00c4a21400c213031400c2140042d16000140341c0c1c018041c0d00b400f0048000006051500300300300079401810542d0854480c001c401031000c46a40007070545c80001030a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 737862284 1250 737861034 737861053
    0x24050c03010f0506130e0c0f0a09030b0708130b1b0c0c030705010804050c040b04060b120a06080c0a031b0503060112021305242205010314010915021e07050f 69
    0x40204c2201c0085500541c1d09002900d410721580030300c0310003441d01402c10313024001c01e40c440b8541c8004001c0e020096403041d040728110710f0044900d603009420402089561020001a0301d09020a05003942d04403c40c00c2d00f5584001d200c0f4904d002682030701c0040780c1c0103d01e43c2403800d00000c2c2103819807001c8050700c01d0340f40c07a000112030b05134044030060a254407400b0921224101070740715841844020300b02044403074480344000b055a029a03c40c0c03501840d44410840b41d2049403003124090600c44001c2c25041201c40e00043d00c217412030001405406000c01c0303506001c0003042e40a001041c4c00b40980b885c07907960b280700d03d07515001e003d000c0c0c1c060000600c07849041c095a04c94544649810850502154804041035286240c81c0e40786c0b0340c106d041c0240e10800400000c10600c8110441c0402283e59815860900da0320611081a646240e060800740d60004030714000c1804214044400160ac0f04503060904690103010500030125a000040c860144140400ca5140041c1860201c4142a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 737863534 1250 737862284 737862289
    0x1110c011a04180b0c040905240103060f030809180c071205070317091002131406090105040b07060b2d011806052a011b02030406080424050c03010f05 66
    0x1601000d07204010488404883d0014184d902025004548000f0705403d0903203980b440300c101c4000380d800d2485901e42c52030817a8401c00640c04c83c1400842031800340017080c0703000814812450b6901004002c10340200d0104074507210100b2081d048002c2081d0841d650608041c840c0d4541e1210100362051900c40c105c0fa840240a1021074144940c1a40d030b40502c0805c0400c10602c161015060700080c3c0901800c40803800207500140900300c2d04088825100c902e0b000800d42402e10745000c0500441050121104981c5c0103400d4a0840361020200c5e0b6840c1d00c03510b001030003004080340c080d81c8480c3c5454804440c0c2c01828040070200210807a2040000840d40150b682510140202d00d14070003611041c00721500c5240501021620491412801444005485a5031502000183d100d07036403400d824a070702d28003900c2d102c0d510b4000e0005d5807a09050250003040c4100044c00070305081c00355603901a100d9000303024003a030268040030400060401908014499000388910003041c046254007180c81e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 737864784 1250 737863534 737863541
    0x50d0e030616030e0a03020607020f01050f0c0322060c0806060909040206132c1f120f0623010501020318120f160305070e010503031b01110c011a04 65
    0x5460050080855580702103000882107a95070903a8205515040703005060b040c00c215240c1d04600c81d070040c02d0310b0b2030004030003850000b0b4520704006a030b0500c1d00b8003110101000415402102880300240d0741e540d001e480060003000800392000e146055052036050080d03d5004011510f219a11601e00381c0f01c1c80c0800006005d00c0034482d50201c00d0300c020a0062801c0401080010416074a00507000e50358030701000303070b4500040740c00c00d141d560f0060b40904d00781c03007000c4d564041030400441c0b412201034400d040741d00020380125031601c0c0d143c1c008a4203210b50103929110141d442282400308020490303801c2405042c00f04002504020100041455030021058504c1d9540701c00c42c842041a050041015112000e0000001801001034402c003d03c414040744407040c400014074000300303107035144c0380c1d00d00700180d8015840100480d0052040d90f40c084210b50700d4408a003211b031038100da40784281c1d00500c480c03455000508000500100d070008190041d000030030b0340100003031000640b0000c0c042903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 737866034 1250 737864784 737864807
    0x105070f02060f1f030303060e0a1b05090d080313020f040509031806121810050610030903090503030c011e020f0301051e060a0305041416140609130603050d 69
    0x542c0050002440c0b0700c103804000c60380404940000038800a00071444240c04d00c80750025000681c803514180a1039035069040c2e9000050460200a98000c50501c860212000c507241800c0010000300c0040766900c850103601c00640028001c2e80c1d80c204005040a00703011508120f0140424130300d090354524040c070409100d6a00c40001d1032410040050303000b000020381341480c3d030000040c002a0b20480d01c0ba03080ba0701c1070030044800d41210626003481882c0107030a901261040d82040100841600c95000354003044c0d040f42400300700f01c000b500d0b083d0744c0c0e80c425401107a05807001280702103c605054000040c11305507540c480b41c100b412000290103902c81c104031441c0c808000c200410940c10805192202203820100d1501410303020f4000480b1644010112000691244140400d020190a6000e5000342c0381004001c03103005400c48901d801031078071489000e4134421412900a45030003048494086000b0a450102c80a9142a00c000c241d41d000540341b600c80c400c03c0c001d142c0c4c000d0381c0740001b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 737867284 1250 737866034 737866037
    0x7031b150e0f06010e0c0c1f06030209010e060609040c0509030a0b06010f05130b07260304060c0e0102060414150f040c1a040513110c070305100207080702090c07050a080a020105070f 80
    0x381d90706c25005003203500450949002e171044440c5206e030309a40801c48544082c03030303410100d09280b035401000311005068010110302c1d00d50341c00740b0009655010403200d0400064601090701130a40c0e000382c41a0040201040d0036000392401d81003001010683d03a0f108003426200e4003e40040041d044132180540c040040300088810024400c02c0300c141f02400219128030400408800f8600c109442e02011480d038000c0110044140710400c00c0e00d00504544d164646000310040e41c4d4000001c1d55980041c1000d40707a035032941506200c411050040801c4040440c11520241c20300941d04105000216425101a001200003107001c001583c03c41c103400742640451801c16007030404100780300d401c000c10110080da9070300c4440e007241c0200001c1d12100203d05d0260560b103203903080417400c040c0450030000b4014410021400000c034082c0698070300c0ba4064594207510740d40c0100c200090f108564010705940b003240070440400c010760009280308000c55000340803a17140c0c08015640c42e10401201d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 737868534 1250 737867284 737867309
    0x60121051608071b0b42040e2a06040803070515011214011e02090103060902091507050109021807030e030304080307030507120c030e060f060607031b150e0f0601 71
    0x170174903541090b500700c0290740603844460340c58070024004200c007a01402081103c0000702002c0304025990b01a00e69056405029681480300502c0d101c122001c950440c92401420742d151a07403941845444540b000303014282d40e15100c02000307550350448081103d152040c0c8450590442c0c013082000c1c100d550301c0c420030300c6c0d00ba81940e0319101c011450340118203139940d8010761100038600c0309803201301007120403005a81d80000c4d0001410390707000360068100a40100710820083d283c07600c3e610b0041e040494002e48034031452034018050101c841019502407048515200403400d00c24500b801010306840400c00c803c180c0f40c0aa80340c0c0822140985030038010303c0007403009030003034020590019481ca0010540034621100e07100300c420746510200084e81c2c840c0c0600444908010203900700b402c41515611074540340000403045d125551004041086010f221307600c000c09041080101d5a11000c0220f021449124100c000c285440c5101101c0c030800740c12214206000c1440da050361620035060303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 737869784 1250 737868534 737868587
    0xb0a02060408160b01141305060a1e03060203010b12091b010525030807200d0311070606030f020a0b12070e010507080c030c010509030a0806012105160807 68
    0x80490341007101d2210f5401c0d40f140b04400040c80814116002c0d0100a503104140c01c24001070140914002ca00c1894440c60482445400d540700c0c0d10b00d500303c604055a1154581082c03140329508551640300504003400800081010440440940300036140300c0d11042850790b51000307440c1c0e12043d4481d542c0d1811052000c030700c2a03502c0340004122002e80c140e2000b02c152050340c4003101c1030780c1429059000803881e2080c0401980e010010038001c801000d14030200d0030840407101e8440c4c1c210001c94061540d15210130350341b0806082620ba04640020703080050664905103031388a40d0704000221711400d00d0000104081900d80b05860724071080c000091041e0365003c0c41a00c4045a034100c541c107004042c0024070010786044001c001517460300c0301a545424662102c5800d40e50051b05e0740c0e080d5041840b841003600c0d841012290300c96000d00e00b020940e03004001143c509910021404422030801d000c00044050b100400c007040e111a640d580700700e54900c2e208403508281141210703280d00009200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 737871034 1250 737869784 737869793
    0x60a1b181404060b0d0f0509070506040e15060c07030c05090403120f0b06160606050609030d05090f040f0506150310050d02060c0102030f1504020a0909090c0f0f050a0b0a020604 78
    0x100070305941c1c0504001011038403002103620680040b0304481c490798a075596040c0343d841c240209600055114020301d012420503000a055008500800c0c174120400c000258401080c96143d003100d00c80506a11380c2c070719840c08040e0316504140026240c00c40c505000191f0750030a602e10301c0c80750303070145e5a01c0b00e1843c0c80b0300c441000e0038103440c3c04800c0e581c0340d00c0c040700241d813507900601c4010781504840c07261034060304d80001030301e610f0b07031200c0d01c1150705100300c404a4030b0100c2c100a0208851900d0340d5a00c0c003102c0003810401d441640320f60410b1405610548140355036200398000d10f000c8807050164184121495020b11044440c0016040342c00810015400e049035a8100340d44000c1147d0b0038100d175140c565003260401c130b601d034800780e0750301c401c1c060484182c95a800000c001541d096140620400d000381620400d8403031559017030703911240d407018450b2410001018140e4841c2c00305041c2c0d654900c0039440c10381d902a191080000007800076464040ea802c0300c1001c480c5802400306a07032203131903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 737872284 1250 737871034 737871059
    0x70f0809030a090b07110303040b070605090a03020a0b0403031b030207030e0306041203090303090206030f0f0109050c070f03020c04052e08060c090a030615060f022406060705060a1b18 81
    0x90488906802204940c6c1541c5c0034409031028092011270147c450005082120079500007070040380e081c3d00503060700c00100750701003503261310b881e000302c884042c5031514a01100184003a0b0b4100b03003444040e1000d0100b555040e001408004e010740d440000785a202020152500b200707031801001209000444c1c0100d0703003c7c0d0803102c900e134041d0070f002400c05800e40225140380e00864024040200180070008104240c034065400360540403000c104501d85610300340014800d040000e8011880386404808051007040421001070018100780800d0920140c0000359209462881d0404007004400b00040c24804c48540c040301c881800519143d200d1490b81081075001041704e0b5000152404044003150050080000c3c42030b100307000f00b0740d50786801c0c4018010454031400c00c003150807050701d91050032078400e500c0c6001c41d40400e11802c0341d15482c00059051043d02c400800c0e601946080111b450116070024800752800d00c1014841e08207030000322042180c0203803036030000c01519000c2c0607140040e84d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 737873534 1250 737872284 737872297
    0x6090f050114041a27121b010e0d0c0206090a1511010506060903030f031314030301031205091e12010e07030c05030a0818060403020919060f0f090e15070f0809030a090b 74
    0x10551b20b80e400702d0000240a688548100985051401c243c5c150146003482802c22548150024000001040d030f03000704038208550003e80b18280104503000305990704580070008018884c00c80e0501d1080c0403000c5d0203140f2240c0c090071154a040c00080190400301c003115408040100503514028850a2803030240c1c1028050506543c08401890000bc0703001c0860882d14840c60025501d03589103142214039135503801c801008002e014401202252100640042c21189502c4040700314054030010540908120040e05404c2d07090a03541e0492a4011030008140d03030080c10060710b607a840e40c00b81581c661034100001d00c200d6041244415200600c0303031002c0c8541c0c000340541e251564a0300012403d0f0401d0b2180422018003d240c0d502c100f00300d118010090807082240d02c0610300d46601e013102c041e49480740c202c2d0039841d041201c82505003404680000803540148000608105900400094407225060003240203100070840080000098500782e81260341c07010105402c103a0180e02681286 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 737874784 1250 737873534 737873611
    0x1501020a0615120c031209050a091a091006200604030f0905030607030c08070e0307150309061b02060a050114061b070b0a02070501050c0a06090f050114041a 69
    0x421010424480070f481104480f80a048214449811810003101100d1255011001d000c48000c042105440d203075a104100d0783c80c078200288400c0c03401420092910803090850340000322104100401000030024810303070700d0640d1203600f240441c00080e81c14581c969020003e90340b1440000340041c0c41800100702c25001850034401542d9200c010070b240600680702000425111440450515800b040d202d502801510708401c0000c0000082925204e26009420307241d040c0170388a084807402608014452540000100301d100b065001030b8090b44528241c503001030040c2c0012800903000e038011103050350050031444c10180040c0c020020180c2c050001e034628990701c442500098442408504000c2181a0855595000342c0c50002c2c1861a50740002d41070140c2400401ba24440004410501c10f5001e44c00064840d114108211945c1000100400c0340d0b0a241ca4141c10050b010f8286e40210310510300700d10b079001c0010f0386010310042210382c3c9403818011020217880c40d002c0203803203014a075403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 737876034 1250 737874784 737874821
    0x40905090a06050c0d050f1e070309050f0a0203060c031504090303090501020310031127040f080403050307061104030b04020f0a051903021905060d0b03031318051501020a06 76
    0x11079031400140c500c200c80302410140c011980c90789850781350245a6124140e402d0003d09450700300450308d500c8100c90910705183c4546400595024004e0344684d0540c0c2d006811240c11102d008405c0c2c0d07441001c446e049000e0300030440810945810070381501e01550780c0c1060800d0505006007440002e256000059041640320240240803410038070040d4014440020096800c6040d414200900d40d89070719254010b602484610000c1c0b08200d203807401081c40c4003600000c1d070b02d413410240259410401d0207011108001000010010004002c2140e240f14041c244400380300403c03e01203e014a20000c1c000b0025403000400520703103e038100c0c20b4000000c2140b9500c540303500c00f00e903c004070703004214504030540001b03206524202c0c1003a80700646480c1e1041c0c1142c101808503c1c80d0041000e00e1200b00d403101c038403c0303141e070b0306000303950a0b01000c0d0709544500d56201c070011b5071b4a404110075912285800040b4040e40d801c0300c800110501c040c0c0003000c0ca0300076562650000c142c024906541d9864 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 737877284 1250 737876034 737876053
    0xe0402150901260618060f0d0f080c031c060e01050120061006081807050111101103150118290a02061e0103020307061d4204090509 58
    0x1141c19000840000442c242203440c9003203411700a0540030408016030324504401003000a6941c14003030000c04505a540c020085154130781004a400c403800010b00200004ca54408050400009010501c807000e803062000391003c111002100d500380904c1000008550040c4859401040300c8031411702c202c150718030f03c111101d80842c20000242c4000036501d80c9810104441548040e495400c480c0c2c0341c0b22940080001081184d6441d1188502414003a402c402220744800500580018040140040c0111030030045600301c254401c0794101b405000c090b425100700c0d4801e0032050301d00c0d0800c007040104a4203080480c06141c00f02e4911041c4244c406034042c800d0031100c0080e01001b51180c00828541c01c04502c012840c049040c00c0c40d0a0003000da00400242c1e034005502402c80720542040700050112068448048288860050b0014849600f608684664621014064143d0510003070320012174641240b46000995108031502d60a2105010030041c55226a82050b00c11040303422032038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 737878534 1250 737877284 737877317
    0x901020a0501150609050406050d0303050402150a180905040b01060e1309051608160909030c0210110f03090d1502092205010905071d01022e060e0402150901 69
    0x8100010003d881880d901c0c0800a4580003480903001d481c2c102e4051004a003050041040001c12502c090704060302e5401103000d54644e0211100303030380c140381e00150341c2d8041c3c0c80c0c010f401c20400c07000ca03001d0070f12215000150201c0a22546005035800401952103920f064000c4a85c0b0484440d866880f4175200c03403c16018029200b01480300c0d00c5140a0a80300394032840ca00c4080da155400040d05030802c802d2054800c031001d1401c400d460305070900280100d040c1c04e044070000a5983c000b0b400c1500c3c114046280e0390050048440c81800d00125000003620380101903c81c010034451036004000150b8140005002d4000c050b81050a468010705040802c40051052140c46410034245005070048410f0026507010b018090550080b091006051a500003403034602d44d840c0704c2040c4103070199110402ea10a0007000800720343c45050341501c41694050305403002c600303924560071070300c1d011300010a01a5a42e0b010303c40ea070001e14030b00c440b42c180200d0955035885010310504120030026a0a103d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 737879784 1250 737878534 737878541
    0x3091f022d0312010509150d0303090f02040e0c092d19060b03041205030f0103020906131d010b0a052116120b07081504090602040504320705030c0901020a0501 70
    0x1550300320f00100554900740034040400c5000c1d10011080c080d4081003107054945204484007698140f400040100441c10304d44072980500d14000d600c03601f4001d040d8003807400058400c001150403103d0400c0e6403160709004503101904e9814031105102c0e5528041e407075081402c1154029070007101c40301c0349181c4407400011110950400b024080c3e010003880184803031070040c2041144113040143c80e60a00c056509223600c01440000d200da801d000000703d55484400380c1c0d205d103002004052040f007a816040b241240031904419060358079041e00d03485940b030607590035402c445016107004a84094402100981000542000c50300d1041e20000d8501c41a828000d500500702d1804081c134100c13082c034101844a4000c1c02e050304212100003884001040458001c00c0000101c41c0002c40d254940307003c2c400b9002c0d6a000692180c5801d143e940030100311425807031881d1100c0010041d40c40684d81d0480d407040142c40c5000011304c1400010040c40c0400014a6158414012510314801e10350300c0d0f07401d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 737881034 1250 737879784 737879797
    0x20c03070c031727010c0c030c090b0d02091f0807060c03120212010510090302090408031506031504051e090109110303070807110103020f0c03091f022d03 68
    0x11801e101c1d01c1042446012144181024032804200340b0f4000121441c01603500080c91a6980481840a0f50982c0e8003400d95806d14039071226001c918203540b424082d03d420458441c00f01b40905041c1409003e00d0b1403514200910b500402c200c9464540c0c0e0300c6d5503150300c146040003680c0c0000c0440450844010030020000b00341663360304149a90500c1c000b40790008081c42511064010720401e05294014143c00741590703800ea032030a2040400180848880c403140d0f0000c0e400c918000184401d0004400003580b1504000000300c00b41c030b0100c0103105040c80100c3d0360b8915110000c040c11401c2c501a0071003a001062032560429103c001900b42c584d00c54142e4004206030740d80c181c68020820300d6080e0600340170b02100034505240c069150965184500c203c000c0c04880314280d0341402e030b8001d505440900c20040d8049844801c41546e03603a695200d10341d10b620802d0400c10100c404d014100c500f00c2e20002036400b400301d22404400d6509048101580081c3c0003140d030b0710400410b10708001808a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 737882284 1250 737881034 737881043
    0x70f021804110f0109122a0e0a2004030f260d05060118061808010908040311040b01120e0a020303030a0b1c05030f180a030c050315060f0d06020c0307 66
    0x1000d65440b04204250340700d00c400c9814001d0740b81d801c00a40c01d0411442031019000103204020035032904d40080ea4046145035514051180038000c0b48450842912900c2084400001c005004841a162644140c00345959820000401007400080c40504284c0314943c42850f40c0d09040048980c1c60200e407007004007100c00e030780c0049000c15500b803441c0900ca801c040c0030b0904900080704c01c0c00000000c1e4a03030054800f03000c0440c02d200c003c201d03441d40a10043c90494001c0140310b10b1440c04025561040c80161003150204428a4143c90030f48100e00703441034140c448258070150f050075070014102005c280d01070b600880760901d0141c9c90910003588108000c081c0003600d11110700030840c14a10084001400c120040e00c4040001d400000b15448449560406a21800701103041100300c0c3c008030700d15400000c030000c00401c2015008a01065a0702202504c00038001c040100100000441c0c9103036200c3d1900c8100049410312030a9040007034091000940b521030319031001451540503030b134203d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 737883534 1250 737882284 737882303
    0x6221502180d02010e0409111017010e0906060d02060909071e1d120f03070f11010318080d0917030919111504170c010306050301020a05070f021804 65
    0x504031030801400d2880010101e8001c445102c00340c00003802e10001c042d000d4050340e03450112034184003480c000f10000c245c006000b0721104080300d0009080102820041c0019195107001142031049031074410300c04d080900c010480d5541d098200411000d9688042c0d801c030300c6c00c10141c1c1d40307a207404403503e00c01d008a40304c0d84d60034802406814200c414081000c810880765080061038030641030481905400120b59200216542e0708605060600c20340f01d03e15a844002111010004000c00034200320f80603520b80c03070444041200660a840e5040c02c0200602d41d0240c960700015060303005400c025041c120300280241e00c0b6134500c3c43e10460103c0d05028004040100301d0412020070156224600140c06000f5500556980a40100302da8051a104e2001014801180d0f1400c00654008040421610700c113034105918260f244c0040060703650000e420041e0106003420140211000d154080d5156441e182c040c2e219561403405e039940c02c0760300000310440090018103000d00300d80224010b419a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 737884784 1250 737883534 737883547
    0x403020d051c0f0501030c0501140912070f06080702010b0d1a1b041419030201050322120c020301200d05060d060c121505090106030905010902060a0207080709060806221502 76
    0x307e00344203203910450400205900e0b03618003080d14425200500015a001d9442940303407003040303080c823401d0380003001e4804d14541c0c0003c40700d40c81451103004041d00c0e0000c0103040c29940a1258441c080300014111034981c2400d10215002d6000080c0c1c40340a0325030405403816468002203050384560b0007140d801c080a03107002401d02d0070394031018415070b0354000403004c6860340d40068400d000040c181c2441c0303141c00103854038503006100d5001d9090350014400b0290700d481072020300095046c10b4181d00a600c0e00e040304040c0c16040307a1104d0320300d192020761400c1103501913260300079100080c6400e8116a1068101001405a014030011905240c9400100161900c1750004903019000c109400c3d010580003000079840b0754044d64191402841c0c042801da003a13090941c09400f0090b802500075a00007100d003400d580c08505801556124400d5072000c079914a036080a40e141ca010385101600418003044170900410704081240d003d0030b02243c2c02070013a44030340426440c6240c210f800b1a4002480 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 737886034 1250 737884784 737884793
    0x209090c1315050a120b0f0d06090507030b0f24040218090c0307081f450b0607080a0c0c09060303031e020a0903110103061e06080705030403020d051c0f050103 70
    0x40c0068116102c2d010802d1b00b10050000e400400704542c098060724152075200c06210700354001144036900030013142c004032340d2840d05003102442260600d0410301590003151080f407038a503400c540c0031018189062443c1c400e204003c0250701c0301608150128181590000c940c40da20300f22885807415000300c5031240381000700036080c81e07801480d403403689800c0c2d07802000d0303044648101802c3d40c0030049040c01078200300c542029200303a07203d1000041d80c010411400c44003e201d006e08070240c0d00c50003d11850100c0418400c10b400703107542c001c00c151801d10241304054400c040302c02500703001e000d03000c40040c9d448081d0310841d45a0780055000030f032201d000f0380c2c0400f01240042418440c945d811884c00c00e10340d200810b01055400002d001070807140341042140c1c03090708120040c122440307169501d0f0303031250807480c1041c04510404022400c10340004210a001c0c40580344240c2d010f03000790031510b40810040764541d01000b842161201c9010620108540e24400e0401d90702a0400015555066051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 737887284 1250 737886034 737886047
    0x1090c05010207080628092409200301241d0103031e020304091103090d11060705030703180b07123b010e0d0306090209090c1315050a 59
    0x35505540c08002d00700600c8400050480d1b102c4000c0064204d250100405000403004001000300240e05041590090014200c845086281e02c04c2032021032a081c3d440b8002901c0900e5000317400e1505040722202e111030036109030800c80b00010300004816400d01d142900e00560301811290040c203607641880070405060030344560700d44e4803070442925807441e54024048603100f002030000d009107010100700716001f002074a02818015205000016026960030220707001180c00f08141d01c1000e19608031280109030480901e81d80502030181c981d103403101030300c8944c0042d25010403d030340c4400154070015401c1139004002d00c10415800709041910307008189459000d9a11501458440400d404440203038100078001c400b01415a9142e11400b01245a400304149146075035003005000120303c4000b140e141c48450032600d04201550b1070340da01104030b0003a000b4080d00003000d000403070000305803d8054180708034280100002c3d02d80751068008405030764004040800d0000c105120b640c2c7c0c1094 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 737888534 1250 737887284 737887289
    0x806070c0605091209210303070c0b011703071410020d0218100e100e06040b09130b0a05010302030a1b03020a1b0c030f0c0806090709180308071805040e01090c 70
    0x1401041200007580d00e4401c0ea100f15a000f0384034510584205d24041c0c1c14010111242c26890192505d0303203001c004c01760090b007202200b110240700c4400080dc0d05401d0303c450902c014520300c021030030400300b0b9588600071400b0809a007110b105071135800017041d80700d000a0a0350646040e000da01e607002d280c08540031182d140d0702c07240300320010320007040c440781c0c40811000e900718211805003513142c02c44e00580f1400300e80074506402200c000b40c04905c15a000c0d004041961003551840740e1028040300c1041158560107a0503401440702d40e00f00081e40c4280c01a6402034020100000c540c141c010080c41c11140c00f0a40e0800b10350003140811704560000310500391a80099940981d00755140c1da014002c0f009800000d2164444600c01c0b814030100e105900041c0420b038084900c0c5080c401c0040343d03103083c00d103c7d1846240c106460481400884288003801c264561502009920342040503a4410005070007800e001e600000c0020b103550b19801500c0c0040304520001a05441509001c018402c0c0358 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 737889784 1250 737888534 737888551
    0x7080f0f0d06140402211812040501091208030406020f0c03070c09201c020f04120b1b2b0c030b0a090203040b010b210103050d0207060e01050a030f060806070c0605 72
    0x5000c2d80b10458110031000c0c06c41120340448149954481070b4140784004100c0e07030516203205440142c09103c208038001d04c03c0c2d4400341c072000041c0d0703901c9199007c210008400100b20344001d001040000e4030302d8014204445040988038100170b0a849440d246030803039102034403589107811042100c41c010340304a00441130000c03808510032041a40307401051081c6501d8030101110704400010004040e816295403441d5030034a00d607161340e10074104901c605001000e03503c240350f03100803640810019001031605160009041d0400b4504c92070240810f908001d09410440710100102002049210b03a0715801c41c2c0386c400051217082d81081c451441c41c03e4106040c2a0b10410500020802c1c8000150442e008604030558a1600d4100061014a40007030b50080da610f800011003044000310750308a41000b154200c5070031950b600c50454800c441c030b203042c0380170920411070072600c94800c2c0c00040c298401400d0206509a99030141c61401504440060000d0944155070701000114000d80341c1240d100b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 737891034 1250 737889784 737889787
    0x1210302190f0b1f0b090406030b0103051b010309120e031c0207080f0705030303010e0a18080d14010f051003061a03070f03050114091e04050f150c07080f0f0d06140402 74
    0x284840e41240c00e02401781c5005c2c1a00850800c1013640c564004001550f4000c80545240d690b0b464a56910325a00180e0b008181c0c0702c44c0c240c05294880c0c480c20703c81a400280c0380c2c1d172074902020140c2d02c0400e07441c0c900d0f405000d000403084c42d281d100d408800100d903903a0b00405c80e0528154603107080142040206030300da040403008001550b000000e0300d0654800b852480703419180d25444c5001090464007100007020f2092088060041c020040d040101400d0002e100304404e0640015413070009004d001da281800c620244540d00701106000842e8402c0d0800284040d21000f40f8409113002148a5507001d00c00020081c0640c0d02110321400000c1506040c0036550401c80304000c4000902c1c4210b0240110f0400606000c0142d45040410303a040d900c5000304c0d04260078007a444240c41c0011410900c18005001c807003404500c0c00c2407140066051603800c014407a03682ea02c01d0b82c892800000c0300326043c400c107851920780c3d2008200704a041900001c80384c0c5400c805881ca50090035217180302d24030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 737892284 1250 737891034 737891071
    0x60e030601081002030c2205040c0813061a04150317070809091e0f042901030b04032d08011401050307270e0603010b0901210302190f0b 60
    0x18000741010f07110b000d6240c05620703a903c0e01c206001d5806008540c0400b241645615415002030a02c2403003522000d540500165594020660354114192140010003150314441e101150890b8081c08850303644c0e14070709a06a04210004056a03c1994000805651f0100030003c001c50b050070150540c90003008a400e20391681c480314001c0c003640c805c00b07002d070580000160510420500f03000c44006440c00b21802810702c00c031200d1294034111011240f02c100c40c00e40c0007004401d1401130507204a200c407549402d07800c42d0b8600c1e641032000b401c11000d10001c43c0f2900c500440a0107105644424030300045810340e21440000d0075008103a018140403080b9a8400ca5540d078400126503122030340341060341401d076100c4003896000031040200c3d2403085580501003680a46510310900a000840003807011425180810421040c284680601842c041700491196103503070041001c0507020f401a12150402c04e4800264000c01050850302d1101d9030b01c0e50001c002500c3d0229030011425a0314402411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 737893534 1250 737892284 737892299
    0x3111212030109051b1206040b060f0d2705033004020f1206011e0b03070804020d29041e031b05030d0c26240414040804060e030601 58
    0x30041c052030710900d0b226000a1a5600c58001503911745000c0382c0c42c80e503184800031007070704101e000342c0304c640c401e9050201002c0b07185803010580e40c1e04204140ca4074900742d584400c00c40206415074810031803041c3d141801c0e50781034201b4070030141540500061507840c110410714841799680741084030b01c40c06901210042c61960088410740c030039810b544900d074010409001030601086280d0350401485024000310b0700f940788640028412a0b92034601088079114454440e031404100c1d00390000480e0040040c0c00b42c50294a0358000c80d0052a44456075a0401c080e80442c0e9000a0102401c44445003030000700315903200c1c80300a040308840301000301c5c0c21a5030700503d526410094442c000b200642080d0500409004549001100074002c0103000c0082401400b4003148080e2482c00c8045044c61a407403030311002105210741105054054041204610181c6501054502c3c03030308140c0d1341301c6140d00401070f00c416070700a0b4000d0002c90340b80d501c0c10701c0041c40a101413048a0194009000401c402c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 737894784 1250 737893534 737893537
    0xe0d030206040b18030d051306051006020f06190207081c0b011e08060405070314040f21050313060204030501180209060a050328080403120801090504120f021603111212 74
    0xc4425486c04a180c2e00c1e441c1007918404c40c00038000c0d044604c0c0c5020310030012516543d000403205203800f61000c1e00390740c1d0701d4582c490000701c52102c4d000c00602180c0e00e122801c1e90080113080c2c2f080c160b003410556070500b03801078420011020001541e0754444403036550381224502100c0203019078082540c0c0e02244008014000180201e0b015603152800b00b0411802a00421306e101d103640c0255030503140900300503a074070070150815654842c03583c81880c0c070140110288a80b40300e040e1101840c585507040040510103140b50150f030340c80da0030f20000c00014028000c01180788503c20882c09031103014010801c0c0c603800036103a01e20584440c40d00b048a030718046400745548851301192500300c40040e19016088910f180000c0c40300b074000034080108110170040314a801680d9a0307101d040da0b04d40348540c003160070030381d0040d000f0301e8501500c031081071048000c89180603061041e03521000f00c013026041440079076041190410902400d10b03009007060325150080e0755140d40203096460800094006a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 737896034 1250 737894784 737894797
    0x30a0b131b031d030c010605130e1e07180506030d02061302150421050f0a020d080307020c04020a05040306050c040e0115141b060f01180c0e0d030206040b1803 70
    0x780b640b580c402400d00d00a00907520700750010a4240c0303a44501e442242030003003c95018203445149030000060200c5440e114921921030904003d01d00e01c00d0500441c100c0b801034088030041403003840c60220b0701b003421003074284a41c1d6602c80d01080c507090030070401d41050280141401103501c500c1c10012909107591044004540507501c42c1c03021100c1e00e00d20000c1d4411904480c03621404150000c0845070a4601d221031180a88183d0701545a110030b019211111460040d500c19200c022035008204800019900325000e40119010705d45e0000119007603800c503220381408520007080802c10b2100c94010076900c1800f41e030341d00c0c0ca0b050910b41041120341d07040c010036000740404102c00c0300481c00b4000124142c040200f249807079140c81c681142c1d650080e0b44060440d03005000209800b20100103889041ea14146004120320b02c804200400030004a40000d0821281e841c402d280350701c404101c1e60906000e58080e000ba49881e01340032800007070103000320541d052414000f8044050100a4034030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 737897284 1250 737896034 737896037
    0x6070c061205280e07081501080d0e040c0e0307060503011e0807060f0203040902040e01030c3f0c0305010903140414010516061514040b06070b061203030a0b131b 71
    0x4141e056007102d401001344940d400c1c1548a00000070941080c0000d030381c0c035000c000c0e00c0c40c245140e807290704076034458000d03004040224001184a1802d4036064102c41284060741c54010b80441d074a00009140070102d43c00840440d000000510804100c1e01c2c4800100520300380445200707192044240d56407207a80300b00410411040000d54103284240100d0b001050203110540d00c6d1074541003548910700080c402190000440900001c058001c4040ca21441c040c0d13041408080c41c800003129200c00010380840c80038240d0b003448074000381204541d8009103000714000941a096890090250300c20400040d54140091008128244030003440d481528020b180554840030a42c1078503010039034516005080500f400111400d10b0080703001c0004a64048041c0000c4000c44030900c4101c82c80114020b802401c100000000b0414040d0915005503010308442000c004c440c41440c10f5810517039240325111740300c00da803008a04d841c0c0008450450410b004001070b10201d440f07001c10f101c0c020030000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 737898534 1250 737897284 737897341
    0x50603060301150602060a0b010801080c09091c050d05100305071a0d2901030c0c0b06030307060e06092e0c0e2101060e040b042006070c061205 63
    0x1000c5071030a4121046010610f81500d141d1512060065201c5404641000c4107038545070700c25400358454000365040b01c0024028210b020080018050440c1c001081041644102e0441114034115840c6d00300d0032415594901da202c0d401e121600c03099940103082060b0511580009002040011501c0c0c0120f80b1151100750444450f40e14010641c0141140c3c00d921515080018500440c0c11b104403071001c0f04594607400060000c80190119031070145036000092174080d0180010342e02e42403580e001f0000800312820020f07140d40d61401c1e501c16507030340016904118140114100f0400c4560400300401e2507042c418004c0c40c00c07100c2c0344004401c040c01010740b14074504607858092811015040000740900410f40b100c0034070441014111702e0108419840d0604c0082c040c0b070030015003401641d010241d880d0584464464881c440036600e00a844000017006140c010ba0b01d840050542500c20302221071001c4c90710304003030600d00f00c41e50300e0604d05c0d051030108103200741440303400e0b14000c01784241d0b40d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 737899784 1250 737898534 737898541
    0xc05010c0302010b090f1f08070b0c01020c060703021207080118050402040b090a1b0c0507060e13060e06040e0c01020c090c041d0f180703020108041e0b040311070e01050603 76
    0x8034090b21a400050380c00203485803d1140309400f488003a4450016803098501f09081c00e1355100070300c580b07403140000c980c100c070b04284200c0107c04014041d00300000000760501802c004883d040401c2a0390400110307a0002c1c0403030740100e01c0c82c1c5095101780300b030502c0070701c07076250400640040b840001c0c1200d600340e0340c100050441d66182d0240c040414040e180741c240d441e1610300c41d402000c6150649182001000e01c000141c4c3c494400310300341136804006003801e586400001c0d00d0302c0c00c814614503030000c03d038418100c21420f070b440786000804000050405a083c04d506001c121403441c0d0304811a074011700c0c841149640c0008140c9a0b2a00644121145503294400315189001d907805c500c034103c0040090510401004a03100e00491080711050115100c01c01c1064101803070401124587e0030440701000958001c0312a5075010703001c0c0c15110301c0c04481000355059948104000c0300e50a80410a110505501c141e40600080840c0b0003130800340c2c00c10036038106100051185030310609001000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 737901034 1250 737899784 737899787
    0xc110d080a020f07052a0d081b0f0c0a0b040303080f22060b04180201090905070507060c0c0c060e030c130b0301091a0f010f120302120307021e0105040c05010c03 71
    0x40340d03240244082c0044d00c03860645061740c0c036005240c117503860032402207404902c14020701140541902000700540900f00003070380c4070401c6070040010b01405800c0c1400856541030300f84024041c8c038039100044c01030641d003a001c0028242564018030140c61040c4418070020703811184007500b00745a009604003aa039001c0301141c2130201c40407480000041340048074108601c60f048581140c8084406102101c2943c070101b06c102c0c04040040e00040708510100b050b8030030741d40059004481450242e03c3e2150644820702595a01e600d80d5000942000c56401446003040c1c8083c094070861030b003202d111201c1c0d80000d5860181d48071451042c0103452140c6011445544503106101019000307219841031418190f2504654094207603010400710001074441580ca150381d0305070b4a0301001c021145081661070038012502010440a5110303100c1d80e100c00d2282400514810729643e8001e02c3d05000301c0110154854000e9107408450303044c60284000510841c0011081e40c0c0c080c43c008240c10f010303060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 737902284 1250 737901034 737901037
    0x50307140a0c030c1103030a110606040902060f0703180312030b0108091b3f030a0207060c0515180d0203040302030d081b03150934050418050402040c110d080a02 71
    0x211542d0600c0002840d0323801e00c0d000050640382140350000c0d149180d0b1240140402d0799018a0020340c8013a0401031100c44801c40b034060503c0300c0c060302d84460381d650a00c4150061003143c2e0001d41d41c551955400c4503413580d15020f8402c0e110000c2c03800c1c1c0a1400c144051941d1080001f0700b203100000d19000f0855075490381045d040024011203200085042c4086081c1c4805101110b510790310f030510742014601e0b82000003100c4e003580c610750048c00d901d45071041c2114031071001c4408840601a10708490303621011541401e01507044030b40c0700302080b038a6a003140c0c60205c101c080c030000d64009010402c0565404601410503103a039041c50505a034442000082480c26903000d5420002c010040c003513819070340c011100c16240141c0e50b00031140c40e0100d03006503400c4106000c0c40043c0600224002401412903030308030411550810310f09050f02c80310484000076424598504240d0f1340c600b000300b9071400380200d85c811440c50402c076803206100d26543da00d0751990018101030021580224259619a50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 737903534 1250 737902284 737902313
    0x1050301180204110c190c080a2a03020619081f0b0d060b0c0703020a17030a0e01030e150f0708160305070e0904080a080c03010803040302040504060e0a03050307140a0c030c 76
    0xc082c2d81c00349407400700308000c1c000c1c46c00042d00c1c2603180302404509000300240c000303200da4021510302c07400c119400d044c2c410a17010840c4202980c194220010050316200d016201081c03540781c01d08581005020020040711006003820705940d500c11101869844011990050300e010b0782c2d52681c0c81100602440240c0030300c1d0302024880c580003d69002d410000b00c5c00310140c0784206c501c0241107986501798a59920070300c656001303e030400c00015013000d019442d1201222010304021502c403100c900b00d94100051103006c0345108490b54108131a0050804055034009100e042c220800d0800000488410011106103c1899612004100514007800381c030f4a905074001c00c0001149007500c1c0400c3d4a0f00030301c400002103008d01021030440c926960a03203050700e00c1d00300110f080030f10b15001c00c4050b020140066668541d284801d07000c0740b005005210781c00740a42c4819640342401180100a50700401070500702c440d0521500d004107034441701c00700801d50180380a03121000030303041111100c110076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 737904784 1250 737903534 737903557
    0xc120403051c0c02010e0f191e0b03040b160219060212060103140615040509040c080d0306031220060f1e010e0a2d0209090105030118020411 62
    0x21a0000820a00103000704803000b1410b44588100c40e907000a60f061603840000a010405c440c90f8402e0034200703280724070f844040080c6412403030310030101c0c1e40d001c044040c0c001ca4100800c10f45075140f034030a450b240c2c80c002c0c008501100c2c510306e003a4880c08070980f8040d290050000d289038034140c0d02c502c00c100c400c100c6a0012201c4c1e103c49030790300d0041e0095018461521404904800060070356019124a00040415054062083c0d5920082012000e0001c10080300502c045c0000b2400351140c000d000c1c4194031648954560700d0070b280417585891110a1080105070a200c02800000e64044d200d001950003401d00088507824004240e022010101d030307443d560310030303c000c020f0906102c445181c0a07400103100301109041000010700c00000c00d003e9001c81000081c007240e925145c6501403000f005218200c0c2c01c00c040c007000c60036400b443c0c0c2400781310041d402041955062802101e00b60040008a008001301c0400c20140081e40f051503d000e88115910548c0307021007030f54a0101d0300c4c0403225 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 737906034 1250 737904784 737904787
    0x160203031b0705040e0d080f0a15080102091513091d010f061e06080c09060903060703020d14040b04021909090f062415180605070b0f1501050c12 64
    0x81800365504098400c843c411401c10717502000e031100c089030f03105121a07a6640c84002c1e07a40e20880c52040300010303102007110b5555000400c02c01d01ca0b00018009420038000141c0e84031f80c81d008100135042c0001d40844155010462940c0440000c3c2c011011581122004281c800c818003d40d003040000d45070f285e5495082201d0030040d5450303a801502550004190340e054001a044070b41205c0140e80101ca0114460601040b14a020580501904135005003101d00d80f22004c00800e0609106480740008a40c0112b80741700c3c0d405d064010018105030b0320402540914040e01c03204150f440140019014a00401401601c050030010350009030450310028411210b140c60041b9407641800000e03500645007501403a920b00840c45400c0900348410000440c0c0c0d81010340d07014172912001c40350014001040c0c58200c50f08001e002c0340008041544415855094070309050600380001800011041076060412400a04115420002c0c05007131a08903103400b901e8065615000341c1e0000c5003d140d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 737907284 1250 737906034 737906077
    0xe120c06040b180a0f020f0a060206100603020a0c0b15101d03190210090f060c11010908060112020406030503030a050601090e100e0702010b04090c14090c16020303 72
    0x140000e080340181d105400104031692074070319105890800300150340c0e01d90071044040d00850410003240c2201030008110340c41007081d2600081c01c1400680c00807015802010400543c030701602c40440040100b42070552901064007401442d2101e586001020340c1007010200d007032140316104e5144e40107005008280c650007030b030001404400f0101c0400440740c8942680321440c0c00c000c160ba180e81461605056041076007507003000108030300c54003c0701c108920b503880080d699001802c0c240007005aa1071342401e246450500d9082c00c00c441c03001c0b03410710004140c100329600f00000c00c1c1d41180c01042d00400c4c6040580300007400b410b00707984054410f103c0407050108004859100e24010361090700c1715041d0b90358908842860450842d0b100030b04807000e940802203140034804040d4023090b0751000080d40ea100000040894001d40415140015128803e10082e040c40c0c201686c802c4044810450f00e00d03017207500d008248280b0342c2d03a507908444540e250086403020030964155950341c041c101d50b082c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 737908534 1250 737907284 737907307
    0x30c0c0f010b1c17070312020d090c090504030801090b040204080303041a1e040b0601120e0d12020c1c0e0d03030506040c1d09071842030e12 62
    0x7140403554401c1c000401c401000a440c140400f084580c0006031007021460036900076104d40201000f50280400718000d8401440948010701c3c1100d0000b000240e149040d0500b1480b0481a4200280d01c600c4c0809000210ba0008001411a011058007040343e0074883d0200c0d02034001c0da40200094400403040c00100940707040d03840c032003842c0c240d00c040c41c903500c0d007070207150a081207100d203600c8050388400b0401203000790345166400f10060411004101030006d921084903946944880f868009041c44a841540a51070f807140c006958000e604042c40a004191544048100c42c80344040000762800000d0244100d80300f0301030f000301843d1585105082c05005010221103c070b00c91480c0030b1101407014082c24484e5061044003030420b540c0101c50090100411000c0c101e4000d001461a280c074180034841c61880c040d01444945602401c00d41d14402203005a580032440b1080280c40d4400e007808800d611481940c495290100300b282c00b02c1c401a04003005c41c492078030f800c800014282e8400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 737909784 1250 737908534 737908541
    0x51603050301081b0d0303093002010b0603060a0b09031c02030d0605060412150e0f0a0203010b0909031219060603020c060f010b041403030f0c0a170a021002030c0c0f01 74
    0x3241240107a51110034981c1d2074070301c4e500010020f244c0c4a11048030749004684203030700c80c0341c0f040e10440c4129828266500034800d00c2d401101c81500050703005581c0036407641e0a0103400c1314070707005803000c600b503040c25000111040541d00443c2d082e0030001c07071400910340e42000007004000144440039070440440800070748951050b88541d04490400600290a05103542220101c502041c05103d43c1c80881c0c3d52000c3d4080c0817950441042c0d211807100504031800e202c030a550030710440003060b500e0b02c90710615082d6200d8004840c8035443c144104080c4483c04001c0f241900b03007002c03000c0056a40c41d0022030111041403c04200305142400125003d0380690080c00c4182c070301021942c8903038846030740354506038007406032810740e02040c03008109110510050300850000142540d0400d020b640c1190410b4008c0189a505c65025001080c01e11403820070b1030701401c01020340d05142005502d0060340d0717803031442000445554000001030340d034101c001c00d40e4010312790130060301c040440b072204c1c25000c0e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 737911034 1250 737909784 737909789
    0xa0f051003141f06110327032d030301030206030c0c0a1a010905010e06030a060e010b0405042114090118030f050706020601060302090a030b040303020f1917040209040b07051603050301 81
    0x100500f8100108581d4060081301c6002840c00000714907203c0180f008031040101001d02901d412210390000d8407641d014843d0401104184001d000300001c45214041064400021030701260020001070015803520303c2100e0303000b14a440066603c8000701c9903035141000e5244040c0440d50144003149010240409080c101e03aa090024000c2e6603c0300144412058281c3d140d59040d40300d48a10300c0040c8070b03600038105030300482000080424074140450103503903084604540d6600c102d8200301501410108400c0205807a2600700b04950011050103510700c241c005075418002c40381d141c42546038054004202840d40004140039116061505658606490083c2000741c080c03100003164080c82842502c0d8209001442c00e902c251550b11081041000504180c0070103808214000102040381d00510003400700c0000326001d00489440100200b03005a00f1404c00000134040c8409031303413000c65568005800c01d1480c0c0302c40d02d5110f400c3d6864850b4a14108500c4000100c1c00c041c140c04c00e015604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 737912284 1250 737911034 737911081
    0xc050d08120c04051806040e010e1609050108100e03091518150403020103090501020f0f040911040b0f0a030e0d0e0103050121120306050d0f0201030b0a0f05100314 72
    0x21152203045001d44180104d0241540014a0b0021100ca41103001c00480c1c0150300544000380e41d040182e4510309480000d80c0303201d0590700990704250701040030ba00800c0100790101081246504141c0d03802d41f41c1e4164040101c066442d0110340d01c2c80242401100c04011009240c0d00445181182d0550181c00003080c0c01d54541a5422036031450401a4103003070038481c0311035480c4c07401d429680103400030710883c502580c5540d03082c806030180c440f02c04018089070103130406660310366141080c10000e44141d00d0046003500c900b80300c2000003a0b9070001790303060b100c0300401c8980c803000d0820381100140aa044941c000e80b0030300c006401940d8000c000400c28500030f90b03003448927a032950703c04c5800c182c50038000e6028004114841022071032006980841148516000c0307003c5035124002118440b846400f680c41c040800000400c660301445405a2134100b074800b4020f1602c1c1800c1e2042d07075030181c80b0f41801100090940a40248a80c1c4248200c520750b01443d4044c3c24142550124501140b08200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 737913534 1250 737912284 737912317
    0x1719060b011d030303010b070503130e0402031e0703060207060b0406180c021f090f05031c0e010513080c07050d0b103003110d080601030f02040e130c050d08 69
    0x4081041050011400d01400f03801940356901c1e0105018807507000c03940c2940d0901040c040b0403150501c8034900b60040031031084008550410340109410b090842c41c40e0800ea1011000344119040c020070001c044035000040140c40f0603145c24034402824450008941c42898900c0120345040c0005080b070300702491240400150a1861042e0f07520071024407165180c100700d8a04100c52903850b041241f0b110700c901541e01140d5016a940c40c51a00840601048801300d10190400c4280500c00c0d40003c50081000340113030300703111054464800e009800a0444500010074200c1c0500821001c001017a01400e00c06070194181081c2d10020002d84406114010020001a07041c10010203112130f03d81c80302d00b030035807114000034021200d0301000c8100d09000210903078003d440014001100703640c101e902e410089161074000141201d80410641d920580305110500c0100d072480b01581e48a0080001c80460101c5401d2103175207041e860307100540c0700b1901c001000402c09840e015180c84000e40d031151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 737914784 1250 737913534 737913557
    0x20313140705010905150c12180d02100309060b120309040b041104140f060a02031206090106051c091e0611030103020d0b19020a0e03061f1719060b01 66
    0x31a1650a188952400103084a6042c0528500041070b180c07000680002c603440d01800c0d41503581015190001d11000100c040b60341d07a10b00241c0000046c116100711110503108906a0001c0d8070590800040410550356080c41000c201c03603680200b00c0d02c1c80003030a440d000f8442002031941c07903012440c0280500e04114061030182054000c50441c0b0803004105820582081c181d131060340141400d1a900c45140c448927441030300c46800600e0680941d80c0036603910500c51055810b5040040c1c80b03a8022110f0000400100307a211041e02c0da03e400c2d1111a4207001c8508140c28050561030001a02c0581007030101404006a41d41181c4245c0c0b0841c0240a42100c00e446d0301400c0c0024880a50010080002c40001400b0340d03107002d902038002c8001d400f0100e18488a04200e8004c41e4078080417400740805c2203814502040040d62010142048855000095401040c441040d00c140313010080708a080c40c0c0121024454058a690980e140310100c5a050070040d010f021000300c6c12f03001c512840c104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 737916034 1250 737914784 737914823
    0xc0f12060e03030108060601110309040507080123030c21030a02060f07020a1a131410061a16051e031b2b030f05090a051c02070308030613020313 64
    0x2600c0c1242c220b40060031b210340c0d40d800155a040f070f0400d0b070548240020004543c180c1d40740e00c2020301070046c0b96955a000d40c1000c4078042c44101c030351030080707050100740800c4000350340014240c411548260380220303101c03170303060034440d000c1081c001482090300010450300d2030240d00060341e038480c41466181512945900a0a030b031180359001000d40032007440e0303140043c1c0d0f100031403040b50405c102000210706070680341c071010500d4581c03d81801c6207400140000d8069a060702070500580300c1c2004510703101092072007540e02445140c2150010a410740007081c1800801e1113001c100000b440c980a00802c007844a19840307501c007a1003021502c850203450004013a00040b00c0550361944045214100c0034241000e103d0032680a1600c201030312800035200c5240f1300c0c040e02d0300a076580d0004001c110100d28003103060009400c182d9544102c0909135a182e1a80001c03d03100304d90300300480c0d582e20784a44010480c03429004000d065498000003c3c410000084a48980000d0141010380b100c0c4104004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 737917284 1250 737916034 737916037
    0x306060a0f1505190f12150306090c05030d121103010b0d2d0207061a13110d14060a082a031908030103110303030408030f040c0f12060e03 61
    0x80c1e5615000010041c8807482401c0340c9140b000070300c1e0510606100d61050072804603000c21084c0b50010712011540010250000039400240c00e00103001d1103159050742104900d84114800070700781a07203680c1080300b88038582c00d0f60303400742034043d0035200d0304a2900000b4221041141039000094a0500c0141e03001000c01c080d40c0c141c03084e4104c890b1500031320a0020002e030130644600c40340d41c21101d040030799908010030110301c25041400056115150741c107040c01218125100c070202e46107090342402c000d41e04c0d011508e041c041d00c01c0c0c001034804200f006148040c01290050030071107160540700d0440d1140c0210749445802c0c11602d440059032030700e81154459440102000c3d800d42c000b1400001e075045080c41504150018086440c04d00c00000d0101700781c00d0408094494080000040c0103012a41000765036850702540150301d1030509a40700c000601c80101803c05e25500240443d040080000718000280100080c0195494554400040d03100c61131004a80c42450b08001540c501350100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 737918534 1250 737917284 737917289
    0x80405060c0a050306061e0301080a14060c041502070302040908030a1d0c0103090f0506010308040e0a06051302090f040e03220e0609060a0b0a030518010902131109120c0306060a 78
    0x380c403d8110b4403150148103058000c2c07620840d00ca610a00d03004294645038019500070103c100040c0345072904c500305802e4140110030042500c2d00014104400010003500b21400c81d84011461000091742e4070080b41000b410340c1000394082c2c20a0703090424005001d0117140a91800c240800441d0040a03550001e02044100c15074250055030b103070350466000390704c46940e90740038420341c4c0070401180c1c1e0fa450070000d098208031180100480d0034005000620b03000f551001b001501003040604000001c1e400c10040c44082c1b04507900010000c036241c03543c5000942c080c070003410621204400000c0c090320307a00a4201180f22020980315800032a00a51061040390050010110b15494180911401c180002c211a0300034203190000111213a001009022050040d68001020700300304811010540d194502c10940742c0c1498a281d0140e030b00c18100c800c500b20401000189041d00d80340e65421800350340c0fa01d9920003291640c192408401164040ba0b4034400c6054640607a1210100003810300c060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 737919784 1250 737918534 737918537
    0x3090603060b130e2205011b050708030f0a06030204140708071403060913080c0604030e0103140f090c1509041103070c03080601090320040516051614010903080405060c0a 75
    0x28010002e032030041301e015800c500074030840400500354a440280400d013060040b01c840c1c8d0b45011003100d01c005489010344040d00d80c9402c2d481c1c4040c90322070324004d01020b444003015000b041d01050491040740c0c001c000843c0c2c05001070028154104c180c68284e00219005004101160009044540b00d9010b18403841c01011544d419034440c4001c8c84820f80000346402001a802c182d14004560090080c1c0f9008003104006c00f8645018500140b240e928070982c039040c181050703151126441c0b1501300a90020070140c0294103030380e0ba030601c1454040d4161040c0d0300480e00c1900c801c46030200200502000d0f000740c3d824440c501c442151032110748411294180050104400c4000007842120010340001052501e583c01d151030f40c54000101504592994003e5100c041044003030070705016165101380d40700120900c16402d01c1d401703040c034441c11943d01f00c0d5484040702036013084a10f11840050ba14984000c0010001514000d005080c080d202074800784502c00001d048441f540d02150100c240303e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 737921034 1250 737919784 737919817
    0x705073302030f06060309070b0706020f03100303020721060b0102070e1005151305060318120c010b031615050c030a030e070b0301180e010207050a121803081b120703090603060b 78
    0x4c01c0c1209c00c1d04c3e00312140840d00c07290200503103015520480080c41c00342e60124281c41101c0d02d1850082e142c01e5881e03002000e650303290b044800010741d62074010417281c1d070072000c0030400e15800300040307081c100700f5000b810035030b061102407104100d03114902e44140c0d1000e80300540d80001300c0800b00d98901650b024104ca403403c000c0240b055040c0780000d1904030301406c680508031115103500701d092589195080d90070100100b446a041c1c04240181424010140c0c054170701c0a50040b540f8120b5240b03406a141100309d0720040d0705a440c4201e0803660302d0f41c0301009480e160040050018041c0c031403281484024070a20801285004040046034100c44100740000802031160110501170701120f03030b80641d0755609000f0100810303070a021080c5124800e2117070300c0c424a005c0300050007600030610f070480036101d00a000c4c00003030101002ca480710300441d400d2004110580d04042c0c5400068440442c9016010a03020300b00f5030848001001c0e07034801e480911641d5143c1d80c00b024540a03c000002d00340b841c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 737922284 1250 737921034 737921039
    0x60207151b02210a120905030d06120506010e1e01080a02031c0806090a0e16180207050c060706061a040501091d0a09020102030d0606080417030705073302030f0606030907 75
    0x15588001c01202282c0c4c05c016004076012000d44e0100c0d1902d010656081e0000104409020403078400c020180c00c0340d00f941c80600a45407070305a5915014081c0701d681110503004240c1600d01102000f0a0000030b110b242601c1d03860f04002c45d02d402513184200c0c02807060458181002c1c00401a14605010650b6058070a64845040183c2c10202038000c03802d6558404003070305003060501a6070001d90840d4480f20189182228500070140d4103030340440b20901c103010060004401040307058600c8001c4901d1500d894035810304200804d038991003890100030490040d20100720090280c03044600036210583c01c580d407040c24201c1198208540c00412a503907001508948041d40900466030040c0b040304d0502c035800701400b04580c80d5400070030200d2001c0081100304550311400a440b240c96109044c10b500308454098101d001d183c50080c03012880b4075202062244025940c42590a102c00c0401034258041809000750b000344c481086d41c0300301500095140c1881c00449000b150b55500900c1100d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 737923534 1250 737922284 737922343
    0xb04051306110d06090c0f03061d06180f01090f27170d020d06050d02060702091b0301060804020306070c08031f0915080d08060901030609060207151b02 67
    0x150004400b07540040900a03d545030074640b14550280c80755400004034510158405068400003c440700101401c00d101800202c0601d030008400031031164805805171141400110a1905500700b00e045d400301740100203412220340e0000d4120b40b40a4010881a83d680741040141c944041a8406c1c285002041c4c60801d0404880040054081d940034050300300b001500300c5095001c5a03014102d113802003031310341070725107644108001000c04940d60000e00ea0b595010940d54001d26402a02c01d8150f140007404001c01001840248000e044505d60340f9a10381e130019016a400b514140d010b48104800108080e000e542074408141d0000b00060442d600c2c000441c0d80b429683c0111208450010301c000340600c85801a5084036107038440c810724003810916100d281510400b001010001ea50082c410561103607007101e415a60030040c0427551041c80d091403000b074862501d001f8800c008000071074082c004140d0255020890940c0c1101c141c0f030904100b00d9030344104000078544545207046d60889074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 737924784 1250 737923534 737923541
    0x120e030604151e061a46050d05090d14210412080906220c031e1e02030316050c09010e01030317010312032c0f010b04051306 55
    0x54072800b0045454540b43c160008107504165040b014140c40300024400030b00c1c03030a1002c03209401c502505080c5014480780380741c10362014a080c076100c0d40d4038200c4800c40c040d00300000c408030300551540c07400210307480d00140658820300f80c000665142a000c160b41401c040b4036101d10146ca50b580c001017226146102c1260f40c400e0585100e5403c081c0c50108000302140420340c89a030050f55402d015455485004d8100c460050420881d41c11800030014080380810200782c4a4008500d050141242858203a0300b40c0400d810103007809000c0044000e06144500c0f0f40148a0f103d1664560a5016180022070504031080c1c003c0d4560428084003c80740c1c001d039003000305140114201e990303042c855004034030000000c0c0c00280e10700954031700600500d078202120890b5141c0d039000f030402d40d61558403840400500860078800b0992151304850000d14101c030718400c1c140104c0280810a862418400c0d07035080c450340c1020b12542080b20180d9145402e100d2940300c1c40c110180301c000c4840958070100103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 737926034 1250 737924784 737924813
    0xc01050a05030609190e150c0c1905160801020a1413030813051c050d0e01201204120201110a0206031b0c03120a05060d0503190e061303120e030604 65
    0x1428500c8401c884005175500981080c5643c1350060081600015680c60301900000c2000e040c900301003000704001c000004025020344540d0310202045045813406c242498900314640144041100000c1088181036006014003483c0703440e0610112840c2c1071300720140c040d602e03041c00b10b030340088030800c0410201002400e03a141e0f5031070200105911100011884454030141000080c050f8004030308000003003012840072080c60601040c0103864600007030580c45540c40700300ca075040c00c020b1284a2542080011054107400784000c0e01c9030307100c070304100c074080b0310725000c1c0d00050382c001c404c12100c000403a1040000360003614007883d640e280800310300d000c078011600e41c008410801089682074018400344c04084268400c040803810100c1c141d038150749020740b125105094840c20000003544c0041150f2044d405032040d4910b03102030041c2500d151034210f0300d9170b40100300098400002d0340030750322400c1506d119244083d07946440d0b4100311000b44005002036019071000c80802d000c02c5103400c01100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 737927284 1250 737926034 737926051
    0x70c06090204051f120c1203020f01060314010c03060807090c0203040e040b06090702010c0c150b1929121b2206030b0d06090c03051501080c01050a05030609 69
    0x1500d800c2680814120b801c1110820903490003069140c40c1c00940034007010003080681c0308044020b100340c992807044503185c4207003072064034125660300c00c06009000710600c04003031900802c040d03540c81c01c2c0081910045480c900855182401d40680e480c001d124000a850f006001000840d040c095003a000b070801c09052000e5101c2440001000c5046003100b44c0710305e1141d0660101c0b81000010302003801c00152150701964100f07070906403400d0f031001210800c0358004c0a41c1200301c08446500b0020540c5401c91904068041c90001410004810100403194980003503901c044501490b2419070300140307014002c03101d0410408038489a0307031028036004001001c604c4800c80700e50302c40030030940c0a002d40c08201c0071044d03050030803009407001c400010700c5035040030720000d00c0003c00541c0f1011900c8008060700c2c0e540307040e001405a100d61020185a000c011502d88c1400001c8000c106402446101401d2142c0d5400c0d034000e5101d4019641c02d218a6280c1c0390468461004002c6603d000520b00301c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 737928534 1250 737927284 737927291
    0x15070c0501081f053d0e010e0603040b1017061006020f0a061e0216031e0516050a050f1e19080c12040603020c070f1a180603071116030308070c06 64
    0xd038403000c81c513800b09921005c58018224403612024101e02d90303503c1801d0506c040c0f00b240c0d025079140c032001c49038459845408264190382c0c044940c09040415005202d90411005906881400000341203005101d44003006100642c0c4c1d1008980d61030304851903058540041a0715030000706140c106003c6541c0203513450003852040e001c428126001810200c460540e0b6589400a040e08210701001000031102010861103005801038807a108440d86482d80100e500b50b00c80c00d1000038822011038544c01019594a09942d4420b0382c2d442d61a90110000350758a109409802000061504001c07000607d01d001c00c000c00740c44240381c680240000241c24042e043c0d85200b50a440c0c001000501000c0d10b0068441c00c00310021860445e07260488140c40001c00d40500c6261025801c102c01c00881951041d03880011000c5149401000c112203a04060040240010203070408030b142c0d0b030030744910200c0301ea003021030581c4504008103210107000305200e031003c11201c41c41001d214616500072803000c17 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 737929784 1250 737928534 737928589
    0x9180b01051608091806040f0b09060d0c090204090b0306161407050a0b070f120204050325090f1a0108070f031d15060102011803120b15070c0501081f05 67
    0x91081017000c0d01002440841707004001c054600b502c29450000100342c010003818503032501049903918041d020030700c10121500307440c0070004d00402000103000606410741d00d4a0340d807580342d000f03403c2c0622114401c1c01010700049a02d140e400003018032240340d2380d45040c0c04550714500805944011001e582a000b000c1c0724401003110903490300e001d100c003580c8040c45041102c2008115248506484403120300400041195030380002d0803801c580c843c0c1c0b6244421040030708920448618951095142c1070611184040040300b540c8043c541e48500700062900c000c219004607051401140d45201052070400d901c0c1e82a0303c80d600140b01c0758101c00f0160740768190321721550303e4418841812040145100208007036540d080c0181005194000103000080d421030754044d044c2486421801445961032109c804d041d81d5566170301e2480403001c00d42e0356943e046800d100d5842401406081d020403414008266041d0400b011500c003040b10000d41500b09043c4010411a03480c410b42005905a00c0800c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 737931034 1250 737929784 737929789
    0x30a0c0501051305102d0e060f12090c011d0d150605040216110603010308070b090316030309030e0901050a030605041721010915050105030901090c0609180b0105160809 74
    0x30000543c0d40c9541186c801800c00030080c00c40c280c00d101085140103560304031919006201440e440b01c0444209072908128115000103002d510b030410708145c18181440000c01021900300d56442d022313a00e10402624100a2941c100c2c00101640d401146501c14030000c0703402c0d4000d540c0c03404802c080204902d555100007900b82c0c1c00c41481c046121011402600c100309105407440903004041c1d40035411585507489200050242d0040a403994800900041c3c41da0f400f80211a10411080308009004d4082d040090041c1031a085c101c0c0401d840c0c0c91407103050702d000410b440c100c950060581560500f1691444080c1002610071515809070000403440303054008040e08220454613540300000400820f859280481a80003c0c03003186001c2c450b0202010100c81c040a4501c282060356481d103440d1061030050048500c0500159a004004192642e1010701e00040340c550340102c3c9800860b0121400c1212400700015020402c200b20b0160402c580140210f0558014001581000e081401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 737932284 1250 737931034 737931049
    0x21225080d060f08010504080f0d06050a0906140d0210140702040f021c0e0a2a14040c02070506030a05070c050d0233040b06040204031502030702010b030a0c0501051305 74
    0x100c1c0e070030740b51500c2080c0010312480e0424801455004024003440c1056103901080c0e2198032003042407000f0005010b60785088980105d0018400035001d20400c80d41c40000d1002405e9a000e213205411140c6c001361414a84940f056070440d800901c541007403200743c2c000351190003003403001d1048500d0600c00100903944a108144c080a0590310152760baa80310843ca0340d0b694200e02c0c40441d07c43c40c210040242540000744003001c640c1c85062060007000d1440c2055602c011500d403503000c1040410082250400e544080001000c160750511046460100c00d030307210f081d1130080540024041c4001a045034045e00001c1e0001054104595042c1d00d984940d420070368250f80070000f5a0040080b070882d0005521124001e0541d03042490b000b55145512030304051014202821000126000c98140c1c0e4232a81124000c40e1300000407007047d1928643c40d03010f5001140c0e81c0e0055460a0f003580b10034207010402c080141e41c482800c0c99402e0a0400646083c0c020b845c9406180e05d030303458085404c3c1c0342d103074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 737933534 1250 737932284 737932297
    0x91406011d242101060807090e07090e0709051e0607060b040b100203120a0e06041104180302010e061006051c02040b070b041106040b0f030c190f0f02122508 69
    0x2004490f107011000b4040b403000c030040c2d1001007001445410003002d1941f203211442a0382c0111206100c50312641e40444401583e0340001501d500002d02740321400b500000c04800300c60041c1d4140e503040000510410004c0404481d4a4004074100810400546243d004d080c0d0482c00034070000d60004200040783e0a03a503404d5044c00581d00004060720b204541d030f10300582c050b0039600c0c00c2c082d004c103010340261039032005400140881c0b5054644840c0e40d0340c1d90800c10400141092240e46640c09080c02400f070402c81520300702c00d01070303140418601801c9003030300004d64080d0b8981354900f0007001c2c01c0743c84180311141140c0c0300540c00d102c04114081080003c015040c01911249907908180c28408103000120600520488040208000c50700c801019601c050070200d0440341c50350340b800b050303440a2084482c808148041c0314440341c4c2c980d42002503180c9002e60341c0c1d1175a0311003040e5172059070313502d82154644421103c20b01114603207000d01c0009510700054800c000911044640c0c407402e40d038202c0c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 737934784 1250 737933534 737933557
    0x31b03100305150103020d060506040b04051303080c091f050705060c090102010e0d0e060702040f09052803090302060f130b04060e0f0a0905091204091406011d24 71
    0x100c4040050000400c10190618501d0b50411081d51443c1d00040451800080081900340c450b00061800d903100d03400140756002c050002c0c042361038143c0e070030741950740d40880440200b510100418040d400c03900680e00002c40151003091145240d1240b90458020703c2000010418208504c500241c030902c881c2e03000300d80301d0011648401e09900003900b540d120200d9501580d00076250020b5803030340450a850400015201950780b2403440c0089405403a020f2191844039042070030807410014002400100140d60382c1c81034034140b00c92802a0b90418400b070001d000191001c00510240c0750410040004044010000703282c0380755905070f00554240e030f40c0901e1008101190030041181c02c0301c1d0074000d07840c08891490f102404840000c070600d21038080c060100d5581d40008a000350200403901c150442ca001440e02c5a54480f0110041c220a6440c40c140d01c0d13801d00031402c5035001e0011100120000801e00c151790f0301440900070702d21102c00340c852001791200a81e140400c5010010007105454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 737936034 1250 737934784 737934811
    0x40207140a050d03050108030c150a0f0603050604030f1d060a0314070314072c0a0806130201090f080309041515050409051e0414011e05040506060103051605031b03 72
    0xa000c000313412a0300c16408034060b5003007086283c03402980803070b101c00c84400c00c0301412201e444150412005041590320105400e01e0700401200344100059910301c0b07030b84265516407111250007812601c110f143d10315280407842801c0c10b001146482030141c03651110924000070740c0340a24a1400c0c074002e05a881c00e011130359403408000002807642d2101e84c08052401d1084080e00ea42180040001e0038110345010750060011500182e0b581500200080c800181100e000d0b00340000543c460b401001001c074085540c418000541c44021000c6a0840d90a48003440c10001d0070000d00c0090003408410240b20f804062021404007603541c2c041c400a9060755446403181c0c1000c201108131000507101b207080800821903c1380140c0d6104046902c07550143e070000c4641c1c001c02505015001d45510603042070150310f03920390142110ba010341c1c4124081c504450180d140c500041d000c45800380d8480080780420b2559440365070044004503000b4840004190301c0c0c03030303982c02c0c80c42c4150401c0c1d4202d0886103d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 737937284 1250 737936034 737936053
    0x30403290408090301060503031801180b040e010f1409010e06040e0111040513021201030813090f0c021614060c0a1203090c080d1b1e080405120714040207140a05 71
    0x10241310346c0002e0801035005516128a0000341100d0b0141c2822070b41c100201c241001140740820743c101c5000f0500c241d01a5207441d281e0800d94406c3c202402010003a0880380300c00146809603004141c0c1c2c01c107001c0d02c0c0c1505a401c007060043c4180000304180d41254803011400400c0b0000d02c9070010610003074031041d448604040401c410100b040c01c2c1c0420140c010b0083d1001c24095034065411070f5440f4091a0781e40c01691240300490265600004c2407903c1d01c1c051b03401c1c48010b608800f4050b03103143d00b920b007418030000800240002d68001c00081c50700750210703d403d17820080024141d4510440468070100341543c0c0b0100c88020341d8529200094480e8132403c1000640c41f2400040d22900c0090302c1c500c20100e20061400d800e003d8000b45034a80a0ad03580c003401740032210b100781c5000c104454400a1818185000503038040d105007400740000e10b088850382100030030008155100380496201090f10002080040d42081340c040c0c803816044c03000301907020800c00c2203042d82031050001d0b014400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 737938534 1250 737937284 737937289
    0x606071406090d0509100c050a0602130501120e2a060c0c0f090108192919061406130b28080114010305040309050d0f0b06011103040329040809 63
    0xd40a0311041c003440010f0117150016550740983e0041030358240380c81b5440c00510b0510914180442602500e810310014461041c41e000110390010340301c080e00c503160303401c020046102c01c94203074021140c00e43e08201100c07a084113002d812440410202030900b603000070b0f8000040c5840c1e11014030923400d42d0111150100078200203d9401c010201207a501400e036141403a01d41d12012214040c41071030300032000c207100308200c409124910111045c2c1261100c076000502c5286060705941101000130310045201d440e0005001e41016907418000c0052010884024080b680d0840010f030103c9214a800200e1010810700c0034006002c03001304004019294184a00076504540c15402c9c204400240140001c80e02030b040404141d50a20b400a860340d120b040c00c81d14103001c1d41185a104045aa00c00c0c24846242007018015010b510042001d440b000300648280d2581000c0c1c040640003407000700007003410600c050a051b110010800000c030704c841051491400c080320103c0703d89101050703d04060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 737939784 1250 737938534 737938543
    0x70f060b123f0d4217101401080a1e06020c06041a0601140915160b0610081801393b0d2303030105060a0503060607140609 54
    0x507040d0700a0801c3c001410080e003109022008900180099100300e0005542d490340300e0240140a240e44215080084031840307a06d03917245042084419081010201d0b10001c48103c03070307049401c0e0400415020000760317140344491401281d1580c141c0c10419064020034241e0006012410300309010704107a00c2d007407801c0d642c030010150070043c480001700c0407c41240d0308400407400c0c0f101d51440c9a510f61110384006110840c04403141084800701103208890180c5009205000e90311580805032607a8555050040b8028903207800130001d80724801041c0d590043d0200d40d207803480800000300e910142071240b085410004228261560b101847d0549540c41c00945e43d103110989190a04220360322410040043d2210300307500e1091084407045081208005501c440300110140c0f0100c100d0003a4104035070106101c404c4a001d14009004d4110161804400c4034181e440060055083c8110028212a00c3d04010901504907000b0811640894408801c20104103400030040029241520f41c59060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 737941034 1250 737939784 737939801
    0xc0102120309030906070f140304061b080a030531020a240302161a040b07050a08070e04060b2a010b0a030807020f06070f060b123f0d 59
    0x1085801d00900850100200454030f59003000c4403031759140c4000d405c041c0b8400741c00d40700003003002d991080d040040d1000070006c1c2045803038075201c089541d5a848c6001c440f00341c00c1a002840d25808000c44a45980a07130700c50380e040151a0404580c0081c1100034000404142c01c1548441300550b1481c0700314a429503081000c3d2400320410700b00c1c98003a98440107071044942d20700d42896004158008030301c405242901c2895040080b00c0d51940200c1030400017408240c2d005c0c0c0307082c1000400180c8150040c0c044911b0250281c2e0360340056603c0100c111080541d1648956116480b0132000949183c800e01030104501e011030301030000010039040e920341104e080100011a410211098a85c0c2c0d102c91101044903040716556549100c64130025031a40c15112080754001000700e80c607003e000e41da40081c4500391241004004140c0300c070b000c1010000005420980541c400c040e02120aa028082402e196140903024030b0800c60a2010884516480f6480708020780080f9030050405403602450b041d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 737942284 1250 737941034 737941063
    0x30108010b100302040e070c0203010e03130302041a0604170109080a050306120c0a030f080d110c011514130f0203150f09010501140307020f010c1223011a090406080c0102 75
    0x50b043c80c0042c045406c003c0206a102400340c201300040647d00c080d000900c581c0c000324181c99a401240c41d104560058030301059004918024508040c5500340c40c0c85015124010941c9040501c4d0005403607035421101e12054036035407900d844500080c0c111000c1d00c081c080c1a241c00d84c072032900c442071285418400900d40c0a581c4003e1800200c0e88070030504009807034001c83c080151905e941041c1032944105120101039914160701e0040d1000194050700382100c0c844028410441c0d04003540c041c5c0b00c1d050040c1030410110f603c842100e4070340703003010340807030301c4080b20120b0030b41c50b0403003020100d82007100c1c8941c1484c50b10350f14581c18504183c1d19402c03200100d54018455040030002440b50207c0035030350000c09400000f01d000c0900812500024031100e400038400c4900340d40c0000c042071201600303031041d40d082c0b0718002216000c000c0c407155650344e00044800742d03a1900050400618580c1d00d015004201008070701e241c1c0d1914040d0344007411004000b80703100803201000a113013000c501e50114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 737943534 1250 737942284 737942287
    0x2031503011e0903050702091303090603140c18100801140109031e0f0b01080a0c05100e0616061b0206062e120c020d02010b03190213020906030108010b100302 70
    0x3207035180060042c14004200150015800300d507480d060f14944682c900107540710540c0c504010340d9010b1001074449282c0305c0c2c1d542d01e200c20341c1c03184240c1c281e490010307141c01d054081000080d62080184081d00d8100450250144015541030210b1004401c080e0280005801c4030f0050005031116003165071546030030728100501d42d25540300c003c1189003299180034101034119123401400302c8100d9800d2802d410401210107540e4864031036036a25880c5c0c130700310f4803145801c50000d8a481c1c003640c1c1c02c0f03104001d91542c01c0d0f5410751350b00700601903004c800310340326002308000c500020030b00340e202d81c416111400e800990203a00c00e2401074a0960002c0481c1d20416000075503109001c070806501400115100504003c8012260241c440b80d01824001d4055071500741c6802c146517000548500b00105c036002040510b002006168589111a02c042c810560079141e000040c1040303841d003411340328490f0006081140301000a2455413080e801211140c1d101c045030109031034005c2c207120101d420382c1000c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 737944784 1250 737943534 737943551
    0x10f060b040303080a09020303121e07090605030703050c1b0f07120206040911070609030c020907020606011d1903051005010509011202011b0c081e0706090513060503030d0203150301 80
    0x10180c04005100d110065141d1b9400c0c011500d0030010703030301d0001e1070b0388400303030035140210340b04c5141d0000010005044640e03401080c00580180301100907a007040d50382ca0311319500c0d80000c1d0041c00010f4038000c4103050421050100c0c20803103000d100c4004500014140f031264070980c503840c2c40c40742d40101c01e982e41104c0154006030b481c01c003120308590ba4442c004c074600182c28030920b409e0103485000f420250400481c0010998401d4801010601c00c4800d00c2c01900e0b10002260348200440300076010520580301c41581c40010145d40c19420001445800c5050498030b41b03450001d111390003100c081d4000466200c807180c03207008445c050300c4140c868078040d40c9844403c1d403203402c03984c1019061102c2c00080c43d40010702030320b00c1d046040d048000103580c56079400000b5030301d40c0e0f0b0080c200c002288600780100342c203801143c864100d40841c0d031400300706802c14003080540c90141100c8405240e0f5400c000829032414805004c42c0e681007440141c403894442e040c100d802c0300740b24100d4842d03450182c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 737946034 1250 737944784 737944787
    0x2030f030405133e030103030e10080c0d09060603021207080d0206150904030201141501030e120d0c111002090f030a020a18020c0a0803010929090621010f060b040303 73
    0xc840b074541d10304090100d2000140600d6031303524510064500e0403000000100178141c110b20ba80c200442c0c2a1215615400004002c0b9003c0e00190b911030741007501003058108548480d080100c0d1280140d0000918540da0f41c001601080704a50481003900000b03c00c00121000b8001018100705a00141203d450aa0700c14006400e103107644a208043c0304002ca01414801d5101c80b06500c011030144201d4142519501038181446d417a20707000a04001ca10301c01200040380d4400f04074072403140c8604108011032090701502c2c2c1c070400c2031704120400a05544401d400c10070745c8000045640c005a4824420041c42205611492f5140c0030f0360080081a00603111020008100c071403401220310030303005244440005c1c0c421448844036920803803c0300c03424041604000e5040318000300c02000340350400d8500c0c14440320203a0311543c00c510060010505401c00010455028034020019041c51881c4010034070007180e4640701349050382d9030300080d104048039072060307002034958280e4441c00c09145540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 737947284 1250 737946034 737946071
    0xf041b030e0601120b0a0f0c0315060906050f0d180b15090c0d05070e040c08010503060a090215030403181d07091a1c05010b070620090d050a02030f03040513 69
    0x78010305c1002e0080004003c9001503002102860348190144124403950704002c0113070115002c2c1d50071400d006540040d4103400361012204a8a10342c48603403c124203440754005641154180612490b1100d02c00c4240070300404505103101d20a60800401c1d060204440080f9110095050302400c100b0f8203001c0c600c118030302a940c0d0307000301c8000426250394a078005c0300c07000c0420f02004d82050404074000702980c0c0000b108c0d4140c440039012107516a1300d811505042e61003441c4048d4014070b40d4820040f0000b51038006540c401c1c001e08150002c2040061000020506503212405030300a9400d240c966585100220341c2100003842c011403018242459801000b8032030980d000303550000a03640300050601c00d114081500b0030a020001c540e55903071180c16951065070300701d9442d440e00f0724a44250503030710140300707000c000011480d04100c000010301000400d036050031707152803080c40300340d20042c1c1d01000f02c2e0080542480c05503445a19180900a125400942e850442800c0c07580d040d08a807a0502e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 737948534 1250 737947284 737947319
    0xd050d0209030f190620070228090605010f0c03051b0a02100906080a0e0d0f03020c010501060e1009030f29091c050306030604060b0f041b030e0601 65
    0x80059541c1444000a40341c900030701c0d001c103000d00a2050091000c89080f41c43d5030894010031060005508441c4042480d0025101351340c3e49100510405c00542800e134003408980c03e8001c5621188080c44004a41c0c40041d030780002011520f41c0001c0c0455648009050600c0c1301604002c540c0006c96640500540034003404481150a0f40c00c184201e00010046020f01c150003408240684214500c0100001628001e41c0045100d00012401e0380b6124420302c030040308040d024020184075010200d8082c2c18407010801019021711184203400420320819000f0001c0c1d07101d203100280007a00b4084040c5051003e182480b00b80d00040012980780d505141c4c4040d8012400c00c014110581d0759a002000f524222903484008000c004c1400070018136030340703504a4034180a0f0a540041d030102c665200c11140981c00d500b091011a00050440d0081c4450300d200510544400b510500420102d80d01c48094100d00304e070300c3c100c507801c10360584540584090504050002d030741c1030502a1034000e4a21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 737949640 1106 737948534 737948557
    0x906011205060115092706050f0d0f080c07090b010801050618040c020f0a0303050a0e0316080f0d050f250e01051806070b0f06030d05 59
    0x31160034000c5600c80010b00b100d030b00301810402c0c101c203140011002d0183c1c468003c2000d802529000c0300c910001a40400380c40c0c20314840308250384041c0d020074083c102050001c0c48948407610045a0150000c42c10803e03042e0502c0c10340550311a04450480d10301444402084001c800c0e0464110718809981b01c00541e625207080040781c0c8540142100954481d041000f418181500503c000c00014015621076060780c0011070b05200300c5040840001c3c0c0d642081200001c204c2c8905400140c20500950034007140300d03c00c01c4001900d000250120f200401c880c49268640e504403070b03008002c03403c24800ca00701031f5070b43c81d010041514400500e4102350014401100c0080c04105180c18035030f03421418a40e004015142c07540003088405601c0c3d038003496915203894002c000c0a4081c0f240014031510700d09038114449070800070b4041c0340b190304141c00115145900100fa203170f0000c4039 = true := by decide +kernel

theorem cover : BRFrame.Cov 737769784 737949640 := by
  have h0 := BRFrame.cov_init 737769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 737769784 ≤ n) (h2 : n < 737949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
