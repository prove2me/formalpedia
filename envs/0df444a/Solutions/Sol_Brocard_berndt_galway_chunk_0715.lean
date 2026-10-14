-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0715
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:17:54.702997+00:00
-- url     : https://prove2.me/submissions/b21d5b20-1d67-4e96-ad52-5ee1748c677c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 128417266 ≤ n < 128597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 128418516 1250 128417266 128417273
    0x12270714010302040b070305090a0509042009060a060305040c0b032a070809060a110709020715020306030a0b100801110703030b0d030e01050c0a060c0206070801091104230d140106090603 82
    0x440713030303882c7e00351030441e455660100000e03140003a250f01c00b0340d01140c0d0b0418002131224108284000c0400071221041c260b155805019110b43c040701d100e5400b2030f0381c80c3c080004034042d420056116128a04141030161142000844c5410030740e0100619008401a01801c401040d1035541502c2c0baa410b0606051003907680b60303071a101d20603040f800b40350023080409509001e90a0040c0f00c900340015520516180c4e40c101009401150007559000c03105080300130021010b20031240034070006000740c954078900d0749603541c44000142110308100c410142c00111070500307100e1800890003d0f207a85513104101c5c10002c05a4035082e250b240300311160000c1d440081e0700070541200c081021308199442c0c2c0003580182b41040320340e4030090500340c02c024030744c40c0c2503a000c16158840c050603241c5500698a46005804036088891040d02400041000740080e044c14000303d4680031902c140d04640035100b0340411440301c4004401c45010301c440344952030020003800380c00f01800c4032030010040c2c00e00d9a213 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 128419766 1250 128418516 128418539
    0xc0d020d050405060a050c0a021201020d0606081e04021801090506010e1801170a050f06071713030c0f1e060c110a1103010207020a060503012105031227071401030204 73
    0x102c0303090020008004c042e170b0f001400303000b2481e6001080840e552800ad08114043d62021000503900b500e46000442e40d00c0c064041035015031070b03c0e0166558079001c50684e804445002d002668080c2c40f907140f02440d60050300364980070741101c2502240c0c03070034001c0024010f060b00b15082c030312892203844c2c001e01c0c0d90420f100e2a811101441c50032920340c8c082d0603d09050901d6820042c101f8010b020608001c2c0300f00285080c06203545684980150442610030700180d002607900310001b1007501307044d5010a100b01002da080c54010548051245c40c0c540c0c40d000e00c104107050b649060340c5101c1e054010b00110788108803226595050107001c01900c580d03440d880340b01503800180741400c0d0f440782c00b403503480960540b840c0340d0780075016190744d544903c00074205400910a84c0403180c07195410500205c0b4003030014005641c0f140045007071001003142403440500092401301640083c250140f1a03280642521a0480000780509800790410140030700034000100e1741d07170505004000030032100c0c2021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 128421016 1250 128419766 128419777
    0x210090b0406050601110a08030108060a18121b05010506010e01050306010207120c0b121006020a020603010333020c0606031c0c08040504060611061f090209010509060c0d020d05040506 81
    0x884005400d940c0e4200503034406d24110706511161080c0b80c0b0740b000300941000154140c40c4101704541d05076071250080001d44040015211209044407200d400142d0f407042c030084070f00c5150400ca010141200c4410200398a01e01e41500d1f9a034448040c8003140d60044e0449282c0b410a280c81481c42c60290000f033354400c2c240c4215981048080d00141c140000708030b09501030300d81e29480719038409070090002072444054404980c003224125000484a000040c6004110340c0600154216841d5849014501a8207140113581010b417040e0054101d10011041100801034600141c07a00b201c5817400345405001444240a90302110000b88030600c02c142c590040c84c1545032041c400ea416282c141c00c0e0780075980c0900d400a0400c0e80105d5947c3d08044002842e0711240d040300d0b5590b480e82071010003110500112040021400000c1c003030300c0c00f03a80003855886010b0612910f0304a00360081109580110802d086680207040707020090341e810b001c207a01e0500a40303415070401d4203041c000b60052060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 128422266 1250 128421016 128421023
    0x1011030712171503071503090210090609120b0a0e0c03060403030204090605030f0304030b0601021c2303060114090118140a080703080d0225060501060305010803041206020306150301090c0210090b04 87
    0x1921086c0001c00e2081c1c001c88001540034286171064903141002401ba2030541c0111800310b6800130740810400c0315914042680d503042404501540c4541104100400010170501e800d0300505c0001000c6e503d0400141c0c3c09940f00703a40050740c692800d4104800c48040340c1001c2c0c802d40150100d1301c00410000255029039810042001c1151141c00040c3e280c54040307940c11111030221401b2001040d0080c20701021114645001002010720a010b460781d88070803200c1d2804520100c234022510040390000d03003140709041c10f1412110345120003502d0002c096511804519402c0d62510200e400c01007280d000910401005145507825681d807000c6038002c56800b802c140e5404925990b01210064400c2c81d043c0c410540000c0885040c20b114000d80000d001d00c030b01081c01c00300009040200001203808413242c2c84e091024282183e13441401079030029000c80d0740807054404a8030701094550045000301b208440006008081035400381c102081e00003200c466500d080300d0070021a00d00d00200d40d01039071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 128423516 1250 128422266 128422289
    0x330303230909010308030f130b13061d01020c010c03060302031b0d0204020c0a050705030d0509091519030b070c0314070201090b160c080705101103071217150307 71
    0xa40a14201140199000a41e00a00b444000428881e51000035400b502c01d283d4007001e603580f1745042c4a42d40d564001c1c02000d19801c0c1000500c40c01e229480940c00301d00c00c004c080f9032030315181c45210910b02d803a000c500c80d903540065034230005042445009042a03150038244145c0c0c1c615000240c403807880c0c1400f00c0d42c81c260048400142d50b1103150810f01c65600800031900e80404520040c2e840311401c10454040c8554003020605107030000d0300001640d61aa03905180c600c4580c01e12481c7c100c081c00d00e0507220848120255245c0e00c0b60070754181003262200b100f0301e132451420310300320410707000c0c100c8000d000b80c80c2002004654000018140c103200301403001c0e40c5131100e00c0100c6440314a540107144e91240820000d04604041d0340102195020b4004124001d845a80d440e481d07004a1140a03400540d040358483d425000751314002c400c405090690b400c2102c1e9440b8555503000c1a5080340c00913a016188103410404021100d0f00042e2090010800460301e2000c80c0d502d20f140d0140c80420311 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 128424766 1250 128423516 128423567
    0x30b0f030d020d0f020f06040c1403011a210f0a0309060302030c0901050a0e03011514030c1011070e010b0a0f0f09030305030a0f110307020601120506010302041e330303 74
    0x90007081684940c1d43d01030300311120352826083c4848031207092b015428103da00400d1054480c5814004c20841000c002d00307480224001004001c0505402c2c80301c00411300c11b00d40131030620b20307041c40b18076170502584025251041c01460010210000350b00410103051061061001204907542135464000080c01c0403a980c401020085d500d001c01030f2101c40e450340c200301100d01c5031604c01c580c0c0821900040610340c41401100c0806445641290b00ca6401420541c00034886d070384102044051102d1b04800d03944515100c5041c0200184241c001c5030910100050b4200007a5211000c0b51a04a551a000141d60300030140103003040b0692001800700100440801d00c0b50030036500c0701e542c1c0a0390610070407040c646002e00d100315400481d0300d10003600400c4000038688031144120020140e111003d4043c41c1e00710303800c01c40106034901c2e078104140301030070042503800355601c1050fa5480040400301801843d004108100301016110038516900f02001000000e400003100d01c40d60f2080c04a004859 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 128426016 1250 128424766 128424797
    0xe0606070c03080a030c09050303090319060615021b010305091c020313060c051b090a0c02030403080a023403060b040f1508060a1118030c03010c030b0f030d020d 71
    0x2480305400103045003c0000e4a40811a0150b1000d000c40e0000d4641d9045c40390384400f0143c9038002c0300b0b49190140c00a43c0001c500d240c0c80d180204150b48038050020b209a20380c04000200c88000070075078050780c000414a0702001907290001d400d01424030b0117102c28a801042d182c0ca80007540f0031541602c4c1c0e5900c81c0d1045030f00034002c0d60094400f07540c820001680c0d5040c018034031081d2020030f0b101c80c02960400c2c0000082481d400c2c043e40f0001e042c0c055103444020070080246a59000078086000a002c0032001408000c0108100070700c9900038440c0700301050114110840d905891034032034003000e04034120001c254100030200c1e500440e00203010b041c0800820041e1801c0d0384101e200a00d4800300c58580d0244c080c01c0810749100c5000c071070303565a585100c0c83c100c07080407040e404190302c10300014094003c1402c0e0035480340405002e0307070b4040f04c10101183c29509504e4114002c2500c40c10001510f0030800b00d07090a0a00440c02013503060031041f400b03900c03025941c154800708244291042c0d6034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 128427266 1250 128426016 128426033
    0xe0609060a03080a030e12040504050c03010807060513030b150405070206091b0307030b0c19110a0b060d06050f091011040509091903020d120e25030204050f0103060b0108010e060607 80
    0x1aa01d500340c4420100e400700c8487c1130741c000d019243c03141d40307007402252815240806807416251300b000100721541c00c00400342c8107500800307041101c641b072000011001611621040780541140705990b580c03040040c1c10041929801403c0d0003c6510480c00c002c0d00150015509031300c50040b00c4e18500b580d001e40082400d01e0cc846c1c01c0941489003103400d000a071743c03014004282d40c1455a00468220069400840e102844007440b005142e100e01040e00c0803e5502c04a20381103640105501d00301b404540c0d0700c4c6e055032412500000aa05c00c841000354250041c002d42c054040003080401000c0207910050183d80102d0154500a600410000300350580030040b00c0000201a01118074400081c54000c0d900ca4282ca50103000035070313040c04e080300c1d04c0260050890310110b050252130254800034803054040b483e4007159180350840d00000002d40c649203e014081d110070050701d0301c40d6066051180554001e070325650f04110303009004202c10f03c0d500c0002c7e60041d400326182c03a40c400c0c550610344038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 128428516 1250 128427266 128427281
    0x2090a03020405060411160204060e0709030303050720010603170406120c02030705250f03030c17040510091d06030303010306050c07060c1806030c0e130f0c090e0609060a03080a03 79
    0x6031401c000380100c9500a502142c4449520880d81482b4a0351504244035001340d094510030f01054810000b480040c0c0641c2003a030303100e445803a00c0c1c0005030741c501e203400e0b40007404880c400a07651348200034410301001030407050843e4000081a407505150070703402003841d8260102804550f5a0b2030301c00d50400c2c4213100701d402c5190840d08645006079584a000e84041d140e0400c0440fa41d03540d8400a80a226580b800045a8140d01e542d94107540c9900d4071a00d42c0007aa200c48119401004089010703a20900300d134018503682c1d580c1c0d13580e282c20070310082042c60340a11028500d4000a0070070401c4e9500104407410341f64048004a5552100001039074a4080e58030024019810180402400e070b40c42480780c038191280c1c41c1407070509941e8440c142d04642110499100041c41810101c416052008080fa00012a060005961ba0a00907801d08a035600b884500018040007070400c5448a290100c43c3c102d1000ca0780589541403d0b0005118400f040c40003c1491034041602c040c1d850103030740583c070b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 128429766 1250 128428516 128428541
    0xb0f16020a030602131e1202100306030b09030c19081c0603230105060108040c06030c02210a18050109090c0c0b040506180a12051c021903060902090a030204050604 72
    0x40d16900301403605c449010150054a881000d20050080c50220713162003001141d061000220840c86180c0911000c0406034070b401e001e0580b145030000001c0c24003a1380610817a101c0c0c4c0610785500c80c0785035541c10074480d00080c284202481901078040381c4020119040c12000c000110300745041c003240200035009503407010342a00501240c40c034011700d107480500700d46c0c0c4881000308441c0c1c0e40c4800544d0703501410355010f41042d5139000c007804800c0c0698812059054940110f50300424036130080e039107160055000300040c120200b0755035002a0400c442c24092001800000d103021304040000300200c44510074200302a0310f941001048078050b1030b6a01401e038203c41014407600d0700741401980c48006403414071030040c03250b4000010100100b02000c5950344140300c400c103961050f0045955801ca1040c10300c42c5600c601250092011a10080c0301000e192a50040711800c000c10150440d0000d41c44a0301050041124456030380d1410304030002c1c0d03503040b1000140750300e07040d01240013441000a41e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 128431016 1250 128429766 128429771
    0x12100e010801140601022a0409150f05010b04121506090f051b040f05060d0e070e071412060d0305091005030411061309050c0904060b0901090b0f16020a0306 69
    0x400c215030107400900c0d1407800f20f4007042d11626204012607440e0803201c0e40302041500c8109642d1051120540e44001fa0402080412001c8190304c85821205e282c24200d40c0340c40e520320041c041714800c6e0240d58014030760066020304107407422018000310a40b01c440288800c508128100400c40d40ea400300014206002c0104100b40c841c0502000030072081d14010056025214101d50440e55403003120140c521844000c41b50320f01e84401c1c010079402401402000300d46460884103c3d00c070400001c0000c1c50b040b02203101c00d081481c405050000030740c05241298004114080703e200000d1802900140140da80455003c09410203c0c1c050003980b852036031015110401a10140e801000780d07008a0282c00c850016411540030042148243c1550860281161a0400100c07105500c42c1d07a1110354105801e261500030303400034007224003642040c0b405903800f00c0c0c424069640522604050034820300d0503840c14195140410080c080c03242c44100c0d1000e44180030381103488100080c0002c6920030001d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 128432266 1250 128431016 128431019
    0xc0703091802070b010522020d0b0d0503030703050601180302101103040803090102070906030b011e0807150807020a11101206080c01111917090d06020a0e0103060b12100e01 76
    0x40c0c01070f40c010302c4113558506104c4004100e600e00b060703282c0c0c00f12410340c0000c02d011903500e6080000c3d401c030344e080005880c0d90740c000702043d8403108031001a00d403049018540e23a240c01342c1d0283c21610041c5c030302e82c10090010700070090b042ea91280841901e4040b94601410354400d0000c4131001c2c202442c070065030001040000b4001d8002000d441e504d01c09030291b0314103d1f15400008101c0d852840050001c0e1743c0c0c200100680740d02c1c100e00075240c05c03054043d455407585a8000a103030401580c03061150015040e20400320b41d80c80000d03c3e40101403807000c1e022405241d250361101c2c546004e001c900c00c60750b08840303440003406034040068007c0791040911005a0306c003021502c1d0b00540b13489501184110040060700c01e07002c155080729080d00c0d004200102c031103494840b092000c00c081644e00c40001c0148002503603c060140b0f6138a80318901c0541d4850010300c0003401d00b1210203d06042c1070504000348101c3c840342c82a142020449c0030524229611080035010002c0241c2c000d07107401320032500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 128433516 1250 128432266 128432309
    0xc010e03030108120c0a081e0c070f0b120412020c192105060f1504020c07090b06041a1305190305010501061704030f14040e04060c0809060c070309 65
    0x81d41c1240d000320240d40300d48032107031101c0314144a070301c00c5584540c00a00703410703000940c488064036200c0003040c01c0d4010006034600011181e8440b8010700c0d1164000501009507041ca070030040044c0480141060509501110341e00800c20301500042c0b190f840010074080d828400c104802c0220401045406148410060501d100c2c546006240d2541c1000c1c1180c25002d002540e50700307019074030400401040d601e1b402c643c20620005800f0b60a41100e41c03240f0a11541c0c3c6001410158509801426056141c40b4a4a086951180f00f0b280101c10521007005030320741042a030f08005192110302996500001180c11141d4400c0c1c001560203549844c1e00344414035148411416248107900130803140c0d03280e0754240c40c4150040d26082080042c040009d0020303101d12401c0704e891919041104fc41d044807909001e03280c0003070300096074403100c99003017000703220180c000c80380b4040d8581020f8600d82000c0c10450349401c001000c011010b00c001540c2c00800d4402c515582c020220220351009a218095 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 128434766 1250 128433516 128433523
    0x60b0d0b09010b0411190207030f08090915060d02160501060e041a0f011712040602010e120304050a031d101d010306050105090d110301110915040f0e0405030c010e 72
    0x8607000c201e90301e080e4810f401ea040a00c11181c0300f07082030304600d08102e1889104080b00402d28a04021030044100000c0020100203440351047e00c644074682d100c41548080c4405000010044070316801d124520b074000c0e80300d6a00b224005501c910015907034000402c10341203082d0081000801940c070b0040c000585c4c0b01040f00e868002d80c411621002003410b0501c000c002c5000544216125400b0400100001400c28511100c803000c1d51080c1c441940e0031400207020798100f43d10000150751038401c2c02075200001d014042c104001c3c074007241d06600b0305445440d0303900d180080003024071404071038007808043c40a034111400c000c01002c011420554050080c1140d0380b03030315442c004904c0c60950004540c000d0080801b41c802c10b070f49940c2840c0c0000100400d80b50000405d84030f140e4a40d64895168400303006010f101c501e2114120b994042c100300303106280800c15080900e1b00713802d200c28400d104940e07460070121151441895519229810201d0851003500c42c1100e266182c2100b21300007c4020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 128436016 1250 128434766 128434771
    0x15110a12020d0906050702090105040c020c031c09090203101a040803030106020d030e0303090c10030f0501030b040b010b0a090302010f0509030a0c080f03070b04020d030c140129030a030804060b0d0b 87
    0xa0b0b58143c07002d0b42e2200141c0d180d00403088000c0d03000e029030b0010b0101e414560300ca4030303c806280c812501524080808a4140043c01c07042210f0089020341960721b9070381002182c4018003454908619620307005241d00001e10660241c182c0c8854551011403100c220142560003030141071081c1e90f40c86d655003d020750355446c04900c48020905009200c00341c0080401520310900101000c2c1c0741c1d21010004011401640410706000c1c10390f04e00d00035804001030310030b8501031480f4111102c0e407810941841c400b501016400b10065140420210600c00ea0007400303481282e6080c00d0030031003031041403015100e0340916580280c00d0300c00c0c80d91481c03e00203510110412260b1107025205551070104402d505c07031003490005003400019802080041c00c10120311640d9034040e103000580c40025681381c0d1000c0c0442c00c0c2c020982d030b44500c440c05006d841011115018021036450913814855400400d45030310604070003400b0301c000d100c00039085c1316141d0806490700200625001c3c031341c003040c5400a0214004d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 128437266 1250 128436016 128436043
    0xe0d1b0602060615070201021005040c0b040f051306032018090102030a150b0a0e060405030d05070302060f0402011b1505070507060e03160f0602040b0d02070506070915110a1202 78
    0x1142800000f1220038402c40d03217a150180c2c040e000d00c4450415200152001500851303031400042c1c0001203150742c1c0307000f0340090820301002c00f0804c2c3ca03183c01c01403c890041264040c507480e03c50300f040010303a10012061107803840c0000d61070005a48002030101d04800300700c44050341d0b0341020050030484c1940190b225a02c036800070040c2d03034030301d0342050a10800350190125110041000681050044101442c0f42000400c01d42c609911040800e060074032221940000c0381000c5082000c054043c0507003944401c4554000c519441c0680000b04140c464210740c03101582056081018086001d900000c1c5032000e0000740051f040214005109600000095990b41d00d402044001c0340c0001c011111508194022040c1011281c0c8800314440a12201282c61941c03c120008449001c500600340990b0b00000050301c1d2140360901c6810581c0007008001086280302d401c0c01000101d4001c12412403061410360602c15488002c1413130103070801c40140000d010100310400403a4000b8110110409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 128438516 1250 128437266 128437279
    0x60c03051905151c2111120f0a1806080907060905060301050f01090306050103030507021e0306040b07020a0812070906050c120901030f020712020d0f0e0d1b06020606 73
    0x540c81200c0c4100c54040d03600403001c0c9016030000203a0300d04940c0e1303051044400489110f45a0480ea21043e6041d00907682c0000600300d2144180d500340c05c8080d041c080e001040142141a400468180e4640b048000c01003456a02048156255119200c0c0039160a56010441290b5458000c0500042002c5030146e130148624076010818503c6484203404440703001c2c0c106400c50342820100b0040e4030030f070f4601904011304c0c034400102184903801003600039802901c40c10b540d1200c5005100c5402040d02a003251421078811250403030f1400165190312a412001000082d11030010032420064000c1018100610103d09402c0e415481e040d054090501c07510703076200e0345070354400c01c0d5094041c4510000c4103400401c00c0000b200d59040007440500d1051400040400307000307110310100d03044554181c405a629011a10140780c04000080d542c14050030302c04c0c007500340101d0051030124030903a401e02910f40c00300841c00304251821061442040d103800050b03403c0d101c0c03000170b40e02d10089805612409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 128439766 1250 128438516 128438551
    0x1091a0a051c09050c0f030712020d0507090e07150e0d1e081314031203070201060e01090c020c010203030121020d05010c0c051605011218061506020105100b03071407060c0305 77
    0x28107a0301b20301061070060094103981d441c00c84403403e0030702444010f9800c2800c2003038002c000b407003e014010181101d07807c0007a03c501d9035000540b410700c603030300a04045020303007440307515441c0c20840310240740ca800c9a042e1074651040c6006c030209042c00c0300d43c0340b0701301d50b0001e90010441d0003c041c107078220b20840c01c03203145030ba240000c5400b540d40310f180907010380005190010a00d545e80c02940d1101441c0008290a503644010003160042640080c18541e9504903038a6180c0d030501115203a030000348025429541040411a6001841060385065050903480d00b801c546a505c80c0c1015940c02a00030170440300154809403c03215018011203d9000d250300ba01250305008200740103403001a52502c0e100c28101800100a0124106030044a00d801038030400040c0310340603407080c030700701c071441004414075245000c1c0c00d46502401c10030390030034050000d00c1011121030503258400800d280c44021030b510310b07180340254420785202816842c20800780c0e0306065055000a03028411144804540380d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 128441016 1250 128439766 128439769
    0x4090915050402011707090e0705030103020111011406060c0f0a1109071d09071808010c0f09050d03180902120115050c21040815070e01091a0a051c09050c 68
    0x118000c84000380440c0c03c0f00007800d010441003100c164030500314203150745025250b900103220b1120880300d09c800120700100500465903c40d0305240440311030002484190406e624541c1c400100800241c026400855410481e0302c042042229802074a026640d11b130341c482c18000d561200445181d0b010388802c1011070b0909200d614009600c603000f8a1b88255500e2150802c500c0c4400903010100b00800724456040001ca880744400040000030000100b10744800c6e4090004107107252200103101425030208099203454415000080d070503c1c004500f041e00b0401030010040a401030010a84003083c030414125180940030b060350542c2d80a040a40c071142d404440900c110709c6001c0440e009a0081003503020016801451070b000d103040241442e450705001468000d0f0700c1e00100d554408102844021a007201c2130b83c0e03030f180003880d080c1d08070343c10401d103076000d4209150303030340d2043c0c000080010f0340074801d000f950850307480c0c88195018210842c0242d4041c020491080d1100d0244612100c0c05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 128442266 1250 128441016 128441021
    0x10201110c07140a030210111b01080109020c150103051f060b0909060103061203180e01030f0b0c040f0b0d0506060c070905040203010f1506090f0f260304090915 71
    0x40c14640d000401c1c401e424a44021801d101c803103802ea401411a00c8048016076925001801641c0e0503a201c0148c0d034a24070b40f4625001205a084105444030f17184116a641d020540301d05550348540091b82e510000000f0500e060b031414441000c540d4070074000b004110012a4902c1c88038003024509c550300c401140c071003040783c036544204240400100000c1c0c80314101082800e41c080814100050820b640d41510000403512482c2100043c82d0311800d144600040c2140303901401a10309991025810341d501d24020304082c45029100720440c030700103041070340c0c80011103001d030400720f5103c40380a945205035045034000103917141c421030402c03001507600d05040d415a1807050440000384000c40c581b4a01e0b40040401a0013039805540358070811852404030700a0f03000b0744425141d040c802900d81000100240e0b100d030011020080c0d0340703804204484003d41c0c04401e41b4600318401e0002c28000c08e0281c2c01050b1101811503600020400092035482e9030300540f00280141c1ca0254034a0a0907a0f0808 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 128443516 1250 128442266 128442277
    0x309060e09010603090201020c090c0d05090c03030a050706090210081618060c021513050a0911071106120703020a0201240e0403051b03030a0b041503080d0906150501020111 76
    0x8009007148010080c3c2807081d00402d248a00600507919600041c0001c140074000441e1254000100016002201d0f0100e200d4598001c541101424450f081480020344910440c42c00c00208440801c81340c0a00030107500c6404210b40c001d0108a14040401010b01403a00841c0c45414409161031045081400b9040310301c11b0324440208640020b003080700a071400200010140d07001140f504001d0104494030380102010b0070315401c2904128600700c00c202d200ca6081c0c12000d011070420070b5500381c03c2d0448099401a503401283d16801c841418042800ba014184545c80d001784214107000c4015010350080c50a030019900034031520810b010001895036042c2c0a0310740010554404000500052007040e42003480ad14000303141c800c604030441c640c1802903440d07544541000060181c9203130f903485005000001610705000c1d031485003110602901c60f611010344460000118580721015940c492800168000810040642004858105807c040c040c0c2c90242d0700c0c088030345559982001c02e0b1030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 128444766 1250 128443516 128443519
    0x913020d031d0901030609121403010506250c03020102010e12030118021e0a1d030c040c12091a0604020f030703090201020304030b0c030709150c02042a0c0309060e 72
    0x39032584a69044404450410103401c0014100032590003990341c108080d802140110300106400d8402d0a1101918000c6070010301401010110710340d00a400606490442e607040b200c0e42c1c4c03030380d84946c4030103801c0040400c030900d910a03102800301003024035112001564000c0e8000c01c501510b010003640d0f2650344800c40400c50070240300420042689880081600d8039a900240c00c00d4640060402080d040c00501c0e640b032603000c112400301c1640b05000c071550344410940d03401c0755481c000100340c445002d814414021602d8411000d0b103a809110035806c0c04542a000300810341c0c00342042c0c090b0764090480e9105149040340400e41600d000d0003030343d40720b00c80380140b50324613152408107a00030004000102d05501040c0400004903d040c130201c1d201e000c4c0c040e00c03150340c1d02d0300d0f900060403c10316030011038440303421f60080b1070b030300f5800340804d0b8a4039419a000140856113421601d209070100268480003150501c030907650680c4200d14074441842500e5580c0b0700d82d1503013000d5410581000955 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 128446016 1250 128444766 128444779
    0x100803040b07080309120c0708010f06152f01090618020333010e060f030f031801050412050304080d030c080c030414060a15090506090109050402131a091302 69
    0x400310380c000f001150054441c030200c1d44076016031701c0100040d40102000303d59030342004030300300900c003420f01503624140c0030308804000c5282000c1e2548028201049010100200110841c0f0210304005c070903c403201419000d1070031051b5100d01e0368060a048002201d032070781400c041c01c0e24140c20302c114490540d8000c02810199903010203844407680c108181300c6074041e48600b496440b090401e100c82c00f0741110305c6200007600d001001c0c86100050046614000d5010808040500501101780c84030032144007968028030a1080c0101d806019941040c0b880e08820022182006000001041101c8101e006d031520740740c03416001d90841c1c0c408040e241c08560031100203040d2080510007141d200d0300c609000b0051000310030001e460034108690b000d1650f0b6440805090320701c2c000c40110010000d0340002e00c070614000c004940c03410410303c50b8079116600c0340040303401c640c0c03004082101d40a07040020424076003d280206a90f00200c0710141c02081d0f82c1e00403800f10340d089040c010301c082e0050b125 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 128447266 1250 128446016 128446027
    0x17010905040302120705010504030305090609070e070908100c020c18040602070816110f0d17030a061208040302181e07023309060106020709020705030d0f05100803040b 74
    0x11001030040100128118010704c038003850f00080c9003001c3c00c00d07540104000100b5203004d1902500b1240040e241c0c3d0b40c40d902c00010802150310015905050f10b2001043c5401501e440d18217441203209900b0013092805246240d406032551580403001b40e03a429400c03508600110414441c6070614600c203251004103600005001c04c1083e00200f41d424801e0005515001c1d50b070a160380141c104440841c0c80400102d40ca51003032800104007a003220044441c100d03804031940e5074245000c00b90545480b2404040006901502981c0c058002082802c031000106001480d0600055000d400100e20039000004821009e00102c0481d91244006466030080c040f112194115001001400070003148a8110b030b00515010054140200c640c0104d071420451404807412035140d5030080c0901c407036900000c0100030441d40007440b04111a1505070042c0d5174001c50038814198410794480f80c0b80e07541440032002028200754802403140740d00c11300b00003826803241c010b280c403441148940111454207014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 128448516 1250 128447266 128447279
    0x71107060c021311130806070e010e0f06030f07020d0507020a0915090e010911092a0f030c031e0601021e01020705010908070b09010603030816050c121305011701 71
    0x40c1c02120500040a94043c002e0507655003081d0b0b8516041e000104101142c02c15092001c960311101030007400c00504001e28000e140142030307003081d07200641001030205c41585180c59404103030210b940e000d0300d00c55482c0341012403d107001c003003a6005d10040c412200704640071481401910b61590340201341542c100e26040e2068050300b803e2984034244d41840b81d00007440c401c50310a00c19520110400132840b42c01c2401c00140d00711824944c2805403440d5400c01c16032010103590f0791004503503559482d140300c000b02540030950041148122049030004140030b0704105102c0614868400491500300655040b0201e0074400d07015030321540581c1c0027110000c5900304545000030b42000b5a40011300384401a1503640c00d42c0d6200c007044d180e81100080d40303018032181c003002c0303030748410880000c0c0111407850b82c004040d134000821440840c100c1e9500b0b0412240b06400721100361920200b25403450018450340c2c00b8039480140c03400c802c4001802c00107160b5000300843c1d51011707a501400440f5a10703200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 128449766 1250 128448516 128448527
    0x90c05030109381501111b0307050916050a1803210201020703120e0f010929010305060f04020f091f062f03160f0506010e040203030306120c030a0f0b07110706 70
    0x30380d403170f061006a9416101c07184041064840503040c02003550701c40e000000c203060814090390002402600301e13038100500da9280300c075000380f65003e40c60082d5035440803200c11110510400c0c440c548206282c1000000e1125070410400541541288142150045030040e4201d200c2c07409e000b000314964644c058240c0c9a07941c001c800c6211b80340261a40d50340007101d890308403011204119500d0850388100c0840c150000c0a5180e4004448007428095040da1111592800001c22109c8442540c0b40000d086468440b042406007802800b41100c5050400600200001020620140800c80100040c12030304c1590918940124201c590350004800c4402e078041da80c000349140b040f80b20401000c0d0481d030110f900290010f0180301d000d0b65107000340c98040d0a065040e4045042c0c2c641080920002da6004021241c026104031800012141403500050a18600424441d8180240411402840120709605510620440803d031013540c0700038040c0d803030812700120f220541e4400701e02400201c0c01038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 128451016 1250 128449766 128449801
    0x2010e0603061c03111f05070905011707030b040207050336061b0f03071401051e0a14011401030506030a03050901050309100207031d0108040201050904090c0503010938 74
    0xa15112000244600f0080d241c14101c1c4400c07814210340d0451043d038400d1b248241e07504203c0915064602c0d600c3c090000301071014616000c21440c49610204015500a9222140d03451000d4003d54480207107060454882d00031055007c02030310444c0c0121109980741d08a03007107840b0000210b02d402c01640040c0300e00e5400842e49400581900c4c5007042c0d00e44030400088141240c01002160b031040309180581d0310f4413241d000f2510303907814002488900950400494440060003c1c0c1d55400d55460702260054010281c2c4a03650341d08442c00412065260f015880c020b000c2a207090045845003c01d1543e10725540340084c2c00110180614442588107000468018440c98221104000c0300040c0d50200e038804dc10031800b0a4802207a081c00351000008842c02200c2401d103051241f8044d00040c00c10300c6908910b41c45503940d140c0c11000c00c0503101860300a0a400b9000b0000f400c1d1600e400b01c504a44580c10b2000728083c880348903c01c141055011100e41010640c1070907030303261f8107100f04008030f81 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 128452266 1250 128451016 128451023
    0x31208010e07030b19121203021801030c0c0f12030e030708120402030f01140402090c030910020d060e0109020c0f120d05131b090513030c0b0403030204030206070c0302010e0603061c 80
    0x441402105d6280c1104c1140281c80781c00300c1c0d91420482032800d41580c0900140f0304041c1030051000000c900030007000841c1b050402e00f00443c50408440d412590756000d00b03c002c107507014180d00d0f0010b0102080311203040c00309545040000c4052004220b070b0301d014030300c0010b1080e00c04210310301c80c4140c0410750b150001c1c405811075100c40021b004050948400c48200400200350b0000c1000350718101480c0c42d001542c1030182491401c4c900300c0036494000d0540072000b0f00c2d4001071495400401640042c000b42020107507840b86585903504e407000703940078411080301845480b0580f0800d407008030381c070002000f00440840c900302d516404240a44402400d81c00c3c142240c029840104803c0c3d90412031b1581d80d18915807106040c0b00322034003201c802800c2d0718401d0f109584002d001a03003101610500721b801800043c1c040d546d52504402a2180c3e0700000c0d00034801062070320410400510040c240c0c0c1c403d8a03001003045081d402e00c001c60000329034890307101c580e24211480841040288010b40e500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 128453516 1250 128452266 128452279
    0x1103031f05040e0307020d06020f0406020303060f0901050108041101022a0406080105011203122a11070803040306050c090307080304080f0102180f03010f0509030a022416050d06060306031208010e07030b 89
    0x850b03480c08070752f0802e601182c0503800c000b0802440340b91403450115014822034018a80f9410240020410180144000e01681400c100b9064607070081190b81c03481e2007034a0700080d044050911201400c01c0180e00580298144140811103080602505044c0d82440340c451b44444000e0f10201c800c11298003031a128180c0d20402d5940c80c0200c004548103074020880050400e21103010001c10360b0082c0c141c42041e680050409125075030703002c4100c070b085a80182c40894079031166071a2a03d140b00e003403000d40c2d0600c6000c80001307000c80084040d00403140c1d41c80c26202c2c1040014011402d078442c2d03550700a0f40241c90401c480b100d03c0c002114100309030020b00001060380844907000c040361401d907600c51171a8030119803a181d0a40c10030440e921114069913480f003c8803500392000c0600700c0500f8210200e90b09506900710544a10165000070030002c005010842c1d03a00000780007407120740030075035040c0c00e01685001558011041b45040300c0000c64041d03207940e00d100f000c500078070480c18425440b90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 128454766 1250 128453516 128453527
    0x603020414061206040804140112150315060609050423070905030120090402030601021204090204030b090f1f090b090106050a0819030f1103031f05040e0307020d0602 73
    0x3211072141d56200ca601c0c048944207400e1000801c8081d90400d20304031031581c0443d040000003814a019074080724a281600d51140c0d040c203006803643c0c00303140000c482c12450130030316204610319981d4000840e8050b901302082c1d401c500c42c000d401d583c040c0c014a004105101420085428294030084060300c3c0422054800e40f8481d0305102409004e6034440001840008188164079081c49054115514000324200d4804076190403034950140320000c1d84116808000070302141d00078484001440701c20035040355180c1c1c480c501170000b90098001034a0b4454880009003840f200060080c00700142e00380140301900311001081103200c0a03a02c4241031a0300c0d00444400070341e03c209654054100c5c100081441d50600302404020203140e80300da10740343d0004c5900e0203040401002c0d42c0c1102c0d01460000b500d03806041003540c0502500c0c3e5205040d20000081012440c900702415081d800c07000c2440d0300d450f80d900d00b00001d03561080c502c02c0040d001044042c0041c684070413068241031050f5000750810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 128456016 1250 128454766 128454769
    0x603190c0309050f010606080103020d1704030503030906070801080316060608030d1e110418090f03020c0f010806060d020d0902120601060311120117010e030a020a02120f061603060302 81
    0x40ea00e0315003880101e80c42d92401001c00c00c060014a000c1c0001c1d0008220242c43c141d0010014101840068000c04090300300c6010302003070860800c0c4819070240700f15074640e0340f4a469a9a540200d5552080c1d00500d00806c010768843c0c1025030403241900d00a50909030601d229100060900a08960640d500c82c0002000b840501c0a8800359100400000d03142404036840b51114a40d024030194551501903140d120003c21070644095940f0114102ca000007030102000c0200008100034041c002c01c2d40c1070341c0404d41d0000e101c1d46a5002030b03500803000706003600152580c0c20141c83c10355000034280001612400a5806000121412800881d0049035034021030b05086415101d914103800c2035006000c4103070580211a4081c61260b201d5240801e5492562032120701806000ba49800c1c0c0464190303c02070941003041500740794010f0320f68481c940d02c006540d80c400301d0002c80c00340c030311500100e21208011900c3c540041554000d8100796482c405050810100c10307112009140e96400c0101c0075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 128457266 1250 128456016 128456021
    0x1104090c03090203011b090e091e0c0303181017070c020d020a030507061b0c06120f060b09130212061c0605010b030a1802150d0f051e0c0c0606060319 66
    0x4401011039240080000101c001c1547c805178001540b03540000007801b101c0a4002001500f400a50a56503031221990048904015500700d806a04d4440419005000c0d40040120b0340303200340c1103855007c11481c075401660790001800b8544199549600060203180c02135000300d030094801400c00c031054410f90700007035a20b0310b66041900c203a80005401e00099800680d426445030132041040c01d072088583d0394405d5002103010b40000c02003150760045041041d5000b09000983c0d40c40140166502e51000d0303000d0f50400c0e8040f62094015251802090391144200da40080151118086941c0d5800c140031022840701704414030308504001c0c4502160480c440c00d4040c040c11207009550741401880e150690f145604901102113448002070016038880f0048420541034168a82d201d5000318050002008680304040c50b1500307140800c004501e01d000160640b001d0300c080300c5e81c0e948860004c005540551881079115902c4440452181c0c6081070103164014800d0704104280003406250405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 128458516 1250 128457266 128457281
    0x6060c0a061a091003050a03030c111902040506010c02010c020618030f0a030206070f0c03030b010201020409150801060e0c030a020d0f020d0903090504020a0512100f0f17011104090c0309020301 85
    0x4455401514040d40c62800d0100c1c01d1300b0040780d4815000250464031496200c8001d194020203269880c0402444203002c0c102d84980c524008013595401d001e1500740c81c91124a8003800c0303118600e00703000a101c940c0166400c0502c180c040e5a15184170b2020350920185030f12601e0640113205179112001402d581c100f0020380d40c0228131010b070902201615010340381a801030b2440c1c0a001c40d00d042409035903071140e0322040d204c0e05407901181c2c1080b9a00144d00910664020b00310550424058480b01d002d154483e204564400780200112651241c09000c000c0c010360340400349603400c001165644001d50082c00d0b0003000900001415440450310301c0890788150764282c241a03c03030034400c0c14507400004a0009140c20f4506600d81240c0311001005807140402031524034841d280070036081e0054910244c00782c460821a0b00303405840e24240001ea22042c0304810018001701070020319014180221980f8016400019081c41c3c00c00d8120406013041d400003400701644c811043c0d0140e0780c01d006540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 128459766 1250 128458516 128458541
    0x302070503220e010902040506120a110d06060806030d051c14010f0504050f090601060f171806070e0603060f040b040c08150a0e0f190c0201020d0b090f06060c0a06 72
    0xd60350b920302420070498650590028020358810700007000b036900d03800b00311400300c4440b121000d8a030343c2c0d50a941008040329043c00c00a1800410b2140205e1300300d500c018152071054891070682e40e40c0c1410540e80e640c401c8424030000b4030501400820f213139100d081d88100c03040c0040205e14007180c65140809500c0076032062030a08103000003001581014071400c0c0e007000c00b10800100c03c1c0380208245590700303418410f503010050780544441c8024400c1c0900070071a42d15000700031007030034800d1143d45440000003090001c0d004910109111038060700c0003400004c07000d041c050544d40c55204105811250b10841900141c490700c5455243e902d5100f07545043c1d0090300c80c0d041a0a020800111800754890580d00984900c007003030048040c0c8401d01c580c42001c245601160f40d58010000d841400d040c0165410181099100f415030380e0190041c00611082c0340b81003080c6c032401c000300040c0080a07100c010810a4000100d0050300b131010090332441003000842d204e03480780d03035903010807110710000b0701 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 128461016 1250 128459766 128459827
    0xc0b03070c060b030120180301090b09071205071806050d03080103060629071103030a09180504030e0427051609020705060106050310031212050a0203070f0302070503 73
    0x1042040341600c41d00343e1a14064000300046020124025050118002041c0c1c9641303010541c6030103401e45540181a8041c0030b0001c2c0720016031464080008801030310f101c030103805220808619a19a07100080340c954021005210103403620a4844e4450707611510200210346480000c9a90b85602c007420f00c1c0b1a1183c0d444490a41c51800d1400848403190070001c2015460301c0010560705d00d86102807480f03404580060b03a00c2891b80f400c0f40310094090078564250001044500e801c60300050b44c0320071294075100700e20101e41c041e03286a085410845004020400c1400c004006003000e41c0440200b680060401a2071000c000501c01a0890740c03c1c1111103038090500c4106494045410500500140d0400e41c104201c5a84081c0c440205000d0b0340101b150200c0002d03501d1107100c00c050020b43d0040c0d602c5032034801c17a24004100078299445813103c00e080502203808000d036482100e101d000e265880000e100c0d10000c00f10301035400454282d99500c403c0c809015008840100800b5a06000e240c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 128462266 1250 128461016 128461037
    0x142101030b160302090a061b0b010e0912070312091b140f03010c0509060a03060b0307030c02010b0108240102070308031003021e031002030406020705070b0d14090d0c0c0b0307 77
    0xc0d00c1c800d003400c024000030140107020040701740e105d401450040c0c0700c0c241001c00c2ca00c001e070000c603900508041d02c060a0b003031b03500000098010300041410300982040094500f07042504084400e40d2060722801000680502d0080070480750030350040702054840c0170b4180e4124180032031a00b002d446c6070080c00b284e440100c01c040e22442c0a940740340560509078000d20140040803405460b07800741c2881c041c0240c1c80003480c021160300c264440b8003e0400744541c0358480c248001d00400800300300c000000558601003d0480542c02640b41034400c2001c404407481c5841d00140031582c01d000c80c070119040d03200c0c540300031002500c2e05015520440d180c1c030015000d1481c40c0100483e6005124441c072001860020f488150341740422003039032074009284007603560f071102e02c2e00c42d00a100701c083c090000e0181c00da020450b4948800207000c03420120505200712580051270040e4078034142c0b00d440481e1300c402240f410706409501041d4840f40985601103c5030743c0c90082014550040307031890001000c1840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 128463516 1250 128462266 128462281
    0x7291306110c10020d0e0f030406030b1f020705040b041b030c0201270b1b030c07020f04140103020a092d09021f0206071407021e03070e06090108010c142101030b 71
    0x94242c80e01c0e654004140076101c1c10607c80c2c5034841c034014601007507120743c17100d4196100d080c25181201c9105038400c0e000310304070718000c1d00e5074942c0c016644902d0400d40b404103032345000c1c0a552581d1310180461503c03820b40d040c0039070080c4100c5c40024295506c400c0c030016804c0309562032000400d8a0b0900c0070000c505460b0400b8152402003105904401895000821030030440503280e021b1190150300c1e6850080740000f07a5015442c916582d0300c1070514162441c24042c50003424100d9201b0303902400c0c0162200220426121000b103c0d10450726061010440142001015046041294030001d4143c030913401158080f49440d02c08040c0400010820440c2070741085400c0d4080405c1c64100c00010031021104410b2013a0320000c0e201c2c03a801c42101c1a0311510f0003510422040090845000641d2940e500c60340800c1141c2041c411040c03135000052000040c06800700984007a42c404c048070300b03071058100c0c0e40d4200c0f0701050364101703140e88200304600103884858084c41c028047c00700079162942 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 128464766 1250 128463516 128463521
    0x402012106050a1509060c02011701090b0f0102030a0c0308040f02030601060519180312020f011b0207080c2d0406030b040203060907030308012907291306110c10020d 73
    0x9102049070b40c01041c52944e090381c091291015034050b1300c1c0259176100d0500040b1044900309043d00c0c61350707445c0d00001074901d40035400b080c00c6280c141c40000a0b10780400044e0788902a5040c0075012903601d031020390000e80305005090b0305c184a1312031141c0b030344401e40100b803401c0e0098001002160340001c240062083d60072154030b18800c0e40c0b0303000008080301100500c0600b80d0b403000803c80707a00a6011400940240404001200414000c00001c4040d006010000c4907191400c0702501546002144400c0041107180c200354001c0d0a8000c01040c02d01400780d03041c001d0b2407080c060003d012803807581d80da41740160313001035010b0348200020f0704080c01014200403010f49a110b00394003540d02000026005080f180c11200c04101d10301c16000800200c0b1840107a500b840911a00001400b004201c414404400e490082ca0480a04a4007402412240c240182c0d0100411450141e002000420b6a04003609030703811445101d090100d07000040c1d203022025030845c40c0a540200b9000f06040306031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 128466016 1250 128464766 128464769
    0x1051f030e010204150212040b09060304083702010510050d0c0801090803040b011401120e01021e030f01060807091a0d0c0306170c09060906030c1f0306120203030d050402012106050a 80
    0x603e00f440d0278038001c5654528030a1036401c40c002d010110015052010350b1068401d140307000e20707408070030580092000050410540020707480c0e03281c154040050500c144980c03485008020341c42400c0301c0c1401e04100120701e0103942160341010344c00740404c2c03d0b2001c1c001c2155183c800d402070f940300e003801d10300004000c41c1604411164030040450356440d0381e02041220020038100400202003890300c2d9a01e01a1103410180c0b4040711051002000ea40f0001000f98800c0b60903038140c0782c1690701c2d1402210007200c140c400c207000400a41c000e100c100c1610180b07081841c00d8041941c500310f282c60200003941c540c243c00c5408070703a8030b14041000c2160724040411b4241c00401400d801d01e0002d0028298074005403509000d02c054030005101c42d14104001c007500b500c000c10820b07184450030400a1500e20915510000030f0900c980040d0f001101490168140d600030061410907440000d540c2c01400c001b44260f04000c1e04114ac40c80a0f400840120344900d501080070640c10700b00320500080c0b090b40e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 128467266 1250 128466016 128466043
    0x90603020a020307030305180a0302030306030607030e1e0102071a040606060e0d1407030b130515040b04020618060a0c060b240307020a0204020a08160801051f030e0102041502 77
    0x4014011920794044103c458135913141c10700040540f1603103600d2068440b0007003a10128400e0252100038550004081c0d0f03c07440c8224101e81c1d1a0f512a4401c601303030340f0307040c101c150b082d0701881c00d80410088034081403841e0a55540018140041600d612491440c0d04000c032490650710001e2000348909401400058440e9040c520141c540c4d200100700400c403c03102c05011084d2084501d00718110034003d40004542219642c0f025080010605c50507100464080b100b078450314090901c80801060350a105a40014800440396100c3c2c0038440150f2001d49110705444c0b501c902961107541c3d0030050101d0720000d45c1c42c40e910718114030b003c10488100381000da12400b60350300105248130b040785030112104103c0090036281c0d100c001040c0d14011050100942c024008644a1609944000d600d48140092818450100314280d01030700d5001d428020305400000c414246c0480c003902e403680443d130642500d00000c1c96070159985a00f20380151b0003020145408080c80380c102641084500b644568 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 128468516 1250 128467266 128467271
    0x1103070806011b050709020a030b060c0304060801091404030e0609032b030e06061203070c030f0209071d1009170307050d02061905130615031509020105040e06030a020a15090603 78
    0x391600e80b85d070707101034920440701c045800048540d40c8507c6600300302492107014089649504540c0c035101d4a0b60040d028003030002c0ca0400000603a0b144501a0b4001c03440345031121001612141c17421111440620405c0c1c3d00114100f28100d80781d1000c0161600d10720044078420100a440070f1414a0000d940c0301c02402c00d414012007031840000403812a401a40440303903071660001c9a0041401c6000e00d0001a043d409030710800410300061017004041140308075200701403666800f00070b4031804d0040c40000e4080d50083c0049815040614a6031041c204078185055442d40e98540340c50790107901600411550004540403081020030001400c0884450029048034a007aa402040300410951a40100e6403514080b5585e0340402e000071280741d40010041c4144d1100001d5190130075868401212640e54540c0e0000e5042d200b4864203c8007581603542c43d241c43c0c5801d4042d000c10201a03d0b80368140078100c585c500503615038540800901c40307010040305000504201824540c1d055000300c05160 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 128469766 1250 128468516 128468567
    0xf1a06040e0313140312270603010e040209040c09020a0509040f090201120c2f060105010201020301290906190306050607081b0c030d17010b04030f0f0303110307080601 74
    0x2110350300464141c0355641c5101402128410005e840c10000f9405100300364800030b120001c140a50340250445d404090700482c007110703e07005100b03083c8424880d1601d4843c481011800624282c0c081c00c0c0c0103405510b4031012507031986a1078089a00c0812a44003203440007510b40b44c42c1c1801d0041c0100301c5286042080400c0c01da80000e050917030b070903e81d04c2034180d44103c2c20054500900182640320302c81002058a031340112132010446d06014040b20303840c461b5200000b441d40c030500072603068406800d09038903208410b10244885c0071a241c4a80d21440c0140041d04090b00c5180c0031b000400b419100c0c1d0540580243c0b000b0382202e0f1076800c00707801203000300104000b12300030000320b40c0032090f040c1307060450b0b242845101c0d0500c40f015251030362500420803014065940200090181000352211a01c0c50743d030b8401510070f40c855448000c0504014032103040100e140d14547d00c4280b8001d04012820741929910300b03001350300440780d803000710700713000c0500805581c000e0001070b000c00200507214400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 128471016 1250 128469766 128469787
    0x1b0106030c0b0d0608011107140706021b062104140604030f111c0513060905030a030e1302270102010c020a020405130c0e0921090d0f1a06040e03 64
    0x74200ca0050310310581c000206003800d1003003030340003400a02d0038000811090030135503c0c0c18095401000305803191100c0402400045002141082c01c03108036400a089145850300c5604000c1001304103254050400d2004441c1003240003080c200c00b2500d0181030704d407480d0902e08011381002149103102c80d503001400708000250032030248010200c136428211150013614400c18501b040c00404842c990541805c000041900040a4401c107007038494003185298942404540d01c003000d102c0c4962650043c00e84c0c0c004a0302441c08114a410068030100700c03944100303091010307a401400c0d01c0c1c200c0300c41c0b610080f900000fa1912400000400d10090005000401700250b80340b01c6888068480ca60390004185540752084100c1c1d60150301511584c0b6680d0764114000d05680b04545800c0107002d07940f0000409000d5040303000f08020ba4040340c600704180c29040c00700c240c0748071108036800500411644081040d41d203284101c0b810155140d211171801405000139602035140c9101c141d4018404403406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 128472266 1250 128471016 128471033
    0x9010c0c030906210e0a05211e1204030e090115390507140312030f0c0d110a020114060d020d0206160c06080106080103030e010302030a110c031b010603 67
    0x203d886034034280240c0100181c0401aa040c0c25a403a03401903c2d02d030654030078481c081403541c2c506010b0000d55804020707040c0c5c0d40010880140d401c0707850540c10400240740049811407550741d01224000c01d8204004a1103a02601100f5101030740032940e400e00000f8140360003407085002d0306c4080c17503210040c025480e0240a480031250341111980072141d91305904840d1890310280340c1c0c040e06040c00c0241c50380c28200d03140c40060103840c10300007440206d030120307003400140e003003919a00400d12882e650f0380792b1600011081c094210703000b82100700600304d5400954024031240107084a2107983c3c070a24560082e003184c2528005c4c190b1001e080c010806250703a04030790002c2c81070701520a00490401c6200040306881081c414400346640a00c8420900210040100503a2100d07110041c0c640d0b00c0c1d00058030b42e60300c00d100050008015845072800355200340c000d160420720240e0080b8196580906584d070a80100096000c0c0f0b51000c6461040000c000c0416911303c0d103004020414242540c032072109 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 128473516 1250 128472266 128472269
    0x70f050d060c0c050303270f060c0c0c030a03080702011a030705040c03021e04080d03020304081b030c010507050a120911040c12050c070605060f010f0f03020708030c0309010c0c0309 80
    0x1000b5a01c420071051140268566824182e000066070340e41e19001310a07115820350a061044000d1581c40c0500c0f800da4002201c10b0540d5245008081a40d5041ca090f003480d80724031800126030007400540c0c1034540302045010f01203442500c95514502d40300c0030003400c580110041610800c1402585042501d000c180d190a9030000d90f4081044000c8841c00d4010340b00e08840700180068091912070050000c0006d40241d485c00070640d0341200b01d2040403020b0307001c03d8074041e200d81c508200200c1c2d40c00204825059014a1005030b07400e100d2107946003802c4800c111002400719400013492407000c0d60010160790100b11840d005c001c080751903142e84651442c051451801a51f0740d03502020018040d01e04002d002d036405209026a2610940b82c071600c0d08003c4040b240207050a001c40e50918004840140b01350041e9508440b610710f40c0380480b605110f1402000a1540c200628004070b807240c002144511890005195a424007925007821907118890140800242c0f20134100085e6200103c5d40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 128474766 1250 128473516 128473523
    0x1080f04140102090a0b0904150b030f040606120c090b030304030503070b15270609040809131b02011409301b010b0112050106020c0909070305011d070f050d 69
    0xd840d01e00000c0060700a10400c0c00c8142d109400c401e0000c0c000d1000001000014801d450134400c8950141400e0b1490b055030048403580f110610000720b28000c0d5040071a0300901031000410115614010380030a0440002d054464031109402441905068018024604d100760300840c902882d6840e4143c81c1c3c02154402441d011200c4041400300c2080310302801c85210052140c28482c880402c412040348040d07517490041d9150500082c107516000d803c8500c1f840d0090880c81c44c1996100800108401c0615041e2805a0b00c508a09900a1031030780202c0d5003803107800011301e03c4d240c903c80919603140203065000030342c485040756030721182c20451100c003902c03030b24091110405408403621840c0070700300341405034850031609441b1302c1005412166055000380c803992a0103060800c008141c4109000315070141c1d0100c03100360214140510107540c052005002e5620b0315459a17100c85c03c2d29004039020810a951018030300b5948001e21518000b03041c0285e40301e9031a0b14150201c0d80040711310700c018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 128476016 1250 128474766 128474783
    0xa08030405010210180b07110106090c05071e14070e060607080912070e0735070e06070507090b010f08070905010c06090b0708090c010201060f0b0f040b0408010b040b01080f04 77
    0xa2145d4044d20400a10441e407020340041c05291120008010001c0100040302960901c3d40001d119182442200f400c1e411076650300d031034030b16503856000d00308415846900c0e21680c5480040049078800300b240c40b00b00e10400240052174035010040c411110040c020030b119903410800800003a5620048600486050b5200c40785804100306150802810380e0120840b40c0c0d6003c03c021003030717611070108060311940300305402880810a0b480c1a21040101c299030b000f240f80f23800310b41d179640101595100c00d88003c10b101e00c1c024266035218100192640844101900d8148906156800020500d8440800c0c681014103150081c002048000da62003054180720100070148103100050b0030002d903064000342c1350003090401840090032014111001241d82c01100b040c5040c545c4180030f030108503403c12000004e85802c11010f0103050340302c0180704001403000c2000180d00100703540030388000c202c502e0002806202d80c5e0244000d49002140c414100b000039400c021030f0103070303895195420076001000d2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 128477266 1250 128476016 128476031
    0xc0123030f090a080a020105101e060e0d050304030b0604050717280c020c031903020309040b0103020c12090a09020306030607031d0115050411090603041502090a0902090a08030405010210 82
    0xc0d03040480342040a065014000740369106141c0541001d809070303a040101c110000d0341d40c1c008080d2006280781321500c2084615040052f50711400d0810006040188442c8030000e5a41c1c625265600c5a80100e680f02400000c20520b440c051241d10b80c0016103062100300c40003d440ca9000c1840000d1013001002d440c940c2e840c4401c1c9001070400480c40c2e910300e041109403074200e0040d55817003040d02800e01c28815080b865912082c0000341c10b02032540341e001142841e607407204000103480041041d90401d0307800e00007202d44440410100c841140c0800d00c00e551003001e80107201c201c504541007544042d0041061103403d44000403420342c003c02d58900001e0400e4217100300d0740c0d52950114003940319803d0850781d01807000c1043c51038044907400c0341c0c100044014071080000a001e81102e00303500130014000200800c002003003807003c80025510061420100ca400940c41ca501c40d00700c0218540e010a44469034100320300010302601c0c15000450426141800007581c5401900c0510b141948a025 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 128478516 1250 128477266 128477281
    0x31103040906120506010b0a0905120f0706080f0912030a02070c0f0617090607020c090907030c0b0309161503150b0f0304030810050307030204050c0d0c020c0123030f 73
    0x1594050042014203124465030343e42e4201030032620442c29500c5000708030000880720010f00c101e464240e1a5203540c031140e480c04040000b80043c0c003040c031145005010f080e8006040a01a4101801694442807014108010b00005072800140125140d600203c0c0220b00c0c405a64290303948803e100102590b1101185004001400c0ca13178080c1040e107000d200702041891b002214210b14014000361121036903a521801039540d8001e80304040541c0103448e00440c0ca04104007985d50100c0404119580a0303508d5880300002407056000b4034004001000340108810244201181003405d98880c00003a804d00403640000c1c100182d2180a0590300c50180b81030880380301c0d162008080840580e0340fa800d0344102c504140d4012a000c400003204140001c02d402070008004041d02c5028005000e1141194203110082001802c1212400801e00201780c42d54001d000d07040c0c031f414040e4040d2080501c0c0c80e0014010b014904030034840d001c090751007400c102c000304040c2e070380c814201c10088409031035041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 128479766 1250 128478516 128478523
    0x10506070b061207030501051f0308040b0c03071e0b06060a09090b1201110a2d0309030509120d0f02010b0312090111030301120b0a050f0f0615160618050a0311 70
    0x42000729640a04c00b00001401019800340d88100c00d500f030081c0032644450380b00c0da140e09082c00020030701002800148500300301c3e0b0b030142401e80030000440340740a100d81c46071071441608500780e0442012200942d02001a05104950004410b40f80c282c1400d08002c0e01405505150146020403940c400c184982a07940c520410008006000200704021403562407840560005c51200041920740c40041100704501c51024101e00602c54400d24829000743c084010b0590801d0a90420400b0b0225860503580d0403031038803001c0c113004010301407211160b10181000004031454401d5900d40304032050385846c0480d44c6041d007507118405079a1405a48010703554070940c504000c03100c1c8004400810034803000d1101381c40142c0201c0c101803156580c44442002d45400b1618009003502c20300200b604070300660604c0c0c0d080b001c0140489020a00540240c03a50703004161040741c07004040c0900000d00003a40b142c65465031114000b01c1b0000100d490720340d03039400d01200007401c01007121408108000c0c00e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 128481016 1250 128479766 128479789
    0x40c02030d020703081602150106050a200f0606060c0a0222050f010906090510060c020f280f03020a0b0f1e0405030f07050108011a12130b070503010506070b06 70
    0x74407085441c3c00f401c1c20024040c000840d06007500300c030300d86800c5003840d000050310400d004100d200e801c000ea00345107049410343c0104000710148020360b181a106d26464061a40d040000b900081a100402ea24a540b8005000d00540e004203410002e40c08419408070b001e01900d50103403140c5040301d0345920301c0c9081081400c00c01814511306420300040300d024011305030480340300701400d1000c00d80f162003030000c03030b0015112079054062045d000c00025000c2c1d506100f00c0303030005095000326108840171550649502042072284180d000540d03000d820703c90340280c054004444103134800c50460703001c6940f003030081c025494010000300703000c0c140c1d01c641000c80c0c00490f046480c2c00d132000310100c0041400d8115000e624440d0058800e481304078a000610541140c80582d80c0100991070900340b13840b500303441c1104080c100010000c203080480400a44e9000b020104002605039031a42409240424040c2100e400c01c80e04000400107075860005444601d0780024180483d915510000740c407004a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 128482266 1250 128481016 128481037
    0xd140a090818120114160203040807060305040213050c0a03060b040e04031103070507030305270d03230708030604060b030f060906211f02070507140f061210050f0f040c0203 76
    0x8145d0742d07405900d407002400f8003e888114501c1803400301c500e401d80c0c490060740681c4c0100c2c0d022450800200f032203500300c203400500284c1010202c1c03801d5140003054842c101d601e02e04039000000d1810002e039146c031540c40106070032690a41054107203040c080c1d4041c0003400140400c4603130301041c0c3c80f0f40d00600454110035405002c450b0090399a140203030907a000004a0306d1a84a2440b04041e902c6585e5001d00485030300502251003083c0fa40c2d010f03950f0000d051400500318844895426806070141c004052560181070b1058403490100d04020036107045411660050f00107100b0310080403042143c40b07400080490340503100d9620200402c100c1c803031309a05841020404090201c00c4140401da914012020b20041d5001c2c2c8240d40d04c030400c0e441036902c010540d502c5903408100e120702c007801141c05400020490b80005500100182d441e4201130704462450411409101d150300d2110040001414150303402041410030900080d0100b1000321081d000f25180c41c004413010744203004584400c6030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 128483516 1250 128482266 128482271
    0x1b040e0108070305061014090711011404060c0302070210030216080409140106021903080a020405030105090709060801200307020106090f02090909031612020a080d140a0908181201 79
    0xa65095565a610b01c9100075101c501840010405a03117521020200f40c807010414000c0c1c00707840c00240810303020028030502c100200b044501e8801c10007030091810215652a120f140b501f001c0c10203a0444e00d40d5902035061600c10400500162180b5030080c4001c80c0034180140c5444040007200302141e0414002001a040014041180640c03076000500007c0031101c440c40036038a0b82010390b07444c01d9056404842050603a00c4000003446850500c0c0e210903942f001500301503540000c213094403800d550001c425007201409000307401c450310400e00103001d00c00c001d101081390705049000348414a2542809110b0001c0054091070003500440d004204021041049a40c44100308002750414025140300e0b005140c04181f84e0640001960354102403d0a84c40750125240d40d00e0311080e00a03540320055000c0c40b01c41d00049240440a41400002c542000c00c1007804035211234a2803074010309000000780303042c1d01c00020030407003002c1c0c903e00d401a5400405203414140080e138080d1654140d407a0560 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 128484766 1250 128483516 128483519
    0x62202040203070914040605030601150219030f170606030402010509060910030209040c030605031b010c0c0305030a030f0903201f0b010207060203070b1614030a05071b0b1b040e01 79
    0x9510280d80c00461700b400395851080ca4441c0c0800c801c0d0703200e522035258103621000060003600b42084440070a15281c0c0121544d40d4003483c1d001910b185080416000301e441215a401c030540c0001d003418100000300b0030003140e86011800203c9601002e03002078100b14000c66000300359192041200d00d00d1400804064200703100445c0100079604c0301c0c00e064011821714000c0400316000b03001746006e03103000401415100c0020514620b111618103544c0b810030003000345000c0421001c10321003010b140900003655850500c0ca40250a4510940c1140c41181c85c140c3ea14020a43c424002e800100c02103d0a041b017040c0600a2494208190151007550750304c00d4410000c002e181e0f11105100303a080c1c080d2005595660001d0ba10f0b80903a0501a01075400c0000142110011000700b40b5000618105184078401900851100707800c1200c0d400d200d035039a60705115189070085891881a4103481450042070080ea850300b4000601412000f4440420400401119183c0b0283d41c05440680c105040c290f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 128486016 1250 128484766 128484781
    0x807080c0d0e03030717070f170a30050403031e0b0f010504060801120512071101030b0a180506060403080f03070e1e120f01050709031b08062202040203 67
    0x414000d220003010951002c0e4401090401000350b480c056041318056880351819256140d66611800741103035100040015080040d5500050795001d20180c6442c94907400114405000844501c020807400726456200080032a603801c20300d44180611000422240c0302e80c038003940940030b4088200d09a140c500030480c141007030b990012001d9507080710040110003c1c4001915284031f03034001d550009114600510500c42e00400000426101d04201d5142c032105032140d100c02d0300600c0080750500d24030400366049607414043c110004004441c103000144c2340c06d1161810342c000d00443d20409441e1000280b0b40e990f40c00640c0c00070341d04030050715a11002d2029510055004841082c0815842040c0c142d15042c905030060203c140c911303a10802288500070802c3d02401807004128900c02d014140701400703028040c2602411103a180e010a1604614080c072000785004612140c40d15400c8081101240000e00b050700038400724681074295040e230100c01c01070200c07082c003c1c0d040b600010522050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 128487266 1250 128486016 128486023
    0x6090b090d200601051005040302030313140909100b0f06160b010602190312022b0c03150e04020a0b0703050301050405010506131404020c0109050c01200d0c0807080c 73
    0x11025150b9803018074590044180003a451004001001030340280018000d03820904403061215034241031007410315a9030750000340346620503125400081c0c84d04504008019004250030100300084811b804240b5220766600d5640b2070428000c0800381d151008401a0303290340d0120541070b18003078035803a6a0541041029041e10411104a07800c0c2025400011038501c04580e260655100203034140c03000c5901c1c0c401310740038074022030700c0785401750700b00415000d000400702c1a00c90710a81c190082680c180401c0d55204859121848030b0905051841e03407051840c0407c28a000d880d0001041c403025121400880c0c011941e68000c020a900300107401760506801c00040c604803401101d040c00b6680c0c940f0144540c1c0e02401490a550340d40490382400002942a0410400d5402070401810120408010b13800c0d03070b103103d500380c0d03042e0042d0200442d9543d000726460788001c01d042c0c0301111044101c4541d555020b0303602c01e150400010705204000c002c0101c00700c03021203030050381c10f607103500300f940030b5649 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 128488516 1250 128487266 128487283
    0xc09060909090d080f09060103062c010c090f060801031203140a06140f0102150a0b040603110306010e1303110102070209090d020d03150b03060312030103031701080a020a1206090b09 80
    0x1207403180d40040d0f05c00c1200741d0071510401003540500481c1e4615910764000d400100f02d0910300e1088280c84090f80d41d03540c441c00074100742c00390002c19010105200138201c02002c1e0411007005590b0b000c140880c0e90049402030449600a14103100c40c101e4000880041c0792052001d54103e05030000c2c01b0b20700701a1b400c1308081e9551105091084a110300c10001c902c412000b40c80d000d6001503075468100322a5280302d036489903040a001c184061000002001c0343d009410403208800c0c0301c2600e1606d810b0401259000d88480000400702d424588440039602c07030044001020801200e14036054007500b901910645980949984810b04002c0741e0a034486c4580c2045400600c14802c014000d203200b4001c40796100c0300c010361002d409003885225903040c2e000600140d050302c1501d40e05400e0b40840c0000314000c0d0300951302d0b00641921400d400d86815010381c040c16060b03124680120159844819010881d130064400d44007003a11482d005010f0040d003203010f8007010403041009166200401d4214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 128489766 1250 128488516 128488543
    0x304081306020102031605090103060b030703061d1302060705010f02070b01170604080d0b030c10020f16140103020307030b040504030e03010e060115050a020708030a05040302040605030a05060c0906090909 90
    0x80041e840355022401c03404103c41100300a10102200012580145e0081813084018580420426110040080d895000f036540c04002036850a0820210741203005401d0a14a5410400d0840c00c000446006100e500f0002a22801c00001c0c41c104001007503110071107858450070150349401031801c00c40d501507024030400d440c0284821002e0040000440c66500c1035a000601609104c6270036205402448494030458161082c1e0b11109410303600d289888101716a00d41c028142ca400148025003420741985030f000c036108190000f031107040554003492100807000c0c07800503100c1e514050300320090722110822540041c0b8180901045c1588440c0d41c0e014400b00707078000c2c050038a5035a07500f5607426003403003113a251960b03031100b08001610071401400051780070710440f92031b107848e8410b803421a0b101407640d801045e0002400c200b10b08150017800000c10045014104140d01c07502e41e5511080e0003407003d13000301400640e4400036503480d010f0395009240901818002d2800c80017a03940c0c0c8000003001e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 128491016 1250 128489766 128489797
    0x1b110f0604060c080112240f150302030c0111031c02070f050a11010c05030f030618010e06190303120b0111010c02010501031e020a030f0305070b0c070c06020705060f1e030408 77
    0x10406c80c0020851100c1150b20107200ba440a48504041e0906d200103a1000a40c0313032220041340e25215180035001640303107161039099102e4614410507140c0044a119076041c00382c076100e0b0018840300401030350910400c1d5004c9042d0716503130440c0e0400902c107000000741040f007000c4c965000c0c01000030706a5030345031140c402e01d130f1031181c13010064032948412800108103502c100311150308030310351b4400742d60454409000c0315103911031800c101030544401d8100b03102c9007007104100500c030310301101580e01051542ca0f80388901411910024141d050107090040510384071210210a80d02c68804040d042e83c2a000800001300c16650007030207004207200036100c010317840000901010300403002c100000d07802008400d405295135203944ca03d900c00700c010b07010311100b844202c2c0450206150241b14070b404a4155503100854604880003118980003042150302081c401d000649800085581c580400b003025901d0340c20f110f07090b00032900510b02d404442c9402005010070886000c014290b400c080d140789 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 128492266 1250 128491016 128491019
    0x31107080304080d030905031b15072a0507030c141e2209080d020703080a09020f011b0828030903080105090a09020406080607030606031b110f0604060c0801 69
    0x8541c0ca0045008083c01a0480d8640d80c148600a90000b2405c6100d007059078200f00d2507183d0041001c54405107913440303030458420415041c001440042d8000181c2c01e11403821130141250009081c2c0c4201500b1401e2500704091061100811101d0002c540c00800001d40548a03022945940c030a008460b00030b060810003248c48130070101d1700740590f0001410806440e1101c3c64200000001301e20300380328050b640c20080d004103060600610152600741300248ea144021b144c001c206040082c00400c10718070348801d03840142e8544090b100010001d07c0c141d188141000342c074a50740d224a60300100220f100280304801c0e202c0403080d0304485520030701d40c0150701c07010b00e0047e402d4130802d41e0020300241d42c0341d0052105150074400f55411030045180010707242e20301e50120b0120784194002101c1ca1b440001081040d40d0325000c0c1d8401360100f41b034184061044011140c9950a80c45030740c030107008820003d915202c508010000c1141542c1c1c0480d0000d00f0300341000380c014564000820005001c0700d00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 128493516 1250 128492266 128492279
    0x605040c09081c1e05091e03060a0509031b28030e150f070303050f0109060602120703020f0601140102120c06042310060e0f3d03031107 60
    0x901c01d0854210710090301540f200c1c81c89414110504690003001d02c003c2d980161810300441100f02609450307a201d465072816003004100c00041d00c2c0c12030550441043c44102c00c0340c0c60102c3c620380c005d90000e001003001d854560000d802d50040869403031042420440c1c0c02c01c90280095450030300071000d0764000c0c100c2008a001c1250b03207a20344018000c05c8403134900c00150b04248040c003500400c0c000d006814040005a9009103034442c000950000e600c440601c04405450000ba500420240303800300405850a00003a440e0f1541c8400d1000700e07403010680d4003c0c14028000300c803802410300c040e2810f560715071041c40201850070724a03900521540700807080c1200841d08454048012500400590740c2d02e55800744e4428802c1c03484619a50380c0710080205110800000501401c940c2d000300e00e0508018066444080040081007084540c0d02809a445059501001c445062101d400c61001d880f442e041b840a0404460102541800400200f03055000c102410070f0384032130080d01c03078569540c00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 128494766 1250 128493516 128493527
    0x615030504050a030804110405010602030d0501050102070f0e040206040e0403020a15050717100b030702100b0a030803040f060e0a0b15010806130c030b0301110a0207150804020d0f0203010c02010605040c 89
    0x300c00600c15807000c1c0350500445c0c042c154a60340184038040e07102210424101040070760b0000e07440100503030300c0410641d9114140e805500c0c0134040c2840141f41c40f51800c0d0011440700010310522040154207400b00c0c040d501d40008880146c50b0110300200d550030075282c001c1d511001d80b94141c0700e900d40a55000001c1442e80503840c0581040e95440c28003d215121f02040044090000c001c20094400c0c002828540708000d18840e2403650058400c46503410320724010343d040c0c808401d2103035400d85024000070b547c00c01620780250b084180340b0090002031410703074002c08020982c2020341c42948190300811803103824240c82110f1102d803108004982c1c40040d107612a090b1241c03071b840720848081c159944040d43c07005040361514600820f0036501c09011074211107403000d00f4803051030000342480a0a804200c0c3c18014050341c482c05003005010100180b24107c045c10017446511589078a030280140f4034400c6070a44d80082c001c110303088841070068001d0400740314460060703042c541003018007070054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 128496016 1250 128494766 128494771
    0x8040f1a0906030601020c040f05090f01051006080403021015050f03030c1213030f0804030b010b0a02030403021012020d06050f0312070b1803070308040c0b030415090c0b0d06150305 80
    0x10224100501c210401040d900300418050440c411070490712129038441c0540c00c0407001c203020000f42400e11455060030007448680a0300a61b0403e4148600c44803468065002c8600918190b6a651160306c0c0c22410314a500072000e888900341920401c40d45459034041c02110343c12200089895010303c1407507141d002d2000c12001940090f24403054107144200105070441030480900d044545a40c0c55580540c003130b10095900141c003040c01d000300003500c03e255016109910180c0d0400000d0b010003076892269000c0240a039140343d00c03080341c9600908091541c00884a825034945011a9a000080903280309251050040760b902d0700781401d020480d5824640d8441c03040c2d1504510f61100501c0c80c20140140008409070048680300c1c0e201070002c0d11441e481390395450701904140c10315003c079030411f8200a103102c20800510000a580f10351880d541c0d00821404912a406c90610455000c62544462001000001d00140300d030f04681c001425174410392500b0b000b0300603c0200700d044030000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 128497266 1250 128496016 128496059
    0x10b0f060d0b0111010f05090d020601081e0102040f1502070b040b04060503090c030d021e1b1e040c030c1101180f2609030f15180102070f08040f 64
    0x401540d5854000c030b4200808070003042c1012104200090806800c580e0300f03034a1138401c0c0e503985d400e000054009000f40000b23002e651004040b40c0d41031114990700e8207170301e1000507907915840c0d100e802040803e405070780092000e061401078850b514041c0903102d20000030a41c0c014080c60101242c0020394a007a50180d45800c141b0500f05401c000003070304d8690024020070f088d841a5220014950b400b044144501c00302039024210307049200030803000f01d40e038010000d6540e40000e051070b24845d00d80d440781050342ca022a40b0340303900800b00c1121500a041745a0480c2c106080c50b0844241a4050700240d99022aa6440d400f10a41d01e5a80508864125000d0451440c030020300d8804562600e8400041e10301580d1020340e90364404076500461903c045003508941d6022171041c02d2803409004c0b04251004000c081c014a21981200080d5000c1c000c1035029101020b803e8080e044400358180c402d116844900e08160030900e0401d49620f030001c0c8606c40e10844019004a03000502d00a4072414649 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 128498516 1250 128497266 128497279
    0xb0714160609050607090519060f050307030b0405090c21030712090902030106031505091504020a020a020a030506160915031a04090b0a0b010e1e0303040807060908010b0f 75
    0x4140c0c604818064203180199100794a810040000c10000c1c02401d0091000f5120340e0360061510b000d1002c412100c00054000e00f0200404101140e0000c030400512191854440c2e90fa541e022429802007060101d143e4200c3c0c034207400c01020030707000101040001001c0303445070600890b21180c1c0758036882c62851082036800034084d031400034190806030710b90100c090070314444007078036500400700320307007003640b005002075102c5d107128802001200c02c80001e058192281c92107031400780d43e04400c00091241c550f014590000358894024030078464142182d50080a071210a656820810781d5001c0940301e8402c003540520810006900804011003180d280802d2814280903444059004200703591703117042c000385d08400d8001265140c0c40303a00d01851240c81c00c80f650b030400456400842e00c48040d458107120b03038014200055a075070074000190a0700c803e600d1000c8200303079021908500132903201100c54458076201107503058008444400344c0b01200c000308000e818080402070810410124a03802c40b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 128499766 1250 128498516 128498527
    0xb060d0e0c0111070303140f0c030a030605011e05090904110d03030902100908060f0702101e1b050708280f11070b04030308071806050405010e0d080306010f1403130b0714 75
    0x5580000e84140308c1d4802c1c90a04004c00440701070708541c81b100e00307140041d42d40e060511456800c451000c2e01c08003040311a09001d000390300050414490106146c0c4510701010028041141c0c1030100c10800601501402a040c0c0c5031402a000d40113509040703115081d00031404800d01e1060300500b0880e944d40c03004000e1034507030070b0041d0b81c41175000c0c00600440c09004901c4418031041c0c05964955100d901c61005480365010540085030f440d02c46880316110241324080d804c039403241c01d48640703c0d04191015030f0380c0d0389103917940031950304981101102c2983c002d6000ea5150020154204442c0a44403082007030051407080ba2240c559001d174080c000340034041400440c0c40f8409041c0d02c1951820b02040d64180c5014001880b007991707018a0000c1d40c005014021540e20111101092005980000c15560702d42d030341c50716a01004100504100c40600d0503d0440d10411001c00300055240c00c1a603a030805980d000e414040040e401d035005c901800c04500c1c154403a09650701764007880d0074000d0405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 128501016 1250 128499766 128499797
    0x5090123120c0a0f0806070201050c0406030c05070f06090b0a0605030303070e040e07090204170105060604090b0a0b070b04060e0303090a1202071d0a05090d02100b060d0e0c0111070303 81
    0x24001c41c218248103210300300c2c9110103500c0780e0481d8030141103600328a8034100e00d04000c440ca8200010704100c1103904000030301441c8407805c020b80d01520024100070498040780c0c502103e40703004009016161620740160403060056641c01076094074000c094204540ea01e0b141034409881c0c1622507160181e00030000030362503511030041c41c40c04102c010004544800301c3c1b4103091900c0e400e138100b503825660000d410000c52107141411210132180c10024011860b000001540c280154495040b2081c0c948000411560300c1c0880d40c00501580144152100741030300b08070113400d40460382110b205207440015014104000280c1c0d224101410040c915400076580d220740b00c102400c40c180662007404001320b1100c0340111030400004641c81d9015080c50312178101070076104064803c0c1340641000c05c2a00d01d0b0350340481e1074540104c4280300480d400a520700800d4070382c410901c462041c3e91134404200308481c0040b034001160f900036a10b00d0551043e900325240c4861440c40010082440c100704800131 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 128502266 1250 128501016 128501029
    0x40302040b0d12020c030d0c0206030406090501140405210708092101020708031509060102031219090602130e090309120a060603051510030b0609060d0203030c010605090123 76
    0x840c1d01409590280103a80e43c3c2012003810b0900c10300150700306440f0039034541410895032510b0411172030072000c2461507401082051001610140900d9120504034003804802d401207204100d00021485003887c1908010352280078181004803511840c0001c00c40901442e400d44084980240d9454039290803030007041007120141c10010888408440301440d40c0344c00388091b0120ba8003d2000d00d6481c0381c4600300b860050035920115110300303034003010310505036400415a1080c000c40080c5002a4460501d656006014283d0100c442030030810f82404002d03860b0080d10a00c841f002458401c40e03100da0007140c03005000c488410060b4400d000c8c1c80b94615041c1244900e203100d9405071591041251903000c1aa8815002560306a00c00c800d1000b810400400d41035201d0303c0351001003621030941d44c03000220b19002d80369034401c0c030b09400403880701d0f55010b00c081459a4020101c1e40d41c0e00c3e150300d0b01030282425204282c41803c0785800000d1000c80d264842e440711505803000540c40e46c0220800c280e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 128503516 1250 128502266 128502281
    0x9060c0203010b0301020a050c0c0907020a030c0f02100c2f060a090302061303121803060b031609050712141b0d0204030c17030a08041101050c011d150c04030204 71
    0x1e0664858a90810b5038070700380b005194034642ca985490782c403903008210625200030900380364020040c03070040140d00356010034032010742a414074114881d041641414000d242c80410042e501002d8030340a0204180c0110401241ca4410100c1c1041c0a00a00c0b100340e08281103031500295021a480940e11032610000030401030f0450308000640ca07440c0e0300400d103160042e0182d0440703065854410f206000400c41c4240031142d00d4070382030b560303480070141d1154003800310311005044a4540c040340030b060b82c0c1401556119a808c22002046039910304142014102c25950480070800030201c0c000c15001500410300c03698140b04265896446104021848000c4000703d5207640d8414450b4410103031190000b04001c500902c00e2205035402e022455000e60041504200264410001c005101e90011052030740302ea08192100812144100141e03030510072040c0d61101c40d4681915808402204d001342812013140c80300710b441c150811809901020350039580c00300092400d010420061929810080707 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 128504766 1250 128503516 128503519
    0x206190510090501030606060306050303071104020a0306150c03030c02030a0203040e06060f070b041203091208040203010e07031a0117070b0a0306030b0403081503010510170a020a0b0705060106020105010609060c02 94
    0x1070a9a03081244110380080e081162216198a001c12101c1e42c107000f00310140c0000c5020f5843d20550340c0d44c11902c9039160b031703d09000f9a004210901c2c01800f90b40b0030001455000100006060f80c8003004002500ba03100460102c1c2ca404410005a0b200001380c5403500c2280d0000c0d0310b4141008962413084130001c220740c1d8400c000700514000c410030745000c0c20b816445900012200d040030b03e0039841000b010b01d114030070185448404404528012910102c040b031904003074240d43c40d50300110b03025002502001c006131142050000030811f05240305904400c9000c40c098007a41c0300c440d01ea000550a40c03c90081da0320158040c484000c1281c018441406503007000540903659030b50340030b01207a08075021b40204c0c2840c4108034261206042d2822072038012802003189103410254680e07c8485401190b00c2c0c16203200c000b01d00c06008204115502d038009000c2c002d0f00e980c0d003c80d006940d00940b42120203014203c000a0386900501075281a00c24036110b0061042c103160080300c1d400c00c0c84106a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 128506016 1250 128504766 128504791
    0xe060f030603010615090f0e1501081e090a02031b01020c121c0905031020070318080c15040501020601030b040326061512070804081e0702010e0102061905 68
    0x40340016800351621720366281e00d0340021036282c0004a4080100c660020480141030020040441d901070707140e40005209007800f10329511002a283c1c18031035031407000d000e40c460305414001d80807000503108030024800c03070840d068215115100c0b5117801c05d48101a025902030740f912003003443d01e503000a08000c190070441304003070560003450004018200f0510081400040c05000500b02484020b452380755215041c024803083e00c0100e02450f001a60301c442c03421000c10404101071040d5034102803580e858861f11031854491071103545550450020503c80c0f80701c0c81e000032100345900d055604454058024100aa1854403640c408542c010412403c000c022034407200c0c07600911404404100170807651504a203024400d00101110100b4000100d620920503407203254000c11410b0ba10110314a8545540d407640d2800c1009800b03202e43d12031000f4142000a030303400c008000a8407045000741d03a48000704100c0c00069840d03100a5a0300704039110f40b038412161030045900100c2e0000b00c03503040d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 128507266 1250 128506016 128506019
    0x70812070b062803021f09030303152d0e0f040308060f0909070303020c0d080d09081e07020a050627190b07020301050a0b0607030e030a060c1e0e060f0306030106 71
    0x104520040d0100b080303c6028168003043c819424801d9641d1040160200d000c0f6002d40f104101900075200c6110050415886000034116000d0305180c010040548000d203000d06680c0780d075504030112110a1120100c2540c6100141522580351054000c60107640080031984031394604076203014008054580040b9071450a02e807544814605600c594a01c0000c8c080709801c510b002410800e881c06190303c5001d8450901022841d031008403508402c107803400064140041c034125009000b00f2940b10494485240e001c001c116038034005080d070700d200f11040340d04552034208001581c050180844540d1451700c0c60189103003549400d0005403840180b00b1000c001072011018440541034018000c101d00218000d02141000d014181d004150003505000364031001d0041802c070301900c0009000c00103100600c41d840e4a00340444000c1c241c2051003800b560400f6580941000c0c1e4118000101c035800101d50401d95109211000a1510091850b0310302042c181c1501e0260300003038070941c0d155682e19070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 128508516 1250 128507266 128507299
    0x10501180f061a0c0601050609011d0d0602030f010e010909030c080901030b040f0e0f0f061314010c0309030215010b030106120b03010218090106030501120f110a0f08070812070b06 79
    0x44050210244060b10f03a40ca0081207100c1d410301030107030b0205010b48014000503200e40c1c1c000c1c01260034440e08030240300c44003400340001510180f041c1405410a0702c00018001c0c80ea22007805c15040c1c4042c0f80d110407841c4d85e11102c50007200c502500c082c00141c40d80f10713180009041d040003031141c0c240500d00440c82c00d40d66000501103607042c0e1100f40c0b07055500c1c2085810410184601880f1004074000741ca0004424100541c4440004000c0d90b12048015001e00030490301c8140c80041c000790300020004d20a2011024008045441c03040d00540b00b06521850b42d42c0c2c01c026042d0694089821990459190010945800a000710f804070000d80f14800d601e2162030034400ba2103014440c00e50703405640c1000c0d040c07102001042c2c10140405042000510000c1a960780c8503010710392140c01ea40c40511582009101080004041c660040c0c2c110000a1829044803040c4103071504842a1692682e494095030f03900c02c0b842e54845aa007009011540200c0c07520301c9031a42c061000362140060801c03404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 128509766 1250 128508516 128508539
    0xa020f0d150602070603110d021b010203090106140d0507150c08070b041a0f0f070309020d0b0703060b040f05060903010603020312070c0f03050a0b060a12050a050f010501180f06 78
    0x9074001280186420031220f41c0c108100070040410381400c000c3e00c60401d980007164030840c8440e50400c2c1d000a00003240088000204d00c020b00c05500031916030130110507480c06417146105056440c850030380030322110b14001174040c0c0c1082d0700000a02c5580d14140c0701525402410260310180007160700c80d4404030741c0c1000140110703482001d0904040ca8649401c001089090404c002038070f200704104210043d00412041e088006081c4c0000d0645c2d652104a018290204009421001c0303c1003500400c10010712540c000e11329070b201409241d84403000001207000390b1007400d0f15001007440030030071810000000c0c4141c0d0030181c000f01d5050b88035000b007071130035012010031a01500c0009041c1c0a000441d1428400380c0250128042050b2442c3c031800d550302c87c20000500000c491401148980d036a12880800500c90740301d181c0107520190808544400680d4011f9809003d544880038030480c042c4036079070581d0000c2009a003620904410b00c0000e10342c0c01d151041442e034501011500c2e41888 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 128511016 1250 128509766 128509781
    0x307080106050307090209090c0304080f04060f0305240f1f0801061103040e0c1605070602030d0b0f01230906041502010f06180b0a1d071d01080a020f0d 67
    0x80010840d02c0c80e0006042c5843c1c09036101c00345042c8144140d59490b5500f042c0f454100c015000081e03160b4549090841c0c1d18400c41a05444102002500017112900030880c1000c480041e2000c100d40c2c1d81d24100d800e2250540300c0c140100645a80040380780e4039088510800001005d4600c1c1748000500741030f08090030b00380c1c001e000496103400042203200d601503c0000c103001c40c20065414240f400c0701e94602100007030080000208007140249021901106508040760000c080342c241e60b58808019441e80d001020302c0446604013411090107080c510b4440b049500103a50303001740c00080f00c56072204840b42c001811500c1808100400c0550340f1100600301520050080a0703181034007002c00ba0848000042c2038a400e801d00000b080b1303444d4110000c070005c007411007000c03ca00001c08005204e61003e0782100c0c07402041e440c80e031132000180c04102c602c07444658440c2151081c041c11801c1460400c40040e80c00581094001000c0075041c0d005012007085d030741c0740d25040c680d5141c0018282e6154 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 128512266 1250 128511016 128511029
    0x9010303031506020f060105040504050a0501090b0114030309100513030606031209080c0906120a0c0b031b040b0304032604060903030c0302040f090c170c07030e040b01050a0f0207050307 82
    0x40d141841080501c01e142c14000349403c0c0000c10704003401d002c3d6180c0790001407084600c141c1d502c00000b0188902401602c40303040c0e00c100204059031003841e00356040d6000f80100100c9a810803904100750400100305c7c3e54204d40140500403986041d082110039510006012115200d0802d0004c0081e000340075640241d80304403c4107945412080c4c005010400035803041025501036603880405031910911550000303401e40744440c030140c0800e500c83ca0804081002403400c2080400051011a810061801035024003502c49d4416442e420b0741c041d5020b280100c0c5d045000402c0801d0010380911442640bc401c0c82d4805c1082d14900c1c0004240604200d4003039401e2078592081070200741d0b061141e1801c030082401d003141814100501d405100203d4083c10000990f6841c440c10b5040c003038124a00700801c00c0d0380304019845c041901d030846400c0820100c003c218800000c40240ca014003075521016410781d00c2070b0038041c0c90a411030f02075200059400641c0a01103001c6640d480902c6890041c100c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 128513516 1250 128512266 128512271
    0x3050607030e010c05030403211d0f160303020601090b0a170c030c040501060e04050c0d0501030c030b010504020304200d05010e010b180402011e030f0f09021c05030f16020901030303 80
    0x418800a080d07070742000340041041750030820480001d40040110052800350022070714020040000440241030781c02c1d00460044c0044000301c0205400142407540042d40410780c1c0c0448042100102102502d001c02005a084240144507240e200d5002c1c03092200002d2a1010840d51342c041c85802444c0054846585d4000500d0821281000c01c00c0385040001601c0c204082c4d03141c80c030000c0c90030556006a40c800d0f42c13520041981201048281c0c1c04445810301c080096596034940303e1588541480103d64456030b000c000503151515100b40d034030468006908208030b1860243c2d811000710002d03400c680c0101400302800c0420001d10600d44c45607041c00001400c100c220f82004003d60348031a900038404a008100801070764080142160030b074004944421000141c14107802404101010300e080600d03045440c00321800c5038101151542c025a000030314901c0291784e03001d10034100b80000d41581e0080bc420f00d0341e442020001c10301240d6034034414803030400560014800610a0303000f80c000a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 128514766 1250 128513516 128513531
    0x150405060d0c11060712020d060f0f030512190c0f0c0e0910050421021203270c030a12030b13020d050108030307080703090309030203250506040b220305060703 70
    0xf0307004044074002c21891070042a951429007401001e0105540000d0100c030f0b00402c0498002071b4507044600900180300c2d49402d66502d610118400510510080c0c850303115140158001d6503401c01201e0003281891510208001109403e407a1400c000e002111106030003054140403030218544400600762140340e030130107420181a03080c035040040541820315458001403100103094648100b484164140490401880c51401a0f041c5003017040e1036680740c03400001b003260b8034090111800d08981507444001d188214400340740d03614a0090a4503805d036002c001c003400850516510481b40d20124500481c24150040114900420040030540d5643c2c010900d4a081c800601400e40908a40c01c015400e62920b0400140081d10251104040c1130303840d1a06401d061040c8059006540c0280c101c03505000741c0c05a9691000741c9015100078507a080360086034a15215003200e048500024940d4109950f1401846200504208a6a4810500a0002c0010400c1c403005109802e01e440010742c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 128516016 1250 128514766 128514791
    0x30a05060111120306040b0a050307140a0f050906040504140109050a0507050303030c1b01020904050903070c08030901200109120503070e040b211f1e06080606150405060d 75
    0x2c20075410514942d04400c60f060300440d180c0c820383e40c3c014000c49002c2000084030b400b182e0001455003007a80c1500500501040700e50030724400009030b190946000300311a60b41c1c2c2c013030404c0c41c1150049075070010070b09003c542545069002181c105000f40d0000081404044055003103a030074060440d8942c000c5100c090501c4400c0c40100c0c0240f4040d0040c518610386800c00528a20841c442c0b00c507180031041540c50344110950580d8848003001d031040101c1e044c140034040e62608410022903819450072000300340c1200c04000d0718a05c013010f0711030100e040340782d01060210018007016600103669a102c024007164200d15462024261920340c656070342070800000b001046c900071940d01560410592003055140d040400c5d032180000d007400d000261441c0b611608114840001c01c201c900742030207034038040c60079500c1900c0701007a80c1000320404403291410801e40d80c0c0d40c881c41009410030b40001e01e25040481c05100d600100141340792030940c40300006015504038004040c10155103101c2d41400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 128517266 1250 128516016 128516027
    0x9060c070801181518021905030a030305010e060d02030c010e030a0c0608070206010f0f090b0118090203150f0306011502120a0207050411160602090103090c030602090301051f03111203030a050601 86
    0x1407a1000018020403101041740003403c604950300900400b802e403000d4058030b1014a0701005000010142c2d0801101400c00401820080c01407070702060071040443c0722880d184845e0000d065020300a03061140d4035400544049807039000f01500b60268610f0a00061558543c4002812741601e42d0810f9040c60f4200038940340c0140c002203958449444184906003000d2511300031113071540000306500b15080c004071924003483c410074945000240c1c01003140304854000d13601c184444d20f420306604440740200b00b44c2c0503c286003503406401c400018000b4512943c1c41050074070460046428001c01400fa191003a03005002010058000d0503040c0400d250a001d2540f0807241d41c6449030402c1401012020081400340004088c1030780060710400f164020b802c04000e5580011000e191701d9502d00b0502c02950000d40500d200c2d510b01030020344010411080c3d840000c1c8100d03410340c00142540c0d50140302c004d0611210707503c581d07490514000e04c44104015031051648401c04591030600d140007600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 128518516 1250 128517266 128517293
    0x609060513050703080f04080105101404200a0e0306090a0512030412110f07030b01030506010506210403021606030c0e031b0103020d090b100f050d020609060c07080118 74
    0x700030310340a0740000032590008501c2c082d240c0000d030039070340c510203103000011501c0713503910501065003414204841d8241050302201200c031807100783c580d090343d2a4100403c0307034040d40d0550b507080204050300c2840c225040203800d4180103401c000c940400c81d000004e1401104685030541c40c0d00100e084c104124084c0325908041000c0c0d00e00d1429400c10303a403107041c003074001c1c4595020011030f60f0460084407000c12450021030b4940080d55103040e1607003019032403e9000d007c15101d82c40703088000221401c0c51001c8840d800c900c400311030004c8001440c240d4061902070425421031144000e030819642c260a105c500410083c0c81c005500c00341010080e04149110740346910a40200341e10425500f0140d0103609111402d20700142c2c1c411210202000400fa500c001600c07200152081040701604800701c030056600344801041420f50f18420010b801040c500002e4121405200292441c10300c80c000d001d05441000607200802d403a82c460304c3c21a0380780305128641d00321070b01d1540c0511449040100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 128519766 1250 128518516 128518531
    0x606030f0b091b0105030402090603011b0c030801050603010b070f0f0804091e051510020307080301060206010e1003020303160f050f07091104031e030512090105071b0b0f060406090906090605 84
    0x80d030f04155000107081408000d001038007544844000400f00d07a0300f0340c440c068126803e181e10300388c0d8442850007051102c1c2090200c003c100b03d07500200b03541c5042ea050300e048134182c0c010300d842d00510713030303100b5040b100c8464045464828040740c1c940000c0c03814001d88040e001d1010006a8241e2103403034452015218181104030a2a060900c014022442440f04544105490540018150300d01c200c5c81c6120344000941445808000030400b6076020440504036140d03a07264125135203c1c10902802801d403444001c0d811350081020401800013103080048082c028101c94001c40b480e500d400d42007000c8001c242805810107034050001c10014452007600004c010847c5041a0950365040c0102c1c0740c040003060f6860902e0180410136200d0b40450f07070301402c1440e851020781404140d06010b00b80a40b00b000110341803070b45d2110a064600c03c1c41c18a240c020105036000e0300c075110341040710580505000d41080d00c071340c0c1c007054541c128091310130664440d0794000344074100360504000320b80c00a400c0300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 128521016 1250 128519766 128519803
    0x3070b1e0703170105100806040b1c06020307020d08010605190c0f1103060a151202060f0c010603050c010309080a0e06130806041a060a090f1413020a0609051005070606030f0b09 78
    0x90307459540c001d0480e80c0c2300c0d10980700090b034000050700207100e0300411040d9484e10307515500c0d00c0007004141c3d0003550184c2c0c400d23000c81d0541e0020820a42d0507070003d00500c0c002940521400c070500d2440683d20100c1c41783c0c4d0816031303014a0381e51108261004480300503185074003c10002580341c10708101c0d083c2e010421341020085801c00e5460341039407404078420f000d4139000009450702555120700884d038010111800003907958480407800f902030090740c4400c3d80e003406419600d1070203500038020807561540c0480c1091908802aa096604102c00d006540d0000030a0011051044101e1844406443c0c035000400181ca01498660101184540b152032200d501070140003031fa8403140055015103103c8200803840300c0140302c02d41c006111905044c14071002d4403003440798407844403d019040310300a9401403d22030303c425099860f54240d03c1426002290400d43c0301d42548280080c024442c460300c004909150350340c4920381100309004040e0354000b801028440303104010001100c8100090800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 128522266 1250 128521016 128521039
    0x303040c080705060d052d01031401053903191b050a050307030209090403090510020609070b0912060705040609060f0207050f040219020f07060e03070b1e0703170105 73
    0x12a034117000b5181c82805c0d05454202150301c0e03450b0344c017403001c004200c105030104140c440440c4030038185080c4800d4520068000700e13000c4146040c090b46114000c010402010304075141c001070404200100c5080061040a441355810032426006501401640c8003805141495800001c202d401c1344100310140360815450f4150140c00005403602c4051500304030b078480d9260700d02a0060f102c0c0b00c444603840f401031010441050740004051003510400d075441050003c1340603042e40d40e80c109841000c01584220001c00ca20407481006021502002c0e01d03400d10050900c0b07d9a00d89003050701e0b9040807440102c0d0900900740d0041c00d00300101100d190000701c0b00030103070000c0e44a034554010309009010b4050700c1e035010348442d01100c000302c6407860003041e903000600b0000d4441d41c00842c000c0040c00b595000040062080899241ea0b100041c003505803d450102c0480302d40c0d004030310605026540c4104140d0346083c2c440600300c968020b845582c0c0b40881c0c01c0c82d140101505030400c0d4469040141c0c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 128523516 1250 128522266 128522269
    0x403110c010513140a2c0705090d0b1b03041101110a080d02070305040815061504080304170a0c0803121b03150303090604091e0c0507030509011701080303040c080705 73
    0x104400c0300d01c13000e10205001203d8011400f001d880c1e412524060031a4840300c008140c502031100c61051101004a03015250401d0849041c403808010750b03400401800e800303001c00c15502c040d6400200784020034075483c821f18044540754004039019521505001c0d1010500c1d6000300c41d45403a2020744025048100d8282d50b17407085405011311803c6010350215065013094004c008650181401c50201c401c1c2416001101000340d00884040d4094400200c0902c9282d444005640a850b40c0401540c10123080200030740c0e40f41e03020b00601c90f1a10503008508042444400d943d00508084405984e4500c0100f003145010000540701809501c82011420241010801600d40022a0301c00c100110f030074541c0001d10314005d40e01d1040c3d00130400580022011880c0e4030100407403242c25000c03080c6020043d4004101c500c1e01d50400d0101c1e000308000b400091003240102a0300c8414100b80070075264406030302030120426080242650f00000c144001d0003060003024004003104001003415608000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 128524766 1250 128523516 128523547
    0xe01020d0305150d110109090605060d020d0213080d0f020316020f011707030605031002040506040b0c030f0d0527070501110118081308190b070e090403110c0105 71
    0x300038404040c0c0e00d0001c114010808082403064540c002c06860341c0d040141040c0a04240d003401450202c0c5041c0d80028582243e8011704e8102c400080a0038140720818083c400603500840410520607070801031019030f1a000b05003800907100020044c007940c5450074014004c1d120202d0300100359807051020084050a18081050b003650540c1e103201d101c080340006a400c40710f00312901c210080c0680030801da60b545940603500f2601d044044404030070b0000d011604903c41c6004040d086101080207000c004440340c020320b0410381c464222440c040c3d58501c1d200031500484c8403000303d0f58031001800383c1c034140f40c1c1101025035002034019a900c01062400d90b074640881c031840b41444205200780c00280030079400800544007800c0c4041e440c6056281c0f0601d076a218401b0058014030300100400e54410000341001001d5041c5051b000d1511281c9031454800c00051822080000e03000f45190a51581c102c00d40c000c078440e48880344800b004134605d5040107a400340803410050180b185020140518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 128526016 1250 128524766 128524783
    0x1f1b120c0302010e010c02010c170f060108090f0a030504061403060f130b0306040c030605011e18230603010b030c06030a0902120307080a0e010c03020a171c050f070e0102 75
    0x50400c40e000d80340350300d4282d01400f403031060103100d5440e025208403942d4064002c0113044205540f203d0791881190a6a00c06e048242e0780d071081002d4402c00500b242d4081c030b1120360080c80e010222501660310002e510318000b5810021000604042020062076030040d0950700da03400d41010860a43c904840440e1712003003204c2e40701d0b2081d09585646ca80028050740440034a42000e8282d8205203449d04140b60401ca0601c0200c9146160900000e604003824214241850b0031201106031685040c0f041d0010b005030001c803064082d43c4440d01841401154105000b8046d400003800551828030b04040c01c603802c64407200c0c06508203c10081c200d0340c2d1103046a500c01c0d2652000103039940c650020401014400300f444943e032200007001414044108060018124141d603900100c11055004503819070481c8002000341c1e001403500c0c1d0000741c04c0700c0242801900a1074140c10034689058a540140d00c10f0414180c0f55510030a1203070041c00e44100961184003030500b16240a1718100007561103080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 128527266 1250 128526016 128526053
    0x905060304170903030409140a0204050a030b0a02040f080f010e060603121614060405010b04061d1e13050c040203040309150504051509040c0c20030304051f1b 70
    0x741251040000c0c0c0c500f580e8440c080034044a407110b40354841203008021440724042041146800141c1d0512030b4002c503400d1b500d000d482c40c0d4000780741d5555030b040c6405c00313003800f4040340d0248800320b502614150f40a0081108100910035103032114201d5003115414120a401c80d00800200b00e441d40300052a0440c44024004059460002500469601c402203200a0102440c8203460314944c100190703c4e4003d03070044000300030290843c0100011038019200c0e03031601078030040034400042402200c03140d0011943c984107200301c0c40c1c0313000e001800c1ca04032042c0b44d100301c140c4298000d00100304500b0742d00ea001502d0851840c206500d010700300d0031540c03283d82103805400da80c1c40f02d5944170382c041c1e070700400000c2c00e6161a8005c8581c1050b160700200c02c0103000320724105507101031070f114030b0b500c0c00c643c1e401500e00c0000c00000240074034040321040240303404d84410040041c103501e40c42c0d0110004028042d82400d40150702c4001801840c8550b100800c2030380700a404c03404100061500301805c440b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 128528516 1250 128527266 128527283
    0x90906150f04060b0d02040e091c0c020d0f03090f0803090904060b0d05070b0403060506180c0a0e03150a0c020a080a031a0d0f0312141b04080d0905030606010905060304 74
    0x74034030009015101c10341010006400214070074812101036000f07030050364011003001f04c0b956106d0420a0f541c014608001c030b203034030b00903e156100c18003c0c1980801075001030007040320900a619680c06e01da810351000c5001480c003540c200680082100303000d016151800245203000b40c44d400280841901500c0074101c0380e03851013013861f1aa100c403002e2080756030050584418581d034825290498000784815140076042400264461510303c1d2094070183c0016148540c40e11307542d020dc211a0440c0070500140148040d180c0c52580d070420503a03202c000e10910a07602071a21324018410742d26850882e005560103030240741c00013060035041d62500716040c0f80c0040e0794001a214106024114503400e50001d0b200e00380002840303944280001c0c014047e03140c0c001c2c0c0300b160025017030032100d50040c03600500c24414003142050480c00c100380d04602d2001c500500b042d8440b00d07590308007040030310b5000116080301c008000030b0a05102c02c952121003400c1c441c0b5005c0c034140c0411400d00c002080280a184d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 128529766 1250 128528516 128528539
    0x903070b0c030903070b010e06010e04020c0d0309150e06041209030201020601120302211e031e040f021f080601080106090915080316021503060d2405040b0609090615 73
    0x41095404564006c2d00e241c1e41940e4072541c1200202e01135607003900088221400070f819040c140210b4142018510007000c0b9078a43c207008034028607a40900711a03606030141170000200c540d0140d8000d28058034007400302c030b080038644440c40b0400041d00c8800c0c805840b80400140c7c3e0080b450034112040811505e0000b00310b89403c90400b858203900c1d080903034003810b6140b45002ea103006044624501e41c03050f13041600400d0880c04078001202c5802c5151500f600020a2040809006030858400c507440d00060003a540000c21a6080c80082390704001d000c100140059400500103030070201c28204004d003541441c4c40184404202d000d02c2e41142d17196070b64101950300034851200204005000d49490f1201200284150100f00c1400d0388aa4400800811250491f000703d034014400100b02e00b403080425a40c00d04d40c4072960011540800c80f00c2c81e540446005070103001e00c618800d800d41c011918041c03081107200e20f800f0b807090280350300c1081006004035110788402090380045a41d0482d04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 128531016 1250 128529766 128529781
    0x170901030b0a080706260408070b070801080d0e0402041503240303022a09010b0a020706090b0a0804022101091509151503020303070c060f1106010506070309030b041202060903070b0c03 81
    0x1d20420303040002c2140208101c01e08c0ba40c0d80107080c1240c4181095280354648030301c101e8200c0000c0c01455100d0b003251000307042007405540c00b111020406080035003032a45c2d651030364403034160301d0000801098a401c21000440d00d8034984180801d25051826000c1e070640d00c1c02940c03610400302c4044085c04075aa9403a62520300f20120001e404002e1002c040f560b11280b41703402c0c0707030407800000c07000d07100d81c4c40b001c0390707060146d84990b05460a0110f0302d420015150011501c080c1c020740f040e80c0003005a030724000f2840001d240e8041c4074040e00e0010400f0002c524001c0310300c0148400b851942807a250303070980000c0302c1c407010b0002d02076640b80c0400c0741d07290440c210448660302d0340025418440001e0000400c069500024101c0b40d0725198407a00c0c4401540c156805003281c444a122070300880014403042c60150050320a890181c54070b101041d849076140740f0200d00c02e680503606034503400d035200421a41045103551007a5020050b50802c99503550303100c1d503c0e00141203a09210030200018405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 128532266 1250 128531016 128531057
    0x601300f02041214100e100207030516050a110d030e0d0201020c0409050610050a030213050c0904060803030603061b0f09061201060f1e0f110109170901030b0a080706 73
    0x241c00300c00c1e0f00c941411064a032a0b061100a440048414040c2d164184080c1c101c0d489800e00c0c92a1074070140054a021402c2400250f0022004a0501006101b5654045d4007004168030103031051008100301c202d00d0901190390385091090510444400d94054002580061b803100016416284084101e0181c070050b4117081920b42190781140c50449400184800000c180340504102c182c000e030f100d62280c0c2480a8840ca5020203500240c1a92210003500c1040d80925440444083c4031418221307003c0c0024296402a880150702c0d074004024002c0d203282c2405043d400c00c40348002405078030405401841c1d80c0c02000c0070724103004000310b00d1080944844048940180004205060a68498030b0203051402c02c9070301340001072000700305840c8601c420030800075080480c0c0c0700c81c21050380c0044c04481c01e003050307070390b00807155201e480540020b00201094011034481000850701c030724481380010100c4030900c202a104580080d001c108400c0c0214152090b620b603031030700c41c4004075150b811101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 128533516 1250 128532266 128532269
    0x5010f110c060f0d050a02030601080403050c010905120a17041104020d0915020c0607050705060402150909040b01140f090703090c0308030103030504030b06032b021f050601300f0204 80
    0x104000d00080d01e190346036003c0000c00c1112803642080040380c403080c1c05007089010881c2c0781c5001c107200401103004a80610054042400d05d6070001c00c45180e0340da80c203428400c6016840255040c0030490002140e0080ca1000b042c0071805c02540301460300d9281c0c050b949038800384585c01241c7c0001e14070085402600700049a580111078100d4200544210358001d41c40b4118442a80c0150780100359031070b01c0342d801c8800003900034005100c191241d8007003281c80481c00054007110742040014001e6916007000c030301d100324015451700d40340c2c2d894044c0440308207106901e0b143c81998a48442d26144c0d80c1d800c00a900f0407007528000600400324034015500c0711040d0000303400d501c40400000101a030000040c0180c80c4501c240c5420340e20780d01d0501d507039800340c0308640720702c81205105580c50280a80300c40004111610458068448040511440080c3d010701c0c5548039441d01d08009031340d40c01c0542c013a1201020a524004140031000035144014140050803206031074a0550400d121150141c50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 128534766 1250 128533516 128533519
    0x20091303260c180a030305090f010c1202060f0603070806010b0c03071401060906050a03050a0b0c1c05061203040b030c070c0306050903030a2708091207030c1d0105010f110c 76
    0x41282000780542c2555081465000790a00000c140301885080403450b1204483d810344800b82440c0d4880104034400d20a240014100030080c03441401246070380c03000c0d01050384a40c01034030302030409604419848600038105400307035004420410040303000085050440340601000c54480080c05142c9055101304180a000e9a00002c0140c44030041940154120f448510041112550300c80500100c1d000703c1c800a002030304441c101c00c01084160a080d0361220384490f41c580740854408507003060200070b500e546482c0b55550100a418206031802031040e08206004608181c03070000c40c04000d11000740700d10449640490b0340c8e07040010080e0302401841c1c3c000c50500c01e9140c818000e5070340390401c40341c4007002401d04000c041d02405541d003c80c185082042000004210350303c40d4411640320740b818035080301032038084a007141001c6c0300c20400b662084802800c554500240103100042410140100d12030140c0104520383c2c010b00311104003170b003500b0407003410600d158030310381868004807045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 128536016 1250 128534766 128534837
    0xc08010b031e070b36060a11010f0609020c01060503061303140405030109030332060402090f030102070c051e0f0904031206060e0109090e060103082520091303 70
    0x40d022020303a90503140d40f2040418248060503103005070409070203102005c4c0e00a002080710801c0c1c02e01c515140e4070b00e000d03100d00214003a80030419120840d130003039010b50200c0f640410140e120031400e004807001003000301d00810072400e04810180d140500103000400380b040380000e1341510286d03031098900401d4010000c000e40901c6060240c00780002e810b4240314081149459800144200500103001450300b82c59801c0d65110020312000b5406a00840e1f4404640c1d0000d452a0350b00f4001024424403030b003072001e0b04614003406d001501c00c03084a800c42440351100c42a001e500d40709401d9848017401c44a250264807141030645032403c404000c03100450800f1400b24150b0742042161140000a80c1c40340241c0c3c1d83c0303500c590b0031100740c01f410740d805401000040011440240140072003111949030310341a46500b10071582b2603408544200d841a0354131400d80c4592402c0880c12100b81c50030340c0e201810345004420702d504520f00c504000d0900ca03a0300740721659118140d5950340508a4540300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 128537266 1250 128536016 128536027
    0x21c0f050a0c090b0d03210e0a080406020d08040b0609070c0203061608010503032517030f2202060702041104050301090b04060c02010b090403031e06120c08010b031e070b 75
    0x601001406025059083e41003825400d000d040a0700000c0d0381c2c5806603a4818107440744061401a15188450220125190310b48074010740400d100256200c0d100341c01042d601c03845d143c0061304000480070b045080c0034000040101044242c0c440d66440a011107000803281e0b15100250756222802c8000794140c450314082040c290f1102c40b40c807400400603224107105a0307860040641c0d0788190fa10741200f011910224900034801e072400c00300c0045c852000c0001c141d62030341e010740301a081100d00d4246440d560050244001c3c070000a0b07000c000c0086200941c801180c2c0101d64948600f10000b80519a141103400902c200f003000d44010f458018024031924096040501d519030040d1010740c0c071185007041014201c0c1c014031541c081120054504403607981c6949060f002014008545c1c0c00981e1000c0c02c034400d10a040c8113800c06000200c405c00031200450500701c21000140c0c004070060382c074103600440181d6000840c0c03e42c42099000032404901d200460b1800d00300c045e40010701e1558003181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 128538516 1250 128537266 128537273
    0x20a0c030b04061d03120c0d0509071811042105030406020d08090a050c010f030603080a031b08091009080702040e030c0f060c041205010b091906090207021c0f050a 72
    0x80c070900a41c01503006110308503522100301c0d04402050800c58041c0d00400c140040341102a114950000030200390074280404c1042e01420360300100d46240458001c02800e000800c800c1e034981c0c9441e802403c003001001c5000380030425507c038038082c00c0c40e8100b0f0049040b603002810180e824090364084140c1c0d81316030361480d01a540b4044c114014001c10640000510885000511426225080802016000c1c0b05100540c0c1d40340c900e01d101130400d52035507000300c0441c24900c020440c081490344c0c001600c2c001c40d984086124840c80d505006c02500e10280070161400260854202d00050310000d28521549042d0100340f00e140e030002d40046c10482c40d640003810200142480b081700350151081e90390300000b26030716400d044034018a002c400340018418002d4042008050920403000050480040c80000d01d10300000c076a03030030b50800c0601554000a0446c0607500c010b0903800000d50030700c0c1e031560010703411500d041200b25410009044000030b01c0b41c5180304140c090703001800d49450710003d00303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 128539766 1250 128538516 128538533
    0xc03070c03060b01030b0108060a0306050414070608010302090c07050d0305060d0609150621150e0a050d0f0504050102120a02010b0a09050103020a051503060f0102010b10021f0501120b040201020a0c03 88
    0x14800f6000c6850041d02015031b50003551018400c48000b400c00c201c0b58110703602e00b0020400584240d07a24100660581e038101c2041018002034031864542c090550304d184104176850700c006081d048085010f001500001e5000109034196108174100418160750740c40105904100700d141c090940c0341018612001d000c04440b0091110071180c0d402e1003000d480d10f61700c111180e189124001c1e85402d8011200104004a84201c2d05c00c0c0766a00101d4626080840186004100101500d090700b1038020f051896400040c1c0d1a0700d41c0c0c8500388079003442d2401d070010f1b40b10307503080c0c6c900c480d41e110002d010700030103200b035005100119008100e917144980724154100280400d0008900170000202e001c5443d2400f510b0301e803585464004034510310760b2408240302c00c81080c13058080c150340d280c01904c100742d99400001418141f01d40d00401c4241c41b400d40340400b04842003660700685117400b00610400281001e544a400d811114541141d03c075880101c1c0f404c002c440c00034000d800c1014012080001c050b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 128541016 1250 128539766 128539781
    0x1903020f0a03171e010b0a0c020402030c21011a0705070905090706030b030712060e150c1c0b010c021e0301050c0a030516050d0b010201020f0304060213120206040b0c03070c0306 78
    0x34100321591341c2c1e0a44925001205803081d09894480c00004100d192150340c001c0c5100001e924002e81440c0d0140d0124050f46c01c1543c00f0340c20194081031644844144c1d50321921201c0c1001d002c0c45442d403410f40d410309007a881c0c107140321404100040300c40601900b0807240005003403a040800c80d0340342c88907445444072054000c190000b42408192a0603181c001059013794000d103443c03c0750300065a0340c243c010034401300e050b2080d000755040b000d441030044400c584600e08024402d540c400310009490180d07807100400e6110b0a240c41c11010069901a1000689c0e982c107540b55002040f140d03607010104808180c81039410743c240010854612072400c041c2180d0125074070706011980782c04400c28140e00140c0e80d088000707a402d205003111145103412074544c07440e041c0001403920403546989445070713204503810b90303050780c0000b41140c00601c40480c50005089050084080300b0315503000a04610132485030b0800c000021506440901c1c0910855811035030002c45001c00310742c0e80c5401005040381 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 128542266 1250 128541016 128541047
    0x21906081902040f06050a0e0406030308270a06020313170a090b09010f1202040f090b030d02070e06011d0306040b090601051e090c13030b160c051903020f0a03 70
    0x601441030300075201d4001d940c00c0d03440488140342c0c07442c01c21070100c404d03812005510701004105011b030700700382d2914464507000c0c6d03010b44e503507000306c0c50002000e001c41d4006a8034031403911071007480f03040c1d0b1a02c0400c034101c0259011074090380e652251a88202500003070300020b8270500c451581c42e0104041c04000b0301070f640960700c0d0ba8540a50310340105034240240c1e00b9580c0802c1000008540c1340b481818282c04003c600c000040c00c01da2078010b001d04400072a004040499500d02a2100500e001c10550540010707a200500d1510304008010b003003068041c000f18140100d4001c0315082001d403200c040c1c80205c014044820a182504144402180954118101d03016220000c00c0905180c410504500d945255010410f050079061045040c001000b81d8404a0180080807020882040c10030085014400701d088509054500c14040c806841c10310040c4800081d1181c009071001c036901c140c1c96500403e6082045550400703a003001140005a8194040c14400b0010181c01c0012000c01d2900d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 128543516 1250 128542266 128542291
    0xe120102030123091513020d06090e1204090905010212070305060907020d141b060c0a12150b18030d030e010612171606020f0405030c091b0702190608 66
    0x6000144031884540524070f80d044114100010b54860702000481c40b640c4010385907120b021038012070328007203802c03061400d941d0700d8486000b0031120042c0d001d1200390209000203042e03480110044041c10b4801d41c803e0502e4183c4030303c2c1020070300c403003941a00e5814180e090701203600d00e01075500030014034003207e8103849642c0450100c3c49451001039500300710071442d1075281c1c00c1507600d00110314a802c00702c0b0034400c9415081841c0b00802c8103002d014090099166180d032903046e51000540500141c00c4400d14003803602c41c2d031420001e20103030a00c0071540010ba18030b0362103601c118140d43d0aa2450102609482910511140558194420314008803510020080f26880340b480c0c1d0321103452044090010fa500c0741c843c00365610404000c10901c50b401c003100c4a00c6001e070b511182030740c22420000340b00e8400440d00700b010342000d10000500407000c03035580540385000b90980300c400d030007444d0a40503054081454004c41d101d018402d10050500300d1151a00d40c4d681c98014a91030049490762400c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 128544766 1250 128543516 128543549
    0x403060203072106150e0f031203040203100209010509061b070303051908040b062b0807061413030f0c08070c05040c0518040b01120e011b0504061d010e1201020301 72
    0x202c482c804c50f42aa815045406a0701c03420301382c101c600310101ca84c45075220610340c9034240140e90401443c0030400e0040d180c41d44a26007401054107058000384d0000b1400c0c010030040303100340e034060f08480e04032104403050b40d00c6904840c01d008074000d0b0242880054820814007205054101d000f41c00710040002c95490014249c0030112020203050358014210040320010607c2440d207550f0181400d10407481131400c20b810003d005c2c1f04c0980d0b140050382c1c101d00018000e02800228080c51080180030200380c040742c1045105a00c45481d14100030301049960302d0303042801c2c0d104025986600750800071b540c0d2901854202042010307000e1082d02c0c42140b13000f00300d050441c0128152040c0c1116100741e0070f4040141e0301400040c140d00701207036040004290078495500090b200301c800321008400002200c54070107410000d080824044c003020310000344401c008055200720206a01a80010381c1c0283e1400f54006841902c02e110600342c1c048203805203010741c240151702841c100c1e1900c01c0c1494420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 128546016 1250 128544766 128544827
    0x302040f021204020d020f030a140c010c110910090c020c030c01090506040e06030a0b0f1501090b07110411040b030708070306180b0d0203030406021605040204060f0f0203040306020307 81
    0xb0320600385010401c059810008000d4039041c0034040d030060018102c1c1940300079400000b801c00015940464a02001c040602c05c42c074410400254000c0007800c00c80c05030803540c2ca8121880d02c0300c440c400e10440381d050014807202030000c25000180340701c040611140d0101c02019407a101ca5589882c0203210b206c054182d59031180c2c040d0b02c1105c00290400345418180550410050b00c001c00141d00b52181840a80025441900c0755125030a0350040340e10500f4140d0305d9440c00c0c100c044405040140014080c80403c0300c1c00110303a94290311540130a080403a90300071a02a00e0f00b84506256503c022a002400260040085100e900c06a407000c0c801d9540000503400c44002d80507004000707036003400c40d00b42c070b00e1140e1084171010030080600758610516800203145901075084080140c024880400c1c2020b02500e0f0b0201520b4111019800c0a0a040c0010a040c1c60703a02d0000411028074030b0302802a0092003142c01440d0400829940c902c3e21100c09098140340c1451003c034004246036500b03aa = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 128547266 1250 128546016 128546021
    0x80a0501060e0d1a04030509091b0f070c0f03050a2a0308030601210606030c1706010c0206041e0e060321030c0d0203040f051e0726060906010302040f 66
    0x1641d00c191508810041c02c02e080c0080c420034040c00321a2100d103107200c004800b09040e1102d1165119a40303a964810603d07040c040702c8800a0160030360549810110100b08802c401600c90a1680c10b84a41e140e003583d041110050321143c3c070603170480d8281e0001109011001c00d285000c28042c485600490354000560300001c1840240c109000c0d407803d2091001230040001142c1140051404c3c07002004c40e5060701c118072800401c2020303160f540b03200400c5030300d40600402300c0d840d0340c42c1000c00e0081ea0000300d030048070000814240c10001e52079044021035403020161b4018000c0c1001a981c002c804205001921866000c2c0c0045850510700050316890001f40803407480c1001e80d90100315081404c0c01c4202c5800103041c6a011010910030001c0a0031903201561140d40141440988200d49042103402e00c1c50b80006106450700d142d08040600b8800528001110203401072408640d80214000c07051201c001003200301c0340500710901c1014180000d9050599001701c40c1040020a40d0074140b08 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 128548516 1250 128547266 128547269
    0xc05090103050601030303110417010b01030f02090d0209040614040305030a050117031c06090906150f0803030c031f080c090603030418020c0c0901030c1403070509010306021303170a080a0501 84
    0x8543c40740c8018000244650081e000700fa43c0ea07401c00d82016114004050a50488050070f05180e556a901c0b40103903900d40107201c1d101d50300c050110328004600380424241080c1c4c041c00f9014072200004141000b203240d0007401140c00f0040f4100c9141410f00d4000c5ca00c1d40142d40e40111582040c0c00032822600d19940c540c00f420444000b1458510000100d2001c8034200540c9804181d9a4070001150501400713206000c0f8465200003c040c02c40000444036684282c000030401d12211a05207c401400800c4a80101003503070542c8d2240d8801c0b04c0c2c0000c1010840405942007849103001407480c0d0300003070f502e0f00d1400031203542c5003603139031002030540d240540e201d001000c1c0000e400c0741c0241540c650092202070040360650385881003460116104600a9108403024480100200070aa0b4280f0f084240200218040d050071071a0100043e508541804050f00107580051031094a151000c5010000c55200707000342011505440708400d150068070049020030043d10003d91091142c1c8501790 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 128549766 1250 128548516 128548523
    0xd080c03270105251403030a020c01150f030308040519060f050a09030801140604090507020c0909030a0e040228080603010b040603020307061b05060a0615020d17100306090506040c05090103 83
    0x9030020000e8003860810220034401c0e80c0035400712408286651003840103602c5140e40048c0561384403030f0072100900f1221a24180038481c45191000c0c040b41c0b600700d04041c22203402d03113442c80080d100c2e41041402c006803040f0582203403200030342d00010000e9541058032013803000c0030f08000644d03c00700c1403019036404110003400076070000018006c1d01c003420b0400d40e06c0c107005000c5a04003903d40544104403030f41a9010b80140e4481010802240b6000c484c19134405c1204025500b003c3c0003d8014050305680100c5520650300451101003421200090307500d0070171050b038000d0310303a0100d0901600440c03042c1e8100780207501b170080144040c1840d029000860394041c0042404034603045c0202c60800c08030303081c070711410809a103c40c0410020000c150081c0010a000610741f45085801d000b1442800190800d5400038030000c0f100030781041020b420003651794240d08035591128180c1c0c2c429821f503000100345910b0001d00724244480052100c0c881e91040f1030440d003103504d4400300b000c260000d11008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 128551016 1250 128549766 128549797
    0x9090201080c07020904062f1206060f04150302070204020d0c0f030e06060405040501020906130e1026010b1e0a08010b0a06030c0216030f020405100f050d080c03270105 74
    0x9001a1596000a00104c0c440452340b102c04c0c1d5101074032001c1140c4041c00f4201c100f0206000b0307400a1540345241e00302c102105d5081c5480c0d2100340c0c428060145100d04041d1158104c5102d0b9454003e030101c4038403030742c01002155181040200e40d00200140782c03100001918441d0800590390180c03190000a045120003400d4907034541c8200006028010000c0f241550240200c91403621140c0c05003000501c060484a80c00d4244000040c44241c0200796503022141078208102d400d04410082c044280402c40b01c0165a80120755140984034100d00d00760040d00403204860104440c1d42a400860411200c41c2515983d82c1c40c818260350800c40407507400791040100b0001c190007a80711a640c000b5a00560b401c0090b0703804009150000c41d8001e490584824840ba0f0862074280303d0b4642c0000580780740710015003000c3d08601c0c1c0c0b035100c1c0945070042c0c02c103800e500140940001a901008106412a0303980c2076a84484c04000e1411506d140e8071010074a561130b0198020400d460100d612040030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 128552266 1250 128551016 128551021
    0x30c030304050d0206300c03160f0e0603090309011107030309060f0903060504080702090a050103030815010908010c02010c090b030702100f090203060103030e030f0109050309090711010609090201080c070209 91
    0xc0000b43e4680d024204d078006800c2003d08503826103845d500501c180030841c850080040801590b45002c1d005005101d044420004c11501c1402100c0f0303508404841c0c5060005540000020f403600d02c1c282003040d910400100801035041c1001000b890446003c0e40c0350700d520303485403188590340c012501000307000c030308103c07010700920f4401d41d0302c002408454540020402e5803070319078604075070041c1c44c25a56617800040810942c14186045a001a00e06804010341d40c50b6032001040a031000d04040ca4241c2e102c00d00e5007242e841142e174000600281c0c1c00801c140103100e00d01034000c0c908803403900c012500741c080c00500003403041e054030b00c0b480060300070300488100c10301d525004011a40a03085500e946805c0b00e405a24108a100d010794800d1300e4120324a004007081500d0016035003500d031030680c14a41000e00168021043e60a8010241c038010041e4998000c1504d81c1c8401c54805600c035803030081e00182c042c1443c0c110502c554000e07241d440d040d485402e080e1409101c0d030240a500892004003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 128553516 1250 128552266 128552269
    0x230f10020c19060606080c031014060c06090601030302060c03010e0105090606270f03030c10020c150c030f0f0c0a0e0625020405060a05030a060b150f030f0105030c03030405 76
    0x200350150258041da0001c002e2401d40e210b41c1041101e0548110b540c2d04d0f000c0c03000c20307080401980c2004c1e0f004c82041c154034080a0200403040d00703001d10b200211000c028030620f80c40e03000586040c04003070410b480141c50040500b030740d00e80c0709110950051207042c0116a1040070780089034107923002613115007116800d14060141c6008050300c0ca81e04484e081011600f00c2184501128200701140520448003d0070f0b02082100c0c040c10300614071981082001c2d54940400296034a034403024800d000d40c5410700003507600d05004028048185030403022003004022141c850046200346014284055140c03202c0018080c0c20404543c0b001c0c0e80c900412401d2403031405840e482042c2d030b9000b880c15152980074036003074407941c007102c1c480c584401c10007102c2c40451815009481c4e01038030603108600030602c0c0c0800295503d40182d40500300c0707030341c0d00e03501c0e592a202c07503030200841d14a94961607551052140c0c0308500b5401242c0141c09504020000f24040c503000c9000403540e4002030003181450308000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 128554766 1250 128553516 128553521
    0x60f07060b061209060a0f06140409020a03021801080f0613260a0309140102030402101206030b010314010b01140d020c07050907030903080903090105040e071209230f10 74
    0x6503007540400c041c00140942c4003985443c9201d18903074005030025041903407600060b11125004403000303a080c107800340480a5074601c082c2005c14103d070045002c90090011030710030100d41d00003035000150440600d040c0183e54820504990143c801c070740016402222998840000b9200c0d004404410700d074150105201d03c215500304c40480b180d010900c00d140f08100c1c1c0b240d124440400c0400d84600c001001e002c94410044010050f82c002980707103190a41c0000d100c13940880182e020b111080e100c11008100e03a90002c005968441d107101c40c256143d0130070789885c00304070400c074005600303061a02070903510804910311110b50384441c0b5802c0c8001046410060340201c10710b118284034000c0001899610086424054100c0f13880000d040b0541d0300b030003445000000c10307042d200c0d4402c00c00740806036480740443d4200d0b000725030b800304e107910b4107402100e004014200c0e2480d00b50514100900780051089841d6829100d4800005006200d84029450b203000d805296000d0300300164094000c185078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 128556016 1250 128554766 128554781
    0x180303010303111501030506061017010b130905070509041109010f03020901020102070c15080106080c0a0e1305071707030b01080a1808040e150a0b0a030e010b0a08100b060f0706 78
    0x1072042c0d500f070700c09610070100261401d074007e454035404142400701c2402d041105180300461880c101c02411144100700903451010700c030b034420004001a4034a001c01c640b06440d0b029041c0c241c0d060015040101004000360444403896206602d0000c8240e8030700710100c200c48904406840e812004203001d28260000c0d0480750384241955020007000380050245039030140640080c440b26030988681e400001d205031816000b0805009299040c44241c051180540d00e601c481c500d0144c41002041000c11071040740c101c007040d00a4113007024030240b190060f40000c070008400d03200e5542c0c0d0b6143d0004a05072030120001501203402c00010079081c1060380c004d0f8a00f840030000c500d03200b803050307561032201d41d10960151150f40045024409102010b40320881100001c498482c403203030a1440680042c4074400301c0030181603075200602c0b210300080d00304428141005100e0b00005558404a82c1c8a0410714240d03c222842c00090030500c0c50301c202035a2030f10800f9150310f42003203202c0d03907550014400e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 128557266 1250 128556016 128556047
    0x209090c030d0e09041b120f110102010501241404060302190f09060c02060f040308070b010812030705030907081902040b030a0c051009080a0c030302150606030c1606020706050f180303010303 84
    0x11b41c8007040328400da181c0c1000a51083e84d460750039882a05041c0f101030030950949045905002c010401e0107400b03880034420203943d103107209071091100f00035a00004a05807200c0c28410110f000078486803d0341c0a032480d060600d66112950301042411201c06640b62101c02c08030307499490900060303210300511181144003409152500000081c40d00450300250700071100710100080810410060541c614010490314000308405604400200c0e0a40001000d0390100180803001a4241c1000c01c4100c0081c1201d00941d8420031500c203003041c400c151510142d00990400101d500d05046c00a1140034064001210b000c580d81800b00b00540c1ca03034542d0620301000004040841d09140130300001041500c180a004865440c5d0b182c0a03060000e0b105009035046e082000300003c035202c500c21258445020b030b906640d210b0040341000b042c50300c40c16002d880280301080b2231003002a66405503004486c2c0c1d801e6401d042d9221400d500d2080348500900b01c0c83e4005100410001e80140302400b4081407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 128558516 1250 128557266 128557313
    0x20604051009050a0204020c0d0908030f0a0813020a030b100e09030405100c0b07030504060c020303040302100c1b0c0603060b0304050705060304030306090e01091101141b07030209090c030d0e0904 86
    0x1005c2d000036040e40c000307041e0b8007a540c000e404140c1e4441d402080c40070003044644095800c2c4464680c1d00c1005002d042c01d51303818030140b100050b450300d0110000114090b4000d1180c25000d84030304118095000445491101035815030020070f601040300344e550300c80c544a00c01540792a04042c10b0080e00216038541c4d106110021441400080488080727a12a003850745d40003510303182c18103045064a4141004505540040017480082540420301641d0f10050ba817010071416031030002110400c140c05d5403d8104112450108200000c1c070b800842210360f2540c0070711050392502101d03c0345100950740101183d1100c1e50400c020f003810b402466100c2d0080c01d000403c60340e034a4404059900918181c10107135550180c14080014101d80304110200a1800d10085441800851568072800c00c010251044e0346540c003904020422100c00038640c00b03080b801803801e0041099507100a00c0c07051f00d12030301625800c55041885202d202c1003004009140301d1864940d5210346400351250305c0f60218100c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 128559766 1250 128558516 128558533
    0x1e050c04150819210302070201020c01030603030e040b03031306050c060108010519090c090f1e0605010504050405040204020c0d02060121030c0b070c05030a0e19030b010513090b1003110102060405100905 89
    0x44803013403001801c0d6480d0310701507550002c0d031000a040440c116412070605252180c02d00100f6403040f240085404c01b55000514035950500103031650143c280c0322541d0b030b202150301086099000e0050081c0300d20a208580e80d50b40c80709c45103400d03034904030754401042421a2142c6031b407400c15004140100c0c003561540303240c2912032510a0036200c2e041e5611141c2600c030003ca80d40c4c448000b003002468031102c0d5040009a05100000300684036078800d99105035254070100c0c095642d01d504550041210703100310390030302e00c44182c0a515207409100e038419000840c80196003641080e220488840c1d0b0560703e8030983c407019a60901000c2d0050529020403080e000c0410008200300000c1030100002e032196102c100c0c10b0010001e0040010341201d807051401d5100300001004c0f00c1446040d6202142c1d610307100e404c0c1d00d81c68002491410b8010300445500000d120204140bd00f0340c00aa0b4081c80e00c45411850580c0160794a8038185ea008205074810200f49540840d542e101d480c070705114200366021407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 128561016 1250 128559766 128559803
    0x4081207080403020a031a0f1605070215030f06030f0309030307080703110f0709060b0705120c03310e25050913050a06080a0804050108041e050c04150819 68
    0x42d5400c1c3c00c02c80d0b991090b031100554094800c4901079001d00e02c0380c2199011700d860100d031100500500c0010741440400b113013030001c555500445429014dc4498034540b64076040389101c0b02601c0035a501400ba01684102818100c008001c913140c00c0e0001c0e00451410b04503690b0580d081d07010303290540c10011402e0700b0144034602400292130802a40d40103041003814101940125840c41e0b110b500c1c041401c00a0900103035010132020940784001038201c0c0c442242c02041c2c3d0461180c01404c81c0904100002d10010ba480d60903015100c400845199910540701d8042c44102c0303105561089000c42015002d042c020100102e81c1c0c0200c03454544541041d4002011640034820311486041041e02c440030401c2c0610240f15003001011035200174803010010761500382c805d01c110300540e0704101c032003c0080c040c80103c0c0140c110b03480300380703424916800060070080d46515551b05c8aa00c213604203103d00020b00700090b021426504810007400c520840140c041202c0e201c440300846041d24041c9c42e00c01c11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 128562266 1250 128561016 128561029
    0x4060605040e01050603070f050f060f130f0e0604020301031505180312250503040809150a1116051c060b0907090807050a14040f0e1605090108030408120708040302 72
    0x2402c00000c00400c01d410719004041c02c0041d1600001c02c00180301e1010881c40c0d1b14044002240d900c03c0c0c810580d640a001044840c0380f0603068a189136151403040080c1c00740030712003018201d800403502000a03488040c00c020591100b8440a061500d000a060b200404036500054015805000b00f1400c171808007951030841c1c00000f0041b452a82030010001c101d4a141400205071024003091502c8619561000d09980030141010313080400100305c02905469040400307550b83c00c101112601c411407003200600705201050300c0a064040e483e81d0f00c0b90b1044092540050361002010703900704100120708207043c4480110103442660312541c20b40d84a80302c2626440c007600050b6150203009013043c5046242c013000d40d0040d4040d40700c980c3d041098401502ca404088039040700d01003100d1100d12940005004003000d226514061307000300d100081582d19410302110019200041c441e81c2e100403071074907400351b8482c02e0491b400c510b02840c40c84005400a003281da10590146041c1612500803501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 128563516 1250 128562266 128562281
    0x7021e03100605030c0306070206070507060902150a1803030906030b010c0803090a031b02060d180c0902030a0f06030503030402041112010f05120c03150702100f090c0602060708010e0406060504 85
    0x74541d036200c00d0056040a2202d66640b290076002010941403801c0025519400240139008100022640c001080825002440c403503400601a991100b101c884031090303603125104903808154a001d4640e100342c45800c1001c21030b0340640760320051031310340101500a011620341290400c0f00e800e42c1040012140000341d40070300e050500030302d1708516500c0c018040e1050b5012290407085020b0038400165211011207140340780f220004602c0c0c0c241c1e58200380600c5480c10000300400c0d40898003080301c65040d401b070b511802090f01c1c1400702c000318100c00001c5885501024003c1d400410014000d410580c003c6000c5e2241381e00c4d514601640500204810542a00104c02062400400b00320394607048080f41d003a4580c0c000a40148015a00002e43c0c4e040d11075403011000e101c49000803c124001d2014100c00070740c20384c05116603000b40c6540b200409152400b2a02000f4084010a203140300040d00c52245045071143c036000d901301010000a880f00801c1103905d030303032100c02c08a0f45481d40d029006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 128564766 1250 128563516 128563543
    0x5060d140114090903040e0429040506070e0d03020318030c06040e0109051803070201030c050d18050d05070507090b04150e06010311311d0a050c0f07021e03 69
    0x92002e501d0100107003640054513100445e4024401801150755411206401503880f05c1c40000c00c18003041140d100c50080205200400c030000104403d000d4041180c0d4481c04441d83c4059a60144c0f408004183d90b915401a0050b4003d020048104420351100340f12030500804a48003001800c000417626441500060505020340c0010005901c4902819400041e2501c4030101001404801a564011b161010741015128001400c03468003d0b0203c413200071704c3e40c06c02c2c007640240040c030403408500500105d4482c07180c10030301d41d540d6210b14203848401d0f600c0800303080310368580204030740030341610380d00316030312640d02c121002c0642082c00142000b0600001c0c020054030741200050704071480c00d010101c03100400c2000d81c804007018140403000207101c1e080c240d888140440c00780c0301028281c00c4045408020850401400603e040c241c0c81410380e8001400142d988043d001c10038080c000300000101001d1083c100103240038581c46050889207405100c0d0200c5a40009140410072940d05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 128566016 1250 128564766 128564789
    0x151101090203030721020109030516060f060b0403050c0f01080f1033020f06060607030c050102031321080402010c05010f14160203040f03020f0d080703050a08010501020105040c05060d1401 83
    0x3d024042904c5ea40002e80400c2c00204a142e1441d100a015407207170510b8400c071100c0500e000b0040140940c00903130513481e680c204120441d00e889844846900601050301c1c4e5124040340100a4900350034091034120041e5038030001a21031038818210518040e14400d1044417440d404592101020b0301610078a0703107006500300e03400400c00045c4c1005024009601150003c14448168040005910b42c10000035241550b076069507040884041041050082c8254000014803d005030106800c4c003445000d01004081c1030484403440320541051140c0700b0208840742c00244c05980207151100340c640c012000461110405520401152481c0d0150400c0801e100248100c803400309040d42e20401860004520340303070410b142d081d107002941c0b00007440f694030040403104607203c000d130300035550707034404074454a84490780b0780500680c00401260700000c8084000084561050182d640199000003001c1403483c10032083c041650301c40d0088007446612920a6030f10000c44e54825070082500203241e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 128567266 1250 128566016 128566043
    0xf020a21140a0b07080601110109060506041401030b01060311090d050f210f030a020f04080a0b130305070f02190e06040507030e120a030f0f0b1005041511010902030307 74
    0x7192620078001111031680004125400104040300301508000a410268400d684080040340c024040c3d000e03421455081c80c40c00f204016840d0045409a842101c05002c0d01880c070340401301000302440040c0040b2101001008124043c0d4040d4a01e240e038100c3c0e00d807800301d0030400300e40a032028032011503081d80050f11080c00640306200c041d09010070001c1d5850005071540e20b000c103901400d8440c1410f001d00101040c2c00300e40c01d50465000a05a400243d15103035075401c80c0fa2900c45c040f070706503030102242001403c0b0070000d00075480c1e925407688505060149030388490500c260300c0d20b4126084850200303548044200791161200030008800381c6100351600205006c251000a0150300038503091450303c60f82c01e040460b018101c072030300c4031100b61030319072111040700581850f00aa071651031402e1180f1016000b80d030031400c0c1c1c485040d1080742d20440c0e104022141849075105102c43c0b500840d480d048074910038002c5110860b140b80020402d03813440c1c1c00190031a8030a80f80ac443d0440103009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 128568516 1250 128567266 128567273
    0x8040827030c040b0a1e050d0804140f0901060507020a03050f01061814010302010c0c03060501090218010f02120705030d06080a02100206060f0130020c0709090804030f020a21 77
    0xb074203a181040e01c05008142d04c850102da40c8003070780e0103040b8207404880f5841c0541110351410000070040107018680c14100c60604100c50361107170003106101ea0104c50001c1841c10015161401d055002d01941c03516803920608a8140d000f80030101d90141c0391034000400320703008009a40b5404e0140c00000b41980c64076500142e030b550b0317002010350f0f4a07050078403011982258045550440350203082484d074140300e80c9016000c44c03440f0340005207210314200020a454036a07601130550070101c00c410754400d080c0f40c0015110351a01c1c041400040c1d021625400700d05140310050003406110300c044a040c90006c2c15260161242e0b0307000074185178044110501940341050386c410042140f070001d440203062000115440c08a02d050481c140034040641901c2400b00c2d8000101106240d111081598140078080019611000307042c41d0a12850b000440c83c4070b4a88030f0341030826400b030980d40c41c140c950756440c101c607800310100b40d03800040c80c1030002c2c4c4a588502585941a04502d2080c8a240141f8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 128569766 1250 128568516 128568523
    0x2101060318050a0803090a080c0105160201140c0a0e06030c070c0b120a11040801090c030b1506190c0f0b010e10120609330506030a02010903030804082703 68
    0x14080d1044051014004010400110791002c1244d0440349950792a0b407446031040c81c0c1150b13000010071840c800104004000303010342c0281d00840c40314424060383c10142d10700b2030a81d024052003031003000009012070400f00c0c1c050300402c3c0c40c10050034210054600b8000180f07164200f03c0d40119880c1e000200e4404204d800302c0500c01820941004900b00b080c44211100c051200402c41c900041e921180d148a009039501560000e00c0d0140080c040c181c03031443c0500000109110440340c202c620404030b10344c0742040350300c0e64405001500c20350400103014280c01b40c03040c464528000b030001c0b4460071030200308a951450141070280131350703203240e52515441d080701043c02003004100d1304101c10b050001b070b0b0122021080440d00000301080341012400e155201c000e14590300c180311070300c408040305011062640303c05100324118040059603150014952100b000500090000d2800a010701c0000d010300c004907002070050103010b0604480d115a0a44210f04150110803018541804031280c6000c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 128571016 1250 128569766 128569781
    0x10b0a05030109030c08030c04051e01140313020d150606051804050f06040905011104090c030506120c01111005130506060102010605011d0105120f0915010602060106110321010603 79
    0x1c0c0c0c020080c049240e1401400032100e01401041e046000000c0382110948006844c00351038001e00640c482e00e554000c00c0d844143c15015140480d0b1340104942d5110100f1080d6886003081e00d920744c5a17500a5402c00800c0408088102d544035616100c1500050962058901414180e11116500d500e0b04c40d02849401240203060310542c1800100040043c40402d541c4d080031090f2004104460503182c0940074021408010a14040120b00029001c50a0f001001e0001d45600c1c10442903d88038180812201900500030156010b0049002a940f250000d00840454401501c4903907054009240688609540c41170307110788034440030024032405111654001409000030040b203481d250020703003c3c00d4030380300004105512414410459024200302d4045030030038858203c1030329201c212004295402c0d02d02d0525480340004603400442c60010300c50680d680c0d600145690f0b81b810b00e08035502c1c4280712544050f40024480124100102ca441c6400e144461008503406c1d8140080141214040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 128572266 1250 128571016 128571019
    0x414010504110f180708061e0604060503060105071e030306060f081501090807090e01050c0f0f07060905060a060e060102011802090a1401140306070e0f0d170705010b0a05 75
    0x5040c188030004081d2002205804401d07620800358101160000c1d0000060101d51102070850b0420890410341c48000944140d0b411905180307502c986106144800319405410750b0495002c1100384442806203015582c04841490080c1c41c100280c0c1d00d03000404c1101c0c0e141d180c55214190f8140400d03805000308006410b682c6000503107018a12801020030101034040b04910361000c0c2c102286900c900d070030300040d0410404036208103694040503001440da02d06d03441560b510302004505000804811a1011010603840f181030103600c0aa00b605688860021501255948140d1000510900c1030310b10540c0301d4000003c07080c1c5000d022084110008107a103045900d828000350920695440c0d18040c95016118140d0580e9035600140c0184501140d50210521200001520180c40260440010301c10760170340303916403201d940030341c0c50241c107064059000d080000314044908201048a0a0038012624800100801d01d050403081c1c0c00b041042ea200c3c1d444003040c041504101c00d440000707140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 128573516 1250 128572266 128572271
    0xa080a1101110d20030a0203030a1d0a082a03030708010603060b04030602070c091104140a03020906120a06051005030c0d03021e0a06060f06030b090405061314010f05041401 76
    0x50041c1440c2d03c41c0880d072500d50a10801e411000c503003c401c24041019a01d0210840c3e0b940c0e2101480a5502e800c01c60b0145030b82c50800c0050448080e51036102a210240c000041c4810780090b541c40b25603070480c0c3d18130160807000c10485204480c43c0308100903042400c90107140d0f0390401301e900400d4881e05030400c0040c0750400500300007503049070040710f080300e411400041e19510586051104180b40b540240c6071113050440328200450300304001d00466404900d0041c242c0341607024415001000d11010354000b400302e0000c0c0d400c4c20142ca040d100480d030082078640629490750303400120b4074103444a00341511800c3c014881030400700130488d02c91404071000c080c113408981e0000d43d900714172040403004090842e00c00100309410041034241c2c40c0e0040091001603115120100f0400040c0b055000103030034011202c6040c106000114050754012010b460b86d50384503146003e007a08144c0c000c69540d0010700c01710700b40140c01c1c864505040ca0340000030a060400d400c10189904015808108603417 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 128574766 1250 128573516 128573537
    0x302031509060f0d030203131413050610030915090803090d09121b03050706080a0b010305071215050406120201020f0318010e060d0c091e050a030803150a080a1101 72
    0x143c030705961841ca07200489202103810024a0200d08500400c01c000c41000400d10300410084071040000d194440e00303481c104940340010f00c004040d038005540d1542c0107044a04c1000005109802c030f0307142e407801045c0040a14068422941c100e40e40302c5010b8800038004000e0000300003042c8034001008ac62480c002d0f03a89401c0a19036100124000e800900141036a460880743c0b01c40011042c0003141c1200654102d40d50703440002c2d10000c01158006542c1d8a082c81440303056009101702409170510380d88884003038846170201c070300074410074082600100e045100003456030f9550041c8009040324000c042000140d034030001e850640810007040b0240c00511a6032a03a0058484260b1100340918014074241d0040000c119207105400180c1c103043c0c10700310300c04455504a0103840807540c40c807070030720403250155400007541006c0c0d00480ea4032080b40d20702000425509005940c00010f100a040807a03801c0000040c4d06005a901000d41a0440c1d4241c00c14080190884140c4d05401e01f440000704 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 128576016 1250 128574766 128574769
    0xb0303030a0209031e0a05010c0903110108090c03120c0601141305040c090903021c0f0207090b040204050d030c03080c07020a120f0204020310030b010b0f0406050a02120307030203150906 82
    0xe010041030010510350115008041e0f0340d040000d43c2c0c1009a6004e20380c130028120540c01e4548125a00a607455820203158041a900c40d51600b4100c0350030400680500d80c800004445030030014000c055540b064000904180d603052100070428100c3d07605c255540c016a0b81d2860501c07405a0003000144640009404580c68480344003000080911001840c2d41e11450021481c02480e042072150740c2c9000480030404d03400041114011592160104148281080c04c555000700600c4800050704200130821400c125508030541a03000103002504088d1100f002c1104a81c840f03800f9400544454645003e0542004407181c0114048841529000503a00031800e0104240704041d00c1d120b42041240510044c01811100250300400541d6641413085207916455020f000560b0515000c40002405869040480f1000c104100440b4205441d010041e501500410125001e500410441e00c0707010080c40300941c400d0551b41c40042e00d074206440c00200c032503864031030a4000c0d0406002d2000a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 128577266 1250 128576016 128576023
    0x60907290714030c030a050904050f040201140903070810020310090504020102070b0309010f05010905070207050301020c061303050f04090f0b0d0201121a12030405010212190c0305040321030606030b03 88
    0x1564200b6840d54101015080d090f143d03204040400085000109041c8102c81e4880300038180890111030a02454441c40b2032030817001c006680090204a42302c0b101d40c41c6480e441e002d88604c0324003c0544450542e0360300c00b141403101030315014039030700d90010400401a04503011200944400a001c00c914030f01340e030000c0d544d2106400740000601000c4000b81c0891001d401105040c0813421040c4000d5a58101000140c40c0c1600c00b18054011404086140d003014030a4446030000c142c010503c5031540883c0692341084001c054041200800400900f0782d50701c001170008100c80c0d0f030001070581b041c00403481110f0903025941d106010660100d80581c0c2e001044814440044600082d032406404d01c41c1203501c003045038140c0108403410400c503080700c00f0016004541d0b0a03025941140c40071000d401452040c90307103440314244a481403510252080b000b00c6003240c443c3c00c0552509480e901c82580340c45020500e00310001c51044162842c5505018820081c5000d04041c400c41d030084e8000b944 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 128578516 1250 128577266 128577277
    0x70903120c110409110301110711090601110a03080405011a060a080916060305011e0803030109180614070f02071a0705120f130f0b0304080d090506090729 68
    0x10481d01c12021014490038200d400c12540005004001800e81c601e02141c1850800300c0c01803095290101c901c41110707243c4d040742d940741d6003c5000c0b1180d100940c00c000a00340080c007142d040040f202110010b0798810481202a5402074441c01010b107442d2611f00c0c00d54055a8407040030406040b89400b85440d0300d010b941e041c0c401828200c01c4ea584e4419481e140c51489030708040800317810b00d00041c506802d0360006041c0c54000c082c00103203c007641031078804420341c0c1c8200c5090750300400040106c19295480301c2c10f500003110078258030609a40b220380a907600042100c98118441c02404901a040020b0b0f00c00c0001600241400e1072908891050100551b811402c2b1a00300040c648c003004000d201c528441c1c0c0945610f10b03100c440b00c100d0104242c000740f0301420f07045c102d0301c0040f03254100000c005045600c80d80100c0c1c50b40d5616a43c280031034000d039442c030b00041d485e0010100025800e00216104001a90081c600140303010740031920650a0403403d801139030034841d0a91343c2c0442c2c00849a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 128579766 1250 128578516 128578553
    0x60b0a031a150703080a090f080f2a10090305160f050102031006081305030a0e010314040602191704080309030403080d09021005032707030c0b070506070903 69
    0xa00c00074409002000c0190807841141e101d1442141d0380040782d8004054042039001e90b865942664942c441c013001c0f10300c010070140543d200f00360f01d100004d030721400500d80854107410041c10101c17541d5200c4510062004511100403204002150007102048229244001c480e014881040541c038040c0c6240320309105140c02e90a0f122216082c858003010000c1c4266008000715580d2070411244031030803d080c001c410001c0e01c00c01c04600400a80023080302e0140d041000746203858100c00c8190740c001c1000c00a076040c50b455440e00e480702d500d8100441d102e240500700250f550504c0f10341c00310f0780c2020180c1d041c0902075500117003402042c02140696000f03900102f060b03520b894600210340b03180a26800148180f00004400c1364102d1140c0103031040700e1003601c00030f460b80d00325102a181400212914004980701003410030110301c05143d100d00500b40c60041d12180343c0c0ba900c0f01e40e02e510301d0750000b981d5100f0014806080060400000b503008074075141036231400307066940d004841c08018030000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 128581016 1250 128579766 128579771
    0xb0405130c1e02070b0c060709050909060a0b130906050114040e060c0c0a020901060e031203041e060b0402070302010b0a050603040c180b0901060806040f06080d030e010e0313030b060301060b0a03 86
    0x12002070300800480740517142507621030b61601c48079084955a110200c0700400051240d1070005090f05000300400d0140031504054911541d84e200fa4a006049000071030740c0c071040301209545144058400c0540560107258045655070500484e0700406103c101140d028070300d44221030340200c0001c036015410980c0142b8070350b900d61041d47c009241c400ca07140080d600420590000609a80001200906040c1a802e0f54010122042c500302c03e03000480b03000d0030783c00208210320b1b1114020294506000d00c901c0700020a0484100420100d070403080b0f044000d80c0d5240b4400d02c051a110b510f940c01030404176003444c59072802c0d648003010030906102d250760308002030303400b43c509180581050f0034461000d000009550394401000f071184605a070303c41e00503842c0c2011107042c02118001c980654030840014483c484110404500808500c034203403946c3d55958902400e610b0040c4010128201d406002100303860442c00c2a02c8980f6018000da40700b80e04d8000c0801c01c468010702507484442150400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 128582266 1250 128581016 128581067
    0x1150501230d020403061d06010506130e0712050a0608060c07050a0201080c0702030319030e061513020c01020408010501060f020106180504050a05060403021c080f2d010b0405130c 79
    0x7280007034040e540008004908210047c0845482c8401c0070500840c060100d64099aa0b1014010948181820325501c400d80c800c00307000460302504200c1d044956440c20098400088110380120745d0700303684141d01182c50704810004890100700a580004140d89414603204140d030380c0d1a941c1007401802411720200e107000a41101b004800c4e20307180d54020342501d0351840d488810403140c20904c840c510101780f0301214410308400c002907107841200e02c505510100b25090f41006a4104041e000206281d002c01c500c907000c034030030300140c0024010071001142550600b030340503100c00c80306a0314008580c5446020801c45141000e21828420740c0400040c076034070303241009400c0c41004040600240f15403014801003542c00101e1461004480200340600c1301c89810071141610240c508040502c028000303d440d00d1300702450f004034100810780040c2d49150b01e2080040d442c001b41d02c1940a1000400d00300b00c00e00b040a80040e05d001881c2042120062032400a80724103030310001c89510b208403245 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 128583516 1250 128582266 128582287
    0x10c080606120709170c100c120302030a09200a05030a0302061303030b030609150604140406050c09120303090d09050603280f06080d020c1f0201090b090115050123 72
    0x10080500900e10000d600781c0200c0168565030006c0c584103d0180d8100310010030502d118051060080398000010021103210907000ca000e9000680340d958015621204000010510700c0995100401c402500403500c002c1410480c0c000d41c1a80b0103230194202c0c0e8142000070f81e0106400b640b110720003100f103180440c103040440040038400c4055401d40b0801046c071070309a50000c0d05c0860400450519070082e034a503000d1005403150401c091080800c034402240014461307030040f980c0511108401d40c24a140040007409400c2d004003c24002d030000028080124428025041518424100700c0856490b0401142d00c0c3d2000425060103102c0040980c1d405125a48401d1098401c9040074404c0e04180c0400c400241060f22034011107201c0c1500b040781140c00410f101c80b1010004046000380c080264068128a54403074100c405c555070b402c0b6000007c3c403409500d6000e107601400001d0303001da001940ca8011203403500b103541071204040b01d040183c640703800c0380202c0d151a17864183c0c031140c0166 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 128584766 1250 128583516 128583527
    0x2c1e0109051e0c060d0203090105100503030d020f0c030301060c11030712020105090a0936020d0818030a060519050103111e130c0807170a050402060d140702010c0806061207 76
    0x10000751301c403030000340b03581007490280c010310b0055501c0c0008000039102c0c50814005100c4a204958042d001446a07801955a0f030707003e002401c0d4000d03203031440d20f405203d4850070f40d4000d030813040118031620070030b03014801e100450320458041075004158040c18400100603081489900a04100307000400f00090346413104694000e2165206c14031802c409000e00000d045418000340d8a00321000040514030000903002002c0d40790042c080410080054403140078a50203664043c072507181514900320303a030714104800c3d03202c580511800111410000803940003840e2103807625807801d06110050010a401d11500500000100e40d140814581e64240400c4d8002906009501076190141551307916410b8104400000c0c0395510301d04140e88100c4d041d604541080c010300c0140f0031045c002f070060350a07a40000d81142c0002e011030f041c01c40700c02085040e5061010720b288034090000606c101660240210307074100d021401c1c0307402d007443d1038404122075001e2100035580418000d07012410303550160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 128586016 1250 128584766 128584783
    0x60203060d0b0103110f0105031528030606060305090f0d0e010e150d0e15150d060926070209060f04240f09020307020a02042c1e0109051e 61
    0xb00c0e0b8600540c0d40b07040c80012000c8204e1a1800303040c0b071904681c940e6102c2c408407840364000300a90030f0304214100600021610031028406031450b504035984412101107841c00080d071040ca40440c0050401c0401030950f14050040e070300c035602404001000b04008110000c0580c500c1c070302200c251003450b00480341c802141c1004c03034200f090f0390321141c41c801400d00180b0345400b159806002c60508918069921203401d8064042522102c02098000d440c00e0045401e4500082c581c000785c0752720b900e8500440d408241c0c1290700301c5d13500350030005200000090b403403282d181041c181d003001150740210741c6421004280d40e100c0c0c203141c60f00d01e20703642c0c27143c1c00211b1b101032a0301861281400155800900741e000c1c001d24101d901c0354440003c8101c007031f000301c0b0720404803540904031507030307241c0d0078800139204180030880188091a4202440f004010485c03112021040c02060036003c01440304050715217121844009905100ac024081100080c0702240c50900d0030345540c2c2801e2104900707041c550304 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 128587266 1250 128586016 128586023
    0xb130b0402090a122a060f050f0c060601090e0105030a0303180f1b050301091e0309050909070e01051813050102090904080301051c0b0c0a02030f1b101503060203060d 73
    0x503c20106030b91080c400c0d20191244121000c90710300c4884c04500c10840801c040c1443e0469800743d0600c01244520781c4400303d5002c030308102e0f0400800796108440e80d0043c5003582415400f41e030400400d9030f4014003002c01849500d141a285504100110380c44168180025041c551140d803401c06406403900911003540c1c0014400c0f8080c00e181c6840d1030141c242000c03a60390052828400b08240c0760600c19107005603403248003921190540c403210a0340c4c1408540503410304c24040c900195036124242812b21540c4078030050080d0030709081c0304244890042c3c10050194500612003408428220002a08440100003910704228245800d03406849036030b862a070840c201000303101c00c021204022710b068070b10442d4803038000f141c842c078481040b03081840e0191903441444042043e02d00c9070f030010060740c01240705891030402c4c110070414007640041c10659952038041301071212068107112547c1c5800400c10103100071200303204103401e140f031540006004c4a0703002020404546d1000a4880503951 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 128588516 1250 128587266 128587279
    0x21e030909070206061f09060c06021204050f0709020c3a0503010e0106020d020a0b0702070509010e010305010b0a03030f0e06071505220b0f06030a080304050c10030b130b040209 78
    0x824500007034807060241c5800e4014482d00110030300c1d4a1786206c030f40d0181304042d40c4149556150010440d180c6041c0c160940b8060303030170003001040c0c0000700d0f25a40701e07a015000500d00609041c1040d89008115802031010f544140892003440d0741c00709407000001406440074181d200b25118142000b52541c58000924861800d00c1403115000400b03503048a40c4514480c1141ea0307a480140d031a608404000c4c0e0060b08101b240c4000a0700b4040d00c43d0b042503080c411140c030240c498010a000c1c05082c1c111441409100004004001090150301c0c050001699483c0d0428a1035078068055540d0b00406000e100715a00b20441a03280e103801d40c0ca20716042f00000d5000026101808014034050b14400a5140008056405c1030f07855900e107035147d1781c440000c62603944d0b01070032400344100c05812554140030b800828408540401d001e5405039001d00301500c3c2c6900104200300b400da0091010405160510b0413140c220360300c500010700c104800712404184004294006030086c030600550980c000d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 128589766 1250 128588516 128588521
    0x180604081b07092306090f22030237060f140a140709050a14030f03120a050108061e090f0706110c04060e010b0705010b03030720010c03021e030909 65
    0x4260415012104209a501c101d40300c0a00711a01a0104680302e41c2c0110300c0d84003081c5894201c0310307415840813602868400889441c4405d41010940c0c080071744c0140d10a8401c94540059042000f940400c9403c4003060400c2030003c1a600b0b02c012f50014254a6507018000308032240741c0c1042038440307000241416039142c03210144004220201c8045a0b5801c40c000213000c0c0c0e4060a0750380181c0d07400134110580603103016440d204c0825020342954050280007116201c41004001801d001ca2000781e42141500e0050700050445505030320400e801d40c850010b02c03894408111400c0c2090040204000e19552a94a0f0b1894503500000d646258810124001000341d44140c4e038400c1945990190340314000030381c04000541e42580980b012030f0501030010000054070380000c0c1000d43c8075400211369840d00000007803c50300490707070a46030307903804080c86068404c19046a0241100034202034009600549009540d51942c55070303112110050310b2048a0480b0800036079a0003a00205001e26a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 128591016 1250 128589766 128589779
    0xa0210030e0712060c14032a0a0309021003020f030c070f0c060915030905030d0203041b03050a03030507030c1d0607051006080d020f1b060d02070605060306180604081b07 75
    0x502c0f4490140e8215180c0070031141514030940c032003204180c0000c416800c5d034850a44038100106440c803149104140404400302c1307036140001601100b501510001f034100c00c580140324407001d04e0207070001058070402c0600d0a03182d5070f1050700c4d001710560054036103401d45854400d1581c1041e01014100400b030300e000203100382e844805c03c005c0d50012030802024589a030b5080d81502e140f0400244543c100b40078088885c0e4580e8051984a406208050b18075580c1045402c900407807500f040e1400d0b040b104d110801d15815029840e007180652170200f150351440030300100240040c00e02d14950100312400c600013039403040140e911a03038201c0c09550b2810f02e850b00d500300400d200d1040411030b029003103906000b14004200c003511548000054130094083d1481206c5109508025650245003440300823800f40083c030162056511880000a01d82401800c0500c0c0020040c011754900305900715404401001003200c2d50410b500082e8a502c40f00145400317140c2a880100d42c030310621030070100080700d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 128592266 1250 128591016 128591039
    0x509060d0e0c0406060c0302031603051204080903120f070b09012d0e0304030201021002030705040f030807050709050606040605090f0303072a0609060810181e020c0a0210030e07 78
    0x400c40c0c02c48041050b140e41e105c0030390f51903c04000160141e0024007041038584ca10098100181c1d10900d0701c00c1ca421903400c0082c00106e402c2c0c41c00d071031054002c2200320303103030808100010b03d0100990280d03082c000c0b45444000d03540724002000300f1480303100300404c000c00000d4100b00c003900e0b02001d006550703000000c05803840304280a000600281801c401412107074021040350b042d283c0607809080502c6102d11248040c0d800a41843e04003c020000040c00802030000386015502c18521181e03101d03880c4c10290b11740219a00008030315803503c414403000b80e80e0401150100c0b00b950a100303071107400003000284403601c5000015014000015400200720310700030b200008070070317511545c4901000514000ca41c00c10300d0055001003805440c0920401703018140c407551210340c5001800340d0a440c0c08828141e0a5014000c26010f602d5101c8890001519083d100e07160002910440c28445080c000559507011010080c1c003d80c0382c1c00f1072501a42c82a0080040003422000312400c1c181c1c0c1e01000c414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 128593516 1250 128592266 128592283
    0x30f01050703150504110a050310030b0c0705100b0102030414031204030f12050304020d0212031c0203071103090a0e070909090c06031b0903110303070605010f0f0e0c07030509060d0e 80
    0x108000e07845800b1556207490321800f06002410341b82c107420460b100105550075440074014054441d1464400800a01d042507864440c1d40c1c00078000752540c00600c1c0051030081800221807059080061800c00c590b4004140c6048641002d0003803807129010011a04080c80283c0710151603030001004020f020651aa280322070f840750b40281101002858212040d010a4800943c8403500703055050141c039180300d8542c484480f401c00e5914264100202c052003200e9000900c05080e0080100002141c004411122103854400914035080c040b100041641549020341741e0700e000004c0124140e0351203558250080c02c0c0c00340d030800000c04030f800c0c8441c00030000d00c2802d0019040043e055891281003c2c00c07640700c0c26a4442c0b02c00c1ea0b046903100715a282c0d003202c1d02c90701071009100100119281c0c0c080c09000380008552011154102103c0e030340301d081c0c29044001e07442101811700420081080840700c81940501e4000d03222440c0d88005066071003091034003105c03039007440c10061242d980800c40d4171 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 128594766 1250 128593516 128593541
    0x60506072114071101030f02030f0f18100f02040b0a0804020312040b1605030d0207031106070305042a0b0403050d030f060501020307020f030c030105070f03110f0a0e030f01050703 79
    0x10325a41505070300311400451450012490034050241800055425000c1c01c60302e6014140410808890120311007241c0003140c1c418001540c4a0a000e103415200c49105d4100c0c2e02240c103583c0d0b285540403d240c0d500742a058450340e0a80e0307010f404e2215112981640d002e480c411820640d28614000b0007841d201046e601a442070041d81c6000e40540c903074030222421140c1051040c2d040c0300c428200c0500c400050034003681d00d80000c0041d64908000ba10050030241d10030385507500480b450382449443c0c214020f012806062800c0244800b0804500ca81750a0380e0101711440c040760311040c55081800034a03481428204c401260110030020041940030844c0c095a40c200601401810703c0310a40d05103202c1c1c01e0150b0000c001445c098109044001c4040724064110343c1048000d001013401c6542c215100d90024143c0d002082425901d80103a054005600f4001420a890030300c042d00c1360f00c104100380381071007000c100d20821a1010b10030b40440c0c1c83c018000704490b2078040000340c040d0419903483d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 128596016 1250 128594766 128594813
    0x3020609010c0903020f0a0b190305061009051905090f070f1d0103021e0301030c0e070207030203070e06120d09050117130f0f0f0602090f040b0108060402030a06050607 74
    0x105003090502c02c5646240156940108440c6181c0074070420300d104020140e0420701d000c2c2c1c08107095440400511a00c01c1d00d14502c00b03240103c580090407600c2c0a024240b21703901d151402000e5541c003054100940b1000c40b03044040f100c0105007600c0c0000d1562101e40c000c0c0300107041140c0441d40e281054419501a103e03004103455213401143c0c00d20300c0800c084103160fa03060300c04034294803d03406001c8040f600348032003401c03406403141180a0b4000b64001c0301d83c61a032280900a60941a5103d0740180190005010300ca04590000c0d4603075034030b402121417014034640000d03600d94442e000c1a600024000a66080c0b40300c0c1c1c08004c0003085280101408210817800d003164019003100d51300d11900280b151038a0042d01551240020100c160003a1204030301c0c019000701048601008034880e91240e03900603034508032001840b141000502840d0300c41c3d0310300000c106840c3d811140b15640200c04440040c3d40f680c1d1042e002e00180340c1508803581020001c100c0c90100001c00030a00390dc45c8141c040c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 128597122 1106 128596016 128596021
    0xf0c0b0411010c051614090903040302090c090d03020c120312160e060a0905010e0603040305030f1009060e0a050a0204081009050c0423010b16031d0603070c030206 72
    0x140c004050246401c0003031b500345040700d0411000c26900c543c0b40f4a402c0e40c209480b40518400a40903010002c00a03000f42c1c012012680071f440300600d020605801070400070354564031044d516000d2013060001503151413002017903442000340d4888141e004e5540720610546540c0d80864041030211940c066800c1e561610040d101c0301c0c0c0f0341c0e980c00d21590300e0000010001000240c0e04c900a600400500010030b034400100c0e075020130494404840c585501004248154450f40000842841d113030001c16180b1034141c407a80130383d6098100744140d41798011075008920452081d8000c41c1d0222a443d800300090740c00100120340690140e802291490001c501030700c1049541d01c0781d2040069601d40c0c6400c500c42c08502604d0611209030502d011070f480058581c04000000d0309100708012211066400c044108000d06000b611454503030802d0070024013280010a4201c001d030040400 = true := by decide +kernel

theorem cover : BRFrame.Cov 128417266 128597122 := by
  have h0 := BRFrame.cov_init 128417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 128417266 ≤ n) (h2 : n < 128597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
