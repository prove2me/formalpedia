-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0592
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:37:44.020849+00:00
-- url     : https://prove2.me/submissions/7fc6ecbe-ca68-4a63-ba24-8de8fab91889

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 106294964 ≤ n < 106474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 106296214 1250 106294964 106294967
    0x50709020711030d030b040605060a081308160809010206010b04030302060a11090301020c030409110c1e0307020901060c0308060301020a09180207020613030312020910030f0f051005150307050403030f 88
    0x400e40c480c42d038260140c03002c0310951a6040d070042d441910202c504000440e16031052240b1405110300407001308100001083c0002055807900c115a445a000c244c40c11800740c00d290046012003500b2540b505002c28107001d19a0140b20207030141503042501c03030815180da00c0095440d800680000340c05c9548001d015131164001d4129053707038002800079544e40401a00803542c9070b2251040c2d641052400f00415050181d031000c4400c3c4034190001800060850f8076040ea241c6001a0130380003521042003002c006031101c000d168024a65a22000103c2d65203003400b400101e40240403600c2a48108192680c968014003604162038254400700b02494035088520028172a100000e98441d20108203614000102a00c00742641d200e0ba5525001c0400418894141d00512a046520030300034017545001030310a6001880c1d00341440004070304010100844401c03034070195603000200e5016581400142000000011000204041c9515502c0c10305030040c00b60046001c001e0404c8084070390110301a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 106297464 1250 106296214 106296233
    0x7020a120f121107140a020904060534031104030611280207050906061306050c0115030f11060d060f2102100e03100e060f01050d0507090207 62
    0x140c0d000001840100004102810204019040000003210800c81c40b5503054140508401102d601010600b840402d9a034140c080b02c02e0705016070507102d030046450150b035640f224070740038501078100045c9500b4041000c0002458401c06c0b400c1e1b55624220352240000244d000b1101010740d450006210030710b84c00140c107544565400581143d05102e80d031136442d64210001c04000d05007085903c50b0143e0707001130b1400c0700b60881201c0007580003050104014244281400d0380038000808981c60042c411815030000041500482d0010b800403a5040a9180074031401501040c140302c1ca8091625558502400e00c1e40301c01c0041004005c1c01c0904559110031050340c5d00381c503003200c040c00866140d06000d0b1655802d88244003909248502d0a0015455810144403480d00544400c04640c40040d003950240169548039801d8030a0002044000b541c82c8500031441c10244040d01081c00d101420041c1400181c0010344214610419040020800510842250301006c40941c85e28014141044031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 106298714 1250 106297464 106297483
    0x51903020919050723130305031204020406050f060d0b01031e0507020709020a05090d0c051005030f01080309010c03080a090c080a020102010e0d0f0507020f03010204060503100e040b0a050702 84
    0x10401d141030120800e040c002d1200b4560b04190100015075442070200c408030500c0e001588059805130075038600030741c25030090200030301640b005081c4039501e80d60a46564800030454410b021004e00380700462800340240c0c80286811101e50000d0042000010154480c1041000c440740c2e4480000100c0d9000c0d1700f1900700c40ba00a141d000e0304a0141e51030a020f0482280c1000050003882c401050407040d62098a020b001c03140e480c1824409007105000d90709403d204140c1e0a0b000704040000c542e510022031424907200c0b59103036902c9042c9030414894903001a00507010b19082070006040ca47da1083ca500c100c0c3c0e40520780b0118035250004103500038022084041c20310442e07014003003622180020011000791003a4000c1060003650800e0a4540c00001d4111000503165540168001e02c0388000d0304403580010200264400c04100003800c990007039005a0210b1004000c0081c0b11715880c3c100c000401201042e800c00e0314041c3d55130044008018610030300745603030350701160440f442001030b80f80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 106299964 1250 106298714 106298719
    0x50423040207080318060705090f0111060108030409060503030403030228020a0b090108090604030f0e01030608160f0902030f04020d05030d06081006050103060e04020d140a03051201050105120105190302 89
    0x644018070704090903d684200e49085150f0742c0c0300e0920400c0080010720503c10b444960b22a403c189480d82000300000300e442e800c0e030410400010000d0b0310305041c885a4000c040c0d0350020340d03580e0315100050041e03d000b0380c00b01d84260030a000420219402240c50750010a151900b07101210301c20f01101c1c04035020288c003035013003451020003080042d001d0004000f0340d01c00f600d0f07081e6550781d158850381e0748400c2124000d00041540681c40c00c140d01070300c0d240f02d21240504021510588840440d894612000800091868824400c0180a0390720844101030000100e066241d840e002845000d01500644003d0164002e07450900c00c1c01002d009481554003c0a410f00107a6a1040000c0d610b5584070004280c1924046002401c0e6000344070311011a10b80100e09c1007240c0e03c0e5020000c8120900d1829a8500e5441d04034410490b0148081e404031403090b1195600c0c0c000b0013101c0d0405401c160840b074140b2204004121070340d518280514115142151181d140f00d1640450f8080c0604662000b074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 106301214 1250 106299964 106299967
    0x303191e0c050301051c0c0e06030a210f020a030e0904020609100305010f05030102040608010902090604081603120e09040609170703090e1e150a050a03031e030c0504230402 76
    0x560300740d4410003c504079181201c220500080d0486042e01d000c0100d00020402c0208410030410a450044040c3d88014010180c03076400b4500c2d00d4003114900d1038030300704035600c680b1407400a895030071403021030b41c040c0a440102a004051750703024020028058403180b0980c04800018115a60607045030440e0b600a8040c0c280c1004008019000d41001e0241d0484a01c1558012441c0e050500c00d46040b121180d5610040b41d02c2c060309800258031071000c00350084420070000c00c100c0300401c004840e040d8400c01d111685803450901a8880340f0021001d010054404614681e0341e03580c1006a03042504002c2c00600c0e100245400c03401c0c00c801950061441c07001050002c03d26403c80310141c04c464030a484c101065072040710007582e110ba40384103c1401142c1d40042468803000042c900443c0c140a0b04240900752104002014082d40768412000121160340c1c140000000f108400000350b92400c0034410b40b030408202070241c0c0598001ca00c981c0c110a070110880b03410744000e00400c0c88010b032085 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 106302464 1250 106301214 106301231
    0xe0a090f020a0305090f0a020d02040f0903090e101203080a090b0108011d0c0102071a040918060f05071b060209100908060106020601030c0b07150c080a06080303191e 73
    0xd4000c0e4010001d4140801d1600d0000b42c1024000304141003003122001c003510b5034002c03a500300010a03142c08c5040c0d03005956118008042a086c0c071030006018041e0b01e031124407926003011a6283c900062000380c20340b8201d1820003016403a41c1c442072031075516040030300660342e80703800c0e143c000c0c95002000b038600105403000180d0b011040d03100c0710040611401050611884000c019034694081c0c0c03102d801039102800811450a0318220510229414141249442d0b624210801a6803851103600c41900307040703d920081001e80d10581520b044040e00031f202034074060b0000341c00d0200d80b0450401e440301814003401040718550403221139445c018006c440d01400c925008001210030300859155201e2301e000420120300000d0076504896010301a42a02d89c20940500c5094200d080c0450313540c2c0851480110b00748650103104295449a43e4181c610300d001c42130002551915401f43c0e401e0f030810010300420700c4800c80008840c41c1600c0d800301d1003051365024146a921400d03030780b000061420150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 106303714 1250 106302464 106302491
    0x105090307090626060c070320010506120105060f0402030a090b15120715140423090a06080a11010e030f0105010603050106050c030d201b0706030902030604030e0a09 73
    0x1c40261041600561150301c28002106030a68080842031130552201000503069030288000704400c500c240752170304c0c83d15884c00000307090080c0740d080a00c0d96511001007000ea4240403007000e10055a0400078040342c28988042640c081c1200340d02d5020743d40010004a05000340d4020720b0106900c40d803034902a01c0e00008414042000206140c800d83ca2100100140100081c1c258150b502d070403140c02d07070480e26180645403c0c070043c041c46a90182071000083c844442031809040500c03074408800088219010000e40a40c000c1207000704600e803c81c1880541e1000540ba4840707039008004c0d020f1101001c005841c0c150310300d0401c562511403070b042c06082c504190401812100340f40c80070b1000f43d03280e51042c0c034180100d4030a45240d50080c440c40d081104a50070160365034220800840e0b100b141c444822141d030b48203100c1042d142c41c1207801294044001c11403d002001c4602d0200104452540041c2e1031300c0707000d0405010444480202c00155884440d00001090100c5040000c010100b64 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 106304964 1250 106303714 106303721
    0x21608030a050c070308011404060f090c0e030303070207050f0303070b01270b0622050a0b04030209010b09060418061509030308060d08041e0305010207050303010503060a060b09060702010509030709 87
    0x441c0d03a03440341440c0c04030740121500c1c001d40f1104c0c0d5060b1140714590b0700b0004080302c103071110042580c1c85034441000144205903c001030000c0c0041041c0468000003001c0083c0218080a2806020754070070010040140e80c04190101a00c800700c0d4441c02041080300004d01d58003540e40c025005840d00000098103e41c50b2080880007849240f82c020040d03007003000d010880c1c00c00085642c00c00000c2140c3d02420800d41c0d114609a0303241c4003403525060f12200428881d2109800078038825000003014010751402103000c03401000b41018161901140101050440c0100c0c8111401000c040042c0c5690b450650000400790000701c42810301900e205000402903449480240c01090000020038490708001c3c040c1c900403900410f18604d041c0ca4007488607400c00c1c0404080c1e48035070b003c400c080009070081c002040d542d07000d800250b4695041034101418007001a12403090036240c107100b0002407401000303413035090700110b03840b544816207800140c955100d000b807103c4d0701d406401c0011506810a51 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 106306214 1250 106304964 106304971
    0x20f0d2a05031b090907170f010303050702092208091201150303030c02030c0d0c140f06070503060a05030a05011506050c0709090804090f09031d01020c100905130609051509040f0602160803 83
    0x11041f105503181e84070001c000303003400c0c080500081c200300628000741c18010407147d04030105d41ca00790164902c01d11420580240000129005400001c0c03282e1145028000300d010840c02e90020070210b0044801840850707071030705c001010706d81c03202001e0205074003d1080e240306420308400d503201c40d041a80c0003007001050781012282d11140319020034012000207100c1006910603401000f0755100c20300151065040105581e80c0007107102c50214a07500d0601845c41e1040c8030f100040741c15540c914410495000075048070041107030074440703400020b20000b0000220340c002e07600001c80c01c09a04041113070b8809c54110020990030246590400d1340140c2c007026860380680d54650405080c03080c05451102c50a50050050b80409050140c600e411604002411384900780010415901d00228040b5003500c0712050140350780d00400c0040610500801c0e601c400303800c0303e0344440032800001401c0064042c00c0903182070507841c0c4407c10400da0b941200c0c011507108805160b0b035030040c90140b600350b0045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 106307464 1250 106306214 106306247
    0x7020109060c05030c0a03051b0c0102030f070e0603010303080a0f0501080c152d19050304140c060406110a020303041401020709140c030a020f0d2a05031b090907 71
    0x180d000798140c2c410001e407401051300c4005940382011141b41180074201c054600d0b140740449110300d6070b40b001000011300750510010000f61700c1e841c001c150030174842d0004040109002c0b2800320f10017684c1e911401c41c0d066a0b414201002140c544420580040240300d6103240780d186400000f241078040001d1003103503500215000d10b03030040754044a5645000c1c8102054001e40700e119000080b5848248411704881c800b04c0203030900d80c5180601e500710881c4022000071a0f000400c5c401030040103066940c50510602c02040c400149034003180e40b030700c91842601c040000c1c03150020820348052100b00903041d0003c0441e52142d44a060383c030f00480e91580e2290147c03040e80c0c4002040350342d84c096145400640710f415080c5540b8001c20b00401d5200801b1140703015400c22409814026060141c030039081a8040000c05869801c1d084094081e40658660100108040c0c442516071160031250300c201c0b0b60501c4101d5206074102c00913140602e026a42d848055982003180e1b0385d41c08441d80c24400c0d1507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 106308714 1250 106307464 106307471
    0xe0903190509040c0f0e010c03050702030105010603060512010506010c11120a0c1701110a11030417030405010806121018061a030d050f0403030807050c0303090d0e012a02180702010906 81
    0x48641c05d60b40758204500030760206c1d5a81d0502c03410b940c084d18043c11542c2c000d0500510300480755001a0860b04240c20640200b951220305000d5070511103003110a030154080200618104040082d0031904424030080003108508071544250701e6030820b0724090250300d0100d0300704a007103141c425a90b81846c0222220281081c550580e4400c050081c034685030440302c2010b140886045003186d0203443e100300c5002d14402008002440003103420b91040c0586124081e50700e031401c0400040c6a4080a4030f46407003100703a10000b005044004c90007031030315088101d001606003901c0410101914050b0b5002d000280b4007290704525034500c00c2800d05091049007510884000c2001c10f607000d005511203001c44100c14041800040c1c0903680007908111903040490030000992082032843d44102c0d00d001d013681000484140040d000204c0e007031002c0c001d00b020080206014402c140800d40001103c00301d5408102c200c0079519011040607054501101900e6149000c4c907001e8060441030b482191128603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 106309964 1250 106308714 106308731
    0x3040605040210030605060702060d02040b031602010b04091e0201020c060c15010506070b0106030f0b0d0501020a0f0e030a061a06070b010e25030b2d010905030105040c0e090319050904 81
    0x4071707110b840107480c4002c0a940c02e10300c040d000c1c880d050704000030ba065015801c010106448600070013651080e13949080181401c004520020f0070b4561103c0000c3c0154289085980041c00d500e010001c6901407207803c59182c0070304e0004032700d4045246501a00714000140e682401c42c408500741070f00800c801c0402029036a0b500c02d100f05072081a001815000c43e41c001448a14805e8100509a84514001207038040d004000142a1020031204441d03581d40022080c400d9500180280c2c1d1021090030701c0030750541e010000c81d45070003403010001d0041e650342002088042080b000400d14039000740010382c5640991070a8800c075503003030045091007400c10000800c00e104004460000d0071010550100d2004220700540280008000950784821000e0000c01001c484525414881d500c68540c0940100c0c03c40014103074100c0d41e00705030f0007641000c04100110341035003404401c6801601440e62aa60758040050450141141032421200701c401c46202e03113070f0301002400d8010021541040580c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 106311214 1250 106309964 106309967
    0x11071a090307080d0822051e0c010810060e030307080309150901020702010903030f0e090901020901090603090f170408010c05040302100809060601120609020f1306260414010203040605040210 84
    0xe4850b0350380c100040d8000d0001d0311108100d400465001b14046110041c0c00c469940c00e0309051055411000400143d01070745d1903c14104004411410203003802c0746d0f18100008070f500502d00c0c0d070240c2814007055041c84e00e4151001c01c111107a1f40d802204031904c038144003c1d0070340c40d0030304c2040c010f0f0107065050100e4000307070042c800c961956038142c40300c141043ca5940d0aa49401a4514040501402000341c034490b07100c81c07411034800c1d4a102c0005964480e00390001d4111081900141c0425150100300c1d00040c40c414aa0018140c026810310841c00c0a0400d000043c4966080024154240310f1a004a690000c0241003078034402c4030804c84100c04040e003111001c50031510107403e90700150104206500400c4120704000d03244201085140d04c6400c21400e0340d10082968200e4030001804e004420303c040400c101401503480d01001c0010307440354060140456466401c02c1c4424030020900300640100d508032015a403030025501c2c1e18090038540f00809049806074003801c000039480903400d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 106312464 1250 106311214 106311223
    0x2040509061909020111030c010f0e030405030714060f0c0705030c0d080306010c06022106150c031e0904060305151f09090804030204110a09210311071a09030708 71
    0x100c4040d0040b1000070300a407016009441050820f9040c0980e914100800d440140020402e80c021000040741c0e21071020b01100031503090011140c2c960f00180310078021a90082000c0d0111903600910a07441d800c064005000740c130034000e25091441d000102200c02a00c04078030b400440d003084050b5420b0f60b030b01c2c00503c00c0454000070000c00c200003c0002074501d6004100c0c2c00c0210b80580e100506200340d078030100020300064080250344000700e101304071041c40c0c0100003202000025180d2401e10510300d001640d00c0c085c0c05178603074801341d004901101c1e801c0100155003d07076100500c140955907032800c0580d103031505036292540c10000074001440003062034681c42807110000f040c070078104e850090100b00a2046450032200708008000000c050b9596029849005c004032241c0750783d81802038000303060391070f89601810350302547c05040c48501c00c0102c0d82280d080c1d0141004682c03061001005410300c411904100000c488401c0c4004c5c2c080f5081c400b0303118100c0c040e803c64030700304e4444851640e207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 106313714 1250 106312464 106312471
    0x2010605012106050a09090b0c0c061314010501060825022505061206030613020d02060714010e0705011706091f08071d0f040201020606120f0a0f0204050906 69
    0x12607080c00d5041e405065014181191201d2030b07800103a003940f0750000a0b41400031741c0c41907000c00d0b2609414010f210804041a030080790f6000704601d032082c50050141c6481c001031a004503036040803494001c0c040a0441c01e0b904140740070080244c0e40e15020b01528100041d1b40d40c440130781000c010040100304500c82010b2031000e0ba0000c0084088160491001c05402000084413030910b800000301903c4031009440d800b8901924000c4607e04603013410f203020401440c000d0303000da02582500158a07107000d04841281c06455040c0c6e260020f0605a01c1d100d04c040004042e5881e0031101103a0070004548001030310320076030b40c244414418690383c0c48644400c1d03d54507448150140441e400140d1841390480e60141c0a200d521907a031b45081040c1030484e030380c3c014452111550000c402e44078111600c240d001e014903841a0207420300d900001d581d11802002e482c0103c552300e500c00314200040100c8199114200c0803140b01c012245031800203503240d181e0880c0a50f007060301044042d6000305040b0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 106314964 1250 106313714 106313717
    0x1c241d0a1103031309020403020117040b0103060f020c10090506100305150403090305030c060609010f2103030b0406060215010801020a0206150103020d1404020a0e150108270a030e010201060501 85
    0x1a0200c00d844075800d0444041c075055140c402000200305824100b84041c000788240e00c401a1a507241d400090104084003003003110094002d410840040c0081a0885c1520780004000a10030300e000030b820002d00c00c0507580ba035144200a040401080b06400030710300c0910a0050f2400740d03c501780c0583c1c41500c06d00004005402c011100000d1110341040103500900a2401c0c0300c91540c1ca0311424215401b9600801546e00444200445800c1030020540101100b0384c560a246241c50b0030421071807104200c034000b0703012030341c044410716100b034200c0306214400a0007000241d03507a56010356a05902c40f00001841c04141c000a2060b50620a51b4020000b94000e41001d42d80e40b101d0301c2e01d0704800800141810390900000746001c815101301c0c80c1200384515100d9a505082c0100880340d211a8400740b22000f80b1410801c04842d402009060040d00782000c0b0010b03150100e0181054a840004030744925110481e030805a4000441e142030500940711007106140640c0120b00340d400c5409150f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 106316214 1250 106314964 106314973
    0x4122a0f0c05061308060705070c0302010302090112150303081f21050312060f100509010309050c030f150708070503010501110c090108010209031002040f03021c241d 73
    0x20003280d0450200e61009201d034952610040c0c03901d00054007a0480410700c0c1c00d500100c0005d00c0541c404011145c0c11101d80c2c1040da040800e940d0701d481c0c00d10010700000341015004903408400364010300c0d10060b00b003c02c00c02405440011103548130321050300d10042d000038101d0800f051521040b4451007000114207519405168102402003016804911815040c2186c5095040200e001030000d080c52613062010243e1780e06040d410454280111507045103c0d1034500c281041c3c11b9040800c4a910403001c0c01c0215441c105810914101200c2200e1603400d4021001c040000980100d0600400207520407441443d498440e0b08880807181191100f0203d40104014002580920039413241c10340d540007107541c03540722800455880c0d002030384550b0150703402252183e001d14003401082c040e044020411030404d450318949801c0d4009511019000b40f224400e8103086400003140300c0505500711407200710308040424080c01e00943c05080106062800350940715a40300ca0603540c2c0642c400d40010b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 106317464 1250 106316214 106316297
    0x906020c1203060907030c0203071a01050f060c060a0f11120a060e070804062a0207060206071b060b0102031e0c010f050103020d0308091606120b01050301062a0b0412 73
    0x25030081483c065030350150f00c0300707008480001b400c0001142001d022503c0c4d80c5820b5150604ec03080c0028040c901070301c01c0d0300a000c006211100007802e6584a22a81c00114200403e03200c0003000b080ca505a0011b1a00001003e5a000107101c884a0060041c3e44040008a60f1905403000c101c9086da11440098104408180403861a810120540600e0045203886441034072a180b0482e2500c0c21200260300102c0b810000960103002041e88083c940c180072170740c1d40001c0d03c103c2d9903103510f010040406694040303801c2c03a03034420025648284506080c10229409441c81c0c48031540010b460f0050a40c208100d1400c0301c940d034000c0038100e03a4040e285062f07030b0385035036003d440005005264a80d24492910859030030440c4009040003044240c40c0c40580d50aa00c0520040da0510b000e01d5040c000100010418250b00c2034003050407541c007500d004400c0392030301034410b1105d00420700904524654800d020520a07140307148203020f039032911004224807000c10500c2c10030040009402c803138281c0404a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 106318714 1250 106317464 106317467
    0x20705090118020f03040303092a0302120a061415010903080d02030a0902040609140a0501080d080702010b0307090221011406131205060402030d05040e011809060906020c1203060907 80
    0x59810711880b07500c05810a004030075206299081106d043e40004d8640740036000b0f002602030004ea69102c0c0000401024209201c1c02210070032610000740145075200d4464452402031001402e21035201c02e0a01101d05103074124044039600303417403804024a04055003106507008649800c200c0341d00a1841c1d00f00503480f42c1e80ca00039000100181d00c4151584035140042e5201d1040801600f40300900040706a41d42050301c83c040402081d80b90103d251000500c4122400039542c0c07844038640c507180307825903a8a13004a02502d8100c483d150540b0070100e000c113410300c882c5c014000c0810801c0b4544407224680b050380c07211810a124503481000c11107296000741c28850000c0c0251400f0802120110f541c81e0040048800310050946103500b01c1c6042c0811440c0074041c40241c0e51051034040d04150419520199040c070604c11080f104146040980c4440141c0d044041701c590804c50800c018540781c1040302c040c0d031208506c0c005a004001501c1d0100c42a501503902070040a0b109071020382d58400b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 106319964 1250 106318714 106318739
    0xe060c0304031106010303080109231303020304030c0f0509090102090a260a060506030d020d080a0203060409080a110606030318061e070f0507060c0803070806120a0309150207050901 80
    0xe8040003907001418410300f00801500d8000c5200b592000000c2d07142003a81e204403500340c001a0000010007400300600745294410700c0e00b1103080b410066071000d40c0c0ca016891441103510003098200e02c60030000700c00d945030781c00004030b83e02a40c01014503964072112508070700c504010294064000c4106118200f4900d010b056950710102600c14101c2030001100d282a800640071a00c25032180200a554142401114190399843c00140022551000301410040e402045514241c0e400310000300107959541184070f01a821441855403074440e03650091084580c5400c4004da0b202c0c1d200410a10f00f0000704590040f80c0c402c00710b0743d09002c0d00c0c0402055a200c03e803081c0ca4242494801620803400000412404e4821415070645500511f40242003101560240f0103100ba4500c5e101c010419480c12241d2140702464805080e41d076160014402d020200084442481a140382100301500706140030f06803400909000211040d8420881e070750b405500405402c0300e681001000610150f00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 106321214 1250 106319964 106319971
    0xb10020a12030f0e0a060b060403030909091b060e040e0d0509060f09030f0d08010509040f060f0603060c030606020610120b130f03030b040b09041106090102010b09040302010e0f010e060c03 83
    0x50b0100e482c10101140400340c428005840e00c00ea045890b0120400c02c1c40d22400c1c07000e20094544505040c0f86407400b0b01010494403500044a4a07500014200a82d02d020103200800540302c46503807035152240244a240901032050066240142401601d0b4001070032000000780c0d5543c030b5150443c0c80c07080c000745802203000804618800c0c40415010f6070280000c81071000804000d040324031880100501900c07040e48840c1c0074400c1d060501010030040e40404074000e80000010401c07442a1030018024859540080c182d0b0385045220f0f0b45e43c0d64140c0100c422900c25a084519503222a103541500305000d1154275244000350546400103507100c0b00c5650f00c100c0740c0c4802407054541d910f81d41d000e08113034501200082c0d51180501d44a1505100b205640041513030340048a160681e501d240d6508451480381c403915000c06d08c442668400d4010415810000e800c841b08d038100307440c0290203060305103580e11340d0f401286a0503040041c140f059140c18001c10f00100300701c0c0c0f10100400c240342d0024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 106322464 1250 106321214 106321217
    0xf0307030203060717101202010e1c1104113f01060c0b070f09050103110403020d050601050414040b040f020109030b0906010608011e03021c02030a030c060b10020a12 73
    0x1000000769600b4081c83d8896202915408540d90907074200d0380b020307400203004210b144a2a0340600200001200d00c8000650a003403080b0500e2a0b02c00142c45440e400c200141c4c0c90301c140d00a2420813a0100940c6500482a00c00b8410800302c024208100c0c0100310020b1072220401d15620910384080000116000174800c04081508200780c01c1e448140f000d030010804551104006020021810400c0b80e06c0707102450160381100301c07004001d00e12903052080c81d04164442c0c0804d003061150200b280c0046030f0081040b025031001e4544070b0740790002403213a248036919001118201c0903249044034416a80032044098541d156940e441d9020361961042c2d04101390b031200440040c2034981c1d21802010741d280209420362516378001c007480b40c160041c0c01010300429000c149444445248001c0e0783e4126414070740c808014101e43e050b26007443c1c0195261180b0f01c2c0c440203054010600c03148050003080141f0590751103100f0301c026000c8503091400164020424807000c105005451040900c05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 106323714 1250 106322464 106322473
    0x50f12040f05120c07091103071404050d150f0b01090b03090304050d0f050d050a120e0c0a030c06020c010813140109050d0201060617010b0f0c0a021309031101050c03060f03 76
    0x80342c40303440c58424606a4403d81010024042000341010440c000c010902100e0600805081401041007800050004000e11a04941000045ca1008161406064040d002c0e0b502c1c1d030040e003815803000403042984120b640c500041610700301d410380180707034200b034043e10b8820030381c1d11300500c0c0040d5920051001100780824000410503a40b02e440c8000310718004c0d105c100c1d88080c03c0c10040d0503c44042030810510404103c24004107401c519449840440e004001503c189511400c9050440001140d540310b01c0701c00c8080b040107030000a000035510035a00312001038031800b0041d10540030550b6030050300074440e80001c002030001c01030700031445200000442c7e034a00c0c65803250328000031a503e24003d070351942424828031f0750000e81d0281c0d900c05000c1201c610351420300c43c4502449817142505503141c0005110400c80c1041042c0e100c030580c0984020035015505690300018121148100c000a103146d194000b042014003da03805025078407109813458441c41c1c10450180040d20ae02c9805004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 106324964 1250 106323714 106323743
    0x50a020a1a150109060e0d02120d030e100e0c041e060308190e100804050f060f01060305011502121803100c030b03030a0225090c030902030706050f1204 67
    0x1419240e0907a8018a014036069400c00c11070160100e00840d0b02681040b1810508000e0154480300c3c2d810f2010050343d085900c18594000314010503e0000c03403401d544948201c180c00d003a4160f012158055072001518049403a060420b81036031604080300c0716550002010452520f01503001c4603000812079170070340130012a00907000a561541d402942c0850000c0f8a4030f091000d202e1802c4132070364461030080c98203a50240003440159203401e60404102c10500002c040140400c00080d2050402c000c0b41c10619142801003087d1509000c1d0303a00182c2042c00004006039007001100100300560080c00d645041160810780b076800c14807001d8501c4111100501e1251401d10824000380794000011924048442015056402c0c0082190203940b042184150b101e89c0804e00c0440c4c416240301c04540c900d60000341804003030568100040480c5081c03094142c16402d9400600294030a80540340081e6035200c094034240030f030140c01400d0b0036081042050040c8501001c903807051107520040103594 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 106326214 1250 106324964 106324973
    0x5030402060a1b05010b010207080312011203110f010902040b09090a1b050406060201051b04030506450c01020601060f030e15090307060b0a120201050a0e040c020706090b0a08040201050a020a 84
    0x44450081d01d44d65561052800d040d64148510700180914070000c500e0480b681d580c007002124148221000512540fa40d241010702c100701d0902004038034812241c040e0a1040040d009026031481284a2481d00c3c62007146805d005114a100716400006881040c3d070a803500c1d82c074003160b5001071007800555280882e40d56242d11131100500541d07800040e1034070304030450102443c508070f021544200f040c081040052b100050b9541d01c80e060103542a84a12200c42c08e401e41e461000700e041490003441862851000d03081101560250084101e401c48403601d401682c03100e8083c09450009821000c8400d101d90003600007105d80c400e604101c80010286150503420a1010745640300b213030b00300040c0c03981401a940640845c5e074204440c2c2e440d000f46482496148206488030081c180440403840c0289207014980f866102032010703000703201c0c3c0c000c071800094032484540a8040800c11075000800c3c8c8242c0602a81c82001080c1c4600780c841d2034540043d40d8540020741d42e001103120340c60050001a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 106327464 1250 106326214 106326257
    0x61401082d07030f060f030c0b0f0403062a031104210b010816090c09050d03050c1615050304020307030201080c130b0304021216170109051506010306050901030305030402060a 77
    0x103070025607000444905131032480040d07038140da010055603c907241e410310200d802d8807609011078080361051540d40c0e4401c002100140a1580080d103054501f40384078500c0704040100c3c10159441d200c002c90100340006041e4100c0b0718180220700c40303200910082c00384041c844622031004040c0c01e80da1560101c140c1e00c0d1964004241c1001000d5080018605500c0c0b0002c906040034043c00c81041c441034080c840300810b41c1250344510340c402c074120703042d2100341030246040b540590500b01c1a5044004012012804052144a548226058910780c40f822601c21020f580c015607004001d0603625245400446074404041c090b60202901004422800d1141c0d0503040c004182da40c241546908c0c0c940104101e0442140c400d440f960440382a000c0c600b40c00d9044032043d0b071000f0503060300519005503a68010100c00318000e220744540507602e89072910080d061486084248e03810f0003a15241c409002c400386080c0701c0200443e00c180302207801490103034043d051605041c5410401170f43c001c00c01d0301c140b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 106328714 1250 106327464 106327471
    0x10120c0203071b05010207060809152211030c010c0b150f0a0f0f0e090606010c0809040204260a020612070e041a0103050702030a021b04110f030a061401082d 69
    0x3c2454804016550b0144124001041d41f0b0801c040340746426a61540c9643c9610011010005020002001581003412040d003070300d600446010f0300001392500c0140d40481e55901c0d07101e48208141c24a16610901210401542c0f28040e03160603100c0c1800b03682a83c8000740b0707007680903504401441e8291a11050040142200000c0e03000103403500140d20044005c03074101100c90b01c05c4004014406c5400a4840d404c20000e10309400680c0300e5080c410710b40d0041c40c40540e8045c0c00014001100b007031911000648003208844400c81e1032024409070354409010703000a400180501129211071414100244d012959042406454200e500081c00b00d84100e0f5421043e1400d40e120800c01c1c1d40d0600c00c099010046000651400d490301d030300a540d840c00ea0400c80c076071300080d0792540000c2d201c54014150170501d4000207610f59a2003d10b100c0e5640089030300e04080c52805400044030030109009102e079101c1a181ea0382d2a450f204030141d0406052000e03845082d000c02c0c03480d0b580ba034800c84003621 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 106329964 1250 106328714 106328753
    0x7020f0402070c0905060411250203100b040b03190305180405010306020301030b09150112020303040312050403021f050304030e03011b020d0e0f0a0603051902030709030605010510120c020307 84
    0x2110f41c285141c5400302c40c809400c0d01c1c0154074020302400c003005903034101c840001041c40c2503821041c190110556040304003000a4050250240d0451482c029402040726440c08540034013203000700c0030605a443c000d85c025140010405880748003c2400748000b41803640081e45805c0e00c520620b408034040e01d074280d0003196910ba001004000740f044040300550005400000790590044219a004c00f00b4010700a40410036070140000c0d08554040049034000e50b40010b01c40c12400008402900e00d422a21091b80114400c84500e14054484d880e0070720b000e2025150581907480b2500c0072513401040030b007882e41566990451815031030a60504002080c0307a9070080c68511070600004042c038102c011024003070f400c080f1034140305540c0c1907881d2090b64114940000c45994100340110001090100c1a02c00751001081c004400d6120f20a141603c0c002d850a0020784d0341c07070007440400c00c11701c901c9100041208008070880c03200c0d500a58a03080321441100e0412036203850300741e41001c62141c842c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 106331214 1250 106329964 106329983
    0xf011401030c09020304020f0906182703031e0a02160c140f150c010207020901030f12110a0f06020405040f060905220f0611030109050403032a0507020f040207 70
    0x410031121400b4103000c0c0495000035411400c10740d010407039082101c0b031001c0c030410101e4000742403500c0d034005034095000d00c030aa58500d414002505c10b90010f80c500c2581100030b00c19106403c1d80700020131a400382d00c190022103c075440211030991080c1c000340c050340800f1b400b004400800405400d41c503980c2405134003211400e80c640103030070a0300345038412258010750f01042481e489613220100c480400010b039108546c0e030007455501500a218984000390701141010000c0144501c01803c801c600340b14603801600c0c130259000503290016082c0b41d22283c0c0c3c0c841c000140001d000d507102d83c0c0480d03104620140c140394899000170281c511182a81d0300ba280d80d40420441030b1420700845402221079146840114101000041e00c1c0d8044400039007410040346401c0208a9598085284040d0080000303440703585900421010340b40c15141600080d00309104510501a031540c02a0481c0d240081c10308086544c0130142c030b80f13800c000c2e010780e800701041000a41a07100c41c0020701d51244901c070b100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 106332464 1250 106331214 106331219
    0x10020d0509060a060f030f0c050306040c0810140402010f090803030a09061b0c0b0c090a14100806090610030204080303011d01060e0f0d051f050709060e1e030f011401 73
    0x1c1d0702c0c010004192800580c2000f4082018117202039441c41620b41060040100180d281003006c01e0804070f43c091070b0148100c008000900c2041e0900c0003d980711903054030039001d21000700303030250b644114003080e40011030004180198014807a90f03d49008509142586995502880303003550012981c081000d07407a0703220b0804001103441419084488a6440540d0b402c045000038024103c1c0c400080ca0380212101040700790500d5000d40c7c4c400039000b060000c0450300d94605c0310140c084614024010001000ca1104150007500b515218200c00762a0341800c2c1c1e9000200304814840d40e00e48024194200070205149500b44000d6001e000a1400342c1c002e040c1103414910300e000c05a20540402141e4240917265a49006980865007000c66003d41c1c00c0640f4140705060840201d62400c4805452140404d15034054000610501c0a9201d090100c2d54a0b0806e83d1190b6008a41540c42580c04032444401c0e100440700700c041403006000c0b1003d0680c0e50240700e00b11521200d401d441c010002004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 106333714 1250 106332464 106332481
    0x30203121c330602120301031e03110d0513081b010f0302092e140405010e0f0409060f050703020901050d020304230312060f0f0405071404032010080a05060310020d05 73
    0x50507040340c02d021840d8559803468031380e082400c2c0d940278003030100041184003400303151203000101c100700c451070107035514011185000b030b00a9001e0030084000d92189000042c01b80c00218503a10948204c45111444024030001151140680f12142082c550b0a010031034180c0c8850000b450130700024098201031031001121445110800c02e84ae40401443c50015104808424166001c44000307080c001480302c10b000016030310104c8104440d400502d0003164000340b081d1070300b100403000d05040e010011034443d85000c4082e841040da4071400300c0e000b0411400e508545030300071940a4020451070010031040f002410300201c5240d9214001d03400414144404054400c0d80344d00b18904403010611040304c800070980f030900841c4514880c60307440002a0a95000c0d40c0402a180310701e018150b81c89440c1d01d0208403078189c9159001d208000948030412a0400d881c0181e19210643c581561540e12004c030500640b10040c065900741c010780007454031480845c00a004d2100c0300301c50106051614141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 106334964 1250 106333714 106333723
    0xa0e07030804031103010e1e1c020d09060306060c0b100b0304080310090605090703150e0901060e010e0609040b090106120605040201020607081b13030c030c030203121c330602 77
    0x402a05c42c0c0d143c40c150030445100000c0c8c10050344203841c0c005034070702c0d1482503890a042c0388032130341c1c1c2240d07240241c50400142e01189401010001e61a9640d98684a80048003201c0c503900035035000c0792031624558003150b001b02d151540122240c02e18204184c40c1c24402440d50030a49084075a280c0100078000303006461203614014000090302009079500d480c0008908207c0039040e1428540d94541ca0f042c0f60725030100711000f03404004860f0b075103420510100d0380200518460714501360050000403030440620b02c2140e018110040c00300411703441d940c9603400c1024024242050030740d65800001808100c0b104580c980502032140042c8514190002a081ca0402800c52040007161000c2125440b6101805034803560304490b07584c4c507030f180d070b0780c1d0050004256000540070a510301000020420310040a41c180e900c2a01580d2440c40c44c106000c040d805208048280c0d8036038481c40045800312680000016822040c050741c03006954598084c50403010040016405075500052214540400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 106336214 1250 106334964 106334993
    0x151c08040f0e0f07030f0209030111041a0319021606060605120109140c390c03070303090e04031b0b06010306150504090914030309060910020403030509090a0e0703080403 75
    0x400b800200e1501070b07400c1c02ea51100610060616a9400e4040d0603800140c1c113850030058068000c02116a26000c5541280c00c14407441081840305e018403500c5005184c1074030b0282d4401060f41440c8600803d081380030390012a42692581030003807020000c2400381c0140e00040c2410785a2995402c0d02e180d015490020580120480504100b040c0b81100b0003542d0603940b006100044076204c440a009084440a221454140800e10040d49400d050141e04000f86981100c0c003c4804903210b8a05140c0c8030207031440082e020a100385400c00a844d084815039601501c00d15051a40044500301c0704042902e8000c00e0303d05100900c00c00c0981c1d41c0511807000500741460202d05d4080c41c1c468014050310480c018550b0880e00ca215840400104107050340009003050162500d9252074050304d40da4480485042d240c61051040b802030280907482200c003503e405035140c625100a50041c403070504009041d2002890b5201c400b50280d00017800101c0156100d900341503a16072450505d15940501c3c513 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 106337464 1250 106336214 106336229
    0xa0207050f010c0b0402040609140a150e01060804051005070c020112060f0302040e0109060c11070509010612021b0d050405030c060412140c090f0603060a09050303151c08040f 77
    0x284030a02036030300070b03120f2512207074000a14001c0e5940c610208014200d02d501c240365a5090a007244400b40c03076070901500c00d2412079410422b1040e00c0c200000300040c144a4a044000901c005100081c8500c139043d601501940032200200d021010342811140c00319080c40002c0d01b840f0746401150303400600700341308654106c02800000c5c2400e0030ba41c4961164817000b84a20b580342d5091500ca8002c0d0000d16046030010010803245110b020090055076039001800054043c030b0002041c0c0380b814082850582e1320964500d0407062011141d02c00951118100c0714071120341820101e240f02d81001001507400459480c01d864500d00000c2c103241108040c0603d03c0f5020030302c018800701200003407009000c0d41003030b414424080c41c0074000e4100f004054013146c00480035820002c103021000d18290041000f0b40481e5610350f01d21603000112884544000c3c5660402c0010a40c004149001045014001840200b900c03a0740d400303521803d04441d008131007080b40490100002010048032800600e101d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 106338714 1250 106337464 106337479
    0x3050d0f14160c0206070b06120319050a110f030a021902030a060902010c150605010f03150614040b03091c110706080c0906030702100b01051305060702010c0b010b0a020705 76
    0x140c101c10103440c80082252009800400c0440649882000207800759a006040c20b903543c0e0b881c0c01c047d222440704507a030310b0181c0642646200d624500204903200b109050b203051072040c070406000c40791a40074181c40d404100c006002d407460301005000805142004000956440b08840006424060203c01c030004850600461401580b00802c810304003581c85080041e680c44503100507202032401a6000c0d01d40143c041e1401d0305400207600010580c3c009032907282e14031800320000c07010b482c0300442d5002d448034850f0f42000458040e5000c4040588905106802d00343c481c130408404d504101c4045106500001c80c00001c402e0303010b0003503091035142c500310540322040c08100d582ca011603c50703101000f004c840012009141c90081c0c440c20000100415582d0400c100b00961300d01003c0c105606051a1490350606503005000711208400b9038540000381c00d07e04001c100035604004000d84c1408400346046001410003d049400303820020540c0762100c80c9404000c6c44c1c0800e90b004039000d44036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 106339964 1250 106338714 106338731
    0xc0f01020f0c04021b06071724040b03030408030d060306061205070b0c010902180a27140c030a03020d11010501321201021c0204030804210c0303050d0f 67
    0x1c010500c0420b41805031400741c0c2d40c2003880359112403045000d101107010301604061005066000448516000b028180210551a070000d208105050072407583d03809507074841c8600f6603007469004100c2c10503005064904041c1e441000508552140d124a440700303940b11400d1040262520400010388180411102c01c0510b99580c55075520b4a8094031200490120340c1d00e000e903400f50801602117502420403620002c82010000c07400c0b1007604c0c5a901542012201501e900c502004545480f0f00185410750f204c2c11512200c008845403181a80b9901590348904001c3d103003048400d8070580b1035402401c0700741d011a030042c00041c086002c40304d41c1c1d0400c40104000030200d100380c0302c0c401140d82a29111881c034250558814071040000d81c0050000c482989030800650180c01081c0032114901084900200358108a101d54000181400c5c8240320510106031510a51011542e00b0070b01d481940d44192507410b200300095100b100020b03400030b840c9810320710a0003080224100450f0900c0240d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 106341214 1250 106339964 106339993
    0x30e100203060f19080a0f030e2b080f04080304050102120703080a1802120c1306030b0a05060a0b040f031a070801140105040e160e100c0201120609020c0c0f0102 71
    0x1680d00022a11420540d030180381001314a18013180100358220454040c1d465a103050805900e010700140c01150700c03008211240e0401e181c500b10f05107880c1414040c0e42c91450003401d00c0c046240310039540d541e82031101088121030440104060302d0024000c58803940b820000a1400300d80c0400d004612005100420010390040007590b0441040200440c04124181e40303a42c62442820020350f2003821070b4907074600e1820103d80036415500594500c0e032007540034442c04060b0f5a440c40001c004040100025640b400b00b5880b20750000301c0240208542544d9803203280003138011760070401c000307503290340d04200300b04408500d5908010054504800c0c0c1c41c00c0c2c1c8024080100501c281203203000d010040020036845901203c0160018074411205400e008074181138064081c44104c0101301040545410340c6000c0d40200200a01f603680c030004100260b004460380100e44d503802d2892034503035002140800480c006041000e035810001c0480d03212840412a1120150544e1415034118048429130760 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 106342464 1250 106341214 106341229
    0x21c0e1201020702030f071a03150910091a090c0904020f040308030601080f040b360708120705030417010f092405090c01050304050c0406060c0521040612110a030e10020306 76
    0x51041c0b2030f40e0f07102d0380c5000340d8500d100cac00741c8003040d44200083e041104245a0841c0b41090724010310301000401141d21501d101c0c40031012009500c0440070f80050a40d0060f1170061020301c801400150800010368040c1143c2d0308250030450701c450022040140659002c82d41a50214005000c49001e040c2030b00c50810080d005882040080c50750140f00050020303110054003603035400920004814040c403c90b60325225540a468464029000a0f0040014210540702503503044009149450302d03080a02807840b100c865001029501ca9a05010003d26441000d000f180103400e40085424440c2606200d80d02d6031841c5030308207242c04240188100d0003d5807280445080c02d20641d2034586040c02481c2c600c42c6004694000e00f00880030401c075a2102c0321216052081045403101c00382c9c403662000e0403c80e90105201000240003c0092501c0780780031095402010200141000701c0c240040301950000010f000403d4640b884082100010400c80c010090b04841c114198145030000a105 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 106343714 1250 106342464 106342499
    0x8060105070609050705090108010903021e0607081003200f01022b0e0303030709030210030c080c07020d05100204061107050303070f02032406010e030607021c0e1201020702030f07 79
    0x30741c0c0d40f000401c042040800114020f0070b4024540310596075921001c601804044030224018011380d801103816100f50940c8882002884002d0f044664800100f1608860300400d04180b40252080020204e11021440d40c04628002124198002c41c3d405120108424584503030441d4000380340244002e0306d80340d802d50b505604c200510804100180c0884202c000c55141d00d40c1400000107200001c0e8020b58054201c038800d840d0300400090340c60058044580d135192400110720f013600041c81210b00c0000a0004920041007410202016242c640c50600302005178421a40e0005050018540115514200c0010340c03004002d55810040442c1d140e0060340001043d400940c001c06085607070504c00340e201c1c40c400c2d411012030003d01c4031440700c5186058905a02003000780d8250078080c1070200b00c0078401c1c09241c009080000300c0f074030511541d103003c2d0074290410044000c148059a1500000088030150000260f16a4803500406040150943c034105d40c6500102c800c0155101d10200e2052 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 106344964 1250 106343714 106343723
    0xa060b180103081b031b01050f0907090b0d06090b0708090708070e090114070801030c140108070e1309030903050f060f01120219290f070f11090c030103120806010507 73
    0x84481c03070740704c50340401d035080503c0b1959800003003600308400f900b646000e90501c0d4020001c2c001500e0f03002c0c50b107221003c143c40980c0603800400c0103206004a82e000199171032805090021b8980282d00c0d18000c450081d42e013214903850b80d42c180442107a00080d400e400001001c041d142c0103280111480c0d942d50390744903e201400d07203200000c020060a511640c081260b0028041480c500b15000802e5800c09020450704075820300c001049088032003910010f028411785074a01c19441e0100140c2e100c49078142d01e03642c00300c01d01c3c1c2c030503100a00d1400780c0780015100340c031100e0125080d40782c020704111250422800560150003007086003002c403d07001303045401040e00030701802d0b41d41c004101100e507414003264642e07005d0100000e1510111403000701c407018050039840f2200c0d800007070250038480c420100801010601c201170102d03801b00740149440c4d224201010803c0c5084c808a882d40d071048a140c51070b020040010014041e0072074034007040520074a4540c11624100c00080d1807802982c10151 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 106346214 1250 106344964 106344967
    0xf040b06091c020406032402071e150606021e030c0a120311040e0612061612060f0e070809070501020604030305040303020903010905010c020c010203090616230a060b18010308 77
    0x42e01003110300000260364000d4400d1008a4a80c14248131441841d495a10301c05900000700c40f10108071300c203071404140d2001040700c418949007210786e541c0e40d80e5102076409010144190311415074a100314001000320342c005e01140c5104442243c40c3c0744030445408200e400802c18101c100e030020400d44030700e5502a50f0410006a81e41d03040300240a0740038811b200c14400107002c80d8005042c041d0b103100703c2c0200c802c040c4c0d2601d00c42d04aa02c51034240c400a403885440440103c01d14010f0030080d819046c00200090055a41c10030f0401000c0198003000f0714a0582c01401442607100c02483c0c0d0100c03900e8001c01c2c03002e2034000000e60b50840140b0160815030745c0c10110342018480d4048515400707004000b448443d442e130404900928000400703c02509c100103448401c3c0d40040141c440781c030ba0052240d424a03e040304000c00c05800844115810440080d60f425100504e01d0003000403030305e2700000d0035060520301e8144100c506401c00e42d23105180c6500751400441084030b009054030360110400e0f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 106347464 1250 106346214 106346239
    0x181518080901051b0106091b031a0402031306140708100e0403081e090c090108010e0604060c050c0303010b09310e0717030c070603050c04290d0203060f040b0609 71
    0x14642c0e0484040c4405135075003401000695602940c110700e00c0c240003140c0c07505a0085c0054150104c0b004031034540c00300f0028101c011491f14051b400740d9400901e4040710402d2441c01d81c0c5010803980d40f500c045191070400814400c0c0603034031021140d80044803c04c4040c0440c20000c184480020041000742004030020000c0d0b81d40d24591911071001c0c032100c02c0155141020301545071030b0038507500c0340c0d40039890030800052521014059103d0a07450380c005841c1c42d450b1901c43e03002901040c2042001c1c88000c10501c0042d02c4104002c500800003e0840c0d610b030003d00c010020200040111203031f41c4d208004401c8641003d14080b02d6046030b01860005200311842000ea05011480d805043d0f41c001c50300b41e40001c0c50b4040001d001c211690001e4800040d1a9182501201c0040e9004801090140400d12901e891420322601c00342551404c142c400b03507400742200321940076031100d2104507004000c2c40040d0414040c402c0400d43c04407402e100750000076010031024001c029a0f1031182c6a4903126 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 106348714 1250 106347464 106347487
    0x40b030705070c03063615090c0e040606080102070309060c020f04050a02070b01080604121101020c0102070c080606330d0504050607170105010914030118151808090105 74
    0x1220305a0f82e000111019190340d0341001001419846008004904070200900e01d00d100c0021598085600c2d2121510b9100d403520340307150412240320040129641c0e840c201c4081800864501c00800d1038492030b04692925203030103020b5620350b0384088160ba0041c81301000003078000300701006844043ca03104140454500001d5407080903030220540051501c2c003407140a41080e001072005601800079083d0030b0b683e8920741942d40c02c00b11009004504e2150b13a105003180f207048011006203c000c005820300e46c0e204905801caa00604048525800088040002d240305000705548800c049500c00c10300c0f05002e022035843d0381c0071203202d84210722001d0200c42410301b500540700403010003c0100000c2ca050302d0030b203035260300c1502d5040204103140703070302c180c2e110481c40858140c50041e901c00050700d252114007030074009607901c00c65055413034080c8071002641c0000b06500243c0550604600002d03650080c2d0100c035000141074036a228460300002c041040e41084070020f01c42071074481d5446004900 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 106349964 1250 106348714 106348717
    0x150f05030108060705031f140411030108031218011a01140910031805030f03040605010e04030e0613120b011509121202011e020408010b010e090403030c090b0a02030c060c0906040b030705 82
    0x244600708146080c80407401c40c0981003143c4080400789c0b0200200c0192041084690109200f103400691080007280e0303494600e4003081b600700da140340c41c0e2803400ca0a49901401e55585500d00504c1d140c80c0c660f104095a8404031f1482e020340034003171440c540f1001c9004178100b000301c401c05400b8103840b41d034110400c0d00e078240030f8890340d50840300f6a9260031080c080441280e0050b581607a02500301000810911500040b09020700d9045e190b44d800076041c882800706682080540741d41005101c040052a030036015404000903104401c1c0001d00d606064000c0c0000c2481c480003000c22082110a0062902d000c61100c1c6050f084500c3ca01c42900c20f420490240c18881148058901d020b400f07810001240e8000e80261103480b4000d002000540004450000800c40341e02d46c400d040c4400318020a000364011000442c4514001080f280c44030b0300d41160380c0c003850090b0016800000d01c0031180d84240410781d000408144c00d43d03d00807140c0000340c1c0c903005900402250070400008a14014010350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 106351214 1250 106349964 106350001
    0xe0108100807080a12020d0507030e0d0f030e361b0403050d0305013606030506070c1b0e1603020d0c03090b130b07050702040b0a150f0503010806070503 67
    0x481c2c01554070b0700322103600e68120001c212010400161400c032501c2c004145100c510787c0307565036203003020f0058608560403c0308518a90b04002c0850600c808100725044100c00c050180c7c55404c869400c0340148a00c84070300e034640c540340460b080181c0001500d9403244000200da03046c49000306440d0340c10007414800500d01c40b0400b05030002400020488041480c19440f062524100503030380e0b944951034220701c1d0301518031740c41036401d01ca410743c4001a5012440081d0489100142c03036a200c7c0d8440d45006415180380020407031030040e01c01008803e00303c02c03a4124005500035030051034900385040c0c4041c064484502c0044205860007007034440c1d03059500392400505c041c40080310b503910180c020300e00c52005481134a50580060384111030500400c1015502001d84403803941d81210850301074202c40012031380f090300ca0141c1c084640d41c1d2800403015001c0101d200003600e180110103000114045442e905018003407004100c0110040b480ca0b52103541402e18559a03175407200418a03010040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 106352464 1250 106351214 106351229
    0x4090201050c0a0f030f031107060c0c201908060a090203160f140f010c031d130b030120040501030c09090f050108061e0a0207080c06090d030b0402030402010e010810 73
    0x318060f005010004400d4070586002c2c0d02c0e0595060b0340d03078a045081d6142400318983c850410440e0303600041e4564084484080c080c544020b48042c02c0d50b8403440f10306040e0065288031326000080c01c031841e02004191225920316200c0c95a540380000e0540c803210000e1080c20829030b00d41c1c02d1b1007035403014001c00c2084040d40603c0c1c250030740c44081201420466001d5102c45085405008178242001d9020070207441b816101c4810014a6940444000400d44082000c0003600207901101c0c0c0c03544d8186000391900c1c90300100e01e2040560515086030711000c100050b0303001075003241c400184a1001c03202075a5080c80c020448900b0820140c0e01c06409921443d10349107001b131500340300d09190b0301003410713214a941990204c3c3c0f0f0700c100c03029580403141031410368660300c81c0208100f5010355004080b9544030349401400d080690301c0350341c00c00e182212008002e070410fa00c00e800d410303403510039142150000c8a0843c1141080c1d00024032400c101242035040c042d80c1701c0030503114403418401034000c0045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 106353714 1250 106352464 106352473
    0x50d05280209160f030908030f090f071706070c0201091406040312050304030314062805030319030b01050403080a08090a062904060311060d06030503040e07080f1504090201050c 78
    0x405016400c3c441104800c0c000703400c8401c26281030348a8000c0000094104122509580f1247c45500c1140c6024000100070322544201d04800c21040c03040000400b810080c20001c1341c808d03401c2c00d081140c024640000c210780c509100b801071707070000012026290603a44001c008038004010400c24400c580016240005003505103c4040d0f11030015803149209550902203880c580141e00c480c090107460b400c1d0b1003804281c16001c02c200344891940300d601d9103001d24071401c1c0d648000c01e080d50b200d0603030044286600c00d103245910f0341500070b002c0d81920a181c0780c0d10b01407450700d03029281e000d40140107040015038804514040d0041040300c1d107241e0446810414110070702c2d8400c840b804940b49400e0744212416400c7c54902d8544101000c482d0004140e48035013140004000c1d280d444030300040d0100b555008044081001080a040906409980c00400307042440018080040080000c0d41c210481d00801a4160703c031041c0300005a02503c000c2104d03443e520042e00c940c0100140d1000600c103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 106354964 1250 106353714 106353721
    0x109020406090209031603021f0c170a09080a12030528060510020307080304020f190603020405040f0b100503070c06091208060108150d02120322050d05280209 70
    0x403654024416141d0442c11121030303c41903481b051003410365100180d4403000595114555050583c152001d0307039403078540401e40c190301e5139079255030005003c1c01180601010075628403141d00502554090546d0710002e148040c200c0d69a507444044103030340d420400d0b4440000c1011040030300750040c207640d6888110551054150151343c024451072203080d100b00010350310304e42d0260000c400c58008581141c49940703035548a030240304000a050302c2094114221540c400003078443c6406080251445c0d0780c016a07038614000c04c200a54088002040d20307540360040e03040d41980e40c07441508154855082c519101e5490200c1174507050f14021000d0441400c10000c07004020740702c07101801101c1c054442e1107160b10f9500044440c0b810880313100010540c0c5241c544c485191446180f0000c1c3e10003071001243d42003c0d186c4a0a6411207801600c121140c0801c000708418110015000b500003070721118000c4412361101035613410f40e40e0b501c04000910342048600b000403120b00c03081054000c0c01ca50f0742404c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 106356214 1250 106354964 106354979
    0xa0e060c0a060b040b06041a0c030f04030507050111031c02040503010c020c0406091803050f070807060506030d0201020a02030405090c1201030308100b030103021f2c12070e13050109020406 83
    0x4222800445460307140003d0001e440ca002d1240014107103029007041c0c2414144007110512036150140d102d0801c2d001d11140703211038820030050522240700c824042c1c85a01d14030f0194076200c69600020306004d4408120030110f9800401c0d03a01060300e03030b551881c6140c00700548100a00c603d0b045680c0550134031070142480ca80002d50004520700a440412495580301805011103081c040d001d10000e0f0300c0c0285001103031103440a4407421089100c100d26000c40d83c0e8481d000c0f94010034040310301070784513000c1040602e400d2051500816883c00254600910940700035102d10450144070300c103c1c02a80030500e100c00c80c1c4c050303900c040341c1100711701c1d40c55849082c00740044034103d800524441040700301041564280050b24100c0794080c0002059080c0e06080c80070760441005144104143c2010003c120102e00c40307044540301d8113002e00e80e440001d1b0310900041c002c01d20a0800181d010301400c03c11010903105283c0c0c8130010070788015424185242c00d0340135000700100039501c01c0c00d18101007482d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 106357464 1250 106356214 106356223
    0x1b02060c010204081204140112020904060e07030c020f06130309091d12090901030f021f0f030c05040e010b0307090320130515040506030304030206190e0102210a0e060c 74
    0x135580d6400300d40048210201140e4280309500603440400301c1c0ca40c02c51055401a80c01b000c11007205c10016041030a08000300e0102e60059210200110098051010460f050b203d91000307500f42c0d04c0901005890032030460b40c1d400004e4000240010300450440505200e410010007522000c0014003044141c2802a1001702c0c0d15021040d45000c0c01c040c5006403d10351007115407200d0040d1058a03168a55103515199414406060340c20242c11510344181a400101922540030701d6160301007400c41d201001012224404a43c01c2400402c04c4180b00e95007615492a0441d6510340b05c0c0360b5641d540800441d451140c5030310041085806440f20049582100003179000c51b04140d6400c1c0c03d0300c16100e410402c0d01c1007a01d04064039507049010400904007a004150702c06405021a481c095884c0c2c0401ea040d07100c100900c640070700c0d107440b290390540d03c1013421103444c409100400906210242c5040400c002c150b40b0454440c00251618115000700000c0c1b5134882d00502458481c10200e0143d602d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 106358714 1250 106357464 106357469
    0xb0402070501060504060609031a0c1603091a0909060909010209060a02060f0a051e040318030501050402040e0f0d080a0b091305120a0c02240331030c02011b02060c010204 75
    0x60303401d26001086451040d20008c00712904942c80c0d9451510030321701001403107809481e07410b1305c480821203170360583e854840300110030740700e684d650954501d0140300e610203229501050310310300420801c0d114190783e040d00c2d10b60071100480d482c0300c00c1c0d242c281c0400c1c0241f061034003c1d41c1248010900304526900450b00520803d000c02c05400c00d41d0342c41c00c81104a480071610460440420000c02500155040c2000c0d8000d00ca414090100b10202d104004600c071148d00c200d030142e441b50208011410302c1d01030b0407030341d20342c000040a860300c2d521441511201c0c1030380f200041001d8900003408845080c2c1160114100180149000707050058807102d0104031003000f52094410a018020b080b040b007800c88202d22043d039104100403001c0d03800c200401010354581447d03550b40400f6680080b654000441c080c210000807180d0000c0c0c079000440f10800b40c04101020f21030221302c0c500100340c000440e6a00c007982403900e52841304070b001c07040c48031110245000c1e40103040498000c00040701540108103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 106359964 1250 106358714 106358719
    0x30403060c0203030f0411010e090c0d06240c0312090602070318031106091f0507031403011206021623101517030c0d200607210b04020705010605 64
    0x10001440c03030070b070390704d01c4240c8107502140c0c80c1c41e0004021540c60b82c64041001414036203083c917100310f540010b0304160207440d100340c0c5803400a401c25806034684038010017458541a07029607a02c003016194a01c41c04054200140304440c2001003c05109030300c03080b086c560403041001490300a0030000025004032600314045015042e50401d00c84d80e04400c1c1c411280d0100b40c034a0f60014503001c6c4049500b004182a0300f104441340407203207030042e09002c9502d4401da552110b031a00614103000304041d22140422480c01c030100010304c071100040300d00a00c8103400030b5025a130340007100200d2501401742c40018181198102d4019000041445044030506040b405c4405450700c8100300c2d01201c20300d603040385c5020240201040102e00084042d60800004801d03a410a6207801c051424030003500f410000007012030024610100c0709200d083c110303880745801032070245440140a016074020504001202103101d0015040c0758103a040442c008a0140c01035407100c001d440c041e0b000c0d01c80f9000365407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 106361214 1250 106359964 106359971
    0x50402010e01080f041103101404120503070f080c0705010203040b0a06150203070f020109030f0b060a140d06151e0504060501080601050d090c030c0b0d0e01020f0901030f02041703040306 82
    0x10880d6100d442c03107038011060084c0b048010b03151a075450351035048190310301c4d4050041e07080030700280c2c19902c84c001d144d004071815060540341c103103404448100c110003280248182031051012040e842030144401d8101e0303081c00c1140c2d4840b10600c002501401c1401442c81d07000004000c2085103260025001e1240c4000c248801900c0b030b0070340b500d41c0b014840d200005900a05c1442c0c0800e441000c5851090700604018000076100c0d12140104480001b080e038400c0728880500c201c13801d01d0100c01c4010404003280910640c0c8140c0060401030044c58060481601c60118416800841303004c1001080d80044031000100c00800c3c003455008244585c502c00c078984140001d265002d1401607115840503501c4514002d48044190010445c0305000e03140c0700070489010000a0450348450090401c28a40c1600c985500000b4816034241c0d0383c500314607900600c210f22074000e0350300685186210909010038000c4c0c40703800800080c00703164003055900b09042410343c505440032004100352030040100f0b2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 106362464 1250 106361214 106361237
    0xb0114040605031c05030604060906060503180a0b06060c1005090a06110a0c0803040503070204090b06091003030e0114130f05030d02070302060d09051c050a02010b0d2109090f05040201 81
    0x980c40d140e130072008000c200c0c900d200007003c15210790001c40d8029402480051f0031619034410314112071035500810040b0381c00205200880540d0901c1c01807010f06803000b021032000c1da82d960910b9040240406000305404501d0300003c850a0000410100e02900200100c0c035041c42880d40c1c1da4082501a90f100f0b1808055104e07119240044a03c02d0500741c07a000160405562481840d83c0700500c29589030000b4403003480160f42c4c038010041c60306d0040d9689076113400e1400130000003080180514422000c00042000043d81081d0781d061019403d003043c40c0d07120089406852640b1508000d031103618048900807c42d160001c40380c07415104d0a400302c6040c490072001c00c0ea0754141e00d000280d4000e4050100b040c46020341c0d0071131066a4451001d968144102c8151690a81c046e00290170106a0109001c807285509100c0c40c074241304122232000304501c164a4244400c0d00c100c48040500d1080b100000f11903008450317070703c003c0068040800c000c0c142c05052030000e0409032030032400030b004000394 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 106363714 1250 106362464 106362469
    0x61b08070f03140601050a05070c030606170d020c0402090102100e060703060f0b0d0b04021917090c06030c0d06080709020a0e060901021009022b21080103030c0503070b0114040605 79
    0x34040340f009080050101a282c0d4401074545030084c40c442010007000300040d50010380c40e03014100007580300300d201103005030800d0000d00180f58450442c039080d90180c24012011580007448060341383c419140143d0b0303403030328400407414807040000458610f401c00d47c024050010009030188201d010f550b00b040007170388424400f5191081403151015035042404040c00c000c04580c040006000010801450484d400c50720143e0000e46a08a10109074800c032407050161000004c03642c04000d84010b41046080752000400740c0c000601400d401b0b5402096280c070740c07815a4060000741c02e03410f04680d0302e00d5940801030040d5000f600c4500001d41c01e2252002d182c144070080d14100031058000e010b1095200707a00e040103101d000c031b059074400c0703520b100040200709480200c044026028504d801200d40c504200b80010307201c0d070110907400d0510f02c508403922f03404107017070341540d0745854150401c0445047c03039440c40c00390400c003501c9446007c0000a4050041850561030403059505200403540ca804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 106364964 1250 106363714 106363721
    0x60a05090403051606140907080607050417010f0207050609010b0f090703020c07050a090b03060c031308031b030a050603010e0703020102060a021309020d06050a0b180904061b08070f03 81
    0x1400c0d00900110042800030340100040d1419a08420803441400d0007519510140c0d0307034107002c0c00c10744002d8005002c44094103201c08405852010020203c41c100000300404500c100c1c403444659003600c42c44049024401c1d0031440001410040035522044542005902c800c1c090b1440a0190f2802c51240e1150400c0c0d0002030103282e0007403135240c641c0d0300d010054010b540301c4c20f0000c156000320071021800756607007010701c005040044000600f00c1e02441c140351402e580503210822803c2c007442080052424080d2442c0c005500031201622501d826480300c064459806420500303640101c10001c86011039072200307105280407070082c031020880911180d00c5801d00d0101030300503040040050600d0007a50010650920207120b049030840e0f640ca0203504903081080c3d11044151a11401c1200d031410f0030142c0040c4c0140c0e4441d9103400d203402d541d040d5102d911209680210564030000f41409080d41c07061100111030400440d40e1100d03c48000c118200c203e454001180c004200c855403140f0034032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 106366214 1250 106364964 106364969
    0x1501180e030306010e0609041401060207080102030907060c050f07060513050d1703070e0a030605011d24010903021305010f06050f0d05041e03030c2d03200c03030f060a 74
    0x40c0554916250340c801107030a1040d81d80f1040e0040c2e0104180c4207152a644a030f820240503d004001d40c44d414240000c1c1000510b80c0f182c0d05a07070050062220f000000700380c003400c9900b54203103c40c1d145518a8010306210011900041a0003102d6000481a81103001401440f03034562003800070680395020001402c581c040003410a1101310008840545d00000640e0085070f14101000c1c034100000c00a911242e164008075141500c80004112030708a6416001e034441107201701111034940440020b2241160304440341d000c0d0446a044004d6034011030300e0307101179a0090000e0407482210b60220000e400e01f84241050700c02017250019940d44100145c0c2d03814a174818070340380340a010102c6032000d004094410b41d55a100192024214410300e000782c1c40301882514045000900320030040c0c10001c4407000108401641924000c6020906078104403a024509000407800c000c00c03200d111240011246044484001410f041074481c0000514461001441c8648c1c00d9583d100c01e220380300381e561 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 106367464 1250 106366214 106366241
    0x2010f0c0506180106090c020a060b01081b1e0d1a0108010b1e0d0e160501020604020a092a020304051e0a0302120f0601170606090f070c020402070203150118 69
    0x36030203d010351102a4040048642d00c40000c1907003504c8040140441c5d050554840160340480009420003415014450100d4424207260101d07103499a02c103040c108046211907243c1400041007400c2d84c1d40d035030207100520300c4400b03919298003034a00302900410b03d070300d48800041119800da2200358494001e06040e074510580c003d0403c1d409450400000005042c1156805024080c500b0501000d1045c40440700e001002440d0480100e841003000e03142e5504080c0c115080803003000096221101001c041380d000300b03000280d69402080083e00200302c1d001c52000754824103010002203a0000c041c00640d00107c0d4440a240802100f450f0480d400140440d0402c3d9480e808101604c0d07e42440c3c0d80f00785004095802401e4043e08a84c10031400360007903d001c1102007103410841904104040c1d02c5202030b6250300d2941030a800020014070020122020001c7c03a07101e04085448603016144143c0e40541154400105440900c2415100740540a00c800009042d00f26009490244441e8000c20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 106368714 1250 106367464 106367473
    0xf06050f040207020402040302130506270c03070c0c06090f0509060a0e09070e0903040e010506090102100c0905030a1406091606050a030608030a0804030201050717150a0b0409020702010f0c05 84
    0x50180400b80d04003020590b841507081c800000540c444000038a501d202c01c0000140d546081c00420883c0440c4030a0043c0c9540844540300c004000300c0d180c0c2c1e40104980c0c11b000e48030798940200f280d00d40b6101500500d4140c50010010722580c0022b221000d540c52000c00740403542e103580c14800070b40f50842c1c540360702c81050b007001c10030600024605900805007070181c4401c2500c400098054050540b00500713180d00004042002c004125015405850200c4c2e21034a01951500000e564841c04c3c2c41402c10103a5990100c03c0c49400b45140c2002040e002d070030740c2c82d901c1650074000906103445617420094000e8400080c40f210000c540c220b5000510321036051500e0403c1022242d580005c7c8020050650307800000c20700ca50100090070044545640d110a1482d1501d0020b0130749102400c000f06001048a60810038000b69002e00d0380074400408686080030800b000400000c083c0d44103184045000034045200181074004080c00c50007070300e030103a40441c2e00c182100c202112100251a81c0c21 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 106369964 1250 106368714 106368739
    0x13090c06170c07050f06131a04080706050910090f05010b09070c030e01020c1c0302070f0f030308130f030f090509010e0a0b01020c0415060305010509040308060907090806040c030302010f0605 84
    0x80c0002030030702c0601035421196039a280c0429246486c000380c80842c00444801040d0040007598180c400e0b4150180d00e4802c201e06150b9294940d60154400c001c007515155400520a508204015003640721040c07003d0080007424188a11900c4492400f035595508141c004141c60078206029402600c442c1d1340c2d94042c0c4256103084401044000800c1c0c110300580b00d9112281e6104035038a0b008603004c2105c890031030f80c1e510b000381c60a10940d01c40c807800f02e2070300410410219130011000841c0c3e014180441a55a542564959107014500003000d41000e02840010316500441103c0d04030525140c07405400d07120420040465030034440c4411580c1d4900000c0c01851540e01708420382a0103004640704942000c002606440c401c0300701030804100c4e0001045499458002d01b401048160f4814100b81001e03100140b01c1d10000f0300d114010301101c0041112180b10712485402420a60207030703800c40c141450324451380e040601c4268019801c00c049803000286c1403113410222940240303140124203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 106371214 1250 106369964 106369981
    0x904020904030c021302040612111c0207021e013009080903100203060a0b04030807080f1902030a1103031015030f0e0d090614030a150513090c0617 65
    0x40c0061045080108000e941d500507102c4101d800c00a0420020143e115400d000b8014003000285e000b0040c00e42c205005c0c12010049041103d1720026540075020400720000031040c003911038024007d4200c1c503040c80442030315141c1c0030100ca900c003090ba0303500c058040c1601c05074001c849144e940040360b9001c01c000050f00745550301a41170725100b0844681003620300300001e030401034100c005419654000081020b949444203512000e017008850b95810a419903d5041d010b01034548014014032001034140f030804021420303105a180000c559018013014144020b440390071002031000407640c2c46000d525005000320950384900f440c540f1740c0e03a95a15254081480350f560240c041309047e55071000c0c212920080c0107048040d44000014494030100f03100c0100550802e070f0280c0c04101180072100411282c081c2200c0d0404152103007c1506024021861070341e00040c1c0c001540000e040d0300d1041181c44603001020824064018450402e80d40c001c1039503042e1940c0e2407100020014000100c004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 106372464 1250 106371214 106371229
    0x40504060806191a1905091b072a0305011e06050d062406090e060d05060c0703120204090527030702120109140f01051e07050a022a0405090705090402 66
    0x800101e04d042e0b4102d036103140803c800814604103000301c82c0b06141c09021500740102e0701030308074200c0449111045000c01c54042c51f80120540140b81c0400900c2d2071042c82c5070000c6c40e498a05940580110840e5603103081c0e8020022181c05a04021603c0d0840300d05049a208003821a0006003c00341d0500702d5940e060018586410f5031420755840e21900080c40f40003c0310b910151440b51200c00c60241480c01c10314010304010001c51013142c0143e04d280002e070011a00b1074000a00e114100c2d1903054034076044d40d402905100e1003183d5813010600142404c820b8220038006d40d04400c04122140b80d43c01d507614030304107414001798260310400c10b860046c20110405d810000440c1d0001603a0381c540c2d03480941d5800041803101c0b0340d510411006800800a00c80c40d60815801503043c0c00320780e02c0300014012000000c00d1941401008207054440320300900544040003d000b13101001040c07191035210004610091282c000ca2400b40021001c210000342c090030f584004001202030b580e65401c00684 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 106373714 1250 106372464 106372481
    0x509060109270e06090a26032401180b0901030b060a05030103120305090c010804021212040807050904020a0302150714060a0b0f01320408010204050406080619 70
    0x10005140c800085281c02040d19041e4001d00150030800044098500400d03a40f0860040125411010a00484e01400568000e040f07a0190410300080c1600000c1d0042c50003084017041c80c0c2d1b2002040102807909040851a403810741ca20030b00c3d1804c90130004461140c0c5422040000f00f492103014071001048002601e04030405141c003003001d80e0400e0101300550016283c4034003050010005004000d0800703443c0402e4440f0345001c00c018905280030590b190200710500b81400701010201c0c0c1076494440c05800c00c02402e10490f1008504001c00c040980c0c040c1c85000b01c00c1c0034103c00481c01e4980940d019008903001003290318447d003142c0810030924034584184000035400c01c24900003030925920382811030180c034054445803800d128260103507441502814491001c10741324544a0b038009a019003004801c01441900c14040b02006100001050550302d039a100802c001410660540081c410748400361006e004c4aaa185482e968880b0180d400f1507401540380080540300c001948074446 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 106374964 1250 106373714 106373717
    0x90106120b060c100b12070e06011202030906010311060a05040e130b070801060305060402030105091602011d03071b060203030a090201120204061101050108030406051204050703080f070c06051305090601 89
    0x9001820758002000d0303a01606919071030303070480d00c08509100030714800c00c0083c032070540d6010000411036085a0b00d802c424010429030070104401f00d003070350b44540c0707035503014542d140000c66807400c21b001901e80d613000901c021120180d41d890754508909201c0203469208020340c85048c10903051505654000c28000c1001b2a206280008a408100705040c824004c2c1e04a4462030281d504020000b01614002044a802030380100010010360300c645401d182d011902090312103442001480481c00b5110102801411314000191230048440110041401b58490054000010141032401c01c00e90b12520036100036030014400a90496040d4002d1036031244149003d181140d0a039403000c0032038100d80c22180c00542d02204650f00b1100134172949000d000520001c504040c64001c00404610442204a6141c91420007103000c0001c00c2024801566100d00c1d010b885001965a440d01a084071809460056000f04000342c401d0250b8219001c4007154560902c03d1810841401103504000d0305550 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 106376214 1250 106374964 106374971
    0xb092508060609040c1d18010303260c0903010b0306040309060828020408010e0c060d0209030708061602060112020102030f0703050903060403211811060c0a0804051203030609010612 80
    0x19501d941301e202d002c204950607286e02141039000152078080f28207031381006001c0d00360351100744000d155103080e91b411258035240104003d0360843d0b0280c60410b20151803800c0000020a11003181c4a20002d070166600a600801040e40079030304240c1c0c0c41c0310503200500420780100b400d00c840b038800e5031980d90004000c043c3c454111140400035181035a0000310080d040c1d8040390134803c140b000e01400503a0200b0b803004129400c031901c0003071034a10440c007007400f0a44d0700282c1345a841c1c80902001c0001c1a019064600d140341400c00801c0d15016101d140005004240c00400e401c2a0668042d01240d0103074011401e002540e000d4a1f4164440e60056051200c02d100c190700c1c558041000303a00c101d110740d880400800403550108072040010310b40c80740b00c50078034080f258410b49202056a0094002c16101c40a40546001c60050b20030340109071041e0068500c0c640a000d96000140201c0b00e09641600c281400403240c03580360702081d03501d0303580036003000e0041042074414000f0326900942c524002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 106377464 1250 106376214 106376227
    0xb040605040221010621050d0807020a0501090807030e100c080306041d0a15020a020309040f11040609030507120f02040b0a0f030c080d0f121e09060b0925080606 71
    0x12001e01c10310719000003444e91106001e021010f50350400020080225600f03541d141281c0c2e40d1592242c00c4c03204000200005000012a018400c01c1071002c4550084001c012012070350030181e40300d50026105502003100212040700600303203828010343c111115a0303000c00c85c41490355601c010f41d101074181d40d030040e01c841007003102141303800e03856803042029002000620719900c0c203800c0601d40b0340850f8041c2c0b8414013044206540100031102e40310812103000465078200c10503a0020150ba00320010b42707035400720f0701007200c0d13030084944000d680c055000c89907159076843d480140b442080e50014070111005203900014101030700309080050f0b00800d844040c5481d81c00841080403158003d0b15107046100040042c0801401901002001c9160401c1160006200541030040020210008030340c0d480940c8240c1c100d2842c02e00d038655401d541400b0400c00c5042200c09484002c10f000d1042c07044001044601011121104030303680c00e640081c04c008100c0d9804e640014000344915004401040703007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 106378714 1250 106377464 106377499
    0x170a0902060a2705150d06030b070c030e030a0807111807200705010e1513030f02040507080411060d0603050f01050f09160b0a020a0614010603180b0406050402 70
    0xb0b4082c0d44040d945004500d14500b80070701640c01d002803804540343c26110306001c103480702100c03048154221101640c1e40c10b0388042c1207005200c40e03400078000a00103001d100816900c006040082c601a544046c41442044100340d2501c2c0040700090800c0c2042040c00700040e401c1e88003c00da03038002400710000d0b01c65401c02226100b0122000d40004410b00c1400040711540c1010703d00172014280206116401d07c40040c10214400e80c40d24440c11030f41e001c5d9400040e0140c219a60442c1045400c3c0d8015580e00d020200880c42e01c0f82203210310f007080002008507104070742480c072868018402e0707a00390300c1c4242445040d03403080d011103500a07160003020020800030020381c81c4010078880001814131f080d00d54842100000341545409800103050103c0d175084928800095410b50b85100e030780c48240e00002e034a0613a40101c020710709410003400d5103910f03540c5201903041b1050b07903d092228003281000e211440d160520024650f42d1883c0200340801e9096000f00c2e840303880a4541c014100308440c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 106379964 1250 106378714 106378717
    0x2090405010308090a0b0f0f0304021f0807080702031c0b0109091104050f0a0b12060a122a12060e011d06090d110309240d06050f0d03170a090206 64
    0x1040c3c0304260000b030100100c1c106416840020800d004c1c480c0d041c0260b01e500b038415440344038001c1c10030b54800320206095503185003401e506c4218900c07030100072200c00036000c0c0070103c040707503428081141440042e103c2800401110120031445074910303140f90070300c10300d14001c00d43c010b800e90400c440100c0104212800c0c0c82a43c9015a4030307440140c8952600f001c1242d09440790481c107010f140000f03000c104039081001580d507200301c54007280041d0354414010442c14005948500f84240d100c1641d8000d00c094410364000b16400b201280704142070100440c109002c962190030340c1c68144540c2c039004500359038060714a107140e5a0001c11018030300154105401c51968610b49a50003410078400b01d080c04001c041a01074140c24543c107840c014600d078548a00442501d42e0103500320801c54403106000300c4551007690402038031603031500c0d803e0085c80300804e2a030040394024041501a8151858561100488503506546280085800e80c518600707039003000d0b001c0f41005844d042d0a1005030746e0b080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 106381214 1250 106379964 106379969
    0x10f0e0105160e060301030b09011107030c050d0311160512030403021501080c011e09170705090612070303050f04030f03050d0506040603080a0c020111070611070815070c02040209040501 82
    0x400104850600c480014114000c0c51590000c0c0481c00c9003d5140e078846209690441c0e411101c048590f80d112800c0b0360140c92869500c03114000c0c0003c48004164100c940128454010f800300c500410b4602c0043d0702710741c002400004140c40511620f0110303070004910740780d03443c40381d01a18071700c0050711000310840e001503c0440250b0480c410050350802425106801088200d00074421626090006810355100301003004440f010002c140003418041c0e00035a00801191141c030307074100b60035030b0019110207507802000c0c400c4440f81c000c0f80c518504003880c41c0301c031042c02d070261200c2c1c2c0c030303665007940d89600004010a02c090140300010204000c031140c100d019000b6202c0da80e58004650700e01046580041001d8852440c101040c03010402c40d0f0140c0d807050394a41800c840c3c484042c00141c901e001c4102c1c40d900e1743c6c4248107021404551002003912100310800031280220703154100e050b00c400c12a12040f510703000c490b0015400d20f104400160341c2500240005250044240106042d0340098 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 106382464 1250 106381214 106381241
    0x209070c05150c16020402070203070b3013020a031505040605060d0c0302130b060706060503011107081e0c1e060a0212060f0111030d0507030b060702011b0302010f 72
    0x560050103024040d05040550005a202c0c1c50b2810f0001c80070140580414603c1000840d089207045486a504460304203400904031030703d1665440b80c00c2c04a41c00000720221001000c041c050202410901f03130040c03e819442a07107200ea44000c1034000015611905a9010816500001c0451244001c4c10820035100802060900e0281860700075100003401450290201519000c084bc8406082d14140e030390403106003082412002041018102103150a54407403c00601c0c2802c02c03000b9032140c81195400e600a00192000040520703050241a0380030b003146004201d11281c1a5184521009440700d0f40030132414265103d5000b8039004256285402c084040920382c8400d003400c200c3c1d29480034000006502c0d000c0802450803940d1406065580501d0642c0307160011070780148402c88090360200112615071140a14060203401d082c0c1d02c80e0080782c940364140c44541050412107151640603141c0203003150440c0391000501d5840d000a90440d50382e0694004a030500f4000c0c0310700540791f03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 106383714 1250 106382464 106382477
    0xb04060e010806251b051e01020702030f010902240712201f0203090a0501090c1a070803040b090c0a06020706020606120706140f04121b030816030c020907 68
    0x4401010341405504d124183d903492a0448001c0c4540c000700d18580c5005251240c8510b100d01d1920b58a031140311b0034415a46070009080c403141c102c056020b04500d40c004c8044614441007402e545088550300301c00603402c101c3e8810140c1807035411400c901c0034020020b0500785009901e840b0000720060041e410381c00600081c047d4040302003c84594050040c5400127000403150040d22042100c100e6118442000c0d00480000c990074010700c11410100d801c03034000e004031002440c00d411240454002c4400800d800c1d06000940034810041d500d40c1d0f5401012180340d40c6403a22281070303044000b000f9021610035420780404948500e44807400410b2260001c00c803550a20368042d0420070001c0c0343c1c0c2d01410032100b681c00c1484000072a141102c03101e040a841780100c50068841a00c1400c4802c031411070005070014403103a12a24160000d401080c614208412810010706d80380050300c00500350783c5042c058407032801c0003000308030031451003420070281c90500d50f40815441d0104640034404201c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 106384964 1250 106383714 106383721
    0x170c0706050703061511120406020706170601020304090528020318032a1903090504050106050c06010b0f1b0c010201050c070b0103030509180a0603050d030c020c040b04060e010806 79
    0x4150242580200b650700701400004c0c100381e211030030240001c0181c01003180030420000070303aa0500850600d1003084001c3c3d65141c0c1c0b00c45d000f940d9450306201d42000a0a4a02c03403007402103030060303094069001640514645840c25407600090300307010b4001d640788030881c22804d070740ca4902224803c00d0b03070810602684030714110280d0002126003030490400ca40003042a0490754103140009240e07021048102c00d0b2000d1a10005498051299040201000e02e0400d04062540003c030400456604a409011903078841100300e440f8000d0140040441d4814001805102d001030041e14491810303140b442c0c14078040340c00041c0414060244405241c2003d03da020441d42d081c003840b5032140b030404040307150581541d0307411300f007840501c40170707080007030100320302020340c0c1d4401c142001e4000c03e400c0102c480c140540403070000c014a1008454520504031000c02c1c80d4024001d03c541300c00542c01400d84803029005003c05402c44c81401540310b030b0b640c40080344420310f680180380a001007100500c882e29 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 106386214 1250 106384964 106384973
    0x4090f0903110703030c020603040602041208030103170c1b01120606090801060f0308041502100501030303231005040203060609030a050607032a030e0a0210020d180605090d03170c07 80
    0x1a00d42e10400035034101400500219402080c1c03c2003803039040d80c8003592a603540c00d00704024001c03a000412415840d400500c00d114010020714143c034000ca40f02100c0303410420030140103209910202c412508000d1a5441c103401a140b01615800181044c0f1503003004401c4000858009410a0001ca41030000a0245803002d2050501500c0700c441071030b200c1c50458507014041d000d00c0c490500c0f861591102c48891620034002d1500048100d603040c411541c403403030083c0151022002d180758038880420651101d02c0c480c1040c1c2d0142e030042a01c80c454608040610000c1e45c001030529403c01d030204001203c54130704010549085000e030000d00024203004c3c40040580750002c9080c0110b9000040b80341e00e074004404400090305030f60a000644203d4008002d061981c8440060360101d2016010a6180e401242e960880307070880c1c3c1c03034105202450300b181c007003000240074101c00035109024a0882e802d0405244000d54001d00b000b8403044100c1c00360300410300044404003c1780e200450020f0401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 106387464 1250 106386214 106386227
    0xa060506040b0d0509010b0102030f071104090803071d0a15020319020609070b041401052a211201140102031309020403030e0609090c0f0f030103081207110d03020f04090f0903 77
    0x1105d120007440820b5074040000c1d960301400c0c2d00e01d2002480014408108420b0b50ba071078810100c0604140007040c0242031105440d0401c68082002c035401030403072945010070038a082143d50307004010016240c00c2083c50100782c1c11901c544429031104200b14041450036001415051100c1c1d4018005844c11500c0d147c10034142c3e2b0312281e08180244420311100c1482d80301344000807001e183c5181c840c3d211a180306892800c040e500c03c0365412000103844045004921900c0e0b1404a4410700252130750409159098460000d0031101a070803240140705510980043c00080d500520440303041101c00c1e00380c090403c1e05d6030f203d01ca202d81d0008040041603044030710a0354031901140e50038184000000442c4802400405540c03c500b00000d680e2041116042a1103440300480d203e075440390703100c4c1703800c04003548032600c48941200300030000b50b5424402c840ed45504118207024000c0c003001c869007070b0044c1d04803920051107507105110204100300c00384116024100e103c80003050201c254200540300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 106388714 1250 106387464 106387471
    0x1050a06021207060b01141201060e0a140409030201090206040e0910020408100c02120d0501090b0a050a12030318080d060e0709140a0e010609081519050a060506040b0d05 75
    0x15508000441d80b400d0300b04600f6035000c0ca0b0403940100300004031800407942100c000040f070301e094001007286003410181c05400c9040e2019500d400010410300c0303042210641080c8940810201812541c400504090b045210001e21078000465010130070340c0050b03100e4015402c500c81c0c40d91701c6000c0000d002410413802070b41d442020800c516081c01c0460061301c8848485400e400d658075980403592a501c08c000000c15545006031480d281c6182c121513201620f400c2c41401001c5c1d0501e600040c481c54014100c0046480041c2940030305450300d003004594050100040e000d051752800791000407500c81c01d885940034485c034500784e540d8504c040814111110761b0005100008800d04015240c2c0d0814070307101c05d0311010909070030107080e0800020b0890364650000b0912405050000651640040780700041d604011b042d501c18541c040003180c0302000c11035450400c6100c0c3e0f140c0c901e4422241d40415004002c105000c40d01640311300204440754010340c00320030b12920002e40030104000301d101e8a0781 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 106389964 1250 106388714 106388717
    0x30201050604140f070c08030901021210050d030f050408060f010302031c020613081308010e070816030201081e16090806060306040206130e0702010606030606050307080117030f0c030301050a06 85
    0x14100c40c50041c0c400f114401030805240d841c100c0e0200300401d00070080c6803440c40c0d0100b0441c1d03491606c81c502c68081d400c1842e800000714039500115030310741d05c00c1a5050603108050860580520503880444078028040324880034043c0421001c9000c0340244a520300c500d00707089204000b03501d548141490126403442c81c050310561801d204851030382c00f140b51034218050140404200741c241c01c101080c0d2080207903440803244d055a0000750340c42c0640050f04e010f40308800b50382403e680c50382d406071900d81d0301ca00c0c0c140b51820500103200643c09504840e400058000e108c1c00c101d1a0b14a010040d4107090760240401448000c207075405030352003412074000d024284090b02e602c0c00c04102107a55010040c0c0000c0c81084e01141110740d188211100340014122850944424140840e020f4020311481c058000081d003012004103151303000724112b03409068540c0e00d201c02a071074a04000c107005004074500d009400100700c04e21000411001910041c0000000b4560b01d524210400500c620503a01500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 106391214 1250 106389964 106389971
    0x60712080708060409020a0302060a1107090515010906020706030203040606052d030307050c09130c15081e0604200703170105010306030f06150f0e07080a0b0312070204090f0f030201050604 83
    0x585071110464101d989c1601c00076260105a20140c40c4011820080e00e0380c0e102e510b5002940d0070b029003002e0b028003510403500d4000903100b001101d07180340900440000d42e01c42c03201001443d10990043d070b4020b0003503100040140c0c0b00c0307000036021000d0b03030400215444045160601d40801c05410f8064a4048005500d4101c040d42c941d622040903580c407a100e060000005403040785920000d200450f4819100b03000c0f607803202901082403804815040000e0a000c2c00a400090500108512a40c04010207940d0356101000c000150101e80841171150b00d154416a01d903800e450b0160140e1403082d106c02180030100c244d04e001c0503c0590106040506003c0c0030004111510785c0150703043d03001503000c2007075580032880043c0107040c1c3d80b11640000110000040e18003804605a00070340c07450743c40755074980341c00300d48070182c50002404581c160440701d90303c500c1400400040a038544040d03c085186407260311440380d0100084815600f400060708844201503081c46101d45c020b00c2140c040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 106392464 1250 106391214 106391231
    0x2030a0f1805030105180d0905010c39060e030a020a030f080c0303190f0b0303030109150b0f040e0106031401050909010905011505010e010e060a0e0607120807080604 73
    0x1020650340e01840428460041d0200201c60295050300016000160082c0b20700c1c2050203041e0214202e00200d154940540c035441000f85200301141021500143d4418208d5800382d141c1001d5900c40c2104050b041005c07402c01400720700b460364408000c0f81d0458880380c95501e80a000703001035424500c0c4a10a410600c981c0340166070b558146010b880e0400c034402258001ca00d040100362158039045000ca11001c010082c400e042d503070040031030441e00305091007941d001410b550280c0b9010003805a01d40c1041c80184802400355100c4a02a040e0842165600d90307186c00e81d041039408000c040c058820000f80c10701c05405550701490050600d458104840a8000752840302070b4018010544254440b00128290307404c250071602c101a0000000c0040b014940e40f200503003070356441041d002c5841c0e0a00075000d50302a41780c04803141c0740506110718059004030300300c42a028407005035a01001c280900c001150951401c140720703003041d448000e080c0c00c00303010140c54035030000d026038400d6082c06a40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 106393714 1250 106392464 106392467
    0x1e060405070b090a172d0703110402070606030b010f1505030402010f0e03061008010f0605060306040905190302010c020601090e0c090901060902071104050f060901150c140303061002030a 82
    0x6241c21586840074054407040c80703100252401c0b842e5449500c88003032030010440c100501040c0c180900c3d140a108030b01c40c6015281e40c480c20f4805800101c0740703401c01401003010900c0c1216020f61990018030052801200f903030f50004031901604107851601058006100000124400c080a0402110b0590415200d40d1000380103120050000b8104942450440d203407600403123203400c8040d0000c1c103551152070808410502c0154502c00d540d00343d0f003440e21505001c00035100745015a00090201e03490b69440106210207000801c0003112107110301d203039814140352807101c60003409102f6400801c1c5000c0880b030013840c003603040c0c001a0074186060140c4901d07210001d0382c220440b0066403c1c070071564440d01d2550041c40c0d281c0c410151b2500000c0c0c400d007000400b0345503a0880f50200d07002c01442d00c0740602031020348411180107801c0704040b4018040704021080704110707583c00780f4100d101203c46a4441400003000090b40340c0590020080c03104d285040180e030284031007240b00460410100e10320 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 106394964 1250 106393714 106393723
    0xb090a0b0a030f052803021e030a081902031f0f120b100e0a150807120b09010f0c031d0c10030f1508070503150c07020f1c03021e060405 60
    0xb004010111148085040102c1800b2401c66845528003181d44101e42d221440c0d40c1c1100900100c005001c4c00c2c0e0741c21080e1101c110001e00200b2120021410a21522003d555901d00640314001c004001c4680c20800c3d01c00740002c603c00c0c4002002804840c00001c0c2202d41440d06401107040c90080040a020400b800700900d05004c0d04000c210149032999162070081140d00c1c2c01c03450b18484070074200115041140c1268210072900c0000d071301d45941d03d05440c0c1d1108954014000d484042d561078030007181c9000c0392290030851003800040c1c4e40b41a410003104035852050900302203a1220b81d4030043c001503080c0c600c0c00058140103008090b11000002d60308003521340300d500a1582d6074074510102c2c640b65201c500c4000c0c4511626801548400090355100061320a184c460701c5420054005481d004041034040d50a01100502b002c209038200407100001030551a0015001c1003525128200d04032a085000d010744c014203807503184000c600112240f82c0036800c200d60b0108003880002800010b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 106396214 1250 106394964 106394969
    0x161707020303270d1b080606060a03022101030f1106070b0705180a032a03030207050112021c05041101030b180408120f0a051e07030c091502010b090a0b0a 68
    0x14020b605200420800c48880c8001c1c0f407a1540012418010380708100e5200344001034132000c5042c20b50300641d68036015a9400701212125004282805076000d00b500a4000e411601031581c40440c40102c8004c0c40c030b10a040990064401030010a410020f10050019421000c501944d0081c54001291101000e00740045c01c42401c0003400509658082c80c20310059901c04e800900c803003851ba90700e0400e40040f40f44181d10740103452949001d601d070804030001071400ca039450b130041c08040c2d1a0038019500204a03001c0103d009230204020001c000c02d03503140c0c104068152a0000b80c1d42410704000740703000400d42e03e4506161901034100305641d00c040049403120415984420140d6403890026014041c0c00d0301d0482c01c2e0010024090b18201c1c40402c42c1c894042d00300200600e9032800440062600c6c00022040d910740810045a5075610a400040900400e403d291000e42d0b51019105e140a4a1100c8480142d66a45038143e807440c0c40e5440740e8200220b80800d01c08021420300240c80c190852 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 106397464 1250 106396214 106396237
    0xe01120c05092b0303051807150302070c21030f0906120203130803070801140109051f02070b0406050405030106050411030112030c0c06030b03100e06060f0a0302030102161707020303 80
    0x503c4242114801141014940707940443d2541034407203241c064094076056a0380c00208a0808400480c0703503001400204441c003800142c0061038054009600a5100207000c0d2031b01c0000c3c94011800707024140c040002e105010520034031510b4141001045000041c8214040295402d010031406034442c4504007221941000165241c0360199524044015840010048240070082001071500504010304075150741c10104210101c4100465501d8a903004040d030180c3c07442d468140c103030000f003804003211005004860001e52201c0104407503401c03907481361001850024040c44141406e0041038010a403d850900c25503c01022200003408140214190095840100400e251080d07203e481e006822614848280c2d8880c0d0008000c2c2806c8080c85004e40704402c1c8183c0d40b8400c80c421141c0300a4807002a03c060b4a404040140501c0e41f64403d60b4040030000c400f2025135030031700c01058406103040322041e40410916080100c03091086606080c00000c3c08001c0144e00c011085848681c4d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 106398714 1250 106397464 106397479
    0x6060a150e031b0a06030506010f08090a0b04051b04090804030803061305190c080402030c0f15040e01090b060408070e04021206091f0c1709030c0d0e01120c0509 71
    0x642110750018140d2060b03403500c14822031003e04400d581e41080c3c0050251000c40106484400580c20340c0c106440c0700d030001e0840615040d0780c42c415200f280d00700b54101c2c241d450f129229140c0004000090301c065039a40c00c403401084480951418004103003006440a00600501307445900c010b014520000c1c0800b5400000900540e44481441d044040102e10400640c1040040c8804514003c920703030310303642d00c2e0150100000c0e0203415200d03c203550042c000c6c4a100d04100500c4951144000c2654102000c0030402301d40e20f243e00d016001400c0f01723142d400020740c5003900803001ea542c1c43e0003c0f4026803040106100000010404200303580440403513511949641c03011415031002100210603a004d40024010b000c1c80220b032200b0a200108904989144038280c8a81103a403108541c00c08901f4522809240d614100300c0f1591181580c8213076400d01c1301c104406418407107002044400140240354101c0d05682100384904600da640104000303100c01e41c90090450701c100000940300309036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 106399964 1250 106398714 106398749
    0x702152a070c050307170105010509042109080a080d110a0f0f14040b09090105041b1b05190c0e010e01141315030c0902030907060c061803050405090906060a 69
    0x1c82c046207001050040c040301c1540340c0e5038030342031410807180307400000c01c1d400d03d000041d651500400c0300307006a40000b01c4658000403280d140c0da61001e4020840c081c40030416000510290500448100c01d004510140da00c0781c030140c080044400410300001400300c01d002c0e004002d94808031180e000650360500c0c407010205204182e13440d8100d07003400000c1800c001004203c0700380e00e2000d403001c880d040d14007501c81d036250300800080d0b540c0d0750201540c1c0000c444528418900c13441d482071640900b00710348600400e42e51034a905081c28110800b030144131a174040e0b401c005100c02c524004011010100c1c0c05035052030144042e142040c4944003000c014565131f0640c03035480440340102c90390819800c100710300b42c58031416101106480152000c8030088000502a0118021030b8804c20401c0042c00015080807800e443c030304804241a01c0d906c2d030768810249541e070510108946640251282c0d40c482c0d00e00302c204000214010664902500080280410f6444061058050701c2c107010300c0c903401031b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 106401214 1250 106399964 106399973
    0xc0807060f0f110706091509080d050703090515070b0c0f04031415040506010501020f0a080702190803041d07030e060106050903010e01050c030402030705010503040302032a01050702152a07 83
    0x8902c0b45000f005801081c00026103140c00100410881d4541902010f545681440503100c40300c65104034801034010b10341441e403561048008008091003401c04441c2251503901042d5102c02001140c50800000580c45042c0104c40c1c80007170307001c07014076501440d248000d03c3c1070105000714800106008281c54140e555481c00340401d01c05185d011052426500d058200684d84000038810715000d03000304601d9090709000440c46103041760708009440e1038a403180e400e000040c0c00701510b040340c200389039a0100f55490180010802003d03401e80b0015050204007010b062918081e10040905152104094540e500441c0c4541141c03644e041058039600540c0c042030150160580b000965441c2c881000899505c0201840c051030094040b03a080c90b03190401503500d40b00950303000d009a4818400642003501c3d03031844170f00020000f07542c0700240c020300d111a420b58406407403010240e00807040d143c485003403e1001d150302086694600c0403c00710f68450000c1100140142c010841001507903800f4003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 106402464 1250 106401214 106401227
    0x4030c15090806070207030b0c0408031b010b0310020c01060905060d14011b0c120809060c030a090605010603020702040b0307050a090e190506070206071d060702030a02090109090c0807060f0f 84
    0x52541c0c07819030f40300b40303404034009440e014180011243c0c4070281e80803403401003000060b901958880740c020b45c504520301500c10052100000c02e05242e64a031042078000d40c6041c0305030b00344024a0030740541c07a407402c9880c1500b0745170107030000c0035070510701020041c56699885004081903080070301e002d40160341c00c0841340502012402c009024040042c0308020f0369000300441c0c2e007180a00c440184000ca055021610300390709940c0340396a94410404034005084070f000441d04900d6041d17001030300d011131743d4030134047e00d4090740880003103580030480905505241c0602d40c5203000440c040c05900781080c3c0022240c506500a40e0704c1266038000c4101d800c54104201a211240c1000340381c1000214500a55140b10850320200103004084c086a580c50180e05541e1030b000405400302d0100790950b0a012068002e03000a907814480d1700090009070700c88011083c00ba001280c804110060141403c1e40810750070b5021a020b940115000c00030b80c0d0b841421401007818910b09030007040d80c600c2086514 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 106403714 1250 106402464 106402469
    0x8070e0402040b0a081308070308070207030f0803070f0c20040213080c011b0b1b0d050106021b0909030a0302030c0c01020415200a02130e010f0903030b0604030c1509 73
    0x1240c4001004070f44246148082c0103c00c03260341c0d5600d902d64610b002100104440c1c0c0c0001c2a0f0074013030002c5000030340602c18143d4030817407510440d01802c2d920f442d640c0c0c075510306003019a00801c000041c0032038a9407000c0d044e04180c0b8642055052521140c0c2c5120b80350354034010085081c103041e24400400d82c0e0300d804803154500c032035101c14800c607251003165494040c1100c02501203540144120900315949607070f41080f5030040c021000135500c0344c0013213408403401ca00e0320003810001c1008081d00e880c20b1280342d01034102c03235004144041c1c80b403159005100e0707422041445021000100014210300100310b5840c000d542c40d01603180d480368411086c0500888541012035400450082201410326400250b01e01042c0c4c1e0301c100c0d2098102010f00703a010a850b4600e01900417411500250400340101011054180400508030440011403801c5414120104a810f42c8030500382e410b160f8903004000c030100080755111f02e450318582c0c0d4500080d46910505000c4900c8002504c402d03030048402000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 106404964 1250 106403714 106403719
    0x80903100e010e06060a0f0902030705071406040b010b0403210e0a03030201020d050a02090d03030b030304050d0c0e010906050a06140d020d1e1109040b03010e0312010807090b0604030308070e 84
    0x420140380501c1e01800046001d203501c0e200b4800055000d14206008004617030400c21040742c0141001c0101019500081620701403242c20801000040c145183c440b10003004000904440d06003441c260061700b206034000f00c0c3c52042031005101081c120117104660031034260040858541ca510f05a40101040b042030382d0041c0208000000d158064009000c0ba1691800801035950f07118460006c03070003284d1030f10390040c2e0365800c0100041c1c020341c404007507400020226400c19550304c5c002050000c1c025012911107070319030f104000a070540300c4658050550107100380056800c02d00828034441840c40f92004125140114003070101e01c000440c0c15100201d02c041d541d51038584004005450803528081034510307031090320b039030760240c5100300300c0e03008102c070100c903e049000c00811000d82010099580d055507600030310728600d00e00700018440c440e03801100642c2c540c5050703130450503c080c81e80001c2005050000e0400c165a600c4200d90540340e140c00c0040203a150301004a0300f900300c4411098 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 106406214 1250 106404964 106404971
    0x6150322050a0c241704020405062407050f06130201080a0e0d030b1e150906160b060907080403050306090c092101061a09040e0f0a0308060a15020a08090310 69
    0x507144922404022810b81c20880311900e030641035070105d030140100100300075540c801a01040062034a40c01864200c840103200c0440180100c2207001d1071080e5038031f940747c0031400041503410041c0a1003245c50801c815401b6107503a161550a01c50103402d880c100031b04000e516000074000741d0310f030784c0b005620102a02c22a034011030a940090014292a004680f140b56001c40c2800404220114409a200f003d40340082c5070b804542121240e401182509a120000780321122003043c01944122805001c0d02c046400da00344402803005589001c1c007824108841d01c0c04000210f6009811660131510942e4100101d50764500b41c2d400c5406180b5040c0c0e8402c5c070407110007090642544014544806180c0200402c2c0c0d56150603800308603500b020b070fa044080c14429101d55280660109901d030388102c0c00d403002400c01c03500160600261007001c0300072904200510075141040c80500002c1c0101403c43c0a0003900240041e554078990000104807500021720ba020b42d071020b00420119900c01c04062 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 106407464 1250 106406214 106406219
    0x50103050109170a021b01020c12031209071208160609030c020916020703151404030507050c090c12090c060a0203041505040b0d05100e0a020306150322050a0c 70
    0x158003030801c411041d114800035840452903000840e00310b498807100c5400400c0038030300c4c40c0f214406d200da1005000341940a1060070b25080e48076545005110280c40c00607560390150904244181e08000e000850300ea40561010300c54418140b40c02c06486800402850310b90f02c0f0704603004070807030900c20700a201c0703820030401e60b00300b5800c4110001c0070b901c22151100d4179910712401c0c0c003101c01c0610030240103910a1000300701060302240f400507044828800421f01402c40014400307042c00c15901200090400107840c402e00405211a05c0c02d0310088501401d28101180b0700d414900421852010700c1d40700c0000301d215880208540207603c2c8018165a07100c224004001e9243e400c603100e0049100c000e8042032001c0c500c1001200d081e114a40c1499050041010782e102c01408000c00d0310001020f0728201081030404100401e10070741c0424409640c070301d040c03000d02039000102503038401d0044040c0107100c4541c161500c2c420340c064000d104840e11848038100613280c0142c0350303000b03040300c0d6580d10003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 106408714 1250 106407464 106407473
    0xd030e580b060103050c090109031e06140709140a030b090a060615180b0f18030604060b01021501030209060f03030d02030a0617030901052a07080c031b09151201050103 74
    0x2154461002624201701d240c1e01c02d10055443d1054916442c00190280d0050000403610028400b13610840d0340040040d80407561181c1c1205c4818101000d01c1504100704a507569000500c0d03400b912100c1d1680801a1409001c6900310026020042070280c0c80000181020300401410400d01d400440a2020990720112010340039100c00f40d480c0090b0701e00f01c0d48003d00003030034030410454040750b804030b1900c1044041c00d02c064000c904a4070718440d8002c04486c999a0400c43c1c3d502403401420002400c1d85c0100c0064a40b031010f16000002c591003070010000341c0d55103141c0681c05081502c1c0d10711450403c5002a05612492810000c45440030041c040d590200d5444141650051262400d110b5500d000070356a80c0501c1c1e42c103d00050b0704014405202c444222035903400501c22070443c907080c981141c51801c00d900354104d00342e0340c0d03c148441c908514041221044083c0460250150000d00a0102d0041c1d0340082800f0404011160b08526076294600c0001c4c1c212100402040607584030301e003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 106409964 1250 106408714 106408733
    0xf090b010b0901200601060e0a0e0106021f0c020a060b031002030411030d021b04091719030507090f090b03070308030a050402010924030b010207050d030e58 69
    0x40742c50028540c000ca030b80c800550903504201a4101c813004180c50f0303180800840d102540328903225003000303c5903400a00c0344c03908400240a000319401500307825851100c0c44090002c100540300d200c500f00050110010340105030384041c507030004404601000240007003494030000ca500340d250548000108420300c00000c40d021440c4108030103070785000e91003040813641d80d00d5400c054444001c20700b9071540c140c0350680c46464618801c0b00c41a90006521085c0000c540003240003a90702c039081c8800e0721090703501d841580d5000f001030034810681401c142c0381040b0420580036a608088d61040107100554080156500035a4489000395803803520250401c0034240c10b1700d040b40852174040c4046400704044140d03204a440d09070258198505124045014090700d054a5065008586d0045181c0d02c8070580800c0c00c038020386402c02082c0b20001803190b8241ca494800c0c0b00d0915030502d0000d801055800c800c004511800e00003060b82c481d14030400c1031070f40c120360b070003408045143c2c0e14108031043c030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 106411214 1250 106409964 106409977
    0x70b16030e07090b1c03090b0c010902041a090601030608030d09060f0203160206090111030f04030c0501020c0d1b0203060f07030b0a0e0702010b01030b09011526040b09011e0f090b010b 81
    0x1503000f1700d004c00844481d040b03034103815002004502c00361010b01220400c14080c1021010542c00420310700300740c2c1c0200d4110344003841580302c0e8515202003856282882c0c100150820428a0104011840c28034029124004c1c41c0c5000740d802e071030b40340210038002540c00200c1c02859002c001c55480c00e02031000550449500044030140c05000002881100c061081461680c1d481d0312051466891001c000303002d80d4000c0c4120300340722109002c4d002080f001d02c05040c50202c1000242004c1d0000ca001030f0000b00901e80111170031851062500c010b03103002c01c02c0d54012070f031081c3e10042070300c500c407082c0c1c098011800e046030042134510700001c00042c2c44074640d009040e02d400810405a04070011400d40d400c210259412034034860041008402843d254804409070b480d0250342c0b00d121102e1254407010070801e5080042100042c030051002120040c0d42102108000f006040c0c00d089040c00b000c00261398038915903660f00703c1100c4c00030f104e400440c01c0c2c42c1e10100b080c40c15a11286080e010b1341000e03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 106412464 1250 106411214 106411219
    0xb0301060b0a080a0b01020705010507050f01050103030e18011d060d050d0504030b0f040c06050a260105010801050904030206040f020d061e0f020702030304030b0c072001020111070b16030e07090b 86
    0xc602141c03004e0528031801c0c01c0180c06038041c0200c1400d080040d00c1541c02598215000c1c0300e0380c4000c4a044100303202d00d07406903109a0741d41e1032154240040011400008448900e845804e00042200840c005081d4280d440704401220301d1381e880c000050030712011070303801410f14000c00850070102d030317440401481a20702c41c001c04245034440120020035041e04030b40c0140403044102083c07191a01032001b401d498891072905e0090703070151000c407116a41460042c00f141c2c1c5d50040041c0804c0da00301d04101c2c00340c1000c2d035401c21140f0349900c00a548103c040c00c064002c54400d0288030954135220750180380190480410322848004010500301d000c0d0248010351258a00441c55103010540d0003140e04194008000354101420f41d1503801075072101400b5100b00000410a00001405491402040706052000c944481d808071002900350742112100620070703030080041c1c070005030306000c005402403101c8540074201c4070f203074906038003e0011800348042440381900004250045800550b20035405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 106413714 1250 106412464 106412477
    0xd050304050d0515150d0605090705040207111206190f0230060603090a1104180302030a2a03050304020f06031609050604062001060f06121407120f0b0301060b0a 71
    0x401038440c40510010f01039946c000510941c01004c50400d400c4507030420040381c1524070050381c2c0d0300050304907440f079003040b60040d05440006132107260000420010386031510283c07420380307006000d078586c905100000038050b65980380d140600d80b11950540b0701c02100c0c04c404040b0f951000300ba201201401d4401c100c808d846660006100703081000c1500e000d072105800600c2000c41c81c3d508d114629042c2506160010b03038814400c903c0225881503e0790f1503000f50050340d0b0f1002000c030b00402c24092424000004240c0c400e400302400400c0310031221058040c60225182c0e03c80344001f4507071580c50310030305030f0200c0040240f101d0349802c110903c40f51505500d450310019030b02d109200c2d49010300c0c440d90300412400800310712840000c1000c070b80e40030f0038400002002a05c401803045100c00603081000094107810080e4040e100d6131180b613403010220b80d00482503180011005080354260a0312035071154a803588030380404090741001c0d041002c020300a02040380c42d891200900d410040742c41d000a0030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 106414964 1250 106413714 106413721
    0x405030c0d0203100b030f0709020403050f07030309030f0302030d1401051c0804030303050414030403060f0621020609040e060f0a1b020c060a120507020106030c0518060d050304050d0515 82
    0x745000c500031565406000342c8031306070800051000515521800ca90140648115650408070030310500b0068504490b0040c0c40d507085081c0b0742e1414682888090107503016010034404285c00601003412207038841e03d40301c4400035500d0b00324254014124070102550522000000c2c0050111440c0e050382c078203444640e0310040c401c10007140804506806408018104000d04c04203200b508103540c464015003a0104a414000066145601039481601c81d26600c0b500030f0342c0602e250050400500e40752015a08074605c03221060990f14400304000c1c81800001403030074854840b6040b00001d408050240c03441031400e1001c030340d00c00c4000c489244000f0b140c849000c038003002446860308080903a500034074180b81090144880c80e0b21001e00082841b0040079401800c900c18011035210300883e600104d4610314500d003a90001c03096800c00c0d0300c2100c03540407001646400c0c02100e9400101140c01030104942030030701c0c60031441603400507900440401e0902080c40070020f2019600c24030510b609200b6503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 106416214 1250 106414964 106414969
    0x203010b01180306020306010207030b040804060305010509060105180a080f060f070804050a06050c091c03082409040f17040611010606050301050d020f0a1401031506051c0603170405030c 82
    0x1004075041a42c10340c10043c40802e076507034051544044180125500184c583c0c840303621884040320101d8844500160038058668940241c80c0140000c3e5070239a40d50a02d800040e04a005060003a9401070741448042c08640c0d650b00b1180080004c0019200400880c1c10400d880749800c4030a01c0d102050781011540751403041d55002e2056070054040e100c03c6001381d50352009000c016012084040023440058a1685c034418900701031210f10310159907801032464054840d6000070a17516081c01d0040080b20b40501100602c09103034801c54140361660f8403460070102459250101804409014101404412400d001007090321015210040c0c001a641d08050a8820a00480700005c40a00041080342421140d020031107100601c0c0d0150301c4182c101007a01c3c3c403d0340c1c0c800092041c40c150600a01d5170944a2207006955114181808500301031024005c0d00c1031141540c10ba0b540d0030712401d0424003541c0528007441e031019011812a441440b000800c0c1c1140c001c0c18868000c45030384003d02e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 106417464 1250 106416214 106416227
    0x18040b1906172512020310140d020f0d0804090f1d0712081804050901020a030f0506030604020909211918090b060c030403080c010606091827030c0203010b01 69
    0x40301145040109155401c1101034421241c24402c414024125140c461004242c0091440b40c4000c1e00e6000380d0314030341488c00c004500400a0f59014041c100c840d440980c607140305000d49020242c94450030b0038900c4c50401d4162080d6800041224501003500480b0700d0b43d50046411b503520340ca010002030011005554650400d449800c0001400404440c00a002003001d466202655809080c851510502003010f0355000c44285045940c0003c500032030700d03054031610884401800003088a2700e0240041b0b661640d0241c0003a100d0a0980c00060b03010504000d5401e0300c1c4200401c000705000803040841d00b44c0c01c10340040007081c400a000c64100c600c916048440080c428222980283c540303400007004040012406802840c100401d50025208100400040d40b03d8004d20f80d0301e1400510f86801c5030340703e4101740c04100c00900e0070050149202a4411141c403807500000c0d10103421543d202c540c0100d945185a2034070340840039400c2c0f40c0c012242c18a100c0c0247c0081c4014002e920044969 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 106418714 1250 106417464 106417471
    0x120f010b100503070c060b1318060c05090303031b070507080d09091a01120b03120306041b0f03020906070c06020d1e09260307080c070b04060518040b190617 69
    0x207450814000f010614035040012007c0d400307405885204841790555003a6604a010342d005007a096005c1000c102c041e11910307142c25240d02d801401e002800c0002510ba00c0090040700104641c1080d081100d0341d036100702c8110135801320807503a48540d030342038058680305031400d2100801c4409030001031100040c0200b42c07403500842c07001c000c0d5140303201c0190b0305030800300740000f66150750300c41e00d03015600c3c10400210101e955444860b141c0c80c145041000765070740900c0d0421000f0151721111007641e000708214092402d14100980c80c7c6403a070021030711034056508060064121404001083d0341c01142401401c40f003a501c40028001c687c5d5818007644072607050000003507000004000340035030405241903e544d00e003d14800c101d0504509071558002d09010b440111000881400d82c80381001143d00a0103d50744240c2040c1c5020400303030540c026194074480308200b00d0100400c903680d55000c0444010010a1459903c1403070100d6150016035001d0440421801d182070a600d0000d000d440b4031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 106419964 1250 106418714 106418717
    0x200904230c0105160507050603090705090109020f03130809030a08040306142404020c03030108010606020d0c1a04140f06090f06040b04030f020f010e01021207051e0306120f010b10050307 82
    0x5072903081c0404041e201136a10003039401d40141c0350007240c0c2d175466400650003000c140c4c00505a1605001c100040003106a011546040c4100070012030030311400c0a0301c0c1d0046a60f607000c200f41d1020306044000d4400c14100f41d505000d854455420030901001803c00d480c05903508106a42a2180103807000d0815030312800d00003a19050305503c50208441902c8260020b080982008140d48031580365810a030071a6a4594458a05200203507040010700c10703181e00c80c604200c20904503100d408004000407416a50884590700103001e0010440041c4010a01c02d01110b001c036403022145501c840d001d40390001640203802090744001c40004184d4003454101d469142292541e030b80a031071f4280b2096201081d8061032a04115181c001e10a481000c8030701400940d0b1040b20401080d00700c0350040124081c0101400342203444200040e840180070460400c107541d903110f10000582c01c40121600046510401c3c0440041c0e04040d005a080e5403002e50f41c140e0050ba40c12003e44aa0204440840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 106421214 1250 106419964 106419967
    0xa060b12060f01050c060f01050f01180501050a030908030f060a050f130b04060e01030803010f0902040602031c06090c03020408010605090403170a23040c0906080a200904230c0105 79
    0x21024a80380300e68000c10310050401500c0c04440140540c182082241c0a1074000d0307c0380010485414074000301c0640c010240303800b8841c111807130340401300c1410320300510741048000708083c6440790180c0e1004020503040112a0344034030345580031902038a0f0407201c007800348040000001e070354204441c0c10030494500820349641c1600d58042c100c001c2010600d17141d8070076181c200004421003c50b10b61406940585400e6540e98144a40071000d910381c0c0c1c0c460404148100030410503203a010050744c055603100010a51403884450111010704407a802c20307900d0038940b0f80403404043d0564014400c5604e201d0080c8800381d80d030410480c6c12141190f014020030000d06255050b0420307080c016030301c00744010300000d45a40c0d03a4103003402e40c0c0015858514900468040c001031100c5d40c0900d00040c0b000d0002800128100101ca03a250a43c40000401c0701c49140540064085c2c0d80136100b4009501510f425002c0c90a401d01c00160030b0000a100e040f101d040010020140e4003061801074900103841d5a07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 106422464 1250 106421214 106421221
    0x40504050408041d0103060e070e0117120301060903020102240f22060e100e07060f030605060a020c09010e01050a031103010b10020d110309030a1419050102030a060b12 74
    0x100140000a0003142c03403110820000c524107072204944070f110700b50400c00c0f244030360440c58203804882218107074509076440400104400c403041c0440c00e066071078a2441036815011002060300e09440e81060f440c900e1404800410803d07406400b00e41140e000342c0c200e034448907512819100d03c0c008403009904085056000070480201d090043e90401719103000f0452015048001c5440001c010b00201c803000e44448100009a0003040004030142405404120100408001a5481107240700315800c0c05420300c103e5080c80d00a0b4811401001c024120a41d03030110004020b44408040350f1080c0f04100860001c0f400e4801144501d050b24409001005901e065445d00d101c1d03a01a00c07040d503410764031010080c0d06903d45028008108205400400360000d08a03409031548580c04410441940148141d8126a03000503079809255000300303000300c40042e5403e45c541400d4100701c0b101441c00180f0205010810154000c0d845200b000000304181521040307120510721409265001405030312010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 106423714 1250 106422464 106422469
    0x4120309210302070201030f15060305070504171606021501050d0f1a040506011202130510050a0b1e0306010e0411090a0b0c010f0c08010e13210f0f02030405 69
    0x1585010740200580034180400c8038041c20100110404540083d40205002c800c6507094000c038481d0f0743e03503081d0511900000c1c1107410760011031840355608040d01c4002007006036002c0d0007103030090100d408100410b0f4010703042c4540c1d101d03643c0c001010129009180058114404500b00d604080d01441c0032085d6442e00c0100588198500c0c2d0541e100d001c01002000021b86545c40d020000301466041d0380f007841d09042c820f0404170305070311250b80100c040d2131040c0145c2e03c19605241301d01d0000e130000b49607250a0100d1007100c0080c0c000e40e0f0401c0002c0d001080c460421000781c4a0b10243c3c01030400802075a01c0304950601017940c8481c00720340542000c0100745400c3d0400181e588100d414942840921000100700f5442030b48401c041e0500060080d56001080c0191885030b100840c0601c1000114040101190030510450740b000446c0404259221070074440074000d43e03000004003a989001c4c180d56551803040b14042c01c0070911a64208800d00d010b440c00800c40815a0051420245010306 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 106424964 1250 106423714 106423721
    0xe0d080615070c1706090d080c07230102030c03090f12090907180b091201050103030c12020a020904111924050705010c05071b12030e01030b03010c0206060f0405041203 74
    0x403c9030b1400307001c48003140e682034045613a144240501c000381040e0401240481c10b100300801001c2c00c110b450010044004007010460f9032042c5e200500402450040288080901c2500d03c204950350001003030080045800e009140180624000d81d10b460b80820142d41d55662085009168060f06109440320742c900100c0d00740d03200360b040c2440c1002d1440b442c0c5000c0521400d40001c88145000b155030401d078181041600c0501100030000c22040d41540c41c0074091541c240c0e0014001c60360294600b080610a10500b18115405030541851f414203180007800d40380c0000905000300c00010b02c00303102601144008040b682c0345203400010b95a12138050023501d022042135020301030708020340c00016009101e02d10800c0c006d56601500e41e110391402c1e1062441c90030101800414981003442080400c885e540c040075030608100101414150042e4003620410700d4080c2d055207041f141803001600840c5940c451075040310114042a180d80401040f40c0055801909030580c940c1c4180700d05000740d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 106426214 1250 106424964 106424977
    0x2090301020d0c090f090e030328090807110103180b063f030f040e1009090c060e0d080d11070804030812010609151817010e0d080615 59
    0x40026152181901407002a43c01040300350700004c00c0d003c02044020b42c11017080c2c01a20032001c0038070103000d020b0000d507601e002c090414020303e01407404e05810401c07086001e03c0e040020803410f00100b00e050504494942040c5820307140b404840649152035131291061401b603032000507075100d512100d038540c074810000041880750810a403a42c030084141000b4185541c0e00c0301c0218500c03c1c044525403205160614508243d00f6a006221b92406180c6074803d40c0c0c1600d503c0d040044040da00c0500507110100c203a441050114509402c103014440c18070702040656074185c455621082c03100c000c0c000b2014440401500c45e401c00d016002c4400169000003080310401e203002804c29101da00c4140d5035600c90342c0100c6041c0130000300241d01c0501031030340a00404060800440d11440e00c40c954582e091a6110001040303000c5805500c1031144882c8a000b419540c0b1881c003566500c44c0d40603000f0070448141b04107902c03911403040381d000d101c0c41144c0e102c0c401c00b42c00d440038501d40c1540c02d120744d0000c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 106427464 1250 106426214 106426219
    0xc0203010605041404060b120d1d0409050307060507211508030c0607020f031903020309010609020a0f080a060506040e0a0b0d0606030b0610020c120307120302070b0c0313060209 78
    0x80780c00054580e40c07030040c0f5401107442526a003060a0a1401804031584005801d006a00c503025044040001180d8244100302a00f80030905484900b61650348441e1855155409403909400030305200001000c0c204003446420200055140d4104c16642d1001201c194000760b5205450b000100740036030090411a03111042c084a019180c044590540d0007410100d4503640c05601004550382c0c1c1003111150a28898000d54584030082040103002e0300c5104644043c950000040b40c0703003050035442503000f0a1440c0d4119147e0340e82c05001080d02c3c0030802d03050001501f64021501c5901103104a004031000103103000e14151500c051040341040007440640403030366803c5009080d48034040c2420103544640400201c8e54150302c2d000240203006000a030141c240f8040c418801600051309480000c802c40d51081034101c2040340518510910300001c09214480c410116801d4040d006049041c1c0700300c0403c0310b56520810000c02601044460040c410782c48890340b000f0070001c0d07004200041c0007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 106428714 1250 106427464 106427471
    0x41d160807141302071a070503040206090906190611010605010219020904150911040c031b03050c07050102040b03070206090a05100c0908031204060506040c080402060912060705040306150302030d0c020301 90
    0x26140800c9801103c01901c228495034111307000300c00301c1c0846a502c00387d01d0400609605140c0c002c529940200f10055016946120200c1c8003070380c4511882154103c94030280020300d4690340d004000d00480c3c1d52240d155800c204001c0380540c0003142c40c4040d010080301c070b0010707001c80e80c08110340c101000d4404d4600c9900c101d11460500c07214010070546500900748509402d12440030301c4102c0e00c0d00091720040514140c80b28100f12800020180c00300c0300c07854046003641b10710381d0b22482881261300041080d80b00240005040c441c28016500ca2003403a02600e00790b903510304820342c071806420b000a1560700888103e00c50554030b41d21029010040703180c82d64265444005140c0380d036012240541142e0120001c1104105840c069590f201c08241e6003030114040c2c0340800b0b843e004003d40001e2091802080e802019203403185180ea02d640564103c41b4141000b2401401c2d07a8020300041d91210b080c140241d01d50380720100210206da0340030f40201280308840c0d904840c81007660350100e074503548 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 106429964 1250 106428714 106428739
    0x50112022104060b0102120f03060d030905030102070b0604200a0f0c0c17161208070602090603010f0614070804062001020c01020901170115050304030c02041d16080714 74
    0x901c11681c4aa0720600340024840030b0000003a14040c852000800c02da10100280079404881ca425260400d0050b40c00070031080b01407506503805401038021941540c030207c1c45000380302444414500442e01920f00300801d0170002c90140301d004d0307a45140261100700300a2280315034881e0340d150700c40d0202403805000e002813039581e09000700fa00c2d5100b800b80303016010f01c01180100a00c21541003000304058519542d03d006010008400c00c110058181d030004140801800207540455424800080001c0c2d42c070360f1182603411084919000b41800240c084034200d41c509116411184015040403071141064600a811552481c410000c59114421462002017187e405d00240580100c41c40004d41c440d40e03484001082440090040c00c902c10000004006186a0074640722403905c40345440c0d9600d54079070400345c40720880608000d40041ca00340b10b401c19060700c2103080318a03030149000d6550039100c035084090320f01c1090003144551b40100078100030300c08880c0f04282c00c100b8003034240c000c07803003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 106431214 1250 106429964 106430017
    0x1c0c02031507020607020a0309050423130b011703090913020301051801110f030f0711060702070e09030702030c0907031e050403030c080c040b030c04080d030905011505011202 77
    0x103075451200e40d14401c05000d0042003a0103000640d4040203500c014200e01c503440e213009009426610425000d030703a440503142d020985000e16041031043c444040007060170110340c00c0800100c01c040c25241001440004221264092607004440c18800000c1d410203144104100700074031302524104002c0e4514920034010b031000c0c0070b5030f44605460301513130340c407181c41d070b466142034480c03400369061011000c229001c1d0018132441601d03000324604000005655030312500b1741c1e12400030103240d4210701c2544100989a03500117105c0e0103890b8071102d036584135113035071542d03070b0ba00c2c001c4010096040c3c01210082001342040005d007948080580f5012903403010303417070755012481100e280800c01f242e10b81c004c100034550107006070802071481d131070316000340d00d00001c2d01100c501690203207050284001010519250001090701c02500c030120681c2d21009a40d0006001071000201c01c03903842d42800d4049491800e90802c00048072410f8584880072282c01c001074009500101e0786078001f607107200c820740340312 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 106432464 1250 106431214 106431223
    0x302030d080604050709050d110609130605030115050306041101180801091703040308130201051b0d14091302070c0e0408070c08060105010f0e012a0209060406030201021c0c0203 78
    0x80034503485152030782c140300701400140d0300c000300500140b1010381801c10090b22240030340d103d0300742c00c10340503013444901c1e5002518900ca0340303007080ea00001c002e0460b40b90b5910f59000e031088500480082000c40560103d81203030103101d100e41c03a419000000060042000c8854000c00400145400f00c8c000805500b04003c0390803075004255681c0d501c000140402255502090351140d500e5081803d43c542590010003914004001090204140080e0b400316401402074859500c01c412041020050010f00c0f035940784140704c0b03440001031250400107019550340d81160804000078011128200e00e580700c40000c2e501c030380403c503110a0425030010b1030748d144041141c06a40319660099440b042410040d2000c0b82a801c04401a000000100aa070303070040741c4d08005140328104801c0150203c40184d07103d008146514040d0310000302c1d102c1e02c2c40c406018042d50140f0844080030181c4690050204455490000901680c803406d03541c0203403400c03038100f282d450031039191001500718158086801c6c0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 106433714 1250 106432464 106432483
    0x2030c09090a06050105030303090a021c050a03030b0118241e0206010608071704020f010210050106020705010f030501050904030c0c15050d0c230a0306080a140f150606030a0204030203 81
    0x102d03044003652404109840c0512801000c007240214110300309000301715202d40c001c04000344218540b03030300c40380c40703c11443e500c002441c1c0020507900e10700d480341000f80140c44010a801c0c00980700d0340c80c1e00750191010303404e00142d803c04e10800103013500044581c00000388041c1c410081c0807501010401800c0002460030071a095a40503005a5140040280c0041d01c060406000d00c00f8440c0c0c1c1600ca004211300483e0f00c0380c0c0481d8880c20180c070900041c2c0c204504107040303070710590400c0008125142c00203041401c0711400c1e42c4a410360070400d8002c408450b802c0c0181e0364080059004078000c244a4a903aa070641d005003d09606666a11360303c0000b100b200c0c5012000c11408900c00e030030842a8411401c0143c00e41c1011880c1c441d1403548401001c1019030904104000820529031a610903400800541502c0e02100e11800490802100300c150f2901168440d00c101041c89284802c0822a00c8403500700c4400b1030f0230f5485a804026841e000103060b5000e0980c02d20000015940401c006c401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 106434964 1250 106433714 106433731
    0xf030b0307081b150a140d021b0607020a05060a0506031c0e010e0d0f0b0405070f0303020a121404060f020a02090109090b15010c140106260106050a03110d02030c09 72
    0x2803a40358030301c840704460b1001d00428070030307207041e1030001413481c0942c1100e00012072864016520580304124100601034918a80d04407803002c920b40034800c0462540070301c181300100071140c00e665003c00403a51000c92550081283d00644003243c0b000700c407a00000e41004005013611024801c115000032104204070902c0d001400c04403005005580003a100d64000605481c6070901508075150b28039407260100c40102401e500100080034002e06004002c0503012080340c0c803a590b962420006e56038640751038186c80e9464003041e40c1c00641c1c01070043e00011020003c84a04040c503002d0191040320303254200ea03055000d91881440182d40f0411601d010b02002e9000060108240c1000c0d440c64500400010001c200e0300c98081c040d80c0c00000545242c0c0c0d11005a080b10b003040c2c3c000e107004d40403d6008181030103560001c4908003030030004141456100b00002c0055a0746c54040000d00f079600e11019108007a201c0d8441010704080d042c8011341030005c0c007201c1c081d01002c0c2c00304034881d034202e41148 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 106436214 1250 106434964 106434973
    0x1b020d18030605240a051503040c0b04060207090506090108070308070507090c08071116050618030304090905060f01031106031509010305071a07171606050f06090705070b070f030b030708 82
    0x10455800f01c0c604c00c102c1c0341c0c00c0d226403030120704042c08540c0c5840002c0d51002a000e001c00081c04001002c02c114014011a006050319142c0e10381010799520307510300884110741e00380000106181801d0320b2650407604803070001c248561071501c420801364481d070000e58950207140d40c00700d2452103600407100c034841181e4500065203030082c1c000384900ac0c1c0412603c116000101400c0e04401407691b80c6054840841c0e0f0a80d0300c180d50003403092a403a00c525669014000428006a0300405a00034481e00740260240c92156440c040c100030084401d010081c14001030001039a25814080065903114401c2c0d01c84561300124400001e1007003100340d1041302e0300c0d848088184602495810030500341d01a1940c5142001401d90f15207244108138607105e5856000840d8000c07403000a01032806c1a03c0d004081001641003101e04020219011120140142e00700004205118412000c9078803a40e00090ba41010340c8a020049400344180c2c0c500200301925a0910b8a9955040c01030200a095080060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 106437464 1250 106436214 106436251
    0x115060e010c050c040510240305100e0109020304111c21140931150e0601200d1706040203010503071e030f12031b020d18030605 57
    0x24103144a520846041110100850000a500040800080d60b0413180030030180c0d40d45030342a001000395404032035141c104c00103914070003034240400c9007081c000380c1c3c0c144515900c00702e0502040340c1c0ca2085c0443c14402c5001001120400c0d809943c225100d6640f14801541c1c9400050b400c0001c044603403480c0074550f00c00d03010030900a40e507510007080030104003100c40400030094079049102d0395003981c1800002e1001c0d82c0b03948400c41506030103240d0311106410760b041e40c01c0cac455901030100c20502803440d080007020703007942c03810a240482e043d05c50011001e5a0341001101c1c071f404020321070b0a403e9441403040a01d92001e01600150101030f0351000304030486c9440013012400054040c0c1d01403441000180300544002c5140c030160b0314114403c41504400448504401e05540d00180c01c1c194031074800010069032080d201c0f00140d0300d503810301c03840c00c5001280240c01c490307402400159101468001c5441d015944440514600f9500000718540c1d98403000c2c01d803031086440e42024824403244 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 106438714 1250 106437464 106437467
    0x30403021b030c01020c011211041215020304080d2c01090b010905010302060702012003031005030d03060b0313020402040509090706020609030c15060402160b1005011d0405090f011506 81
    0xa6501e0301d0100c004003039500300c40300040e441d0b0100502d43d0707041010b681d64090030000e05800400070700f000034200c956201e5031207140e41003150940b0800c40382c11004000a0b243d10ba42802a640140d4021059500c5c04013450f940d400208150b803401309441c81e80002c0c204441070081214900a68401e002064900491a04025002d0142c1140150b985480018005038841e581950015942800c111207104c0c0c890702c1d4142e0800f8512002041c0e40300c00400c121005446280000480d081607044400044002030b041d03055038403500800c20100028000600400c040180d6209242d0010b40300525081e01c071004910000d00071a02c10602e903004c0901008a160304004407a0702c91070740da0103582042e15000c40c1a445040e12070074030070404a0000030484c1c50740d0740d42c12121643d5400e003803c80c408500303240a0781314200c211468610780710a51000070b800d50240340a0034500c22050b2010b582400380004000080c80c1c050910f080c188620301160f035006400344110039101e01045108035445250040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 106439964 1250 106438714 106438753
    0x702070f120f0339121d04020d0b09010306020304021503040314071109090105010602010e0a02150703030605090933060d080f040605090310020a02031204080403060203040302 77
    0x88000446100001c901107541c0e02441c141c1240e01d0726000181c201c201c41010b640d0f4004da070302c048940c2440c244c190b507001e821460b0180002d214001c065a004482c2100351040c070400ea4108452011510040c1440e00d410790050440d6406600000740c0181c0c501e000c104074002c240c004030341d2a07900000348010341c50450181c54010070049440342c6146005d03500186150b1580c801c0d5072004402207400b5007081413138844054069005411404c0300e20300601040e003c2d01d003e104110255103004c8a094080c00003103400d10030b60350050500010301c2804501754809500c036003015410150782d6031002c036490b074550860034000d0789414002c7c89690707030b6190b01058444102e80c2c141c6d980b141c80315031740000c24035101c20b00c0d030700900c103d802c07031119421401c1c07440c0a4868982500c1c407200002401184084e0420041c04074104150110790405c0c0c40c3d02c2c030b2314080384184200440568014040b0403094080501410fa100b407040d0b090f207080507925607588090b46c00a403812405038000d01e100c640c4032540d42c1c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 106441214 1250 106439964 106439969
    0x80636240601020703080d020702060d050a0608010605010219060b040908040608010b16080304050f120406090807030201140d020d021803010f050114041802030607030501032a06081e0702070f 84
    0x185034454140040040c0d502e100380e10000f4107544000c00c0342020001e00d981560166600a0841c56480c1303a29180d500003003d04903522001513151500c0400da0759414032071001900c0c010f8009010410b0740644200c0b8103000a00210399040c0c840c400440340d0780301d60185580e40c6100d84000c2e40c68038285038000d020010140c102c0c82d8401014800415544030385e01243d00040e4106100b80e82c0c0c1c1d201d60801600b455400342d29040c01c6d201c3ca04d060712100391440c000b041150815504c00704500e031103d03206500c1b0b80e007a200180c0081d8100400b080c2e41d202410080c10308403502c0d4801403030015080c0c001c0307045c4c2e00450300d0700c40041951031100445040a003c0e5149000035048100b1456040c41c03070380c228500d803540005015580c1c40c2c4801c0620014007880c560403540090032503126160060000b40a030070240800c0350005a500c0f0401d10300d8180d02040400180443c0d500d0a102c0e0801e0001c440411004110b061760a10030600c2d00ca2407003030f10324050701600e006e50151820f10b00340360946010304d2955 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 106442464 1250 106441214 106441273
    0x1c050a0b1006020f10020a030b0d031d0609060307030213031703010f0509091f060e0c0a02010b061201050f0f0d03090503060603160302131e0902010e010801080636 72
    0xd0109404c401e07008540c20b005076020000060329000c509008500920310a194150420445007120741030680082484c440f1406445207000160350800600400c1e00646240742e030456010302c00300785070714066005440e1080300c1c0151410301c00e960307842e0281390301494440ca04100710000010300a6400815081000e0702c0d05840300d0f14203050105442d0344d200d008450f000c9500c103800c0005041740c20725400c200000c00b100b0402e25000c1c109548003032544d60200341404050b40c038042800c6400e040c020180c3c1c0e083c4003000314200c0d4503841c000c240710140210342c1d19641d0200701d20200c82043d030b40c4d503850b603150380c0c0c041d9542421850810b41414901800580240d2003035202e156012035000c001c00c940003d407a4152503280c0c881a414048001502103880d84c4c26500502c168900034091055202d070414030b000f681c42c0c11690038400d0054480c11400e000b000c110b500500f00048481306078420300720320480c4507040041418010841030482007080b1141c40b81070f410400903111030000290110403a081039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 106443714 1250 106442464 106442473
    0x309010507110a02040522030201021308010b010903060209010311180f03070506040b0f041703070605100f0302041d0d18080d0e0111010b090406020901080a050106020303061c050a0b100602 83
    0x510311580c0c4503c01c0c0d0000348907036100c000151040c0780802c0040b1402c0c0203074030544100c000c0d40c80c02902039082801054106008508002024201401391505061041e111000141c2c11916108003950000004505050b04c5640240540b080000100410060005d010010500c1c100402c078045111800d000d01c42d9100503401e001c2076a4805c01c031000c8900c202d118a545403621480055240120b0b40400c0b0000710703010b10040018408002001c286c0d129160400459860000303107103140d0f10f01e00a028408246490502c01820a035103c0c405581d84041078020b01d0100d908480d00e003040c00300c82600024603200c491010080c104c81d041d4041c00030040a884980345814004040e00102d0311210f0411034044800301541100390300103000d0303074405001d0052500d01402c28001a500c106801400a40c135080010040d0609100303690589480382d000d145107441d02d004000e00c0810440b41300304400c101854503000181d0400014052074820091102c29150602080b5032080f0b86600a1065410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 106444964 1250 106443714 106443737
    0xa090302040b0f030303070f02070e04031e08100b09130603080c010605060c1b0a0b070308070e0d02010206190b0306100e10030f0f0305070818040e03040e010330050309010507 77
    0x2008000e03a98003918502d82320b00740d51440319007240b50441981c0070780cbc284c20500d405d11007815401030082c4400c500300300c841040011504c00407a40b241c0121000250507083d01014000c00000c5002000203074001460044000301188035001115220b0b44200d581402c0002c8109528000303008400041c0422106103040440c0d01801700d44136003202100310b607003080d00710f240c84890340c5040c11403003d00805000e181d2101010714019090840036100200400c0584000304010719003340400c22560741a80600413903180c681501d0004054080408140ca481c5c0b0310005003601e0401030184600d0115402503081440e1000303041d00700304050052100410b501d03400384040307440942d20981c4c1d1607003d4031000030003490382011291400b880d42c2c000c200c4807001076465041c2e60f00c203000012850040309e042105c1000b41c003a40b80c0d00e200e68442c042e4928580c000400205030074003c441c0840d52040c01c00c59885131214000083d40056030000c00c0462408030600c09655401d118046e071184150134040f04490 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 106446214 1250 106444964 106444969
    0x180b090714070f020103091707021f050a030e030f070302070311090c030f0c090a0909110a0f060e0301060503010c0f0311121306060305060c0a08090606090c070c0b0a090302040b0f 79
    0x2142e4807000e021095080100c200b1a4440d41c0040e99031900710302190824400c0c1040569143c3c4042000c2c1e1140032080040c1e040f0030390000c0d0a40582000d83c03102d515020800505401414617540054881e00042c02200c40c81c9403c030004014080c0b095001e040d266096240404850350b089003408c2c06a103441d410454510342800c00c4a402c03824002501d1000d07510038120101607c5070610064200004560004100c1400e4000c607005070700c00d0740078814205400d0b05200c1910030300e101d107070000c10340c02404201d014022195020840030140000c2107181c4c03502d0220342540c6d04945200001100c034000300c141150300d403140141c400c84c200005450710000945580351004e0103495028001407032200f4004000c1141d0141d40119401003c3d54002e14006001080d00d030018075080010130300340d9001031120707040402c40d58410203004002c180e080c5c95810024842d5008a0022940ca644080380400c00080013005007038880710a945410480d03007507206000c240d4a800790750501802d1108140042e5a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 106447464 1250 106446214 106446217
    0x41205120f0a08090c1801090506101b110a0303020f07080114070e0103090c030c081506100e0607052b051c0e0a0611090109080706020c010f09180b090714 68
    0x220185080d07942ea4a440031580c5c14103800d100f42c0741c0d0003078a44450a0344880025a0300e07040342d410100401039a40d5500921242c0d048252110001030301d412000d1030007142909003441414000c0107840d0b0440045400309680010b1900194051ba1290b08030340f0000380200444c4000e048203000900c180d441d10f60b0000441c82001e400d0702d00340942442e45e80c0c4c1d180d1007a40310b11121038007c0091a400350340c07030810184008450003220054001d00a82030400e05010088601034000545a000c1846c1644422035050390b048030b02552205d010042a00400c10800203190042048940c142d140c0c0d52840d8100a20803d028240043c070505220003030b20000d0b50344410428100c0807002181e003048200205040000201c0010429403800303842201d2484400090015054282c17503640c001921440101d54407482442000300684c015891209254400c42912010421500346601100c1d115011115000000301400e24600d585010401c000e00e80102201d412510074109002c00009041000825 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 106448714 1250 106447464 106447477
    0x130b100e0406020f0c01090c030303050c0418021b030a08010f12051b0103060504140105040e0304050303071b050904110102011a0109170312040b090106080c0f011b08041205120f 78
    0x26070208042035084482c4c0c040314070341c1125000802c00d1030044c0c0780c40c011640300342c00280c1c0041d20703200015801083d080c4c22a0f09403002031200c103803080300640b2080d02075070080d8040d0401500040313010b01110410006031205481d1510740c100251b0500f54007042a40559000c26441650901500040b8801140c10b480f56400783c000900d0840641005038040e0a03075500043e00a45040d00c0141203007407801c0c2035030503100b04640500c0592615401c543e074a00031401099030540040141c40c3c000345103200b150083e0b01c3c1101078400450395a00005901c20003c0b2004d8034a107009035200c070420340c0d0a01c1890307110941d0812004145050000007403464100c2e00440800a80c0c10500c9a84103908005951400d581c0f04088681ca01e0203141a045c0348205880300030705982084000328000b4030208403c1c089110142401001c2c104400044603071541c00c0d403124841c05030002001d8041441480100050200010003648410350380c64041e20340180e181c00e1a121070b5050203c03800b08024001107400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 106449964 1250 106448714 106448723
    0xd0503060f010207181a030d05030f04150f0b1c030e060c1006080d021b0d020105073f020f060c0703050f0d0f0b04050f04150b09130b100e04 62
    0x45140c81d540c01070b4644401a08140d15080c41080c00b10610141900103a030b90b644d0310f04206648010041c00e25580e225182001301c00710720240002440d95040e0f403019070380940184490000540398007107038011144218155843c030754440800302036a061a864981642c240c48a005468480300e17203004000454002545215040008911003103e004201e401c080513140c1c00c08000c61991010807a950361202c050004c0540100d0480b01c02c000000c6000c04090100680011640781c1c0e1940116031a901102044030300c2000702161900488000d400c07184048014440650380904040501180c00040d00c51007086521808039140250310208000c1c0d00070004c1104641c40305011314064905004503403000b03800301d101081040448103190454091204940c40400c408056a0184002d43c1c0044070140c22514643d03010030000b82c030041203000c8010081c41c0000f41c0043c108000b82540206880b021094111202090103011440c000382d80c0295011100c0c04400707240642d140400c04008002a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 106451214 1250 106449964 106449979
    0x703020a02010e07140f01051206010c0f0b0f07081501050d0e1c0c02090a0204050609010f050c07030f11010201090308042d0506040c21020613090203090d110d050306 73
    0x540081c000d402c5005200c90880c1550409911828042000748448049520074075001c0740c4180194003810440c2c61600302400340070060b03600c0d20019260b648010b00221f540029038410100800c2745202410300400000c4884006400c18620080c6241809041c03c0c0d0000c0c09400c08020980c2c00c04101c6d1561000c0300c10210f610301542e102c2c40d06003030f540c00440c00480e41c1040d5220b600c80d840002d400c8ce00c0e2084441118503100c030f2040008a0169004254100c80104102d40c035940c09241d07454801070304c1c1e00e461450521511112801c080d0617510031541804147c1042e8100304015008e04803100081c802040803100c51b4400a20541e0050702c042c0c1003000104800c40e000944804225014054000002c3c4840d29071800c207680e444110380c180c03401c2505210218550600380407610794030007046842401000315408004496000103d0100c042100f00303c001401803280c006144140c07085405440454038040c0050420762084071194441d03003000910300442a006000e8031b0300b018007640d006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 106452464 1250 106451214 106451227
    0x4020f0d182102060c09100818010c030204030302011416080916120618081b070812040609060c0309090203060f0405040501060812070c09020901020a0c09050103030323070302 77
    0x3031804019040024200e2005840c80b05400d25104180004001c0036a00301d650640c0c03804805d0760240a408060342c2e11210401811520501c1000625004040420307600e007040c40c0c00b516036007168103020303621000c240c0118040080c550288210440790f1403100082da1382d482c1c01e801e0301e0080c0c0030141d450b405100d070210100381c103200c081004010400300d0811460f0710f40e440b08405120070001f440304a408504200100303001c00f14401c105070009902110413803c002c041d10281000160b050080c06040c41185000201e14030700f0001d242c0c41c6c01c0074548650341c4c1d070300700207008140354000c0c1c015005100d41c030404900000c0d4080d20000498a14120060322030310303000c00242035090f510101c40d074000d06000c02d1005000c01907100c0e1040791030180031a0180d0341c841c040c00045010340388024110001c0d03003904001130301311500140354540303052064940e1b14500f9038601640440c10f0300700e020f0b0780f5920f900610405030540704280035504400440081c2100303150302da514203140180f48e44101a00403686 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 106453714 1250 106452464 106452491
    0x80307080709030c03031205090c031509151501031409100c050918090c030d0203091212130305010f110702010f0e06160b07050702060d090201090905010806070e04020f0d 75
    0x2000f56030700c040c002d000700d9a2818000c00c03c4038034030042c50a2620b01804100800d00014041e01c00e00b0010300500741c00d903a84a10610075020040040005010301c8100810a541004105106061400d40304224291400c001030072101e80c00d00c010f0711031405106021a4100004070340031001950b032004140403103502821030b5107015042c0c4041c5c000703401c4400d01e40d0408844401601c112440c00456210000d020b0415556148214409000d40c2040007404541c5c20a41e20004408046030200d40e0340044040c1e0b0b144c4142d01504d419a09045c03420001e0003001828042d0310184400d01f0000d110384041380c821031807184103215009046c0500d66a15404140c02124048042c000040c511502d0340b8101b5051241c000e400001101d11a030b0403000900201d0061007640c0a068000d8403046c10110068071100051114400590502050840002e05c03e80140512406040d0f4071010b400302e41002c0e01d001d1306000d845090789200394014800014001828820703203610800085002c144299540310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 106454964 1250 106453714 106453727
    0x3101206090b0c07110301021603030f09020a060c05071d062101050901020901030b0418151b1205060109030b0a022d090a06030501030b040803070203211504020301030803070807 78
    0x7002000340003024104000d01101c40050003d050140d695100e0184403181058201d00ca5460304c0040e0003049034401c408244281d000e4100c03010405400180841250002001d568003980481c0c00200b00486480812a040c0242d83c0188010b0406506a0910380c0300800d841700d00602c8140500c40c00c440e42c603500f051000042030b0300d0b9038143c020886418018030b158040c3d882450a240420308044001c0d0305410715100c0d03050346031b45509501c81d400d2442ea07901c1111860389e07191030544a8540c0141c0759552441d80043da0f5028080e19048803074180c60754944240c0780300810035810300440f4217040001c45c0f40300030201d338001c540580040c0d60312284140010340281c8031803a0b14000c44010146c21002c12900c0080041c10070480d00c2c1d8030b0095039500f00f1801d440d02400001c1103402c002000c540080c04101c080d6030044214010f43c0c7c103103c1801540c03584a03402c13800000c035401d40d10040c0a1014540312003080502c000b6202507141d5815511030398480e00c0041d000c2d40412618500180503c1d11620 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 106456214 1250 106454964 106454981
    0x4050f0f01020a061506110f0709090201050f0a17010902030f0403050d0e030403050a030207080d1e0c02090f04060e0a02010c0b04050a0503071a060103021c09060b0a0909060507020303101206 84
    0x4008101c5c94031445a4000e5901c1640a0040402c001d154000c500c1d075070009045081e001031000410100e824030a0313241c050504984202d05200c400d00c00c074124118500c001e8000b1407403554a90b50407001c5201d0000c20030006034400c0c0141441007061105142001c22419030042c0c16043c03e9580303540b4643c200c6d0050590307564012a900001c18003108001010a801c0507180c0260b0071a00c180e40c0f40c03c10152140b241100c103d012070581415403100002080c40c035a50300306181440c00e60314940d50041500f0400464060450b4002d01c801c220403c200b91059501c03c8c8881001070814407010350010f00840c015200c05007000003458000b50400000300301100c0c3d10f55201c41944d80350400d900d489040c80001d42506894030b0010b1000070300f194860310035244608070b407000c255821944001c0000060a41000607554a9107503020060a91901114500240400c00300040d506c981c9091000c212400a8200400c6400801c10b10950118100c1c418054849203150455000d090307149c203000600011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 106457464 1250 106456214 106456223
    0x7020f0f0f0f0625060b040b0306010603240305030c060c09061206150c0f010b0105131e150207030213020c030306120a1b03020913051e030c011a130204050f0f01020a 73
    0x1c6150500b03602c0301c0446013950034031903041403102c3d4400c1402c0100303990341500190b4050740048010007805103c1d82201c203191a80e4511800400d1a00440e88402c42c0150025106607100080780b08100d0300c02c114459011006841e07581c2000030301c4000a00922a0220710b00e80421007201081c62903860301460107040d6031604500b680c40404014072511034050003001403a551070522015032070b5024070121540c10041d8450319222605040b40799540360303410a2138148044003404003069808030200789000301d44445d001801030b18550300c104140c00c0c02c0c0c503815005203401403281401080d000429650031600032100c1d0700030481c0c202061840c04510401c00b41c0400e031803441da210708003200d600c1441620f00070b072050b0140d5560444402c503040300070b40005003a580300d62991400d43c5958120441014441c1065074541944940d0103425940141c0c505071031908000204101031400b604400c901c1d4200c02015402c1c07925203000070396200f9880c0c400c7c43c0102e00b40d00d0b03080c0c1d06a209204106059a21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 106458714 1250 106457464 106457497
    0x30712050f0d0314070206011511010914100b0d020a050d0314040e0f0906040f03030c0203041e05120f0303060105031009020c0c01020d0207231203030a0207020f0f0f0f06 75
    0x2d24010050b225200c1c3d95000210004003040840748045a981d0682d00310029800304c403618008200c03074900c5009071096403550788907100c00c0000e0110000c10508500f850050801541e61031080003201c801c5204940300c4d4240c5003d02005071140004401150800c4820140c44411401c1c10392700c8180e0404e040f031540d00001400304580012180c200e01451103a0858203440e5942811595141c1050701c01519254040c1c14010010348aa00300c4014110f03240306807803e01d0347d240c2100c40030012a80c0c500804110802041c406810120300140750440080c0c014400b02100100c180d4907448080c1ca80350400c6000400205244283c40c00c0800410101c0c00441d5516a80360300d094503000b001a1090050203900c811032100d510000d001c9050710b104110354030403e0302034007078200311038042038803607130001b19071181f03a00c490105001952051240f5140942d0359065071041091046822080700e108400c2d05066005c00c0d201e96404001a6405882062441c2c5480c40000c103540140400d0300c85030800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 106459964 1250 106458714 106458733
    0xc021005090708071e0b0a0c020f0103022b0c1701030611040b070f0201080a0e0705040e161502070803040b0307050310030510090c0e04210504090504030f120b030712050f 75
    0x8081c8001450941100a51705055214616070141d0710848200c0c000143e07803460004051b00d010440c801c840d100c141001860000e01c405680c0d90380390300002c19400503c0c0c919540c3d00c0500603008100001d0641d180001500c0c0210700c140c10780c4041804041e08040d911584001145160380880d400785c1b01d441e03041510741c60b0515104074100c0b00240c0c01c17400290400f020030034800c0709000d480d0341e2403440310192450382c0c01e04040c000148484101944188984070039807003060090006039000e010807503068250714580400c081d04e01181984440e500381d20400081140d000d401040e650001e1880ca0104d5503500c610130b054038004010f0f04047d199004007107085a80c0e60b52980103040c1a4410b00c2c1c00c010b070780c0d0741e11240304003198101e901404030304c50004010350000510b2260104100e042c2000c2e414652250400d104a401c1101c04401044c80c000c01c3c1500384d60040a0f021003111002020b0080880c503001003511401079104c0c4000080e0090354000c01c1000c00d200c494030140442046072200c0d41c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 106461214 1250 106459964 106459979
    0x81518061312090501050409020d09020d060902031b090109050421050903010f0b030a02190306020301060e120c0d1104020f0c011b05040f060503100302030102071b06030c02100509070807 82
    0x101c6090007242e00060021180c1a90390052504078204e81e0142c4990741081d240520020281d80700b840464026640d40180f8801a0340300c500c0c00c100c1c940100c0002418061a01c1070626284400c0511f1041c00f8403004840020f559000c5124113440c10b0560201e05500c3d0391030003800003075003012154107840f1241d4003c080760f03a2020240115040880c001d111402c070f08900c1e08200c801c00c1c084590190014000003003d410020004c00c0910071039141d0004c00f85d80d07500d4450880e002a00850006132001c03400c1c64881c174120450101003039400c130203040d864141000148512184850082c00b00c01120f0300343c00795039225416a0340420210b500c0681e609070300040c103070003403050003107003038035940c080c0c41d881c0025100b00151030907144464040102c45043c06402d464640008080061a142102000c03005031401e00140401501c030f907082410315000803091907050310f5903410103000c16243c800f11f0350b02c540d0700044003130040104000000e01900d0791610030f81080000e410041d0988039a010004229 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 106462464 1250 106461214 106461241
    0xa0803150105090d1b0f18110c0f010b01090e130f05010b0303120619061d040906020711011101020c0c010c140706020303160207060905060d15060909050c0408151806 73
    0x2040303174020701c1d030420b032510402e00d051000c174001d00840552003810030441c40150b51100d007d44124040c070501700b0902e1300f0801d2420301c0b1038040c0d20199450341d051034001c0d6002241d0102a0524908000240c5803400c102d0501d40305404028152542440e83c5005020080d800040542000780035240e8402d65000303e01781911080e6007041c02407860201c181540301c1c60380e00c40c4040d038403103545000c402d500d640200c8045441d0010a2a8800d540304244d80000e480f620080c841540b2500383c0920100c1031100140c203580c203400e40591b0076401004110841400810f061500f0002420141611070301d80c140303968100c101e102049094416040c0106031203170000702862040480007540c0b5241d4a0294080761248014400d103408600507030341c00e1000d481c0c80f8000d01f080d030320790f0440050500031903180384084035017a5002da0003140700c2c2d034802d1007403002600819500086909041d4906854030f084d055940310007042c1c80c0c404c103095402041c84031446100c0c130703001000c1040c1218804d081255410110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 106463714 1250 106462464 106462493
    0x30233040f06110a080703140d09060b04150602061b040905012d06020615030a052b0302030c0a03021c0501030302150901050601021203150a1202120a0803150105090d 73
    0x4150058140101041d001601c4540d544d17008011034101400d1f90703810355452610041600f000042402042924441440741d0a81c40d8000d20740415101c0610047c00304603180642c000c8090b0342204824031001d900020056006150b1454800c07900c6480c20700d1141901a50308140364460402d000020300d400d032061a14030b103803034903240403180307040031260708182001070b12440001d0381003c0e000441002420400300c0d4410f60103001c1c0c4040191698586003001801c642400e6841c1c925041e0f40c0c2c40c0c490403105076440510604085186003003141030011540600070f040000c2540000385044101c1000c83e181e00740b000c540b281440b195843c1d24001c0e4035009548810b2500508000024016210500806004880c1a0040d101c0c5840e5507440002650000b01072a41003400071680c070001e5120414004018094283c2d00d82c03a40b04280b041041094512041d0344074ad900c00c1d0350312004200d0080441c1d40240d071040140b44001c4044005030b41501506650b2903000701d4142e8808103001440628402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 106464964 1250 106463714 106463717
    0x9050402010311040e0c090d0f06052505031503030408030301030c140f0f04050916030b0a0e0105060307060c0218010b03150105041d0414070602032101030233040f06 73
    0x800c02c0360f01210360f20f0040b0320602c0004222480070607000f00c02d80000b040000000740802441c40b0030780c0c07a60498540401320403104180c1ea1420070001d9908401c0708641022201a02d41c0e80004070f48000304603000103801d504108840c6112500035641c01c100703c44c002c11100040d00d45a60b500d0600e140c1036004c43c800e8071044550010300351214503040009080c0542c0080075446002c034114203007c001c040050406425200e01e0032a150b0034880d040e48000214810010003410345001c460180507510b4003040312409038104000e004081c1c2c2d0100c0e50006031b54082c83c01c800d094400303000140d02420301d00f5245150050040020a510340008000c6110f5580b20740d50307803500000c000045a151190380300c0c035140402c104070590800001030120030f400500440c010101d0302d0b014140981000020790083c0d000d40e00004620610500802c4070701403c1d60640e40b040320725803442e004101c124040303070781460380c2460440355005006666807840b1840d9243d8200d0684442e107441c2c1ca03905108442c0103c40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 106466214 1250 106464964 106464971
    0x50601090e0102090d08090a0305161d04120f050d02030f090c0102060114010c060e0706020105090709090f02010f051c1a030111090607020102031608070314070308040b0903040906090504020103 85
    0x41c1450414003c598010f0405401c411580400b515911030b0f5030440d0030025484a21078400001051040240c02c0603202c9540218100602e490013003054941007010b003102988080e0108004200b01e038500018074021070820700482c4a04910403203483c03184603204524280b01005000510694101040c81283c045c404c94150340559401a070f6580800d10917074850403101804560f180d440384581301401841118046005a010a10b503400d2503e550031050040c3e550f082042036881c1c041010710010940b10104200110003a241c04030100b1000d000070b03060140070441d40741030a101c0c0381251194124540c0c43c0075540c4d04044140c0280905041c030110240e0508824029886c0c18407400c119109640c81e0b00d4640407240f410b111090300a00d009034198003040c03169106840d4102c3d00b980c07006105041060b6550140d10f03001d4840c01000d110304040c880240804c20000342c02c0168190000c0d0016104141e5070b807a021024036621558100708045410b02c60b0024540782541c120a0080340700f40c80a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 106467464 1250 106466214 106466231
    0x1051b031005040c03060e0c0a0e0a08030a0302211603200d0b04092307060c020d0209100b0703020307110306040f06200f0a0908030906070303180b0405060109 70
    0x100140416680e04104100c8141d04001c01e18155005180318544c508010400c03030b0750b0742c0b14040382034170880c1c07071090145000400c03403c00c41d44059a01c01e03d410071940e1a81d002d041c0301c80c259882c01803a0340a4245640007650039001c45040c03501010b076000f01615140b0514100b032070716115000c9149510b020030f04102081d440f110544034442c8460318041d0001d42894006602e420240182000b0706400980c0e0303082580c003080c1005281460201841911030000e480440c0852803c00b06a01034020403014085d5400140d4609003014600d41d01200c03402d0701a00c1e484500c7d0400b414984c0440e04c0440000f03024810150040b0180c2051401500d110003562a24810305441324400c0318014994108241c0000004240398040f8440030590f4001c030500511b9102826243c0e4440d0a48a44984003c1500240c0039807201160016280040c091400d0403840008610b0600540c00003c040c1a00c2d0388205403c403240011043c2241d4200400000ca401c09081240e29440c00780509031060381801520b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 106468714 1250 106467464 106467511
    0x1203051614030d140106210917071203090b04020603060406081b0108091902090403090503060103030302040806100501090b0702010c0501150608010b070206040b220308130e060616150501080105 85
    0x20036040351010b4547d6010952010443d00c1122481c000425440c1d0743c41c1c0c0005c007c1407507403142050980030341030003644e00c0d511401d054007010010400801018140005040016940c08400f40c00641c140c4031986c0700c0c2c85610005000e0703d800d401091a601c204a007010305d200c1c00041d080300800c82a25010a9902c6a0300c8030368450380d00e4a00c03554848043ea180d5401803c1c42c0d034040e94000c0c0240b40024040340c484002a08020080e8411350000b87c01241c02c0c072181c8024055070f074002d002000081c241503c0d0000103003880281d07221341d80c03041c2004902401564000d004840403d903200c0001c112814410081c0d001041c060301401c00020510f6001140040c40d0400f1225129001016241801c2c030f45003801c0c500d94014a4400320961039503107003641c43c0003114940005140b0400d540c98566560300d0301080d400e4629480520400c0460f03082c84059110441126140d210078411800c602c00e076400c4c003850718400b000d540c40c9030500c0d1400002d8480010f60206004032080660400079030b0b00600d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 106469964 1250 106468714 106468751
    0x141201090203100f06090e0618070312020a021f09030222050f040b0601050a020a2303070311010506011815020a0c030501020703030b060306062208120409060f1203051614030d 77
    0xc10b17491fa034080750100704000440c103a148210304424044843d80e40d141c0ea03030214422030040c0d604015030b21040c1004214586000c41c689541203e9810740d186074408032000348105268403010303000d04040d40308203131129004486001200ba2280091000c1e0034003294034a41c2000445003550a0740d017a80100e074843d881003003100c0499440e940108081045500c0e980b12481a80101080650340b00c1d0641a0141e03040c13000d801c005010340c035440141c030469000d140c2540c90040c03603141003098607482780c20020065800d14003501c0c2c8000121441000c1410246d18200c1103400c040c240680c4443c0c00000c000c415001806d0003031107030394140011b070030300c10901c40da40c0000d83d01d45a22210a00412450000c00f800d40401c001400000f40c1c2940c0d664907100b42800070345a0000c203102e20020301803100c5071860180074010310385600e42514852808400100507815034030f0080402c0000152802800e2202c08280c00c666000a01e07501400d9441c40000e0b900d610616285050905021505840850003507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 106471214 1250 106469964 106469981
    0x50c030708060f060607021f0306060e131508010905030a020c010f05070602090312030907030605090703052a030328140a1202071e0201080a06141201090203100f0609 73
    0x20041c50141c40c2d03080c41800b003c00c024050340c2c1050046c4141000b587d1003440941c0b51100b61284580501c8403d0401000d9801c02c0d0030400620101314030710f144c549c49082c000320ba180100c050000b804501c9015001c20905184c0c0050711960030020400e0600c040030009010b0048942c01b250403c1d800300006644141182507802d02090051103200e012445d90740003040a44002004e80e040c840e0062161000782d003054407108440e0340060814010420684180c03900007224070000c000c03952440d1f44803640c82c07000743c40200c03414000c00b0302903c111398030003a41011043c00405a90b182c50f9281810149041d079482400d402ca00c06840e00035000d07010310101150501402d42080ca031200108055858034000908031244541c00c0085601007403035003c01e024001e0070b6900321940d061140c000103700400151003403904038a07041041192402024510441700015554050030f01e06e803484107401400c4141d0003942602a1406c0395001c10030940c410401221107900030020280c41d00c01c000115000300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 106472464 1250 106471214 106471229
    0x1205010f030f020102031c0614040204050306070302090d0b13121112130e09030406081803030a151205010605030d030e07050402070204060305030a02011b030903021c02012007050c0307 81
    0x5040c1030000c5100700d100000100d0043c0120380c0340499280507801405103145260091543c0d5032400e01400003900340718100090111400e40c00c0c94180b400180d01e40b040a070420040c140e000400c0c01c0c0c1d81d200d0440407088560800c3c4407003e58a4240398034a0410913220084071002042000807881d00e0080c410169074081d90b02c001d090000400d00308900e0b640c4a11601c0b1600d50190100088402c1030302d031218400d408103800f0719240d924107203004c1c00140000d00300041d1880c401c40c40c0445208004207807580328603012400303d0307146030b524100007a42c1c0c0181c00007000c4800d02955102800f43c1500503104a172001c0d41110b5032030301075807411000c85400c170b030003c2c40c60b0b0082c2404100c0c0d0316054000d4040280010b0000822590787da585a10350381c405120000581d454032400702c819421441c00c410120014101440301d15110755000b52910280303400c541d035458071020003c00043c0b003584501c280954540701c081c07240410a540240c0360f000360754115840e00c01c4a401c00460f0401080b0300c0d04031a0348 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 106473714 1250 106472464 106472489
    0x30f050322080a0b0403030f0f06050406090501061205070e060315150f07030e060d020a0f02060105010c110405091018051e120a0311073801090209030f0a0302060106120501 76
    0xf9907070707040349568014005404041d00c0d42c40b01c07448500300d0711415464120000740010842d103020700b8082620f086a10000c45a23152400401c00d031500b1049452204500c480d0016241d83e49000a4403401d912000d41a0001000310030024580c19120048005c0c08045038170641200b00749414000c2442101c062213880300d0180b00756000030b4002d010415841c9030042402d401c080380d00008800302d810058a41002a90743d40010030041d40521010b405042c00b03180c404044841e503103590341c441201e105620301540d0740340c000030001c5005001d003048100f00001c0c10302c5020000961142c5801d0151350076600390180c0c00d401900d8a0b600c9550490110081001e81306258541e45840c603140c008090341000d041d1144218003005c442c0000410359148141440420783c440c07507501018044c11080488000128500315000b000c08100307286045403c10034016a8501140e8003007421303d10303041884e0080740728028088080580214072a8141c4145a9460040f07548102c0fa190584e40280701d0070701070702c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 106474820 1106 106473714 106473733
    0x803070203071e05070515130f0501140712080c12010b03070f021902060a090f0e01060323072d0c0606080703030e19030f05032208 58
    0x540c0050340e10301c65130384d1841d684140c00d0146034419040001d007191030380c44140031a03001680101603000e000e41d448090f82124805405100d000c140c098800b1a503d041d4001680c5009401c186818250b9049000646030300342c0c06000c10f1000c132000c00c418510880140c14440c001c080300c000241d80e81c90081402040382143d00394440464110066968800c101a0079002050750115420340c0e442c03400481c20340d03c2d40940c1d84001a80c20100e6000580400743c5140326040300c645881c1400701c12032198940c5030840c0c41c051a083c507401c3c5c000204a9081c864020400710410312074084c1d5a07001d801d428040742424440d0034100023504e14001c282003048074061a002803d28100510a01e41146d178080e14031860b60000e140904004010440c460f100d20450314002d54220210782940c0d07000f814610b03142c1e0b00851036018070610b4070015003031a8200394403041c01c83d50040c1c0500408031 = true := by decide +kernel

theorem cover : BRFrame.Cov 106294964 106474820 := by
  have h0 := BRFrame.cov_init 106294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 106294964 ≤ n) (h2 : n < 106474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
