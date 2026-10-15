-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5511
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:06:33.901225+00:00
-- url     : https://prove2.me/submissions/f1c77567-cf6b-46c7-a135-3f7604c5863f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 991007194 ≤ n < 991187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 991008444 1250 991007194 991007203
    0x8040f06020d0905010207030b0c12092409060f040218090d121b05181503010806060910050d1a0708150307030f02040209061c0b0306011403150a0e010923 68
    0x4e00f405a80b2039401030002071009103150340d000849601c11820105500c441081e5884240c400c0421500480860b50156001d0000159005a50503d000c07590400e12031f00e650740e0340000e0000103020118800320b002c40d65480366841d8001c0303400032014180d08104250588a1150b90155004100800000440d0308c44030f00546440442000c0d0240381411011402d880c282c1c0000690000341c4107840c581170542c1e540c151142c000280c0140e0350354a0b0341c1081c0c01d0501d007907409410503200d038110030100481304910303140e941c054030000d40301d00145650f240350040e1648100d1403d481d448414604015940d03901c51085807003070900389502c041214a8005040d2034101c1408003419100c2c13500107042c0941895001401d06a8015100510380421130b0341d601d11000d844403007034140c9929040d044c441c501d010048c003405445079405940640440e440002d1750741d000954150850101d200002c0d0080403541c0c841d846803c1003100a0000917490314011486441d0240200c9046050340141c9540710340014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 991009694 1250 991008444 991008449
    0x706020d14070308150301020c06010504111c022101080a030f03020322050c060307120b03190b07032d050f07020a0f060615090e16050a180308040f06020d09 69
    0x501c110300d0020780b40c80c01c4941200003015085864000700000080b6282440242001c0511801604055050804020548101101181c0308a85c2070116041400142440c0300466003650702c01030799143c3d000725181140c0103c0b40186400040c190000410304408100d5141f224400c0d079a0417509888190203904900041e00d240c541e50f6901c81c4400078031684992200394841c0100d00300c070b402c0740365000022401d52044603018002603c803020041c0b081e506009009241904901600341070480e4a20050301604a42019000543c1c0c240030909180c040d0307000c4a5501204640c140e05502c0381c1183d10f01d41c10b549a500454a4680800500f00b1036034400c0e0740f409072039281d000e0302c0c070040c29449400442c00d6a01c0c080d1001596540c0000b0b903503c1400300f0086071a003d40710b0910703103860010304100420700204002944c1150107807015046034400300315480d02e0035506260280c400c04800503010060302d6040107204400c0081c01060340c640075203441c0201c0e801642100c1541902c1d410031241c413052072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 991010944 1250 991009694 991009727
    0x28020d0b22110121020a03270203030307032705030301051c0b040210110f0106051003020901020606092d0f09161208090301020d09020f10120203040f0b090706020d 72
    0x502c680703540e0b61040c4283c0c3c0108403410720b81e2420b904007442c490102da12040c0110042503803000c80c0d0298035605103848821001a80c45c00300d4001a94011075124440203040004042d65140c1e0184161902500d20754a140604107156000c4400d01d40540d99610a014481c070413108120303c1d441d4810050710341e84c219a8804d000f4141d40c3c85580c02c1c881c1410741c0580b22824000103d4018003a01c004211504881c0d88203000401d0303040c036141c2806003400d5044041e0b0300701401000a2034041e6000a10f6981298040e40c10b03190998651081c002ca071405660140c04d01e40076818005003002c402c40c10940a0711500b052a60a0b40b201c01e01c036541c600140c400b101e0820b01002c0b041140503012400764400d2030280861030300d4165084002422a03200004903039010340e41c1c4602c1c1c4294100384c1c1c03900c1c842c00d0b419254442038001e200b1000d00113a0f404165810b030360b0303000000101007100d0f0600c0200da06502402000c5e032810650299901c41c1003a010744001841160602d604035441403403c9045800d11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 991012194 1250 991010944 991010963
    0x5010632030402030a0b0f0601090b0a1b1103030a05040f0b070203060403050c031e120a0c090521030403150f060312051305210c040e28020d0b22 64
    0xd2100000d1550030007003080e83d00d40a000c0c03020005c600304500c5540305070002d4801d180325150820024020095075004a015108140710882c02540c100400c40b0b18604550450192640586001100320b06094a401d4041c08049800e07030f100390b01300020341305032604812201c01050b180c1440700d14134042c84138080d501d640440c001c500401d01800c01030801072140b03001c3d01c1c54000306d6401100181c04141c01c142401c500001c91403504030031040c10744d400207583c0c28140200b04149000074000049406103600c54504501100c003104403010401c10b45001940c1960340340c994a0401d0380e41403038000c4a22000c5030801c0340765900100301c2d02c511402c3d6907004100f504511414601220507400c0210ba96200200395180403402d42d131480c0042d0061031a80d915914408541a282c03402e0824402a40d40600d0400010f0084103101290092111301804512009111101044400040f00c200301a400440310102d0a00f80030000d809284101042c000214500801002d42c2c0d049500076100580101d45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 991013444 1250 991012194 991012277
    0xb060a02030406050703090312050304050105060f090c0f0d0f060f120215070503070b0a0f140c120c041502032502130506032506020606010f020d0513080d03050106 72
    0xc0c0000d80645c41c080d1426421035600c030b41d6172800314807000e80d07240003040003c4200410400c09001c0c00c2e07800003054851800c82124040818a180c001800701d0140b5400440e401c510400c480090355100f50110b0410b004541043c080c1d04000c02080c0214015140c0f012008202034405007211100d0980c050030400304100c5250b644042900f0081c0121881d0200300510710108803003001e110301401c1204c0002410105400b60308003100e8034031400100c802070360701c00c20152948a8060f0344000b0b40d8a495603e0325030303a0b80c05c03000d61403080d42c010b80c0e8030084903400e0345074090380007001c0c00c0c0d44a9419804503862881c17400c02e14a10f254180b00951040707030000e00e040440080d81207070f0b400c0360307014085514401c104103030a051114800110261849172800403c0543c1d81040f120707070050303400c1c20426088a42c5100094a40e40e04560450a001000581001865800000500408501d0b0980f841840f030308034002c1c040c10081c4941800940400b580e5142541110034100030208040460ba20300030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 991014694 1250 991013444 991013447
    0xe061e0106081009020c010b010908010c02070905060a082e110901030b2b060501050406051503070e090c19020c06040303320c010e030702011205150a14040b060a02030406 75
    0x101d004010f07441076143d0b18000200001d041c00601a8040c40c01c00205015641000050840c10950703c00001c0740c2c10b117131300e01c0380c1603070081200d0043d11200300021403d03030f65040119003c07420543c00082035100b800c8114a010f200149510b02c010b0074801e1a90000010001e003070300342d4255900744428000c00304017481d13096010350700503410b90a02a0800519105080314881c15038039503450251a424048400c20812a9070311415015201c1186c040200c50b0034807000c1040103400740542045840b0020220343c00710301500500495800003045040c0c94508603500302400d411070114200c1080c1440c03402c5c5013043c0003281420122001030b2406003061714580b4101c07800c8940240e0ba010303451030311261000c070140042d85049011020041c0b9a90303a11500b0405003110303080194600c45400034804100141e034814031440c031102d4041c401180d0341d1103400d000c410740e041401d80aa406002d019000451070654640c03100856000c03201004540900008d00500b40714100030040160410841442820b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 991015944 1250 991014694 991014707
    0x31a090c0a0306030506070c111503010b031b18040e0a11040924020909072c010314100f05030309180903071a01030b01092a050c0601090e061e0106 65
    0xc241c03a250208465580781c6625081400507100d69002600303d2103100288420215104420b4030240c90044926018003c444850302040c020720a5001c00040410280d103002c0020001444030140c44550342c0008141c0031032102d607800a400e0181c1c3c2000c8240c070310f814000c1090b00c0c3d1190422005d480d8010240c003004000c0c10202c60803944104025289140d10200b581600c0b00003404020060740d406071041080742c1a91700401d5502000340540911410b148241f45409480b102e9200302ca928200c04c1c00144d000d04501982c202c0e8100c0d0b100200b0030400704d1107041c20105d800b003507090350500f0384550034140c0303134071844040940014004075081000028800b11a90229182e02901d0400d80c041d5100c80ca07034480d600c11070403682071000c010700034465403440706030040000340c3c002c001e461116180d0001034805074220703600b1020044403000505000c1c008444000c12840c0940c0d00960b15146110010000a13840c13102d00d2141c040014071618000c4460591012014043c0d0202d03032070198211101e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 991017194 1250 991015944 991015957
    0xa0c0308092e023d06030602070c150306060512060a2c060603010303120c090513090b070507030c1202030d1e1a3a0f03031a090c 57
    0x440038010500d100d10504280c070a002848001800b80304524022000345064482d116103502d258841407255101c2c0004080d0f1103030f40680003070011000b003407034450350000d00031580007030002400010303d0000c2181c0c1c11011015900c1105201900040b00c1348100d044401501032400802c004225112000b02c48410540e4001e100904034902d80791507071300c0681e0094106a01081d030f21f02d0b000c410304100000009890780400250342e4242958515140100342c0109035055801e007507035030001100f8407413040700b5074005840090400d03400b030340000c84400000e20500d0f90544444111001040d50743c0c1c410030440c2c01e085c0d00355a403901800c80702d071500d0441204115504c400c2d88001c00c604c90140c20380d4092078044119400044c50380300d01c1170740c0b01070603504c1180210a0300e18011107001004d03500c01030395180070300003103030040d1a50901e0382401c0c180b0b80014907148520805c151040c010000c441070300303442c000d01c01d40d028440055291820040c0d0383c0c002580301c1d0700034030300c03800150380c0c0314400080d188 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 991018444 1250 991017194 991017199
    0x3030513051f08090c0609010c0c15050d0b04020405180a061a21070504060e040207020307090912050c07060f02010b1002060115080405032203080d0213080a0c030809 73
    0x40c00c03560344000800524000000780d200501d6a4500d08405401c40911a841411107001e00000c00c280c40005509100f603241803814400c0750100d0b007043c031401c2c21040c2c0162400b0200301411000980014003607811100a901902d8240103049005041a000756811a4000b9216144003a00c44040d07012070f4800521024400d5603070306000800c03069039101c01450700d071012221980d4040e4600f010356000c0802d184a1594481e400c180802d140c0d022048074200d4038140307040804041d950300014060712428201035410721a408020810000d1039200028043c032030302c040b001400c2041c0c0180c485004c2d1f82c2c0171100ca500029803c000580c000c000952080010380300004000001200040301001c100c40d005005034491401803003d440e81c4950b200407000340703042094103482c04d42c0d01d0682d40d114400068800d0030b000301c3d500c1240b00c0c40003140005140e00c15140d6880b82c81000c03220000350040a0700200102007a440020703114001b00342e003203d0071781222041a10604588510203141e000f00300458 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 991019694 1250 991018444 991018477
    0x130b0f0406030b18041a2802090d0c08060709080a0c090207080f07060b03010e0f1902030f0f0c04050c0901120902010516051522240e030705160807030305 68
    0x808515210f030015105902c24112005503140f101074800c007424000741480d14103c200c80f00d03080e101010b503440400d20918420056580c00150000c1480c1030074ac2003004059038040b075404214601c01082052240050341e899a414550387c0c1036065507000100006480d00700d54420130300c0000010f4005001850060011030324203803400110700016031080034252002682d071043e9030a103180a0260281003095440100460004843c45685034415442e40180382612075074064119201804450382c16040700381650320581c444083c25455416035054284100d01e40340000344210040070a850b14900306a5a00800401150795400140000003040e03042c080f045c05030031080d40d81d03200040002c910400280c0703240749a184c1001c10140c8082c0c0400c46200320440800d06824041d81c0c41100b0a0700003000c1d0300306103403401512484003e41c404d045085410815142c43e1880d002006100183c4a8021600402a0ba5404000925890180c8107072900030480820100e0304c14800b500001c42422280d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 991020944 1250 991019694 991019719
    0x1a0d0f0c0e04080a090b0307210b04020a0914010c121b210e090402090c070f0501180b0906010305070501270603202a010b0301050705130b0f0406030b 66
    0x2101d001c0c049a044514203800126205010350015008000300030455800d411410280c3c0e01400c0d00300708040156104110352101c1410305915000100c05a031301410845d80c501c901d00000702540d000f400340041d840c01c1000081150751041348000c150b0b5403c80b66480d1000e100010031107140b407000c22150400000c1c0e0b080607012807414294013042549241d22080d0b10101000040c000c150080030280c8244241c504200240c1c503000707074140e48010070071205d95607501c1170314240042541c1408080d1071586410116405401e6a14000d0841400b0346171031807071642d5080075159a110700b400014401d070441e141c108510b50080020044003068966803107080030100900018010700342e4407003000642ca455080383c0311007100061400349035012806038903040c40240310f2018590030303d000004030001d2008000c03411100b1341c07010380f0a650044c0203218500f052800201a80c0050002101c0352030300b044c00041c000c04500803500481050110075040918006080d002002c484044a81100c0000d482 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 991022194 1250 991020944 991020959
    0xf160807030209012d030606020712020405101701021e0304050705010806180a0605040606020d0203030712020d050a05160e0306060d03180803190305220503040f08010f1a0d0f0c 78
    0x1401c0385c08808407040304a80d02080011300761000b60340f2003000d41d000380e0020b02102503d2280e18002da501603801085a484034041c0c491480c2090740814055007034003c8100d02c501e4190014003999807075100688141c0810b0304c0c402e441d88415103000300700b030b40301000c100821350180c90440e511405c01010a80007804913058041c09081c115400500d940c2c0e2100d0900451500348a000003800071031000341742000d1100d2000c0c0d50b030b11000d0100c1d8140130740c151b41d8681030661340e012510b0510800600b030020381007084010018200c19105960781c2228a009517000c140301d111100035549004000308110b456034400d2100182c9941400c3d020840000740030501400d001c00f50000810840d0011039803420500541c0e441200071181010425007401c050190050550485620b10401c043c0f81034428480d51a1080c510b105e0b0b0761110040c60503030744e800910b588040d8800004540360303880074400c1d40328040c040c0140702031000e90660b008400808602c0400d01202089000500c1000b010070700c1900d60700e1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 991023444 1250 991022194 991022237
    0x2e022a06070b06030f0a06140c030108072d030312060614120c070b01030c03030908030f0d0b1210060e0604020906040e10050405010f08010e0d021e1609050f16080703020901 76
    0x8099584030384500c223800c004601122469409101d000c011401c5505000e211601c43c50030340318003541c90914214417441d420061058420340203052540440c42035491602501c016101d10300100c1d100d00e0114000303a031501844040460054a00c1c0503031030410240b090115056014040007104c0b04180451000034614001250103103000702c0c0d0003000103281d49002881000c95400c030b00e096420034004d01e20502d00740704c10785035115100c030b40c0405c0c455020f03004501081007101494406200ea0a151200302d242a030000d000e0740d00c1001c1801d02d43c5e841d074007404140d00c82c18507400d400040810003040700300400d00e445c5400620010000e50380036a5840028152a02a0002d00902c10000c00800480f04244500d828a02c40c21026040001d00aa4040e48896001c10100c10200c04600b801142003014003d0680e00c90600010313080e440c3e115a040c200804044a030414030340c0b010004a04003405810302c0040400311952141e0a0340e07690502207002c0d4010044180c1400240780300c0c1000200301030f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 991024694 1250 991023444 991023463
    0x31603050d0905060117010c1d1909050a0b0612011202060f0408011b080f0f070212030c0a0e011d0d021809010b1c050c2e022a06070b06030f 62
    0x1c004111a5052000300d42003200c8806000000e0ba00d8008c41c01e50141d00400a1441c085030300c2c5103c2e0554940d98003003240c0451080001e0744101291034081005020303540110300a04100004000c1540f196040c46003901c030b5826031500040058004112144941145071f041610203000c4500b07115034030400c3e4000c0d8109800202c560f0751a085451015120112800308610b414500741d0840c0c24042003582c02d08a0103000c1c1c2c0040c0c950342e00010040f900800418071241c6001144541d00d203085000307008079800078090540001c1001a0700b0440d0341c400d00c0780f1142c02000d81c903503075070640d004410041c0510755010100e070845403000006610804920b49648982807400021504c0c00103003081092101d1140c80050b03d900c8880101404248001034203c9000b10688941d2210900c401c03246410007002d0070b0455250103904420702a10390f0200c1c04001e0003103c84210300c04451444402c988682d04208240d070032200c1408030602041c504000d40da008413014050340d0718440c0c2c10b07011604000606 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 991025944 1250 991024694 991024703
    0x300a12080f060f0f0904170417070812180d02090103080703080c1c050903070c1706100513020a180b04171903050a0314070801030501051305031603050d09 68
    0x1842080010034000003910762000b4200d580341032000c0844000b0303150004002c0410b0040c0359010001d001c012400c0c01b81450031851b00c11180c1c585584031684640820024050140d0340540440045c20f201c000401e90b0000188040d400d00740804600301280b82d00c50b403016558000041140400580c0380d40c84a140618051141c2c01d984019a040107015040084d09035000410304001d4501c145609490640642d8412540030400d03882c1d5000207440d40c0980c040c05090321030201d40008200c4c0c060740001030034144200c00d40d5100da0355110305810b1402903100e043d07002840803c002c4e080010302d500800303007654941000b544082140b101401d01c4105a007041800038000107003482541004030500640070400401000e028862103a041301800845034000d05122002c1024070303041d40681c0040c40a803000410410641ca41982c00604010b030a110a17500c5d5482d140c0031609006a1041c0d2106240d040b00081d1700d892109170750034040840400090701001010b00c1482505002c81c040d020702d85010707 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 991027194 1250 991025944 991025957
    0x1321170a0305070207031203090224030628062601080705010e090c0406081305030d1b020d090608090718150618150302091c06050105300a12 62
    0x3400000d4100d541c0903007500c0556120320703c01c2000601d081c810700007070034044c078010841c41c3c114804a58002e04c80b464100d8081c1c110901845145260340241d44140d1046610001402054a402c210f44180c000324400c1c0b55500c1d04248038440c040c1401d01e030750308154042c3c0120702041f1120ba410380c4000b0f07002400c0c1070b000400200310640c0e01542d022400f0f00304440c403820030b082c44414000140314ac0d10038442804480390008000144030b407084001c031b0390460305695503075070690010030052006442c1818198000095003d07008d10001d10701c2094206900c0b44e03000241032032030a0b5034181d001881d5240600c6a500041032010341c088072641c4007110703003102007071501c41c0d240b0b025403031545508890100100c04408040300361005000d201124075442c41003a0030040d0745c400f01c1c00380c49031841c0250410306000076031070405240c28041140e540224400c000990701c80080010380e81c82540401d05203250010305c030404404031390a2801c0344a0321001c81d01c0440300b50740c90615444502410300082500b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 991028444 1250 991027194 991027207
    0x90613020703020f1002180d11060705071a1809092a03152e0510111020030a060806070c03020607141b010908040b09011202132117 58
    0xb4100203125034074551711002e6003020418041d030a00a104041c0701072040b1440d80d45c1505000480d0149442072401401d81c4d5075910880c00c01c50b40d100d031940701d511406a80c0e00d00c1c2e4441c4440010980d1514001440d0341034100c0f000030200072500001138504100f9000e28505001140d0003401107503021840c2068070080789041d0010142401284000f048030451007104114a0301c40c00c0707800310480500440c0b0ba0040c12080010264926015001290055414892600d83d40d401c80101d00c40c1d09102001c440e901d507000b4000c0f60070344500403000b040300d0300d0f00708800040c0180350001d9a448520342e40001082991004810b01d802803e4400401182d1340c0c07078181081c10307410b0160070760200050501d56031030103d6080c1211680b03d8000540306451500340301c42c0d09140d00b900700172100b54000c44a00d0701c41d511005044e03a1584a901414086001c4003c14000c03030089000b41d6000e808840300301c145003842c0008511201c0b0508203020520700c1a49150030000303003051040d18a5031144003000d9280d41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 991029694 1250 991028444 991028473
    0x110412030305150d0b04030201020c030406080118060609180e030d0203161b0305210901061d273901051e0a03020c011a030613080909061302070302 65
    0x300064210300300d03451450070050403070304c40701803a07004c0c164056020003056450742001c03402030090300043c004a000010700010202d912040c441e050304d00b104800c1204104039072040046428621601000c5800740d030040101403020101e81150b40010003000c1004940b0f00480f605590002803144403942e4040107003e120540c20380100800003481c20900c3c90008400d4848020040d410002030401038001400c404503440880800c1d8118050f04490000b0b0a081c0805400303454203014080884d0001c08030103028010f91041c150282d0b040580396a40e140d0340c071917509006505583c411000c3d1081c008081007040407800d400801681e100218100419506418002040340d10031040c108041442824211060400c0d948482c507200000155a140341401c1a0b02070b00440d09500d43d1546400201500c011350724082c07915003081101501c4c12999510303448045e2050000014001c4841405041e41c2810101d4506400000007802005030303400c404083c0c1c081e42c1c441801140103030401d012204052 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 991030944 1250 991029694 991029701
    0x40b0304170304030903020d02060918011514090d030302040803030708010e0a060b0d050a0b120703120f05161b0801090501050c0306100e06040b070b010807060e1302030a1104120303 80
    0x11009441e21070300d103090645004002500900000c2d2083c1000840d400840d079802040702c81c801c0c0c001e017640100002c0314850801c003800900c01d807901209001e2005460034840d4514100210014100c2420004048203002c0c4034004a501103003031560070007002c50016070801c069880b5884030307910280c41d90b04201300c8009520000d491140d00605104050001c01d480000713403070011401103000600c5540b50110321016200c1e204c3d5403504002c00080c241408000814541e007581d01802c1404402226144219041100d1004a000081c414001a441ca45405511110140c05400003140c000b1180c40d100702e20000d0755000f00d8150303544918450400500b030040707680c00140881c0b000c1c11742c0b61610114050509940d118010804940d400c0360441c0d07540b10542e0054031800d0383c0d05031600e90900d00341a030450207006030074007441007210019980d48120484120002d006c0d00c103545182c018501c5002940016003030301c1e100c54413441c14001007070700b580161006250101800e488040340341000f4088 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 991032194 1250 991030944 991030973
    0x70f08070b030406020309010609060803071a070203071401110a051c06050913020a03060c05030906010b03190506011b080405010e0f0906120a050316020109090c1e110102040b0304 79
    0x2250004002005074512250540794825007080026907a40d8448040724010911900301990345850800007040c01a00000a07050262061002c0072950292310365810100c0811555500143e204120380c1700040d80c0c5948200000300380c500040b0745100d2294107011560051004400013901c0445c00a40e46540d1a00310340d1900c58201c0c1c204484c900f0700011880c0b1900081c070599040c0f802120550031501c2d420141402181c001100b0400d46650000c002c019038000d03200700c1e203e80300b00c60011500c009444e080302c1c024032080002c4035101500e0b071200c40c0503000c02810035061041c0415040c1c8041c810000350108103204004903541d860811001505482c990704142d402025803400624250316000708176034101c0c5044900c60768510030034420f00e141c03d8804030000c025001c04500b001b031020041104c0301e0032030b100762254001c0f10f03260071600c4100d0b0f111a0342900001c0540c0c102503824241c8450b1403c1d0302e0000e1401c40d580a000070071107420390740076174080700d100e0400000300014414490402c011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 991033444 1250 991032194 991032209
    0x50d06060e0d08181302040302090907080a0b0402010c02100c0b1003030c0b0a090c0801051504051e150d030806040e0106180203191b020d09081e1608070f 68
    0x724039600c1c02150060741c000030014010040010242038403600303810340e5202500c0041c07010900b00d462042d10800381d0000d1008900603607a5001083c0144000710b481000d0f900c6200c001c0c1000050f5841e8a81d1550b8040c0050303060295080c0c140300584c482c01030300c00385d5206a84402401683c00c0c580221041c00040540e01d00240c42c0c201032001036030015521001d19044884100a901e5004e40c400091a034030400030100040c1602c0051080010740106100d0f8501c4017440c450b40032840107120603503500f1030308840801340281501042c981c0103450f00e80c1140d210015400c2d40071800001c100712664070801600400c540328100042d03450301d401401311038031150000344411032510814507210a0700140310800b09070080001030b1150b4040300452100c8124480a000e211061441060389400148504005000d40300d03403135080c1406080f681307003140c80c5d000c0140200c0784070003484400500440d110407828040c040301060f03004c200507188806001031b0005400454a0104c41680b45083c0d5800500c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 991034694 1250 991033444 991033457
    0xe0907080d0c080f09040501081e011a0d030207030821011e061b061103040501051317070503120108010e1c080a050a0e0d021e030f090d050f0d050d0606 67
    0x795400e900080d510340c1aa841400207803103000003041c0c200c10340241139132150481e1404000090100c40014a025168000a07413036442c3c4039404003a0303003600c24000c840039071444040c803025003c2c18030b031091015180c044e2055840c441d40300e0b5202e04155000480f035200d0500d06500c2141180b404040d620f00400036840000d190149000030501240078501c181070500500030104c0c00f14200e8403400d0343d20707035501000c2000100e40307503079000c1c000340c1003603c00390392030362805001074100410038000c10401504191032980200458040100950056a04840c0f0303000900007141e907a4190321312140a000b010001045039048101d04505c3e00d41c1468041100e140c404181209064014103459008200ca11002c906540e130009404050005842c00400d242b08103103090208590205064211604010b0f6048025256031091947d034000c0d1071613128035440c200b10743c440721300e441c041c0c6800c100d200da416100d0325400800e6050401414421120200b0000a28864007240510514014200d5403c041c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 991035944 1250 991034694 991034713
    0x120a1416140706031e051b0c150609090c09090114010305030316051329071109010b120f180304090b01020105070302160f21030b030c0301020a0516060f060e090708 72
    0x40750317103854551561700c040d500d0010901000d00071300c03000d0b04681440e410f03656034001003402030f6942c44400c0150181701d060002080b0545801030b0401d01440079a0000d0000318260003c00001d00c81c00307451204159620511003400c4e5401641060003540984040c40d2249041070000642804c00d140c0102003000c10000b00c59007510314104581074039017032071410b2900c0814506259100c5990980c0c90040e140215480007000280801400a08000e80c2c00e10900c1c1da9820080e10540111410702843e00803a4000400310010700440a90010f41c405203403a2001c4603004142c2036070710070b81100c03540700e40302d1520410650702401800e07004601860118940300d8014502c0b9024900010300408030700c080902e0405100541000c24050303105441440c85079208100b0290080401c03440c203a0081c0901824010245810f00c241c40e110b0171240c9a043c94008041c2ea0494203201c240011203c0c1541d5030701000c2c41405074881e800c044d107694038144141f405d0029602e841c2c01c4c6c1561000000d80d04c8407650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 991037194 1250 991035944 991035971
    0xb06040506060f0c01060902120402030c030607020d0e04180c0303020c1c020904020111030d060e0f010b1b030c010f0f1b020304090b0a080f031902120a141614070603 73
    0x116103042100d09412030704c49039404401409007034154007500b111070022a01011400400c1065805540308504a8450382d0b482024140c440c0d01c1298601c0141e0420565880080d015503806941080002c2000816456242d501ca1034400c0020003030b00d00307150341381c070034010950100700031002d01000300c0f0b900002c00701841d544d041ca824440002406a121900800c086900840c0e00b07954800001040e251240b04440450f03005042a00c140d03503028401d038000c1031409500d811420305940c140700940c0d00c1c00c107039803441e4290003180054884062100b003000d0000c02000b132056450b152455400440d112240d0300031642078902e42c80d00407040044031034a01200a070000116000c80761101004070b00226a0000101401c400380d1208130940600d119000c25203a0100081c020080150100c980c409002c01e0226510180403448503032002d020002550703400d000e00110065500d29440540c40d00784007081d01c00700c50301140e508540b0780819030304524601d4400d110180240c88117150411a04050441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 991038444 1250 991037194 991037197
    0xd0806030316080d11090109050d0203060703051e040503032509060f0309080c030a020d021612060905031903110c1b0619050d05061210270606030b0604050606 70
    0x218503a2070b20708240e481e0400c6007020684450045000d0200300140792440143d4256002030420340c0094210040231501e0b103441d011524026801030010562a596444140d005100c094a203d8041581108001c52500d01c0300fa9a4803d0307104101442d240d00300ba507031880b08000c12040800e442080c18689081682c2d00c650050200d45003454441c601803c40a0150010200c10300007420a400c0062418030480001000305080b40c0b02d582115509413401c6422030720f0700c034030040300b040c40c0390011004c201042c050f1070700c918070500a00c00001c8600f602e680c0c00346542d102c0108a0360720300f501c2405a001c250184180d8810442e6514910300d0188020915610342c0b4074000046070008594449030138035107601007500c030a0304083c00c00e8200d4011802e0060900d070041c030100c40328281000d001811a0410030034002c04c0e00000402062180711030703204500902024132206038443e140511300c00c074525200c3e18002142d4091a400548182542099074888000411450181d400d0105002c0e96446600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 991039694 1250 991038444 991038457
    0x108070509060304150f02070323070206030a4208280f06020403083a02030702151602150601050406051305090411040e2803140d05090d08060303 64
    0x7090046003409015100001d00c0d0034500f9498461011900b08c0030141c000a0703000d040c0f108800c4001042740c1c010b51040a900c10000c2c020f4000c2400c0c17010440308002900041007400321a12040345a03010100e24201030380d00341904818440800f04d65141083c150203251000d07107004c0b070240024078110000b00d80c2d80c021540c41c5c00213000c6403140342c0007031000c24a200c040c030503441401590386591303070300340f0b0342d2150800030105100d40200340c40c114025848070350b4a818200700d2100f0305000c0c54010798601c000c0d00014001410b50040c1180700719580e02c100c03051485804507806001110441c002c0091074070380181d103000c400ba00920140210360381c008050394200e50451400f199200c03a40301045042c080981d10094000d0240024401000300c20420540f0010080d00c00300200411a201c0c150f03500240b14040078960542d40003070031000c1040910351000360007410400010030b00f0f0a81c1074015400080c0445202c1e5850091048413801402105198901450701c07558034241a80000c1c1c6911800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 991040944 1250 991039694 991039703
    0x2210f06060a0e0d080408010c1101140610030b030a080d0b032406120f060103060e03091e150301030f0326060427030e03010b010f0504030b060a03050d030b0108070509060304 77
    0x101401076038138200d1002e4540e03844840541c40715074034071000d4042c5c0b01414680c40031401d2489503024585051040351003442d0400d50083c0c40c0d440c0c5405001e03c0200401d002001c054403140948019101044002825481003081c1965201000350040858042a1125100c1c1c0c000072180040c121400060064609140101c00c03020345481e0002030503807201300d1089010707010380801c1e45010b032008100c59048901032641404a2000201803a03102d00c107021145521040a039a004d020400301142100d8049007c0e08850031081c45111414254100b6481143c4000080240101f0590b011080b00345442c0c1c00103210002c800d45107490201d413a00100414090b41d075a80c400b003140d017141040c3c0703905460000035104080519003001400c00b036128007090301a41c00c2c042c0122055218010700c4a090500e5901c0500340341c21603607001d40000f000740090790712803a010360100200740c040c072a14140b8201c0e91000174501142c0300014000e000c00501c1c01e42407040c20300462601352285800c072640141e00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 991042194 1250 991040944 991040957
    0x110c03090f040902030a06050601020d2a14031204020a150f05070c05270c030c0406140c0111031f0302060a080403020a1b0608060a03051c03060902210f06060a 70
    0x800002c64014544280c01a605200d0b0081070018401140e104a0142034203909070f81241e000710900391180a804111802c80f4864a0822040d04022068035446c1314401d024031918001003840c00c6240d500616510b50f0000a854140009c52818612100041c5880303034400d005085105809040c201136618020148a000203280c410003101c0001c00024140003000050013020a0300e140403c6054007100d440d80c0910140401c200c00703501000d403031040c50742c411018a0f260824401f10760b4103c40c1184543c0d0070400b8000b1162568081c0a00019140c620424944030300c0c0003101c42482d0030981000256250b228041480541c8070b1104684d0f444005091240054540d440c3c1203142140030840170b0202100004035200c8c16640e030141d20101c5500b0b41d90b00c03285407552000c00c0700c86070741480001c0c5298030150b0344500e14111001c0d01020101c09050000d801d035600e02c1c13410240e0340500c080c11a5070704130f201d284101c105010748007500210b03d402c40307080d64900034001c40c80b50301c11500040d0078001d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 991043444 1250 991042194 991042219
    0x20a0906271a1908070902090f0906090112020310050a0504030f0c02150c0a050d03290307062f0a0605070503040f0605100503010f051806160e040e0f0f01110c0309 72
    0x14403c49030050552108895900b550b0f008107100a42000810600c01c2e00041d0000601d03184c404221400b441d802081e006840e4684280211500b155000803601801040760b4041e2511241c41002c0c4900c20401c8082800d14192400610213501080880709000070a0500c00258450585224100401c03052465944158401c1c0c0c0745409009000245548503d510706200d441e41a00107500e80450b07070b18110103041d41c0c0d101116070481c03840b101d140c15a01c00c1c80100201c8d80b040072605801d0104000803148101c40b0b11084911100040c01d844441e031105025200700034180c0701d511b500040c50301d40f10b421030506036600882c94461417009000d07036440c0c401203400309440c002340d14000d1100038000c01542827030480e0107001d031804443c41040c07050607480401c200ca001091443c482e2800e907217903080c169050311059038104070400b00903070001d13914010424050010041480341e80741a40042c1800c52241c2c00c2103081d144201002040381c4c1c0144044404241c00005448404508540e10401d520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 991044694 1250 991043444 991043479
    0xf0301140607060c03060509010504020a020a0b060a050d0f020120030a0c0309180e071203050f07050106050604090e010e070f050103330603051302100c020a0906271a 73
    0x341120142c549813402c0f0403d80c2e05901035100e281200d00941c0c0c03002080e0782c0c0d0710800049001d2480d1440158002c018007400040341244030903842000200803601050720381020501e0006500c10032a00c0381601118003095680000400409806885402c03c212100c90301c4642c9038042d96000c50140b1011301c40a0701010f0040764200090a41f03151112405906403c8803c040c0520f580364100c03a029001000c80c0b40c00b00610308120b89509620307098642101151410000d41c4a00010340d803a560ba0000400d0760b566003030040008101401000c2018100b0007403281c2101c09510080c1d40961081303034108601032420001008071035090030002001400507040460401d2603001a4a840c0000f2140b01c04041c4281c219034241c80d01c580d01007280e559203100f08400089007140c003a50048800d120214400c1c402c1e16805841031000e090a9052991281030301305540950b00100e2400080503030300c5c41550300e40c2d0f0600800802500040c4501c000d8924411400755560b40c200d401007030b082071070b040c451 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 991045944 1250 991044694 991044697
    0x903030807030603050105150a090603030813060209030d030b1806010e040c110f1609182003060a0b04110306060d0209010504080f0304181e0e01091509050c060f03011406 75
    0x1117410200034020b0b80703400441d01c07203229020940c0034800c00c0155004070750b801e0b96201312800d90754161a00c0500780c4494022060741c2400310300c22683c6a40802081400e51000d0003a895840665100440c4c40702009041080c0f0200c81e841e1280c0c50340ca04420000e1983c1e00c0f502d00350f5540c0050b94009400e040304d800c01c407085182c104276010036100c1c41e0320000c100c601c002881c92502019091191440382c81d00082002e454540d0b03a92642405089144008071b8110f40550746000c0c10b01c00d4000300c20b08101c001c42c3c18142d003110844006a038881220005040502070b031164480354050003851407800070009849405181500391f0340550206226103617900481c00c0754003400d000320499201e020a83d0505540b41d000e401055a0403012002035840e4070707085e01604001401e82d0811280c40700c02c1040b079800900c270b0342408490350f649071411403001c5440b4440b4402e21481e8a0004101460070b0f0501c2c52400c903c8da00d05034020b2000700240303140c1035141b009a906480d0040d00307800094983d0700014038107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 991047194 1250 991045944 991045949
    0x6010e1002101a010908070e01090c05071a01030b0901140a0e0114040b09070b072112060308121501080f0411040e030d0507091a0306040204030b010303021f090309030308070306 78
    0xc140c90301441d0140d2030310003c01c0e0301545400341d079517180d820707217801c1483d403145034a05c14003c44118401c014401240584c014032107911072440d2003814002191102c03584000d4940025600c0c0c580c55005209214a0621960b407000d04c4034002e100401d155101d00b2503a40004122100c80d40d60344270f5001d0240d00070341003903200380d00d500c00d951580e0a042c10302d0208507409036132a10082c0700340400000c10003002410340d42d0307079a00881010003180741070784070301c1c15011140251010004041c0301c0c5100e14034148102e4010354010002c558485600c0c113803003032074101e0141048a102e0700d441c690024582c1c0c0601103541c082485082c0c44401c1c0c48510f0a011403c0402c15220740c022b00303118620054250002c05000210b04450050005d9111120103450440e4580200720f5140100b01c1000d2030b1105210046030400c3d03000e440146803da60752112040034070284c2040340140c021403500543c140c500d40c0420885890741c0c504110440382590050a0180d241c07000500b40038003c0c3c00500720078000e9015200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 991048444 1250 991047194 991047223
    0x90603010e0d020d0e0d021f030e101a09010e0c0a0306030807110117090d0f2102040e070302090f12030d050f01060f0203070506060d020d081801030e0606010e1002 72
    0x208801902e02a444824500011000441e5211000380d00e00d0b100200f012010703006015602c050326400790389205100c0d2200410289511007003040c21020003000a21241c007065240001c5070f82d40790710703452110b0080c0e11501d40316140000c0107102400c0c45414403030b000f201d000e03151a0380b44010300701580039108030340c0060b040c2600424030005014030400310401081c0c0990714503028070704000030700045840a8443c01810b034403030307150001060301a80d502c22440166082240201c0a8046040d0040012100e5290801d4001c10b00300000c0005200c01a0441c800342825424a40d100010a0200544102d13940c455061441c040e40140024421201d91100c00d80c0240900e00c1c0c280f0000c1e90040c07003841080d002580c05005801c1091010090700c1015920401408280c1c403218100a410003499000303903400500002640000f8880c03e00602c2a0b40503400b4418814000d58005421604001140c00188c1c01030800c0050f03582e800702002c841d00c14100c3d100c0d0304213101c0c40b804900e8291803280104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 991049694 1250 991048444 991048453
    0xf120610050901170c1011030f1e030c0906071a150f0103090206040e1b03070207080106050109080d1d061204150204030b0c090d1208090d020615090603010e 69
    0x4620041541003005840041d16142c078184d9075511604880c1c905a05401040d80160178580301610301001d114880e8410391038043c080a41d402d0b80c950a540c028541d40c0310054000580a81c0702034241100115014483d03201c43c218613010b515440301c1d1168800e1148103d4000502c0c1c401c1140501c106109000c144404051624104c800c8001b0a50741020381c0d803040046c006400f030258403e015402110f68068603041c05c0c14a4982d080700a000041c1017225050031480b481032200c0e0a1001941c440d46044c0d00501d0028a00103d150840351190032160401401c44400d1005c600009072035034400e0708038940b6005101b01d1004140c900a0b420003d150b00140000d0f0901700710264860040c0554061080060101e21400300b120881c401c900c8010b001d45000c3d00001c04618008001c1e203490203000d812300c04c107446196280c40480100014800215000c0000d01280310340412081103440c0f1140000c241500b4400c00c84200c00b00012010f40c401c50306100021050703102034221219418002045072b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 991050944 1250 991049694 991049701
    0x30c080c120d0b040f3806070c0626043905041104030b0705161b0e0612071518091e0b0a05010f020a02121f14060f1206 53
    0x40e00584600103c0b54800d0b42090000741040341c5910410b810107101c51404100292a03140c402c4917502902901c40c046c0c8a1500d00c4020754444000501e038552040090641b2517080c504c016040200c905900c0c40c074011100f04102c4401c0c0520301035600150004840c210341c0b18038400340c03400d20100c0841c0d02180c912860040c0c4260010000c164261541120107100c24010140209414014bc1c80068941e404000126482c3c500034001040c18010800b01c0c140d90039016108d0856044040c50801041d44111008000e580941501260004000c485200c6190b00c4c14406990743c58181c0242d08c59030b294141c070b50700c400d07004500c1020740c403414480f54078084c2c1ea00c00358a4000d14544071544601d80001004401c040b0343c0744a00710306410000e00d10b051003802c10004403041940d00c81c0c00025449013210b00b00150380d42c451107440303416489000b841c503041034003422800d1011080041c09641c1c101024880c61400d02c048503a40440c041d00c20b040c01441440c0007032140300c80c0c608100814000c101c2070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 991052194 1250 991050944 991050967
    0x1c140f0304080d1b1101020a06020f0d0b0f03060402102709150b07080306280303020c040e0a020f0105040b0d05100b090310200f030907060c030c080c12 67
    0x280c07044038592416243c450000d00c40558102c01820b0140d00c0348040180c2040000740107000c211841001071044500107005a036a840c100d0b0b0110a0039524440085601403100b52a4055030448460139a003017809050b0b42c0020035910344020740001d21552611035a100f0a5210780c580840305942c02c812041e140c0050010b030340703804005000c1c0003400c0d1b00b0860700d180102c1d0500c1010301150700c43d00c0742e1494442d20342c171018804d1b0005000c007075020340c605015404580e110784070384403c0c0c036042550380044e6146240c041d1a0170710341c080040c0298209031044072100310201e4802002501030b41e0f1481100010001240d8a1140e42c000e0581030b100480d2101c5141a50352000b84030301182000196039940321500c0003068000d01c024654183e000d010940c00c652043c1c0c0000004030101c04d400e0700201c0496030361003080d401c69101c81c0c900c100b01208001002800f00301c1c010040c525400c01075005409500c00800001e24501c0180c600980060088858001000b410010010065505458440030441c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 991053444 1250 991052194 991052197
    0x220f020a030207122f01060b0406050a02101107080702040f0221070c110f0a0e010909060f020703050f07050a0606060507060509010606052718061804021c140f03 71
    0x90079140c4c0b41d021501c0320980d500403103181c801c4880d4071900980fa04481c40c3d103100c980b80c042c014402103540300c0d9400102951180b02400c0035180c180c40c0d098072a5041c01c0300929141c410658503512a003080b0450301c1c2c120040e011a030704079030409442c0e59508100d0002c01d0180100c0100d4000c003510024068185001c030080000c100c40304032103808415101d41d4011a000c054100000d0000d01e108060305030280351510078418803280103044000d030b456454000358881c8100b40d000400040e10303214060100302162143c030100e01c045e00340850412540d500c0c018500d01406080c030317001078800130f407003014450108001c5200380d80c040018848980c403400010303c00c2d00000400c40c2d0003800c3c140410113080041c050141a142e4655038282410b04049a0007440703e0f001148070052000a4442900c940764131245156900c4900d40c20251030400d40d0900c080341405110445402c0201c0e400e0000507510300403010607200025105400044407820030421601c2c1c20043c10046125501c03e50783c58803400310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 991054694 1250 991053444 991053457
    0x6090309081b0103053303010e0a080708160501020c390105030712050f060f010912020108040c1503050405060106020a020307092003010602070807090b220f020a0302 73
    0x16250840e0a81ea01c000301e07540d002140c251034008100c1e0b48146240c1d48250f103c164000582d01e00c0c51040c2c44000e00084840c5200ca460060001520500004a0030240140c10b0310469003002400703c00b50680b110b8100d40501c0d82d00402007040080e81e04040301c081200200c4050f0420021503449245440b6240d0340d41003400c0a05020000d0380e810803000c9a071000e420306c124003140c805004980b402e001140e0652008103000180043c2c1031030000340c6801440350710b201d42e86084201d106030400c81308000102c0b1809209034104041504203104101110000ea60aa42d0a00b08880b0325100c80c60701212810703140d040151400002d6000b004d10300d503d500010b024070f0165040d9201d60741c9030081207031202000b56010b034141d0f1110404100c101416802940400e0341007a101e024001c2880e541c9503030b46e000b0380c0854010b0380203440030301048805111100080c00110300c100169108000884e11000f200700c0400f030503540d000070126110000ba0000340150010000c00c560700c0b039001d4009002500f00c0b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 991055944 1250 991054694 991054697
    0xc0c08040e1e0631181713090506060d0203040506040312020f04120516030c1509050120011134050307080a140a0f081b160c050d060903 60
    0x14910b4040040c1ca50040d601601d000790100c0111035852484929944049451012426070000602002ca03c00d201d10640300b2414a07024600c500790f41424680d402030741d617843d0341d80724040200140c801609076200d001c40340a0724011a2650315a0300088a600031166604c40d402c0c00003003080704201022414610403803181c0c440e100804c005550100480c000d078059501420701c2000240304c00344074544000020f0384901c0032a2506061880d00080b011900d40c403c84180c0d070468401d102654110a41210003078052502207a01da01d0507000804911400c001c1e07e10507404200c00e040b450b0400e401c42c0040241000c80c6d641d035040c402140f66640c1c0d0780c0404440c0c1202c00340c07a45682e00c021800300d200b5165080b4005606000c01600d0b40d4090b5840010300b58140800301c0c0b502da5000003c1405400b110446443c0c4c800c040002402c05801e076440102065201040360000c200e950300c0032000d031005243c01030047c06810703000e40390000d035142c02500202d920040c240740201c20040311340c000111481c401d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 991057194 1250 991055944 991055971
    0x18140f0604122007050112061502070302030d110a030503040f0c140a0b0f07030e0d060f05060f010e0d15020904020c0a02180705031b0d3303150c0c08040e 68
    0x1658442c0802c3c0c08034140825942002c202004198420000d000c02d042c0e0124000481d995079810489210070350780d0545001d40c0015408005603d414040518007404505148483e100c403e080f603500c5400d403280080038000044089010722440d0400700116960080c0856103284e01c030759840b181d1030b01d020940380c441c031110b40000c03e4400810381a5082d400e4015416410000359590590b0a01d850780c02036500034a02414120224030580038407500700041c0d4a00041d18140701702444400c030080f540c100d0500424025541c03c035166510b00300802500403101c104024066215840a03100302103080e6070241c008500c0c942c9a00d0040f40ca045420b100300d500e000341c4024140050000c8208403106030200b50309000203581e050f003260300880120511240306141801d440400c0048a680000c810001c15210080d000306c5100c0a00e0098690340a80c0504080c51031940c0b01d041100d821755080e04410f86844490104034007070707007000314410b5100c5600c81e01c0355102e44ca0544017540032181501c18a00c2d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 991058444 1250 991057194 991057217
    0x51c050a03080105100f210b0d08040f0b0414210f060a140613092607140613141e1516050d05040f021e010e0418140f060412 55
    0x182200031460104d030b48484520003152542c034144981f14800001c05103854040300900ca503104040e05501c0e40c404c0a181d80c13030700d08000300ca200030003442c7c000130301e1030104000912090780602203490307e10740100c40900312201d070f0b041e6811010550313406100662244403c90140c80802040141c481d61001c101080344451100d49003200030b800f910001e800011440800c0300c0c0c45c815402001109014011050381c001048020008031103101d10b81c46440032000c03a401d0104081c41241902e804900d00081c220340c00c00104480c200c60000300001c10a490781c030240d4044400901281d45414900844000519202812151100f5120354100181c409640000c3c5034608400305004916a80340e4400f800c0110120100004140103030098991031072403501c3c00c005a80d9609a1303049500c41e1450003080788480c10000d0b09080c2da00311594452810514034090301e10107012101282350b00b00e02141461400c0440d864100b10503030341458024055030040100780f210401001201c04c549076030f09443d590 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 991059694 1250 991058444 991058447
    0x10091e0f05060f01080a06030503040b04051903080418061d0f0109090b06040507030e0105160212040b0f0702060c1002090a080d020d1128021513051c050a0308010510 73
    0x900450750b00c2e600160b02c124100540d440360311034562082d452500042c40d10307201d44425103541c1187d4410304950724000380500a40c2011046146403c0f801e800c1c1c00509030866580d031645004602420060b04541000700841c4ca8144d08008001c007040740e031002c2c001180d464021111503086502520901400300002030700360980c41880c801d507400c5403007040c00d03807207100401015180c05403a00c1c04058a80c41c1440102e4028030a2900030741840c40b0341000071a210b140641402c013803504403a80204284803c00040c5a2070741203c8003001c0b812007071695124544000b810071b00075040c080071184607400b0182c1864403a9401400b0443c0700321103d400d02c681c0c400e1072503555a284101e250040e0002c03402010305a00807214440840307400e009a402031100c003a2120742e0215080c44c41c3c1c130300c42e49a40c441015800c002c066090500c14201015240011141480d03850504910034680913a605034006041c09084c00045030410352721205403407540b4001d0038024122582801400c1c890401c4903581070285 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 991060944 1250 991059694 991059701
    0x506060f0c1b1f081003060c0e090109060f170f2505120c190b2a03070201090e0718080f0706180504050c0403050a05030a02070510090b0310091e0f 65
    0x2c00c0f0a40c109802441c08039412280d2440c05440c140820007901c0c0c000c400150140910200c0d50b0803030785e40701c21a40c1c402040124100303040e40040c4007180f410b5018000100f40c0000c00c0191034044c00c0141d00040e40901c201d240044255624445d805078109040e00031150000d4254420000e48031404469152020449011041d00c481105035001a17040b00050500841d4045101007080b16000081d40d140d2160a456101030205107003441918452655840d902c030351314071111034a000071418103480c0d90002c2c0c10b01c1800d000e00c408041010300054031841c03040074103250180d415140b0f141482d5941500c2680c5042021180105024080700815264810f540b9400d800b540e81c540100d070305161200b8880200000380081d03030940340170040840440c0c0c6c1000808a1030b0720400c02075a503640b58290003070420210360003d9100d124088607512400d980590480140c4024108299813601caa1b98040c0d000c02d0a0703030054000d1070802c0c0d0411040301900070341800c29112110184400400c040621085 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 991062194 1250 991060944 991060969
    0x10e09070803090618030a02130f0e120906071511070201020c0904020a0b2104050a020a080303070804150207021201230c0d0c050705100b0112050f07030506060f0c1b 73
    0xf02c0805d2010004400041003030000c04803014060341c80e0354840741c021649a0030f801042580094950703009410b2040030744a801c14031300c41d480192000140d00c21800580c0d100c0c101500f0b00c40c0c01d02144007424040e1a0300702180c9902c02d0181001030138000c44d00c2c6c80150b005004142d016000d402c01c1c0912905016581d0b902c240e50044c168181e4506220b8010440d0f00300c1c9560003920312a88040c0c1e0503002c0c80c0385605000c1e500034002044888810b1040065140e02c07504126501c1d0030900510035042e40058030140c116070700003100c00d50244c04586030402030081300000b0b540590300c2406080031a6042d40183d84000c007507203007003840d0104c000c02c8000e41882a54401d11420342040482a203001c40e50094480e032a0398900140703445007a0303d6040c900080c4641400c0303c0796441e101d100d03113076800825120280982c0072082c81030b442c1c41880545003002c0284203034181610745000940540e503c004403581a441e0004c0c00d52610900740300b0a60310380e0445003030030043e4128500d4840c2840c281041341c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 991063444 1250 991062194 991062199
    0x6180b1c0f0603050717010c0f2f06190e030702131112010f091802010e0d0503040504090c150201110a0507031e020a0218101406040e010e0907080309 66
    0x1040c003400d240d04020441c404510360701650368080400014821300c0800c0040000280c2c11000003461040d1508441002e0100d6007401008000f003120b5641001252008605804a484444201e000f09103800c026117500300145000300030030404204007103442050300010003a0100455143e0582140d42d921a40c8006903200c060102b20101c0c240c09030300044105500d002d046401c107840402c5804034040c0c2a000b80120a8005d001404102101c0c403c484150341040e981c0b1401c491940c00103001c060340404054000c42c5141c50360024040e04004540c014034002e40200803041c0c00d42822a088849806403604000361005c1c5c55501600c140240780a440a604910340b81090010003035030a903020750412014000104484c10800121100711109490685c002d0540d0f450980304101e50031000f1000c01c10b4401a1005002e074a20ba07030540102070702d440d890345040a0200c1d900064190003558003807040c982c00f44002190041d00d40c1c003540d00601240c41214244e5481325031441e224000c1046054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 991064694 1250 991063444 991063477
    0x1b0e07020d261005121b0102120403020f01030e0f0106140901240e13020301080d11031801120c0e0a080d020319030b03060702030913020705070b03071806180b 70
    0x303030616110b40d440e6001002c40c1038080c06984d0312404a1000e5001092446294010403441c080e00c64000c001110046424800707048640c00694498600340660700004e402481d0245d11407805034000d074016554100c050301210301c541d9540311440c2c081c0a01e4003580a0f502c1214400000c0c0307007403803103019069a841c0b040e00c0002038880d68000c0c00c4082c3d0ba01341c580c1000000080c00215864410b400001d64000060151341c940c100100917207030180d034408807002c111244806c0310681001006a84940d800991000c00404004c40122040020700c01000000340c50700b4007040c98503030000310030040210140c84280c881035a41800c503071190050010040541c00400196035803080310354040d0a8103002d824009011041400424074020b41120707280b0141e0f0001441403018031f8502c0c000940c80c41d03130030019484e00c0c856540c6c203900c0b0304c294131a09911400100c0800c0c02d8a00800c1c1c0c075000b988108800b03019041d5600e40060020102088052a10100d0340740408c2c040283d00071100b0344c030400325824 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 991065944 1250 991064694 991064747
    0x2130602070e0c030622061a0702130f111c0501080f0a0201032003070e121603080703050903190308100e040f140304080115052b1b0e07020d 62
    0x40d02c00e0f4002800700346d0000c00d900000e40703c3d41404c44010f040e1450998001195414a403000840071300b440542c0007400b07030a00c403407001a07441490b84a1003079040d200c0482e0b1010b004450001030b002211244420000104451400151a1182c50450b00b070f00003050005036a038005d000c2e2100c0c1c1e010596520780e0880b809503030243d40070340c00032450002d45091202070700e0034011850900741c105540c544c00081000c646071100d8034000d4151803800501802400d510319a03d40708002c214228030000780702c080e0110352070050502403070550302c1510016003900c0d403c040e08206c41c04803501d82030084004c20f040f80c000c00c903014541003a02e01034440503060154107032506d8403021007541e400300d41114502d0070740c080b086480300d05001a200801c030920020540801c082d82030844552643c000c4d600404400c009480344e4088003202001d08820440469a0301c4214144200d10300380300c1086516202130510300091030706e40c1581e5148100703020b40c25202900303454181141c01552041031070440c02410070a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 991067194 1250 991065944 991065961
    0x2019030608010e011407092907150515010f020d0315170601080105010927170d06050a05060a1b060906051e1509011a070b0c03040c1d0711010209030105010902130602070e 75
    0x380f981c8101c10007240c09c4c0341c040c1d0394049055095036400001542c07a00248013008181c041071280e40242401c243c40303404400700c4025070f100c50704030b080000c050f19100c031000201202e825505c0075203000c0c9c0d0000100500c40c0801c0e41d403002c0078410140b00b586040300000700e840503840741d40100103480c4908003c020841c1211044200380c0c85060b501180b0106c0e900915520100003440c0c0080134482c0820818a810304101e8649140c1d40018018681046501489030b800b40c08040f02c0b010403410668103800c0750030850000c101e0100c00511080c600740911245560030022080401c1c60342d140c1e51901c7c1c0d2020301c850000b00c159455183c00c230350003100501000c0e10300c00c840140624495200c50401c125502e4615030058155280101094000144414003c030408400302034100d20f5050700c944020210203201c0500c1c0105a601040420348130305003811002c0d01109c003841c2c0300500030701c200c1d6100c010407030003035000c402c0c202c200001c1420001011400400c00c1000c840005500000d2595103604 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 991068444 1250 991067194 991067249
    0x201050a0516050c04180203070504050c040308030705030a05070203090a1a1204121814090703061d01081605060318010e030711042019030608010e01140709 69
    0x15580c01d115040c0103100492400c00c402100860060b001060202d801806100031141d40d440c444032440c804006550142e1000507001d001c07035100f40e90010342c1ea901c0c8030b1184410b014540004004050010030701095551010180d0b00540701204c0400c407a49403050103a0b900e03c91181c031141c100901c44410810048507884041c0f0702d010303125442c0d1401c041d00a840d078511804076422504081d002501101032036102040e6201d01c10b642822000c000d080c4100c100c084903e8426180c45824444000740c0c1191182d00190700404d1b5200302c000504441c0d40b03d60b101060240100c052510580054040c0000c45403d050300302e0700040c0119103180c4a000100d11821126080700090350b40325024150500300802c010b20b500da024400321a011b5801104000607540415581d10008006640c006082225081291140544070354171400e19030801c1000d0300038114987c08078665500c3c040904a1218064000015007000c94841c04116a00c3c094280d038400308070302a03104000112200000b21248040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 991069694 1250 991068444 991068457
    0x90f030f03080a020f0406090306150b270a1d07080c120a0605060703122415022d070f06140a140307090e1308090d06060807030303090b0703051003020105 68
    0x840549170200c00504031526031b116910000c00203c0c034540030800d0000511070703880c40300d900c14001502c003441c0807409a0346000d040c80b1449103061200c91045005862200401c42c0e80001e0180d40b21180c2d02c042c403031400d40d000c540c0c81c032442070b2840025001d240f199034800e201d0b070300b144d60302401c084103203003170402500005240c80b01c4159103d07000300b51980c401d0081d0002c03501c00c1e0f4841e003042000d030360141c0c19135030820b0003501c503400c03800d45000c1420300c42d81004c3e00740c4a00341e11009012107044800c03071a00107400d9604482201009101422148a00180000200c014100e512003070b44c6000c411a080107a1203071030001000c01d210401c100e240f0b4001891a15164a450742680014034040e000907032013a030b00000840c0c0400010051204410f040d5540b211a560448454034400d847c5c2000c50700c21a8105e5205580300603c21040140a83c011030141040500711034001ea22464060001c0a56900546c0c8080c000800030f13605500c280110f5102d00c8002120041c283e00e183d005503030b00e80014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 991070944 1250 991069694 991069711
    0x201020703080c01051b070b04200a030803061512130c08011401260d11030705030c010b0f0a06023a0c0b01091107110303190e01090f030f0308 63
    0x1140000085840e01003c0e00b10600088000500350a000a44005034121482c00d046203903028080d40d00850030080072540e0040e0440e40854203602c4050300703c4642a000c0903150350116a90714080709003e0300381c003d540300d004243d070841000e000c511824902401100d08602e000d00c0e0500000780e941c0d5186e03018040d460311411120ba01607446422050075607072140250340450809900400900703140a007920f04649207680c058410f010903040e071603182c5c602400710b030061185922038001111130030401c0303a0a854021043c1e039100c10111150360301801d90720030780c2d901c68911f100100c40e651a00179a0401200c00c250010600380d009051a90440f182c4829055034074204c016500c41c092002e00740c1001c0c0291583c0d00c0620601ca24600525441c81c10b80161051601c0c2082c3c0040b00c000060403a241190495403000c811255100040d2440c8518615030102c00200c1c5484040f25402000c0c4448030701090300c41151180d1aa144000464080e120141c10854014003c9021034018400e03180c001100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 991072194 1250 991070944 991070953
    0x1f120201030b0a06021b06040b0306150d061214010b130b0a03170706060b0405010504031b0803070804080613150509010b0a0f08160621020409050a051e07020613020102 74
    0x7000020f01e498440c0c0e80706038096040400300120304aa01030880740b800c4022503500c2d08023402c0c00c80a41c0c8500004210f035010b001030401a11a5000090940f503c0c01d411490a020403601e03942c004400003c0c0000441d002c04c844000c01c05400d2040c0170720240c5650252403244000c10103216200907004681c00c04c0d402603800a0301201003854420302410100c1420300c842e42e185028600403040321030390f17440b400b81640140401d11a41c0c0e44007086408803900320015105552218903d034442e0126a84070410500c0001030140c2040fa001015000f11102242a1251540d41080300100c1c2c0340da0b140014204540360390f038804140710b10b038400e83d0407610260000880da1141303408540c3c600303580d801280014a407044c0c1000b8005082204941c00c03401c890038819441c4c64218050703c0050001406030300c0c03440c20040e01c22500d80e2541590002e01024500380050b0522040480c0240425940d0120600340f10b0f000c0040c1300103035002c0602918030b031760061100c2c0e07441804402d00c074a075000d000c9046004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 991073444 1250 991072194 991072211
    0x1b140d05150c0f0304061a0307080613080c03030a090311010e12070809100809010c140307050a02030f130906090236180603070501230a0c0218010504051f12020103 72
    0x300300000c4c51040c2d1041600050300c1c00303140101d00c1a00001c2d21403a104e40e10140c000d02082d0345c04661355802a0424000b4002e401445c43c06488a006030000c00307215101c00f05c2040b00d180e031650424441a8000c0e1038030600d928007406400d0980f410203c2c4400035900401800001460520044c481c00c2e010f9040d0a042140003400107801c03503113800a45000a000da4140600c4150a1051440b0322209040080d00c100c1d0102501400d808010002002d021004c640c44002c14000d1088500ca240c0700c0300c885503541c0442c1c20192202c0d0080c043d0021041c544200422070209a108860058240d007140c603280031041030031804083c1c007020000c1104440044c025220740c4480400c81c9040d1400e03445860030f4605041030500d00081d0354000703810030040b4180c55121854100c812404402c502000c5591500a680c0a40fa034084c9054003c1d0040040d16030760451400301e40c1514182d480c01c540600c0180c466004101c40e40d05086074403143e0f003d1040c3d081100400300d19054644e2481814041412417 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 991074694 1250 991073444 991073467
    0xa0e0301051005010305010902070c120618050a06060b2b0e011508011808030a09110a0308070b060a050112090215070b07090b0a09120f1b140d05150c 66
    0x201c0a0b12100400301c04200c1c02d00442d030705400f40301c3c0074010f00308003142002a00d46400a20349041e20450382200c400003202e00c144400303034015060306800f1050907020300c505032900c00d6542814580560307001d82741810128100c81d80604588040019005145042c00c07d200540403111003881d41c2210141c0d00c0c502501200000e024010025442150b5032140307600e000406800c1d201c0030f82c00714210b64100c102400004460405490708145d901c0000110076800c1d1521580741d0b40300c018015840509502c0000400c0013550007802c1540c4285000300264559030184040385082c3c1c014280440c00c200401101010954404d0351401e000034061841c8a0358004108840d81c0510420350b07030003040f01e00300141c3395008885a002086542242c07490502034044c002c000340d03154000e41307006954002040b4140802214400071154120003208040a6200512441916184100700304114280c0f14209246131000e030103000c07180c1180282160103a00b080701019070340c00404800020100f40032222004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 991075944 1250 991074694 991074701
    0x50915031e010b07170307080f13170d0b0a030b160219030e03060f040f0b06270703061410080601050d09120e0405090714031203040623100b0a0e0301 66
    0x3c10044282c5a43c410315801c14110460154120900c08141082400221940645610ba01c46814101c1c1c1881c2d449004e0002d01039084450040d0100380940c400b120303891090350041c856102c0c4004c040001041460610145005601c0050030030800c00c00010810003113181d02c51281001071041c0d40e540884801030040800512354143c0002e84110b0350302c011814200006070304034a5880064400340b400790344101c41110540001015580304c040440c0711034441c2462200346681c40e1403014146c01580403018030140303003243c00d800068240400068201d0079034402442081024003c0c5041180190081d5401032002d441c1c5030401c8010840a0b411040503c42c1c09492441140908018400b10000626024500040ea4070036031508060190b948000544030b01201c1844d04681c1c064110000000e00f032030280c4218020f101400800c000801445a02c8400f0304121b14003508550f01c0003401010b40c22001315441c40c450030250b44c00707118404000d0050105100d140ca000303500f002484c8007003030a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 991077194 1250 991075944 991075949
    0xc0e0a080d091d070c020d05010c11010b0f090a0903021507050705070b0a021e0102130305160902070804031713090b030d1b030e041107080408010507050915031e01 72
    0xc50300110480300d091984401c0c1d000003022180c003400700088003001e442c4001c1d00042e00340000d100b05003005030215240c00000c0010160010005c1107040700d44507024061080b00b120144e19075183c00d00035030b0b552403d1054100c00107006131074001030b5607400d4005401005107200079015032140b41c0010a556003000800c030b1090800d6a5107907150a05468014981a03d98006ca0041401408980f100a80c00205085c0a0070b4030f01004041e00d58100282e4024416528401504c00c0135410110600c800001c0c090414915450561400360340c60090f00200d019409006100c0101000304102048640c43c210b034018190160310b40c0b9140051891560300c82441d0b1126001d5503ca881801561400348980689800142010380e802045610110742c00c0d26005401020300441010111044e12964444aa003210044030140e075004a07050400302500702d840342121643c2001e0001d41e060740300d0800d85543c00c07000707030080900300022504c810483d04028581c802d158813605442100904e580c400600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 991078444 1250 991077194 991077209
    0xb060c0307120e150d1401092009011e02071d0601081005010519030207020a060203250209131103010c0905010e01081603271a090604020d02040c0e0a 66
    0x6072590585450020801c000201909016072401c4243d02c503214000915042c405944507955203880c84601800200701d075280e01c9074811840b0780042895601c42d440b040c0814152030b042c07450b149502c030403141d036442003802c101d0006440c1d5140d40c1c1510890030300c43c05441d10600566035000e850b202c001109010b00708030313106413988490034400c15582124651b90080489004070b000e003410000060110310400016408610f500400740c1c1200703110303038190390850ba4001c1000c1c1c0b0255540d00025038a8214840005984051184004500c800a0401d00c15140c0c0a403241d40ca580d125240301e584600c2280c2c0980e031200f06803803460929917080c401c5030000201a01c92090b52402c00000518050408900d5814004810148240c0503d0012407201d5806e0340d103800300c0d003c1007281455140c0303003c0c04e118a0020340501410300c1003084401c030060120b80c24000c1d030f5006984006031281d452400b13840c06500049902429070260034035401c03000101c3e902d82411011210000081200007030160300140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 991079694 1250 991078444 991078447
    0x703020420030403050d0515100f1b0b0f0906040c0b03070e0d1a07020a0b010e0603160f080610061722060203010e150a1502160902091003180303020d0b060c03 70
    0x6141841ca0b1191f140c010811072440202e1250300300104800d0400b81341e003001800b0f40304401c04c0d02103122f031b80890f00140d14282060314a011510f04000301a0f0140c0d9904a42c2c890100054140840007400e548101c0e00281e0071314460b031401100586c2648041d02c1c110802c807840f40f006086854440400c0d6036103104411078040801000905250060068420001c54201805420200c1c03004141181565401008a038007600c0e1075000030b1506ca80f401203260410881c01c0000f801100860042045500c910107942455480700b4400c0c070059820b001e91400306844103045c0385003100901d8056805808101e5110341210700d51224040420741d601c04850b1079070000010300024100000807a0404000c0041c0208140100c0000d110862140500842c450707241c0c00d0210014800c00001c6691400c01f40103043c40d507202c1607490b01a5100504032070062080032071404419200c0d110b180c40b013100030700301a62200b845a4084010354000d00407580915114400190740c0c4d80d500b030081100220810086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 991080944 1250 991079694 991079707
    0x8040f150e010333090c0903050d050307080412030e1915020408030405060309030909250f02031614030d05010f1d0c0a0512010b041e08070302042003040305 69
    0x500e440603000d240ca0403d42003018240301c1268405500d00c1c0c60300e08001e40c00000002d1485142c1c00c15141d4000c01c0720900b080071081c81580c00c04068402c0d0b03402081502e500003d2030500762080e10040e038108001843c0500000d0200d07886211407074043c2a81c0c900810301b03000e1001d1640c5004c0407c00d21824042091aa8804002443c040107a120b6191441982002e16080c0d0700740e244c2c001c911809006010004c00030300c2d249030610031160014001171102265003010842000e4541840816420101c070611640c1c04450040c01c241c001100940d004515100c048001c46200120051040310044103030640c072061818140040c150b662021007000070b46d9803400c07041008203881039010300300c2010307442114103402141c130b090030358480302441a0603a1850101d0301107483e441010307101c420f01c5411000104011082000500850b407a0131010a2004a406007011000c1c9642c0700d03030491580424001c10050800340c10050320006400003c000c22040f0500341e0105038800c4808030006000000c1c0c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 991082194 1250 991080944 991080947
    0x210020a021504061a0a03050304050603090a060f050a06060c0b0103020114040305010e0607140a02070303180801022b0c02070513020c10060501090b030412030f1118120a08070b0408040f15 83
    0x1172801101e0101d6041c1007851468644546034841c5000303590082e4400000150340300010441c030041d40340d1100c0c0801c00004125240c00c01060b00740e500c0d1070742d2750401100080c1107200e00098580542c00c00700b2258164a1a40156860030151401c0080040d003030100002082081c03103490110400027001e440075240c6140002c04065802d000201506400d22803180c1c416800103111003035941c14142045402102e40800980f81c0499000c400742e5030000a1a80209414404406140030004014200500c01d004601c095031422968180140d100200410061401f017048403000c240170031006240c5030224118508145a1002072090152a400b042045517440b02e4220003d10f02d94400c18114145582c65400c0201c108800c3c004141e100c80c1d10303000700a2140c0c84001c068003001e100a40c0d8500d1070b048041c0030050709400301d1127030000188104031030300301003041d00107180d0103007541d07160003042d99a5109189024205403104002480003040541c440ca20080c013902000700ba4400e8600301003070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 991083444 1250 991082194 991082231
    0x2c12120c060c0310360e0d05031b09060904020a08040c0e0f0106030905100f06050a050d0c060c050705030a030c050d020120160b0c0405100f0210020a02150406 70
    0x10a0b0302c904000c100b00b040100b0010745150a0703401441d021404101da500001801a4202515103102201e900900c9000c0160b540304108460400081d540003501105059825000464801527000c0d48912405a0300d0060310007440225001400709080c140f0002c04581241c000803940004255000140800d02c10781000c030400400c8a8100c6048030318040d0500388602d0320600c900c2c800d054a4840c45010000180841d00c03410440c2d10042066194205016000c1c00580c420540510111039002c150750808415180c403154200d80150000340c9089070440b04040c0c0840c0036550750250040c04a001d69090054204481c060380c1d504c0f00c006440d04026003819040c03a0010b082d03a05d06481141c007040c800d84d00c10b070b051801c282003a88607110040850f450f541020401000c1c1480b0000b00a4166040806030081c0c9400ba1a9030651031400c6a003034440c003803460004000341c0e2050380b100e02001803035002070030b181c078141c81513035030540d0130007a040b0026409031021a0304540b59030750510055034403103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 991084694 1250 991083444 991083451
    0x10c0f140d090b0f0112031b02030c181501090f050f060d0203131103010b010c02090604091406090d0921080702030307050c0310060f030f1a0703090507062c12120c06 73
    0x5000c0d035420f0005640c050410740c034801111002304440c580e407100355074090291120b031841c00b502000401042040300b8000001c2180c50007012402d40c000800154441e46481041c6d401d0702d000000c00c0c074140010001c07410001003940f584110100030300081100700d4000f45001c1c0700040074081380e81da4103207010039038a0421080c05020342e16205820500daa400a030034900e20f5015650210f8a0b01c8040c045405060301c04409071641c1d0303818161208036100011b005126241400a8585030983c040d012a0f0f01c4919208240c2e16680c4e008002102d104001c026420551240c1c403400e2800c0a181c0c0824115001070031305a6850300180d03020841410103210300b603603000002000700001030800c10b07110503100301c502001c0c265203044005081000b030600c114a0709c189890408010720310b06407800402030210301e80100c0c0c2e01e0040c0320303001a010780210000c0810720203200032009030325544d80610381d20328190804a90b0100e200a03045103070360f800b400305110b140085c101d43d9954068a41da45441c040025 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 991085944 1250 991084694 991084709
    0x302010614090a050901020c15011e0305120d0f050c12010f0503190809030f10060605030f01030f1b060302070204050f0606121305070b07110102010c0f140d090b0f01 73
    0x40307181803141d03480b0584a030f48210032610006054480740b80c5a40280a03400c000d00c55403040841d49404d03030000d81d401d40c1c1200c241941280d404142d185c02c4c000101018840144507500030241c0d2250b00440c4c3c00a0880400080f0001407981000c1710701070195a425603118200000014010454005e82c09400703000d0501002c07184c941a1a00c00031030340d2550500181c0c9110b4000b2a005020008400101e07481054001c0464048a100c41e00c015101c040744400209218604500000d0250041d4140c900c9a00c1250034400c841e861600c0e80c0c1c0000d01c0040702203c00b10b0b241c5070415a07008043e00d500c0d015008591b0300503154840c0b4814270044810240803c20000584020040140d0b5807204444421020881002c0e0316101c82d005944425207084004040b402808004200164108092b1400d070707001e100d648206141c40001a82210440805c180011303400c43c080401030b038050803d22111031140a019807a160030b108800040700d655100403070315121158148540c8041c03980c031890161005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 991087194 1250 991085944 991085969
    0x311010e010905061f0b0a030c0216031e051509010b1e30011406040501140f150f07050c01140a1b03050d1e0e070302060d270501020703020106 63
    0x107034039034035038400c0005c0650748095203202e400403030011700c0c0300844001e100c03c1c00c24640b104500240580500701c01074031000148100b825501403040818078801c00c4076004a911007500003855210143d8001d844c0c1c040c2c40074440e10b5625040d400742d12540758800c400070b000000c0d00013001e808001851a030425600078403c20030f0340c0c9840307c1c0d0324040d20301d400c0e1550f4210801d0107003040b100040e055020405114040d4a400a690191a41141514442c1208440401c000e80e00e40100006825880006903004080d40144070f0060902200c0054669084c00031142450a44a8000e841d03038000041110950004200d0036150b50304529801c2c207005100202904105041d80b00500b4140d0252800011246030808002414065402c44407080e070304420503c0340c8250341c1d40401101c2106100402c0442c82c16010004412002c41d043d425a94000c0403d4900402c01200001404810400400c49800d0751080110586040c41c400724076032103200007684032907050501908452096000b000c1c039040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 991088444 1250 991087194 991087211
    0x1002010606050421020607110103050a0903200c04150914090d0c06110a030e0c060910032a111501030f02090a060b030c0d0b041103130314070311010e01 67
    0x80100a03a0255070000c90300c956040140d441c48644c0d5800c009010b500140001400c3c0d080c00344094220f425400280c80030f200c6034440b008244229190440e0250005a4080312003224100b41200003a40418000403540864a1a0002011690155900403a80d80b151b0b03002c100a4909014110300300001d03109065652400b0004592503442c0000b91004016020704203c00304503480e40a42180d42c0c1c600001500c03a420b03c3c1003d401404402c40c000600d1060000003d141c0c5495422a203c0315000707005140e80201032039094010303042d0702e01e400c0b4603903070030100c03403050441051008240c246099803240081c490a900c058100b00d4400320220500410100510114585032003004550303034162084503072591078414040c0103100942018519000010900040a501001a01c0b030180b51070802c04c5001c400d0020441140d422411a2000030800d10018001a07248000b40408a000b810200140c3c03800d00b0341040f066000c2d00d000c0703001c50010f05004509400910810600560180003040070702c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 991089694 1250 991088444 991088447
    0x2190209070c0c0b0328090809040f0f020703080415050106080c07060209031f060504020301030c090c090b03071206080f060c03090c060d1a0a030f02060306010c120903021002010606 80
    0x18008010710240103441555004001114141100804152514a8490034644c161810b01c102d4080300304980a50040080340742000c910410002e01d03880403801d450a50341409000207840384184081c1103581d21841848810445d0004000192195884445516251a098031504404110701c240249060018845503070030103000758104041007081e545891082c035107030010384600d9000540500581a8034109951500c0c52075441e948568000c0c0140c680b51401c0c4401c034002440080d007001d654401c00c2007045c869911a040801661406184240d2610300000195100f80c2c1c180c00050304082c3c900503190142e1181c000038001c0300340645003000395400c11681e105400741c21410452400004100846001c010502c6c000c0d401510300c5407910380b940c02d26030007424801266400d1003141e440704101490090044420f590740450036418090301502030140d680c0008000d503052180a09240707000c2034120145500d00b00306540c43c00c1d0f07160b04501c103004d05019100d1170141568100441807019a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 991090944 1250 991089694 991089709
    0x115020601030618120908011109090c1e0a051c020c0a06050601110d020f060114030d0f031104120212010c1d0a030c03050607020f030f0306011b150606021902 70
    0x1a5000788000c18594202c19410380c03030310507540f4028400d811030006001c04c0341e00081c8640403540c011f00200061480d008100c80326204901e00c15030b11610382400031b031422100c90054a60b548017410314114034039186840e02c2ca10750001060b04041038010541c800102e8030040078400c0010406000c0d418145054112540c41200000c0281107944947c0098100c1e445211a0401c041640d01128025144010041d4859803104440c200c14080c8100119002d00b29654407011000c01034000d0140150081044a0860507800c215041580780d50540b41010420400780c4043c00b0004103844030100c0e075104100520b6581607540600c2e03410310304290b4040380c0090480002a081407080c0810b0044400002c140c98842c0e04018071003044001d000c07050100c0024080c0c42450769408882d152110003062030340da409407002c180d55000d020030000d401544955200012103072000d90b1500403581907668414040c01c0a030080303031034680d200410400240d04100d40c0307094100089142014052640116640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 991092194 1250 991090944 991090949
    0x803040204021605060c1b070b0f0f090d1112070515090f0303220f03020303040b09120715090906211415182a010203070602130e0115020601 62
    0x2282c0c04a03011604040741c4480e907040039405000c4d10031a10340422591113a40001c0b41c4a402c0048549241c0080790000031400150754100f80c1d0941412041c1d007180009038848190078200700001d20104000e6245c6400011a1034880c046000841c9190410f0002145802d5104003166108807001c05c80c03502c0b00450f115102a4440f8030b1503882d084034020070b4010040b00015034040c800020b5400e0110f1040091041c501e03000700c01a02902e5035a41901407003000c40c00007a40c5508100030810400e017401000740b11402c0c001c0e00d40328030ba9290300489401e121450740152850041400d298105551280340790000e0b20a030081000807a06080e6001a2286a19240d1501104403d20082070003c0488032403054803502040f508602500e81003246e0207401500c50415540c10340008444220020402049510f20100c0400d00d4610003064040030540035141181540005c000e54000b04080d4002071411021005e0880c42c0c0700d181121201754841c0591105100b0204280500d106540c0461004e04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 991093444 1250 991092194 991092199
    0x20a09090f02131a010f02030c06010e0609060117060607174003140307080c0a030207090902180c1c0e1002040f12030314010801050603100e1e0a230c060708030402 72
    0x852131780c41c6d010303881c0d8401e560004019101c1c2c04000294400443c4002d4402c0380c041d01e500b22551105001504d45010302c0200090645001d0005446400c02e0000b03420f9140c025201d84003e000501040380e1143e1107440c540201c1c0d0a13500800040022404001d0100300304111010020521091114144e1116020003400c2d000707041d41080c0460010001d0300c00c00341d040f03410146d803181c4140d007103541c99405200460250040304000030b40d4080c3d07403240201c3c05402502040b0303440b41d80c1003c0342200d14010114100c14006025141c40c50200e0b0080140c9114810320003d800000c0305600f42c5044407030940c414440f401048184100c41c032462803401199100144030414032010315094020f00941031031031a09a503002c000061741141500001d000b40c0c8280c054510a1081400240c151035807010780909940c802c54600c03001703e60300c11000081404413415114082e178103945059003001080058804401c4000e400c0c52110414040317000303040800c48040340341441955840c002400700034400391 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 991094694 1250 991093444 991093457
    0x209010e0910110d1e05060303031308090409080a0c17030705040303080a020705010f050703050a200913060e040219180902211609090807060504020a09090f02131a01 73
    0x255080e090f1040e00c403404203d0405001d8011001d072140d0618021250030030703e2500b88000310b100c2d0304012045134081c032044030400380c0c020011340b41e1091030713804409100d4000d0360707410704080407581030409002441d106a0394440c84078442c0c20b0000b0360241c0c070000400042020002d120805400c0700807a030441e545824410b1445d52622030080090088040140495003010329162151070154800e41c81030030300d602e04015070748446032500c04485000c2454550803840c0714850000b10f590384060113209100070947c003014482c0c030746940705032180d6034002c1d18410038070000d010451504409822400d4620292200d5052805040440c80f100c6a200514916550b41c1e2030420b54648041440500005083c1e0746001d10540f0303c060341d200c07283c041b41410111015404101c41a05008010040707400070140b90a10900b034035003000a00003e041240d000c41d074144009120105400703074207002c0380a00c0c0b142ca80c0d503101e0300500c00020702d40700c1d85100b09480d010040c0f051803824100324440b00401e01e00711 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 991095944 1250 991094694 991094711
    0xa0602130f260703050a05030a1e0c1e0206070506060319030e210a03091412060a05070c1a0a0f0203060108180f070e1e040b0f060a0902070b040209010e0910 69
    0x2e070410700d0b15000600507001e082c11b80400e2040000042c840c01c0c14075030b107201030121760140c0d41404000101462002a422a031401e010550340e241514060182402c0c29040703048503070010700780340d101da0000c072481c2e004601044950300d001e0110600001d410404103c0e601501c0d64020308400d440c0700380301d00c01c48950102c001e0080310520519100002c010444030480403504001d0301c0201c0c0c40c4140a002c842c0e95000c04005e0030040300c441140041000180420303192400c69402a183c001c010380300b0840e507a805103011070140308103200800300e28003020845003082d6010700e040d1040540303d000c14900400c1441543e0740d0062219912140c006400040c1c11880c040080c142891246012810300c610b00d408240800340100d442d001c0d07880801d1348180103c0e580b10031084070b042200d024000001c503500085050750000405035100100a000c1c401da2619040ca94040f07030804102942d0300c0300848204011420807001e00350142c010740303040c04400c3c0f0302108459560101c43d07a0a101294960089 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 991097194 1250 991095944 991096019
    0x1a0309070302280501180306020c030706140403020105060405160302091f090e01122d05060103230c03030a030209011e0206041506080d0507080c0a0602130f 69
    0x80038080c650042140b1040031006250a0b0035a002c0da008404280c10000c0000705980100d002080da4418140841c04031032440d11540003d4102e2403000f089400308200e050006080c51148034080004000e40b5401404c181c14002d084500003410280100e2829080c0a1001000104020380411910b805a580c913189408694100b43c144010040180320700300b050b001d20740000300700d029641010041ca1050f81d98411844164003100000703086265400900581c02c4001541d40c604a6107071024007110420035911940382950036817090743c01d155500f61421044459400b004d4600260000400b1810501e0001030380b00d2042003005028507900042c0704003148d0050001030743c07a10900d038030048180c000c01006901d0b01002c5600301d48034008511414620312051082601350343c03a000007041d0509100310305403410352101d102a103521400703020b1542815002c02050030040d00c20390740582c44460040115010031402d8120001800e603804007400803411141c0000d925940c182c52124500000844 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 991098444 1250 991097194 991097203
    0x504050408221a0726070b0115091e1509030209010905040308060d170304020109150f1814190b040803070b01120201020607080c0f040603150801061a0309 68
    0x1a0780700031040848840b440126121400c0342190890080304031108589000c810580c422130000428003410114170414040540c0c01c1c088009040b030015034074041c6291144c2c08203480c00d030b00440010b503002038805001c1d94890410700041941030036141d0074018660251009441da4080c2e11241c42c2507480f8000d1181c441c0c00907030011500a050050a56180e803500030140508a4050b00461000c0b4040f66131428205003410a1540140f00240914420700c4110001d90014005904019100d80049001d84440800b004900620f8940d074115030f501039000707000100d060300d0039002c401c541c40c4200620191603410300308031881101c15001440702c0100d0b07100da85481d0303000000580004140407648030400002491403d00990540886a0340da5600cc5c12803803940030002c0c016003051002c10384050141e80070b982c1044482c102c060811f00c5440040046401035031000d000240c951410a110600580090740034214000c0280315040c24019410700c07580c51007890f0025003100200040b0640802e12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 991099694 1250 991098444 991098457
    0x2062406070501051f1d1320090601080702070b030408041203080a0e0c100c2a05040e030c2a061c1a03191403030a0603050f0a03090504050408 63
    0x1045240c03100d074a41461402000110340081a1540101ca6000000c207411001e81c21108401c1c10030030250300380d40c0d03c0510400050050041842c00c1e040b0704001404075550a00401e0700c800040c5440401c08081122950014060a05112104e0188012580e01081c0c52040e5624103c44a07540e4650b840c01840c60b200c2d0794803041c03000e075048440f40101684901c00754040c54080c0010301c01b00001801d0141c1350010384002c113030300150a14016444901921403130241038041e04561654104607141c3c40d2245045915240070b04003001e4051000b49000d10440d014915140d000314100581e52000559584507030349108000304603c1c000442c01800c15603080c03000c0c8400780a1940b1500681146604030b070300e02d484601c1e501d05052440c00301502c500c2003c850f020300200200b07503070800c0601340790f00044100c1e000c0c2e440301014001c0d250350000c00c100460280000f6100060341605e503042ca1810440c0c264a40305103a04002c00140120f81d00c01d0342c00060344c1c0226400569902da030324189480d4854034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 991100944 1250 991099694 991099699
    0xb0925060f0e0303032e06050a03050703090c0602100c020f151f090207170702010903080c0309090103050c1c05070513020d0e013606090305040e0c09150307020624 72
    0xc0100c145c0d003204004582c510306d81142c00818940d140e007881240b280780900400140700b413000814442c03207074009540086542c02c0024210203180c8440c2c400483c3c13600020056070090140411800403481070754034451181c40a4840318000030b05494460741520b03040c034040b0411001241d00043c0e64100918042034980c1414651651074294001941041c502076401c200a4201518540400c4013103401f01d0707038161760b034030086410f55036840182c0d04006105a41e901c014480060107807580c0010038080c500840040c1103e1a80204000680030a110034a000700c00224869000803000a122001d83c1e20440d038031844800c041c00103d00038021134810302c503010b00b800d68801c40c800065110130625218002080008842041c01d5643e21000032800384ea8916852a801c001c103015612044a2074882e10340a0301e007640d01c1421181d0380006884c0102c0e010800182c1e00343d14a04445003050b05107080303c0850a51902c002c0103901c50070010700001c0010300c0704011009840200c0d681c4060040300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 991102194 1250 991100944 991100947
    0xc0a08090f032a010302180d050c030f011a03010b22090204060308130603020903070306090203030c03070312140c0901080a090210050d060509040c0303110c0d0b0925060f0e0303 78
    0xf924601030148950a0004aa907030620400390b06500c24001c032918140503480703502c181c900e014103000380c84107040d1094680f8011042d00301042e03a030620103400440c5003040042410010000c044005280d61091a8466807405a02c0b002580380c400d10308600312200000d0034485500c07000014060720103134400070351280c0f0b002d4020041092040c060040c1d40300d40c40c0c0700100c4545400d419022071081030344440d41a800302e041080041d0242c0c09c0b406c0003e202030305032410142c0b5910f0301c0f40786130404c50044020900054454085151610502c0001c40054a4510302ca05101c80148400c0c440d07003507618104028400042c50f82d0010f9000550b030540d020f441101d031a554620018a80d07085202a80360441c20018002810721b003010880f0b00072508209500c442078a150750980302c0907009640f01c0c1280c003e80c21110050360382c10100d00b01403801a184000207183c10700403e4203080881010700c014941e0409038482d8042070f00310100a40d812410000006003010b442500c22800404100780d15120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 991103444 1250 991102194 991102213
    0x1206090b07050d142509150306210f02010507020f100f021605031c1e0e04060e1b0a02010e0105090f0705060705060c0d0608031912020c0a08090f03 65
    0xa210005040c1c4500d00901009044404050004040c40c1611203a4500c203a8100d50100c010303800b000310000b85e002d410b01a00e81c0d41e0711403040542030003070980e803008a41e81c2d8000700b2003d05062101e070950640c1c0384000c80c1c8a030b00d9565010038803c0f50074002e41009808a00d04086442d9104445480c03100140201c04140c400382001b00584001c0c07455500501841892964480010952100303495005003c0c20792030f41e00703d040507603019081c0b03902e00c100504914118032104074044070390320f1140141d40c0e0842c3c2c1c076001c00901042c0d60003a4005010340012804010025054034800301440c040b9051440d540e803031042c0b0490240800840016580d440c001c10310441100000d070b0000325400c140e080e00e10242d500c42c2004414088c540380a003442c1c000100240c0b503050641c0c01052041010b5000040054440040d45d10359081801c4080f1a80203410502c0c0d00250441c003000300c0d84068040c00d615240380c19440302d0b1035043c5110010045040460443c0e402d654800f480c1c00d20340e4010707089401191 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 991104694 1250 991103444 991103447
    0xa060909060914162c070503060405010b03131104020c100b090603010c0f0309020d0f06020c010e0c060a0e040f02030405070303030c14030621060c13090e071206090b07 74
    0x2581c101c1210080d80442e04803198080115110b044d00d10f081a20040903454407a0100d0603103001c1000031005003071800850351140842420134041c80070340e1f541549a01d0031205003c21102c060300003039581c481c18820408480f4003200e031250101d034081c510440720b60308440410040d004040c083c0700903010f0455240c0c05403841c0e612120385c6000403111242c050700c0b5001413500301c81703440c502c100014000025101d181ea00a070401810316101420818070703066640c031020042050100304441c000c0d000182603030141800d000d45c5c0d2078003484402070002003003000b001a109101d00c01050061218104041c4440e80e10b960088102d10701c0c1c0c08007950f40b882e2918019031201c4450000302d01003880d02111100c0746d8420700c9120715181e0441412490346c1c03207000800200d58041e08008481100008022000303090522456019070903c804580c0c481c0440c000700c484825407a040513a00300c2c54014000600c070000249c0e402154904d21a02c86c04207102e0401e48068908400b0190080315030000b80801907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 991105944 1250 991104694 991104701
    0xe06190f020a2a05060a090501051c051303110708030301090e07050402070f0210090308030117210a0914130509190f03080c131809051014060102120d02030a06090906 73
    0x240c081100c3c920803980c540003001614042c50300717150009840f4000900044d4011001440c1e02820300d5007150a40d8034200320030042c1c406c05ca030090343c0c00c0208000e8408068200f52084210400103002e429542d06109003103680e4001481085070f0b254450100e04060041070004c030380607180c01703001555150000d04050b40c60038000f01c0d040f405040c14903503903c6030600c2010f0b20020b03254001207961460b4130f85038019014401880c2403500324010559003440107004165000e030b181ba6810785090315034500d000c01420b400c019074010307950105040d00010107640c0c0c111400c00240c8a2440018807030b10303a4924245010307050101854011200758000b002c2c050301904403000c0380d10940c1d071000140c0d0703440032000300340c001c941c106103020036100e80900c22030b954180c4034040c01c65900c100083d1a00c281d100c0c940781c42410b02d9201e0302c1c00d41c0c038a00c044440c1010283c01f68012400e0005180d06180c5100da150284501488020f402d41d0100c042503c0c070620f50000002840c040c00141301e0010300c1d045c004000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 991107194 1250 991105944 991106003
    0x60801140f0117071206060e040c3803040f0c33020309010e19090e0c0d030237110406080c01120f06050603160e06190f020a 55
    0x1008220070000502c807180d41e46002034541400c020f0400b680c68810350742a1070302031240448929844020214503c44a50040380c403603805581d40500c0146414002c11402c440002c000a90b95250440d52105018140407102803030718a500340d030740c1d0340c2d00ca08200ba0010301400004140250a4000280540540743d5507003810941c40081003000e0f8219501100031400d06e9002d0015030002e000c00000d40d80505102425581c01400415254900d0200325102d402950008003216590f01c502c0b603a03c400401c404540300000f620b1109003c401520003940d9030485000402c1d1040349000c030381100160000c0810010840134030740308483c021900d0a000000c00309042240240e1514030002a22100041c40c10740c03c3e0780603102c9006d000e80d184034103409010500c8040c0d520f541c441c5000900c0d81c032000000d511030000d000d4107030415030000f600200000101c1e540d662143c1c100303000f500504040c5580824241100b4200600038461621044e405d080200744060305281c1c4040c140b4521100c48d9110340d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 991108444 1250 991107194 991107211
    0x9270c050c0105061e100306050306090106080c0f0901030f080d0507030e212d130302210304060c1a040507080d050301030510053111030109170d06080114 68
    0x1913039030b806042c0f1440658124107002d070705070394a82c0c001150a008180d510426602d240106800d0b03140e10100385806401e43e080032107607554040411140509000441c12014211500040018880000f03048428180009001e01103ca401e00081005400407603d4030110002d050009250443d00540140321085010706507006481006502c00c02224441410f468a440210f09150070b43d12600341c510782242641c1f40e4000e4410302108a0200c0c0e03006408c070072603151a6804103a041d44184050820803080003400c0040494468540d280044251426a0100d28201c2e40035407050400c015051404e00c600d101c0e000c204418801444404220389060302d51017400c031800100022001c440600c400d11014040342c02961201d44020450b070095504028486e034500a2406408645070481c03804001002d9218800c407500401c110310b00c1f110f001406000c0b002040010304036103801040890b0940b00c920140f07030005070020130442540c4151302a004800007000403c0704000400e50042d002d54072180c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 991109694 1250 991108444 991108451
    0xc030b060f040915020d09050a051b1539010f0c0c08090409030207051e01020d03060e0a0f2705011505154b0a09270c050c01 55
    0x101c0c1402c050090b000030070307889951040c1440c082072180300250044020700701d61545070015240400d800308003404420780180040e00600500d8900001d0050482002e140201601d1111150454801042e9400c400001d0b8100c90002c50004000207903085841d019144c50218500018008005501810388002541806c01c82c0107010941660160000c6000038503134201000300075100d050035040b08000314420b00448207000c1c0c44000180c502417044000c8124001004410300640d030b41001445241c000d103040400101e81003034100300304039500030182010151200441031100e68940d207c49845072100b00700c00d403481001c40b848007a541020310255200e40c01e0844a90f10018060f0561045820040c00100a090b0500d01300646400446080c807441e403040703600e004c0c828641e00d0403d0008825036484080c0b00180d81b000d0341c4400c001a035101b00c480050085195450704811244182d1b0304404c991042410801004500c40050035800d13031045003441e1001c1c07220358110303020340740a006810090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 991110944 1250 991109694 991109719
    0x91f0b03160207062102130909050303070206060d0b011509050310090204050109180b040311070f060f0f0503060d05070815270705061809011e09061514070c030b06 72
    0x201c1d06151214980c1d641c400b20002d1700e8080700754640c010200c0c08841c01d030507130034070341c0d01e114002c01c031400240151100c0e000002005662030f41482503c1c0d001804455a0320290341584070160009014000e41c01811408240d40c1c08003405008400020030008080f140d90400c1c0083c004060519484200d01071400d000010582e00414002c04e0040c0342c00f0000e20051000548450501040c050002e80031700503408062250f1600500040002d40040c820001066150001c01002d07036030010f4200c002c00440c121928821075000044942247e41180d00030040c2099040c0a030405046501080c070324880c1d6038807041c804240c9220503110300d01c480354009036110b51002003d200606488242460340040d0010702051500e130340503101c40c10041e0740700007071038500d030021611620b02a048002280984840d91a040d040c002040d000f507c00c256043c0501880c0000003602c0c5076042129800b03200c51110781340c0780c2603548410b407103c0365000f04403010065541d0604011840d820745403280a650341e082070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 991112194 1250 991110944 991110947
    0x6020a03030c170a060911071a040206070c0312170907091109031615020f0d031a031006140d0f15021e0a03060b0c061f0807080105150102070302091f0b0316020706 72
    0x988d41e095801c01d15044c603c1141512280c107084000b4412640080d00303005850104100d43e00420140d0311801600c62188014007001d0300e00c02110380800308201084080110b40d8102048500840705500d002140c200b000d038554200d1400345154650b014440c408006c400c030301c0d4000c0d42404444200b80c640318440e002c044100d882c0d030a0201c94621950200000410031407081e03009103071001c29550f03174880c10450100040d0030301d07040c488120260b6031915000d028213021841c20140340081225800340c1c641050b60b03140c0281060030009044500143c20036007801c022501201c0d44201034140b50114118070700b00d00c03a40740e044094031100181c5468070110390034041c4422a0070108089008148603520030207100c0280d14403009101685130b404800080ca6681001403901905800001160529001e840134542c80b0010009130b046521103202040503894514419802c1103000d40051040311080581407803180095001c1c0c56400400801c00200d21400a41e0300b40500c0c03280d00713171111540d98000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 991113444 1250 991112194 991112197
    0x190302090415030503040e0901110711090606160f08070219030b0a0203040804090903140f0a0e04090317091516030e06090601050d02010309170912010606020a03030c170a060911 78
    0x4240345c0c0304010500c850380030780c0030700741d80401c61070004203403c0c00e0b1021600080d04148030498070660560b848084510f802c600342ea90000060b07031140d052819405607502c0141c84c2c090040c0a04001e00f288106000e080811900c5841e005481064250f1041e0000c115401c0356100070f50b0003100c003c000c40c000848900844c0d018a8216560608090421403510000d00400804409010340700700c44d050181140006000b10001c0c4880c00740d10b0b42200d0030080c10344201601000d101e145048400400a41c0004800c4604012003250f9940c9a59041004e454a00200626940381e01450f08000d030080c242007070b81000c2e0314541c2d410f00452400600044c0c0d10795094442400c5600b00e10f0042c040b60620424004144d40145801310f101105502e40305090403450700c10040b88540000c0d00a9107040c003000e049050090f0900030001d5034500b000c001e4036205446001010107444e6000c404041e44118007030507031071003001200001800e102c1e400500510052040350401030030003200078003451000c1c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 991114694 1250 991113444 991113449
    0x9170712080c0f1606030b031903091503020c0d052101030b040317040b0601080c130f030c29030c0c010e011d01140606030702010e0a1a0a09020f04050606190302090415 74
    0x100c00b041310b9400c144003a8050102030131b1064040c42100000c90102089441c43c0c2c00490280d280c400300039091118070070180c404415440e0a05004020710514400b00207200207140d00700b890055200d5000c40360550040c601c5182c00c02e210001d100001c814084000c002d00d0240e03100b1f49a19850640482441b481d034070040b1000b0b4002601c1c4800924294010310030b0652011003240c1d05803901c01c42c3c294030b1000c541e15030008400b043c24040144104044814503a0151515050340822141801d500201c1c45240f01c83c41400c01034040046440d01003000107644480d04010001d005203200810300e5070082c07089030300c68087d46000350480c2035104018482e1302807081a4200040d965a52a001d01c0703082d61015208004540d6200d001c81c0c02e8803402d000740c80c8194414499452030304402c5030100a042009019500624640f1000c180103948450310625083e05c2502c01143c039a0720100050039900070051b014010030008a00030180d1070b4143d00801809004850801500160368400212418a070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 991115944 1250 991114694 991114723
    0xd030906181203030b040e0a200102121615020d0506010801090615050c03040e0f04050d17150103094b1401062112080709170712080c0f 60
    0x2146010a04c41d400c08921000f000e000450607440801d80c2d540f40000701d520a0351400d40040211019101403a1480c0116009100900204080c201d162410b071080246840c0c44030800d03800c030001c2280801d4031070245c01c2e0f2a034085499950500b00e1101030b002c1150030764001802e0304004909078001e4440d000076500b00855100e495850341d04190740f00c0e40051300074400340c03006000000b881206031282c5407245855101403030b1241880e1415510b4014023544200c14030121481d40000e01c14072000890780700c600b40b500352892044a500680c014440c41102400031120000c6080c2c5000140c0745d01080ac1072880c440c2c0d03002400e500b10120303d07040d40604c10130003a114500c0f148041101041c2c40d990320134034507000103442aa904140c0340400c2a803042c0c140103000e83d010460500c502d528000c2d00c6591a401c21206a29002d400140f04020700d005025444101c01d81c41c1d109040d04024142c041d1811044015440c2114140001140c1080700e02d0006846074070032910450401040c2c132950080d00c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 991117194 1250 991115944 991115969
    0x51b010c050409020f0702030304060e030d11062d07020f0c0f030c0105220915080609060103261b010b0a12060b01031b030501030506060d02150c0106050d03090618 72
    0x10a400f01c0040d5121840d510b007a848244410005a81c1c240001c10041200d070700d480c800c0401d107000b403505088049034030005000c00350706800d03c114000f00c1e41a0340706034400584070105c050401010545c03510180c42d80c034294880410800e0041c0c001600b10364038407034807003100d003904422030402081c0603018842c00d070140c200001c104115400f90f0080c0000c40301740d04181c0d000754139050903000c6400181d0b204107161034445210380c0c81e076100d00030b10001a10070700c8058100341c038002e030425a0b645410311004124903203034025200302442001c0c0c0c0c0106000c80018095480076000741c64004408101d90600d404d51808240e02d0591910740c01a104648a106d503083c06100300351200310050458400e120706240d1901c4802d01080c00340c513910a043e8450b81c82c00955541541021440c14000904142c000e034205080c540141e915050080c00c0301e4403c1c580c465032140402ca08034050074155202e0360308070142c1d0f030320034003015005401d0009545150b6101c070000e0300805840303492006c07144101c1048110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 991118444 1250 991117194 991117199
    0x27061d0a08120606190503010303200307031202131e0602150703020a030225050d0e010509060c07210b0606030c0405060313080309011d0a0816031e051b010c0504 71
    0x103016a00303901c11001003604e4140f40300841458102d0706031080010020300d0000050040641052040e03c0258040f0b05003e40700a104035519540e1051090203010700024010140341c0540032b404a9001a881000c0500c1e85603a440c030010014240070310101c890b4080300008203481c3e20028082c0c4404000d1918000c2d5501c07603403c00d4000390701000c4c44804058003007203c0e80801d0180144014903109490100040003240e0804900740445210000c00300108001d0200f0903a034844262403044a003161060358401c0360800591030304c45c3e1540200400d4801030207440308051030700303107640d007660042c148540d103543d401080124511086482e401208010710084c0071a040c00300c045c5622103007181d520802891581c86060300c42c0c101710b4007982d450391292400d181082d66480d08032541d243e40c1009040304003260f510400319006a40f01003242480e1034a17020103161060322055619980680c2500840b064004000c0c15a03000c9032854070150813018032003903800014880d8004034800355450504050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 991119694 1250 991118444 991118467
    0x503100b0a1806091107060b0f031f1401030b0603060f0630071e05010810090504051c080106030b12060a1109130222030804030627061d0a08 62
    0x8040c01038602c03501e55490340410700b030105100300304003171748000500c0d41c80340ca4074501402507400c0c44964500500c0300b20494440c60301c00140c0c00c3d811030702030184034180c7c2d164006180014034401c24920300000340743d000001484140f002a50069009800307031142075654001d00c4500d40025181240c010310304000855610a0076510701007150540c81443c03034440640f101c100e00d402c01c0f0b0340020480c2a4010000c0210000b40001c4100810003800e000e4550301c0c04071004203172188184100c00352981c6a1000408000060244201941704507846c0510b04000440041580900b4010440428981035400c807080c41d04654115002814100401807a40d03500308403800b400d4856004040c14800f404030b5403541e668800a4400d890f68403400507103c00c6010704030a07046142101000032407402140502c04500510122800e60b6000040403508001c048111468116010417074480e03011460a15002c002c0d4a17005142185004005858014031036003c0540301c81c1c1046004040304c44c20000010000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 991120944 1250 991119694 991119719
    0x4052106040209070905090f07031a03060a0b0109051302192a1704180f020a12050603030403021f0f0e0d020d050f03041e0609060c03200f070503100b0a 67
    0x19410b14010403406d07610b0f004a041e9281c1910104102910030781008000c950621030740c05001e0342080d0300c039010050710011940314a80501070141c61030301e0306071100069014411040042c48081c01a203940d41e291070071a002900a040da203424511000e258dd03010610401d221184040c9000f00c2113100044409a05410040d2140848582c1100060210705601c0302c00a00300400740b40180a014042042d403d40460b041103030002e41031441440015003203903100e040d031b844103034404c600012551523140010340f41d8000c2f07900095210305180d2154035201c405551124032520603440d0204c0e85030001030b0907a665039407d40701070782260444040c0c10151810361425a640790084054900010303013400894219441500101407422100c00880c050004c0c031105040246010b1a01c841203500f090402011541c02d8000501003028201000c60000f0022060014540307400007119083ca03040318001e604c520451049910902501140c0260321880e0300915059000c001c3c220300e4002e0501402c038002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 991122194 1250 991120944 991120951
    0x50a030509160b0c06060307060203040e180a080712031a0f0d080c0a05071409011a160c29160f06020a09050f0414010e0916030804052106040209 64
    0x9034451582ca00d2110307600c158a45000d0700c4002e025903590840408418036103100074068034080d034445482080352035408402e940030f4038501c009201442e16030840004091041118400190040340a0801001040c0c030042940d144501540076215880300406e0707040b204003011038110188441206050386c40e00d4010000216402012502c01c030550f5107170100e89810200d013000030307548034561442c140542040001c0040101c2501b0710342c0103d0314004503003114018480c0f9511049902c1c1e68442c61070305801034030344400030610039420010fa1403c20361340440b1a0700c602c42041e0b12060580b0404410003400165800d26103403581d16040c40301e0031048441d144000203480c45451600b001002400314001000c0001059448441150800702081001c2117000c85d514401c0d03141c44030304070358a0040e041460441d91b0306100e16480350780e0050400d041000d1101c0c01d001000400c603000c0200003640b00031308144c1e42d096880710000351000e4070062008450b02203c03481c8d94800e000140c01441d20001e401d50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 991123444 1250 991122194 991122211
    0xc01110304080102181207210f02060c15011514070611040e09070902030f0a0504020102071206050108070b0708040b1c020a081630090b0c042103050a0305 68
    0x38155841060b5401c90304609024000c50212555046031441c103440314149020301c40000e840b149103441401c1b241d41c001c00c1d00d89610400c004a2000038011118242c44560760083c10080ea03804105590549503a8419203101c030069807000042501884400384800b01011a140c180002009052200c0706402c210340c02c4590341e44660340907501407654009080140000011a81141480044a82841c44903009200018810700400000307142c5403040c540c0280d00d548000032152aa400102e04005440c0c100403d0011090b010340c0400025600081c100e442c180d040c0c400454584041b0354052003080c0025000007814030051000c64508801410000900c900c6400080c200f172051100380d0300299241e601250b000820030268071180540030040e0025840e1000883d825003d40c04080300c010324204501408031a017000c001d680c0c40d8000791419030072104e01f882034a441c0b902035105074000d02981c0c1c060749246601c045100d0072820344048050f0f046e00e1f964248503c080d000c83c000c0800400402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 991124694 1250 991123444 991123447
    0x810050c040504061701061e03110d0203060c180603040203070b031503101b0806090a0c020a08031f0b07031b0201030b0d0b060414060607080c1e0303270c011103 71
    0x1007a54a91140800400e0b0305841719403001c60030304000e0308507091903011403c41160321240940030200c0502c05829a0340c0805421445c032444e801003801d40031003180094240c49002c00344520f5031790b1391001c2d00045d2024035081d412803c0c0841407210a010942d1700941645c440c040030700c141c265800c00740d1b5103c4a41400c80c42d41f55131000000c5e00e049440e06200300c240350340e02000c000703959079a03c00104d120658104440f0a00701107011074028000103101000c1260744a0096254610a1044501164001349d0b4075481e0708241d681e82010a040e01c0100c40207901d00440001c00e54100ca00740c40e030031798154444056281e030780040c1000440e004503080741059a60b841e00c078850340d60f202c0c9200446010300503c0f40340d03240190501013180e00380100c143d0b0181500b010402d43c0c1c0d4a91080310011039004180c00d4540b40d50090040c6000c04020458902c502c0c00c034000b21109100101861140c85034040308454100ca1000d1225115030842600480342c200d005980c3d115405281d200311010100003c9a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 991125944 1250 991124694 991124699
    0xc0f01021f0c08090109020d0b0702100e010509060f07050a201b0108100302030c04090f0b04030c06150608040209071e0324051e1f02100f060810050c04 67
    0x1404403a400703104040809aa07a1607074440580d002e10203a50008841000300040021a0006000d484021030000c1c505a0540c000070021442488111000c8807000418040010310200c00d03401703007004071040c0701c0502c500e2000551030840c41d100b0500691036501d0b114034110401404503003601316081103000c65030096250040d035120030405001e6a0360780d41160081200e1034000140302c5040502030100c0c80252000620159401003100903e500084030f0015400c111881c000720508050f4202500304807032801040300f85500f1050701d40c13125102c0c2d1030801000e4801407100580807100c1c022100010388400c0000c005041c0030b01350701e81100076410008111695030486013502c200c28a00c5000181e01c41c030500c3e16520721086000e603e007010704510f8010604080118024491032065003e80e18840801e88e46940c952014040b440091041c60488440c0701da04081d540f0500750620307080c804e241000d100c1d0040407034401c41041d01d0280c000742008018014484001e040c010340003452591040000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 991127194 1250 991125944 991125973
    0x4150825092414043f0f0605220b1503060702071805010b2218090b0f07020c130b041409150106090308071104110309010e0c030c0f0102 60
    0x25150b01541a911000d101c01514200500c20319009803e4480d01d04140024400709a03084004014010300c1c904140d000c120307405005400d81c01c80c0b1100691818003030500d40500c10301c0c2d02014a86801541d051203161500500d4100308140d5594041e42ca03c64010700c0400140701c2d80e1501d800c0780d5202d411142081000000074244a410f8484001603032050f030f81001241e040c1d060451350281d06c1c8204006940c903114246050f81f050885110002c010022038036045501088400041c1103c0b0418210042e59150404004c0c012203400340c2c0c03040300200003d400c003459502500e2050446a014041c1c1e880c000003481452141841c400844546605220b400b5840701d00c14000405802417400000341040d468082c1040f194480c15605030a0321001404165007100c100030490b6840fa0104d507554455040c90004c030000300c0748a0350300c14180107213200e2000f0828051406a43d151000708400c1c0b510302c003016501e104050702c070364158001000010840c900b021600c01d4407101030040d03404504a81a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 991128444 1250 991127194 991127219
    0x60906140304061e0501080d05090a140a0f09050138030a180f1707030207120c0e070e1314010b0309070806041505010e04020d0f060e0a080415082509 66
    0x19071404e0156260010004540200a059460041d5041c400d1030880440c000c01d40803200d502480341c0c9907411220480b241e456100740040100a40f402c810206501c8003c1840913003400e11490080800038602101c1280547c510b807120340c00e01c800a000782074000b41503c02c00c0c0e0070003000c200c00c0c156299510f9240f0620076044e4075425200b604030042d002154030b802001000b0750b01c0e0b03682305000300780300102c00641c0000d402410307036a02500914040e8500e1070702e003c00e5212030304030080d040052028084c0450f00518080d107000000c0b591900041c2014040e54121500140b4480d44031201074010070504060000a541100588041ea1222a00d4041c03191400f4003d8508407681c00544000340e4101c00c15103d01c4e4007401300d02021412034282600041c1c02001c8000d0058a8243c0c1001d04204012143d40305000c82a49803058400c1e440c15800c01c04035580280c803a50b145446442c0d41c80304054800c0200f07500c00ea1100281d410075900c1c1000300750b00250041440780a0011708100031440408100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 991129694 1250 991128444 991128491
    0x110307050a142106040303111605010c142a100e0d091e0b18031e06090114071d0402030a020304110411301f06090614030406 55
    0x15044109110602c1c140301c000394008842c1c265403401108000d03464a00855441d400c66010302e004186c010781c15460310494800d6141545204481402d214100007064010000c1c40c450b944500500e2a0041074251035441501e400444041c0e030700352082c1d4004001407111200d151280201c038a6411100c0001049511045100c00701d41d1120030001c003405d80c02010030000d04101120035000b4070303450b50407281a10a03402031980904c004105031440702c8034042e032140c040034002c00712100381c41902680340e800030181c0f61810603406101c2c001502d050050141468080001106030303144c2e44e17041c0f011914944034440101e208284141d502820755030b58000b560144001a0005a03a0305151034140d66190a403845903008a043c4041c0d660000030b204290703a546c1d50600385404840b9100d200c440000c050580c000410200380d601031082401d09100503003210b849280340501041e031500b03801da6242e0700c0e030310804001803100c501d02681030100001458006100d0080419050050b25050785003041c1035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 991130944 1250 991129694 991129709
    0x1e0603080405120106030506151917010f0b10181703040f0e04020a140d050604050c01020105100b070f1a04050d1d1302090a0503060406090204140112110307050a 71
    0x100e070a019070300e0318020329070b100b5944030020405e051656a440b901c0e118010304042c0c0e02e00c8284900300d1070703403104607039101c1d00f1999003072842241c2d4942c03455051010800035101029880d042509400808602c6030f041c900388014402c194560f690030342252040550544070540680c0b44000094004040d0b10254141303503100083d680340c03404e1501580107a00c41d9404071420804e140305200150301d41c002c4d25410354003161012140c4a07080d8020521100c412400180981302c0d09040109200340030402c1600d0000c03d0780207001300c0d105c80c0100c50801e5500d000e41544403100b0010080010f2005070480c806602c034003018034000582109100d81e01c04112401d4500781c0156403100310075503200e031542c05864a180e400070302c0540189c01040f82611710128600095500081d0710701c0e16920505850024900101103589514281c90f083e0094402580304034042d50a020703009007000980700381c05050310100c143c40010300b103e030b85541d0a010759080c41a81c0502441d0350101c0d4a45506034144054100c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 991132194 1250 991130944 991130947
    0xf1507150b010f0f080f070905031f050c040f090b0d0210020607020f0f0307030e030a0b04030c12050403080f03100807061d030609071512060e0906070c05060a1e060308 74
    0x10040003400440f407044408040040300c1e10440385803500600e442d90400c012040681260f62110000da5145c0317401e4000c15410303c601420502d22070450580072840b4a0140c006204d180c0720441101c030b440c0500d00446003a03094024060000c2ca8055124800800d001420000c140c0341540108564820304403410700143c200318200400203030100090751a122100c0010300ea140c040c000201d4890054850050030010135800c90b000300d90b0104030313500b00103801c60b08150352401e0a1078040c1070745071003280840380107241a1150f41da02d400760058804998009a089240078000b0001c0d221640c401810000d035031600c55004945580200401c0d40506082d403181050404002c01111040f800320403014820361000781040329452001c10204c0866444e141d00189407007d000c425078210070441c140203012440d0460000703603884145c0215015030b40e400141c403040c0e258030300c04035000008000050820351201000c16540c44c5e05078407000001181d149420302d004681d601d0902600d016500940d050b610 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 991133444 1250 991132194 991132211
    0x61c0f0f0c020d0f210c0503040c1d01050402070615090c0909050115031d010216140105040b15030a020411040305010c0503010305150a060504022b09020f150715 71
    0x340d100300840204240001c00241d404030704010b040d503184169100801c030018981182905600304001c100c0040610180300403c0702480040058104071025102c052007500e00142e460026000c1c02024070b002480f56103580e00b8a014400070b5403001000b02c8059641e1032407000c44c002c640b01080040c103400200850b810000880c000d110005a420944200e454200100030403030720400c0c80c3c0d42c00f004d281008180c0c80ba8050700e0111582c69000c01441d039500000b100c1e80c0ba41c07021030b410550307180f00350048002ea0072401d030349900301c46040300e00505c0300160f8000300d54618458451100007a6004044450354005e9502042c1901c0313402804002c0c1c004081003d20805c803007806600302c9003c040ca8540e08640c510b888445e0360350011405044070013072f000d0200d05180384540102c1e01401001c1cac025541c0c2c1d00580002514282c003228403c40c24007440031f8030399000b10140a0710142c543c008120f0a2250b200d082082200c1601208034165003008000040004078a101102459600f00700002002030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 991134694 1250 991133444 991133471
    0x1801020a020601030c150206130201030b1509041a030d0e15040e0f010e09030a11190506150303040b04210c03050a0b0108030a1b020d0b01080f0f0c06040302061c0f 72
    0x245c2c0394101d14844480d403040c05061075070002e012a030001d030203461540c02d0a00c40c001a401042011002a001111242508074010300e1a000307201c00001900d00b000095803409103010000301d480a2242e158202030401c200c214070070b810195190b80014025114a0781c2c0694000247d0300a5005d1400b9402d12010000051800d2041e40d006100200200702a8580340411a88078842e0310300420901c00041b080d1010418200900c40598142c0c0c01c614040302c425003081070b0f58034412140038003d4070007500300e2010f078100403040c2e504494544442d0ba0926052000070006c01e607490f00c80c04040031030341819a003c9200c149a2800441c0540e0140199007a5401d20218811058016441c590b00400c04003002c103031b10102e552204c50804000f00142a43e600c0001c0c1d01c104100405008503644c0d1001041c152004120003000303403c03003011259500c181c050410345641c08001200d6002605020030805814114010001c0207400c0b8001445501c00d000b22200700c075944c0c41001e84050340d0314031891101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 991135944 1250 991134694 991134713
    0x14090d020f0d02071a0d0c0815010e100507031101050c07020a0b0403030c02040b040e0d1e0c0506040803060102070b071a070809071a0906030109150501080903040e1801020a02060103 80
    0x1880500a0402c40396400d0019559101c070b482481589a445110100764401c040b007940d101d90202182030205407600b01c80280b8801d015641036008000a074207910b0650300a041c01e44207240c000d440b02146038214041901c0300d81181c401a018400a0591110b41140a108451041200031041034881c281401807102d124842d820070a0b000408010a2010a401807070140c0c40a074110f4000c21808013500114000d40320484030090707e4070500e66242d194503044441d07000190090304007001d180380b1610044500c5040203401820f01d400040c04600401d2100d4006c42c4e202c00d041c011500321590b0b64414580c16405507800b03407841e4101c000d010a40e040100043c0d50849550300d07150b985814a07200441d00c4031501e104e04212002c0e4400481c607500c000006580304488010700da2912136a40d104800064000c039038442d40c48811500012a40758082e0750300324012201c000007142014201004a00401c0028200c20310f1080304200d4020190024001000b00030b96541c06032038203503d940b810b20400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 991137194 1250 991135944 991135963
    0x60f070c35031015030b0316030501050c04050d0807110909010c081003120e150d060f0503060403170910060b0913021905031008150417090906010c050114090d02 71
    0x7a040c100305010500710001e83d03042c161589100000e016a4288a040c0c4c010725409404503098003600701079079a01601c80901d20100d9008030024800c039502c3c0d041c4c800451146004a5901c100605085c80100d9181d102408400d80f0800740f21042e421550002445854200c9016103117a4403a210b8180c91603010b0040c5070010044650114400d0941d40e600780c00c503240301110010025074448001c02c035940c0c1b811011a4052088400395603a089148001c00740209001ba03000891094400040500300055114803e030b030145d46030402c9011400c1084034112014002000078424140050407000062060000a0541d5201ca9a84580b01014050132260b0200600c0e8803500c103020340000340b611080b03003040d20421890269501c0d034034100101480c401d580c201c003c01d880365084110001c10f214890500450151014801603000c4481c17511652040401030368110f10001701080341940641151481244a0800459952042c1076090710010044410b01095400301440c0811960140150441c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 991138444 1250 991137194 991137293
    0xa050a1202300d031a04090309211403040605030606071403190e03162706090e060c0301051f0e090a1505010804110d050304090c0309020f12060f070c 66
    0x5941c3d101d0004c5081c5e1944200c0c090b024507121080281014420100d100c00740c813128140749484984c0c00a80920110352000440e0000341000100d400c030300c000800c1d10304a4802d503803410b00d90340e60a0107002c1140c10400b022220160b20403e10345400300240080e207090041984108010440c1c40d0006007161143d09905010342c021740501c0c241001c00b24900300a40d10b40d00c10359503046016107508003d031061000041079541c134144021540000c030b600407208401c04101190403544520b083c422a0b44001c0c403c1503805509540c40061440d0400c3c4420407242003800d109885140c050042408024115a114009030780d440b40004081c0050341c40c82c0c0582000e180c501d626160a0b6950080c0014180c82148180c5040c01140c003040010022100a804500e205010101c0c55080c05409000021001ca104000c11401080d043c1000112541180d01d81c0000f0001c40d15900500c8028030400340108042110840b0110b0108440c105114080701d1f0070054a170041d2010400b192844200000242 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 991139694 1250 991138444 991138451
    0x709090609021005030739260c0d0e01120e0c310e07050d1a070507020d02040b010905180a051e0f130b13030e0a050a1202300d03 57
    0xf134490b801451482e00c1d424505440700340010031801c4410381c105030a1f0f410703003c2240400d401f081043c031340a40c1100c840c81e40068281c940318000208820b01402601040650109503001841c504c55454082c502c0010304120b5a042440c0348810180c44a41a001229034084440d1041a0811408500302400c00011880450a0310b02d00390200786c00000451182603194486205003070004c2c0040b00040c00700801214201c049840c1048002da084131152480c00036a00008044034010001c80303210941c010402c241e3300790580d00308030052158480b41410001ca146022580c0e884650007800f40310707520b234818002850078550b04c3c5c041d03070390090250b414101000140f41401215154654200c110180b040482d6680c88900214140c4440d202409407801e4106108480c00105808072aa40c026550031110300610001c1c40030126040c851940c000411080420000c80400780311044684002d118515610a010450184490200f200782040d9a101c82081c11850200700c040101c2c102410300b0b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 991140944 1250 991139694 991139701
    0x1170c15070813081615020d0522091107150e0a150212040b090d0206160e011e02060f1b0a1101090606060801060f1d04020903070909060902100503 65
    0x464240200c41c03004101080100e0103043c80800b0040da18007400d101021102c1940c02810500f400c40c0007880f802889079680402d42e0350080c0b001c14007558004103611070328a0800089542d2240011001d144415806112004540740074240190308151800316242511220303d410000e90300e2100f00700c1c20101502d0041c04480700480451546080d40d0442e40100a8103140c4a440019119001d5000d0100d071582d01004100080e271481030340030344001801c0311141404c41c0000e03607070707084181c1d84003451920011315a0142840341d140e0790581c1d4010300d048243d035002e008010707a8a11222400d0000f58100c50b007000806a83c0c0c682040c0d216074000d440000300b0200d506445000d1003a070815100f001045050341c1d41442e0250011a0a15070080040180a03540c40004201e207000780280e10015410003140d00089105000540d0400d00980e03c0010b0800d00f541007000a40c040062240c050045100020f20703d41a84183c5201038001c400106807100548108a0100c200074801018060140b007030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 991142194 1250 991140944 991140979
    0x203090a060c0909020c061015021e101a0f0d08190302090d0b0402090631110d020a090501030204080d0c0203010b030307050c1008010e0406051b0301170c 68
    0x381000303a034004200103507441c40c0c14011189005142c004141c51400003d018412000014050340324403224002134146039107404240070704201481e5000010317840f407411030701c0c8a43da8030b2984400f005948112955514158400f0341940c0c04201030f0312400d00988100d502c070f420004911103640004541e04e107100701256440189074000c01c061348050402220b80901528041c2d4121854048018811044541549890302c2c0341d0808407000c9014008560214001d8101400b582c4ea0710640c11355410325410080b00c144140e140d005200c0502c40d610340c40815805007010004044055880c0c00161359400c086c2d42c0580100f0076070b0b000b0780c10548100030412509502003000c003d10a03180c5440100407146000080c094000d8000f0381707070306001c009064010013000089200213070000f956204411034402500750f0f03070b02100344209902d075010f00f400500055901e5009a510107408201030780c0161003207004000c0ca0704240c002492100c10030849918600c82080f04040c405022551b204100c07908400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 991143444 1250 991142194 991142203
    0x50c06130303140d060e0411011805041a060c1b1914040e0111070c0801050103020904170c010603080903150136090303051801090f030c0f12020d090801020309 70
    0x1404011882c0c0814903444100ca0840d130b2041507041d000e02000f034945003690304440c029039040724000302200166900d5402420001442018041c511111030725210502020b40054140c42c0004400c1c05182041e642e01c0c40d02a00009400400420b068290011140800100e0a05482c4a00e041c5171865040002801808040d034000702041c401d0701141030041800b804000406d5220b80d400c20104102861084001d465094020075801040b02d60303aa0165007280c5081c08040e4010070f4480005001c6504401c404e1105040ca050080c039101030400c0442c21507003142c008507201c540014500349145010404992500300d04110608254900340c1c030b40f14100100b142d4810440c4410024034101140300014103601d8400000c1070147d2850380c5002402010100d80030225501d100500d100c1800d4140311f46807010740e000c9603910050b200358170165004486030404581e4442c6042e00000068a841000154440d070754000b0507403a00c4281c005441e904141e0401f000701e030310510420090100005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 991144694 1250 991143444 991143449
    0x1409060f030f01091b1d09071e090e0c03040309120c150305130210050d02030f040501110a020705041d190326060909150c090301060506160b0a0e011503050c0613 71
    0x1304001040e00c22040501b44034000321900340c0c041d03400401c100c071741354000514500c160f0307084082100c0000c44030000e8903a072046000790b14880b0302e02000504045400c100a5810078007900300b01700c0d001d80d291a41d98081340c15100450704480008003c000c488074115031105040000d040c140b0191a14130504107030a4505800644140d1030b14000c2000c0034003032021121903d500b8041550b40307140080c1051000c0009031421a00e540c60702c0d4880c0c41c150015407d580074021668082d100355890501007001411074500a0003a5185890707200121ba1030402078140c1d140326100b109526100d0034200036101c4500381c0c08100f005a60b140340c8105203c492074140e40d001c3c8040741e08500740c2e110060a2450300320352650040a146801c028441244d9264010f0000c902040340280000f50300c480074412107009102d00800c4142c4619104c800140421400315889590301600040070301085030302d0b500350f80c030700308505078002e4103210180709201c070500c10101c1e000c1060301d8481c98001e0040e1114440d04051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 991145944 1250 991144694 991144697
    0x304051e0609010c03201501080105040314070305040531050709090e0a0507030503220e06130908030109090b060d02010e060a0c02090709090c020105161409060f030f01091b 76
    0x201340400400d80600710f041c9a4400c1d04400240c0103040c24800783d96503410302003ca0303c001282c2d000003034441050040520030f43c0e040d940c5081816002e0304210458018100840502505001c0400c85131140b03108005468503081c882c010054100181c0c102c0840240104000c0320b08000400c1401904074070100100e50618800141c1c2950950301542000c01c1030740000c101e4012124000244a130010240c07004003100c1caa000742107080030901c0b18030f594049c8504086415650b00046051074000b000c0e0003841015035010901c02100d90ba003500a5009070000c1207585c0c3d503800d51034240000c10340f2080e4001e0064418801c3d2021540002e8a0f982120110910540d030001c0c181000324420003004c248503074098600c5025081083c0e001d4820307015401341840540c54160095081d52050180c0390107100c04d1039880e8010000e0101c121388400c40c441e2040c0d80c40304200304203d803940340e51b002041e50355209181c040c1c07241020b9035218501041a0f000c0c0394a6400c10030a0b80c046407440f504100800140e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 991147194 1250 991145944 991145957
    0x1120c0914060c010c03050f090303010e011208070b0f010602010b040b130510030b07020607080a1503120215100312020615060a09080607020a170c10051005030f0304051e060901 78
    0x2840c0004070b007071203000d640201d15401c01c2001c0141e2601904601c0c000c80c403551907240c0955590000d240c2d01d01003442405240701c000701c01004101e56000d0f020940702d006e0408a03182c80d8180d11101d03c480700c00e0b075800301d2058007074004000f2940c2c20321034a040c01800b1202440140034071000540c3d0342c00d0401026010595800110300c00c075441d400b0078001940c3c480800000b6241410002c3e4851408076542404104000000307124503071503110b01a081c010502c00f003041d690030754031042c4d950301c04003484006510031045030b000d90090321001c044c0305000b002403003043c850a510b0300c803542d101c1c0f100070312302036512107000e020900d4044406601d010381c054030855100c26840303c0407100840158800e6001c0d00601302400061a030108548801074000e07a01c04052004401207080c0038414000050540e40004070003001c4159260040368104000c890703075071402d98407140040d09200701c1000c01c148560002404012a00302400d4000d2160034020a000594462101107072a500c100c480550401c10f9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 991148444 1250 991147194 991147229
    0xe060f04020c0a08070606090203040807200301060f031406010b1602030307150f0c0e06070305030a0b0603180708010506060904020a140c03090301050c18010807050f130501120c09 79
    0x11a503042e503509120860032601040410f0402e05481c0d4002075066400a046c070001164203d0035000b103901660313124016624099094848401018a9a0340c030310710100301e0340c03615003d503409000b054090241d0449000e0040e2a52418030fa204204031444c8509820550040184134a54015078080c2444910100300c001458800641940301d41c2a0040c400c03c2c0310400c16000c0000d650100ca9080210300003040b40c6143e142c4144c8000080d039107003550041d41005810300180c803e5014542000f05c072038011034151041c90000720b079500100d5424104060303513442c0046901c03040060000a041c0503008100a0803c0c1e00400e0003482001c002501464002480c1a40e05200b5420340046070000d00115440d5480c4141c8a5100d0348465800303807196003000c2c00f1400d10b40144007100d11044031800100c41c170815440040d9105440103217040c09008040c800c8000c43d1040b41c00800d48034003d1005115821b00348000501007030348010901c040c49240c81e000c10241030300121a031041c1e95201c05c0e4009201c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 991149694 1250 991148444 991148449
    0xf061005100f2303011508010b18220c0207090501060507060c050c120a030f06050a1505040e10050a0b160813030c0e0402091e071b022e0201060e060f 66
    0x20703041c0d20840803030000c40c0740f106010409000958140c07072000598414111030f00600303c500060a000e4042501805c00035010540c030f081c0b41050b0034210140038800f140300c040104403004500140394684283d10744102d0001d481d41408011f01400d160740c001c010550600030300422030701420a0082c1290707990321344520160b005200742c07040c445c00d560856180b440031000f00d1074a900300b0b2074104042800c050202d80b500c2442e00071001130300c20150040036900d207804a0b10241610301035440d014400204000326061710490111803144804102248030310307142905008211001d60b10001c20040148250000214616500300340160040f8081e41c40396103c499002802c80790390b0004120300314441c000030790f03c0c000540d05c0741f15034000c46c0c0d07500465841c104202c2d00d80000e00416484187d80c400011112402840c504082e210301d0198a402c0c00c6d030f0380d80825820031600001a0703034508100d9450988517402d140135196a031942c8000d0014520300310b0610040900900007601c40d0700400000e1110b40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 991150944 1250 991149694 991149707
    0x31504020f0919030605100e16050403080a11160e04140712141209010c03270b03040b070f020a0209180111040807091118210f061005100f 61
    0x900b00142055035035401c05103d150f82d202a84401c42d001800c2100140544040d42c41c0d42d0304860540c00b01c3e2403260358800816840b01d84c280100c40a00c041400048042141003015210b4401c0c00e0302d0b022142040c8540481c40d1040381c408445040d401d42000b400614041042d442c1c10039031006c60071a8400d4400613580c246611500b081c012002c3ca0980d21040c03141e6240c100780324004407000c1c0c0f89a034820f910341c034480e8400c014815003c9034a44168400007407090036040c032403002d40110361101031003014a030160f100f001e034040c081100000c001e00090002103140d40d5008900c0d8280b00c031074860003034030103921481c091b24080c0c420382c49580090b100c91210080c00010400c0c000c02049000400034500c40a500280a04441e510035200042009209031203007403010714190300b289090800c1000c0c0c5141d40310703d2448142c2c100111969040c500c040c09101039000e541018081c081c1a800105218600180181400003003240d01004024a032507400007210850703040d02d0304510201003403000b40e968 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 991152194 1250 991150944 991150957
    0x120c050a0303050a212903070e06100519110c010c0215070512030a020a090f0501080a182003101404081e03010608010e060303071104052208040f0b031504020f 70
    0x2800c1c00c12246c42481000094210b0304100c0a059940480a080c01459500c0040d402400d40101c4603030013080c520714003404116150101032400915188114451010410a01a019001c10990300d0045072900702800356148442003841c01c42c000100603000191845818840010124000920241841014005001c44010340120550b0b01e0501781d007400b000b94480d80107800000c050b608089001100321006130122340c0141d440171a1600e800901c440100101d100e00c2d20001c0904140d803000610700d4070308120705440c00c91640700d0841d0303550901d400c084000320a00001c5140520704c2c0c0d9425500d10140341c11507084509142c5400c0e00d02650006108140c0c91030405500200c000558280e00c00c82c10b6050300c42240e02c10009407560014913960340900d8000410510600740501c40c1810705900c0941d1082e00031001c81c0020001c0c1046155400400c0c40644069000242c1404005082c0710804c0040c088154140e10f90320b00070300540200b07042c0200c41071240b5000901c402c1c0031100e25065409 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 991153444 1250 991152194 991152257
    0x2d090506100504110a02030304030f0c050a06050106091401050f071b290c0c090c04090606020309031e150717160e040614060702030109080301120c050a0303050a 71
    0x5103060060700328804400303601c66140700d01e0910707680e1003032811035805544110342180c0056040d502e45640940700b1014160308242000101010b10007c110100801c0d020710707004600c0090154100030b00144407000b1380d0003916900710070840d81003a990f0b01004456041024010082d2500740e40d1904101000c2440e00c050140d60b0100d001003940d00d11806840f900c0501c49204800b00a42191158440d008042c00c003a003079003250341031100900340703903100aa00500c0040e100e40f81c191104141c80440f09550002801648041050285418200501c22450015215103812401e00a01403a03940e10070100100d0902c1040020075100340c081c40c2021080303082c0c00c5800d14585090048050700006a0714040005890108400d01d203040c10b100e03442c2594501c02c01c42c51442c0e0030001b4090a030348046000c98240d035a65080d0000b0171813540245000e45803299185100905600f4100040186600800c0c071811000004000090308002284e403542032038207200c100f0394245440c0300d02c605a400707961403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 991154694 1250 991153444 991153453
    0x151209030d11040f12030e0f040b03010e0a03020c0f0a031203020903030a0c0203150919030e04230711101e0905011d010b0604140307030f0803040b07032d0905 70
    0x8045050351000d40244e03035081410441141d030382c0103400400c1c0658580070700800c1c010526441d140c10805e8044800c4240948046138400a10340400c2c2168004520300300190085030f200030403d6814461013103c03090071240190100001000604d4285d01844014451035401d00700c241100d0290701503517104280101a80d4440241e9680a0410042c180c02284a406085c00c80c900380942e0020040c002c500318030007050241d503d000e10203054440340e0001e0f8148802e00c5424202c0c2e83d6940100454400c800804030320b41200c94020080461000d0508402e001c1005454041d20381c002810318802030b00481c010950b588007881e0082c00d031403e070340e039007148904003926041400415080341030503200d02c145140c0a40d1140300e50900325141001c020358000c008210030015503100c0014000700401c0181076a07002d507078070795408000d0111030307a0031110307104c0100410080c04007642d506640201a410207000701c0440c151032079503e081c0c145584403150100e00030407401c010b40f40d0003215034982c05070455 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 991155944 1250 991154694 991154711
    0x109030c0f0306180f03120603060e010f0b09070f1809051005010207050a05030a060506190f0e060609090f1f060e030705060c2e020d05040b0105151209030d 69
    0x100304080703103000c01e8420904008400103800d60b01350402401d2034100019402c990001d5404907240c00c802c45001d06c07020b48400010011480b13038451030104501c04000080d05510b5141c850090358107606506100b400d04a081140c0c0c6904007554a1700a00f1740e00d0700748608207440900c1c82c08581e040e005000098900f408010b90501803030000c40c2503131426000c071006150b41c0d100300104035a06026003505038100f201c01c032000401c00e410041c1c00c02002440030b111001814452103004486038456400510015403c01c0060a04c00085070412800c0e1007003850070f1101d2000c21b020b070102402e1801702c03691150020f181400841151003400024000a861035a0703905070081000310300140092003401000b00004881c0b81207070443d00c203400104007508a00b401030102040487d000c00740c040c12003400300740e00303000140248014a0bc503c60b002001540e420241866000448141c00090040442d091081d4000441c2000c1e606400c1c40c00703050154554a404095046000301500c10140505041c0107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 991157194 1250 991155944 991155959
    0xa111c11041b03090b01080705010f050c0705031204140402090d02100e0301020309010b0a0801270c030c090903030e070e1f3302032805070c0e0115080c0d0b0109030c 73
    0x500b96280110010141070347c889610350f88980013441140d0105a0501e50002d0050281001d400c108002ca0280c500695136500800d003084907005000d05160b50004061000041d000454140401c00b40d13400c5080482a40100d495001e2103140030f4030072090f901003034400d507128814030101083c000d4002d64603410030548080c0640948400c591044240c1c41020400d080d0501c605109001c05203850030a060305c1b146403210b0482501d0040e15503074120800800410014021000104030071080040c031001641002000c031140150303035414540040c2c0c0200300c5c2e04968110250481110a90f44070096000f9040e200010450f07403214440c2c1074905030440340880c5030a510508013010101a4030160a0f00908070303203d210b0448400203a6076440312806104902821559107c403041c2483c9180200c25160458400c5066210801101082c2c0060024000b54980c03d6104c40c9075081405503030401001034443c0d401150141e6a407503644110102ca00d82c411020180215003049082e070038036483d4101c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 991158444 1250 991157194 991157201
    0x70204200a030c0507051009080c160504110a080604050a0212161b0c060e01032a030f0204030b01090e1603030c051c02060a050a020409020406020a111c11041b03 71
    0x2800d00c0800d2511103030391480e5028900311a041c5d07600401402585070705411a03030040098520030f480a1109100e10480c24108005500300710a85040035a042407600f400c1109451124000703124440b0184030204a003504031199503045071003194045019a07400e071103a0000c0c010810004207400340321003440f410741c1c00c5016581d82080c182c1d6501c0c07031a1040d840020841322000740d004000181c2400c04100070f503c075007a604030140d01458003081601d050642095030b814940900b07601080c0c0c40580c003204a0705842080384a102100055040502e1034842c003070024814440d1006d0b4079150700300c0d411209024004480341c800880384c00a8202e0700c03800c00500d4095880000c880521608201c3c0904000703500c140b0700c4500c200c0d8014030840d6075542041016200242c0040c0300c0c280c083c0b0001c61101d08900190000e4100e42d8028800c1d03402c60700301150480c02e103461003809000542d440303991800041407a00d56054020900b10340c042a000003040c01440e05442c1e00190484a40b442803d0710780c181c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 991159694 1250 991158444 991158457
    0x816230d2001020f0903010b01050c0a060c020c04051501120c090603180503030f071215031b090c020c041d0d050a020304050a120506100b1b0a020a0e0f09010c0c0807020420 76
    0x20001c00241c4000401541c0e18030419807907401c280d00c40c14cc0680050101d41052100c4061441a164207082e8070000c0ba0946400342c61400b007249002d40240c0f56941e100c030409103040c0d006501440b00269045024042560f81e000d0b1a0415483d150580907040000c4024150964400102c0b582c916041c4001c035a115401d4a80034002615481c102c1d48d0044035005a800c449900b402c5920b5142c030b150f0310055080a030540041d00c802c003c0a0015401c034551050640075404c980151403d54003440401080340d032143c1c035503580c00700081281d60720f900000852222440050510550780c3c403440d9030981c50350065600079980000102c00125520940004034001948a982203030410703100c0569010035203003540203182e40c0241c10710203100202004603400d42d5140c003031030a803103400740b10344c002c90074620103900708000c589055024403800b140049010356209442c1c400070403060381c859400030803810540d0b030080e00c400d01c0400c0f180c1c1556244c2c0d21500050f02501c903401403a030340f8040c9a00345078004a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 991160944 1250 991159694 991159699
    0x301081b030607050a120f0b010f030e0a0209071e02011b03050f0705130b2212030903032f0109020306060102010902061e04030816230d2001020f09 65
    0x34540052000d80d9800d40844010301074035003030382c5001d81280c650704500302c4101000b402c805120365262452080100041ca07100002c111410104009042000c44c0c000c004109440c00708214100700d0b001c9000900a40e0440307e1030003d8030344c1001250154402158000b47d1007104628080b80f64055100010042d504141e11442d131040707074001d80445408030744141000241d00700051940b80b2850042507018a10348800e1106c0c0e484d401891440d40280d08000d240307070754143c035440c1c1400e501c40401d4010821941c005200d85440e44c5e0040a1140f644001414408200c29980c55480d07040d000e82e40f19000320300d040e59240c00070060907000c2d100ca200142c0c040e000c0c0e034000c1034440d44103004070604070b6000303800c040c81c0a040c0c44103210703071402c7c10345101e2481c8028030010000440360001021000892000294802a9400d15104000281c014100c10031a00c1e03100030f00d5540042506000c175540c40c03c5c9603882d40a444a91681400b8840ca100b1203540700043c2001043c0d25440500140c4105 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 991162194 1250 991160944 991160953
    0x4090b0102210912010f020403111f02070b03101205161520100527010209010c1e1401090506010f080a02151204060c0e030a1515031502030108 63
    0x1000d011002c1c50842c26008560100802c8501218204203410710304100080000141040381041c010302240c01c260001c03514000450005809840d0000380214032040b03030170203a50210b10b450b00182d990105ca100302d00841c0f001000003069403880c0c0b4031034001001580880c00d040020b500e846e5880e007100010950340c0c0603260101080c42c060500d031002040440342c485004014000024501d20500803811810a00c0360030300c0c0c400065090301807640035405807200f164146500381c40421521500e40032203541d41c0e10500c036031030301b90781d000b408526101d4200380c45e580089070800403074829080d0900090881e0b1145000d00000030360540c4481300545c002c005580159807a0101442001d00c1d0744500300440d0300280380500903141880c170b21103c040c0d410100e5440d00343d0400341600e0060013102c05070740095940030403940c916002031901140c400120081e02007100c0d03994840e110750b10300061407c1035903642c030f007040004680070f0b00c0c0c0302c055500640071851180030b2a250341c000e580240a0901d0074001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 991163444 1250 991162194 991162213
    0xf0b0306190317030106181a1b010c020f0d030b0d02040207050f01110a0f03050402090103060e10050703020403030f020303131e0803040f02042007061a0607030903060b0f1f0302090604090b0102 85
    0x2521f040000d4800c03003140c1c44621031f1070480c00704854100030840c040c000d041d40d041c0c880e410030902c11340340000065005444501400392005040100500c115070a042c01d00c4080031040da20090030010050b4119401038865060703040041ca06041e00c030800440d980780c0f50509440480040140031010a580d40e176500880d110305c42141503c409a8000390007481010061000600c0b54202036044c00d000411910f0782107040385007030305881d405e0f112200170950009081c404c0c5a40b200f007110b52008980015031031420f11060f400d008606844001c0c0c60543d130f40080c0344081414162900720a5000b60a480d03c4e401c02d0f0900014014a0700800c0b4826440c00421020100070881c21a802c0649084042c1c01e00f0a5038940c40041c01c0d02c2c2d9600100f000b4129040d982c2070340c0340c0c0050500f00740070341e03903001d1143c3c00e52500c2002c60f0107065080d441160a11420156595410301c0604510f03081f03000320454407200101913029020b17068010345d100a0105003c1888000f90384514500c800176422207402c400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 991164694 1250 991163444 991163477
    0xc05060a0518120f03150a06120606091202190902070309080d0c0213150b0406021f0209130f090c18060605120103020f13020f0a090f0b0306190317030106 68
    0x6190944000b481d0f8401d000d541c00f80c121510155900c4041d514000c02030340c01d80000612481c515030810000b04035081c000c075010000a01c50040980301310f040205000c0d040c0004141022a4400005d20806210700b03139440341001031000300000e2040382415901e442842c64046c1c00d0046a01907034041d480365414861029220340c1c003541842c0e40181c81419860310040c5404050301c130b04252154a4039800000090400c4180010b0005241e664080e000c40801c40340b03902d94901120104852160050084148d40e50303a201112610b04004500018000c0c47d803000c40010b400c840401921101c801d000004a490140001c05c118001858003084001c0d101c15065641d0b010b60350b09406602c0b1040018001414141c80c0a03c4c40600181400c0d1503d84022034841a42d1106102c2e901030360011510114158108038030401400c940105c1e80c05d5a0b051091011041c00020400e510621400b80240e9a40410441e007501031504403445051107010342110781c0c480d5000b80300b92000515a42032107816032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 991165944 1250 991164694 991164703
    0x14070801150b0f0309240402010f020c090126030f09010f021b0d050c04050a0615171618030606030b0a0203132a0f3f030c05060a0518 59
    0xd03880b014649041c801080d180507001d8200030001d42d030510660320107034924496011600314003074000200b401503140903c0014480c3d0200c6e0311403030540d80803000ca400680c0e24101c0d0320b81594290303021a84118821003801e601a41420200b61941c000007a0100c02660f420000b003090340407e80300d9413500c0703400c03000880e520301d0700450750002d0700c402c0f200e10036080c43c0600e002007015005c0d9048031710910415000404403282079403400b00180c4d0341c940400c003105544524580d6030049081c11007c44000c2451000b59140040100040e0703004440300c1910f10303016442a4100015031804104515241d02c3c000c002071110740010f8410064150024921340c441d030080302d102e070100707a50600e0903c00303550300e6501c608800c070400070004041d501103101101ea003503070010081c81d1084140074090300d0412051100d254686040c22099080602a40104422107914214000c4040c0343e0822900313030b00b000c40320407002c400c000303050380501424407040680603007090307005544040300354212440300404240d54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 991167194 1250 991165944 991165949
    0x803130617040f06020415091a0a080a090606030b0723030124230403020a0803030603030414300105010618180b100c0b090303010f0308161407080115 66
    0x401d03000d8800103001800660700448110702c01c41000d03040540301d00d101c40c00383c0e40346040c49000581454042080d0100001d10b064210500a4928502440400c0042208a005104040f5583c60340810410030a40e548031100070354001034070701901d00b4001c02c010810320702c011011180058041d02d462001403541c4c12a4129584080c1030b00480c2c0550300035003059401e0b00d401c60300340803200c940c0c44422642d0024460012140d5011196113501b588100420b21106400088450b80b05004003c2c46840020407501a03c2c951000c0c4254810001c000404001043c0c2c0f50080e000c00004110300c114102007001f04180f043d00c0000e00550b038861404a6509001003480312000395046002c12003451802490032400c0b00c080b0000c54244e000e040031483c80700c411640f00c0d00244400064405200480b480f01d9005040c0c1c0018500d19454000150030014250101a10003000010020400402e117a140e0389803c3e885541da54900c010540c07440d48800c0c0603c942c03070443d420058000080b8000d500320b5400d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 991168444 1250 991167194 991167227
    0x260307020f16060c110a17100506060403020909010b0612070f020d1e020102040902070c08060f01140103050619060206060a0b12011412010504050321040308010b0a0c0b0108031306 79
    0x2003803804100b19504c0076140001d58641400c140110001c0d112081c440024000980c18060790800301c92010307143c02107510705002541c0c90103082c001255103440c202d80450360101c6071700e010b60f10307444e40450050581310b1034540d00520004581032840b100c0c42840d4800ca4241d140c6a011482500d41640c072840488006000220b14020038080c005114009030704404043c40014180340e141d141e840101d03446034030103803100d8281e000c003001072010401c1602e51240e1324103e4030103154034200c0d81450101201040350305040c2c54200244c40c2d0b4840d01000c0ca8002006e100a01102c1d81d0f070f02021b9114034044d64140d009408a400204c0d6507161001110030510052240d205c140c0e00e401da4811110501c0f00610703034003406900c0c5140354210309003c0c0a0182d0b0091016503581d202c0800551040050700c1d40098555600c2c00811010a40208102d41113603244240240c0d6801c914000700c0303440030500c030000c1030400c08000104031140d001025001c0540c20340d01ca24112500d8120036030f84202c00e5514001d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 991169694 1250 991168444 991168483
    0xc012306041a04051e180610060207182403020a1a030f0405031207030209100306030816110a0b030114030a0b1801020706020d020c1c050d0504260307020f 68
    0x400c2d03814243d110030707401120f0180c46441c40c040000c6140b1041400d45500c1504900a0845166005e042c00403a8020384c080148605542c6007460183d2030341c0359881800f000d154034a0000c51050460b8001c00010180b0300080303000690303403824a5650460314041030b805444000800f042201c500c0001c0142c0f040300da10124103550b14200e0310101f5410052040310302d40000c1c42403020b28030480540d14051f10590301e0246c0c441500d01c05010401283c0d100e450704050810b0340c1000403074070740f80803038141660079615807140b46071504000e6030710268030002e07540107609040d0019102c1e60040185068900340708030128410480810035996141202026068514100110b405404c405001828400b121800035003020890345602d4103c0c0c00c0319190710303003551300020300803030006043c400802e4410003c4502041034071221802059402246480704149607035401240500c40b4840c02c914100000701c6d00160044004a1104072940090f144c0001603c9100c035005500440400d4007000190b01c0c5031310a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 991170944 1250 991169694 991169741
    0x7112a061927120213020a2706090b0a14040906050a050922320c010c05030a03020f0f190813030c0f020d0204050c03191a040c050c01230604 62
    0x9a08242074443c0403684010f01041e80208442207001400e6680c0d4162542e42a00d401852840d5411004641051008081c07500601c56aa040b03c854010307591840d801c01d0f1100480541540c1c10b07003119400120b403040200300082c5a124030303000030003134550541c1c4000342c490303403202030050324407050b02c850b416101d25520a00b5009418503094030007601130a0b050785031018100c0340c0d03d0b803008850120281c030b14003000400c0245000b00030000d0f1980e001e00c2c000000d02016220503840c2d016014000b402c258000829041c0d1040780019070f96285100500b450b41ca4108000c01c031006028070712640089a0220b0001e0102e0241b80071100c00e4a8040d104c40c02003000650382c0c00e140080720b0030200d0f0320982d10900c45002d612584076245c8180c3c09189400c0d500e08098184003a01c0c0c0152000100003810b22041e050051807501c0340b5040d010090303601082d245c5010200780e0741400b4801ca404100e40c07815080003840203038213088244107900c0304402d4025480310f005220960702203514500e41f0b1034009120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 991172194 1250 991170944 991170959
    0x203011202040c09120501051b030405060106030e07050a08010c0315060f0c060906020a121b0c0b07090803030703061508071b05030c0f0a050607112a061927 69
    0x848080d1114644541c14079101c0c801061700c1801500c0a0302c090b0354030300410084000080d20020f05011400800d400c42c54503a5620303969480501903c001c01d61140303160340013002c0c02c020b0580505002003550241f10b4a40202c80e00030300726032900301c00203804c2c280305170610a503000b46107003502c7c00355603400503c01c031624050b20815500b1808588a5683d007081c18042174144c800b501c0b80c0d41c1580e41c0e06000d41c034880d0302d140585007460000c045100d0084034130036015400840c00012980d04c00506070340c1c1e9440c058103440448403980500b600303000c000204000e951703041c0d0202040e0f807048040c4a2200003024801c6a1030384040301c074000801c0344941040e0f8844101d0701440c400301e21034001c0703e20385003206020302c0c14140d641d40c110b1409c0c3c2c007241061003005000d0040303c2d400035030742c58900410310407450781c142d8881c0c469802d5003615052006030300b491109241c07009007240001d01180c2c2e07038804505a502c0c04220441510000a09540d84090b0389540303600c17940003000071071803021400b41c241303202c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 991173444 1250 991172194 991172201
    0xd170105060c1b030a0f0501020a09060e181306020705070e0108070605030a0906290108060d080403030c031115061e0102030a0302250f0b0f040f0b131407090f020301120204 76
    0xf050b494454808224001030000b00b01c0c520a80c401c00001d80c40b07480c90341015060f05030540141c001d0290100c1d8000a58071421042c01504181001102264a4450f0039282a9501c4840a040030f400025043c0034024000703001c008941c20707000000004c0c0e03600c0104613164940c502524002400c01c20108041c4100c94201802c00c1d801108009440454125040f00100c0d46090f0105840c40c000782003501c0d581c010000645c03081d0180c840300301c1c565080c2d0381d80601d03101d140401014081d54041c224245849041031a074600061803c9507205404044079640c08203080340c141d84155040c581020030490b00d48c508610400068000f14200000c0000a03400b0b500a07507801c1480d60000304d045240c445421100c0c0070103070b018030070683c8071300c50608044074080001001c24220003241e00c18000002c9041078400102504404c1d4480140c03101e03000c0c62403c03040380d034014000360f1000a050840d190040740d00c4003121100750b420440f429858034050140d010034800c85454440007802200942001d40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 991174694 1250 991173444 991173493
    0x40311030c0306010608010602010608150402060a12020c0a170901090e06121204150819090c09050414060604140c0c031e07020910030206071709030d170105060c 71
    0x8080d564101c00800109140602c01da2141c40010480401000140e8081c03103038001600003240940b005100c41502c1c40b40c1a80041c0000303008032070025100315400e2082c400340c019009150810b565032407800003c40d986241e41042139586040005103a88808519011a000c000b41030f122504014030300425203918040041c441500702d140f150300c0034034408040c018164150715081c1c002d52154144a600040015030590030b405000c98030b030600100402c2e0080e040500c60043c00081020030f0223180c00b40e06c03111070b9808804514189420300c030412000d0070300380441c001c6a4040f2019545c4881c1004151401c101c4120001d80b68140030400e0100c1207001802d00804103c00c9910304055078448042c0c403004c0445071a9910700200d1560214644130104d10b07003142138110790f000c01d581103800140091041c114001c0c0b46c8440450104003980e9848240c03125100014240d540360070f0700c440050700030790f9820200040c0b01c1315400082400d240440c01c0c0c1c2c2486160030000c0c441c2d0400e0001c1c0354200513210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 991175944 1250 991174694 991174699
    0x2004020d0e06040b060603010f0b03060d0606030f06150605040605090d02090f09100c0518030106090519061715071b200307060e040f0b0a0902030108070e0408040311 73
    0x3000605218001401006880800c60004110b60710f444e080401c0c0080018101c3c0d4800c8008000401921104902c83e41c03d036140e8076091a520f80f03130342c40001d5080849900080003142002000020b00050394980300300c030740c0a11420701c80c02980440d450362a400c24003e010110700140b0041c402d8602c6800a0b12440b070002d401403002e988690005005400c0031910b002050048404200027560141305060001c0c00461040c0028100d00780c02816500510300e500b18103015414007242c43e5a42500b1440041c000304078100300301d01300040e5411404000403c00d004d040c0c10300c000065481040e07810b4420f041d000602511401013082c607aa0a1000e0190249003005404440c0b03484d00903041958211491154448401694407400c0780342034186400400c9120b9082100100001ca401145106840c42c0458001a51031000809031000f0007012401c7c0e500040c11403004614172807141c1c0114140c603402e80468000581d2802c0402d1411411070b00280a640c040c04104006070a40c030b480c074940c4200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 991177194 1250 991175944 991175947
    0x108010909062003011d0915072d02010605010206040203060117150c1801020f0a08130f1203030b0603040305040e0a11070303050a112706090319020306060607200402 73
    0x3001c085400301c1081d0740f81040300050002c01081491101c4c040341400c0c0840d8680c0c00550325100d04800e8548080d9042d03014510001b9002908003407050f000d02051142102889002d0100702c82c0d4991510010309102c00550310700350303001c1025800000e55070b02c02d1768020020421603003003c521a03400891003076118144d20a11104803085105491442c0c030514081001c140c880c1c4144600c540003a101130385c454103642024070303401384808021459980b642c1d00000003030750f200100000e82001541c1c603400703501250f12640021400e04100c810f0301c0710060103941d06220740284001080118481650002c000c80c00410081120070009600c0641c0400440c000146052202075040115405148100d0009590748200300c501360562040f910b000180280f400e040045442c0f0060042034004140c0c9125001c0c0d1001900c01c0d9220012141e030b483c4081c0c00d03280703038110410446c03218140d02c640c01c1b4403030300407180081c0d12070602c2c1003601c4c14190080c0300c10b0000301071003204224451000e1400c44d00641c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 991178444 1250 991177194 991177211
    0x170102090a0905041a06060702101b0c0503100b1c02010212030109050610030e03160f051203090705060315010c0c050604230409020f151303080909070e010801090906 73
    0x1030782514000180280c40c804166072a0a203044a5000507007110074640031044002d00446460b41010789803415030541740040620400c040955042c14404240842c403424071040104100749280304004646040d012248562030640c00c1d4425103800600194102c240341c808084140d07810070a0360315050060055500010700710b21409450b40c026005602260b8480c030502c07500e82041c5149844020280c54100281d0000526540c0c50703204108055a101d010028000d080c08800e03d210029298031008481c81c1c040718484d455841e4100711440c00c658041c800000a5034107115040381c1c401d2000ca81000a03040b0710000555140c41403000c1910500310030b2102003000d4450700001c0024051a10042c00460785184171082601e00e2002c88a024600b003900140c0107807a58600c4040220080324030607000c940721111142c090041c1c152052240540c00800002d0000880c01400180003e0740c1e01d0761981e1703404805696000c10004064001070081004101140c841d0380680c241c548200c0c000b08103500c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 991179694 1250 991178444 991178449
    0x30412120f060626060108070c02120607180f0e0115180f090f1e05041509030807030b030c0d031d060d0b0102071221050705060a0617011517010209 65
    0x1250b0350003c1d4003092101c0d0040300b0a1a4004101c1c54100e00742c2608442880c0480001f0050705010f480c25083c80304100d040170441d9150761030034800c600544c04880e8103142400d0020050b0710006c07418401040d0350040400d859a000310000d0a90381d0040041a1a92902c04940001e000b40d99012041105089126850084e4100f558004184980c00b04bd03401d03080064010494030000c0301142e0710703860321200d10b911190300810440e64a506000004407a62541040d44905c08180413580740c00c0c1c901030341c1c0020581c0104809001d20804d070b0381080480c100600381551541c0d00d0303c20592200c000c07084440000d103d0588410421b02d40c0d05140880c048660200c3c2c140c4d04000c600850440d1100e10b800025681007003058000d0000d11500b80402d6803549450410780211916900c020110300d22074100f9501034802c075891760740d00004031074007071a01ca00f66800a0410f80210a190941035400d50500403050144010002d100c0c24131106051412050021000700c1003948440f80d5000d210082495 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 991180944 1250 991179694 991179701
    0x42315010302010807030204050307050f1906050316080108030306041a06070b1b2a0c060403051c020607020709150f03140d17010302061b0607091703030412120f 71
    0x449101900011550551002501c0070f81c001701014105803042c0f00401c138503500060410122441962901312103030300080411000484001d200c12038411000340000c1e4241d2150045124807482c2d83c0c4114002d000758000c480d90072083c494074555910134000f15065141c00d42c02151142c2e500401042c5101004010072016000250243c4400140d10204052080030301c000b41d04186202602a1500244c49100520141d140d0a940c641c1c54a074154100052401c100b40340c24854000c1880313481d243c6c1c0e441c0c81a5600207607086da07104020900c141c5114140001103c900030a6142c01904c80c142c1007412200081601000aa14498001c1e00015100c1d402d8201c803c091805000c003041d069070441c40e00c40c9006185002a010861540074400c07180041391540ca0550b070f8121040c640e910516580d41c0c0c01c0d42c185c0d00c0354004030301540c010300c0ba81541020840e001c8444600300a402074800521071900e174002240e0243c0342c280700c0160000258441c1d180903080e183d0301000000d0401d9a600c2d0306084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 991182194 1250 991180944 991180963
    0x60402210106021e01060302090106050a020c060313060c030902011407020105040314160608010509180f01450605040807060f0902011e020d030c030e0a0c1e0e0423 72
    0x9600b081019004058900c4441c460344c0403448020300141e031955010840381d50052191a041100205125005500c00e100c0c800b005c03400145403549a0400700ea4807607900d00c0264003220303203500c0c201c11044590b01a0007030041144d0141c5400c4240007510000d00840d500141040341003050403c4044001400a02021400100e20b801007003101c2080b0a82400c014084d00180140490040100b1040e42c070003031459488901115060806058164902c0c60f14400100302e00840d401c007111038078408400300000100005281c500440650350f05000d0006140c076006002c0203e82111960340031070169000b40e9041840340312a50710b4071460380c4484085a00c1030401c64041e0f515005124255030740030004080d07134101000e2142004801d04006981c8002400c800b109050322005080c4c5c400340030b40e00c06161306050070141c07400010180f130804490213003805041c880b401d10301080382c04651030220410030f980b00d51844065a40300c60302e400c3e07271400761a22122881c000308a40b81c2e010741c0301032160a10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 991183444 1250 991182194 991182197
    0x6090906090c0b0f09010f1103071406060a030c1202010216080102030a05011508070c080f0a05090a06170a0203060a090c03050411190b090303190c03030c0215060402210106 76
    0x1080d48a034a8801c0000c64268042032454100740311042018141c0c501700c900c1c100c000d0030128042010008140c3d6050010400381049010200d0702c4424400c4186100e502c0d0342c603100565106a490104010005c5d25a010140002c0d8680318240324240c3c101304500ba001d030050044600a00e00f40381d07803c40d4095660810655070b5004001c0c01041036050198902514001c10090b55119050034024031040c8010107550800400607002c00510a0f008100c5d0425180107900d1595260100009080782c3d00000e12035016a482d401d00061440c810300804002400250100b074160300c4031010348000e500007412039623000104030800580c080ea1442922890f0708192804202441c0c1401d004400c540e031145001e02441c0136030340510f5406404060a0282d900300401c4680760108040400e00c0c40c040c1c20f4403110b01225a55070141c17455045014070030014803c0ea002c0c806440c0c058412a1140e8251030444e1640b070340c2c1e6003c206d1916154015101c00d5a4004400900361801010f90703034030000c00e900450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 991184694 1250 991183444 991183451
    0x10e0f01050603010b01080c0a030b1e0f12060415060506040f0e0708060321070f0b0f0901140c0904090611130b1e0307021c180905060a0b090406090906 67
    0x18060482030003010340c0014214000c00c50103210b1030001e00340c10b030010700300314254400160610041e80a6440000c0000000e0082c2002c0b1032246441c6610441e65000340b4400c2c804003440140c0303442c0010354000c142d00070b003000d40385685660351002c85044074011101800c03a140d61020805032194000761004042000f1405812468090f08100c3e805000c0d0040d82040411410810b00e900e000034031031003005030a81551110650140d440007240248400104074103680c0341104148222800c1640c000c0e00c002c0040d40301602d481c8030807070803a000c00c8244140c0003403400c000b030611210300014242000000d0070209000500d541e8a9084401c004441c4080b140d01007407116002009942c8030010741f880d980d10510380100201208040d1001c01e0500700d40c18000000100214400d102954044415040c1501c00c00340c003240260440710a40c400d202040c000c010f002481085a0007682e0040c0e40c00707000b03110300700c0c00c0c564020051b41c48141182d0f00036803200800078561102d48036050b8100e01461000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 991185944 1250 991184694 991184713
    0x50d0e0d14070e06060a020706080702030714010c0906021f0903051902210901090509060f0d150f2318151603050403080f0a1103040f0204060504060b0912030c010e 72
    0xc0800c040d201354000c0c002840340001e44e40c1c00041c06001d0700e046041101041e030f40c002080f03107176218141b0300607c441e551800e25440c0141c15000350740c410036251105503000d62200300403a0307110702d0040c5074407450310204180080180a075002c1403a05000b850301d07510b8032200c2d1102d042c003041d00540140060f0302c2440c0c0c40a6840007041540c80d100303040408030389800000d000080c01c0d208a0702030144149640004940c0c1d0760780d40540142e0001c4082c0480b40214400d05084103c20048803c0c4020783c1d040c04030b00e80320901c5500c14102005409040c2440c40300707001d40c0343c4000b10300c01410340d08040c8000c809580d55607801c010550030240840e807090528a8074000e00200700810744610000e05003804180000240c00100c1d20754005009004801e8130756840c0c14013006044d8410018008007800000d02003400a410a8501c0c200e000751810b110131b42e0760700c0a00003201c07a20302ca00d41040300e0a02c41d080715868440403240703000003054102da007004141c0c80610308450a11941c0361450744040704e10b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 991187050 1106 991185944 991185959
    0x70b0a0206180d050403060e0f150901050705040510050306042403050712120f02030913020a0813031d01021c050417060708010306022b0608010e010603050d0e0d1407 73
    0x2b118403681c007420078942070b45825200040c0d1542804d00007131000e03005004403000c4030b03006444901d684656102c00c0b1602d4001500f618cd2041d21040659047d402c07201100c0d0040a0120b080d15000c0c0c51461b141d4a062020740c00080e18010221700d14011030800417055030020010706110420403038044040342944904881c640c2e001209004440c40f440440c0e000e490b02510603124940780342c803843c210454006000d0030080000c4c0c50380001c107410b1071a02a44505950060044441d05402c040e804220310304c8002007800058000b00d0100710140201807646402401240a0302d070768144502c00070460641404041c00d41034002461410900500c0c1c0c007000c000c40760b04061a4500e62520003000988282c4c45a001c956080c01c10700000c2a2042c801c03002140d912200824207841c00070b030141c0e0030b100c03020074541c1c0c800c94820050340440d00c61075040c5150060703440542200d074200b500 = true := by decide +kernel

theorem cover : BRFrame.Cov 991007194 991187050 := by
  have h0 := BRFrame.cov_init 991007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 991007194 ≤ n) (h2 : n < 991187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
