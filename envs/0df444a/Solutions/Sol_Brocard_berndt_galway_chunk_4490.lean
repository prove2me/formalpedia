-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4490
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:47:14.874543+00:00
-- url     : https://prove2.me/submissions/8af3a041-07fe-4a1d-8c52-e31fb8031c2d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 807374100 ≤ n < 807553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 807375350 1250 807374100 807374107
    0x30c040b0a020c030706030603060b09011809030201060e01030b01031703060109090c0c1506230f0405091e010606030c020d08240d05060f0907030c030201180b1b0d1112 74
    0x208101c3c94422030140d09500350082c52400a070305030305600044c0544e0303c01d403014880da15800c03061010b16031007442854200500b008a00220a003030703a00243d0502d0291001140d85c54072000803181c1c0300300c02c0e80b0880350320404030700420600c440290103180420b03894040d14035600303050700000d103855828003800d00c00b542c2d1141000ba410740904415a24150b0100805c0e48442800d00c1c0c100c02043e240c81070280c000c40780e01d001c50142c40d151442241c0100001c2050503600045001d00c070050200a007450003911840d02c032450110701042800c0c0c00740748000c00110300581000c070001d06940b00e60304030f00306540c8042c2030700140c5500304800380d6001ca400085502440049010b550815286a03e0303140c00240004440341402000b08800b845400d208516040325162481342c0b903901c01d20362002405000031128103200542c425030701c107030b1101290210800103549490005486a000b9000c503002c0341c0d400300c40e251a007503080c000c10844035002e0904c0307444d1110800009459004400509a4225001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 807376600 1250 807375350 807375367
    0x307050d0b3c0d0602030402042c070b03010602060f10120f05010506010806030a0308090a0614041511090d02040207050319110a1a062805011202030c040b 68
    0x2540440318854000740524240e00c4030280868030401c5041c1d45000b500790340c1d9141040a1440c151203820504082d125003000c400310344500740250405001280c1c00fa840390304080d20340101c0d00880f19490404014280604c40a031f154600d4880107501482d094030051004021032a004125503a00c0041c1b100380003032076030300c0b001442e00d616029001548001030441e201010f0000c20110826114820802002140c940c03100550384400b040700c120f503140c0d0100303122800080c40b41d440c050708800c6030b40440da0350210301d650300c00581e80462148505a40448208000d0003184100d100c20842d03005800c01181100b0305042e03100d0300c1140301003402041c46000d10300841d12154100c2c0c103559007020607281c9131010040b032950f03a08401000300c400580240b5480420340404210840d9441c1e2040d4510180341c034822803481048030081546070710001d44010140ca0840c4080c0c0100c0c0d1007024415004100e042c0f4001403c28603504504000702d920502c20004c50780242022581510501c0d0b24068840214 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 807377850 1250 807376600 807376627
    0x702010e0d080d0911040501150c0f1e020f1f0e0f04050108070501021c02030a030b0d0f03032301080601120807050d0507110607030c06050a0204090519140c030705 72
    0x14100248164000a40502c007400140e00604c00148111101020000003004020981d2800e010f5103921101c07908282261502800c0046034a40c0f0a0300003940542030b50b11596480c1030380ca01084d1211060b0b030010740c214600b070284000c041c10111420300600e041d035065401549a1604400180700101d00e07464860b5a82c403040d46120303c00100148515a1078441c40c5841d0100703031040300e0144c4201c3d02c01442d100c101b01010403c0e0b190b51390007581091130009048018240d40c40c142a0400c040840c1600820a00506101070303038026100400c4042d114400f41950104a02d600303d00201800f00520100d080811924115040609886008085418084801d20440a00400507c00e142c52000b0290308000540b4045002e240030000e011131f0340052081c10b1041d600014001044803040d900011107981c002078000c0700756000181496201e00c012811650180c9405410f046508420781007a2064090080000c0c41200302c00c00b6800c008080100602010b8451024404007064241d4070848 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 807379100 1250 807377850 807377869
    0x110607030c08060306371104140306040807031d030a1202060106030b060d1d0303040605071b03020d1409040f05060a080c0a060807031b050306090c04050d0f060f021b07080c01050702010e 82
    0x1840c0e00400c0a4810101f1016060380144034510f00062618410304c035610740842d00c5489143c10000c00791618030315907011541c856000c403455540d144141d008401e161810804160070900c108240c40c000e4640082c064a4000141d01c80d1040504003114480c0f180c40e0070341075408620b407980300440c4860005c126665480802c40c18401903100101c00c002c01d00c400364000c0c0707000d4801601d84400e40d0307140301d0481001d00459800540964414006060340d01d1040707124000e424002240142054100d070000741c240c40c03501c04604411601c4600384130682c5071000840b030081608100070081d4000c1c074000300314030300500c0c42160705100d120320018001502a80040c843d004640410402d0190349100103800780c2c0041c0c9103540034002c004001601000c1000c2107a040c2d07100244280c0d48040d060780d441803140180f1504883c1c440e2140350141500d242400984509280e5030346c0d83c0c089281c2c0038402480c0036896448100580d010412900b1140d802c14202c2d0020703902860300140c1800e5010210307810700f4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 807380350 1250 807379100 807379201
    0x910150503030f0306030a1a0a06061d120a171309021e070f06140106021b03071a07052e1a0108090c09010308030a0614090a020a110607030c08060306 66
    0x4000080049048d1803104c41c5031042d03449640400c0007035100c520448003040d541c4441c1d01d44640e051107001c07141c41d20200c64000b03131041c80f080b034210b0f02d165600d440f02056010241042070b0008601c803120781e1143d1755504050880c0740411030510b10100760019038615542011103e01e6400545041403000b0140501110750f001a070034042080d000c090380e04070800910824005002e80306003103908a150a04618800700010000c0800c541412903903041c06401c5040d02c00c40341010006017000400600c90088100150307200794040040b2210401801c401c0c21401c0c040203490a80d290711018204008101d00000c01e01e4090441c0d0740c0c50704601c0c1381c0002102d4095000c0c01c490000410007510200039403140080174414448941d4454038003a4510740040466403000c59100040c84c1d412550740500240009440c0501038000300a4a0a00304802070f5107001c00179868060421526030401703007035074116800b68010a0940307014081d10301d805034000008640001c0064000343e8140c0354015564005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 807381600 1250 807380350 807380363
    0xa050d050a0c0519110402070209010603022b06060806030604212006190c020c090901020915030a0510080d0e060c101b0806031c090e0910150503030f0306030a 70
    0x42a981007540a80403460011103c1544e4240030102e00c6c101070003507038402503000c0c01421b000d0342001401d6004e90410107a46080f44512403169014070804490400200440000000c4440c10604010a41c6800810641c002d600c0318050000081450408800340c5008082c80140325103c1c140c11a00203190301078511514842c201c00081c00103011810b280035506030340881440078850000c0030260350808058070003680090041148a080209240d64044112000145060b000c1e1000690342c2c08041d02c1101c1c6007601104004c1c0341001342c45030316080b150154540400078075204480b03a941010f14810010490540040d81042c2c943c1e42c1036034140e001c2d1a041d600e401200b160301e40300415000346441c0511b1482c1452011071406814014001d80303005d4060240d5401c1c07e035040980d14541d07411442040003411001842400001000d4040c0e00240c003d00224072401a101e8145d0b0340c40c1089030901580f100c020002c541c1d001046945a0f000f6000840d140d5444900007800c260b40d40300d024018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 807382850 1250 807381600 807381613
    0xf012705010e0f2805130b040f1401060e130201020109150b0a050901052b0f06091208090d031104050d0c0303080a27061b02010507030b030a050d050a0c05 68
    0x98080c40400b522842c028a1600341c0e0f0f80e11488554a0709480d0341d001d03442d0340e0b00da81400c1c800c2003d540210303510004d0180d440c2024050707544c5a03484440c04803401e850640b035503c410b0040021010200000c960401c2c000d111550400500f00000c48024250f003411100100000c42164000c1d048a440c5a0301b04954030098060121440701500d0448030b01c074403881d0070b1500450189841d01c021030603244083c0482066204003803c3c40880300b1031142d52004200d6000c200c0c00041e0740800307403101403072107400c1c00300c3c0ba1354492a000c1c5000410030000d00138080840f041006403440047c00c07852090f20740c98042070180c1484440100c6104581105811214142c101d0b000c1c8000314403100c00300ca2096030340010721756502a604040301c81c4c07103214040c3c003940c11100c0084100c04911306007206018450000f40d82104015080102c6543c0b4250000350751541d003040000c0d03415210361000440d003980a02604d9074195a82034440c05034540701000d0010114040200c58458010510001d60141c2141e04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 807384100 1250 807382850 807382859
    0x1a0d020310050f0915100605030709080a0305040e0c0a020a0b0a1508030c0607080f04020f0f040f09050705040204031a10030b04051501050409110103111c05040c0b030f01270501 78
    0x40d203c100d030000c0c81841902d50070f6031000c0c0d181051034031400e1201c14001419040c000c3c11141e941c000742210040015102c80402c070a01c081c040034081038826210281c1c2d0750b10341039410b462003400034000700b01203100f4003071140c841d6004680384c20520b611807102c5580d580d448080400500040c030740c0441e000d0580740b001c00e030913000000514070028028100c070103550f0740040849012008581015089600d00c0c0450014200708805014000e8010101c0d0341d00d036480300224044602800c0000070481d1a1460003045c0041400b4810181c0300c1960300b5460b06045440d2001070059181c03900e1a00f4000c500001c203a15007440700f220142d42d008951500c1400d242c2802d60340c42c01e00c000c0c9082e402885030000209850203214588525610034400104440740d00010750040910744228415440c041109902440011030010780b0440100310000c1c0303a0909041c040505401038210000c40307001041446020180700b60b19a04444441044040302e04c445040c0d141c40c04180402d640800f42090004034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 807385350 1250 807384100 807384121
    0x110a080d03060905160212030a020d050c0d06150507020904060f0c08090c100e0108090f1606030e12090910090504081225051303080712121a0d02031005 67
    0x2c01c41d04060801d206a84071081c0a190580400070004056445443d01120b00e690640107158130000d40360b4010b0801100c8402142540c0e800c940a8005160002d00703401716402c14030a110107070151a0030030b131032418005406400c40c869228042d2040c81800c000a0400105400c0714000310041c04051140c01d01c10380d400742c200350060316403424034004d1500350849420612644000368519660344070700005404015244d50b0400f4280030110300030040701200c1140c2c10400c20032100c0d0b88007541880c803440c200c0c00400b02c40c4402d0302d00d212070300402000d0360300c86010b8050306c9884e202154162180d40b1110950f1442c925558850802c082c281300800c400d0190380d1020300027548160448642d5692038064851440e60314408408001000148034103103140300d24040c0c006408403215500c6969204c0e2a4500140c001c040200c1e00031000c01c01540c813050b030082e001c89800140e588180011600038a00027610540403103800c1c01050704050740025541d04004401110540c40800c120b141050360005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 807386600 1250 807385350 807385361
    0xb0406030c0b040f0909151812270e070e0a0801050703021c0203061302180913030e09130b070507140604030311070b18030705031b28110a080d03 64
    0x31941c4e4407440c18005070040c0301313001d194400740d84210140d00d10355146036032070700420001c5030003510070410310800400030702d01d800c00300701100c180d03194120040c48200400e41114040090f038040c4400c200800c00c0100c00c00d850307a030f0300403141d8140500c00300f0001004c05e070400300c42d0b40b00c0c1c2503a608140034030050a0b0558000d100442c8a0f90000c1c0341e005101000100b41d10094408540001b50b5032459540e84080b0341c080c01c480407402f4410000c0c0c01c52400041c40302c42c0d00740c45200300191141301603410950400c0401100d501e007a551025030703103001d03842d01042e80c02112002e0b2414030b010f1f000840c2d051040048400441e4003488505600060444a942c0c0b00421a812030109151480000000089200f0b0360260f13a40114982c0c42a92821080a100d50800041344803510007404910001384050025004540c400d40142d6600c80c090760980c0d143c408a0304052140d50800c0701001034000383c490300101d070290005000120b030300480c0042000e4500b070340e1005081f070145e405007807a01603240c0c015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 807387850 1250 807386600 807386609
    0x3051e0a1a07020c0a0803071103030d020c060f0a0905060c070503120a0c0807020c0a0b0c071502030c160608012904090204031119150e030601120201020f0a150b0406030c0b04 77
    0xc841384100c02200b40000341145019802403a881400340c07000060305404042a070340000b0701540e0900d8400354000c4240c0e00b091110001c19082482000900414038102c990b00102440042c00035004a481d85a12500d010f0a6000c5000c0002507110500408000311a4000150180c3c0340451800c60416030080c00b610480c8000108070402142d0000c0c8000340900d91000c00034005000355191080e030305400c8c2e20082d4074224900542000103100c02d060b10110103c110325402450f03503000144071340c03410207075009903000703400c1017100040c80079980c0115102c0c1500c441c12001080201890000b45000303822003242d1101c2200050082161011a0044c008072441000d24018003400700c0100a440c45c510015402c600403e010308101c14111460310320010801810086619039080002c20b003007040c00d0700000b602a0340105107404659040100d0202c5544200140100031f00d580c0d140c0b00c6c20101041804030031a10395004402a030f07140c0d80400001c540c01000d000c0030550303807502c0480300d4001e03105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 807389100 1250 807387850 807387853
    0x1b160602070f030e040f050c1605010e0a142a04020a1b140c0405011211060708210717160918051609080a02040221101e03051e0a1a0702 60
    0xf031103280040c00e4018140103204c0c5003502070814049000386031400c3c1e41127009442c039649500c604420b5010500081541d28040c2803a000800407034116039103088562403040303040c071000700d080514070018100d0f48050300000b01d60261780c69091140c00c03281309110a03450801409042c1c0001c080150030b65982c80f40f0500942510749000d450300410084401c01d100c0d10b1004088117034480005035060f444400110130081c85142041002c0d10307502c001d6040021280a40060005144040280082c12070750040300391a00401c40846414a040001c8000d0b00c1d00000404071925181030718060614500603103414040c880004c00000d04a40203003c0685501c00222140540d80d0300c002d10a4410b04290b0380d2010007000d0300d5040350700b40f0009510108a40d649070003c100c41c20540c0b141d201490b80103102d0f640006038060301340505141700d17492036400d0400390000d00e50200002800401d6840b0300d09107841680380094214000d46080c00030240d001004000fa02c400003882001c07680c0b02a0080340c8550 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 807390350 1250 807389100 807389111
    0x210e0306070212030a021b120403020108010b0a0e150c0f010f050105120d08070203091201020a09170a02060c0c0603071d040204270e0708151b160602070f030e04 71
    0x882070f61a0551001c0d0324240301070420000d00d42c0100c1d9002003a40109096440f45400c62409040e0b0802c0f180b00140050700300002400c006545e402482d681c05000071042044c42c1c08011040640b5201c03c0d07201d10360103148114118403081d002c3c9070a483e15170031035500781d480410750071a106000344085c03070a940c901d038900780012a5604041e044030101c04850340c024007880c69541016030f00108c00030007000461200b041182580d86402e90710f4903005002d5000543c440a0518018000301480d030402c1c01c800c00e203090301d114585c4002032041c4070260191901680c4655035000c0300c2c10101092040390300b1010000034801c6035544194000d0b4091450309858288110710003c001c2640303d148a104603100c0c2c0f030911048085103294503e00002402940042c05204104180741000c1c0d0b1907001c02c019400601380304040600003000c130740d0300210801d80a440480300b4010441e560143c081d803041402e44a603010000c11109078111801c1940000d5041460156890004d01164180350550301031820319 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 807391600 1250 807390350 807390361
    0x909020f04020f1c0608250f030c182a0c060203010330020a02010e21010219020102190e0112021206010f030b0306060f011709010501050f01020a030801060c210e0306 73
    0xc0c13142d0801e41d0030807001f0f85011004032005400d04600800101103420382d9004c0000c16082c580c0c00384000714424030140ca5168504a0080048034150a99001c4203060292510b00c42404000b000820b54070801c204400365820b50049816070a40c02c1d004100c980f0003c00172041c0b04c00d00000c07410504800000c0045e4292800ca00e5a0001071743c0d03a90300244e4000c20402c001503005071016134100c41c0240c0b8001c19031000307200c828610000405003d441d80d50008103100d420305403a41180d142405c60000758030b40f140400802a605941d41c00c81e004004540c02d1070042688681c541103003041040106548036442c0045c0c05200c41e800380c031104d002c90842c6084101c0b040c0280a008200b8030014090085603481405108800d00d100e00382c64100414490300103c040c2480b09114001d00107200000307072031f60414080c49200c484003001c003415940200206c000190340040e086040d91014500f03d540807402d880c090560440790511000031505102c030101745503500803c2143e0f412803c50440b0155281c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 807392850 1250 807391600 807391657
    0x10150315030c05121605040c0e180612031c05100f0b180d0203150408090307090b0315190b0a120b07030b1905150408070305030a02010c0e0105040909020f04020f 71
    0x80070442c44001708881c1080040e407070240c0c8040e8038444942402c9900d40010700000b1519000002d8800d0b58041c01c1092100d181009900c000040e0700c0b500065142c0310b626100400c5c2440e140820220342912100020411505441e29100410242c01c816206e41e468151032001c40c3c008641601c40454544041c080510340002c400408940107030261010344200c01c90310401410040003a1503162040161b14000d4800304640d10017052202d500094503101042094186003035040031000304e195030700510480542400b00141c01c117203104400100c05c1881e501045040c4950782c04a80d1380320400c910241404a80c4900c640300d00c8290342c0800410158a0030807008041c0c06000c5681407500200a100721b00f0424800c08506503000441c90a103503403440d940e440c4c411300d6041140d0b05e0700f010030096034807502401084001003041c245004681c00720b20000340740d0300540c42002071107500ca007a01c1065440d541d0b1000540c0c80064415075403108001001c001c141c0c010041e000f4410700c51000021a8501c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 807394100 1250 807392850 807392863
    0x11a0a05040504090f2f030102070201052502031b10170105190e070c05120711100c14070521030d0506060d0203190c0810150315030c0512 61
    0x5140d1035032414141400d051000400754040115a030707960858100c408626a80c101e031002110904480071582e02e50516261400f84621106009a005006860040c1e130842d00b9036407810362545140000100001c1d06200c045411003001e9054002c01c03040309104258504104c950320400d41e0b511410300d07040d910440c1d185004500010340059400018004c03450a50b08894911340da590004a5840d142e8051000c0c03000e055603454042104810b1030820024248802d01059034074084641c2007403055118141503115036201340703100b8141003120111250040820080440d0841d03094000300210341e100325a11a0b45004203440fa2900054820f030341e081c1c04041c900d4962200b0b000c0c5081628540c00319001d030034090191075001c0c50501140843e015103201440c42185001c2c402071803802d04400320400c88031410980010454114100811041c3c01e0601904032259008007040521010408134001c261070b08034401143d50038900001444440c5596105032a401c55070001c084524003031309a5541c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 807395350 1250 807394100 807394117
    0x4140a1b0611032d1309020c010b150304081b100c021e030d0903091e18050f070e030c190f140121061203050d0b03010b13050a0605030601080303011a 66
    0x90082c118541c0c560600c00205402e190301d130b40141c24203003a010310301c4521405402064010b54086501c2a0900090140d9940d0400c01d44000007200d01561070000240f0005001808020703000806500340b0f10710024240002e03400506079403103140c2c8221090b02804c260701080c0e00511580c1040e10004000c90324144000496200440c9401d00314082e039009021108020b13014010099400108001820001c940114a08150454103420b1264000e500301003050907c00039441e28041208250090080d075401c480d00341083e02160100e00006450300c20f65170b04850b00000c0001c05403204005950540050792282c050074000103454885045071048011411070014811922079000080149140d0000b09100800031800c180c540940451004220800301e00144c3e0000f40d5440302c02ea01c2c464490780d020124000d105400043d00005d0316450700d13131718080b4040d0782c50780890703d407031700540c0034070010800681030f501150f07500c44525459130003d100d600e13800f2061440655001d202c0314121550607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 807396600 1250 807395350 807395377
    0x6060306010504121103030a0f0f1403040201031e020a0903021f02120307030e16080114150103020c03190c0c090507050f0723072c04140a1b061103 65
    0x2500d0702061100310313498018182d0304041002c040011586003031008094842c665200d0851b1420001001442108504400410002186a50780012030700c002140c2d000b90b02440c0100f0710320180003c0ca071440404078a2251007901c000707140780b503054101000100316402210341c48a0700c400ca041000c40f10301d01080100c01604103201c5554292a100044c541110003440c00145c40c4843c000c040b480c0030341c0c2c4620641702c2480d4150800016500340510b40c1c06004251507030b001ca041001d42c0740076034024040310074103141e000305407645111001c1090ba80800043c3c400036890300c6104101070034104c0264400d4540b84030211010801760001d0040070f020724091f941d00d511b0071062014005264100f4001214440c0315074203000c008500222007080c21480c150040c0c8141032919180082d089842003605c4d40c040503940c04006005070080c80c142d40550170502d00800c000e0350b5003a1904200b60140014102c142440c03d00803030b52540f40c0080240c0b410f50720360781007200520306c1b2146d4074080c40790f624000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 807397850 1250 807396600 807396607
    0xa14101e0c140405040c050705011811030115150c08030f011418040803060103240e0108010605010203160309030b18160b0304030f0e060c01020705060711120f130306090506060603060105 82
    0x142c10582e000003041907083c50403d0408c451a5141400d640d00f00101032808000c1082010a1002200d802294550100c00030041c0000d404d140c0e02d00101c0600c00c4645201c0d1886a10007500d00407120b80d0403c2c1e9100c00c01070f030350345040900741d10038000230301480501118000044500b8100071300540000b188405a2006594442c0d440d904941d0004000504254545110555041d00c801200d82e141d040403400034407850424103a0008030340140d0245810382e040000800c0740e0398000c8111440b408001d1058150003103203003020366050040c0e910080c440c0c400c0e42d0812141e20f841c0541074030b090040c0030668091885000482c46503040d9030041c00071100307080010030002801458070300c030b01c89083c0c200b442c4a04118400228250801203900794144d400003100c1082081c103105695001690307041030074032217060b9044959500028480b41426070000242c403401d0085c200c06450740c000006500000c001c2c3c4a00e003150180100d800c04036010321841c000300b142c0380340034030580303100e003806a403107d09 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 807399100 1250 807397850 807397859
    0x409030203041208120103050a111c1713060507030311040b0a08100306050a14010801090b01170c03070603020d0c210f02040506070605180f0a14101e0c1404 69
    0xb002043d05404448400b010440e00d10b00e01d40504000c0c1c02103020380090000c4070102e0410040c205807003218140700c2c0d02004c0003104021504c1400f9800c2c107410800c000d00c90305403c0c114011502c59224158050360740380c280054056446130080c50b40c14840d40c0d0a02c64505031101c800100d0185018a5054100501a100c80d5520400001d60320061003120502d40507529154003046500a40342c5499040e207400c2c102001030380034030142c0c1c01440c400000b045081783c552204580030f241809602c0c100c0c2c62840c1c4040d0a841c0800070740d02400401020f90301540da0326000600258000074000b15424104030800031424000c1102400c00c8161403600007988400c07181e448000d0541242c00200c0d03c1d13007400081500d132612806407081c103119800018250820002e01410240203d6007000945d11000b0345198010003c00c0c101c03201030b030011a16021480410003c0d0415072641e04070b091451030f100c01e054200c14180040324840800e01c2c1b0420100f40001d03c2242d0742070440300c0c0f5481501082200300b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 807400350 1250 807399100 807399119
    0x190c0b16110f100507020a0f030906030621080306010c120c0308330103060306140f010f080c0d0c0b120106030c0e0307170312010e01060305011d0f04030e040f1a040903020304 77
    0x1c4d40038107240306841c244106c9940d403c03905001e07182c8c05e0300060030b03010043c8903e64061007a803000c1c0c030368450380a1001045070090300701c004461000414020011006c41e42e16409450060a40ba80c464840303145203420410041c4140c002c4081500045c0e00d080202f1b00f0340b12500d9003203922002520a400841002262014405083e042030311b04040d0340c2da1001020600610588083c00c4001684c0b440b0340c03c00200c444040711042c1c0180c00c04d41c00007001000701900019050141050541d0100011001c1e800e1008c076200312640400d007941030005829000b064000180740c1078802030380f020031003a200050122451406155110b4042e4442e11050140040380070341c0c041009003082c201c81c1b40980c05144503282c4082031340030614401001005000164141c01018054140f0400c1d1406011420042e002e038000094120011590075001043c241842140d98019210340a0000c1c8900214075111100400b942d44482e0380144407030707090315102d14060040351180e541560045050a08020100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 807401600 1250 807400350 807400361
    0x11090a0b1e0d032d050d0e0106050306190605151b010606050d050405030904230601022b0903060e070302041103070203040303141c0c080a050606190c0b16110f10 71
    0x10504040130050307425602240c449010300c04c002569826100c036911264802680ca1803c05c0340d00a90526000b446662000110389030b1100b8149070b1102c2c1803039000803610007801b940d00000d0300030030210083c42e190300310000241061030789004028000c100910515013266018000c08000410420040c200d40308180c00ca10b401c1801002076a103401c0f203050008085810105903103c82014102881d240800c1c4021840c1d8050400c0c00034109410120190000720300092125000311070501520101180c8220200c03c082e5a00040c1000401060382445940304c0325071104901c02c50814110001100c0c0303c00a0724001e50458000f1401c080c111703039084d00d1046a103440100051410b205540080300c0110907480754051003080002c50360b0003124010b0101e10000c11000e05d01e130810040c03282c243c481000b19030303949649050f5400721403038003001191a405420b00c0680001a400c0a000c20b101c0a0441401c41c01c01c2c1e9100d510750070200c1c221554440742c2d003204040d1590040d1910f920036010a1f01701 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 807402850 1250 807401600 807401627
    0x3161205071e030f09030c05210a03020c0a020a0b0c0f0102040e06060325080a0b0d030f0e0409060e07140108040803130f080d0b0307060306050a1211090a0b1e0d03 72
    0x10a0b8141e0a240c01e030f089900b076040603030001f1200c0880e00140701080c050808400300403101100180e0040121840e14400c400740c1030201940000c040744441d005114603500554024020036420f9030724855802550860740c0030500324021862504100d40d014800c8800329000c1c01c0c80040e017035844000304011a00300034031000c000c180c041162598065000c2220b100c400098644001c50b00741451741c0c1d0300702c5101b14442c03030142080c0c801000129821143d01608600e192800307103883d50b82c030070106001d808851700c020b280d02c0c1080d42c0100c080e50041001c4050b11280d03e80001c0e09490b680045483c2c400c00e0b64041c00e003100400c0811030740140c1000742010b05000320145807210005a8861040343d00004500503019610341c10a48545030074042d800040c400c2d4078003800098180030028103000c0c064480c050f25400b004042004100c0c80c2c10510403001c00c02040b80c00e1074034120440002400809081611469202d6000e01ca41c80081c0c1e40305c4403130301000d0100640d01c2c00c140d8007640c801d0540e03941e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 807404100 1250 807402850 807402857
    0x60a06050a0e2d04050d080f011805040c0807030c03150b0114090d120f0801080309030d180801290910170f0f070503070f060e060a0509030303161205071e 68
    0xe83c00d0001419900c0c0e0040d88500003e00e6000941040104241c0010348039410300c600103401003005880102c11400c6010101c400010a0703112442d01c241242c1c500e5014281d58001c41800006011800c03102030704690040041c0c40c4103a003580c484904450000c940c2c180841d4144180001c200100005411140d50261021122540c5902c1c3c405c501135605072507400244d406071300e401d881a84a144603005100f0303600110f080c002e0b0140000c2d10345c040005c000e010095900c80003070700b441c1c0c0b91044100070134503403008000c02d0b2a20b12614143d10a00b07001c1114024404102400609000c40002d10801080e0100350340b007420209554a0202d1840700f0801a203e103601034920f43d0740602c056542d9000c1040200f0140c2d15080a05041545c90f03071115803101210707102000050380110140d00301003000c0750b02640d1001c844e8010384483c0501c0100c650540320200400090440d411070040007030b445a01c0f09140c101c0b000c2000f0007655821102000040d00000040c5e201143c01900301c990f0381c00b00e06 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 807405350 1250 807404100 807404161
    0x330619030b0a0b0c160b0a050c0109020a0801150e070e060a05091306171c081906030b0a18021003050c04270e030a02120715020c060a06050a0e 63
    0x180010b440d0807160f000007240c0300001503400d60300306040103c0a010071030302c40c2d000c074202d140c50144d00c0203011310180402441070009241c500080b0030b60000001550050020031401c2d251075209000b000000c46995a0300c09a54000c41c00d54001c43c4080e01c503881a40c1c81402042c001000e000c2290041010642406018410800c455031995110802c84008480020740146090240344112a20b82214840b0f8ac20031480c08000c0e00d0200e03100c55441895003420a0240c541c5040030070444050041000a54030b03104000c01000b51030b88009004101049050200c1807800d02c80e8090005101c80c000d6000212040d40c01c0028000d4029035070101c1300d0008903042580c0da11215225480a0000f0381050310307580c0480d40c0c207070641d00c0b40c51420018000250b0508460500103035035000c01e103210701014500070800404200c10041d5100314400405001e40d10b0708a00f500c219a151401d80b1a42c00c036078102403005c140c0b400d181d45505d046881c0042e50740340300d131140c82e1403020501c401c900c02031441da80071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 807406600 1250 807405350 807405371
    0x31e150a081b0d060b1f140f030c030c040810050603011b1d0a0f060302070b13020307061215060c02030601060f020705010e13050f040308010f0303120c0306080633061903 75
    0x3408a074045506040ea001d42140050402800004072050f42a1812010b0000c00318101c811016a9840b0ad25020301076540c0d1203102c0e50040c075004961000c07406c0d10031a180e160710811650010b46c0944402d0300240144034000288200310f002203021200050351405103024242d00740030401a00383d20150100070841e44940c101102d0710030980004000c2a0005851410090004090b990101c80215103480510342c0d46c0c002621000e41d840b490003004000c4180e43e900c03a20a901c2183c5a1082d080c0d00b1441686da082c01034034000e40003005034828000c00000064490080001451000080d406008080c1c28000191411104022966000050060006c00f0022070f48500b5000d030306100d8071500585010300d0700910041d0141c21211300d102843e40c3c1000025048448050481750f04178011a03005503012080f0000d0525501100c0e152003070b60300384000d00c900c240010090340e40406000345510703400c034008650000c13107070b001c290001410494036071062036100c0c82e1500700d02a880c020800d52801c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 807407850 1250 807406600 807406609
    0x2101061d0d0303200a17060d14011e060602010b09060a05150c01020403061e0e060f06010521070e0906030a080f1c05010501030f0b0114031e150a081b0d060b 69
    0x1900561341c0f00c0070000440f002a13903000780c0140c2255481450003886480e08202080d06a02c2e0010000c00e815111010511100c0084d00300400b09c88941a2800c1842030a050303480151007a441980059460481030a03001d050070070f495441504013401a071161498107041c0a0707000c0949800b000f981c041405458400042070000f88010b500a5602090220802070149030425101c289011104d1270441220400303000460100c0d440304140748003002598800c001682d040c030940d056030150510f452035400e45800c102c44140d004295641d220304044440e003050005401c015644240d056010303103010030002d060a00280401402d05880d10f00341080e903030b0011044950701505000094440c0014044c550381882180c211600f00407061000c02c90701000030b481500c07114400c0360b03940c5c0c001002601c42c5188050040c8402d0382d00250704014500084c0c6020b03900302640c06140704410b030340b000184900001071589003c1c000c86c041e001c41c08240788104101608000c000300d0b805503c031086000a95038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 807409100 1250 807407850 807407891
    0x120f170c04050402031e1602070308031b0d14130c030803131a04110a031e020a3507081002070303090204050103110a1502030a031a04022101061d0d0303 67
    0x101c1008030b200c4e00a1070301c40f42c021401894030300020700c504447e091072540001e44e08100e1b03810440c0c3e00d40e42d45030802d031003601103e9907003250080d481c0003c07110f460958a43c042440c041741d00c030200f9090348584000c1145042c01d41409007060281c00030901c080f6224000454101f071207080341c000002001c0d0b8841c00700e05107008020150003641d40400042c041d500d40c803c07640d000d00712562000182503a54a20040c12041d0070034102107281141082151aa045208049c003e40142a040010406c2503c8810b0300e06a544484040700354810310902d1600158000c2554400d10141c042d200483e815500250400c9005508160710350208001680362803007034501030750040b444140b00d010641d09100c1014010743c04000510b0210041490b855804815900b04880740d01d404210a041d000742c003040010003146141e402840042c031032041100c500403880350020125082c1c1c02036a81d85405490000d007100c030405000c0082c0b07a104000340b400940c01c0b201c80344a8140000c4010600400e03041c01d52 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 807410350 1250 807409100 807409111
    0xc100e0310180b010501020d0804030f110f0c1504060c022b03030603060c020703201815180103020607020108040501090b010b090f1c02010315090509030403120f170c0405040203 78
    0x301d40140b0700c0c0911551501e0039015043c02e00043c200103907085001000e10000400103800c102c0e481c41c040368400c1c072590010754190800022542009248460162524869102c19204595804d80307001c032046100c003950115480c544454502e642c15400f40702d4a2200d00400340350100c403c1c0c4040b134804164441d00140a402990002005400c502d403000441388004011425940200002c00000300c0420407404120b80c00c20401d1060004800850420b03140c1c4140311048039400009c01c203985150104252010310111040c8942200341005480405400e00000e50460001c22206004d03502802034030b40c00c44e200c1c031300024180c40c50340c07519800f400080c1c002421854001403250b1031031800344c0030000c0700c440440728001e5884801744400784036454030100070b06164481d1095443c00c1c80d4602c40f680203051400050115242c10002e003904c0303030b000d0300013203859000c69070408440511413503c03640700c0c144d140c9a8100e41d16000244410602000348842d18100040002056a4469001650103030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 807411600 1250 807410350 807410381
    0xc030903040314010b1518040b060d0204230d05210702040c030603060b0301060b18040612030509090c1606090c0506070b06030f0c0102030f0306032b110c100e0310 72
    0x903041c1c0c00422484070f0094282c00300341c12050222854540c0c04031010381d030020b412500010540641004122a070283c10131280d032586c8089030000d000988180401083b039002c016400140c2d000904020041d49003840140044d440066a0300401050135481d440e003843e8018900d0070040154005010340c3c035a9484000005d48a12080081100b03034003442c4040c0d48100c2c0280481420250044114015048045003058814500410580355a80404040c0401442080d000f1010741005031a50340220b00044c010b080442c001030600244600351480c1402c0c0320981d122030042e58030b0b9000607044100c0180c45003095030034002520750b034038401089814418075814001e450f0107002c0508143c40e40751240c1a9030883d180d40d01260fa40030080721040302e0039072f40701c5450362610343c0440d03d0f00c161010820081c42840c03206900101d881070514029030110340e1a6000300a038403411984589030403c5003a00300c5044038401c40c5482c080c10401800c01009401c840c0e000c0801c001090a4504806001301c19 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 807412850 1250 807411600 807411611
    0x18060e0102160825150806040603080a0c150605090c070c091e0e030405030303010b0310090f020304061b050306040c030f05070e030d030624111c0215010803030c03090304031401 78
    0x206241e44040300ca40d4107030244c4141484c501402d100400c640440740724100a009800030352a0f035175940c48100a507420540741d0b078071202c0022003e403d030041e000058440040b40d03450400c0d0040c80d4000c0401707940010f00031250b03549485102c81501d03000003c0407102c0c8080e020300424403a0603885000c5c2c2c6983c010030741c400180030807508081166450502124039070000c000902c45a01c00008480c11501c0c0c0310109607032039960340c448051606641d0030021659046c80580c5070000321640241d4003031401020308214008500740000764554008140c2408540c0500c002081407030b256000d0740e80a59913045c00f090f094140d6844804aa10484002004c607420002d10300c0107050410525011881c0c0d818100311b514100a074820880a09882d145030386091560580140b40c45031060110007654142202c007032079a44030681220a2800c20040c00511840259041e5914200704484c100d07490711000e140b071925042000b182e00d80c0014142e4040b40b10400000001038402400c5000040b0101e000254 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 807414100 1250 807412850 807412873
    0x9381201330b1306080603030c010e0106140d111c020306010e0a05101202130b06070c1715150109081c0f0c021021090f020406050118060e01021608 65
    0x107500381907000707954085402d20103015004885500d40b8150b07500380c1017030302d200da542900083c42c51281b04141c0c02d96508140145441b400150451401c0d00c201a503483d00c000d01c201e081c0b00116903100c502815141403600c885525007040400074100d25500801004401c41640209203000002e030701100d0300d00720000820442040c2d6100fa150402008280481c0301890020b0070055040d800c10040d2040000d4064100c41001c503511001808901500301c0752102d80070308021850381000e1107141030141c03605450349514400410003002d00c1841c1546d0840680382e840b0741040c001404003c0d5418003442c0940440c0c01c01c400c2001c600312007070f030701212900745c05160b1004040c0d000400c5403c0900c01904103c1d801a038548080e080070380500d1500040c0c90014404072050003403174a400c0c0d6041454151b02005111a0305428401c05009550601c4041e03955401144e0000042008001141c20141b09102da07600c6031011010113001413040b02c2c08080a0f51005880c01f0140d07000310929803201040d0b86 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 807415350 1250 807414100 807414191
    0x150803070b0108060a14161808240c220905090d0207050f010c02012111040617040b0402120f011b180602060a02091909381201 56
    0xd500441d0305030180260310150b4090496007401820540ca00892080d215500b03910410000080c1c40c448c50103c1a0203640f03842d52a2503102d07403e440c4400c20b0010080100520700340068034010f00042500d107280808070000d09542403c0112200179242ea0608000f03900303401ca0240750300811451b00913140c030011180b030180c0750403110744c0018002c071041401282660703005140c0011841d02820300382d5408800b841018824400340c10041c2006182101011000541c500076000341c80c0180c0b01e004041044000300849000100e4008149101100c001070040c101010070480141031042255484070707004503083d0035140400908081d4400c00300c0c0c456000ca03403084040740c0810b0010a00385909081c808025115000184460b54003a000610040c03180c8600c0c00c61600d510490500f030202c191284c1202014180b881c1000350404d00141c60344507800784c500000b01d20007400500726901d6520703984c02d0010109401d80c02e81110356a4019003420030003010184030f410505264586c0c4c420310180c5884 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 807416600 1250 807415350 807415363
    0x180b070206010e250e031603080a0f0206011203320306040b0402031b03070c0203060c040f0b0f12060d0b0411240d0b0d020303070507050109050103021c150803070b0108 74
    0x1013441d036440e45200c40520f04901040e0035424003e251020303060b041040441c0c82c1c041002140302c0380113410300707000080c8504140030300f484800d550b44da2602c140e031074441243d0b60324083c01a080c05080c4040700e180047e00800a03108810b140540d07809904081c50221046c21000710007840c840c501c004108030f02c61070729219001803030204407000c6065049c00443c502c9202d0380000c42c1d005e0260000041200c00c1e008102e5000340a6006017150328500d014615a0f0058000c2d00c01d0030300e5882c0e075040100748801240160765842d401220440d00300801c006101c9040040508403503040012190a4000315000d0400e86104500828000e80080c41d0b1009014085e5900ea820034500014490b106031854214412a00e010801d694081a001340308000103881307002410000b5418800010340204001d0007040217412180d00741c840b0f256282d031380d500560580c070604c044810741c2c8012040404290155900040c4140c0402d640b4100454032140c0561442d84088416103003403041d05d0040110901c208402c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 807417850 1250 807416600 807416611
    0x102012c1c120b0d050a1115040605090a050102071d0403090b03010b2113150b0301020c0604030e0d020105030a05090a1e020f061305091e24030708030a03180b070206010e 75
    0x5046101150b1542620340c6c00c2000001e24a2011000c040265030350101f400700c580c0d9050000540e0745030742d0381020303140c1d40c441003045001c2c1090010000380c039030000c030341c0d03600715070045a02e890904080d503003429003a03800503c02c400340300c5044808a12840f00390040d501030010700b001c2d05d6072204020002d00e0307603034181940c002d00e80c0002d8040000a2a50294505110b40d01ca4405240740c0003038000040a0704100c202c45405601c0421864612440094000e0085000752188a8444030760024441a20075400019011440030000700740040c5a40c0e10040e80034440c48256031003120a0780c0c641c0141203503078460102228441d0201c3c1c095103402c10040d40400011269180b41400205038450300e4103891003418030500c80440000c0300c40454800c504046200c180011907289880000301414541a143c602d02540c517640c0804082e0400007480c0090f95070b000011428a6a68041100940300c1d51002075582c2450320140e10015030b208600b00e000f42c2103900a00034960401710b0308004080c0003400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 807419100 1250 807417850 807417859
    0x3010b07411f020f04080102030709050a1502030909040303091b06031a150f0d1103071e080f060a1701020306010e0d0804030b040c032f0102012c1c120b 67
    0x6081c0e001107403030142d42e41070b0503000300056100c8005a04480c8a4043c660152100354000803c11003110350200d60101942e40803295400380c60340b1822403000ba000d4822001c00036030700403c03103203c6a140c80c0d40d800354010721900e03002c42d02e070700301d995503424003143c4080c0142c0c01111102e05000050701130261203100c1c000c5a010310a80341f8110000781003402e241b800070389440300000d9869030b491114000c558040300b400c44107118000c0241d0030589140c2c0300b00ca0348400100049108805580d00d10352256103140b55a8035620030340c98100d20420942c1000d060180d000c1d12a85d000941c00d80d40400c856103010011000503280c0c684040090f00e10f465001096210b08000c1c0380c800002820002520701781da0700a00100e0655890340b50032814126207400141c82c005005200c1404032020150815201301e50343c100b918a100d10390010f81c00d8a880118407410b90a1501098828124480710305210418400840c2d8000442914001d100e14203036440c000090356500712036440c0c42c0c01e0b0141c0051301c1c20030b81c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 807420350 1250 807419100 807419113
    0x60a05100c050f3f13060e0f0f2101150806011508041e240b040b18040602070206040806071e0f050d09050102030717010503070b03010b0741 62
    0x144d085820401310283d5071181150001d00108a494a07011100050504d40e150781c3e11107004400b0465400035100d0b560004401c4c00003207545040104182e001000090b08414038150714004000024038040101c00c000e81c445051a0003d0100740260000e581481d03010350f04d428203007092113081185c1600b2040700b0032200c4480c400441d03031083e07201c0d60140d00601030807048500620030728041000f0200203007014a40600745071040201003481c6007040d10b680300401106400d1001c0c8400c1e101d80300e44165100040308000780f0707407103528100d00358051310403100107180c21003960001d118bc1e0050780280a09a104108001907031350007104d521006e81184112031f01c500d000d00d0b0000c1c601c3c402031500004010010075901c000002e19007020700d0703142c2d0000080d07440c0e14020400034a054400740a10000f00542c030000135403800c0210300d60b400d403031550804a10f10307824100c8071070300d540c0180c01c212401c0c1c9144c070410103241141d9281aa64540c60380b81213400d8040b40c480c0070050700d10707502611802d41012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 807421600 1250 807420350 807420373
    0xf02090105070b04050106053604080d090303110f040e07020105090d0e01051b010e01110c2805030403030207230f011107170106060f08010f030803060a05100c050f 72
    0x141510300c0b00360b00c24240c04403030340c0d00e20781903000d04940ea0095804c6541501006d40f0444881c460440f0604540e994200319460310180b40c01a0b60142d901801002c401c0081d46040c041c41d0700810400782c02410081880840d1403e0082a9403110090051382d00020609100c10204008100c2d000041407000340000d0810408107500e6400315a00042840104542d840c0c1c1d43c0d0144050303885104000c8089012411900f0603103001e000e40700300b46e100700e501c1d107020740700940204c00039514100016030040c89c6103030341da00e41112640110791425035050700d10f00143c0e0024100b04018006036201e43e0117040326520f810501c000400303075100c0018800f01c00744c1042240351102218144508000d280141c1c62103003155015060510a4100c602e0341c4880140c418403e102c150094011076116960710303009000840707422500b8442c00c0c003c0c0e152615400504102096018000e103070021001005240b80319078030740000c0c1c000003400b00408040740c9000c103940d0074400140040c1140e19600f2000d030165103ea03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 807422850 1250 807421600 807421607
    0x1020705030d0509060915030403020105220819020c031e060612190809120a0c090c08010605070623101502280524011d0a09140d120f020901 62
    0x34400905d002c0e48000c00d481c03507169901c0b2105c00040c0148505142e40c3c1c205402c0c024040c0c13008890b000d4500e248902d40c11000c82c00d40308a88051a000a84641407850178600c4c1e8160005220081085100d00c141d510072a50f8207200a0a031303000103112889850f202e030700d8801d0428500802051054901281180015001055190100c0468003030104001c80c01d142c0b0030994041d2810300c5801c0107800c1d1200303d605e0380010724424200e0080351001040b50f500c4941c1340039a904084500300085541004101d01030041d03018184e040c2c818240070a00400d91003e400e404102414500000f54151007440a00e00a03940380c0005032048801e825084126008042e40d075041c5610103003103007080521203489024900c20741081d07081e44103081e242c0021031501d101e01e030442c50251400181851000028940080d080e50302c1e0410301c0b220110069a480c0c60b01b01c001001c0c450713401d641c1ca14101001d0202200103110038015510952100223902c601c5174103150880b003a4501c2602143c2c81000200703035580c0c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 807424100 1250 807422850 807422857
    0x50702010309051005130b0604020903030421080304031d0a061e050403120f08070c03090303081812131e120f05030705011e1a061308030301080a0201020705030d05 72
    0x40a080129840d00b0341d1801e03e107445525410b00c00d10798a8203040c000358211510798a03902c107000303020040680e01d8102c1044124440c0c0c5000d954154801c000030003071281e2240c01007000400c0400100061030703241d162131030540c2c402c03102103001400741e030324240b030b503440c0802d4000002505882111656080c41000381807117041168070113000c03041d41d0303042d803035544154211006583d00511170150703a1030b01c03c400351030301800e4072080c030114007501f000a0085105144241c2041d40559910600d21f103103441c16503683c00040c000d00d007c45814844510006400c21140610009415020b5640c0403a441d400c0c84d1414550000b05003079902000748000409841d000c802034540c0b0002d4200800307010300c3c1071040070300207a50080c0180000300d2080140300041d0b1044a0600b0030402100006103e24643c1c0d04a594101109807280503c0c02d014045080030405420b82154800c0f00303482c01903c41111034135541099014007076680c01100c0300d00465a050060100501c0160010032603030fa480c270005013840c003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 807425350 1250 807424100 807424103
    0x50d03021303020310020d140c0d050403140a020c031218060a020c0a0b0d050f0613050709050414180c150702030a0803071107150e09060301480507 65
    0x103030041152451481e260004070002c40c3c0c02022544882000a0140b0103900541c1d00d40d0b103154a0100101001144002c00380d01c504080003560b41f81c0058501a2402454040c005404102e4284106482484c2c10802058810180d4005051740b42c20b000401d447c042071403450380a02e01040c80322000c1249070312081d6814a1080300c1282d25004400401c03072130300c804180780e107500c070495840002d218103aa4000b0801114904818440307030743e4202c07484400c05c10940d1407641010003850444c0305443d45500031600480d040c036124403a00d0b564000241519000d00007842c4006440c0c080c00b4007100e0324098500c2110f110000340030601c0340c010000e1130049044d01601030484000400604558090000c00c200f994491092034690030001002051f02c90428050b54691264040204541012051407061400303580d8440883ea8540c5050100c0103c003d410709401d136498140113420046914180c1003400000c500441d1918100c15a4510710340c80c1c0020307604c0400d00102c8100502e0f80c000111001d0b036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 807426600 1250 807425350 807425357
    0xa06090f0f0b06150f3408030906010605040315090201090e0c0903010f06030b07050318030a05041509030b18030405130b010f08070801052106091006050301020301120b070c08070c0509010b0304050d 87
    0x2881000701184050184d9828586c8164000043e441040004800b8500407290b060032078030140c0e260381c1c00ba40c452085001c0a01003410140c41c503c002d00540e04142d280910600d042c4005c42e41d144c1c078030340d8903400940f01c2c80103214010940c0c40075800c0c00d1003104480e1051017000d000e05403440e100c040c01d02d500a40013004100c0000000360301c8a180301d280c5030010040c041225641d040b03540c002007450300300340200260302100d150000030f10f03881050004140c940100750442161107440c010410006010455141d41c00140b00c002003039942c0c02e03004d50765248807040101c1c0032143c1c14001001d000840d1130340004e12203c030091201e102c1d07200c04202c2c1540c90589001d004c181099407180003401e140e50780c0d42c18501c00c8004015121502250f4092507003402003041c000c89880d0000c0600f40c5c00240a050703030010310a904e280100d005480c003180c2280250900d003400d5429601e40e00700c00e9000450503140c881d03410700100300c1800d10b80001030040c03100703940050560500fa55880d403107018008004080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 807427850 1250 807426600 807426637
    0x31a0d112b0507031e03020721051005071103120a090602160c030201090602123f01030209010510050304030e03010617060a050a0504050a06090f0f0b06150f 69
    0x4640e010760709404a04a21a048a051405140580c1e654a241c0400c480c00c030f8240351007041d11500050424400d40c1d00d07030080c021071410114a4003042405011081005901d1058580859028001c002155031903d02c0800c5a01c0e1440c805405113140c541c40c40d20303940c410400c1c229410668801c09410909400020031101807504103400a40a01c00e00001c4100c102d00f0000200320340c80c80600d00b140e100f03807150072030159912400c1c0c1e101c030058126201d458a0400c01c50198014000e00301040c40c80318003040444942125400703d0090045c1c624085600d1800300510640c5416043d0600500b0100c0c1c001280c0402c21400402131b000c0500020180142207422441603a400e4000001401004c02007c0e4880c140f00c1010340d581e0001e03501290741901d002d01249a40300c01b4090244070b0b03508480140420034865444400804044d0011b030b400c1010911040001404c040420b0441402182400d600d410301000300016880402a01e50602c14100f10780c101c400701c884140c507401442c40380402030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 807429100 1250 807427850 807427879
    0x4030e0a051309060f0e0705011101110310080f010203060a06030e070e24090907120303060b04061d0a030c15032703020f03120a1a10031a0d11 63
    0x1600c8000d900400e41c89902809a0900c0741c2c1e50b90f01000500b40900342c2807080745640d503441d00498028a85040a0b900200003d00055001d000f5141c51105448000601e6145d5102c500782d194105503007078028002e902e001000402c0040105091034a01180210300c0c5062090000e80c080b691403044c00245911440451982c882c148084401003070410a00ca0301c0c0c0c030f09017810207840c082242c00031020518100c561045809c154a00c42c0c80740030751100a00c0180c0c00c2040701100e4003203800c821810141c9031f90700030881100c40809013008124584581035035011003200c400400103c25403440c00381c0d0415200700007280e0032020f04002c4890001e09608a20040c50040b00030309405a0484007011901e8800c41a180702c5048000c0c60714000e80c04c0d00d4020180010b0145c5920450035440c510003421400f00d07261038626885404c0d10541000049422259640811140c582691450012941d02d01c0807000085281c8101601c1c10400c540509900515546000c62807c603c144140220342c04c661119 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 807430350 1250 807429100 807429109
    0x303070804020118090b011202040302091f090612030809010b030606040b3705010215160e0d0b07030516020a08030c0405060301090b01030c0813020d05031c02030a05010609030b04030e 81
    0x1602c01e24100c03410a20360b440d201c0b810040c6c00094200360000c3d03000f40908540f8140741c4207031000e4960043c48034107591a503030050008101c0032074056903800d040c0300001980d07040c248035070001080c80c0d20603009954000c1c10040d11549000300001c096905210242285640208149500100c1104e00203140f43c0c0182c00b05401249034542000048441e40383c035480405420f4030382a2260511842d613143e1a120f8004903103800750f01e06e00007441c01090010840340c00a00d1603005820303101d031400d48039140c0d145001454025840d6030581e0306014110a00044903814012075500950f5120360f22088012694000c1d0384445225000c1c0c02c2107004000702c1c07101220b040448e40103100060000d6103e5071610982c00061059040280c04686407500b580348241c0240080c91007100600b0610001c90014bc09001c4079410700d100803a0316000410015056141100f10360f160150b03038000058903894000d003400200d51040e00300d007088c48035080c01080007450302d030505a0f0099140c0b500410942c003281c00319 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 807431600 1250 807430350 807430367
    0x70f0f06020c0114180d09030803040203011b08090f010e03040b071505040c140d020604030230010207230304060f1b080a20030901051b010e061009060803030708040201 74
    0x6402d50800c040100045000602c1d14080d200e810781d0390710181800303a202130391044410754400111f04040820004513030351030080c5074003074000350020480c2203000055444500c441c2400e0380228000d8800c3c8006207008201000441101400820020008403c07042c3e59006034072031002c44200006003030041008000082d802c459081c2020301082c1003600d04864040c0b103501541d01034001004c0c21040c585131144180010783c3d005400c0b9403909040d5000e1042d519444010490010000811020007000c42c2ea60840b080d0800c1c0001a100c28940c9000000e21060207400f58044001302c105003001c030004002c540498130b01c3c0c201207101c41d085d10001e03188104885154840d81d8002c504c804103100702c42c001071207c201c85507240182c62000b00017510100c1140496442180c0c01481080c5003540500000e14040e85080e050003080b9290380325503420356440c01102c42d4a07802c103c003804007900701d24850001410080e84c003403007a5801c0c03641060b581d000c000e08980802a143d4003080a46e4025844c0c0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 807432850 1250 807431600 807431617
    0x11202031608060f0702030a0c03032a081909110409020a030803070201021206061c0f0216050106090e0316060c0903051531020d0813060207080111070f0f0602 70
    0x110301955402c1c4858a03020704880900301003019000081241d0310100880d000c0413181d45940b8051030f100d48003240140109050360008842600d4080f014114031007080c031140c10b040d518400c0c3e61611407480311850b0610440864803500303010310707030700000c500404581d0741e03980079030f8009418221400020b42c0d0701c45079403007d0100840002403100c400d80c190002d00e4200c41d81c030039050b05521041c003071000c240b0a0b03d20140c03002141c050074108040380e980010300c810842810140c00d0180010b00c0741500303100341d10300f10340030381d520101003000b20140d009050b201d07030402001e1814141d055001c001d03410740541c07006002903500c19060140501565038500036503040001c640105180c6915510800001d031222036084010000d010606505805107002522104054401440080e800d014080844a00c100c90ba004140641c820411903441024010304240d40200b1001e03150980a501b11150320741d01640030f00302004644045101d100000c41c44d65071010315440c0501c168240701000303024400d103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 807434100 1250 807432850 807432883
    0xf020621010e0f01060809032704110421080304260304030c0b0603030406050418090f0503030403031103040236070e0a08011b0c05120712030f050f01120203 69
    0x21580c41d000e1000340340f0881482105891698840700181d807240d20458951655a00030010011740301d0007044600b101a404000092464422a002500759005650030040c0b260000c14200401104410403041c25500010301e119810380f0381e1600320b030300c1c8001000a0001d8000c03030f01081641405100b0307100c021105425290712402c00d468000c144038407091040e106d13403c40802103650352401000302c070112852500d5403480d003442d0401d0002140118210054115a50510000880d4150880c014280e128901455503480e1500d0050110b904c0390090003c1680c06004000068491854000c00052051340800ca03004526001091075484540c082041d40c6540e014000c0c25034200c0515980790b02d085400c0c005d400d172545181c900301c8210144410798243ca60a1486109024414490140b4010000d80e5020f205224170134265602c0341c117048940050a40c00c400749103615120303900404090500512903410040000306a9110601409440c00041c0411400710b650400001a5040b060316 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 807435350 1250 807434100 807434167
    0xe07272717130905090f280c1205060a0213090b04021308100605041e0c050c0105040302070e07030c020d2a0f030f0f02150601121b0f0c0f0206 63
    0x1592008000c002d4840d12440038200130208844e0f100205500521003180c1c2c0003841c00c001d101135243d100c1e0b2a986212003421240525840202d0350310003a0074090054800380842e003240900c0c240340ba0100040168840910604c1307200d81c850f080c3d8140300c0c1154100d4202050511120000400901c91004d200d07440f40d190703040000703459001160100480004c1c4d40100040b540c0c443c1880300340d03108800103c0e11a00c0c5560b1404d80c070000d9500200038441e0f075142160600321441c640e542180c1d400c0e0781c190050303848036008201c070842c1e18151039800b8000c0e00e8140305500c0c0000029559180c8200c0600c00d020b10301025454151070a040005800b0381200c0301400701c80c0a041290380344241c45001d0300003440b800703420851140922841803403c1c071198001c101e10b402d02c001d44030b0500c801504250421501d004544c150708101e0007881000c1c10851800c22070f40c2c20303041c006040d41e13920301301c0442400310355804940407a203600764a00100303806990b030716034a2014a21801c82c0c504c00c090034120301c000c1c0d030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 807436600 1250 807435350 807435367
    0x50706200304050a15060303050d02071419060506010e01120b0f061813050c030c070501110a03142d0a11030106020a0611031314010e07272717 63
    0x901360f4a06019102c8241c00c3c0001c80d14800a580a502001d0b0109008101e80d17000c90740e041d4001c00045018002c481c0d601c100b06140c40b81001c000001c1c0551649500c20712034103204680c480e89801090908026008203240000039004c00e00a0321001d1100d0740ea1414a600b5485420740b94540c600010302044d80c8483d0a034510329486d0480360428044c0c4c6d8a4501c90b42030921610401c0c0c0101d666640e40c60550b070310511410065444010115425505d4030714280074603184070040c1564400ca80c4001c55181507500884030007060060207403400e0281101006250000041c0641442108003041c40d0140d0740c003600c6401034003041070700995100f400800014919804208181d109210310700c01e004140e604000c841d00c6000030303504503000c2210003081c0c80c001018810f1041180d01d1400000c10651540c0b4101030508855a1051082030141074240080c00050510501030b1130a00c01c0401901da42507655100712070103800780750000390031290400c0912601c0e554641c51070f0280c0c0d12039951148103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 807437850 1250 807436600 807436603
    0x5041a160c320d15090602030c0405040b1503060d03020f030705010509160807061d030105010e060f09090a080f22050a0501110c01050315040504050f0c030d05070620030405 76
    0x102d90280c0d40c80d020322036a0181c54003101d030740020701c482c0100700000d29403c0303803525644402d24846060381319994a004034005800343c005544074490041c41a5103d910b0b1000340416140420700c4217129031241c17015a1501c007049015aa0400f10950703641d4003c0ea10703464180c1c601054006a50701d244004221401000b405401c0548980100780c26101c40116024101e0351042090082d2009604907900c00d0011a1040300c958407041c019914105101d002c1d0b80100f0308551007038121800d54080b5004000e10303070512140140149509955408041c42c04248481e121a0700c0c8000410303070a000542141a2007441c425a42080c0003032503408508814103484100042c080d12429000d200400c0b0005072941c00380e41e00c1c0340c100c0311034000b400c0e0140c511401120903500c01007402e80500f0340b0340030105103500c49118441c403840c4120001d201c2000c00c10302d120718090034038200f24481d13400112520b00e07040d4000c069030350403a44440b0100d00f5605c014080c564158103000d51416840c0040100814001c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 807439100 1250 807437850 807437879
    0x218040201110f0d050901031803020a020a2c1b1308060f1501080c0c070905061908030a050c0a200411040609140607020a170d05041a160c 61
    0x100340c940480e0006440e28083e15085840c0e2204001d03041a1603c00d500c038000c90003807002850516001070500b0a20040e1551802015015001a84103204080450502003454030207056800216041c80100724016003846002c6c0300b000847c06004000b103180e00c0c01d070381141d1030110051a10152500907032986510403031201c0c4200c50f298403440010444e04102c468440d405014190003a40e070070003a800042d0f50041d400f07800c40171210304c00c0140d1690154140070300c101411070032401107034908001c2c041006080040e04200c000001300d04040020800c00001c452041d0b51609127a070300e5441b0b000eaa076083c000303169030292a44280642120300348511110b07040b800307101124108500c10801078241c1280c001c03405041c0103d990030790248108070b01141402d640784c000403e00c603d02451a03000c0f4900030090703880403907204040e040c02c8401e20310901c07510300da1160382d10302541403524208424103500d016004414440c5e40000312408001c41140d00042185d40181c08000d6031544c41848007400351 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 807440350 1250 807439100 807439103
    0x13091e030801060c0f02040b120726120306100306050303160b0a0504020108180102190e010f02150604180c030809040e3004120606030c0e040308040803070c021804 72
    0x11100d00c00032850901681c00344d000150802c03506507050100f9401d010040030160300080d40141904411a50030b1000c01082002c0c14802c1045003070810441d080c107000d103a05400a403101d820020420321180c1d55035050769030045040f00ca01b1444268510254024107a6401017500760000240c40b51000d81d2412084c0a42c2d1b101302c40402c2c459550350207410031680147c078000c3c0011000d40c0400c0c0800c1c40d14950456039a0690001132a00b1424103100c11800040a09a000b0450740340d02c4200541e000080d00118007100d00160424080d81c03601070102400c000d0010f4821980e6408400f0a0485c80801d182d82a40c0014031000c0d07941c690514080c980c224050481c4203508009c9015002e0740003180750003015144480d5500e180303501c00c04a8800704c800f845100d64840c41070000054561054005081d418080c6c031000071550300f10308241d100070040b500010f49210302102440300083e4440311581c1d00540214256480c0c2d124400200d42c545031328503000c0e600082201b40201d500290034031540c0182d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 807441600 1250 807440350 807440357
    0x60c1206150a0206372004030614010e041203020708070204050708011e0518040303141501120c1d0103230f01140d060506010c0b070c03020d0905060913091e03 70
    0x41c03201240d44c02051803808140c05ca5105c80c04854000c540d66800201c02e41c8041704041d43e00780015031031401c4e2a007081c2e100b902d1541c1c072945e24000900340660102c1c09490b2101c8000702524040d21050895800462000c040560004180e02031141d9001541c014684c020418445800d18000080820900303005850b284c1060348550350011452025041c1299400f50503038903240e104005503074800400410540c2810b071130380d501001200c18443c4091194200d01258201d2051540005140050540400490519001002949907040507800c1201d0720003040c0b00c0c00e030070324041c012005015040c00c0d0000001c11a80d01c01e04904411810038410300302c030b069608043e03a030b828500c6101c1d411406400d4000c00c0820790b074008214607070000c0e6807203a018100341445a8140d580c040e00040102c84160005015580e100b0805605001c4695104c6a600c2c0c000401e500f0240003030f40340c2c4541b030080341c4a03815005050700303840c040303401c0700b040035800c0340ea03d6003d01c0c4d0390700c07612921081c01c00044000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 807442850 1250 807441600 807441631
    0x60102011a0310090c03020603070c1509020109141201050a020a181a160f120e0906090105220c05090108010609120b090309032a0102060c1206150a0206 67
    0x801c040c0c4600c808810340080c0100541c108189000006004040742501e600c12080300c0880541c5400d40154001c2240740d8506213a81c5e100c0c2081301c01040c003001c50b00b11031424042400c001d44e80c01140b01b0280c50b0701c1000700780302c583c80900090000d40c211642e03209550074a01007181d8940c860b40500603030680c0c3c3d20f80003655099480324105000881c01130001101a811141a01741a00c1028101902c0104000000d822541d1118143c6030000da604a410310400b01d01171807626413000e100d40c0e164506440841041c10b0410000d51503203c14018540103100c000340040c1c544e600328540d20040920000200207160410400402580c02501500e0109289000004e00305100b1041030040f0f0305100e2511031818841d66909280741c00c0500925490700c82404001a070396002c2c0081880c03440c03016422420490004e07812410741e00310340000c606641004040104c1058028111100c010b01c10f02001e0003075480c81c1c001a000c40c800303507000050060104402c055107400041c03490040050180d10b010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 807444100 1250 807442850 807442871
    0xf07050a120e03150a0c140309030405040f0513080a0201020d0e06060a17190c03020438031c02120d09170301030203030712051b011e020c0601030f1703090606010201 73
    0x3e88022010035800410340500c0068601c01c1603500a011b0385450f4506018400500e2501030200d40080d1001d60f120f4000003003c010030b01d014451241da50307644c070609029a14107846100d10b00d142d80c00700603003111341c00140c104019100f0340c1221401c0c01001c1c003c0208200e000001961108100c8a890003441c1603000071805045d003c955000d4241100010800090f10f03031041c20748000860300446103a10390140100045e9528040c0103805c1c338110711604081085641c0380c9443d01110448222152a221010350311a24081138680340c8800740b9042090711109c19100b2464020072580c2d410043d11b0100f41d800c01c10003036401205203140112103c2c15030310540015a02030380300c00c0c4002035150b0b004008900c0021558818402c004030141412070074945529144207209018905034041655620704049890344001104120580c807072800f1824002c40424850f078500c0180406040020034000042c01c1002000c90b44120840e481c02c4103880e41410000903664150554049001d5400d11800b040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 807445350 1250 807444100 807444103
    0x60f0c350c0d1806051c0c08090c041e0e070b040e0f060306070503010302010c0c051e03150c2205031c080f090331120c0f05060f0f07050a120e03 64
    0x10f2150700034036020311043c54584152803a51203c40320680029a039040b03420700580324841c020b031407161500e0303441252404000d220b0034812003c888500c214905000000c440d8000d1600c0000300040d0000003d50100007068289001d01070382c4003082c2c0110015011030444000b6a4282c0a03813484003500c94907494920401da1165022039640000690900042016612940c0000c131100e001e120095030282e1a000400c1200d034000c0c0e28802c01c04c41c00042c0d081cbd142010030400c07030440c215070042c3c409418110a0740c10b503441002021a005181307a1842b840807001d030006000101780080c2207604003446044481441c038160b00140003c1080c040001da02102d00240e140e02c242c1c80c66000d9450040d0101c0e40029480d1010340703800c0001c0b0314002c0302c07090030320020807180906600e4005c145220b005103041e050702c114035000300900b4081010108456102c00054a0b048124141881d8403802c01280500813230042100140c1035105035075100381404501d40d00031b0b44045241e510071001984c0c040605 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 807446600 1250 807445350 807445367
    0xc0c14060a0c06090c030c1802131a04090915050105010c2117010b07110604080c09340905060a080609090309060c010c09060f0c350c0d 60
    0x1550080d4042100d554107500c200031108245116040025103101c1341e4440307041c80341242d0000c031804440d2602c01d00628036800f04682105120303680951522150101c040901c102e28824801075130300841d01c40d09110300c980250382c040e2042a0041111105600b07100030010112214080a00c0ca40b07400440d00b548110024004550031181d041c0c404200040361015110141d9034a00402401620b5402e080c2614509940248155140c4688440b031a0170008901c100302007909200e0f032810003080148080200f48901d0984c003c8500c61003503a40c08490041c00c0c4140341d00c4030600400e07034065032061340300541600510441582c074042d4031510740707081c0000c6200b6170408601141d0b00c540061018600b40341c246a000602d4015241420401c0001c180940c004030a1407800da511001190211a0f000031000c00416052400b00300c040f00004c0003401b050307a5401d000c1c02104074080514103010840008040340159280406070703582c209000300107503401c1000c080d0303058000c111a44289501c2031899 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 807447850 1250 807446600 807446639
    0x60411040b01170a06080703031214100e07021207050318010e13020d0207170403141f02130803040f0815040b13030e03030a0c0227060d06020d020a0c0c 67
    0x30780f00002c000c0006070800030402044003014640300c01d00803a03140c00601c03d10004600c291610300340e038003c1a003081e080c6c035000c840c00100b0011070010010002030301c00805080f00c8000c1c0340c03c1c0c0641c03130f1000200c0c1401d201c421458206d203000074103c01081000401010f14030070601c041103803825110011960395201e104803680c0144004504041e404c02039008010b6105e04070001444c200701c95596802c01d61031562071129a400210b03041040c04861011101c010000d00080c0001c2200100010540301d0803200c003045159000ca0000400d40c4001140c9011313101d150103c0e901d86d83c1c2e03082e0000c6041c3c000d0055013624028144202c0d10b981240c00240d0142e9031041c082c1450342e0300d508052071083c40c1840c0c19001c0045070705d81d0041e5a10284003d0041c00c0c440e544c6c1d45580359690051250480010284429480c041034608144c0c41c110780410f90081400c4070a5120300c051810000080d004560400c09081e10010301d00740e605402020710740001e441620f1090303c2c1543c0c0e40c101030121402545 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 807449100 1250 807447850 807447857
    0x131a0c240604020c1c050304050d020303040302030a05210a0e1006030804060509060f0705060103021002061003021504030c09020414180406110408010507120f0b010207030f0f080c060411040b01 85
    0x4101c0500e031940142007425145801c8442d01c000c281c109000c1209050440c2001c5030b0000240402e100f0180000d400f01002c0340001d51031820140d500079a00c0c0b2440c02d82741c040120207d0419107006400000c1840b420152500b01000c0c10801c0b4404014188221141c035684150402ca032040d281601800c02200d1300030000a0500b0314000c030503074a51380b10f008400d41c01001005886071565104028104031402000146020360543c81072000c0c0201d03a54005080d540400100221f15088007058000c3d02e5056030002142c0c0d59025400581d809240c200034806284480007103902c2031140d0290040f15021404200d0390110030381030006c1000d03d0341e000f0140c1035a03040010007040480d001207034200f24400b891b6161a030b98140706800c4840543e052400104003010a5209c0c0080f8003030301c0c06860719034100f040316818a40c0040d68803132651000070000d01c0c00109002c00e100c013610108040640041c0c00640c0c0d041d9405d001e80e203e8400f150101c405040064901007141030a1280011042c810b84 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 807450350 1250 807449100 807449173
    0x80d0b01111203010509040519060213050108011211150c01200306012003130603020c1204120201030b0f190609060801180e1608010b04140417131a0c 66
    0x90100001001f001074800f8859515a60140545010060503950252400507107640b0340244004114840d5400281007000c44001448940d1340700d640740d1503407940810f80600842c0141c003c640c207048452007030540c0e03c0000c54000c0b4501c0c1c06402500c420084100403011000400c400c0b9170003400251802d5000540c00300403201402810f42c0220041c2100c403003141d06007070800c0c5440c5660f02c5642c00080001c0e4000c6408041e056041207030708a26003001020b18105800d09010743c2c03142002080282c1090344640100c4005d48800300c45120302c9802030f0049251006114054607c03506a2040c0070004800d00310014026108920042c1a601c82e80d800c46081121044240060070515550380c45074001d101000c88411090000040117041c0007002150f10281d0740204001c80360100009407107002d1584c108030001d032500240b020342e004904917442e1501d0007607048182013240381d042509002c1d08820180320380c00400c0007520b4858015001c692140c4000c4031789209031101d1048100c0e40040b0303031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 807451600 1250 807450350 807450359
    0x6010f1a1206060c12040b190801030302100b2206060f0206060603340e190503060c1b060c04090b0409030c110402121f060203120708040f080d0b0111120301 69
    0x24002007030300c0b40a51046a0741c02c04081c02c0900c299116502c000d944040000703101c0c0d05220740d60b239002441030003418181800d600d1914041d480714841049101c0007996040882c1c004d40d030701740703c243c1903031016524841d403000117422071801800d0900174000441c0c441c01c043c6154070310004105129100c080c228500790b40350350032081e0006c8100300702c0b5200115501004054105101e0320f4018540266998850501094081c080300050803003c107891448011010f100507180000ca00b90480c1d41840790300d50b2101901d40c2d45064410450026900e4024a010320032002440c82c003030015601c688404100d00701a1038100300443c7c08a543c000c0115a515683c0300200701c0f000c040351013030007024002501e0202503074501c203c010400c0329071058005061044d1700200d644d03510020082c000c40d000a5140030100c0d001d1074441180142500104640d4900050410510aa411401581c403000c0742d43c40744400400c800103000c110f00c903540083e04a0141b0348588000181000c1621002010a4610307400d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 807452850 1250 807451600 807451609
    0x60c190f0605101a1b0a0302152217040f08010e060a02032a0f121b1c020a020a060608010b010e031603032f1f0204050a051003090506010f1a1206 64
    0x743c04506281d0745e5120001c40c642c428041c0390320442c42030307002e803000c9c84182001250f8420003900c1402da031114083c601105800c4812910420354010f00d10b8030b4981c0007107022815520907074000c144a40300d040b20000301c1490540004554065071000d0f207903d0b0ba036204c80f040403404100c584004c0c420b100040078815494120840410b02c9140401030310b01400300b01d1900503980b05200d480d940c02c010030204164150314009200c0503441c0d40d9425481c1007103640d01840c5445944603104800c60380060184100b034020400801d01d140e1085003400981c0da2001d1042c001d022944105010488401c44034a507450081481080c0c130068903401d00d92b403801d648007220300e0081c0200741c0500070240021129030030228091006003101442c010316400d00c41d219108007031102415991211401404203112590301c900110703064417002c0d03542e4032058180540c220007600010401401ca801213000203e45504c103803040406171400401d01e2084803a001711502c0072841100f229041c95210080461020b181 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 807454100 1250 807452850 807452857
    0x70f050a09210204020f0405090903070c17160303031e14150613030b0103030f050304170304081306050a0e0a050609060c1509060f010e090c060c190f0605101a 70
    0x16030442c10300c1d810b241940030a0890b07000c0807160580b548081340c01c002900d8454400d580c0800c10f4006507003003103480e58030101094150b011702810000350910841011500b000700c1001a42130700360b003111136540c0341006801004d1200c0d101c2a02c0300e05000e4803141919501803200002103640e9054050f98a03600d415101707501044005910440c10070944000200c1041d180000d140111038004d095407440c60058450000e00f80b00c101030003018070410000c0f441d40210240302c07030751240d003140e62640c42c0d1500195911428101150a01b020240861790715408400790000c5452519401c1c4100e00104c100b209070a46071048a5022038100326805481c201840541100f04034907040728007194a0b80c03000d120400040743c100d4442e41c046000c100e01080003120081c01481c2114040d40da50400784e869a40b20941c04000c280298000510811075000c208034841055482c500100d4550020380f40812075000400c10a58203a41440041800d2188803280503007154000c89001e00c054041c1c00c1907241580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 807455350 1250 807454100 807454139
    0xf0c08090615040609090b070906080c0f0a1b03020c090603070311040f0212010902180f0f01080c1603090306060806060d141204030f0b0106030e032a0f0303070f050a09 74
    0x141c136070030002592072440c003e020002c0d100301c0c40303110303289003c0d6401001c102c1180d03c001c1c1003000000c01d01021104020440b181e03140720a031059035440d111442501c2040240420f07003030710b0311046200402d05501190b41c0401f18000c407040c00072600c5400030555a02c0040c0006413a00f80d11615480c0540f0b0a640000e00406481b90094100100b1003404100d60500340c0c44800040e80004032035940752912401c001c00300c901195000c400c0f00c801c80c081442400281c00c0c00e03042c01802008103162076059000e0326901200c4400001e14006240350003400450344d0305c000c8401d1f40c20014042103a0b232010134902d100e104003400302c1c08451040d2302e81e00c880410f550a90005401240800a0405e00010047c0051401400c0304448210705140028464405074000400c1500e000406411888044101d810b1036400145078040b040c0301e000e820840317030303848052003405100d202c180301da52010100145118480580b90240080722414090b905441525000070009500701801e1094920a8200b9003440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 807456600 1250 807455350 807455359
    0x402100e03100e0a060c091a1603050d09051009050f06151918061403010e1b03010b120d08011a030109020a05120711160b12070516060f0c08090615 65
    0x903142d5210007046901e025803881c00183d2039001070107021302d488120f1123100c0d09040d0a40c64101c5401c5450200030a21500a040110001e00541c0522442e0042d1106d5a00a41903894400c0880c0e01c1c040100499142103c040c040c000e0046400c01313010a04510462440c2440c0340d41945500c1003000081101f00c55500e06c204c0700303c0224014201428080ca441c1c40800001143da050511749400c0040c0061014071a03070405155090142e00400c203581940700360050039140e1000c14001038090405140c4090b0403126400c8007109500d0002002c0ea0301005588900c041640c0b20132882d82c4007000040c0f030030f2804ca0200010000b01c091a8010040803000d450800d0400c120340b4070780d08003400103450f0302001a0800c420540401804d01c1200542584ad070801a00c1c1071400c41c0d09111130048668004955090380c00040c1c44034059000c0340c2074030900520188011030031740740c10301c01400403204010125180015800405029400f00c0c0d002d164a18018035031a034030020380680415004180c183c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 807457850 1250 807456600 807456613
    0x120c050f0610060908161503111204020a170c010c0602041707060201050a0605130c021606080a0b01080c030f040309051c0b06090c070b07180e0402100e03100e 70
    0x10020500415000c0d0658500c01000c083c50700d94010000c0400e6045064140c22070381480102113442603240c400c03a902e20020f005040c0d0300410079030040c007041f4045030461b0302c0010240b00424005101c1413140e4801c4801c520001d403103003151681384020414035492030340b1210110090f03600403102c0e039200c2849110f001d0701e0316458121042448000204032882580a04014401140c080c01090761013034035114104a42c41c6040d00240c91400300444000c1d0041d40c0d840b00080c8c86100703221003115501c401200c0180310380e0707802c8001c01403e002c440740302086181c41481900c541c4250412800b0b501c041c1d8606013103850b010301204180002a03c105e06029201c0000507650701d56140350140301500c42c03031200c00403416041001101c0c1c6c00401c03551040b086030302045030340310381038042e100100e13042034a48500b690350310700c162804e40c0c0800c81000100b0190000080c3c982c41003014510a0340300781c5403080079208000c015500c640803292101e515400000341d00110071050343c0030109044460b000c4500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 807459100 1250 807457850 807457873
    0xb010207061b060603110f040e0a0206090a080d09180b1513050406090c02070906050109182a020c03070e18030910110d02120a0807020f01112203120c05 67
    0x8a54450740100ca00001491b100c001528042c03d1148038920160b90070701001404050550301d031086a04000d20441e030200d1103141548540145a0240c20420111603620450403405001e041345131141c0b1011540c0c09100351410360260040328070b00940606826203540c0302da0310303001281d00801000d042c1c440c04500f0020b607aa840c0d010b0003000f003400b000001035070000e00f040242008178139080800c405040107804c003c1a40d01401460844885114455a02c0400001c44c800760043c500c012240c9001040c008100d5100c0c040c0c1c3d400201030030b400311000c0828400605807158140c5c485c0408440b2000009003041c40e01203005100a0000c2c415a071410f001c10700090452031442d0450000a0305807040070210301410010142d1007000303800240025101350000e40c806210b044144003c20a882c4049485540208210040d100c1030100a00098007900c1138076845800a5141c000b440340b202e130f0b07850954038540a1100a5035000f0004001d200c1c0160015a403010b4400800c0303803244134008134080b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 807460350 1250 807459100 807459113
    0x90c050f030141060f0609011e0e042405040f110d020706180f0201030c110a050615060414241225230415180602010b010207061b 57
    0x2043c0500760102103102c048541410046045562070303094841c0018414107940d48480c440341c885048413040d84e11014040100c5400389000b0b04d005408840228111505400102810300304800392410007031600c0004040700003801d03c80c030091000c4e071089001c3c401800d00d41c000b0803800b030440401190445510090034a10360241d28640f101c1d41d4040341c03036000c0280c5e9010340a81d894915000d0382c01106039850b100c440e96012240203040c581d69060720b246140c01101100031550400c402e8940c00c580710300707100340c407003800302c1c4c01d21540d1000380c800480320319007402a1030580b00d0540d01c010700d070b4070080700340704440600c22141040291a42895400e040070400141004901d074075918445e4141410106054156020240104d80f88104904aa41d84c400c0e5100c030100e9031120220b2280302282014503040c030442d0400540003611100000010741c0294074001064003035044c8608c182c0d40d8010490880d41c000441c0782c0140c114500400400e0f1040110b14581403103034100700a812000d64684 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 807461600 1250 807460350 807460391
    0x140708070906050f090c0c011508010c120e070e0405011d070e01051c060b0d120e030f030a0503240d030c0b0a0504020f2103030403030915090c050f0301 67
    0x28160340140014801040607008410091000340c92a00c00d030982c1d41c001607400c0030010030107020180049981999800c00b500500f003607102141c0c0c035030034085c1c0322140d00d03010b010b00e5405e50000c04c0500c0d20059200c1411304c1008a40703900e46001e082e269081c400000440c0e04041d0060316030359220142340c1c950018220454415801d801300520b10145094100000f140c01603000320710900d800c03090703800509142c903e07015066900c400001051940b403c0041d4200c0c1213408080c001d044101c076140c403140c2d0491008000300350114212515074240c04803280d40ca2182c800c0c068002082440800c1d1304c4a45a90304412140b4400841c0c00301034000300c0031403030740340032203209500043c109041041800764004100c4d801c011010b030184131510307064004c101c0344c802820b5803c0c014105880368120203010600600024001003058a6890401d030038001c001e01800b00703041d54407800002600d03105000d03034450110010380c44201716070360303601e85410000f0158005109507015520f502c180c0c4280b980c01c1c081c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 807462850 1250 807461600 807461609
    0x51006090b092106040c1409041e06050a0b1e0d06090212060c030121020a14010306091d011410090b0a0803030f09120403080405061312030504180b090f041407 70
    0x14066407501b42080625060103a000114200c0d0150b00d07030403140c0340c82691a42c01508006464204003030941e8a00310840842809401c1c0d41c07420040c8580c1603c81c3d00090340500b000c480341503810003480c9540003901e142c0d5207aa03504c0550b4582881c0003408640000a01a0004100c0201c20040e50029414110101d41d400d02180c0000010b1102186001d6401ca01400000f60301342c00300171603070106161503454010380300c2000c2d1080040480742c2c841d0301300c0c5000c0e020031040dc2c48581540200c00390700d40541da00150540d420076880b805501006041c652140590405145c85540b4020140004115980d03609400051406001c100b440341000158014540750200394014940114100d0808100e00210159060108020030220b28141c3c241c9c0c080d01d400f12407240c2ea5a0460010b410a25095403040058812154003141419013110140046034444050180d00705684011802150301621107294001200c01c0418046071011a050741d001d0311407085500e00030b022020b0181307450341a911 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 807464100 1250 807462850 807462853
    0x121d0a03030c02070e010b0d09230a020a0e0403080c070812070f0212160b060a030f05030a080619060507021201181719350a051006090b0921 62
    0x1220b12000e9410400715008000c40f60b08001594141400c030b00d40c91149480e01d09140307171a4111803081c01601d440c80c1c43c00e00810300700310141c0d00c050204a502d41d800074000313a21a00785113500040c464282c80301c4070303c034542c140c0d00c002907a40c0f43c400420391600604d00907504000d05100303554103001187c210500400040d1038140c1d1030140003030001c1c507104030001c0030b040c200c4007445040d424042041c00c90710300356400b00721035010740c1d102e10100b9507111090380007402601c0040011400d00070080018541c84503103a0312014603075245010f0084845015040075401d0707810749401c115080c401c5000e001d200d4030042415402c2210030045609442141c42040660f020180a203401c100079041091060381100000310309090000e102140240340d6030300500d050007442401c40240c40150a17014100d120420850350903541d40b040784d840c0b2100101c90b940d64162800002c80c0038000100342070303000c680213a524144064108643d04407240c20548916801140d83d82440b814a0b0291980680650b03040c0d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 807465350 1250 807464100 807464111
    0xb070801030204051e0705070f02060f13080705100e0303090405011502150907050d08041d180a0c030201120f05151516030c0311060901061502030a121d0a0303 70
    0x401045403800340103900c0d4a001c07100b0088017030141241d050b9100c51207040860300d50303c403410400c0d921401403030000e41c4240c0008002c11801d0300c4c1806002004064222800d4a50b11003104a07030352440c50242d294070000e102d0007000098462008a691030700c0103000e070323818041c00340041000d440c07003030700619243e0f0008010500c0655040144600080a8141c20300740c43c101114001d41303510080c0111401299a0480356007404400400c0750000c000c3c070281e80c0d001c0c44000c2c4003406640c505540a80d90380a10503050070080c000042d008240f960000b401e00803440c03844d8015a0101c50004501844d1525506009079210782c9108051180e00000c68000d80c0b20144010482c140c200501080c004110a101854150042c0740d10352024690509043e80c2408090034141c1e201c881c1c04401501c039204600c01c0002c0707a0010740181e002c4891410a1b8124038042c19400e03a102c2c007402844e04001050101c0702c280c0d6212940100303894054482a181c20000030761411803e00c6c0310081d00354003003071729003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 807466600 1250 807465350 807465353
    0xa02091009021812030403020603160201020403080706050610090509070f0e10170f011203050f0f0c0c03060709081504140f21031306050a0e012f0301060e0d0f0b07080103 75
    0x1a416103805000c070002540c902802c40c8d002a10b07900010f0040c5201955040a0190b41c5000350704a60207147c00400f11a21072003113140030700c0030305402c882050103034840044041101e0b00404055041e1075006102d0041903a40c403504a0720905040519020000c981e40305022a807a6122444503504096842a040c00d0241e40c1141e60340c500a014100d42d42200d400400900c03a0200c0c4020f000e82c1d1501d030041d82c034100017400c1040343c041c9541070110100d00003030107669850b00142000000e001603041ea046591111810340d4005101d03c80c01d140341e00300d82042450581100c4280d68054031452461410300034200c034181c070b45040725040f84555484000f400c030784038a80b4540304d08940042080d461541c906440d01044020398004018420b0303448030701241da594043e0304031410b10302c0040002c02c001c000c444891072080309101c159414803000c942d0008541e40940702180e069a4650701ea01d41d81010007010301c90b1809400605072200c03040c8560040005016252580c01801e03039640b418481d5055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 807467850 1250 807466600 807466609
    0x60e090a1716140a0605130b0901270302070b0d0e0f0a05100203071e0509042a080402010203040801060608040c0b070302101a0d050303040b06010c03020a020910090218 74
    0x150303a00908145814000c0b03884016400a07107411107540300d820518450032400805140801c00000185000c1c149010080042c2a0074205041c10f40500c68180040d01e4a04846003200c032000e6407480302ca10107070607880c0d54641d8502c1141c4113520920460b130b143c3d6034031149a141908103041d840005611458025140c2d41300f04000400c000038103019040e1300c2080c0d52a50b6960041c4060ba4501d590044001040306004101400d00c41c81c0c0a540060490101030380102564003548410303102d9854030318104803469800d550355901100072019109181d5a004090343c15145c0108200d0441c401004041840340e400c0c01101c0082c055070b08c401207582418034111144c003400c4e4000850340340b006e008140c04070382c1c0058500c0a00324640b100084900c859401a00f40107480c00d51641c000000d8000030003005800070055128600684200400e80c4550004445800000302c003d0010b03070080c2c02241c00341c82d203100050380008044441045a03517448207000140e810072401c624011800300303c008040e00b030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 807469100 1250 807467850 807467873
    0xa0e0c0c1615080a06031b0602070b0403051e0c030a06090b0105041b030b03101401031502131a0912062712090607020303040f0914070c080d060e090a 66
    0x4001003a082550308050b0307070340404800c644800c41001031032000300780c03a0103466002001171038002c0c42d103001501540c040d60075880b80341e102c1c1c00d00501c00c2d0040000da0b043c5100070b841c00c0d03d0744030340609802c072110b240289146007491001a81e03805581e01c08422aa0100041070209200ea0004074200ca668142014032440c1603003c980a0b0b820407445030ba40c080c158140f040c80700c2c0a41000900c0c0011180882e01d40202c210700401003503d080242c41149200402c0e986c1240d214100000144001013400b8060b40189900c0a100074294102444244c10001c00038101042d5240740500b81244400041c12425100c518400503030803040c248459030401c01000d0445101c0120130b0502048482d250316520107881d600c2c961103c4001c0b030170411a0380e85004032121140c004040b02c1e10b0369180d001e13681d10f0301118400d6041003498071105030590445410064480e4a440d01ca9040100300c0c1d883d800c0c41c680c0110b10004006940c0c02c800f284410240600b180900c00e1b440050a14018601d061703411200b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 807470350 1250 807469100 807469123
    0xc0f080a0b07020321100509070e030f0d050a081902070602070203061005030c0d02040222080d0e01050702091f0303020607090801050919050f060a0c17041109060a0e0c0c 75
    0x4000708240442c0d502011040448507120f510f0010f06070791151113207034500c452600b01e48da01c003400d070b402d11201e107500a880d1440d1101c210265400c03c03401e281140d81c0c0340d00090145021401c20b010625030703a4080e1030990b81c03202c0104403803003191440c0d8845a080782e011035400c9810650105844095040800005500420b040090b00c04036041c600040d0b82d45002210b4240f00c0c0301071481c403208541311601a00d43c20b4100349a0417001c00c04011803181040c11600035400301d8452000d120351624490b11119280f1507040e15064680b9903175809000309040010141c6050804007550715200c01e003501c900c100107500980c0a8600c50a00f550000d24400244d482040180c0c1000d00340030f443c60307022a0300c0c502c080b85030a45681081d1103240003400c10300c204102114a0180341c0070849203411302d42007109100c10691b030380c1c1c000c03501407003161f52040010f0344c6c0600030750005400c1803100e09140e072803c0e800c250010200442c1c0c81d0303900c0032890008000c44150561000100745900b602c24100460201300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 807471600 1250 807470350 807470353
    0x40f030c05060c100b0303070f0c05010f05030411010e010302091012050a020903070905090708120706230a0e16170606090c030a0b04150303050a090b04120204090c0f080a0b0702 78
    0x44124042203540350034120102c02c00f45e9856842c05241c1d0703010021119540e0b8041c6610301006101d0500710040da440344120b5011562821164140c81d204400712486158450301d1400345c00ba175000116282c8190048590516500300300d43d1521380e0751130554603281411a40c070030003d2212210f42d60180d030360107000300d003080b4010300086959680110304038003034400051000503e6a04c0c01d90300c5e89401030961040d0303064001d0451400b180c0d0130110041442d140200028801044061001445550b0030f0000c200e8003d08280840c40d0b5030802d420a824020248048945542504d5030b0001d528131f0fa03512004e14180001c1c28071384170b240c0c02d10032980e12400440c0d060515103000781c48039009100c001d12152019907140c0c200320980c1e4695010140403007520040e0703501503449241c0a000c95001c655920301280c255800050000b0b80041160242c40405c2184a20090350f603003444050308041e04200ca64141c00100480c20300180349022000f060f00b00000c00c0700c22880d050034100394802500001c01c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 807472850 1250 807471600 807471607
    0x705090c1b12220e07080108010e1b0603130c14120c0607020d050a05151f0b0f0a050d05250e1e010c051605010306050a030515090a08040f030c0506 65
    0xb584034000340c0d980c0c0c030320300d0341c443d41d00401408032100b9507182038000d1096604180203000c2010b41c800020b5058410300002013002c080e0802d8001c0e9500c400d04e902c00e022500d46031035407809041c2000916000b42030440c6068600d8150b941d01d083c50602504403203071124041c4007120140c6020110010702e00b400350003820924034400d02080c001c0c800d0400290041c04001c08100c10403904000b14001a07420105a590150790b001100049443c180c5400c041c20756408404440a00c982411804031011854605d141007882c0f210350f2416044046010305103d4180200c031001d1344903025113849000032022107c1442e001000501c030714000161b80300d040005e803042c603c6943d228060480d030202c2091800030701c42c2080764012940109140310051180c010030303508240200003442035406440c0c00340c03800c0c04425103450601c43d00801500c000b420f55409410000640401d400f80315402c9890790040d961000420313142c264556000350b01c8614400c55201e820014404030341d20075170160030112007040c40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 807474100 1250 807472850 807472873
    0xb0d030815090f07050a090909030306031a060a0306050a06030c1e08030c06150402161b080109152c07091401080307110402040f140406060c081b0705090c1b 69
    0x2c40c05000b001013081c424001440b07480300f400f900f40c40303000f8600c10405110050440c5001005441c85110460700e100b00c2d80619002420b61850061051102914000e0918a19180d030809450003800469404c0d41d01e11020010070301200559026103002c00c15012104c5800040c5030283d0082c3c0d1014002d90030074003d6501030200858070f075030041134100b04104207000c1d8000003002480303001d80d092115100d240c42407081000800000210945030396040305916503410401e400d031800420300801001c1d00380201c407614800c69100c000030050002c184404543e881c182050044012014a02943e00445040000040c203006603c041030341c100611195500d4800051764078007a504009002d0100400c01c4009074a69a041d43d00410a07000309541031035494a1200c0c4001c0d0031520103004500b420408221280501001e1299540c446e82a82c40c100035803121091302000094041424050300354001000d0fa10b10412030700070040501d03103a564018080503401c80810684041d401a0001080d011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 807475350 1250 807474100 807474121
    0x906010303050c012c0d020303010605270306011d060d030801091a190302031b01090b0310090f020301051c0201140a0c06020c01020903100b100e040b0d03081509 71
    0x604595250500316100d030301c00310310140908159642003205603601c000c0144070b052034000200700c070000041565003402110308201c0e2244000d010b0710f40402c0c020410044000c20f805416107543c0c0201d03642d0b42c0120150310021b03080c940f0aa010301102c00b4148212801118500b41c80345d08110708a40c41203070300c4070341e039000b4116404c1440341101544d40d03002440b0540d00c2e946170000700090010314110040360400ca031000c030881c06000680c02032042848120f2401c04049402a48020503140c031207410b441c1240000813075000601030095070300380c0e031400900b040340f5010754261810402405a1250b0412040c010038501d04055040300c504451404030150742c010704140200c010020340e076652a41c203250142c80c3e1894181004000510025102000c0b0606602404c80c020046080ea29010030365007044059030010307001c00f54044034540581c00c5a03800f640080380040005000407420345940d0700081c1e0b541805810a4000c0ba040804201d011090080340d2480c9210480e0504041c0c00c1c4004242c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 807476600 1250 807475350 807475363
    0x2010203060a0b0405011d0d060c1e020f030d1812030603111f180e0c0c0106080d050f0901090b070507090b040c020304380a09050a0501020309100905041109031509 72
    0x4007900e9151003034103802900d618200e03607056030f00500140f210003030440000344a2f181c01c6100b80b00d5841a440004511403001c03506201c0000d03035400031410f02d032601004100500d90021000007440f00c0800a5000485810003645120f0703a81d240000e2041c41c508025407000c00000e02d091040c07404000c96076050606504402c0c000389245002d0801903410007000f140340e80c954028034002c144400400200044803c001c0c000da6a050f8024008540e940b1440b81e500c403030a881c0500845d200340003003803400c1c1c46180541143ca030305140120b4015919101e043e0702c0c1e88010030644054109040c10300c580790300340c0070341c0e1050003003036904100307840309802c000352a4044c40c090f80003a4100080d2550806090b02a10080150712940b0f20307404082c165210310843d4400080c460103c0c140703041c0001c2a1409200d501c0484d0310603000b661402d500c20b000c010210107150050302c1440340542d00410643c503107118180c80080348000329076890500700101031400c54007c0542c84003025510812808031401b1914 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 807477850 1250 807476600 807476627
    0x32180742030b03101d010b01090e070c031b1a06011d060c01090b07051206010203040e0f070c0804060c0203070906121403251b0b0301060f0306030b01030302010203060a0b040501 78
    0x180340500c8000030341010036404401e0921420300d900002d41d5541c001c1e01c000c45808410007007058186c0b1f51300564030122688190001d8503123040000d51001d0003400b121448a00c00d15120701c4103140d200120720903e0401c0c0d01500d0814011024039110b4000246007500300c2000d00789a600380501110f18525207091010b058000d41d00890803404007102504960362080e0301200360f81c8a46000031000b03041c1d41150343c500041c8000c00300031030643d500100448050390000d0300b81e03401c00d55a0000c821502040a00401c04000d5001ca45001240c902070142c170183c0000d5480e104414050700405181c40da03542c0000203d00d1030440708000d2800d43c44003c44016034040750400f41d403030214044a04500805144880c0744a840703107080118104240343d40032191040c1c021000401c2e664601030440401d6005001d40c0e40c50400050007914010349441104000c5403070042a0340c2e4032980c8003500158207900440145c0e4021042c4542840d160b250f5030701604c40c8000c501d08240c50706000030050340c2c45607072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 807479100 1250 807477850 807477857
    0x50433150c11031b09100b070210020c0333060604030b1e040c050427061107020a03080d0c021b010c03090905040f03020132180742 58
    0x907040d040090185015400c684014161158a0041c12549022280b001ca496101e00003940014840d0300c13000d400c01098401c8403401d10300342107255003408910140f82c42c14500b54482c0604420b072599080050340510800808524030244200a20000594510440c1a61b120500c8108456625880152001c41c0c3d04410031040681300c038060a0000310400002e807440b003404c032040006010356405002e040b1002510b007000750703003c1103417215100214401401c91100003c809800031814641183ca8120b81c081005854030341036900041e01407400354000c9405000100344a51113180e144601c18094102d030001c1c1040a024090f0084060380c400d0b012030500031441d004a003410300c100d01c120060469a541007155041904040164104480b811401503080003c100c1c1d14070742865009800c000d0071441488103c01c11130354610412030083c5851100352610040814501c0204182001881450603600705042c00e10040b1200c1441059107001103d022003441c10028002c0c0000d80e586070440c03a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 807480350 1250 807479100 807479117
    0x302030706050403140a1e0804030e0d030e031005040c06050408150a0f090b092b2114221e060608010e070f23150405043315 55
    0x6415145c1311845002c0300d44039000032403011503143d01310900c1040034000f412031884911035480b0450700e4180803600140042c0821030140310700c1c01d1081c01030400354844d041c200c1001d040080801d1820101421001d0019102d200f072005100c89601c0d504050061f0740781030f615143c01c250781c450390b80f03c0c10264214103007400d00010341ca5645030342c84000007103017419091118200900f04000d8083d07040c2e81c46c4415005400581c1d010b011100c404114041901c0b80821410840319410383d1190f04840d81d5404541d030800c60881000b4892146408a80d0154154003c5080182e020f40a003113440800424091407411900c2c0803a506503281c0c81d45030306000309940c0c509180e1a1800c09032415601900a035800c08150a038009400300740d100039516074400190005580705001e04904140a07814518510b407026034480300c3c140b00517046106142c0d1b4146500c0c1c00e54407000720302124901c0084c41012444030b04038000c0c90101160b501c15041845003803840003810291148180c0402031005003c1c000c084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 807481600 1250 807480350 807480353
    0x140105030d260c071e030f0507050705150310060305090303040b04020f120105060102010c02070302060708030408070f1101080c071a060102100f02090a050306090c0103180b0a0906150303020307060504 88
    0x41c5444203109007207682c0910745041c000421a4181c02140c81180c105203400c51240c66104101c0c150a01076400d0355031240303a0b00a0100580321640643c6083d2644c0c05a0302000c122030300c84104414000ba82044102d50b40d00d04254560000f507000e40140c0c08060400f4103005c038608001040c2c940168205488a099440324800141200300b40d000081d001001100e8881c00750006500092080e8030a800034081031302d0b140c00c101c0c1c86500a00000750701100500c0882e01103070361840503652142c40368140394503244003500d4a000d17a490f0201c003264407078450340b02c0c4105941e1001c2d20907000b541c504509070410303981d6a9180040684500860005086000000c07101c0e031080000c460309500450082100041c02107030351011398404900c260248100000024044c1000212103109040c010050600100c00b000110301512046131191000d030865074094012968140d105070256a940d40001500d211502c0c240c000d0b500d100b84e103600041080c400c1000400e0b0088221000581d01c50301c006050b0751107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 807482850 1250 807481600 807481637
    0x30d0c120e030d09210305190903051605101e0c03140414030609120301090216021e090a0b0a030602070501060906060f120203010609050f040e030d060306140105030d 73
    0x8800700c0342e141c459190400c01c071580004403a0305448210a59404944d45a01d0015484000c102c1c010002003003000a005030351b09038001c0c1c5801c3e00341071400f5100a80c0e40c7d01c07a40c0c0350a001d0200c4000e0180144005c1185107008080d01590041c1401c049403640e80d02c12081c400e111080c1003102c02e0045440e5a41300f010300c45c812280021800c80c0c81c454483c0d0310740c2c0036070221098400b17100b802441803201045075440300103044501c04014510403451682403000c1d500c040d410000260804030640c014900040e903034520800d4009100c01e081140e0706c48854200880d0040180c1000041d074a8441031750403d440300d0503c0c10590341c0020b40566200c07400d1805030700504c0d0702e500242400c3e10700140401c406901c000c541b954221580d80d4400c5100b1202e010310120312080c841c0b0300110350500f00030001420000c04051900304001c100140206080b0080360445e407010280b841c00c039696400500c01c015a61082d0395550b603041200445540c1404040b03130380c414440c0c82a20a0010000c5200c819041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 807484100 1250 807482850 807482867
    0x1204050603100b03011404060b1317070e0a0507022103150a0b040b030402030f0d0c150227010201060b03061014040f120b070e090711070e0c1305030d0c12 68
    0x1000030f0981d03407583d5800b4a403071400701c00c20000c2c4c803590420300b00150352000d0b403050340c51000c52100340a10707071441c001c0c00c0445409150303810041809108000030301054981c003158031440040e000800d4518002c030000f41003191008081e41e4030b2a0b00640b9a5540305500309582e03020854000c02c050000090b400141c003412554406078078420000b03000b007009040c0001542c05248281d00b10348801c0310b0441140d0701d4160307200c0114001071035004554082602c5d81d050180040305408010300e0820040154619060f40980d18050800140c0807040c103940d091040700c00a09a041460b825800c05100107031981c00d1000003281044400300242d491500402d00b21401840403d0104810a680e0316042c104108014401d82c0c044c212180020a001c1c0552144402d10400a20348241a560390a00390344035400040000080e2140c403401182c0c0e0700d26060894020990600c0098499a440e0360608080210790400390007030308003100403c0c03280d8100b000ca45000d60302120340c0041c000503090848490b02d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 807485350 1250 807484100 807484109
    0x30506091e0c0c121e04120215070501020c060414120316091d01030b0105040221040c150519030c0f0e040207020d0605060312040b0913090b0103030809060603120405060310 76
    0x131410700401d0480e804004107503440f10004c0a440000b40941c004202c0c0c0100d204460000c0807a1241c0b00052504400d5280355682520040c1e003000d980751615400c90300318902c11511648520140410310191090840c50b001a00c002811640340507690b9014901016064441e1105401d49400c0e54030300889a0340301802d015070603102c3c00c42c1400c1426030342e25000c0c48151901f41c0480c001082c50704107030080743c02c0b10120000002c80304403a0b1080c6440c00703100402c290f44d40f1250480100e010074689072403c010380c90320340c3c230b03180c480d1a03c032088150114030754002014145052082400545c0219040210351a24107045150400c400b0106020703109001c2c0003540002c00310198010001c0315488180984401d0b0103e43c40183d6006d00c0441d18031541c003e811100006210002940c41d20444070115800100004102c0d0400c42d5258544448280c1049002c0703031800041001a2900700080c550155048000380070001c0c0018a0480a101d0341c050030b40501703000400030700c184245492400051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 807486600 1250 807485350 807485353
    0x2040e0c0d021c020d1a0c19051b01050a0e0f07060905130609050a020a02010c03050c040504090f0506070c140d1b060212040c090612021c03020a0501021603030506091e0c0c 76
    0x43ea403850306d00c50750100015103440589030f030b50206284081081c04d4070782c81804460444500360368100305880c980c00044001e109000e01507808036000b0300a0049a004841c2040045a82001c0d001418280191355250035802e5106d110204012a4001d4602080743c07030688491104002c0301207160050200303508000d60311403d100c14401d40c20403030384c000e00140b94185d00811508400d47c2c1d08401303a81c0c06592a54101e00d0030302c400d0241c3e14040d40311403556031088801440e0310211703654142c2072090450305140070a4482c10584c0901c40e0040e008105007101700c02402c6d007821a170102410410851003026038a98230411501c080101c03990488000a0084440d51180d282c20b01d0401e0f100c1d0301c01e0044105680c14400c0000b4841c0c140040c81c2c04075607000b009000744c00420048900008918070040c1c00b10f1055041c90004141c00b0300c004c0140301811064121310005a00b40681510406402d41e8040e801074410428081c041912085011505200300c10103600c9001d0020964007940c07084242d00d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 807487850 1250 807486600 807486619
    0x1403010e060312160b060103150e0907120c03061b02060412030609090516150c02190e0a05040614070512061216090f1104180f050f0402040e0c0d021c02 67
    0x261981004c130031200c50320a50700300d0040d54801004500745d81010b210b0310441c0c80078420a100c100364121002c0d900c4051081202e82c103660780d40903c0340a42d071300c07041500c0009204d001070090016900904406100b94500800c10388102007000703503180401403010700055042003807249054803d4110746d0007040680014000301505003015916061740c21529440140341280001b103c1d88800392044c0510143d0b04c075031a0248141d008c2c001ca6501644500824841600c80030428504542e0b078940180202000000d5070700c2d00b841d044084510411090244a40700000c0203401d03a802030448414003094411419280c4428000c1682d01e440084260035030f0080000d48043d01155200b082e089a41c224024040100c02014202c204c4420005002d00340801f080103000c0080e0010140b00f04040034040019681544003070501103482c00d0700e0803000740c0d076840c041c0010b52802e400396140007000c07080900880c803900000507000e9215050002e000d00c01420207140041d40d026000103850b40c014024615 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 807489100 1250 807487850 807487867
    0x2040b03070f0806010801050d0b0a060b0f03090106122003010b10180e070f18080109030c110907050315180405030304170307050a0e060d0606050a09061403010e060312 74
    0x812030307030721040b0703800201c0441c005001c039886454402d04a030380143c03081012000c152141141d141000f0440c2d4900d948514001503050046801040700c1015140d18940301d081c900c205031309654003603110800315062200e41e0b4020401c102e60300001661903514240f0b54880d0310703000ca0701402080c8456540b24150741c0300c0f900c0c110b401008000310401d0b0200307001d4040b511072080180003001911050300044502201b81c00d0b1901400c0c4650305910300c0e03509510807955602d4080d0039075403038580c00c0703000405650100301041154401c1e4140c2a0084800c0f090070718250200601c0e5010050885480100684402126442e590101c0d0181d0014980a52007032a090801e19980c3d40140d07811203070300014040442e0325150310816280a6001503440c4e03403034005c04160860f6a5208040c000e03a00582c1041520740004d0307540301d044001e00030b9885513078031103242d200041c0c0350744500e900440600c4500822222021317030740c400712410344110403806507150721080301007454200c90b203114604800c0d000a001d00f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 807490350 1250 807489100 807489107
    0x506010b0919080303070c0201023f0a0c170c150f010b0705030a1d03190b0603030f070215090d0606050406140904140c062d09030607030b0402040b0307 67
    0x400d4405540340d5004421010b400030310030140303201e42d00c10341e04103101058806105a191101550051044400c030307141800511624100403281c081c074800c128140d19002030006820713440036221030b030681c5060134800c2d04058100705400b14010000128080481082480b810685d48200703a42006c0b11800020900305c0d0070181c600b900c0810346000c00c00000240c050819084402c0c4aa00030051400d0400d1003e068403c405604040e640300d0701e1030301e01540c003070310100000c10301407280a130740211034034190409290401d0058000ca00075002003004081e0a61903004849603580d0660b460551710580200010441c0106c150840d40000307050741c00011303c440c5400500c140c44007220304008040d660075400c4548100c8c400015080840f010014001c5600c2404c2c44401424038030503115001702d1079002407440d40c4031550f05100920740d1441480c1c0141450807001d58001002d412510b024856000a655004010146400c04d0f803560403400ca02d8907a501510700030400d055566440f8100703030720013a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 807491600 1250 807490350 807490357
    0xc06060f0f180608070b030907240801050f0307180b0402070804030c0f180930140405031c09080109030309061419092906122103130506010b 62
    0x100b02c9030480c1c1c00c8601050140308920841d035028006005151500c8441c15503a040208078480b1802042d1002401500200d01100300701105a4009400c001880000c0c1907400c042e0400c600480c1080c0c2105880d8400040313110960340380030041c9085100e581d0f11030b00946031710002240c2250000ca4090100996070000c0e1013602d1052064510450b110a0398001c081030a20482103028009002c00d207210580d6031207242254003c0c01101003040300c40c840e20780802107803166403c4200b000d41c4400c034400d604c6640c1c0d80c14081001c903002c0c5071500d07000009640d2440ca1075031060380806d60030700031250381c002c0340c4480080030113a0003070100049030708020307004181c0f01c0015162203040c80d4030f4002c2110480842445070004454030f042c1d00000c46420002491404400c650a49109030202c0c48120400070800c0b00c580785000d2000c280ca001000c1c420074002c04030300054513510803422081982d41c45481c40e00d000f1b8602c4c452a45903504d608120901d290341c104043c262780103030000842c440040344005c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 807492850 1250 807491600 807491609
    0x27080c01081806070e0423100801061a031f0e0f060f01020703060c050f070f060b03030703050d0b0f060d050105030c010f0e0607020d0b090f0105060607050a030c06060f0f 75
    0x50032140d503104102402c4000078140055000d4109000203200d090050710f000b440000041d000181200780e200d00c240e4038419144040c00804603041c20030038008003180902c6c5c06028400000d00160f440c100303a8015420110304c83c10601c0030080001482c6803034032000c0c0e810180c0c82095146100d03a8030780c0f40003108030040e40c0103201038044030300255a5082a81c0f0845001c001a40201006459510703403038020300c40d5140c0602004000c00106007859440c1014000e40c90003400900d6071b941c80762a10a00b203aa1040b104d50007a0001d12000700401d03001030030303503200f100f80705404950442a14000f40c1c01c40303c2900030a0b030000010419140c0b00006603c841d043e120203030100e40c0c1d218403003001507540900200407480007500c1c007100ea00490400341c000e00300301c1d8806800c0e249410075559581c0709110382140c006003140d0012801c8400705009000301e03a0084001e4a4041c030b0180d594603003030b031100703455040074042c4a400030000c010040158401c1d001071182d07801101d0071030b440d461058810001d40c1f06 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 807494100 1250 807492850 807492857
    0x605040f181509091104052707090603050714040c1d0a09022206050405061b0a0519120810030b130506070914041413082206030f05090d27080c01 64
    0x2041701038146846024020003040000460701d40704080700d820000001040c40209005415002070001c2460140e20080d51013040079250b038904240c1c881c800d1038080000700340b050703003003990260781a50040381a0103080d4501100ca450b401c8020702003030f00c0c0c903030690000c003072a440010102c004101c4c884001d0604048810401d0071299510400ca030140030b5170107140d0340300c142004402e8024103410340d0f080260024200713894614080f03403035090524540d0703a1881c0603c00c1144402040000c0700d669107500084a0810058504001d004000304207458000180020301100108020b414080e1540445507031002c12646c261806440040c503130b000501c280c000180e80494860708525080c01003500000003c25940d0311540c8036021840001c079004810f944c0740500308060101d05203080000a104141499500395840c03500f08020100c50b4190040c920843c030309001d01214500102e20b020090703c45290050008a8044500c5400398240417054007180102a00145400011031030012105090b00d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 807495350 1250 807494100 807494123
    0x211b03060609011a090d120906110307080a030b01120f062916021302030403021506010e0901030215040b030a0506090f040f150608010f0905070605040f18150909 71
    0x10103000682e1400c0c043c404441c4641d02c9007103100300065000c1e00075510010405103c0e1a02d80d2911881d5910707500041c40068005030b4244862500031010440a101c020003c40c50460282c81e25140b0b4010f03000900e0825407a4159030b04a45e204811000e00030b9078052003004005c16440c200c1c1d0080c0810710404002e551801031007c104401d40c7e004003517049055888525000124046103200141003004a900c200a05041403036054141301440c85a4880d03001000424001c0106c005100c8004190710b04200300e04c80041c045440e0030502074110b0794190b46400d1406854180171506e406540c004007100a008000c101e40e00450717802a6000700030a40c2c008481e5264261001c050312004c6401809541700b41500d480020900004119a00301740c0341d00095517510343c840ca41c25980c9a0300e004803040e0315000800700303104091104200401050400c01d20781403a25840300350244a612a100c2540b80420503085d40201581201d1040508100040007140d02d6405490040107940703c1600d00304805c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 807496600 1250 807495350 807495361
    0x120060606030a0e19021f20011b0f02011a030a11040b0d0606092f0f0d1d070f0f0501030e1207080315040902011d1311040305101a211b0306 62
    0x1000c01c0f15847c01750b0343d60306880e41070b01c0c0100c071400a40072605100d9596507840048944000d10392400191802e503403003e0711000808002407cbd28a01140072403000340c0f00422541aa900191010425600000b09000402400b0000d0014910307859401e40001c10b00788800e040080d00d038881800c0c0c4400d0311040102c68038038102c400380c220340050003031404113094841301130900c5408040e0640103003050005140510040c0305a083e504620b4081907104c0e22503902890584061041c0350140c055449030f503a071070340313050742c0098500d07081e20800741030594400390000030f9003050011403a60f00940070b440d95245c02c2443e01a10300c4c0e0080b9400d0700d14400c0b1701450205807419000d41420b168059490ba80c100440d18640e240c60344842c3d103906d0384846c0c0c8e2100114581443c1c021403185100444000e0b4440349181081410000340040d22a0041d180070482c030700b035406e032042840c1c542109464aa030944005001c00f00c1100c0c400e085802311384a0541c420500312400886130401c80015000d540c03058030795 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 807497850 1250 807496600 807496639
    0x302100f02280b040c030c0b072907140705010e0c01120606141830030c06010b07030203120a05180d020604290c07020120060606030a0e1902 62
    0x101020350000507007102c1c9880114580c422841d410034012543d08050340c0d603e80e51010369128607880640b0200d4049498400e10117541d480c80201104102c100e4280c404406a001429000a00ba030040c410003048940b03800c0e45e81020341c0c904551041c0200018491219020b83c1e5250400c44280001e01c0b80030500b850085078007030784c021145a5111600c10030740242c0c0c1c1d81c00580101c03524880b250340940482445660b08880c81c0641008030b0384100300d06e9101c034041c1d4500498140c2d00c4000364401c020300400c041c40060103d04555042041d0303500d485541c1360890840c072840d000300d16005606030074041030701d105a001c036018040800c41804440507010265448581080300540035070843c0300014041070a101c20902c803081610303200d034000c0741b4501d00c41048050070f0320520380c0c007038000c204842196000031103202c114142030400b03003803000403244099480344001d18a501507003001c8049100101190080104600d4504c10303103029095901d9020600900c080e001da208404511151518850 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 807499100 1250 807497850 807497893
    0x31e020903190b011413090f0b0a0b09060423040b2a0307030f151d0a0e070605180904080c1e2d2d340302100f02 50
    0x42c00301c03400d94242e10f0050840c55600d0305031170068100f9148100b00034146040d124a410311380c0b20308070310000308109040c1003000c0c0c1ca0060048144915100710440c25030f4a20101942c0038070f040b1404503e422412002040100d03810f84407a482c9003e480a110400c2000d45040e07120390300c407000a14880b0a007152049040400080c6802c8e049004c0002c909400d200350840303c11400d08210104601d14004801001001d01e6403102628804a000082c0301901078424039800c440c040000f84407602010300180e0314dd401c2e0788500d1091000000e0024068508429a100c285000030700105140ca02424007541c50b40c04a44885101e01450001800c281d1124142d088081c2514000748403440f041c0c442d880300710601c0c80c44241c0ca2521600b4041141c1000c101c0c50300c5904d031102c4001c0d12800c03101030380040e08041f6001040310703420030a00302030074070b6110400e0548481c0c02074010f010490121030b1040001219007000c0c2d00303d00072490b05400941c05c40340103200c612665003140e2080d0001d051794140e200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 807500350 1250 807499100 807499103
    0x9030909132f0f180907090b0f0a06080a060f260f0706050d0603080f130608010b0a030506060d0e0615091323012d090b0a020307031e02090319 63
    0x10b005001d504080c204807048198208000e0500701c900041e140b80c0c562031000480e10301650381d1020b9824040700a40e03019041502e00c003552a44000c100c0200040c040d0b440502a210420075420f00140b00f01c402c40d00444020103000300042195a12180000e80e03401c0307640a002d22203a900600840420000140000307803030031280c0944003040c10002c0032a195031100111040d4503442c2d890120206074240b000781001440f0304442c3c0d5840c0040d1844140f20000c6030b03c40010710603408c00402240041500f190049601c500d0005455603038080003841c0ea005507001c1b0190311f0304d08642c819090000280c7c2c40d02640c00300c4040181c6490b07940402641030f10803103201d14550b0301618035200142650700e403c2d42d03034045000000000c5102210359070859110b03000e01007446504030359020072600361403004414610601018408003042d910348a03600c080281650406950001c0040e0991340310303a01400d000101c0c82c0341406080c80d400046000307500210000c41c401e000c0c6010300104011400458030903207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 807501600 1250 807500350 807500423
    0x9041b09060602031e2106010c0204020c0a03172a071e0c09021e0a0201021e04030201091a0a12061e0906050402070f030c020102010902060d02210c0904050903090913 73
    0x3000003501b0304030030036006000e013818003120020401c01030341c4038005000411040c800a088050843c20020004900811000300c000b010105001404550003810080c52002c00b00316107650b100a1381c0001288030380c14015002d0303003814128030b00c600c20300c41500c200356004085038103156440303220b2201244201418107605070388081c1c030004404200801741030500158000141056508c0440440e0540032030701480c11a00c00090a108560304016514050622032480c098980011401c154240c441c0f40d2040c0103000c1000e40c02e12460040360080406030903501d07007d2140e1071851504100540140c00b030001010b080c900c000c101c9003098425144143c1c0c00002c080243c0200391010b0f101c80002010582c110f549460082c409a21210000c0002c0309101c000141d950004c07903200310a10340303880100f440c203a40d0300e414454002d140c1c00aa60050700e0803034000800c0e0302d61580d444c4c514403c040c011070304851803600704404140c402123a00e038060701884c8880c0d605000511074520458140700e81c0101c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 807502850 1250 807501600 807501637
    0x30203280e040c120908090312040617130209040f170c1b010203040b252001020111090103020c100608150f100e071b050f070e0609041b09060602031e 66
    0x44d0100b5081303200c0c040c0c01003810317900c1d003120600864182210a8a001482d1000050401506600ca10603140c1c00400343e00c0f4800c9030900201e4840805065280030b8810041400840c091060014150070750a40c0030811003118100c03515520240c0d00510003c107003070300910010700c80710401d2400002003802c0507405189800d0400d2a10340e4150409071049580300d030405180c45903030004c030301c40181d01800340030b40188034040074a2000f40c50b0f10810800d0704590401880484e00d04001e01907030300203442400c0150311008007844d0680b601004001c0c4000450800a00103000036004c650340440c1c6800b100d0801e0300b60349800008001030815507210508a11280003008000300d421070403500041c0900e0b102c111144900180080107855200c15107481d0001c0242c9100c1000c00c01002e0000c021034410807605281040000720030300001800984803903450f80c071045a80801c0f252120103450021070400405403248802503807600308107070303041514180d4042c3c158121400d00688409145000c6202072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 807504100 1250 807502850 807502877
    0x7090b12130302030d020a0210230c1c11130e0907140604350a030806040504030e0a0e0a0501050105070f060b0303041206020c07060e1309030203280e040c 68
    0x81d0303505010642c00c5000520071202030100600041c9191001c0b54010f01041101303640306012200c0d00303da010304400f5492841c03400300029500d0103500c10b40001000f502d031b6080301e071280d1885541c031000309440c0b40391040c20f007100c1701e2200140ca06000c160004800583d2990b0180e88448425200980f4540c0071740402c01c000c8007190304102c444940a802d290030b02e41d0319080d500440c148062480c483d89111518004600310681c81090900e0040009100034901d0362070280000b007014185e6401280c8450004003814020340568a11540140c183e50605075640140001e0380c1080d5031305648203003044000143c940c8284241c402c1c3c9a0490381c0504110580e9440034018124040b066405001c02e00001501454400e660481c07640503440145e5154150022075007084601c4e0801c00520411111080058413201403c0c0b904201c01500014009510b0409901e1401190119440d00280c0b411001520142400c42e4082040c50740307444d101600a0340030131040c0d444820705c100000360310700718021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 807505350 1250 807504100 807504121
    0x180914060f031e01090c14040c090506040302060304050a140d08090d080606030703110c070602150f242d0d03121104050d0501050105010f0e0d061a03100507090b12 72
    0x810703c0300c0c10000040c04031455480c5102c030340d000c0c0e020441119074500c50a14a0030280244040c4c0c442501c1c00c9054282000e00050080c040ca0201a000703c0c40440090704014007000410b00480c0c21503842100b1202290685980300403440d08400020461004600506d900091707402c1450807907120007015603903200610440d50001882030080640b1803c02607d003124800081c031499003c0c40c080d00180c1d04146c0060714010040c054140d581c082101044080c921007041c154104250104c640c1c1010400b0f4004420101141d03507195000ea003100d5601c410521000581f000070341c4051107585070444c000d0800c0001c0d8a502805404581c3c00801814034100795808100b80e810065007090078581c90701c001c261044144601103407542c1d5070314018400e640c1c2010902c140180503240c1350222540320800720703408801c0e10700010150f54440003a00000100507807038440001d805000c598440c40c040044601600d010313903202c1c011500c500384c0800c00301c4a92040b10440380d0011114069a00c0790943d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 807506600 1250 807505350 807505393
    0x8010b09010507060e070f0f050a2702040b0d0b01020109320a050f010b0d030e011b0204290d0515090a08040b281b03180914060f03 58
    0x11070401404000d0300000a1191045080c0740c00041c000740307078480c14020700b0714801c0d039a40c1000c001e85014400c20001c0307507104481300003594071500060b0704e901604130900c00381c01c1040c00c1d0707000c00700d00126010034003804440240050001e099814852a000c800041e03080700e501d0b00002d00b070861818200c804800d424080d2803180ba20710005c02d46030315141120707a41011020181201c9036003010303920f00d083c20024001c0c4e401c1940101c5902c01d84012075500a1b0010500e9038034207062086800d11801c1d0200b40400c0460560b402400c28852104c180700e081518222a0401c4c18074259960010a007508246074480e90300c42e8031200605107a0b141050f00c003e0800024115590f81c8140740580300000c1641014100414868050fa615403030183c4114144005500b10300504200108045a00d641d11041c0c01d9603020700803050800120090404580b81c480c0e802c00115400c160890018480100f607000240c2c4000800707032550b150301ca0504201c1c2118422604544c994400c0d41c1e4a05c1c0c1c801800c0a2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 807507850 1250 807506600 807506617
    0x90b150a0e0d1511180a0503151e040f020405010603111206030c1906021b01080c0306030c100c0521030f0c1201031a16050d0b010e0d0605010302120d08010b 69
    0xa00021034683d4041c03100381c4100040c03211103d40080b8443c0c0445264280300d0106000c211502c030507403810000400d40c2e5a154103084030b2161b85000c0800c150101503e141c40401340344402c4c450702850141444849289010300c02c03405207191100002c1e04511a00c51101110304c4050300625000c80030201000788040600310030341c1800354490540c4a585d0f800100c00d103000b40340c5010318840d8584507000c0e080c2884110001c03030009142c0d000709200d03a03004560562000030b038010640c0340c2d10b03482c01180c0361044650700c1e2a0440144d88015900035005108241d0300c074850f00485021540500908150701140e05501c0b109000920100700980410761500b07a0081c654072003141050300038059480e0625007a8819203170111480c9440e424130a01014041d800151491a56540c1d2003640b0010f001c3c0c0325544648011603664601a1841e80c403805d04000042c2c402000254190601d00700000200020300c0100d110300c0d100007000001540c0400d102500c00c05582700e4a80b1a8071b40340d203405665114026 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 807509100 1250 807507850 807507863
    0x3050d0e1c031202030f06030615060702010305130b04051c0201060815070c0b040f110306060a0504050714040f051c2609040e0a0b090307051f060e01090b150a0e0d 72
    0x1580f00c1080e550f80b0146120341300c0d440c48500f2504180c41410304064014002d144507900b03000a0b02140d8455508540038039a0a1800088661369403140952030050600014034141c8800280000c0c002c001400ba450310400101554500008003001d034200d414a2141c0f01443d080381030001c0c10706004061071640704005040c9404002c400e41d5400a000300200d800308c40541900e0882c106022605007211002c0d1016401080c01d070401800007417081010780701d1075208540394800034003620b105110490b000b12034814825200e13600e030208105c18010f01c2c020103018015040302c4007020b04d0318500801066403c001c0c642e049900c00c841d0044041403055440c188094200210000d5440350f00c54510050346480c041c020030750141c40c1599a400700a420428160710521640012810106094490b0f01e0400040301c3c21110404481014120350b510918040f8003c00001482e603c082c3c000001400003114442c2c1e10122040318803241d03029101042000a00700090403007103041c003e0300141c0b064080c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 807510350 1250 807509100 807509117
    0xc0607060e070f0807060903020f15190302090315060a03080a0203040315090c23010c050a06060602280b070c051c0309032a030f050c060c030103050d0e1c03 69
    0x111040ca031440300d9000507101400f9807000c1201030001d1004101904181c81d2002d10a0b1440e00050100e4a55550080c403c03880360303456902540180b0101c0d110800c0e44000e001c90781c41c080b140a4000c0d04408841c074068011141d245428100100155208080c0104500c1000c0d083d52240034064100208040030752008000100114180c0c20b440221000130344004510904507250203c0080401d0780464400b06c201075003c49070704261102c2041c520000c1c40c2c1080180c0a505185160079003080c40175040520707041e0041800e541c04941003030b1400c0c00d070218044400d103000c584084c4684a6001401001044c4040388060307209a0342c025116029a00700c0725041806402c0103600c6074440c0f00714020031759a0745035000700340d0400b0300156000420110311100303400d110321090720502407240c02010000442044d20925000c2c000703a580700c03c040011a111450941010b00840c1e1007800295084d2055140c1c80c04154424009500c006c00003405103411070a90285415103100319980c120240030340308 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 807511600 1250 807510350 807510371
    0x5061905010f1d07030e03120711060108210d020c030a020f0a020d02010f020a2307050102010b030d05090a030b040602040512010209100e01031e05180f070324050f090708010c020c060706 82
    0x108040c00a608c0c218807010520b0614003000740c110001644440072030342004c0010801c2c0840800d8010703521601500400001c44d20545c02c00c0144243d0b02141e200f41d20200756250070202c0000034120a040b00d800301d809001068140582c2c803400e049000390701079444080c40005500c201e214804c0040345004485410340640e83d881e00c08500150541006143c0c10710056220384100102d07401800b00780020402c080505c0080780c0c076101c094a5150900c0790005468110f03172109035180307009540102c12101c00b401c00f031605401943c46882224400d40c00c84502968900061089072481c400c01000c008040400d91416a54021a00c00d640c0c14942d032070f89403605005440c509040c000d4848a4005400d10b000a9040c1710b941040c5005e0074a81c1c070110608025243c00501d400a803a00201c0c86101c2800311000302900c003002401c0000110300b800284007640c10342d108654058010581a01d410681740c400072422101a42190300040e40f2010307000b40141010b100400c1c400e80941401318019450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 807512850 1250 807511600 807511603
    0xa050c0d083f04032622140309040c0503090c0907050c010903030b0907050f0a05161a042006090906040e0d0216141011070305061905010f1d07030e 65
    0xa00034040b803003400204100800da88060b5000c0c4038003a040034896a04c0760400945001c160082540354600c0740b1808420042c8105602076400582c410040d914081c0406245516034011407411401030342081c0c0d65244590182c03098900c00d150801c02030003452011410480b007450040c0c400010310030200140c494990b02070040c4d640c564003e442c00b2544c01040400d10200780c0000b851103040090501140c109040c200080320022000b07482c22580320003d44402d504101524903008214401c059400c0c1401a10396950078810390090206054240c07952024400500415880942c049800c01c070703c84461030801e002580110000d0000030381060111561480c0a00c041007010160340250103091444200804500203010914443c02464080001082c80064102904400c1c4642440c0c40e442c5036100300014001180c005040720404d0905010b51000c481c1c81900420803141030100110f080c0490b0300b150000c03580c0d1007010072052040e00f240c8041c0741401030f00d007808068950f5050403200e4030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 807514100 1250 807512850 807512947
    0x612040c0e0c090a080a1e11040207060506211f09050610030b0a020703201f0626030307030203090703050d021b0d0b0406020309010204090203090a050c0d08 69
    0xb10720a04950b240c0014040150340040c1380c1c032800c0302d030307004d80385010008141c540008101740c2c044440c24500308003441c0081c403102c41c43c100720350414030104090701445000c6c1c0003c1c5c05140117903018200d00c08461808490380700b40d07a0520080d54030090004411444040041c6222084034000045207445580c80a0900b03009030b40c002c1c4602d1761800c0074030900c00c20014039908050010000c51400c24556009840040c181100d201410405050704010361000d00c103140341c02040c0c412030020400050781c40c1c07004103c07500480f0403c0c82d070300f00c4201c178881890218183c0000c1c1f000040d4116a62880110065071004062001038051124004000380080280c0c000c0e00e8201d4001e0104150070350040c0c101c0a021500c1a0311500d000c054484c0400d902c4c0f594240c100342c1082c4090703602c1d910442d88501911455000c129136520000401c40e10440201d03800c4a00341c400d20580711a41028020044940403801c0054034040041180c04142c1a603d21400301226000d640d41d4034041c4803500d403011005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 807515350 1250 807514100 807514111
    0x403020409080315060c0604020603070309050102210601020102270609090108070e0f1314031603020304050307080f0d0c1109070302090a0b030c070312090506130c0902090612040c0e 80
    0x140030040c040d03a6407040320749100104c0156255800c00307000f030340001c0d5240b03005400640101400004100b080e44a6040300c3e20b800d400c0030096690b0100c8030007040441c000744c6242c140c01440500822070a601c18001c58140c8448201c00c844c20a10b00c0d40c5130080303c2921800f43d81d01c55800c000070031141c0c0340c1c0e1000d10f000b003142402400c02645070080d401d00f170040082c880302c643c0000030104a003c0702200440c3e0a101d80080184a501b6213102d9041d103140304100c3c7c1104000481c440070420180c0c000010000d44105500b07580249980354642039480c0e60b18000300705503030024411029803610403103903441030303601403130302c90070303081a914003080c820003066900c0400650001040b138081d0400e904500300400c2d100c2c003a24a5072400c40c01d140740754020340c00001c02300180c18000d1030954103030740c100d2841d254001c0e05864850410241401c400c002000f81269401072407070700002c035039106d8401d5810110700540103610f0b149413490040e4510000a1084a80038080303a00810801c004040c82da1194 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 807516600 1250 807515350 807515363
    0x207034b0b19051f33090918110405040b04020105030901060f0b22032301020408030d1509060b2a100209130b06040b0901141c06050f240403020409 65
    0xd0309080070040350840c0b20b07000807020381e01c80c200d00305009915120705d0040024080d0302d400058038103002207a0218240e400841918140f01c0d007945002d031400c1e52001018403902140104102c50b00500c41605d02c1120041c1030b08004000144c0554000d4000f1503010306840300026029444143c4185001d8140c0c0264104030b00204418100844074081d42d80124000c2401c988040c6ca1a9500300308840040c1e213120240e40711010b00302203614250180c80240820909803602c400319015850018130705104130b201407a04c144d070005440c900c144140f0003074480700301c0c81078a00320310041e03050355007982040381c00c0e45003501c25950f4656201c18440c00c84030700c044240250381c90040804103c50100e03039804012000e880e00d590003196680f00f504075402c5a61500b41c50780c031600128016540c2400880c0c1c54040c40c1c070300141609070300c000e0743c40350380407280c1d198001c02031a5210000d002c680c0751807100c4560004180100000100009407003001030100c80414a0b1a254483d070110381903480851003100e12 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 807517850 1250 807516600 807516631
    0x30c0c0f06140f09120c030c01020301091401053322090c02070807031205090306010b0c190f30020708060610021c0207034b0b1905 58
    0x110ba102640180c01c43d40354481c1c2c101a0500320710f400d44880d50440401d140203000164440c03060814402e0700c202c0012100215200d42e52030b551840030300b84400410000044040003c1001c0c603007100d040c41c808012204c0418040c40620024100081d40c42102180a01c05d00011403c2a5110002605500c40341c0d02219032524202c03580041d25406245403085d50448031061001800c0040c0100450303400921558440160340003d5556100340403c450305401200000309171403424800400c0110396400c00c43c0c4a06007a200041102141654024001c1c1c510380030042c08204801c41c0e2250300800000e04030420320714110091020f1221401c01c50160700580000c001000050040c283d00013815078850510881010300252101c0c0340c80270844100c143c55103204d503018030030445540a564443c11004030300d10b8010198140c5410309a00f0a00c006034408504022640c107180e10440388100906d520004000740d0b83c400080200a0410750413021201d030b9030200c00f81c9401802c3c0101c01c02140182c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 807519100 1250 807517850 807517871
    0xe040f02060415210c1b140106060801060908010504020d110f030106150306090908070f0615061e020a03080a0c03090510050603062a09012c01030b0f090403030c0c0f06 74
    0x600481107401306542c1c600c3c140032070f91107541261551801610000f00d02c0c401c0300407442c208898154100007090340d0343c0307406000318100d40c000030224142c0e1000e484ac01c4005664900c07031801d0314070445000b034021081c20200c800003003001140c0da0301241c006040c03207c0506140f01003401c480c516403045c6a03e00c89050328101d41501449054040e14180c02c0600c107245084d00d4520861060b500020140210310315406d01b4061164042490100743c210280e88540c3d40e80c0005001031501d046440600300300d240650556030002a0804000e0b034161030b0509a903854000c22002000391602c00c000b4541c403003220400268050000c0c44500314405000601404c15105040c9401d600070103401d12551030703035648420101507541c00d0140c9510810300a5417681c003040103c480f5001c2c41810702840310000c0010403038420900c00c5090141d0300fa60204100c03503051003044907031091a0705240e00702c0070380340129011a10981000d0b41d103e40c0d9041c50030b01c0c501941c3d03410342c403075510305404e03100c080d91400402c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 807520350 1250 807519100 807519137
    0x9020c031c0b18040b0105060715050106020601060f051204080a050c0709023015040b0303160510020708041502011508030c010c0305060315070912050303060909070e040f02060415 79
    0x80e10780140c3c00c995101881c0965428000c1c0300c0c1030251500c50329010600c2410412002c25203181e2403100300081c0455652110040d640c0e01003800356002092110024608180c030400039200d040103100da2029140d121074a900881707a001000420420508000800c0c10349006c00603400101041c0b0340040c0c0d08c5000c6100c103502400300c1000c07501480c45000116120045821415030040340301440f4600101308140050b0081201503105500343c0008152005010740350100d551005020354240c880e00c9501c0f2810748100e100b00e103c000c00350502800b01740b041c101d00e03290702c24592196000028103015041d0300c520b4101c566900103a1140e00000e106101c048083c003560f180c41d8940d04082c00503090034800252103c101c0025592011019000514481e12400c0540002c000d05442c08401c40b40b6030900d40d460703601c22901a400b411450b004182091000514641100c00e94131007e005032300c440d030762114507904581050b40d100380103000201e240f001000380009200800e8686070b044691031400b40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 807521600 1250 807520350 807520369
    0x708010c0e1e01050324090f070e0909151e0c0403030f05030606040e040302010b060d02040302010206060a06020a080a0c061503060f05010b0301060c170705060105150307050409020c031c0b 83
    0x244800c0c10901c80c2c80c4050340c112064940001c02508100a2190600d0321015403501d24621035502c00320f10420303c541d0444900c080c40c0668129601c14803040402003d01004c0d403404c1d244401c95501c0800701d10541580b000d0300e150804a000b81011072074102080c012800c0d0f00c10b4425003000100081e0800030190446c40701001c0014a0404e181149041c2002030143d004034480c0c0704020902e0b00018003058801c0d4080300041000034241074a07261035004100083d00240030490241c4645008030f00703249440741d01002202c106500400403403e051782c5d80300e0b294215214101c00e004114403183c001402502230011120154850f1301300d414954200799040c2c0c0c107107594a02815103840700520089550b0405c59040d0b50140c02c00c0c5c074078200c042c40d090b04180c1d080a0b010f2080381001c110f800030001b010400c14100e03001121941c0801c0b031a240f821140d03201c15a89403000c15400c1004102c00c0159401a0008075007283c141c904204440021152040700c005290000503030b138191403200c0380341000f1741c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 807522850 1250 807521600 807521629
    0x2a0d0914030a0f14011406030c0d0206030a090c030c06120501090c021209031f15061e1b150c030c03140a050a020403050a0506150414060f030708010c0e 67
    0x140e203815a4200401d880700c02d007401c0940104442c803460014407654580858400751100c000308401e05a51510030313800c1d03a0035203000384240280f4007004500e28100b003241c0700d4150002c00c15803450711340c5212580241b86110045610020018000011804142d42400200600e8039800e9088100328a480e080b128140c00060441d454800300d114419400039148056941c3e030401d0f1680e649401e070010b413504200c5180090304100e00c0b0b0300b905c0492541c1e00203401e8074160201c40341060ba00c84105803410320b03e01040d000343d40941207002c145030344614040780c98114050151782000b0410785424520106500c5c084c14910b46441032001100e90520607074403951000d02c0c0401882c182048940c5217000d015280c80903207030326000810f058a04075130445000b194884119000c020040c904a9160141103e80d6202e81d000d0007042180c5003890b01a00480c00300240121a00780d8405080103852800c85102c1e0341c045c1f04680d4082106c0c0000d00c07480c1111009500d030000110350803410031403402c0013aa40d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 807524100 1250 807522850 807522869
    0x5010809030304030809070f08030d0b01170c1303080c0c01020c100c030e040f02040324110d020a0c02280b070c05060d0207020d030e04180302060c2a0d09 68
    0x300480c1200c0441500d070019454902551961a0311100620341049604611000c08800b4030020398100000003d110909a0003401d02501048400540da8a00f91458111960144d00d001401d00290750b0000c2c8501101d440c0c074207071445c3e1030780c580710183d0704000c502c01130f241c0c01a1203460b070540c1c0405c24400b42c40412509003d80040420008000040001e4000d040c805010b42440791561690820349003008601004c40d21180c2d242002c0341402c6043c00760000c0606c0b02d41a0490083c2c0c2c40c0218511810b801a40d1850300d00c15180150095001840c10010008104e003054016501e65510f2980307007030300d5035186541c02c05d4800081d0307003034035190310900052904010310000a482c2c1584081140d108a841c1500d8240204680c1d000c1c0c8070b1003000951005802180e00109030304428466480802603604205001d600407420308001815000603000d0b074084800105420b455400500d07d40e07000440c0313416a83c4824500120b103241003010000725070404440120480d51203500e09000b0000e941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 807525350 1250 807524100 807524117
    0x20403021e0f06161203090c0902030c190e09101403010b09060906031015171902130609060902030f0726061f23090604051c08070609030305010501 65
    0xc0d8800c1401d41915003e114003080385810000d1500c103040010382c002c840341c61441e207852002002022113510880307200480c24004201c1400f00c0c0300b0ba034401cac0d40702e0312000e00d0502d040b40e064100900a01c0840100f01e2281c0c01610769440d600e02c1e4a001e59111f040107192282000d0080014005034200c0f18002d82c0b500400640c41d079a1812801d800c0001600e0980c0c00b03172370f03840107c1d052a01e101e1090414a007047e24075591907540d0303c00c804c11100714050300804010303888030391070703c0c3e580410305140390351902d904440161812010280002591040004140340c2d107030302e02000c1c0c1e15561300c900b402075804400c004c40f0072050504142d00c14900e1904103c0c9001d40c5000c022024600504c0311103a200f4035000a00640740c20400c4100300c900201c07184580e0b649510700403c1059480050010410340c0900003130050600c1040d9640d0b0b500007044103080c181044203220040307004a4003100300302c000b01c2c0220003052442c002032803a94016030700032071540b016060290540310306070700c106d04010f03144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 807526600 1250 807525350 807525409
    0x60f030f261c4a0604050f06070c0201021c03020c1006090c050705030d090317180f07140108040f1b0608010506040302090a09061b1709010507050714100f02040302 72
    0x3050040440920052a42d10710f0072405404601085011201d010501c80c3c0c3c005c3c0030501c100010007800520b4128101c0d00f0315921850111100081c2c41c0000340540d210000707014084404102071f843c0683c90b4034005042824207103c4e50300d8520304640d907548072540d98030305000c003424030b00890065100c1420464030302000c503511300d9540e2003002d14101016640d01c01401c101841400e6420140818004464003800c007002c81140c074800c503140d2601940b00312a0b5415030420081740b4030040f1000c180201031254007003401920500f100500c125010703d5650800c40000d0000600c2203003c0580040110103070381403009c05402c0d110306801c094802d030000e1208100507541c40c01800d0b4809031140c0b01040201075072a051024007490b0461004104140c00070820050b8030484550320075113038038101201922400704007070807654181c0d102000141d0070007800001c10102400102c220300d202e0111048040a903030014102c0ea43c019061010503000203041096203003551102608441030142d000c1c41c01000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 807527850 1250 807526600 807526661
    0x110c060901050a0c080706020c0c04050f0105040e160e091002070c0b0d0912050919120b191415030f0714060c0304031401060f030f261c 60
    0x12540054100500021040b03c40c920941c0c000d03c0e00c6500c100c05a88405142c94004060f4219141c96044ca1245103040c08062415018090261604644074892a4209000c0c440644603851310000c1034841c4550101034900d22030040e03002040d90300701803030544c2030078141c880c10942d13001d41156007540144810004140c036068280c00702e0b2006001c5641d10400826144080c1c24280c0016020b06800c084006103507801c1002030010490441d1182e6541210000880803000c450103800b061a240b200424002026061ba10350401c1c3c900c0030042e40e22442d50100c100b40c41280c0322500c41c0e01c1015040c40004071003d501d540c09450118090314200c1100700015982e1041482414040040343c049191b140e11258201d590741e4007058162540d4a46909040044c01c44c0c00201041c03c0d0f01c0c0c4100041d502c03209400040c15603900031001d010805661f11115189807000b0004d0f003411040c461040c15a00d00074004024003183c00b1a500382ca200c940071454111030b1450b040c2071742caa0145c8e0000402d50310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 807529100 1250 807527850 807527857
    0x60f060f09130c1b0804060807090b122d0c0306041d0d020c0405011514090d050c090105030a08070b07170103111311090618040603080c010501060509010e090a110a030c110c06 77
    0x21480c10408a940d0101c0850701c56440e035000a00c540f500080380803c052108403180e100b0b10030780d501841000dca17260140d80100b01110030384c5841400c0d5011402c018140401135400241c0100040390070510440318070941c00c6000d10102c0c4a03400030006c2c0d001075805210710720800740c0458080000d585054080101e15542c0070750700e4200940c6041c091600020201030325a1868082d1802c25035010a180181d690720740ea0300803d100e40c1c1780070b000081500e400609012000e0313009130300307509001081da16000c0d0000d02500540600921403049801c2d050b0200c0300ca4001c5015044010386607844030180b280000e02001580c140e030717007464038180318100144100d9a00000580d0129035890000880005c8025000340c441d6010703051103400000d00c1501000b9051041c2035000800c0242d0761440305440c40d1103188200d0f800f1501015a81009140c01511035a00800114021540c2118003024040c288d2203024404013080e039600f01d1405103548101c1840342490424028401c01400c000011043e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 807530350 1250 807529100 807529109
    0x804030804120c080c1005130c05010807030b0907080f090d080c090105071407061d09010b070633170a1211100204090b010503060f060f09130c1b0804 66
    0x450000c18a001d603c603051291490b500400c403d6118101d058440c1d4a6040410651a026080001040b09501509904011540d1003010004850316083c01520707440030040c40f4905066449036030103015291402c00601c100f003243e541d85120316069140004112020f00040d0071030740025203031703080c013a00321520f1078000000d01903468482c00320900413030301d43c0f16030344008007900b00000c221a00900001217103016540345481e24141501d020160030701e040e0041400943c08003045004101080345907004020071401540080790920290007540c17682c55080050050400041c0411079800210134850b80113011605400341c10b4003042d810382581c852808401900310039032018441d051030f01410781071110301a10019a200f201580440f0070003034200d8803840340000c4c00d01d8030240d80c0b58402e0088a11885000b4a40100e4200f0801031180e00c3d0480441c0b0031182c2020080100e10340c0d0b0b6407030001200485880d01291b100710110000b032083d0320300a1418240d05041d03105130300217650720041d42d0130384 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 807531600 1250 807530350 807530363
    0x1009054b1005060c0a0c08071403030a0503060609010e18071b0506180705031203010303020607210b030c15040504061502100c021908070c080d0c0201080604021e0c0106060804030804 80
    0xa03400d40000c4c5013003860051006090440c0300c68001050a004519601180c0d4580d03144503c0d6182c1c0c005140e00d92241d282141c00080c0c040001490502e01301d006014081010300d03045400c0c41544002c42c80e1200003510440c01c0c2d07001c26081119555200b001d036001c070032280222600d65011681c0d01691050054092005540c0b00c01466800780c1382009044c0041900908981f400403064500040c0d40c0d00a00081d1f00601418000a01481c00742c4030796800c9a00700c1082502c801c40140d6181c2c002c001c2034003410303414061991100c0032030792486845045008900c044540d00e0b4984000c0102325401d5621039800501c0c0070704e030481c0182e00807400c2045144a060045030041140000b2814590703640c401081c0e414840009d442407241007000303030041a2080e140040303c65200c85800f40e8030080036070208005200e00e8208001544180c2402d50000c0020303001500b0105040d85252110b0601e002c4920144404200f44203110024000c000c010f06560421072501d003804c1d10000c0443c500100041c080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 807532850 1250 807531600 807531607
    0x30c010e010c210c0b0c1207110a0b070201021b0c0609150f03280506030d0c1103030a02010c020601061823030d080a141009054b100506 60
    0x600401d10481c80100400d00c0301d030304036001c0d4540c020f4a56204008151181c03145c550000351401c91074001c03201240398099040002c1d0755003181c01c035801c1c6052840400c883c02084018000508050f42d01d40c080c400e0b54002607210f0301c1004024401224000c0c458840b40e001411400080d15040110b0350317801401d80d204141c005104628181d10303c80d00385e0000203640700008104103884a140d01c211b00300e002c00c42c5810074211a00080f01500d41c00e6030b80c50382c03581003409030070755560144d0602e0940300d200d10300207504910000000380c00c6421065072480542d44403203524400d540d060003a01c6c05003c44d82001c0031a141c100152101030886030092085040581d0070f00d03111000040030400304400001e04032488041c1c00d02c80113000541c196006003005e030809000d2072803542101d500b58840c40e1400010725040d4a003a019030048c01c4040c05a000303292100106104e6807440010445c49107108204110201850016520305c904122001442c129002014031100d05542410700b07080f220120b0341c003502d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 807534100 1250 807532850 807532853
    0x90b090d0f0216060f090f090b0f041401060e03070519060f0f0813140d0c060b0105040e0604090204090b010b071101030b01020c01110316051c0c050a0b0405070902030c120105030c010e010c 83
    0x146e5454507003209800b0b00110f840040c4981c0660013881c45a081074030342e140d850841c40c00384070507204410041c800070404c0d500144055072280a171405840e030010700301c0f0396031350343d480109501396140c1141c0700d90100104024001c0300d400c081e54186085240c60702d010050034007140140381d50006032002c80751901041481013446541c400300b0019403850400c0e41c4c500302c2c0d2040c02902480300d600081355024100a0400099030060303054034110f541c02e6a40501c0ca40d548401c1100a00066800301e0b41709541382e10f01c40105119401c00c0d030207822640030f02650f0b4103080c10b045003100e006141c05c1d0304160401c1d00d0000280d0380460714007007250081c2855070410a4104500d0300714000c50b070b441e807008c852504081090150000c0c446e444111080c2a4003075072400044120384a5850b45009440d0394000c1d0001d4002840000d82d655016000f0ad0aa8040ca0b4892040c803059a0003034808802e107103030114003070030304440d00920980100303030840051422a0241001038071075180b4400860501820130440c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 807535350 1250 807534100 807534107
    0x3093201081b1309060605030603070806071704020d170307031a0a170f030a030204050103060807030b0c210f06040509150c28020f070b0c0a08030a090b090d0f0216060f 74
    0xf800351910b00014080113440b07280c020159041102d841d03200e84100030700040ca0344c0d008100140203140720b6403031284040c0803028800740000d01030300072078000001500e4013022450800810000b031001c02d40c0d50b40d4904140034010700340e4028a0100505114454540c40b40386d031760582c0303c01210480114103e5400c9070310b0a240c00c00300002c0f40d000d034901000403020105541742c0d0040050301c500341c034100710454079421144e5903000c05000c010891241d403404110040c0c2c1e004058980842c07a1003075101d42c85642c20710b240341d0120940d44060003071000000c0c072401c1e1405014695000c3c940e123000f000380707070704107141c0c006d06500c06080d0032070100002411500030041a0203d4407505c0380b44402d51903100c0700c1c0f18025500c441c4120811120b006c0e8940c04103448100d9400c0f140c07641d1060000741031080b680d4407103043c1da42c4041d02400c1c65660350010170001070321400b21542308090010180c040e030302502001038a007401d061141700443d000390190b44003000c0c00c0644d000641e2568900580301c100c101c001607 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 807536600 1250 807535350 807535387
    0x21204020d02060d06030b061305010503100e2521050a0b0603070b22081204060302030a022208100b010203190c2001030b01170604050403093201081b 66
    0x40100c1d9081c045e0103c24001d0588200380134000c140c8051580c11201c0d490541145c03000e009240c0c0c140c100d01c1c65060508241e4004424000542d0103480034442003040c404004c4845241d200000350368000304008040c1c0700d00c0d14120b152503046400d003613900650703545605c030341200c0c00050261a803880810220b071010401d40000e450403400c0c80b9541d0032549510003800604286400350b805891402041e48039021070003805e03190750407207054209400e095040d000f0390001800814030b2642071061060342d08580700540c100044210b42c01481a00309001e282c00e00721881d02c0ca078081418400c00c508140d9000044900c0d03076800302240201c000c2c6401d01210020b041c010094814000b013107607000c10420307a420001e4054401d03241044150710010041d10103a0041503032402c00c03640d84001610301c0c205a0812540715100e450141080c54072000c022000754040015141714845810b61014000e034021882015070200b400c0920141c0f030004055400c2c030816080b1482102c0c0e002c00e44840310103001004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 807537850 1250 807536600 807536617
    0x903131203030606170402361f030c090f0b0a03110f0a0612051905090303160216061b05030f0c061e0105060711090a0b130e062404140415021204020d0206 68
    0x96008d51500d681441d00542000d40301d500c40d8403401c00f40c0c00320844020799003400300c80d031145900003040e140a005100410000b0840b80781d01d40c0b42c2e1040180d9903500d0542002451050f001ca41da003080002c1032100e01d005140400b401640c80c24000d1029503040050076801116400e0040341a81d03460147d03403081041001c5422280381080d051090111020020f0341c4220030024a4011000c031240007284c0c1c40344c20301c0702d24040e0321020074140701241c070170007456a841511191061280c98940d50b620b1031a0301c4002803080c6410007041d107600ca41d4042c40f689800686103001054664840304959600800c11711800d48902e40000e030003404c001641d81002e0a00c030340102b80b60258039261503403a0240c4655880c0714816448a62424420280d510900c010b21201c00c0c010714065403a41801c4039107030546c001d103120010310406140e06903540c0d0b00512100d11190076020445081a18060010541d000344258800c4d005024003045030300d092090380d61107601115801c1200c0120700204500d485a00613 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 807539100 1250 807537850 807537919
    0x70219030c050d08010816180209010e0d080307110f070530010b01110105070f031a0402041508070f020a12050d0504060c02060c18090903131203030606170402 70
    0x102d183c03c95802c181118101c44203841607800100d4101c10107000b025071400b440003081040c4c1c11008094031300e036000e003a45220604048091828680008502800c4210100e0301c5400020801c4031007940302601d02c0d500040d100080071b403008074444003a04c5410502a044c0605c52008200c41c4454804200201071610042a44d000c4840712680074060407103104443d0100d0a0500300591805052207154481c445a55648070f000c01403460403805440000e07450724108a0f1600411400e949600c000c10090030b0122905412681c0c0d008094100413000701200e090050a00a0140e80d64000c00c000c03607515070000412440071045d001c00c0d107140c02022140386000e440d1208000401c601d0754441000e00c8441e8007152003070356449040710200c0c8201c52083e41240d10002d44440b07142000c0c0b00c11900942410180c13400d040b040329812004406540c8031040d40819120f04400f807507018800c10303005e01401e01d005401d03043c41b000c6440c0d078014061310080c020000a501501c410140c1440402c0c01c108211 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 807540350 1250 807539100 807539113
    0x131e0c0203040b07120f0c0b0a09030201060b160b09030a05030a0e01091203020a180f0e041104020a1707090b03010e040203100612020f03160b180a061106070305070219030c05 77
    0x605c44440042407003c440410250f43c2035032446801200000380181e4040040e414690b1055006006000d444a0071000d641d21002c0108141e01158060311031321640250b03019004e1410304042018031009044446540c008100e08200d1550010481c0e41c0000303801d40c085800481d8000241c010600c402014100c0504016008101c03a815002005602d0303280d502c0c42119142d840e0310382e0100c1c0072840750303050b01c1000b9a010000000c00c040d0030395201e13000d9042c140100003a400441c09a80c40710001900280c2d184056400700b110250703801e600061540390411a060400301d004656203c103000382d04460045100040031075404120212903801c0c0050301340801550307281094506803000108902c914180300090045040c00100d14a0080315800300700e55071498500c4001d003941c020441001c02d00d40100805803262111806a0b0090403a40d075100305004440308440d04203c0051302c40801c00d8145414000141d50020310700641c080c440150060394805803a0a64905001c0c0300300034500c2c024003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 807541600 1250 807540350 807540353
    0x80f1e0a09150e0715140f0a12090302030a0309110d03050c070501030216060506010c0501110d0f140609091e0a0314070803040f020f1e131e0c0203040b07 68
    0x1e800410180b0b100307094102150503040058403d45001e151154043d0b440400200840512000402010343c0346080c400e8003400c001c4100041b640c0204031962200704001a010900b070ba2081105048500b21502007003a000c01d66002901d034411507514004150311101c2d80b205210001c400d200404200510b0040500d119180c00b5102d80c108120088181c015143c0002e1103500a00840301126400d541080500d185595000001c1c1740c007812143c1001102d2248000107002445490002100b61110701d84a2851003e4441554500c18503039000504101d022458582c81e22a92504010121564245550b4642d41700b8a0028806c4581070103202034054004450390118400861500999a0001003085d480c0c424115100c0d803e0b0050036444d00300005808103548000c0003023201d00c0104401d611541040004400b803980a00440151070103031146403451401c0003a41265408a0b02c0612800d501d118054000c544035805558600761540080416075200740300312400f400aa814840e11040079 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 807542850 1250 807541600 807541621
    0x121c052d070228200a03060207112b1e0c050a06020619051b030108010209040608070605040509040c080f0307050f120a030902013f020406080f1e 64
    0x6546030000750040201100741400a02c20501e4420711601d0703040c80503c1180c0d1107040c03040e50700c0700d490b280c80b400c10000d0b40301e50340341c0d140d92000314010103026841e038195040c0754800c0c41e00c0c80d004600c1450a0300703035000134044001030205080d4904901c0c2c0d02091050500070486050002880b09400c10229101c00304041800224283e07a03080c1e9501501c02e456840903a510181910150403400207089904176205450b00040d40c442a51030040c0104d04a6841c010515002030300802c11a940100d0009243e00b02485040010001d0100900c4070b00d14142c0040c210f48258081c1074001c0340560001420312640e442c1d180c00414a10007190310742c000c5c880c4029240e400c0440708543c18083c008880e54807100004e0002220030886c0c0388030b8981502000c00341d009080040049050001601942505080b4042d40144000049504140a4250a41c4040d07860031140071000c155105010a000c6241c0c40001164841c00540000313059485003125030258071040c4152841e08410b40b4202700d00445d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 807544100 1250 807542850 807542941
    0x3218130c080a1e030503010510050903070f080c311d0d1202042417010f0f090e15251d0f09040209180a14121c05 50
    0xd0b0034401c0f04a480400306622012081e0020340011420300040c070592800380034804045c803082c1040f603d40b0540d1030100341426a140d01c10010300015150810940000380612900c42c0012120b109503480e031203001c0815902d80107000c44406d51607910326a40c64890742e000102e580c84914610842d00400e0701815070711003c001042001504046101c5012500c82c002d0b1000d60310b501c28246084101640da00960407002d84440c07007004880050000032006110072140a04140755038249000e00744142001d00c0c404607071003080c400d894091100c07030707000c00800e8030358094445503a0341d803030768641040c04c100072905030100f0b982c3c0c0000b280034104035580001c003a01406160300030781040100c48000b0004403180070800c00b50040c10322000680149000341246a218503e00ca403000c4203011818214900388400d00700310b44404103100481da12003010072502412400258140346086001a4000c81e013010013102c08000d41d4a074000b18503161040c1c0e0005405059606000c45910004a825140ca85 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 807545350 1250 807544100 807544103
    0x31204050411070809090a0b090f15030703050319031407020607170105010e012a030908162d0302090a020d0f020a020d05160503043218130c080a 64
    0x51800c46003510340c0150105950f246a082541282450500c00501881001c010802c5143c56540e8400181c195203c1c0b00881c007942c40390000706d40610382070325500c052181050800d8460390103450200001140002100d0822003162500006044080010307405010040c4043c1b141d0701e0214100652036a00140480c0b00c0d150b0390780c80003000701d661540354100403020302903240016004490280154003d10070800b41001c1141e100004106640e2821030030350500d50100c00107040110204460401044a410a000c101c084481c01610300f40d0000d40240c00007071580101b880425030350300c43c156104001001150060034000d01443c2002c89440254082e000348400d01d0b15098100162080f47d01c280c0c1d5843d500c940051500603600c010035a00d40c1c12150011000c0806052940f000800900c050401003035141076000c40e008802c0300320340100030b4945c0d1460700b10f0941c502000880d9a42105440d401756448001c0d01e043e15096480315030304d01c0c0351501a050b01c5100100082040c00012680c0040303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 807546600 1250 807545350 807545359
    0x427020a0504091b05041401032319061407080708040f0b161d150705100c05070302070602060f0103030507050c030703110307080303041112190510060501050c280203120405 76
    0x9486400b00412603040c0d441d90581c890441f001071000880c10261008601045c040ca01c1090b944c6112840c507202d10300c0a500c65001c6001198001c01696000c0d52908841c0c00c3d18a81c201d1418a100501c1200c0080c0303120100401e04000c81c040c04031201100c50216000f038000c0c8240d161940070045942c24115903d00081c01e80e0583c100c80b500c181612205443c0700a00c8007e42030b000c2440d80c1525044200d00796454010880c450035040d80303a2150044e1743e40a41c8a0070703121865800d01030304142c4194800c10540d00207104102c070102c0c0c55a030350f506407607140c24000c0c0c803480c2906003149402c00d1129480d0b014884c0e1719010080c003203a17500403c508442201168217494540d007080d81c0b40c2c001500e00403d0402c07100c5d01760006141c50a5001a50020442110b082d9694040f0040b136400b018031081c2c9440d00071044040c1d01c09170a0046101402d42801d10328030308141307003800b04c1d56211807004150040c20300b58000a45013594095044105800078120f48400c071103e2008602d5922603c110b0340314 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 807547850 1250 807546600 807546653
    0x170606033d0603020a0e040b011205040507050f06040b09010507060603050d02061b0405030316020d0f24020c06060d02040615080a1b05180607020d0b070305060427020a050409 77
    0x10140f10740201c5515600740d5840342d0012649006102c09004207030703007448c180404880e820303104003010b1003880d1189025100801c1118504000d00c20403680700710714280135910070441441503608540484030103250a2908607a544c6880c10401d00410481d04010170354010341c0a060100769000801c00d0007941d40030115402120071010b0224188079a2040e1601604140204180e100000e000041001c0c00508070b0040d4080f159030300d54034071408a0742110800310402a581e24060210018001c0d1080c03c6421850b080082509541e1040000d004511511121500c0c00c00c5454640115008203000c80036807051070182580079044410499440c84814600405024a5680c151040724000c07900e440d11031405200700211b203012039a8020a0303400000401641c00141c481c60076800c1160f008042104032810424001001d8541c00b42c1001e101c3c0c1d050030721403840003603141d118105440e91030f200d8000e09451071020404052541d0310081e40645030085010500c0180c8043e0395103c2840c0c20540b82 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 807549100 1250 807547850 807547859
    0x7030b06120417130e180d020307110306010e06040209040b04020a020a050105130f020907090807060504031b051e030705120601150c0b07111c030615170606033d 71
    0x1104e00030341d41c010b41100b18801041103480d41100da40750300034580d1501c03510540118101c0f5444c00b040742c00c04070016840015541309002c100d0070b045036444011000b03021213514144229103c641c0141041c3e101c0c543c00076043c101c90b551540900d000d5040900155202d0481010182d1038008500c401d0300d107942802d001400c170440610300e0317032200d41c0d0080b07402d02da40034280c0a010407160b00411040c1803280010011851400030885c600c01891036560345980c0350700310b103440217412412103010210340c00180d81c1030080e03503980d02c0e0360010003d0a8061850382c1954400007442c20142d40c0c8404d0f00800d011103824035088006c116141680e01e03e0408005c2604030030300c102d400c201d84950252035900d210010862107403241c41d0050103034800074221003400c94900902013501411000d04000b003960b850f410080350600b04000c0f441400b013820006105003050b081d281c2c6681006001500c1a00c0000c0021504d4500301055000e5000241c019424800c24031144901c01e9408102842c03401c410610018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 807550350 1250 807549100 807549143
    0x7031e020726070b0405030a030c030c081506091c060b060316030b010c051006030b01050d030c080c1e030702030c100e0120030c030319060b0301030b07030b061204 72
    0x100c660703070300580103052404546504088100c1c1c142c00d04000c0d003010840d0b0380100780b150708000e0040303004a029540da00c0000c00040c0480c0d08007101c0905050910703a03011046604038103c25440382c100c201869160f1201b000240c401d00c2542038103940220a04800b450044034050720b824460721030781042000c040f1010800580740022101504c3e8070108001030310b01c031403103034009580119040c1814036030b00a0381da5600b0300300b15a90000f02500c0d50380701010030a000c2241c40c210b006040c180d4034810f040b02c20f0b880052404107c1d10020b01440e1000455007000305040040070b46220f1041d44d4036901c45480e403400307600c80c3e0246006034443c0c42080c0440d801da181030051076071009016201d4480300c07503240c0010b45100e0001c02000ca850300042e004445407000070700092400d104000042c5a07645064410411315100025003200000c0c50034100740120b010043c1100c9c150398011140c03801a5803200e10850240103003c4100d9005003010030600341402a07070329540d0295200f80d000e40402070f04070b040d10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 807551600 1250 807550350 807550357
    0x90c1806050c0a150f05180606011409060f130303021c08190c092315030601050714070f181811010c05011d0703030f0c030207060f0c060507031e02 65
    0x1000b0a0b007004030144002240003031010440d6811820108034140b00840003011a0001c076900302c407190308a10380a0758040700b440b02552040007401c040c2032842913903d0415550040365a00c50184400140080031fa01d078582c03c2d40c0800944000400303046459180c025110318560310510700300340c81803c81707054140c0540700252248412804a0b0201424104a0340c0504070350007a420500100241c0460482c4010032a0780e031a40040b0007100074520b9940030701c2682100400d0170050000e05000748600c0f681e0210898034120b4000c0040070f1900f5045001c1401c04500c2d502a507801355140c1c2000503070780e4070f41406240b200800070080101d40c190b058207204100e079829004000e00320654458007298042ca0391000d00702d00400002075040502120706400c0e20740d00100e0b1140c2c0c3c2c040082041050341c0300c0c1c035440c048a80c074580040e134104a0340d4040e540704d505000c2e441c05d01482907070841481d84035000b492035003a044001440a0301f48220050020100c6984102d0361002d0b214011955007424000c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 807552850 1250 807551600 807551617
    0x810051f180e090f0303090604020105131809140109170c011e0b150c060106080c191d0a030201020604061a0303040b0301090c0e01020c09040606090c180605 69
    0x40420a91599908040d030310803002400c0510540e10105a100000100c0352006080b00c103480d0225400d28400d8103142a6020002c88403d6004100300641d0280208009402c42d0382030030105d8991804040c44000c6074025003060b10500780818004a001e841500302c0a00e8600a0001310900c1c080d503a82d5500361454148040e250702e0ba0b20700b00e44040114007000381050180c004c000201c4032804021200707410303000c0920303ca40710385a8001e1501440e280241142e0420700905180c030b000880780301e86803600014845c400a2112050000322101704c0c407001c4417081d004001d48201a007400303800281a40c007243d04140d800c040c1401c0b081200d030a0880b410f9003039913016002405560380300c2d510003000d0003010402e904898010f6400c00b485880400280016109a841c4181c0341d40c1090003810880d0201c040000800c1040070910009903000b14000d200803406a6119203e80d450381007060140c1101d5014003a842d20b08060151030b00d600ca0307a80e1030b0550100f0b40f032003421941d5040444135070060a54 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 807553956 1106 807552850 807552859
    0x111f0207060e0304030b0c0705010204092c120d020310080a0c0303080f0408030103060b010c0813211e0c05150301090b0d171803061006081005 63
    0x10300030200b084000071800c09103113403240502d00340c010300030105000700040c0c3c403c1805401c0d0102d07030181c0030740c0b44203014046c0c2c0340450002c0c1c03400105084400b0308203100c86805045011401e003200e804c9080030182410b0001c041c1000a40c400351200c811003004400001d10014240710311400280920003c0c2142491420040c001110052010003080c0ea050b003000001100c48007540d043d03e8001600250000392100140da4104182d80c024060b0640421118040c6884400c40401e0361f40041051048084d510301e4070100c1018080010000840d01c00e01d0059240c0381d414901c4818040c7ca41e500d000c1c0c0d40d401c00b081c5105d211480c140d004490000040c07018440a015084a90b101540c4840798081135854100903080d405604100e0750000045440701e11140c031300260140600242a142c40f820400031032020a50540706000101da0b900740022034000b0900c0c0000102c48000e003 = true := by decide +kernel

theorem cover : BRFrame.Cov 807374100 807553956 := by
  have h0 := BRFrame.cov_init 807374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 807374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 807374100 ≤ n) (h2 : n < 807553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
