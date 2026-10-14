-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0440
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:49:38.497403+00:00
-- url     : https://prove2.me/submissions/ed2852b5-327a-4bad-9ae5-431492204959

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 78956836 ≤ n < 79136692 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 78958086 1250 78956836 78956863
    0x6030f0605071e122c01020a022a040b030a0512030a0b0f0109090c02010603050a050607020712080f03070c0f0302150903040f090906021606060f05220903051603020609 74
    0x650440000501d9504c0e490403e40c11a56580c0a42d008101c0da5a0281401c02c0b0b19801c40d400c2d2480703011494000d61100c12160010b004105182e806692040021082c1c0303c0c03000c1c0800c030244060000c110091082110701a8584650105103001078001e110b18a081444a22081d84900c0c02003d12015150300c3c0492030300c61104054070503020b0f84c1000e014402c1d2690410009010545c1d9042a401481c2da03030000f81c040d1203204000010040e000401038410500c681c20740e40c0c1c0c0390b07a5203000c10390381208400c01001031300700b80030101042205101441e4040c0c41407401440144c80d130b031600c4503a18082c03d0240d00503041900014030340c031410f8500e150070040c680c0c029450a464101c400324410928052241078070303201c0380c180c6d0070711130780c1e405966012170703014a41c180241c00c0c2d1800764014000d51141914502003084001803030326007083c100b010b4640c0c8501640700c41c00d544a40c4001003c0b43e0900314107200080c400348118035000400c0e402080d100e40c00408940c105081c0d05440c0006440400c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 78959336 1250 78958086 78958127
    0x1903050a0507030e0a06050709050a03080301080f0c0a06030b0303040e011202040b011b0308040f0c0810050108150c0319180204050c0703020703080a050d1401060e01020f120d06030f060507 83
    0xa11108030020380d20175003d0b002500000c19440700c0d6021a8442e148d0391116602c00344024011007489003030350040d4121820401114071030303070140a0440e00d60001e1141541d0207100401d040020381d0194000c040500401400d0324a400c1e00e404018001c0603080c1c128113292480041008218241407040304564402420440c8811526100c2c05882e0982d108000302006800404101003150791070a07400c0d440d030701c035803880300d8181c94134035031076962860240c00c80e2801d040c0000098440d0300840d80310b84c40c0700e109d468000301d9a110b0849440941c00540301c18483c0040e0151f80d0703550718084c821403083d440c51070509000d41c00c0d9401080150780e40070301800d9001408220450009800141400440750300c5a82c5e0368039401e130b440069075940a00d03440c2032011420b007000c010200240488642c1030311059120b40e9168442c0800499441f880019901c03025440760301031140d480490070140c82c9d52450003002084072601da64a24500180258084480d0303901c803070501c141c20b40c02060410081c119807511 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 78960586 1250 78959336 78959351
    0x3030c080402060301051e12061b0f0a05090d02030708030405040b0a0f1a0c010e0114130308060f0d021906110604050303070309020616050a0c17060118021903050a050703 75
    0xf4036540300c10b204d918894008003008100108515008a40d0000c00620b12540c0d0b0301c4a8605a8072104200c0b5515600c11040c10000c0710303001c5142c1940c0c90010740720340080c00d01a4140d029546c680c8a68090343c1d03c00900000580140d40c10411140038015000103103445078074000a0005a5400d060140d20a000d030480030b20030564103014070f10032544d81d402100c611421a19031582c1500c00d66910300c4c003d500f002401e0b41080d80541060300c0c0b82514000000170742d90f490001c07080c02c00c10b10302e004000510200202c2d915180002d524001c02400601d00c10900200e940041c0c4c0b030354400d82e40b160300341c0624071041101580001c1e4415612041c3c4014003001d203025540d0b240c4a200c0203080ea0145582d8018030403d40d1600e01c161100003807a42900c0c403c100315820000e0b565880300c1800c03542c4024542c800300717072080c0003180b1808040b00400208a0307030742092900c20203542d5a0044442c142d0342442f20701c03669003104420308240ca6007a1030014582c01d001c02c071039041e110028a000145410500c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 78961836 1250 78960586 78960589
    0x21b0d020f040902090a0603030e0103020702010f0e0604080a03020f06100b2704020406050c010b0415030f05150c0c070803040509040305070c05030d0e0405060a0b27100c03030c080402 81
    0x92522489a0444549a0744440940080e00038441000c1c06900b000511040014001003581f1490a40f4020b45840000100c00c5004400360300c80e04d08002d00049142018070f2442d802800d000205d818010040e83c202500c0f20346223071a0012126003640180d01131880c40d8191101800070701d801c06692220b16440c142018001801071041c0d0301525211456080540e40c1c0c100d004441c1c4c130501070010819580e40d503803003000900c2034210707842c02495540307487c6a03030b071151400d4811005801e0701c6030008058103166071101a0104207101d029582c03802858480c540d10380c03140c684144201e030207101c010345882c2220b02582c40c2180300e03000100c407680104024803890351640403180e0301551601d0a9039440080e450041c070000310f954003240d0184110b51116151603000100b81c2d10301041a1800c00c010b40c0d48100f003142da80341d540b0420102c00000c0014403800c2d8070304400c082100c000214944800500d2002080760040040c20038400580800441c038109641800b80b01c01c603482c249000c4060341400d40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 78963086 1250 78961836 78961849
    0xe0c090403080703090507060f021b090a0b0102011e060f09020a0509090601020316060218030304030c0306050603030c0d020d030f020a080109020a02070302060f190507030e0d1a07030606021b 84
    0x80001e001c0c07180000014960354480d400040702c0541c00425940680e0b0b90b80c1d4084d140d601c030020214058000c1c0300802c03142d1041e105c0d44480c64507004004540549640c41c04000600304104580c1c115503c2c0e850102d03490803252800130100300101000601d180c5070041c0548198411340024191034010080c5044456004040e41c0001008542150320345d00c80c0c5005030b1540c0302e400b82980c40e075074807004c2c0380040c048646d0142c080385008040307810840f62810100f544034403443c000240991030b030301404d00204500d07038003159019a014040340c1c94074620780c20711440c01218249800c01688840802446203070315000b00c0d00d902c1c0c01d1709425420050804030161071004140110707170140e640803030b0100d07080e8400c1019000450b0007034a11582c0d02c1c030b80e00d4202001d5219142d800d1003911031040f8046a14411402c4560803509540c4a9a01d01c422508011b540000c101c42502c0031580d45140b59180008075210318001c00365900d0001e9400d103010b03030203400d00e83c0101c0d00d41c410032054080311303083c0c1d100c0c0c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 78964336 1250 78963086 78963091
    0x140306040b12100507140405010207090903200f010c1d0d0305042111010804051e1e15160c2d051006121a100302030f030d0e0c09 57
    0x125000700315071209201098074280503607500c40c460b1044454a812030a001e5001600640301070780c0303c9504500140282d8410b105170305c2100e006a01901c4204050503841e40007004407032080c503104811040410380c10740f4208002e4540c1016030002d02142c841030300240300b1542198550700305645200e1082d910740c220865226101409610f5110f07820f4101403040c2e080790061301c10409144103901100070300800758079074210121110414280003034a50340c0544660340c400c1d41d006004141b480410822a50f1541c0c95500046c018420b0b1245407078036100403c41c080c00342e9044001071030040348840d000d10b20a1005802e0001c006c40c00c4440f0443c1550081842802d076070003500c00940408640300da40c03600682c04403886003000d828182e01c5c00b0084040f40c180c225940d00d07101401999103d14084118000e002c000034000058000c0d00c250600d400000150b1024010090740e402981d60f0700400e080c4181c0c03140c080c031550800502910042c1c0f49209804040d0b2100c40149054035060001c9140400301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 78965586 1250 78964336 78964339
    0x1a030103020418050106060e03252904090b040b0f0a05060a0203040f030f0210020105010b0301030f03020a0b0c0915040b07022803061401060804030c030503070309020409050a0b07140306 82
    0x48107442d0856400c528440d00000ba40074008010030381e61114000e0508e02c00461541c400d015079800d4903c20501044004850f05040b900c481600c4d290191150407000c5902d11025000c59500d98145034088400c003900092000740c8000c202c40c0004e10802c403c40d0049203800e0301c603003200c044c07070354031500e6130340420b003e640c0150740081c1ea81c004058241e06e5401543d004803d640c01c0310a001c82084000786404440c0b40c070960700c2c074804444039072003079090b21403d00460038010001c0c801040851603581c00d01c10320a02900648500d0041515030802c1f0040441d42c4115103400000e00440380c1c1010fa0064400b007034034880c040c1c101420810b00c0c6585214000010307115201c2c41c5d003101003030400b50f50140005001e040824110a5892808001a040001c0d42c44001c40000c00001540c40c09210601d1059506554009001c59250707003d035201d0300081e241c02d04166403140ca01c2c0c0180c4980c4110700d46039010700c0040c44109014686029200b000170421010000720341002c02502c140681500d0b0403540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 78966836 1250 78965586 78965591
    0x40f09091a06040b1c03020c0a060c0308070c080c0609120c1203060303090a03030c0203010f0c02030a030509070801060b070c0f031502030604110f030a060e07121e0c0809071a0301030204 82
    0x4031000001d0107810f121051a038803c644c10701205d03e01c1044216480c005101c3c0e0203807001c18441c0010030211440b81d109400110b032100460341d0000b8032031071040da03101000c2e041c4010700c18241e844000c5a0740000d144003005a11407024400b016004208100d075020500390b00b00d01c9e00f11004110340c0c840c0c1148034001041100400070a6094ae018025116007040c00707410b540720a5500d0800a10a014900f000d9010354640381000c000f20006010350300041c42107400451a0001007442200201030003070220720a80114100818004002c1c042c590082490000c4240c5820f128101080c0800403907021329038945520f00d00b0800601342c040421804c1c42528070041c0c03281e443c43c0104011300201191182c901c003002a50000058505029600608440703404102454035030b0714100d0098415909071002c00c2003030080003070030b0401e034015115218010080e2103102c07919035000307420341d14000020f40c0814480010010418030801c5108006c0c403250941e103190400004859695200600019002e00e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 78968086 1250 78966836 78966841
    0x7150c181a07051e06180705090103080a03150b07020a14030d1d04020f041701060b030a0b0d0503030c030f07020303040f031202280e011d010c0302071a040f09091a 72
    0x4180459030140d14181000c0d41c5a0104011040c1c031746204480c4a84400b40000e4040e4038104002203400c240c58000e080a11a40d0840e15421220341021404004050b281d1840e01d030340a001c000000011301310050b000d40c030b07041d407881000320030600d03900441268100c00381d040d01d141c0d5001a01ea403020f030060400404031125030081a0390302585010098000c2d000180340c608176007580004100300c40c85c0384100b25a0342800c10003a0b00340e461501c14090310744001e0022402c0141c46a00071200e01000a040001f4040c081d501d0702c0c1560001c80705901940004820000c1264441060f140d000a103407001e94a180f90940d6501d00010320b000e406800c000000d0040c0c0e20056040c0d04480d0500c881403120310342200081d070050b40c944415032240001406110750440c655004515810141c05a12514050013550340011501880500070030740862160007000036500d419044d400080c1b81c03030109980e41d201e04141c070b00d4199403607550044030994580304c1e020b0041180310080b0f2120300090926603044c0c0c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 78969336 1250 78968086 78968093
    0x10b03070203191e031b110304050405011202030105070918090c09050a0c020f0a0201120c02120a030905060615120624070c060306080303040807030507150c181a07 72
    0x180501c3c0c1d028070741e00e028803158039011900081041e410150781c1c0011148007000c200110141c0c0e6154172000b501c481d01c408150080c41c0540c50710b43c180d1003500c04076404c040e5141c0c00502a02d0080e841401600415080c4a0542c103003070040d107503c1020342c06e00c0c0e241d60380b03860000d0cc08111541c078050f0f104c6680c4c1c2155402c00400310720140c010f181c074a000b8452030908284a10091801204904c0075201d01c40380c0c1d2007020004140040d81c590140c44030b06441e051744e4a060b01a20301c00340d822007180110130881c8126030010002d4041c00e50b0640d00002c40c0e60030b80c0b400318500100a000ea61151440c10448440c1c0d50511080742c2050444c2c0c0700d503410030b4644201190140c410784407500c241d0a61b2019221040070310a000e45400e83c003030380b040d9500c079590305000d500321240d6004645464000f040010040b50712030004102e9140b00307207408c2c0d1500b03441d41ca81e055405d84500c2030051790740e00c401002c2180b40d84003d03082c44070195041103480c0300c1e10300040f441c00083d40400754203c4440204840050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 78970586 1250 78969336 78969343
    0x50403140c04051518161d091305060a0b13090c0b0406030c030501050d03020309011b021905030d0f0905010c0c08030703020105010f060e03060411131103010501030b09040209010b030702 82
    0x2600c0604188400c0c10700404d0700804421148006000301c12112480392185620074115001e07400e07807407a0300400c0340c280d8002c942c0091006044174041e400e400700c20303516032114403400303110300f0108490352001c40c030a20b442801c040002d0400ca000906080c051201d81d03032a5000c18400000c010f00015803140175240c62260312000d68480301012401060000e802d03500740e0041110300f50700740e50401c41c581e295000c00103251002c060190042e8400c0c81800140c0d40620307804031068050f100745e0811882940e0005010313000364480c41205a130000b03020441ca0504100212031103441e41400924552040c1c0001c00704906842006d04100301d421412050040202c0b8503000b500a2600341c943e10600350602a01030502032260203070303880355058002039281c4140c0c00d0303580100c0e0040140809840316160601e01c10608844168002c46450017050349076420700c140c05407803520384900e503140d601d81400941140d103040460390261001104000c01039840502d003e0559400020a58407511203034401c034075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 78971836 1250 78970586 78970603
    0x10c150603030206070210090b0720010f090c080a020f0f0d05033f0f070302160c0801050105010516020d05030903070f050f010f020d0e01030219030f0b06030705040314 74
    0x4100349811404024140d0205802c1d1248209408a0710098540345421040720348042c00902000c40311008a040c00c0e00c03d10602488660601e0030000303495200c1289800c5482031110716114640d00c54101003000600080f2a0042070030402404101c4445d80129521480c0c0240b017030700c54400001842c0d0555900045407038510741000c00c4030746442e0118441c11801c10302000140c0b088415035840e010740c00300d07540c103085940e280545400d1151224150032040d081c018049509154081c80082ca6500e0040081d241d40d50080c1c070380d1400c46151010f5242116010b800443c1045030402c1002c40004251100400199058030142034003442428028150b000d07860200d549805100780c001000c2c40302c0e00740d0307900707480c4111000415040a03170010368034070000c2010031016801503103022040c3c500172000c1148040e0181400341c40c08051080d03070301d4010180490000400d0341c62051402000702407113101400700c800d0380c030b1600d1070910030400742c1540a5072100400346440d01c131215620700e200b44030102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 78973086 1250 78971836 78971873
    0x1006021f02190c060f0519020c07051f030e06100311062101031104020936010f08060109020f03010e07090e0c0306030606010e0108130606080f010e0d0914010c 70
    0x41d40a041003004012141400040d44c0f0541030101c5c0b0502a0030302d2050901031410b00704207150031a0343d064183c019400c00a0520f070070307000c2d0040c00201600c40b0350859005554000695042900032100a812a030014032940d209512a0041000109006800b03074140c940017005045140e4030500056403030720a1040240d9402c0c0007604044000800c425051f058a2058841060604007113080c0000c034081c444c4402da110703148460300000050050408191040b2020710300d040501d041900350090716080e400a424200000000c20050800340001c0f4003500c0000d00640c07904050192284003800117020b6105110b52031800f00d004103000d040c03454024424006000074074034120640120642003140d40381e0181c0a1200003c005611a0520092810058681d682103803520900c524118148070021242c0c180d5034480031480803002c10080703009101102c0041a8807622846460610542940e180140088001e092100c000031601448d40e40d0020b2038007105d035407a503003816100030a40c54500c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 78974336 1250 78973086 78973117
    0x120f0e01060f2909040b180405070602070e040f06020a090312180b0c0a08160203030d051510020c060306040204120c030b011e03140705030d0e091006021f02 69
    0x81882080d00c200084610140002255103c0d00c02001d4004078140c4542c81d62010070000c5000900d0a50b0204000380710203800c01c3c110040340f0154456103403054400707440e83d0748a14010058158104880005801207004505007810286d035141040380003250003c0c034258012a188040e180b065030040001e40c0c000d121921101d001c030318042c184c0540c42220812101071082d012500f00b21300022245044500001483d00c1d100c03a4540f0110f582002c90540420840c81c3d8500f40540d40400107040100c110343c00000382810620701d00094441c1c580ea6070360003801d10618420300e0b280c021480c900c00c0031081e9003940d0369561304800607000f441190480704000f0181e00452052068112400381a030344219101c2c1c0f5140d895a001d044901031805603c444142c8c0d8500a00024001941040c00d1562031021603452986617400603007801c1561402c03900140c1c040c1009181ca140100360346401000704681c844805d41480c2c0b000b9210240000c0c242d00c4c07846181890300102d84c1ca581107400c1d184000341c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 78975586 1250 78974336 78974339
    0x9020d0f1b032004020301030206070b1b0c0c040c080601020303041407050a0303021b0109050f040908040509090322030201080c030702160f03020a05040204080307140703061e0507030b01120f0e0106 87
    0x3000305406071505030342010000d031080e2070f100d0800c1d108030390603070b50024000e501305480c41d90746c019111402080030303e580500a030001c10714560100a080e20380c901002800b0710054400034441120340300709141c4100305004060100da0f0b40c0100c1103e2b0015005107481c031121541c04625450304600c4d0b84400c4d0030422410001040c90390125000c0213801c0c180da1813045407449c4078011500f134055801040c0d03101d01e1454506100d840c0640c440d031201403180c000d150810b42e49000240c58100d0496100c007090f040000d00901d030b050035501c6480501f5a0361a01942e00d41540c0008104c402c00400c040d038000d1002006c580414000c1007140620400103042c04000d0b5118803212030034182600c400c0707028108046011446113171600941d4141c0d07140500031401e0a805440b501002c1e80d02032007042d03050190600100100346d55001e10076210300c0b13001c00d04e441d81030b91003017500403036100805150806181c15281d0002e80e0b840810080790140840c0e000c540e960060200c60014100400c0901166180c03400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 78976836 1250 78975586 78975593
    0x9060a0c020103140907060f030b0d0803040201121401090203040201050910111005011a070813032303090306070302030a180f03090803120613091509140109020d0f1b03 74
    0x600c0c08554800ea0381401000010b0700c22142a032030949482c42c06403c5444144002da104140380b1180540919010810440c04000305034000545481a030790040000100401c1d9604621020100c80a09c4c60800c00050301c0804405000818010300307034800c1d000004603082da803081040c0c0d40c0311304008080c40d0350103042d25800b500c20110a14400e03006c1c003502c1ca001207074801c80d1041c107040310b44400c4a000d903100e41c0c800480c59540020804c6546983c140f005500703c107105460f10000d103200301c061480e10f400c004040d0070f0341c090016840720150303c00c1013410300340e850201e05990052a6410056100d844104900c0080d0143c1150001c840340d90501c1e503801e00501401c41aa003034000d84501540c03548500001d9120f00c035209641c00135288803c00324040b8181010104030340403d0b2300001543c12a555601c0540c0c1c19617000c45464507403107660510510040440c2185041c020078001c0103441820b901140d01d6040014002e4070502842200d00e00380b14101c41c0340070522070422140310034540c41c0d14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 78978086 1250 78976836 78976847
    0x2030c040b030a0f110702061902030417030406030b04020405060702042a0210050618070507030c12051e0408190c0807030506090c0904030804060e1513030e03070308160809060a 78
    0x24541041c1401d10501c0301d80070281d441252040707038002c8c00302d500d080710711017049001c5060007401c03001314401080000ac0c0302d032221070540b4404041001075507440340741c404d005040e9008400b841e44110703c1000200060fa0b1442c0444d6607042d4180c030003140705402004c0008020050000c0d01007555001503441500780c1d40859060000140d0300000c10a544982e014030016414202d05100a40ac0010103e81c004c1d011710040e040c4684203240066040e04550307511415000c0d0000480d0204101265080000d00f4821f81603c03c0306003591100e0500d803921024a80d2800a08420340c124000303680c2000601020040c0c0b00013901e00c617011641c01d69074a2804c0c0d07980b00d10454001d0080c0c012000e203e0b80b01e01d007104200d401640c06903210100754840f511088018000507500c400e15100d40300c00d2200c2c0480c4000301501c1461000c1e402e100366141030030b014000c0104110014443c0c1c10110742400051500e906030340112154103d016210320b1949007111080c0300b00260303a50300140100b512564180d010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 78979336 1250 78978086 78978101
    0xf09060e010903120504020a05010518060a09150311090d02040f0608070e0f0f0f071b0305092b11060f031003140c010e011b0f0b04031b080d02030c040b030a 69
    0xa54034900004d48003400f0a0031990709550003940014405c0d41086998410406400d40315406880c02d10f1010220700080c0c0e140c1d0010314640e021a4125004101440d00e04a444040c01314034203052100300704910200105114900c0740c0c074420240555142e0942d1501d50188400d01c2000301c040000ca52030394010b5544000511138030406640660006891160662429000ea1030010b6010b000741c80f130442c00c04030404010100d07410083d2240b01c005032403448800c9100010f00039210107946450701030a000030024195802000001403003c60302c0c3e41c16214110030282500103507010003078400701000a070b8a1140001803a20a14040180800e40036480f0018040360300c25072080744c004c2040c0400a80350340c1d9458049000c505100007d91032540200c1d01e00101c0c4070b2081035581030030019030320303e0305039403210505882000807d410881016007040e05202d00f004540720000c880c4500d962001124450500d01210040d0040301040c000702c00002510040c009507040203840385010040b043c01000d48 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 78980586 1250 78979336 78979343
    0x914060906031c0309031704140d02030a0c080702041428060509180c030706050706050f0103080406030e07170a021305011d0606070204020c07032a03060f09060e0109 73
    0x11040441c86516000900d5030424480c402c00304500d00c3c080505900404404005905002c4030724804403040101c80701d464407032032040f40c419101c02c40d0043d42c140341c02030302c050042c10356008200e405500b07134116040c04070155203c414503668850700d01c0404c0c09048140c0e00e014440300408140200000960416001400718801000c0e20441680a480c250303586031040580000e0030b000880c1c0410800681ca03203407009050f08495035500c00b4000f192502c203480c0d104400080e40400d6040800c603840c004d50b601b0080d6a0030403005941980c545081c148070302c5c403c0c1c80a169a90002401d14802801000000d203841d080c0c490510541100d11074441d03010b410201e103d580816203807041103116201e035905a440100c4034908100341d462501c5845003020309515031000c024044c460050382c5a00007050b880132480054440c4d9417a51401c3c02c0c0b00f481400000b0780c1b10882c111440510042c49d411102240c0c2c1100000c1411f00440705c41d20028032183d84080c040b0b074100217042c0d10344001500b040400303074030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 78981836 1250 78980586 78980599
    0x7030311010c050a0513170c0109091109010f020a120c050d080c090f04020408011a0a0902040509060105071a010902042d031103070f03060606090506090307090e0304091406 76
    0xa8103241c00ca40814020768081107080c020103214034071940180280704080176055400c10b1f212000068400000380925103e6400714654100e1942d10080079801000516410b0018040d602c9001d1494003882c1c0c0807904004445e40d240c03462520030011071181d2904031010184c1442d500c1402030091040200079506442842d60349403a003071050529038851454008802e0400070082d08210407201c0e540c2047e80c2c407030340a01010034018802c0c414544100d0030f0034070b20821081c4043c1803103410041da078040141184180801c10440d241c94204c1540702c0401d19040d5691602da28044c1580303843c00c41c103d421204c400e800452034180c5580100281d450320a482650b8900c0b80100c0c0c0c003070000d81c0314524000c000b820803c0001840e6a10500031006004061b15080c0c0d449204841c281450740c9c1c804c0d10542e498040c10040140c0190b0b40d20003802041d5003da02d0480c488011903558010b038419000d40566030b40490810600600541e0301034440807905208040301c0c401200c071101002d85009100e040e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 78983086 1250 78981836 78981857
    0x317090907020a02030c090901020f0d0606180602060c0304061b020105040b1803070209040303020415090f0f0506180f0d0303050603060705070308010306020913020c06090714030705060d0905010e070303 89
    0xb8000601100800da0090051401d0840c010a201c1001f00c083d006404541d0288064600030081e42c0c003902000511113000241035140100081451001840300003007a0030080c014400103501050580d40042c4100c0c60a1b601d0300e561804400500c0541c3c10641d040402e460032042665064009a0040d80200500784041d16140520380b180c8402c9140030140b03610400031540107041000b0307401d0740540a401c0040c1000d60351611000c103480002c045100082d0180360612041c00c0074402103000e010103c1e44100c1941c1081c001c580103110701082030306034603031101c8002c05980d1503003401201440d024000142840151401402074903066031250300c0b902035034001030400e5108505443c455501a5074a8000381d18580343c0700000c1d07000d500a01c0c1c01a0003007c11031080010b50000301202d0300980020105c900c1d1140020b820140c0a030800c20614440f4a0308003065507000a0700d01c25035800700c501030781e184858030740d84000306000c0c40000c0165080829032035505901266100071240a03454220303424 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 78984336 1250 78983086 78983101
    0x606150306011d03010204050a0e040c0603060b09041a030d0314130b04031b0503070317061e120c0a03080403030801120519050f070305060105040c020102040807051903170909 77
    0x80c00101ca400307000400060340180140d2200549407030081020b8001840c003500ca0780070a1071014660003500031802010140004c0064280c4010020b05103031030200409401c2205001a1b071154200051081d40c5400107078420000c92451414290801030856030081d6000b18040c014010f10b03e50890004200000292443c0a5040164015900c8000c2884561395507500355040c0b043c417030225641800c40c054010009100300010152786000c2e888101410340c1c00740300c40d480a00300600441c00380c070311140e0002101c1d42d55585042c01d0b05089a03010620741219003441d241c280c40745040c95100c803601070700206101400c80240280c030300a40d11481c160f070301c5400100300322584078002050350380880c81d40040d0711103416106003d02c2c440c4041c2e072007100123854410f291000c1070b0170a031456008070004101c0b0f4034041c492180201040c0c0001c0d41850700e445220307612010607200303e600552505100e08d1242d03800541e01000fa542c0a00000c5c100c00490720840c00d20b820402c0c00a00940120011840702c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 78985586 1250 78984336 78984379
    0x5211608070e060307060c050a0605010303170106030e120307050903070311010801050603010e040f0819030c030615200c0d0809010201051008100e1002280809210403020a0303020606 80
    0x10007015000f00170303291030b0500407546182d071444182c58038041d4000c000005100303409510b00a5003c1e42c1d505105c041ca0700785c0300c0d81c880f0041c0c2c0a4400d151034070410005551010583c82000002c800003203840f50341e695000e0355144584441c1550602825401204001044044072950340382070380c0303056241e82ca030320922031140f00070300401c1800001040028002450506002c2c6010f20a2842a05010f8504000740d115589240b84e800032944030b004072100a40d1620503c40200041000c00c4204141c1c8a40544001c1001c00031021a000c1c40180c400070340000c10a4142030b1001601501082005040a00240d040400114015420840424030f15145c020750740044d1603918002d40800070081560f00b00800c180308089686000303503480559003803000c2c0b01606100c000c5034100411810126101e18440001c02d01c6034003030188a6040c403214401c00603039410481e0403121303d08100c2e20b40340d03500b4900740201e6000941c40000c07101c000c0100340d030100d26240200c0040c0c5144864880540d0b40c40007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 78986836 1250 78985586 78985591
    0x9010e0613080903070b0a050d05060a1203270305031801020105070f030506040605041d0105160c1211160e070f080c13080601240302031005211608070e 67
    0x4400e0114050704021076004001081a10b2004048400180d600c60024545400028030392000c282c021840f00302c00d000030b024455102c03e0403202c01416030704202080c91803814000d805003c11485e0704049802180f1200142d0000c204104005402d035660314103155641e1201011440617104400124525401406128000d48854441c41e044004143c4100d008107001030486034031075141c4600141070748444c0f1550780c010505000c6500d020010741d0a031070031b4440c00b8142ca00700f9250000701243c16a40050381d8800f0320745c0040f120301c40d00c5d000b01084500c01081c000e407034103d0244035509092211100d074060110342000c02d49400c030703541e408801d868110503038194a000c00e1411001074800d12201c80144400200702c000d440340c0e9601c0310b990500d00b1009030826004c004001030901110030344050300110032070242c41c00758550300d465580d1a51100340740c40382500400303c141054020344030800440340011a16022600380c1c100c03d40b4104001d2049108507081805501c0c0046050b200e02d4448a2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 78988086 1250 78986836 78986851
    0x80a1b140319030c0f050f130303121406060412020a0308030f0103020f0306090a060f0e010204090b010314101202010c021c020a05030d0e13150303050a080c030f04020d020a1a0309010e06 82
    0x1090681754050544850740000790b11581c2000030030a908a5900b440600d1002c2d6001c0c0d44c800c0e041500c4448800200d51401e0f0b440540300d0400810005030390344400850301030f941c00811000c968501403000c0750f038807582c030f4000034180c001c08410040d411141551150490b4022524034442000410515854040c141d50300186900004411004030303226070041007806600350000110050703400d500f1401c9821030340103048001d858402c01e90481d0390502803502c08007405603c000803418200c10a41c034a402500c00e00f42e009a1407001e6100350381c0641c50342d060498000d01418600c200200c0035010044050b070b0100e00c600400318004c260f5040018050140d01010b0311821944004901009141c4504c1c0b506035440b65202c412813520001c3d03503640381d00103500c01e8803425200c2a42d02c00c058a80b4000819441c400d0070140100000003100500d416000341d0151100703105650503001181c6100815001020300414402030281f00e00d416400440c419920a030080120301a070701e00d03507a101c18059036040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 78989336 1250 78988086 78988097
    0xb07030c0209010e04051c09080304080318060309100513060501030807031e02031806070516090608010b0906060a090503071706090a020901030b07050409050709051804080a1b140319030c 82
    0xa10459410307176000e01a200ba48d003007071840307950740e6017580f455075210341c001040700d42010800c00402d842c032904280b1007403000c0301e040e400e5207841c58020350303900184800b01d2030160b01c40001c43c0344000c2090b43d00542c143c015006120541e105d04000c031860340300020440c009054030081201d01d28070340b80040402007269001e1807030010766000c0500c4148a000c04594402800c000c22400240104401c0f1683c2c6056003c140046140c64a242c0454406501c0b4003200d034109140411581e580002c000d5000c04100c54481c1c4034030018204840d8001290442501403090000120b49800095904a40382c034101c401c0303804641c2c480c032a1a07200c0c0001c41c0001d402090f68001440050b9000071501d91154480c500941096550f04030301040d2007090360164040b0340642018400c0742080c03121030690500900c2c00300100c0c00c1070b68440c0803911510007094100000501130100360003410420340c1185401c030081c81031103503085d0141901daa01c8031110300151180280707403441c06806402a03059900307503503c46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 78990586 1250 78989336 78989353
    0x206040b130c0510090512060c0d0203090a0f0605240d0201050c0f01050109050403111b0906010201020408030c161e0603022a0601060201060b180d030201060b07030c0209010e0405 79
    0x288025280c4800040ba44821070301c00100365511402000f120b007415030380d902010540340400b40005805210342050080d00040b0402c142d019000080300c441d0315411100590700d580d00c00056042075105800100400c5071700c0414424001c1d00c0d08050701584101c084440304030807818040070125140b54206070000010641c1c82c2c00340d0701a201070801d164a040507103a513413003807800307007030031a00240c104003401c0b5a2a000e220902d6170103000541d40e50382c0301000700541d8543c2d168104107181000d04041c458080364000850591003901520000c14030102140e49810282d084a80c4500240c085001c0d0b012038100009100c0b001c1c0e207040c00021200d01800303c00f860508004401030340c01642816000b16010300100440f241240006030580382d8500a0f2455506210000342960165400038103154810300010102540e08541c56520810072600e601c820001d600d03007a80900701551001c4060540400c110702812341090f0031003226842203032400c00c50782c0c0b2144072190b00e8400340c602411aa000008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 78991836 1250 78990586 78990601
    0xe090a15091113020412050a0b0106030b0d140c0d0606050310090c1404091a0f071d21060106050304030228080318030a050d0b0901060503070f0e0607140d0206040b 72
    0xb0143c0b4040c410a8098a03040d21604001402c42c4c0405088505a000d0000c40c002e000d82164610f0140240345018400c0c140000d0004103031606158010709107009480c2c447d00040810040143c0c00c010181c00c040d01c0e11682d0810070b00030007462240501900400c201c24601401c01e20a50606c194032074241400f030307428040441034105a411140d604070740e0b10414900803401c00c494603800e103400320074600054641101f48480307030003000d03108805000c10349480f0006025403100b810458803060318100f128110303115940c0c807221040c0c00c9082660080b400007040881c0d00800461049010b0303000c880401c00c0c80d0241d075210010541d000704180307224030219000940010025500312404030740e00c440171000ca105150842e480440090b000c950700061500c040701207406080146241119068680e6241060260803403000034012001c101283c110313041814061091034056883c0a89120b80b07824881c64200213440c04040b4601140c0301c1e01071302884081c40001d10780c3c4620b9006a80040d607446400e03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 78993086 1250 78991836 78991849
    0x40302031203070207120f050d17010b0715020d050402180106050301060c081e0301061b0f0602210412080108010e0a1101030207080f040e0c040303080708040c0e090a150911 76
    0x200f1460840c042e10f040000c007030316803035407480500c0e00682400c10b50380340b00d00d001707440d04003462a070406114440e03401160711092807104504440d81d0a0103d56210010303e81003041e000140d10305540503202042502e02041c556200e148650300c00e0780c10400c1d8281c5a0101540040244121400160700300b005100c01441128410255132180902900705200c2c519030004025001a82c0d00c0c001c2404001004115441901e62180b403000c00100c6400402a03240c103183e5444191014000326000100c60b182080c82c1040c0c24184508800c043d242414286051741d11035180081040000e541c41e0000b2400403418031544503860581c4006003500038907a07582d180d00c1c808582d07455060603401c1c0030140c0442c03046001040b140c01d041203940e90b141d0402103401003902d0081c2150101c648144410f10000360420403240d040700071070410070120b98941c548104003500320b420006050080300c00340f003c41c081c00110196a680f04950000e140c00510304000b00312944c40801401280800c03000022904052 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 78994336 1250 78993086 78993091
    0x20031911040b120109030f02011b02030f1308060f0405011407020c01080402030327030709140c16210215100501031e020f0c0c040b0604140a052205010b040302031203 73
    0x9040700240141030f031185030171200b01d00c0c0d064002c0358244564122150342849264a022444c1100d91b401e0b11034604025640e014001c3d2005404100069142200301003000100085c00c031601280d00b145030000818102d844291030403a5990700b0801042c81c8940129109403161391103074010f04246142e18011501c090707002d0010b9030503000412440700340202881c00c150102c8040701c2c080107542e440000340761a104144c0d11011079140380461030400c0070001680d07242c02c1806103100c65210381d041314271034006080d002c1c402441607002d0030700c1d80000009101c0c2200d902c540740d025107400710640401c00baa0100100c2c1e0f4440d0014048800b4016503000e43e100f80e00c0c002e03244401080541c01c2c03440b080c1c122b030b0140103482c82c4100007003004840c00208110640d11000c0c1614244144a569030204a1601686c01003000c802a1040c80e186151a61240c0700014440104044011001d003681c2034509142d80784121b00e4181010004141041448111000c0fa03602900500c0c601c40c007601091582d4001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 78995586 1250 78994336 78994339
    0x70b070c0f12032705060f09030c01050a0f0b03011e0e0c0915121501031101260603070501020619020901170703050a050f04170a050720031911040b 65
    0x1100648000b080e40798540d40c014402c1034034006404016280704001c0c2002400110f60451414041100020800301d1500d400003e040480310351900d4094880c0d0441c0550800c803445503180a041150070a80341d0080106c0d2144624104004807c80062600742e40c0150416207003d0f03448004000d4080d0954000d4070007180e6501505c1903842c0c100700054012a05403500c1000c6101000c0c0065240b03082e400c004840d8441c0802450409250700b003c1042900c14800942400b0041440c60750590050003102281410390154482d80b46001c07440c00c4202c9003d0b104240288200c0d1004202c95000050050150701d640d00c040d19480117000c40500030754485100303a81004102d210144690380041030003070060080f130f1004580391030070030009822030b0001451418400e11b404144804100d503a80c090241d140e015610980c1c890728054282d0f024458001c005040c40100c10008245003105080b11080d001c0c02c5080e213040c4007803404500e408c602511005401c01d490810040c0c3d0f140781542c0403500c031010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 78996836 1250 78995586 78995603
    0x140411010903050111031b070c03020112110316091d01030215040b040902070203150f06011112040311040605060a0816030902150304020420040b0903071e0f0b070b070c 74
    0x440790350700344c20b4524011049440c04400f1040c000a807841ea941d99540311341101055003002525220541d40003c28030010341400545180c550958241d03820041c150564001100d036241000310000701031820300100600010308440c4041400d04070701100030403903107e0840c030b032000fa401c42d020016118015208400c40e8541004009601010703180900b005082c50200140c40360001e005040c1061410a8003500b01400c8008102c1c601e01c4c10300a15812100038607044211400c01a103503031505d808068890007030280810008100a4540c9031081901010b650600210b85c0c2c1d2002e1000380d02aa6401300c0201c0ca2020025003e07030300c8403038481e01c0040d007171801040415013074001c01e00c2c1d8100002901d81c0807130000104025410b090084a0915900c5100010300441007007081e80a80170301e00070844850030000d16820150340030021032016042003800800c1e1450030041406581c0580c1c40341d5400c4003800c0d41c001401030000f0302510181d5400405090311036680c00012500e901900408841800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 78998086 1250 78996836 78996839
    0x506060d0908070308060a050105042106240803030c040303050a0e0405040b01080d0806031e1c051e0906120702100905010606120504020d12110d051c1404110109 71
    0x15026100045000300842e580d241141d04000384442c1c0000d0255000304d50b58403041100e40da001d000c450455050850004040003058511040c1f401417900180c490307410620150020b00d90314042c0702c074500b450b140d02800d084c0d80e818016103d0108403078401c5c140d50103120130004240144000c00700c002c06490142c076001210340c006000c03540141d4060700c0c8211920018081090700704288007120b0300505007012145400400070b076962031804c0005654800d14400100c0c0d1050800ca201f90b1000c4003014081998044100200250040210040c010f800044800d07103048a442c01c4501c4541e018101a25000da4003480b0050304501402c04000c52092280a200112492040340d003218811070000c10f490749454070040503401c00d00f40114849d40f5000600006035100180c01d1003059200c0a4840366019260003038802000c3c0c1c000c111064050030f00420243d590050041c8003a24032400400c1c0c5600342d400400081b50044081060321004020100b00810031201420385101d50526109030074030b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 78999336 1250 78998086 78998107
    0x40221010e0604060b01050c1e0a0525050a0b0405060a140310030506060f130c0201090206070506010504050c0a0c1103030d240e04080a03020906130e0402010e061903050606 76
    0x458071151071810981041c1d0a0104104040c0100c0356040000d01c0d0141c207105e005190103031100281420076808580f0614008000b80c1c00307016810165402105a5611050880c407586024083c0030000f10000801d0502007424548445148141c6401051003420700e4100b006200b850360040741480240604548955039840300700005520485c2c001c2c244441d00c514510300703907103040c0c400780c40c1500c602128450720140c3d03240c0000c0391804100c034a5000c00e0352186540c06030b0050100c80d0003e03401040010f00b020074010300041160484030103a504119569030303d0941030050280215400c0040d10302030084010031f4001e8004115100f0040c1034a1402c800d2a00c680c080310100c1502c0700c0075803500650f51231411070a04404000b8980c540001c3c54901d07082c0d80d40000c51158850000c00d066003c40c12040d5070b1640782c10358481c120401d10b91000182c0320b400b6004003e00c1100c0890000c0c009204140407401d050b4103541c044001c5d1100300d0341100f00f401d01038000e010700030034050300084240101c0e0700b00f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 79000586 1250 78999336 78999341
    0x6090509030c1203061c06060801020a11070f030807020909070b27030321070e09010b0705010b0409111519080708011d060409060e06091b010207030b04022101 70
    0x540c006a008503610306164000600781034002e20f110a08400034401c00006458a21200c1c03030f140d0f0a41d100000d0b0343c0c03ca150200007402030340c00140f220b40c800b050040340160030800c18291031010b501101da216990309028420500207000080800e0001e010013070050900f03101c45a0401403820a42ea501621140f030725400340c001240703d00035500159060103044a41d0819012404401e0380a5842d04202c0b501880300ca1240e080001c003c21480400180c0192080b280740752500c4004040d242d840d6940d90014540e40c000070300640d02d651034020000c0c014909031052001007039104032009038185546080008041103d00b45504040301004403900032005440381c940f84181a4461082c14140184010040e85058122181d12000b64a114030916500851290300510807074011800c605540741840162612101011080c4140020720801d80c0021030052419402300e0003212240c4040001281d882165200103404081d024000c50054185011300c0002c1071b0107480d948400e102005145801c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 79001836 1250 79000586 79000591
    0x110a020f030c0307060f0e060c180a050a0302010f1b080702040f020307171305010213030309080604171612030608010b010e0a0b16120f081602100518030c01060f0f060807050d060905 80
    0x200300000b14410940c8060896164ac00c8040d01c2c8024500e00f06800f2803201401800f010b814400040b0405400074495200c441c0b03003c17010846548c511101d0314040c807490300000b400b00e10031402c03e5000c04a5007018400d5038440c00241cbd60710b02101c01004081d0f9141000030b0b08100408031090804004100700b40001d212803010b0305000c00c0b0351491801c0090090002ea080500705030884010300002c10440300c10441180141404c1d035a42c1e80c42d070102524600040d010040920000304484035005800d50301000449415100a22543c14040011254002503a410a910000b80001032050130205405489000d0304000459444400342e00c41c030004907007442150700056485001c0c0080f295021018980180400904815542c0c5059001e03442d0403006000082442e0385100091800c003481390524041d04004099030741d1150341a98941c041c03d028000c0e040c1c90400b0f44030024070348480300d02034400c071920340e0b5492542e504c4603041100d59510450aa103a41074480c1c1d4049040034181c4240c50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 79003086 1250 79001836 79001851
    0x910020327090603030316030209031501060210060f080d0c170c030a022116030e040e010f060f0f18060f0608040308060d05060c070501020409110a020f030c0307060f0e06 75
    0x4102100d9034003000742c890001028103010b03400074800c1c0705c800b10000d2501820442903041c05070300d030200c8001003031801d40c01110700c0080f0050358000064280d000308400b404800740b59000e10941c0d4a540a05280384003131720404000c2d51041c0b4030510214802c040814030248a49111113402100982400454001d0340d18a4895000001e082c040c480d0104009100041740e040040140c00c1ca10040c0d502500501100d0f034204401d814032002094450710b180f400c4108000c0040003070b40121a031960007003003404c46041d46186040c0380030074500310010901c401c41e151000145001400d007103241040b12040e04200300d909440300c0340442d4001404e00040c01400e0f45640c0d0200c18941810300074103680c1c0240040d4062251f110054000c1030380403403440c0c0c0c061142d4610b103a8422146c07520703a00900c900c2c0c1c400c44003a8940b40e000c1c55451080c0d0014064000030741d084401e210120740b4140d481c2d1280b1900c2c882e05500030031161300000e41c00c0d004000314081410340061803000c191010350604204460a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 79004336 1250 79003086 79003147
    0x80102040f0e010608010306050606070f1511040b030a0c180618060806090114030a06050406050402010206060901061b0606030609240b0a17010b0a03030203041a0901020309100203 79
    0x2444039400d21a01d000080190b500d00d0205549401800761140700107000c080c212a40360000900c2545500c01280d00707131540606d8400c5844550304004944021324891806400d08040100e90140307060400c0d50241c41c692110140745881d84003040d80101400d8a0301020b0040c1c10020840010010501000070510350f12180b0f90b4410402001b6245400d0360400002c0c4500340040c0441600c03031060391415250008002c00202101d0f10000f072501502c3e0400414442c100010881000340780e420140c0554800e070200e909544130b032010420008002d02603c0000349500900408008420203020440b9000b03510014032191251a82c00c00d40d500c40005942007440680b0403e840b008849445401d4403c0c0a8200080c4e6160340021b5074494143c030917002c080d2928a03101500b81c4080d07200610341000100303040c0c240ea680e850080d49a030082d1292011100f18146041c40f110b6004c000c4034281740d0140c4c080d615000c540000c02011003080614041148801d015010846420010b1141e550440710785c0c0d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 79005586 1250 79004336 79004339
    0x60c03090c040204150c02041107050f010c17150112020a0806090109150302061e120103060b090708280c020718020a091712070308040201030c030e0d140c03030108010204 75
    0x880385003058070069103009510411082250419281204d4042401031811141c0c2c4802400050040c008041c1c1303095826000088080410200240c07030303c00ca207130040082c0f00c1d6001da860140d400c40000003458004041e008001002035041144846990205041c85212032240e082c80307808a8015412520100341030340f00703000c0345181010185004054907101481092003200141d03a01c131245201c024019800422980c803016040700c451200d04101141041d00c5041450403503a02a400f3302c0203485a0345001c1d024607880c02c3c07554680d44298880c1e1500720ba6a1148a0302401c0c240008802e5461602807c0e8440f070041e200b030140e280d0b0409158002c00200341051102581c00080c04411001c1c9881001079901c500c0d08440909d00301c52017406a01500c44450414a0824681082d11701d2000800500c44042582201c83e05004500030b980030448550f01e410180c0842e40040350000040e84a9158920350522503020520a491400f010f5030402c81002c1d180c2e803460f0821b8001c2d10469401290 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 79006836 1250 79005586 79005601
    0x4030b1302091003080f16080c010204060f080c0a121d060115050304051011070506072001020c0615060d090521190513050303160215090306130501090203060c03 71
    0x98603800c500f103038031010382d05440c41d660460315104403030768a994240f0110324400c400d100b5220101e800b5800c80307202955404201c0c8900c2c000e5025005100c0403517414840024190310403003441e88900c2d90f4074002d03460201c0b011400e0315481007414580c1e4130991100c40f55046101445a10b0144154040c01000c1ca541000c01c010050150b44c2131841c01c01605000300304c00b043c030000d100e8850428407040000c480010301c403040524400c42c1006442d0303100e204280b0042603444500c0c54030080842c201082e40601d0456281d00343d2088540c014103943c0f001c2d020400b504a654141d03051480d001300a03074076105c91500741c3d07016141030000942c0c50350040e1640c441821484c0b00603078001c44c01c104042e440e085241a42071848650303c900801000745c00301c1c007400e44914810380c41024200003402c580e212110603042c1400708510010403400303044000c40c0a6002980c007026540c030158020064682540c03142c080001583c2900b2050b81d0943d2079600e06d10140e18107008441c0100d50001d03186541785440c20303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 79008086 1250 79006836 79006849
    0x70f0b060405010501020d1218050708030315220c03060f080303040b0604150b070221031306020f1b15160c050108010302090a1d0d020a1109010506041203030204030b1302 75
    0x80c004c2d8150b4020240c4000c0090b4480d13421105040d146400046600035004400e1081c400c80e0030050041c4603a450100f2901d40000141d0700c140c2c0141000c1d400d000c050300500c00102200600600b4502c2c0780d0301c12003406900f40d04250a5030f00149030005d002c503038521030801d0001046d0302550301c9410001c10300090184c4103078003561025040d038080c04582030342c1d0711181e440080c03880781456400010810038110354a40005030521aa180c06020040c403011031040d8490b401192420007101c80014001a00b50001c9620010007601401408100140c1e1402071381c10145442116031000f03000301e1900d03545440402400c008840c1d10b009094103007143c5800d032001c2c401d903042a4140b0071b10a00410050f65003420070b03644600308107800b2134043d003a107204811110180c490700500e8012a00500e0b40d05a000a421264030300071407183e8100c0350410b0600c07100d07102c28003805801100422017840342805000005c5e105610a103030061520f45d882c2c0f00ea80c40d80c5002c2d1102c180b25000d000c07250f000d51901c10f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 79009336 1250 79008086 79008089
    0x30412050c04051302130b0607060b210c0105070201031806060303110601081b01050702030607081b040b030106270f0306061706041209051302030f07050708071106070f0b06040501 79
    0x81d02e0801107810452110200c1c2d250131000244180c0301d031410300d038035804c0da030304400b9030310a000d861103032070798540e1a0020240c55900c00060090403024950205865000f90350741c11000b980029000e5517201e0b0004403186c1c2d1108000b070b81859241c00b5010503241508400d404018028000080c40340c3c11481c008001c0445403c1d400201e0f800400180301414000c9916945030850074626405003c034440140e6087c000c03264040c0d0f260040208100400360407408892156a6000100040c20010720011a4902642c000ca4040000520040c09110f0140f4041c03c2c0302c1880c0340480100034410500441d1001858101482031003d1078020400c00282e4020000508101e1383e54812169408d2a040d98a010003131014112058a0089080c9140078041400c09084040d001500d010035002841e0043d62045e6410010103004000054034244a40d040d114101e41c0041c10528100441d1170b001c030340da0507034401140d200780c2c10000240055081410024003500c00c41d0100f141e864050208000c84805 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 79010586 1250 79009336 79009339
    0x12030306010f0c0503040b1b030703021b0109061d06040b0d0b041805030a03110d020408010911010f020703030c0c180b01090501020601050a03080c0705120304091b090b0d0e030412050c 81
    0x46540100000c0c00441a1000e40307503804109902d4110752500340030348000248230798040307000c00100b060a2540c0440e134448840c1c0386d00c40b4030075070500c01c200450380d01b9030f00d206810009400003000d6a61380711035030188104082c0101200e083c2a250400e07100141d03c0702022000300c5980713124420f46d80c18540503048940b1900c80c105000c42c6841d4440c00c3d12446010b0b4110200b5544c1c1d0380c2e2440d6a01507070b040d10007007a8400c078110f4450351200381e041d00034661890b0568007007010250079480340d8412070520303115440355409040a10324554040e50559180b4408545000c0908004039050300d90b05210b1801028035031005c10320901c502e002600200a80d00000d0464000a00512050b2a48005901201e0b0702000f00c40da02c0d241c0605881c1405041e811480c1d0207074000445145802c2d000001d08141c1c3e0281c2ca0030840c107002400d01003c98510a0f15400200300540820048805104041c2018209484022502e40302800300700d411a80070350012144504881c2c00740050084c01c10240610050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 79011836 1250 79010586 79010597
    0x6060103150902031905010602030a0806031b01050f07050a030c0b07020106060905010f14071b0603020309150901090f03020619180b060316091413150b0f12030306010f 74
    0x40d000400c03100341c01039000d208125070f000000300b44401200c6120080505030301004100550711000004c0d16a44150500304c0001d00c0c590200d41645404607200100c4015005a584441412801520283c1103031090a00018040c4004400302d1000d106031488a48250b8035890b0250b030a182c668402c6401802002c00c40e0b24001082c4482034000c440481511401d003402d540003003002e1401c40c0d5802c82400305002000c0003140780010862a4041c5d440000e880795008c14840d5103a0304100d04a0204549448080d40842010351001032505581d9400900c614008030b10002181c41352411240d03100e03400c030016408001048007606d07110b2880a072550700c03004103125904813600866140c000a050203054408800b002c50b01642d000c110b410544243e1010f160a41c0b0780c0c1c0c9540d45d0081103102e4803142007080704000501078420390403814015543c4906a202c56001806182000b0195020a43d030461018003840344d10381d64444031501c0d00f824960081d0f50b217203440e40004000b0844d4103a50400e008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 79013086 1250 79011836 79011851
    0x80606300106180213140d05070905010503010b1503041b0506190801080a0302120a031b090306140f15040b04020c06010302031204030209180102070c030f03020601060915080c0702100f0206060103 86
    0x3503500022100b1981c002d2071200e124000180060341005030103100030418894031b02e0008ac41010b5802c128100c403000c82c000c011040c0200c040c44501a12260140759120701000010005406106164000609141341484907a229408a141540700410030300d1292460550340300810b920036a2240540b881101502c041d10b00c99801940d6203101400f0301c20290000301d0405103481c0319620400003542000c00c03903002d40b0219540502800218081540c0803800c01401c00300e40c1401088280c040c0c00c2114184000d50769a100d0706881c100d01981e05d03544180c680286c882580d43c2d80c0090041d03042c1c10b002601141d45980b040528000b9980d81c0701007405400d00040004d40d98550b006d5503c844c258001404900000014900900c242203000304034840c640400b106014030000c0441c102c5100b5004c40f10f060742c8030603064550445500c03884000c2510759905012281c4503030f01c4644c002d416810326505100745035001034203800e0411081000108103500ca1072070f8642c10080190010021700341005943c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 79014336 1250 79013086 79013107
    0x10f050a0216080d0b18160f050d0903020703082a060c030610020a020901091d07080d030b04110f120c0a02030a0f020a0f08040f0801060806063001061802 68
    0x240c0400b00d0103054050701240c40048242d0035000122410b400070101130900d180e0400c90b0107400003d9507807115407044140c0f0700500500131040c54803001e8558031542d0400700034064140241c100140200c0440c06502070000000e00140051700d4402c0d003c1d80d00100003d0300b0b20040c0454603000f0851140d6a00200910100c0045034089a40100c000c0c1c8251003504854182603103084c140c00d01c02508940e01c1c0b000007070a15801d42c824004040b40d4240340310f49003d54400566555001e0181100c2a00003100c82001640654028008903401410124005080242082c1c081d0440b851051086200241c2001c201d005011503030743c0190354503d01d60402d000d000000355207001e24613448051003170b041a1001018001c001c22005240d01200100011800740341550a5401902c900c0c070400c15180008540c800040c000e0b0001c1d90301c4c0000030031160f035420b410049070701e01a00c491a508000001c031600d8051012402840f03030140e203000070036458a842c40d00441c44050618580c03800c0d10500c02210301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 79015586 1250 79014336 79014367
    0x10f0302070b0406051012060f050708060117090c040207080417190615080d030605030705030705030604060c0c050d020a0b0a050c07030c0201201c0504030308010b0a031b02010f050a02 81
    0x1580020b0000b07a646e80b03a100094010a0325040b003016030403000306840c10810b5a070444001d81c0041c0d003003401641c98000c0155001c400c01e40369140450462100c0302c080f0b03502d100a503688000d040f01103658054405010500302d81c4030000a40c0d2110700007c044c000300149070b1003189054012b0004100d24403040000701d4450160f070700000c10898894030041e508012800e9181c015045405c103440407650713001009402041503104046c00380c090342c1000105440d02140c00c00854401034060a2640e0304d0317030b403450010211481010140840005c1500120314108003410046a094000b0191402e580c14030001d45040248080fa0417400d08040003107003690b550540b404d40c1e9060800c184c6401091005131165558030b40461807001801c0700c07400d110a00000c41d00f0042e03240d0080d207910562504e0701125948100e02020b4003050f0040010440c0c0780ba040002c0072600d81500e070001e842241e201603072900340302c905501c100503915901c18103808045442240d8002c4181d8200314580504082e14300c0b41e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 79016836 1250 79015586 79015591
    0xe030903030d0b03030405040203130c05030f0307030e030f0a0f060e030f090603040f02040f0f0608010e0c01080702120301030828080606070602090a08010c11010209011403060619020606010f0302070b 88
    0x4103440780d20000c3d00d41c03810000d46000d0100100150b46a203060000b120004015100a40d18110b0303012000504e4103000c170b4030700c400010202c041c3d0320700049034a05840c03030400c3c078621a41602c1116160320740c5481c203200c202c101500c60300f0f1404400c3ca20f42030800941e5490041000329410800420244a000c82e0864030342d07110070f17a40f40d80c0340c1c1d40f01d040000c0410803c0b24040c1d00181070942100d201e541a5100300f1300710280600800109403115611400c840d010745d1501c0443d401a8200e0041d580140341c11350340030300e07248120343c4000c0e090402921590401c2e88116204800400c0c4d5500c2210400c070064098060b500190746071902855009080c0f50000c6d206e1402240001901e105002080e0112007e154003c0e080d403c40b00e550f040424003c00e100301d8038000041c0d03a00c0302000307004418003c4031500c4805079603500e2085003820645070f5aa02c007414081c0d000c1020004411170750381035245201056001e0300507151a10b07200c000541207840070409001018810404440028280b03040c0d141c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 79018086 1250 79016836 79016857
    0x305090c0904060e0109060e160b09040203041401090b0402040b032409250303170c071205070f111f0210020f070530030f130201020304150504090e03090303 69
    0x450646443c00e0000c000c1003004c001e2000c0b5400c001c00442803100b03581200e1060341944c0704450030a81e40c1c0e4100d24040700030b80503100041000300f05642d00e82c505034002d19000307409400084103201000400c1801c48000507070864110030000708104c01d5140920070868501c5090340a44002c2c240030310856001c01c00e100084440c80e0591001c074026507010024110110314501d00b8903180a070f49408490720200b20710049001588044003c2c0f080b00000c04558010700003001c54904206090799220744020074080f04004004050084001040088608080c00d9001d4615044005020414094400c4001000c0c220080002c0d848950b1036500090452061121500040c3c80e906000000c030264420880090b0141c0305107060780c03d51500c5c080003181400e0300710f5901500745075004a26049030000304e4070f20a0072000280002d1810005500c0d07560040e10501c140c034501600d5110542020700191017400000304042418002407000344a40d0401c204842c0003582070894120000303640f8401c2c0704020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 79019336 1250 79018086 79018099
    0x30c050a0b16230a0c09061203030924020a0e04020f07030e030a060509060106090504060e07080a060b0c07140a030c05011803050303070e0f01030903020c0f06120108010c0206070305090c 82
    0x8030501400f003048007201e0842c404000780c0244a80d0500f955004080401c0d2500101518001403d00c2d003880b03000120f80c210000e111280c45152000c4d0020001c19a098402c0c89215085440081c2e102450f5076050022590058480d010090b00900d190303080c420a5005903c10890b9410104526003583d044c00d5151402c0d0381130010110219090681c0e100e0014038060419003442454440460715505a071a41c2e9940158560b03500e04001c1580c00030320402885201d990042642c540c442d51200e1f40c4541c5110003c6400c9540c1e001441591f448078244061a41000505110761640c1644424007280c089810600c0130f415600c8031350144400c0c1c805c42d03040c0701c88404400c071804200724a0350021904001030303a80f00c3c03030000e00c050002d01c6180d40d0b05114150b035491400d207645c002c0c131540c20000e0700760340144a140e0f081d10910250701c1310a000543d202c1c10134401200130291811605005e00780c4031001054005180502030f150590251841e000c0c50f05000c20040c030090001070709404c094045808 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 79020586 1250 79019336 79019377
    0x20120030115050d020c03070201170c0d020a0e0d030302041e0506030c031b0c011401080f0c060c0109020a03080909220605060f2709070e011415040609030c050a0b 72
    0x1600c3d02c0c800d0b4501803d00c10300110344218030000c040007400c0300038004e03200c0340d15041c641a0307140d40201007207411807041841400040240d03086c0d940a00324000c01030400402a52401e00001ea140c0b100c0f6000300c0000750000b4060050150050581c40c455056401c10300219050800007940c501004040d08c018075030200018061a00c2d00b4159900340003601c00080e034800d1a8159103001c1c01030380d003c0090f640b0305407000040d03101c0c000032001e4504d0901030142c140d41c202841040b120354809d0040641541d220b00703482c0050303640c400205004520401d01c3c41e91303c035140c0c418132030500401400c09144041400740c188003074252041089026500c00c500107043d644100003d0030304104250110340202007940d921808084000342020500d01c0c00c24828003035a0b852889681d22081402201041c10140b0010800200e41c8802e0f540c4140700100b50412060b03e1042988543d0050341c003100000d010078030100180818440000060702047d1600100c5500300501003131340380304100c0b1174103854501c10031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 79021836 1250 79020586 79020629
    0x10c03120203070c0c080d091a03041b09020d0e0105070908030d020d0216050a03031b021f060305011b0f09052b020913030806040b0a1e080303160201200301 69
    0x40b100344e00c4d41d1141e080301126403104003240d6200c0c20302e58a80082030090401240341403940c00c04c2c0540c080001c07042032441d40c55a4840c0c251084d018000c05000c414130201052452450015000c6645036030000503a140fa4940f803d820f42e1009009442800701038001031155150110844003002c001e04000744e5241c0d52466503400920030b00b0100e079240070062540304200040403e1b040200c50181d90248003000300704954240c1011fa1040c910050f900c1089c00d41e0000c0307882e004090708604070400010380141d5075110f26094400006455030f280083d681c2034180c032074202c1400c00d00000c02e4a01007e1a90420011506450400304c051801c036480d1a40f5180c5115200c44903524168090828020b40c100000c0d0070f00c3c0307808855011408a03a44800042490401740701c0c41c010820002d08442d0010701d48940c6030b05e00d5441c80e48100c031890b1000c201042414003040114040d1100e11501c038165466428020b085070506508140007c41d248000011840c2281c20341c2e0560b046505041021001c454 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 79023086 1250 79021836 79021847
    0x2060117030915091e130902040b0a0f0e010e070206070507050327040b0405040506040206091c0b0a0f0b030709020f0d1a0306132a030206120114010c0312020307 71
    0x4601c1580303c0c11894080c0c003010500000b9000003241915035041020035900310603013942803000e240350404400101d416070f64086401c44840e641c0054400901c0103841e502164422450750400c4010315442e1000300007034114013024a00601c0300c12003421190400d50300c020b40b1141d014009000308007002c0345401c2400000c0c011280c54010200500b2514002c04c00000c2111381030300a1140b0603490a507140009052074003600d482a98041d0281c14260303a40d03401c004031030300100c04003500907900e10320000190312925090000c0d14040e151241061070688103903400d542100d00e07842500c0381032441c41c0c5581d890000310403043d01c3c4041805625402103009035440c80c02510b4100b40020b05041032010100c1600744500030310304013501035a1090352010a48021800010f100130300000049203580b0442044103c0341000c00324881d84a4a51a0381e40c0024040e41c1049107a2040d03540c00c840108241401e04079503c000072401e00708040ea003c4182c40c0601840443c00007030704603540000015400d68409c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 79024336 1250 79023086 79023097
    0x4060c03050d020307020607030606170a050c04030b0405010504050d0302090315040302010e010f0b0f0103110d0209030309060706050601120b010e060f1213030305060a1202040b1f020a020114030105010206011703 93
    0x2442c04640f00e103080c2c43c00a594550a540c07180119190181c086a000d100300c11240000d2100c070722000f000d44542d44501c00401c0028054942c0c03040510011000600b40c1d0005401103009100120300d80c00c1900380741d41811a03030300301c61043c10f1042100c0b810760780b004a030080715480090013107e25179440341800d9024000401840c0d615511300030342d11000b22400c0d8030810b4a800280ca106070b80210a000640444402c100d81c41080d550038050baa4111030150000c014841001d82a2070810704a2400302e1402e41203408200c406a8039075080240c1564844154801c0c074078003d801740301d00007540001a000241850016001e8240000c100601d1088902110ba9410501071a48030a1074004603407003250a50080c11800030f030402011a5030b0345042000c40085c0d4040000e0310720040300c50b90070070009020000d8541d0b0040d0300400c61645120070700201498901d240d40281641201d01e2000400c118003082c400c4505110520040c441a60700145c014155107441c0011003220300c0111040e440c60142 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 79025586 1250 79024336 79024357
    0xe0d03120f05070c0b060d0b0606031003051501090f0506010e0f010c0f14060f01060801090c03090c0f140102010207080307030203092503151a040209010918050411010206040804060c0305 82
    0x50406025206501c2211004c0321409203590321410b031203400c100280070306c510401401801804e0041045440c0880003140c00c249840c592090407596940c400d420300d0300da41076044e4000c00c80300c010040a4075502078501950304601080101d803400b400041d0000040403001030003a0480901e4040c81e90080080d400111307004600421010340610345034646d07207441c0401ea030680c06610081203186c0f0303032460302034140c0d005a1143c03403050782008004002070440034a0729082540301c8050328049400082c100c0b0250007a9401260411308159201c84040503401907281103a104108680115008030305584d0051914030780035940c2e4440140152401c0c0303541d0054614100100d0b15110160344244001e0112442640c070b840d03004130592080d9080f69002000d200c0c215000d0900c1c1d01d0985000e500428010905041403030603103450b0f81511004001101c40c0c04942c031b07690f40500081c4400043d01d80d844001c2407009181d40d2800356203418840c000c034800c13001842140400070040501a0041c1c0d02005072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 79026836 1250 79025586 79025591
    0x80c0d061e11040501020d0807140304020103140f060109150815040204050a0602010902030c0d110103050709150e0f0307031a13020402070b04060608030c072927010e0d03120f 77
    0x400c44000c2c81544140302d510f0240c4141000914a40d0140c052544a0103640c0c854a164080c000c03106d40ba19840103100324101a92131302d1f85400c410700b00c0b8155000300c4c0c01d04400200e515080002502e00c51094200040d6200aa2449103203075501c440302c1948209451184140d40c000c0783c0108000c0e0007550021507200c0140d48000c6082681541b018425034022012105038900050500040c050302a40240164402096180b900d50080d0080c0d600300f0703990310300003203d1035940f92a0900b0102140301480040d03c0e40e9041c03c2140b40c10011300102c48001c4001e00030851640e924000c0c5052125185243c481068001951100c0d2101c98241000e4000d04107550710101ca10780100c5440c1e00b04c8040b036007a8a44000440c800a001042d00c0b654000d9400078500c003800c0c80c2500340301c2005200c1781340003000000c604104100c0084060010000000c075814130003091482071503d040101030003503040002310480d0240940d102e950010f02943c160824141d86041640d081020b400c2138011680e0b03d030b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 79028086 1250 79026836 79026851
    0x905030f03040b07030b06121807030606081f0204050604030212010b030102030406090b070206040209150d050d0309030f020309010c0308040503090901030b01170c0a03061107050604030f09080c0d061e 88
    0x10312000958400c80c1319075020056401d114040180602070141c42401d050340d0400029540043e0700314540d540000c150445902c40e0780c170365803402640d1054011019581044820107802d5401c07002d440012842d421065040c0b60a10f804150070f8061440080d1080d442c52a81c0441080c003075100d41c4429002400a542d03a1074541041c0c80903002910045921002d00c03030016110350700c04903196000350340c02492852140c44110749a20a00c098501c4181d00490358400040040c00400c80c1403950b880ca520041101c03080d03402c1c050089841200f552056410401205e45682e034010710160350994107041482d06030322241040d034518060030513000c1e04410b4007000401404001040c0c44d041307803442c0d41102c8281a2a94a16464288507840e05405c01070901c0d0a0000542c80d40020b401e000e2140409401c0480f40c1d1901d5141000644041e80400c00c000e1070500c405500c035504c0d501911081c0010101c00107074001003611000103000140c005070b92035071485041541003050110481840d0028070101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 79029336 1250 79028086 79028093
    0x204060503071205060a0308031801140906060a03030905040507030e0619050907030b0f1305030304150605060a0203180a09020f0322080415051b1507050316030905030f0304 76
    0x340c1c001e03615100815008080c01c1c00101c0da500480313202d07107400781086000c01e103140d80701c1034250006052608504042d2580c5a42d4280910552182e6101602400103505041e60800d0401c1c8014100d07038003440880c0424000300707422144420498070103603000160f0303541d01ca0084005100741c540740001406408184162041036070b008a40803400514100015121706000c6a83e40d038242c80010003450440300010440021400701d15802242c3c15104c01d0528426518141940d1040710112407a451160b94441640980d100d08406008140e480030700e445803207000690390340180290880030610700c4403c0b440c56240d540e83c0034000c12044009640341d0200c070540200c5074000b101c141154117883c1c0c23401c03807490816407414101c85800c0350b2400e00d81414004000d889803000728801040c00410403131000d448020082541c0310b042c1685c042c0c41c48404070705800c0c15013100503019604200c07082c4140501051541d20054121900b414001494000c41c0b5006007503019410780900255000700801060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 79030586 1250 79029336 79029347
    0x70509070818030c0c15090402160506010501020619020c010e060108010c02061014060d110d020a110f0705011b06050702060610090b0a0302071e03030204060216081507050409020406 80
    0x51184540402500c0380c001c5010b990300d0085a0031501c00c0d6124014195440c14086541c0c2a01500171000c0c0740340c062600301041c00c0c1e070301c0032091103a00d010011250041c000d051180d6030140c07100344080c0495040040b007502d205040c0c00c91304032129070b00040c1001c810002754408581204031354142c8050b0b60356541024000d04007500c0080141c011407000800c002d80000400d016124840d21400350002c00c00140300f040c0c0c000400d00d9070300607030700c0038124100700c0c2e078602074a02c0741c42e00c081c0942c3e91b215003079005001d2840010078840729801b52004588100c0d01207615002e40300c00380f820411002c400104001c9411460780050269880c150901c1541070740401d1480c4201400d4907249040f00060740c04940040381d80c400d080c220401481070307030800b41c82034000f84020b40c010a1200d8a50108034603503600380c1046042140820340c00a001c10140380c060101c002e010401710440441d00e40703444d408640380d040f20401e509640404500040742c4901400c292400741c6200d203011500e4940380d0802805 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 79031836 1250 79030586 79030591
    0x5011403010605090621030d02030103060b010905010e1e0406260105070f0203030f0c070203010e0705090c0403081b03190e030601091b080402042306130b03030a0c02030705090708 79
    0x2075007004070100b090300b49248003a0041e140600500ea444001c100503030590340201d0030000d041c1c003040100f6840c0b901103001a41c00707503006407000100b1402580000d0700070b400c00c0e484075040c04980001001150b440b420001152950400b5440b06170a075030303000900030401d0341c121000d041c08903c9420b802d0289140d4008829603000002c101c1030b1200002a00c50030280415400140d004200003600c0125104500d60488542c80036a41841e20300c0d400079007519400d0002403200d501002c8200001e01e448131065400600c82c06c54240741c00c0c00c58890316102e21900e41c80d400c00458980ca1100f076440200121080800100d40c52410301140f84001003254410341a00d510a120b10000452000b01354030034406092a010001c0708160400007007500d122340020b0003607170310543c1c8403090104c12020100303807444c84a80c140300d4900c1d0700d050001c000300303248003c002500c0b03039103003400b01e00305a14000308a03104504107040802d1042c0300c910000389040b0013504000d0304281c0103018402201e402820307090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 79033086 1250 79031836 79031839
    0xd0804180501050f0301140426030103080703021e151e010e09100510050f120d0207060801120c06050711060f1b0f06130303020c120903070807030b0a180204050114 72
    0x4d8001110b02c2014281c0d60b80402c061010142c600115001070540402c880c40c11b840c3d030a903000b03a2035000030141e2098000740d005a50b640800580e403c00c042c0c0c144400c1c083c42c0a880e00302d00c651100045031a1b40e41c0301192035004400b80700004245107820070400f80c5070b10301c2404840e40c0380703607150690362b40c07508000e40720100c0e11b2180142070801803003140205c03442810402d404400507031900c42000146030b03241c1d24840d0454500207020000d05400e0003450740c40422034000702079003454844002c240c02416030000b81005c01d040c541c0c0000a01c5168154100ca1035458140e0300c603080f9080a5000010410340d00380e00660010b041c10103845588080d004548500c0c51748115400f42042150312441548040c018540080001420480c1e14441010300e9502916005084c805482d4a8a1412003140c4500401c0607001c1081312141c0380c00c00401d006000001d01401406240d0342c0c41030110740005e0186000c9545450700300d820100b41d011601e51141c5c00610030300103075a440d101a000c401c80000d00c03030f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 79034336 1250 79033086 79033099
    0xc140342030f01020f1801030e101b0c020a09050702030f0a020a120c0203060106030f11030916151205070c1b090513050a110d0b0103030504150318020d080418050105 73
    0x1002500da042c070a917086451035500141c5041c41c80440c001601d0b1116440505140d40c2d0800180d01e0182000544c4000030724240000300d901e180a085a00005450f500070b08100c40906408016201d082c1e1040480e4007040011829844119099041d4003826400100c0d9400c042000306183e07500207048405076006c3d240c058018104900700700d4443c100484c4c040d42651010004210f198465071280f00c01c48065840040e40e807400c4802c100b610f50081d60b42102c0b642c0030680d52107600c0c0c0b00d0134140307008200398440403110f891f00081c080d0000c1001032001800a40e140000f4200ea4001c40743e6101090388000007500501300a101100c403402540210b60105182100107604941c2130703100244600d4001300140481141652941003554171301c125560001000c0c074880b00000c41c44005c3c603005e0b40c484d4030b070951510300300840400e0703452600d40d504040504040c0541209401c403c1c1071203419070142ca00080b141d419091140c0036100320f07405044004a03036a44110b045d8480e900480c16203404030307001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 79035586 1250 79034336 79034353
    0x3130b280507021e0115080c03010605010201051e1302090103080307030b150421020a060c0308070903020901060c051203090a060b0a0b0a050705010908030103060c030c14034203 78
    0x4480071a00d0880e81400582e200e28002114000800f036902245031440c0c0010481010714a1030038441d4041d948031072003d138880c46e42c1100341e103020301806024280c02c1c0300800092074508030310107442a0600f480140340b000c0101250b481442002c6013060150040c104e1815560340e80340840040c2d00494090f0002881c2640c44900c600d0600095020ba200008200303040c181003107010007507200e170b10840186102c00000040016103490158000030300a07611303000e00030505401d001d41114002010700080182c03000e8140016074440b81101e0540303103546000400104640b0304a858084201081214800f001c000c01201c00340020302d0040c454820081445003203640f10034032003481564021110480000c7c400311080c1445140500321103400390700042600c072102d03191140d241e442a002039620a480b60344142440350140900f681c003095038941034001c81c030928a60b000380e02001c1c12408141d100080ca0090300180302e01c2c29001c40f2080c0804031101e41e003040754210b1040c902000316000b4010000c0c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 79036836 1250 79035586 79035661
    0x1203070318030f0e0604030212070515040320011b0b1501020609070b030408040906090b0411030609060907090f0b0919080c060d0603060c0e040e0d050f03130b 70
    0x281e40d1a000e526403510003100b8a840400e48070020340d902c04982000042c480000986e0b1000301c0c680d001c0282c140509100b90801060144181c82c0019003442c0c440304020410011f1500300c03c0c1c0950091854040c00034055440049074040404014201c03804100040358090018252100c2d010382c0c400f009030f24075504031200698613450204c07800c40150704414801c20507145250000c0d9031041c8144006885d00f5210001c4504680042e0481d2a0840d03071502a484503040c5403241b2803c801034842007a0031803074102c0c0001c0941c08000c007194014065840411401c601410000001c1c054a103d03440d03420780c0301c9001a004d40c115519440c4a9016000780301c0c50140141507207001da94915014050003259041401110307800010100f80c06aa14240000440c1d078078403800c80440601d54403040800340c000b0412040d41d00715806050180c01500c9510205904407048804498552492035201d54405004034031880b0001000b070040c600700340070420f0141c014600c1400d40c840c6010f8040c1e40424040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 79038086 1250 79036836 79036871
    0x10050301050a140414030c0f0f0105070516030f14160611090114070c0e09010209180112020d02060d02040303020a0309090c090306090606090f0212220b0405030c12030703 75
    0x144241030000e24000302d40400da0642020420100170b8007120314064943c0c84c2c40c1d10301010070b5241d410641040003414284142130040f00c5d080140361400e141030a503401180100b100d2400300c010240000ca0300c00c0b06010340030303840d00c414031400141d140b502c5511281e100b00b9006030300c20007182c0540c54000345a452074040825580300e14010780d20903144001c0c96110380b030aa401610140e070012400100085c11003082d01c5518490310034007001589580c0d00009001001c040401c81508217038546005200c11a8170980b488031268040710220b030b420410380007041e039501c01c403540e101c0c01500000b808401d2540003d0340b1041c0e18400d658440700141c0c2c3e0340d103200444140303125940006a2481c1d0410128100f44c0000c140c40f0f01444000030790a0750b41e2402030407107481071001d201440e00421403d0f041e1100d1130f8a580e00004841d200020001038800c18020300d0311038030005002240100110301441401c1085e240a0248103049406d404005000c0ca4000e1700220381d000002801c0c08824180b010900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 79039336 1250 79038086 79038101
    0x3050609040506061012020d0618090b06040213030203030f0405011101090b0601031a03150709140f1005040f0e010e09150612010b0312030f1003080702060a0e040510050301050a 78
    0x908510307250001000417241a0340030250401541000921801016100600e40007007aa80c2c001012460101c0003900b60b01580c1503c0081403818605030007050121041650120f07003100c0050362450450600445001e007604081d401d4440030590038112440b0313000a005840090302c411044003600ec114500745c80a004008015980c1000824581e50080d0055076002000e0490f0102403801070001c02d14102501042458861441003482112604002074101502078241c3e440e00c21000350b0081441c00900c00001c50003840c0340440703403450300e120340f003528007500c02c8200c1365109507a260751a0306034100a000b03124003040f494004c5152a180010403000c16440382c1c042d441c540d80d510f81000035120710040c9445065403506801d54050758140200a07082c01d0b02c1304001c0c1c03681044106600300160051580c4030212030483c5c140301080c5c208060711002c0741c0c1118060381e603011184003211080e400d0240e9070b4001d806c010030b00c04909190a1401d05131002a4001c005c6035480030800010303074400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 79040586 1250 79039336 79039343
    0x12110a03020c041a090f0103060b0418110a030803010602030c01060b040312030e0f03041e1706010b0c01060509090a11100509090c0903060c041a0306090c03150307080a030305060904 80
    0x411804071181404c0c0c00140007076282c1c2e000c2c00d894264410100e281035104507200f40c00140094010300400020380305e00c03544044180c8041150801c4001c3d20380d40301101c1c59001c1c007200c0c0a0715250543da40c4104011011b141e2114800e03484e5651900b010b5038a4008011908095080000200303c03004180142d404132500203881c0708000c04000b2064008040c0d2420001440c015100e1142148a0410080c0000c242003802c03040b03903032241240c455078082250459a2000308040c000f4464820020701c6a05690382c515a41e940d585c2800d14060042200c6c0d40a9034000d46490104030842c200402c1101e111402000348410b0001842c080002500505000e4008200240070640180c1855040d0700ea201c034455000314505107030715000030b00d000c0c812100c4803991100003505000c0c0041e0054030400410804c03025074114145100016030308030000701b400f1055100800000d8400716040142ca50b0307120094165060300352140e09503500e500e070003207003580440e042c00c000c00c80c50b007440c170007642c402c941 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 79041836 1250 79040586 79040593
    0x105060319050907030507060c03090f080303010b280c1203200c030c0102030f0412020705060f0d180c14030601050307030305030c12150a05060702010f0806060705010912110a0302 79
    0x341d005003000070480a40400340700d1007040c1000c4000f031020000301000c5c215680361810924000c2c500104200c1d05904030300000ca05041007045050342c00410f03207040d9203400044a031540014159803d40c48940328924050140d2191104a007940000200541c14001c80d4009544c0030b4081058013503d04481641700789a01c011100207080a80c0c1002c3c11003041e10074143c3e4541000c1102c020309981050754160300d80b24009003070004000c01c030342204c6464002400a04002c601d44000074003240901c03219400c0c000350000b0000340301d15407071b800700f40410316000e00141c14002e1404c000c03001c0b080b44e0180d40710100d0322403d403140500e000105241280d43c0100100380f140e0840d5000c407842e400142c121b440304541440388444100062484c5441000105641d500c2d240c4c5040c204044880c1d154000b40c01202c0c10041e4602603603200021a08290640c145002c0079207400000c070701d1a1066030405402d035441d0a24520802c06444e0307110040508039a0740d0317124000005061504c0d00194100140542d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 79043086 1250 79041836 79041871
    0x20301210302120a02011103090d260103020409020607020303031503010c020a020f100201020906040315141312110a050102040e070905030304061407060627020405030c010e040912020706020601050603 88
    0x12801c50040484120768800451804121f1000011036081502d10364a1600100d0056010340d40c00b00c0301419000011200130f421800c04100070303a1051381808064001d98444260600750744555040343c0c041540501160303039a242075080081c5041050305031038440d500345020111103034400580700c60351a400900207030b03001ca0b82c07504002c2295008900d410955400b0310005259a80c0e9201a00046020312485c9071039281c806001411220300c94001e072030076031044d001c7c09000f4000044610141c0d90241d040211285032050079606000d0070700004c60340d4811003604404012064000d03004507103494507125400c1d1251081541e040a40380181c41d0168401d01007000054071819080c02007440c0350b54110300d0a15140c85003015030f51030b50004284425882c1c582c1d0488250000e0760340c40310a44001c04c40c1840e0408002a8035105a44c01c064100403c40c0c23400c15241d80d89038450004141c2c401c21020949111580281d207500d414403c28015009da1760000841e03051030f0341124454407690000c0da40c42d8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 79044336 1250 79043086 79043113
    0x24030309011209060f090308090706170109330e0a020406050a26010308121006051b15090105010302031005071b08070b01030c0f140901060806120303010603020301210302 75
    0xc004000b000c1e90380a07150030320361000c1c54951007000c2c1618080d03a08c1e1040c5190048610b46003045039071001d010842d41100950043d516150500e054410710752010030f6064805c91488039010010f03031004090a01c0a2651404e404240c05001c1181c10600310300070245c1e1030f04941c1049000d18412500454801c002001801d80b2a0903c481c2241144004050440c0310800700e507192a03098004995103080054418820391001c542d2503804070110170000091800c0c640001e042c0e00a01c02d004e11800c0c0703010050b400621091100701c2c4828a04828100c16240240c0524043c02e401e00c0207a00901440003280c22000035030203030600c900c1494907a82c2e01407540980000c55409218400c2d14051000c0c04200006160660f019000310b0080059040550500740f00702c5c1d480038a03030f02c800595584d400600c03040d502d070036030038504483d00740c20651a01e55407603000c07034296880440301e0b0009010020000c00c0ba142c0541c003842c10395684a80407228013680104240d030181103200042c1c05a0b0141d4907150340d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 79045586 1250 79044336 79044341
    0x309070501080c1b1c020c09010504090203100e101505190f0b07030905031006050307320f0d06020c01050a05010b070b09190614100614071a240303090112 68
    0x110800d08044500d203400c005c890039040c018540500c0010307000220141030078500021031030301408003207c0401038988030f82d00180d903482c21b00d0181c0d5085500c1e0541510b46803801c1c09020068451b81c54288005491403407140440c07420380c05018401d9010404c1164200052080c000941e800c0f00d142c030b031400d8204580c2015542110740100c04001442d8000324840e1020b218459a204421901166040c00d0004160a181c12a00611038103082030080340060100e00c182c50600500034401c0d601070b8020040420b0f80070590b544540d8001828072130f101c08100b110381c0200480641e41e4000c010a803200740850b01540c00c284145250620184503200c08203a81566041d0000080e400304c40700c4542d1052185115002c0e41c0003605c100d580d03111488050003601c902d2546c0b20a040390302244040c2441005006601d8059040306d20a8020401c2c404001d1290030001545960401d405060710b09080d2420303e80c4005219440200e00300c802300c440e41e04000040e1080141e050315840d42203055031255100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 79046836 1250 79045586 79045627
    0x180213030303110720090736120302031308160312030b0a080a060b030c0325121104200306010309020f04110a14030103030f0e03100e030309070501080c 67
    0x15100e004105007000207440b05c8150740140100705409894180c80c0c0c00b0000308643c010451400d020021040032402800d4601c1900500590218100d13447c49801c408240402203812113042c601e0b1071100f5400741038002014240b2104c51003030b140001d81d00c400315603454000541c0b5280b48000c03680400d00c0020031002c0d0003015001246800150001c5101c0040c0d81b0302c565074001c00c0c29070809040d4074103001c1140500c981125003a8020310b50400000080f950f9807040e6443e101504111980e8051506a40410750000707001a00f84809410068200803904030f10b1920800c0c4168a0300c01492102188000170344d12075103403501c2c102d0941e502c4200540c0a018038031012a40131225902d80c8a080e5a20720425102c12084074505444080e2207070081c02281c0422141d840ad58010b000400001e80d011310750004501862500d18419003818022030b1624079400144450340d81401c201c80c11809000002c0c52082030003408a8090550310700c015521000266100300340042c0030084800c020415101171203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 79048086 1250 79046836 79046861
    0x1d010f03180804080106050613090504050f100f1821051e04031205030f010501030b040b0405040303091104090302070e06030a05030c0a0209010e0c070609032304180213030303 77
    0x101c120031021804030403a0154011684010085003c2c40750700403d1283c00050103050721200e14020b50040c1c0540d50070014440c6103106038445e4002010030809020140480d40c91800305c40200655901d5100035016070341005a00525101d000104c81358441e802d0700c00207070001d602072442a002c106062040451030203040502408024008141c1c807404440c0a40d00740442070307561642d04610700326601c1403c0c041100708000d810300510410751a800241c904480e02400c00003410080c25003c5405051083e20542d031144c9414208414035400d5044408414402d6030072001201c844020802144c0000c500a00164000c107001e212040710b01800a0700440020b003203a1214a040d07441a15683c84440098201d0700890400c4007107051491005000d411284640749052602c816205924007501001400c01034840d10001d0602d8081c80040c00300d5084200c070343c8c5501e0b08070011500280e019100380400031554030720010007042d40f84241d8a10b210314190b150017081c0796440413030192580840c00c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 79049336 1250 79048086 79048091
    0x3030b01110708060a06050102070501120905100f05190e1b03030c0313080f0304050105160c051905030609010504050c100302040f0608010302040c0c120311040902120906071d010f03 80
    0x40018160800820000f0858000203008a2800c40c0740b29055581039071000341594020745040c400307603070010800b00360462802e900181d40c01e005d040c544e1500c44620b01e00d42c04a45130030030306c50185240c0c0d046207205180728961503403424141c281e205e0881e044000a4885508222880b0303034400b215030801951040c0042c00c80e030410481c0c00845082da8400082e403043c103410090f040001d4902400102307000c8211030b014500306880c000029190303119403598051501851120b003802c000030f920440c40940005050520300400310007448006001c5405032504c80c2c4600e20002e83c03880c4050080520660b0300402070300000040038240188440d0042511003451f400303110110314840283c0009000700b28ad550b80361019450b41c01400102c51900c9203a00812200103203940209030031140114401070a850000340d907940103402c081007405a07800801130140001018110310071351900712802a03a44000307440554547c01c0702520215800303a40751518a5041c0da2040c0f0540c044c20681d5a044c100d0b0401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 79050586 1250 79049336 79049357
    0x506090d0f06020a05030402030d05070803040308190603030207050a0b13050f150a020c13230601031508010c030605090403090501081e09060108160e040602070c03172706030403030b01 81
    0x42d102603030000003000300092000300400040d4507040140800c11101410010316041e615101c40f0b14501c00148042c05201c46c07100403a40b81607941c7d050400004030901c0c20414644c6900d0025125911441844d208410a0b8400f141c07499130b83c0c0c00c450b10002404588150a0301c0d0400b030082c2954424400c0d984102c2c152440e02000e009440140007120b02503001e0610803800800700304c51421512202240185401841013585400d55400c0b1051180c83c1640d00c1d4540d04d0400403000b5101e15030b00364143d0242c01d400001e002d0f105401c803015041c100d407814015161a8014000b80040840c1c0142c009080d60200b00015401140750603041401591540011226252121086c07502903840003000d5020000406c40c554080c441d80100311043d01c1c4007603019203042000500180054409411244c2c0014008100700070f4010000007107602c0050b19800c0e0a02c520010038a4004200700c0d07015619084850218461401c14003102c1b07003001340114250b440ea40c504078014103c046071a4103112800b84c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 79051836 1250 79050586 79050593
    0xe01053105130207060501060503040b061e040f02120108030f2209021b161d0c0c01060b0304060f0209060706150e011e0512070302010f0210020a0c02030c0a0506090d0f 74
    0x14041082c02402009641c0d26031342d19042048035016030088080110a01c2440000b9091134031143d04028100c40c0c144003034103001d0380f0a007400e40003440c803640107203002042d5490000c40c0d005071a480b00034041c06c804d141c1e654004980c8a01c01d0304500b02001c801044a840d492608500b800c0c503030740322000480c49140e113442e50f100c1268054101c00303c0c3c01d140d04c1d807081f074013031000c1100c4000c07000d1040f40b01c0790b811301e000032200d48406040107070711000301c0003030014a1062400b400e0700c0d215a121002400220750f10500f6400076030050340c00b55007141c10500301840007002030084803104038001d4170f001d00d00603554031160010600d03c003000171042001800090341001d4a100240030305040103206404059161170b141c0380d6109039010600403504140305180540c0045680400c03241c0a0900e9100500c405400301c1c200b1200c0c07003e041100c4e00c007144040c5076680c42601400b0072031003907007251402000001004484103c40c8915a4040d4040060310000d08103019003d00c0c403440752100f041010034555 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 79053086 1250 79051836 79051849
    0x8060c072a09060905100812070203010207021903031803230c0907030203010512010510050103021312050c040e1903030b010c0206182706010302160b040b01060e01053105 75
    0x340a0b4001d42d803520000d0240d00020310519030420241003810307400d14a400201d6844000c04500c089201c000401d004055413400e40489a0080d40180750345840d510515441c0085a40e600094000039805103050f01420071056041c42582d400800c20100382141c48001103500c007003a000c02840380940901c0007020b0721043c004a00504080d100561030750f040105011090303c0c58100107a00740e052109000d0015100361070903045d10020f183c090382c0c1c0e06c8682c1c5042021000d6511551504c0d0304001810240075000c103546018035010ac4090001d1060f4a51070342c1c0c1d0f2035001d60b4115a80ca610060180064080da01c00d2004d1541070610541114080e00020740d690040d00e00039a0a00102031590704500c1c29080c0310300e04201d0308108030017140c07101c4031002951380f0050000d814140d0014403001c3c0031800c480d5503030301c84c2d81c000191100f0b46881d24203080c50010138494040801c0c08240244415805141134904400c00d28000502e5020112241c4a00350400b24103010184cad4210404103480e103605 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 79054336 1250 79053086 79053089
    0xb0c0f0316050c030d1e0614090601030e031803010c050304020306070807020f0706110d020604031407060f0207050102070203070501020601080307150b030303090d020c0d021804060f0507020c0103050108060c072a 93
    0x400b40024080782c422000346d401e40d40034008503900d03441d0010a000e0300b1340c0c0f0940b542c000b40054031600032a07a54440143e0007008a2000c886040c03001003125106004400005001e500d02500284269004901d00361464001514001d41c140c0002e0300054140b4841c0d6101c0d0f80c0700400f48100c5002000f4000c1007400c003000c070b40150000880451500c5140c903003c000400300c16040d0f200815503450161401445000c69881d80a100280014040c06102d1079401001c1c02640e03443c000c541c2c03250640b07041c2d4000c0d40070a008074000d0141800010b4071798004030340a4100c0d00000d0242d807810a06607a40c9034480ba20311040403403aa9900004141510100b014600c1403680c0001004402104071029140600318019a44251500503c1c1001a25000b0342c0c50740d9040309000c08601e54549280c4107003d45080c80c4c212240c20b00c1c0c402000121039000400a000042c01c5e241003089988030070f0b001d51203040854078480712110400443d000169074422003084000761000b178201160f010741500302c14000d60b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 79055586 1250 79054336 79054357
    0x20307030906151a040b0f0304050102040e100501030e060702280b04110114030c04060c08070f03091806030b0f04020120010504030806010c020d0b09100501030b040b0c0f0316050c03 80
    0x601c3c1d004c2c080c41c01c000e0219811240c000400509081c07404100180718829038540c082041c9010000c00d081080940586000d004d04da0240303011031403c5040c00010408034890540001d06282c01503041440202c0c00a000d2075a6501921001d14100c114250b039149401d8010031148059401c00c01081d802481c00e40217034801d04890300115003180006190783d0540080d0b502426041091201140c071490440c3c080761042d0400751103c007041d041c21540f81c021450b000d400c0c0c60820001c1e00030554041c10754810f554100d0440903c10001c203c451044507554040200ac3c0c44050000c101011030081049902510514005100c0c01941c640d91300080c444c40841c200383d07915442070008146d0010741803a4810400c0c07074001c0d0244115000244050744645000d0108060031010541011090200100d0b503c6403c0c801d022a5959141c80b0014440071201039550640003004621862030180c00c44105004a008007402d58649080001115603500500c00c03c2c40740400080308600c1060015080c850070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 79056836 1250 79055586 79055621
    0x4050c090a031118070219020a0305100903090b0702060702040b120f010912301b0c0203010c02070302060304060b0315040f06200d050606091f030f0207020604050103020307030906 79
    0x2e03003014410f40300c0d0380502d201c809428a40c05c00a8055000030207480200302908030110342c00660010030420340c81604040c18901400049241c281c5c0d942d040220040d101c1e0340d51800090761413128600070300480300d009520100c01c0280d5805460940c000040310400142a6108407802c0f20050b4542207a503880100565101c84201e400d0004804096502190b03506192950000d0b000340000c200da256203030a4003e8400c41005000300c070315541300c058085581400c0400c17403a41004064504000403008034840d41c2802c8540c5400d900c08034040044a81c050851804c64555903189030107422107500c0e1b2070b05403044501c41404c035440003503050300880c06203d9100c521456030031701c1c2c0203441c000142001650000d080346007100c210f8004641030000c4800000031951110300005019115403000541e0001c1c0038040c0040c281800c204400c011221a1000c00019240d003a1840c260300400300041d601c000240010009540250005c643c080c0d81c902d000156118165182e000712080000d91084103030707 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 79058086 1250 79056836 79056863
    0x100204060906080c1305090a090605010f0f0f0510050a0c020a030305030103020414090309041a150c0706030510170109060608030904060902030603060411121b101d04050c090a03 78
    0x3e401420706904451540c103841d24003044c400440745512035600c9414024520400080e00ca240e59a00aa2516601c6901803141e9651042e201d992084c0c1e03400303040c9111501c0b03040002e550507000d5102c1c1c11103102030544c400d0000c01e42c1c401d48072604415200402d010024400d48011b035521207410000e94883c3c1c4034103440c1c0d4158010720040755044d01d20081c4903091607090003c0c000c000000e035032080d00100c5011940d03015082ca9513200c15181e0005581000440c032a039611580001d0141c882c01c0c03254012603580315942d0b6000c9060310015a0040340d2007080c031105001383e0500f40302084480808000200381003070035640d102c04540c0164420509508003091421907450310340a404000c10142009600b9420040d00203510b403100600020070b5a28041092480754685030056014101041c06480d01c461502281240418100c100f01d442600300003180006907003c1c0000c1d41c0c06950308002000c0300c8401c1414000142006091001c56007418810001143d44424554010358402c001416104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 79059336 1250 79058086 79058099
    0xf0c070906091407020c0f0d08040902070614010f03060203040614040f0512070209060907031d0105010f0e070c03120b0d0507050315160f2006060906040510171002040609 75
    0x1108500f0a85160900f2042030100242d80051402c20b038142c21500529402e10303000000b501c0180b0314100910140001c9400281e004442d07010300381a90180038180101c2408120f10901d4003001d024a107400b5000001c01e00c081343c01c6501860b807192040300f0010301d0022015100c0394005049031700b101d0f140901148a4100b04080c0500e403948a150303000e09041000e1540000c0688400a0070310f170252402c64000b4402600c84e42100e041d4015130b10803043d00400580071280070782024010743c6002a818440040c206151840b158450b803030039078951050008a0f581282d0303086450a60f440c00e15102c207a12001c40d5213504c24a80f9140c0f0540c02009218905814941010b40361140b0b02c807400f1100f002c000310000c8406240d0040e08003498800c0c0c2034400784605440414080180e0030400c0242c801c4805072400c0047c01d540210700c11900c15165944000420040d10700482d001214000d0024041102e1000240031400d003011400a640c2d24400030007009080380c20580c0700c2000150b2050080006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 79060586 1250 79059336 79059341
    0x5070b032d04020109080606011b1e030804120e09060103020702040b0a090f060902090d26030a0c020f0a020109140d060c02150106020c0901060507030e03010e070618080a080f0c07090609 82
    0x1000140007800081c5404000072b4400001524482800c0203060490310030805040b1345000008020340403624510078604005054840444040b2151081c05a030446d401d8095140181910030003403201c00c0070382d00c18004401039046260202e801c581c03500d0341115030340e0340d119009016200c4010000341d02d180c0c02c034041c0c083d994a644000c507042d104000340051501c032400006040c54004074040c0180c94072104c1481c98003690032100c0200e94011041c0503007441c158001051141c020f0303003191520155400e0080d111000d41d0002804580044410403080100d090400c0700c0001c01070114440501e01d44035582905e85801141c001030304402501c0403e00625001d1034054800c80c8006c09076960725a000c03c5641006004080134803101045000415109140c191080b4501034028444440f4a02046550f005a03000d10404a91281191280040300c0030741d40e82114502401401001c06070f03120b08846038044070000c44490700402941c044082c0070408000105602400020000d2910608008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 79061836 1250 79060586 79060589
    0x602060702010b0a08030301030f2a0303030605030c0a031101110a0614100e0103150e0102270f130515060c0c0102060109060602060f0721050f0109060305070b032d04020109 76
    0x4a014044c00034880c034207000007075a0659500c40000101c20b2094203008419122080000c800c9a11802c0b0104c0c1050309c04043c4c4080701e10a80303060180685a40401d911586443c1c0074681104500724200003040d104a000c0441c01010f040c44204c9681c181c0440381424011001a031301c25807075044003c80403045103195640040021480b451150500c8000002c419041c80041c050040d0355241c4850300b5190743c4560650102c2500031035880c0950100c00030b0321303448045100c1c03189580210400460802d04c0040100880091600d1a2031020b081180700030300000c0c100f035000c0f03000482c50b1003260706c500b001031401c0d02480300140040200c6000084ca02681608042d4166080c040108601500000c007141c10000d00c950301d8640750741d2158111140d45641c2e002d00e0b4001100320400150741c609512560041025179180b46160fa00d46107601c040e41c5081c03100519540c007200f002c01c41512034402440d04107040868848000700c4030524200e80e0544110404000c849e4107081c07004643e00208040d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 79063086 1250 79061836 79061839
    0x311040501051807030b06070501050403020c061e130b040b07050607211e0501090212090d08280c031d0a2303070c060309050d0309050705010c050c0a0602060702010b 73
    0x59070400c0b0114500100090007514802030410219058074001d8212044410001c0c0c529520ba200c5030034268040d010070344041d400341c062003403031900c0f90030315500300d8800c540302c0d41007480d0410f0b080384283c815a00c008001c02d00321030f1065000c544402e48800078401000c2045106450b00c000d82041400c1c4880504950b00344107035040d6288401e43d0703107994040008110f050009101c01c0f510701c0c020020300d211039103510640c41c05001041d21110b507806000e00d041c50201c0080f403a503904220a0303540c50241094070120301c8000005040940c0c91042c3d40c071414500c614001480c407410549025500c90a25003000301e515441c0c1d444904400803440070540300700b080100782c110103a4440243c200c00410a99401d0580ca11120740d10705020001c41d490a5400310700d0102840d52400c006008003070725174046640780664804810703458428000d03100315681000181514501d020019a550407541c2d208962038080c03102072550300e40d20200580300401164014120324600b551000382119001040c60707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 79064336 1250 79063086 79063091
    0x120317010b18090402010309050a0602030a060b0f040b1308030c0a110f0f1003020c0a0605061f0f1b0618110301140604050604060317070303150810110904060609031104 74
    0x500300142c01004400101100781c850b00010744071400101c4c003034004104090031a2003008805020840c02d5802144101510301d01080200d869014002140c821002e07a11410101400300b030140340309450090440d0080c0028240c400ba075111082403c50f0090100f1108507008000c0341e9003070081d0380030f21801d00314003190191034000ca4000060034000c10502070724000c1c0d2800180ca0720140c0a541103a02e062664012203202080d0b41c40d04401602d1304072a0240280030a11088201b011218a1042402d070f460b2207041c50030b14201011a030680b13481c908001031065412152010411030300c290010200007141c900e43c1e1041a041600d91480414066030090b85030844802742000c0581840b81c00250444005c1196100c0da40042d01502c80d40d0405401003682d1160014001c80017401410304038030a0b28203000120040900d1801c00146208010035500f0007a4461340001c00c550101000c85029201c40b0f00741401c6101040c2100c2c520f4101d01c1c085aaa190203000b4020000820101c4035002c9800307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 79065586 1250 79064336 79064347
    0xd0f080301031b061704051906020301090b04050405150405070e091b03030a02030403060b040e03120906070206010f0519091107020307090c1407050f1b1306060e0d0606120317010b 79
    0x40403078409881170903044210301c02082c10460240542d030803107440301000100c560198140700009500038802d103032880c3d103001d80b566940d0416004d22480342d5040310140c612165008040070342850300070000c030780c0b80c00780b044081400714034281e205000d426004001c1004001403607107030740718180c01e500c100c0c400e501c180100c4031019800000c513415203501001c003044d0200b081c001315024001d512058800d0340400718403041c06401119480d4411004036086840e2625404001e90320f507030080c01409107801840c81c00b402181040d000040d136031143c203811005181d958440020443d00103054081d001c48000503500c06500e000c01a2901500c40c5010802c05545102e1001d0300d0394003981203e03207034803801040300c805001041c4850181d114000c415034107241c081d0707829201010040f204d0390380b02c3d210514400381582da4610803141598040d49401c2003a11a4804009180c803401004a907880d4903180d020580c0f42c0030030004e000071442929100e603e2007440000c00c03500e400503040180315070000e010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 79066836 1250 79065586 79065599
    0x9010b0d0b06010f110715050702040f020c060109060510080403052703100e1c110105010b030105041107030e091f030f02030d02061005100302070b0f0108070b04120209060d0f080301031b 82
    0x100c000845000156400b407503071a009003660180292703000694041c1c17908070030110506960f002003110b03101140548a0a03030700c84420340201c504da401101d40280c18280340d240843d0141c4856031b003240c0641452401c0c82d06500044100341c00a1400e192001c15000f401d40841c24200f20004440090300820712001207003202c0240c1e41c104841040d8840720751b4103c00043c0d9402002c2d000a0003c03101c009000703540e1941e0604038a0350081c4607481c000c51a151556406e040750314295110075905030b6034480022800402c0203844c50300606920318446801100710080ea0700164218015446a2100f02c0c0f4400b050041504201c001c83d80036043d904000d04006419091300451400e944045505600202c62640110024058008000c14100c07154040c011000101800d0314120380c484c4013281c10280d161001034500c0e0040e48180409109040748500c0180380091420b9403142d40900001c100d02d4890301d44111442118400b9101c466001006005110b075020969108110340c1d122255440c0c0f0700744 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 79068086 1250 79066836 79066843
    0xc0c0306070203070206031f0314010c0909060608240a06120b0a03120f0201020403060c0216240c0212060412090504050609240301020301091a100507020909010b0d0b06010f11 77
    0x5e0068a807403180b03410314230180303203100b80d0300002d1a0402c2d40070f146c00001503449802413101504c5880481c040e101e0024811805018101c240c0312203603218040c0713403240001025400307440c0c41c040b000d06800c0c6080c0e40d000e0f16500e0301400240100e07990005100e4050b0460402c90b040078005034012500341d1000e201150f8903480b840e00c041c6031461710003000034441808034024003d94100401060030706a054400076400114030780c8900c0800c0b000b0000907a501c1e40004011890b40c0b512003020590b0f58645201d038007030305404c4441c0703002800e40d004004d4500b002ea8140013048030122110611607090401c25540400900c01902c0280c0d4100700301d00b802d1300040c0c0f0244004052084426074091b481c0c4c00b030508542c5c2040c40c810702800942d26543c44a80704005842525204d016a02c10902e111202e4908103440108500c02c46d1109486c002c40c0e41c0902c81208402802002207640ba00c001840c0ca459880e440120540111090031240c180038000600031409280c051040210a403010001c10b030010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 79069336 1250 79068086 79068091
    0x50c040b09060d022106031c02060c09030a020301090b010608090a03090b0304050a02040614030d1403010605090a0b0d0b0906040911060a090f080303160503040c150e060c0c030607020307020603 85
    0x4542d007503100c40c20345070454064414858081081c0e0340c5c0c524a60198417100040c14003610741102511114414841014404100030100b40f0050340040301060304581c05900904131075001074255008040550082800c0d030f10400c1c4d085809450060042000540c414640c640100701e4030081c00da00e0815450050650f401c90168120f5204000041070030442c08104058460780d016106100441e40c2e090107803c07010960527458064012441041d00032071080c00c0400c29414030400c801d04503401c11100300d8550300304400d110740018040c3e40214000c601c0ac00503046003001a00d000c02c0101500041c04440c00006c0d000e107000c0c50826091000084600d0f62140000c4400d9030b20a489a2112a04503121031280c0c2c002a12815030b80c0000c1034030800400114072555070703400203192070014002c1c222094441100c01801d9140451401d000c4500e5030b180341c1003030480d03a20704401481700d130400240080e8020340801c00d880d400140300d000c442c00c0511440e03a110302d40e400518282280350700400d0252200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 79070586 1250 79069336 79069339
    0x9030b04020f061612030b0105130b0f0708030903180a0503030a030e030f0c0c030105160203030f0403120518060906070c1103010f0c09030309050a061202030702010905100c03050c040b09 82
    0x56100002ca40c0c44035002e03582e144503a100c01038014111800c3c03006240f080f88242e800024141042c4004035402601140d150014210108a0705c914100035960980c03c40d81101c1140742c400c01088010031109005236005902d4200659500d20210040e054030ad02c80744480ca004d910b403c001008103580100a90300a0a1141008540907a40d103180600314491100042c07400032020502d80f9100300d00040b00942c425054008010903220556602891030201d880c03980185d00800010b602c6100382c5055980007403282c24040d2400010300c07210800c0d10804c0364105542c1c040c2c0041c41c0c03c01c4008010f200c0d048003020300500281d0900345801060540409009080c000401d460041240c50035406000c0415401c01c00704100d080b8040028a0446248400c0e00010084403021550346008100740044400316100d1140c9803c241200354080e401c002c19170400d41d541c071014513000c07420511564600884e42c03200000c000c99603810140413200090310801c0350400c14082449807040c80c0d000c44466940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 79071836 1250 79070586 79070599
    0x102070507030c08100c1d13061d090a081b10050c0705100507080a090206070203100b0a060503090c040e1e060a0c0908030904020c03040b0f030406050105010c0203060105101202040b041509030b0402 87
    0x540301080001240c001c0300d8626520b800740004204001340421250034180190315403c42c1c82d162f50480da9190344110107031402d030003085018160404140401c034140d0b80700c81503881c100408041d032800c40320121380400030b407a0005422410020248088135100c4940d03141000541402200201030680c020200501c0c01d5844a005055658200c00d860034107a005049402100b01c0c204502d010303084541c2e51500440e4510008950107001c0c006580c4075103034103402010032007005820480589800041718800e8054400d4460502c004c010f40c504108000100800d45401c03d00c9000c01241c194a903100304000308142c1c180460080070044440e0302c241120003686409088506078218800e5510540c00d6031000501f0350b21034041e240103544142e000780020480c680c0c3c2da4005550a00078214000c0d0305410500044c02545808142c11141e07104070f19200c25008001c01005049900075000303800705460201d4200114032003401c250303010011601d0402e020602c4c559401c21154001b4000a20410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 79073086 1250 79071836 79071887
    0x2040b010c0b1801020f0c0c15210a0905030a0804050d0c080f210115081e130804050607030c06060501020c06030a0209130606050a1205090312090102070507030c08100c 74
    0x3c0d800d406849a01c10030001e8990340b8070800076882c0e42d9001409086016110702941b0121000b086002e0790760242e80c8094600380d50030b55102c0300713032882d40042030701d01e00ca680e07074584030089081000905001d071015190b0750748500b085c0c2042c0d4640f403640007120003000781d52149180000e41d414103a503449281c00e0021034030b40c481d80341d080301141038000003c00d501011000000c0c03500403000e071883e17800009841c0d08034a6114014451510ba0b031858122050440402c00309800400d44100d64a606004213031003801d00d078607180010581c0d80a0b0b4020b0340020303481802002804018403848c00148424001400c001c008240400c02d2804000d011740c10480d8003142032442520707164400c3c00144101c403c00c000b01da889007000341c1550402030410300042c807240c904000002446c881c050141d0720110096060901c1d08404415541000f0106085950280326443c0040c1b02040900d018510500180448a00f080315041c070b401c00e0740c10085541800c00b480045900e41284c90a600c01586003003800703040307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 79074336 1250 79073086 79073131
    0x9030f060902030105091507030c090302011101090b100911070209061e1504080f0c1e04150e070f020309060901031d10020a02070f0302100e1c03080402040b010c0b 72
    0x40002081c00703501135090a0400a044001040300345616001f1061440207032620041141255940340650010688030074061000d9130040e00c0b9001e1048114002051428036940c070074001c52020365890781071890954003806006120301400b038070700104607030700c42c2010030070f0b000500845000f9040500802c42841c0c011800480d0343c00342c1410b40c00c054035a001030b5000b10040c148692040c410040700740101c1440074403452000c00e400c0c5120740f0041c60280354081c120f01d6000c1d12078220301180d90080e1740f00d4484400e1110762164000a0084881c0b0160030314280c807001e0204c601404450b0119001003115203415526841a903000080c00e02c1c0010349000710040400c02e0038400410000705109204020071101040d03002810101d00b01d07801d5410080e581c0030107400e0035085010007584001c0151008007158440c100a950415004020107821800800000d140b202000015030018011000300025801d15000c0c1d43d803e22030030310300301d1100c800da92034407810881c0191129082030343c1e680c8041782c1d0b0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 79075586 1250 79074336 79074341
    0x70209040807080304050c0a0e07022d06010906050a061716030b1f0e241303020a03110f0f0907030c0e03010e07030c0602070e0a020c01110301080303040201080a020a09030f06 77
    0x2c10f40c0410ba040e545c0c01c040c2090b13030f0b55000200d40d0b82d00c1610f40e03290125644a03a9041c060142d541600242060384204111030390000d00e2268a50b800980c601d090300c00d203107040104070700032b05000400241003030409041c010854001e80194052162601c0482e8002c00740c243c60030f5124594002d9a8070070800c1440480250100003d580c0e48400c00c1c0c0800141c04400380d03400b80f0040307160340300c50301c50404050130302c440b11240da80704000031010481d41601c5880f9410040440c1070705035104401d2151242d0001d0803001282e0415284004840c400d14142c1c100b1000300e20340d139034046800c16007119604d4002070072401c00034003000800d80c0310404058402e01861005400400c001e000b07028400315550282d9994003103220507503420040d65030028041d80045001d03000e07686000ba10b04240c0e620300032108040d62203490740518540d82d40740c031141c008004601a5001c1c1816001459a030304041c000100030300c40207405c00c0035191042062603882c1b40c1103000401100e60105031603060b016075040c00b000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 79076836 1250 79075586 79075597
    0x3070c080702060d050103110901050901050d030c14030304031101150b0409020915040b0a0e09040305040303080c070203010c080610020c032a04020403050607020d030e06070e03030c1507170c0702090408 89
    0x101d0b00e003805c1c008020403640e40d0220030400c1003598500c12310303030786c8070100010f2010a115558108203401e6041c0c003c00e21071440c0c10306d07560242c20110000d02e21071141c6842c40e40b085800f40c00160303640d41902c030986401e0240d0f02c0307015a01160241b00504040204199100c0e0703102d041c2003103500252900198841da404007136502e15010445884030780d01c1c00160042d520840c0c3c000002642c031003c0034420724210000f0340c062601545c2d030f01d0400b415070b80c00303407000f8002030859841e0341c0080c00710740010ba400340a0084600020f950310f48140c10b0140c10310410b103500c00c0e114000c0d90841e0301040f0094800080c40d4251047d1401030344000051f2103003071481c0401c000c42094000e400050007100344100094031600441e5580d00b152082c101c003050031000c5601504c08000a41c0150b008940703c0f512520b448a41c00030014150780c07504116500451901c008007007e54079074411403003003007120398100200e015507540c561103a110929005a11044520954200034880c000e44c0d4007240c14880310b24141c40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 79078086 1250 79076836 79076857
    0x90a14011401111603020f13050907060305070507050a0308060a0902071101170f0106030525020715030c020712060207050609070905240906030102091012060b03070c08070206 77
    0x100d507100c00041a911509030a568003007403105a85010083d0b0001c1e911040d0b150684480b441c07036045030b08004041095111055100701540f8245007090070ba48601d42c0980c01c1d00000341651440c010019081d1200180500280401403041034049140829500052989464115016502d540024458810542012151910110b941000c110710f0000380e5032100c0c070903290b40754500d40490000d0b1040e10100d0380340d582d2111900040006500940003d500000c8074400101100f800e401c003020b4680100904100507404400100840005a01075145056891905100803075031820040c0d500c542d14401d01d0307a008030443c2c0e180284402e540c10b652501e580982034504030700b4189001c9a032000d02d40605020300c1d2900000c100b022081d20164001d00118a5a118058000c1d40130010012001410250195000c12881c0d040d0360320344907542d4030150181c2310051640034480c01c0300115221038205d500803600030001c1c000380d0342d08078148500c580e9004010b5070340c0c0d00551001c01d081e80210381d0f402c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 79079336 1250 79078086 79078121
    0xd1b1e0e0a15170604150e061305040501090c0e060f1908030f03160302041202060a030905030a050a03050907081f060b0d02090315010609060c08040308070b06130b0f090a 75
    0x2c000c05038800420004032280758800a00c0c2d03228002040100c03845044006082c0c2c40610040101d6071a4014299100d8401030403c0c01d4035045024900949000b00e030100d800d81d554001960801c0f001c1180d550151200d00303103559251070904081580701c1085641e1300e00c070312032206000030501c00c0c2c1c00030100a480718505407500c6024844258a02e50026034809003903007400c2c5440350f00d0b03d200e442a542190600e4445e415002910707000e104c00c0d60300100c540c904054960010380040340b0704100900310800595a040e90383c1c00d00c0e100007011241d000c0c000e440c0940240b141007004000c0050451440c5d0850800f81040c3d0401c00440d40c01454503500403803404a0100740d44405954a40c09000c4442e025030940786e4154508184000c1c1c10400d005601c0030078143e420903c111840360080e03540051141c08034a14080e140c8d16800025000b419045030b10b02c003060b04100d11030508031031316141c400144c24140800c094403c005203801c0c0320000c585004608a00000c0da03020780d2038020114541e4900c080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 79080586 1250 79079336 79079369
    0xf0f0f03040b01080a03020d050f280e060c070905060111013207080703050711010e0303100807060906030c05070f03020d020609070e010308090a0b0d1b1e0e0a 70
    0x1800950300101c800380c8600d086800001180000030903d40703c09030b4143e0103860312030080442510290400c122500f000c070814003203803611031500018000b008841c80000c40c41e0300350b0003000503c800e4214002070f005c5c400070b02c010720051030001042000d8034880440800c00703a8440300100e0710301d0003810580403658205080d211404d441a00c1c0e2800d20380020041001c0340a81d4000340030405000c0c0c4e5554005000d0a00040520303101c1e52005401c403820b4a0648005c80600301c540342920599407204082d07410010a2000c0151001040340c0105845005004c1461821401500905182c0325841c14151981e02c92440c13184500c003203851240e03001003a040074080740c0c01d00947d1600c084c000e000240c03003540d01280200d000041e174081251011b0300e1800d026802e5644491311504601c105540094000300d0100f80d402060b8044e180d60b44840320000b510320020708c2c402405d121100c40100a01c400d0328200003001c01c030000c0c00c003820f41541c01d000d9104243c40006c81c120503017507400702a020720303901701 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 79081836 1250 79080586 79080607
    0x309130b0603041a0112020603060f010207050607060605100f0504060c1703090d0206060603010545070e06040b03040f020a1a1201080c18070302040521010507020a080f0f0f 76
    0xc0d030185104e00c100c01c0c1651aa01c403a1164081c05806002079032210701440014040d1070503290701e244107101881a00c2042d0f0355040070440c81d03080b058080b18603a884603030074465070400c030a250440b085c407803500911959040402078082e05c40c41c0150001c020280321030100380140f16580607803284408500c5030390380c9018000d1a445941a21203280140100408505249024011369041c0d40c801000c6032074204030075441202d90b4000c100d60340d6141000300041000000d1041c0244e800130350120929241c0d1030700c1c5100403c0c11070f01d000b62502c264800d00060103000801c0090303e9215901c400b180020b5405800084d06a8000d0381c00030341003030596a00740041503d0300c000b0348444111500f429010740d884da070105442d00702002c1c00300d811034907a2044150480c245c0006d0b503040800750500614040d01ca130081408043e40d080e0103d03c090b020b2040d80180903091150903400f081d0340c800381141f20100d5484100ca403240c0d04261101c0300d80840d1020030041c11740100c0c1e880e02106c1d4456130346d4001040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 79083086 1250 79081836 79081853
    0x301030c1809080412060c1403070f110303041101021009051504030c0c0b0904060504050405030a030902010c060606092402060c0a030b09040b0a06060c1106031005030f01050118060302030309130b060304 89
    0xf004541b01410441003402c440d00507241c26044e1005180c0322421603940c15001c94071b00303940325115001c00181d400e1202c03141109100850185001d5071661040d00f4425002901d0004445035000d0082e1815082a02040d4042030360f1210081040308940c1940300c03420221013440c3c140f1000340405084400000c0ca09045100130502071800340d40500440d40d0700d8003004100c03101114041c1c01a041048070b0400144298003481c0f0452050500c00c4100340b0780d0703c44c3d404031643c82e00100702281012000384050086240d81c1000016005c0a0024000403420004c1d01c403c0040c204000d056030100d601a216030207a00108140500900300d61203914003820004801d40080c0c6040100b0391415001048940c440d031404075419030000c42d410740d104051400c0c0302c00f6a00c02080c03181d40381001003010400399000d004c40c0740d071101a0030012030341d54141803d4210785220400000004c9140c0902040103031000300540300c5000007111040d0b00c02200c1c2280d0f80140c0f0169a14a90010740001003000300012003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 79084336 1250 79083086 79083119
    0x151317030a0501050a090b090a0203040309080604030305190501080d120e01020c2503020114090d060e060405010e010c0c0303020c03090a0602070608090105150603090c0301051005010809030301030c18090804 91
    0x4490141410382d513001b02c3c808450303542100c80d4009007614000783c00d180c2140c004540143c801d04e448405680d607600018201700085d1011400a5100d2040c09420300d00c80107807818101e68002d003001694549140180e48052132501c50b014402441032809010b00181c1c440e801030040c0c20300965031203490500d0291100d00841c0e1404030503555454a41000c3c070000c400c0c605899042c3c40c0d403880c8034030b403007440e0615030007541d80d8139402172210304020300041c403502400200e0f41400006103100e06091500030b0a417028410040c0c12685440383c002c400329031102d5000141901400e0042c0d90302191002d130f5040d84113068600b41c001d00a00e50008030305900040c40340440b0310f50360b90264a0344405000500703030741c1c06a98001801026200d80341c0c99242100045402000e0f850840d119112040042070075a0341c211550044030f90440703010040c0356008807403543d004e98064080c525560569944501120590046500c00d00a406401c5203540690f84a0406560484103003919642e4807090010b40c0303480c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 79085586 1250 79084336 79084339
    0x20a021314060108100b12070e0f01271d0117010203010509010504020a021606050309010605030109020d11010c1509230703121704060e010608151317030a050105 71
    0xc28404040c52440344100186a0a03025074164140c544000450300c0300000380c1503242524001c500043c411403a00001d207902c3d003010484140d0703454000030251902a0b4410128018a0a0001030310304d41e030701c0414800d142c4000800d402c1a542280f0341041c03600c159801003101d006034030602e2113a580d99003a24604a030400e841e02c407550208250715500341c1c0030a01c55140c02c203045100500c142e00d0f1a40141c501e0403076600c104d0f002c001c3c1c1191140546501076100101048002061244005082c021030f00034200581c000d2141c00e006a010481c00d200c079030000f4000c01d02c100e02000c44d030707031040a0300e07014190050603200c2c010303185201c503400401400320101e5094420522140b188034070600c040c0c0034024200c0190000038a9900d51010310041140c0d00c0c1c08021440208000310803215250341c2c0118000c45000640c03a81489000d421070b1703c25085801181e2140660040c800c0940c1c1406910007008044002c0d00003a9103000200c205044d00c141034105004001c010342c09116500c8a0704884c1c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 79086836 1250 79085586 79085599
    0xb07061d06060616080a03050106030e0d0c02040e1501090e06060108010621020c10020705010501050f0d20060a02010e1c020d0509030c0307180b0a120221030a020a02 73
    0x104102a6500100ea15400100d41200300000d506150060182c102c4c2d5400060703560719810030b6903565159a20150703441c004039070341e8401071000503458454071a250f26268000c16029948a801500313038154100001d202d107494035a403051018040c07100040d94040480329403003d50712010780d80c01900080302c86922903c280e9001821544c0701e40c8116040f1501625403c070f1080c0b6603910262424418007030f1030b09051f001c0010b4603400808018059412000c0c0c0c00c0161a807840385005401d60b07c041e405944604030620381c1558950301e2078000382202d603200c10103030b9003d01140501c140c030303449400c03a5503807007003000c1003078129a90117400005008881e001940c03100c441c10071400f18030344140321544006a20034108101c0042c00342c0014000014018201d90001d8081d90010b49444400c0d0408100c009210000b00911001401145440b0a00311400d0faa190b003840b19095103d902440040c4c4903c0054000381c9030150ba50203190b115010b4030b01a03d5071544000b1000c0d50302c04440d14205d001c0e80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 79088086 1250 79086836 79086851
    0x913090206160311060c0301090b0102250e0a0c050f0a020f07090203041b06050f0703031401030309031a0403140904020d1d0f0c10030902010210021305040b010c120513050a0b0706 79
    0x860104d030745d51182400d00c04550859007080ca41c40e004080f0000680d0540c402c00007226083d400d1035440ba803020141012141200307090001d0001c2151000d0074412500d4104150000d81c1c542010550b201041c0321a80d0300d4440c52201c0c2c00f01d1420b84840089002c0f405084004070704801940c0056100351b00480d14025444005650140c40d6540c6119842c00600103000303080620310820010220a4000e02c1c01050700f5443c218042403011003a8800c03008030308421410000c04c450345d00b0109014829681003402c0d803900f51009050300040300707282881d40c1c600207407e00907130f0343c0c50b41560010215907030100701080c80340b880340456088900440340e0500c2080b001000b01803000521040c100f41c00384c001d00f40c5c4c21030040e06038050000c04404a0545c01a4516808055081d1001c0e0a82c01f0780072080c18285480d05040c4811100c8604049041200003001d030004034181280d008a102698544183e581c04900c920a003085503e4002c1680404040800600c0d1984140a000d82c280180701c10403151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 79089336 1250 79088086 79088117
    0x507021509091504020c070b18030d020c0d080f1b011b0c1209080a08040e1602030315010509120a0b1503060412020111070f03020606010302030c09130902061603 71
    0x14001c00803003a40c80844803002440a1400d4008061441000307000503092101e000909802c001843e004034200c0c1030086103240302c000c0170f0191062400c000b074020781003400304c070740c002526030380755846250080401c3c070440000c0111440840da1400016010030b501c40a50010043d0351500c100c100405641c03c01140e000349502c8803205110000d1a40c5600204001a6868403040e90f0131071104010310000b010002030519081c0b0010000781c0c41040603982c0c95041c0b00c8082c1d010070000e002c090101c6902810322009130b40000c00c5a8109902d8410034004001d00d000480c2e0921407812140d4020040000c0061210340015680c2c11062203400f0141039a5a030b50039407454950f1881003694958061004500821914040c400c100c010720320000c90482295140c80c61203520840d803c40d0380b44911080c400034143c0c10321000d0780149092806516608011103100030f980a240b600bd41320705080690745203a070640343c0c05102c00365070241640d6207880080c01c4180748480802e030300742e0100b81c0030780c0b255010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 79090586 1250 79089336 79089379
    0x1205071b050703020907050d050f0705090910030c092901020309090901020d0203040c0501120515040c0504050901062a02090703050604091709041a0904020d020d12050702 75
    0x58905991940302a540321110140440c486440035146400b0302c0304007001681340d0406043c40b0b18941d44402d0340e80c5210800e004201c070001008810026040d13814020283c2d4880100d404a00b411210700020ba00d40d0b0a1a5402c0e103860343c4002d21080400800040e280d020740c106510064604446d1841d46c1200502c034641c1070341500000f40107810030482c02c4a2440c100384041e80120394040014248505a010041203034410754003620f6008041c0000c00c803641e0f01c00b1a0480f440840d04c018402c03410441680c004000d010f14600b48034507110701d003581d003942c424002e40300140401004110716503900c900c0035040443c01881030040b5401c1d142e07501180b22039460090500ca9015040c0d882d2030b030701c10100303c005003800382c2417585c8646c4414201010070300b20301c80d8617000f000b016501175550504004010480d80c0d0b013140302800b001058180b44540d9515080c590f403198040d41c404052441e41c2c0700040d498040c4240041c00c203040c0d012031001495210028003040c92003921091088400b00b004041d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 79091836 1250 79090586 79090591
    0x10603020306060d05070e07020102090a05100801090515060313050606030609030301030305030a1e0606021b0a05090901110313170304050d0309050c060a030b0f0604150302072d031205 81
    0x4042d031201c4041821420002101d8542c0ba0040090745c0c3c50980f189440d820f04441900c10000507034020880d18130a1070a030001c0c1e001000300300d60302001704e00c0d40e0fa0064584401403017584001540d0300c00003118211000c0081140800080c005540c904d0b1120b980c00b86000b12140507500b074401c181c0015183d040010394103029800d91f4005604503842d40d07500b1901584020280b40c55036031a200078441d025000c500103401c5540c3c03580c012035150b040440080c0b4008500200d9041c004485010000546400c2c002105444003590084036503030300c40000b40d0151848040341ca441c0d000000400c240e08985103003d40c0400d105601440312a4401001b071207403400107070350180840c3c000700c443c0c1a4150280e03120540662107141a1000410700030001012900310200f00004a07454014040d1603141c0020456040d11003210708600300703402c014154034800c40c4050a01c09141d400903040c01400081354401200c0c000a0320365001c1d00e00c9904814102038021401207020030783d02030119404a025004052 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 79093086 1250 79091836 79091839
    0x504030308040f050717060f060102011a0402030408040317460c05060c1806040303020316031b0807030e010309030e1012060602010c110105040210120f0911030d0201060302 76
    0x1070315500c940d15002c0b0f0b41c080d4003000f01c1d2140b2400c100091500e50449003000d04090b024058191850114a40301410000905032411039140604a15008113400c100da401d110040e00c0041c1c0701d82d103c0c50000124880e0340c2010340305c1040f164900d010303816114010400a2075140c800c50800c0b00103040c0c10300031894903495040c0d5910000c10403e0f040442c0c0d500c0c5500404030316046c0c0d034808003070310b6450401340240d0301d11001c036200140226045a01c502d0b51208900142d80607407420703144d614029100d005849049a04421b688541c0c0181889038190000094101c8180d28469046e403814035800e500551040380030841d40380d030440c1a503020780b141c6145103805440782e45040c07443c24104080041c8004690b41400100189014080500d21644d809040d45400018034124010400b42881d1213a58909806a0402c07003000010388810141e914102d03c141460032035005400d6905010b40102d03e40c9545052500d540300092003408030902c2d02c040000c0d01522404940d00344203d00742c60042c00301a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 79094336 1250 79093086 79093097
    0x90803070f0816061406040c140d0507020304080f01141510080a020706060306090507120c0506030a020f0c01060303120c051206040e16150516020f030f0a080301080d05040303 77
    0x6000b145980d001000460824841d64030f8503c043e0b034039002190b01840d60b800f0f90101140030000242080d1085101103007503428a004066100e42c5202d2161180070441c50301070fa00c0c2c0c0f012410040c000c01c217407000740805100350341800b080020960300810030040054008464a4007040c80050154100708030420f0192650380610ce08900555030110302030988205247e0800140011440c2072041d174029520030340300810301c60b0300e0381490f510f0035021740c20038543d402d1a2a0b01c00c001400c0390004004450302a00d903252256100d0b0480c400900440300303401566840081c28540441c0c040d0312107416240300392031303e222030a1201c6000d000c031614806003401280d420800b4000c2100038461866110380010808902102101c02031030600d040d68001300c0425200c25018415003800c281c18828170341551401606007000d05500c000012407040000e4014903081001e080c15842c00c4c0715000092088504a540f40d40f82c914003007031581d00c244a144064000c0c1c1c40888034880c4100121411203401d50b903034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 79095586 1250 79094336 79094363
    0x201140109020403031205040203030f0c030306030f06090304170304150e0301110a021009170c070314150105010503071103031501030b04050402181f0611060702061611150109060609080307 83
    0x40c0380103103000388c81a40d0610061105c002801003000040007452400c81c040d40d10f0341072034028140741141d695418691030b0040c10030040c8a182c0081902c04071a030103103440742c80c2140002003500354031450f04800d08222410851038804c0d6005203240e10180025002046021043c801030a43c0c3d0250300c0f036160040c0c00101c0d05100e8101d0741c7e0410708004c0e00450704640f01c50311980d00c1c82e00300e6001c04480c0099400241080050003a100061082e0001d0100903205a00d0484201030404a050046506000c4080302140b4254443c11080200d41014000c0765943e0a0140040d040c4103032141e800c50004c3d0410f445204141081d0003400d000e00d0340600500482d012442da00c81819500602c0c2d003030158030300c90031001c94205205495000700b0350ba8803010500c1c21100c070307628144a00244148155402502070010b441e09103031058006002c1461309c0d074038411114000e6414419030a2411a989080400200366051640d00070001c4030701c261108240640c2e80d24481c0c5d101d0040700009807031400348541 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 79096836 1250 79095586 79095617
    0x9020d030531230d060c090f12030f0c0501060303031d1209220c0e0f030c03100c12060308040510020d020a0303020a0e0303070b0406060501032d06030210020114010902040303 77
    0x1c510500c0d0f101c58490200c104541c0030a0703140c04110b8083c0c440b00d48a0000840903a08030409102410301501c10070032150420034941121480000c00030200400640c2c030a00c080c0c07084800c194486c0d0b2100080c0032055036824000c001e420004e2030401501c941e80c158801031003001565088940072003400d541042d05d03010030044000d00c01d03a0a4440010084d010b00c03466001071141065910180d01c0b2045280f01e014203000c040e640030f00b4a00e019600942140c0b01d0b50b600080c0444018a08a401241c280c5014408545200101c40000503503402d06c4070202c104901c00001d401924002e0361204660080041c00303e030fa84e08192800b4001d030b00203800c0b01010900c290000c007808052401c0904c1c07001004408245503600115007624049003480c1440100301c600c1c0100f034000c0c842460244180005d0001010303034181515400c0010326204d440000c903032040398200600440d0011700d4810307140c01020010f4040d0040c0d01c0f00550300750307040001140c0b076803262080e1400d0740c0c0c255031342980ca40c0a028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 79098086 1250 79096836 79096859
    0xb030d200f0307060501080c06070201081303030b04020a020105011d16080603071d0a0b090105060414042304050607182601061403152809020d030531 66
    0x465000602a07500e462809520400003002c50a10861001500d0f6140082c030a0902c0d002400240c0300305020040e03180941c0e8803442d100c0d00404e020380383c1c40f0340d0903a03454160000c08101c0801e07a0818000315882a24036019070009040328610141141c0e04e102000c40c44140000031144c080182c05064207007006e00744210b40c0c441c2e000394054100d5605c161681c110a100e1458220b1881c14a0681004c02c0140b44540c021103842c10015616151103506007800214503014500174a804100402241902030741d42780c000352190424a404141078403080c001130031805104803026102442280046a8514440c0d0b0356078008500c1e00811425182c00d01d0121007244800581200c125070814003450180e510070302c22440100610000c03024203600c50340c18941440040014007810000c110100311246402c1580c1c1010520340e0328072111303440c3c4900fa144004100c00003002e504001d10800a034209500b181c0200044000c0f40481c0e02c0002801c0c040e00c24145400400702e6203840941010800c004042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 79099336 1250 79098086 79098137
    0xa080c12010b07060b130c0e01020d0807030902030a02060c0303101a03010b0d02091f030c081b07050a05190b01050f010c0b0601090e040803180609030901080403050f03090106090b030d 81
    0x14400440c2d43e038440c5c000900c2a0070b0441c034040040d5078400141d16041c1c0c0000c0c0400b90028213002400c605064044060040100109050305054a6144603411036034140a013080d000d90042c030003070302c481c486071107542d13690401c5901440e0303030041ca030300401c0e484007605444100c04c3c803201d01a450b43e03080455015054000c2c403da800d01c00e80a00c0344802555441c2c0e028902a07494030301101d426810f5000080541341c10755420000d0064040c10f02044d40e5030100c525026038540c50520760f841c015894a81e16040314600044c066000310350502118909000405084034010410f118040c0d8070356007004010801c0360082c41c041220019a400000c191b10301d01540b0100504020304003a95860681c0a54001180c044407943c5001081105920381d05103031900450903240208450700c1d1a0394400d5603071054040c0a81880b48803030003e0201445071080f95a1200d10540458690a01e450054043d201038040d52040701e042c814113030f0f59401d000809200140c1655174005080d000510100c8400310903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 79100586 1250 79099336 79099343
    0x30b010509030307140c0f0108041202150a0f0f0b010203070f060b04062607031e06060b0d0e0d0e0a050918010504030f020c0d03080c0306040609110a080c12010b07 72
    0x500ca04859590240080c200f1107008034045241240c03201000c90a01b43c40c1c0030614405c20405104c0c2d20f159901520203540300d5030004513030600c15a0b5803c261301d405000c11046102880c50801c000001150f500142e111402c003e8080c010002210701d01002c0d80c00b81c560260041e80140583d0001c10b503002e5081c0155401740702d0000b400d210f00800700d0282c2d0542d412824070454084400e900001e02c5c0d950a405408030b0b000075222040c156501d500847d078500301021841d402481e140c100703101c01d44d0700001c020141d8401965941500d400e610001d4801c42040d55464020a03c0010115010708020450703004000c0150b0000d0b8100010009895800b510f1040c00d81180c850441150000344030742d0b8000c40c029101c1c443c5c4200c51013802131030503e1204016024801030b22400c80069003000000e90000141254186c495035400c002c02c00030162035200110450a00c00306040d154000e00040200c07034950703951754055a44910030041d25109401040031915a040300402040391940c000e0103030300c0e20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 79101836 1250 79100586 79100597
    0x50103080f13050a06030204061805010e0607060b090f07030f0b010801090207030201060b07061b03020703020615030f07030308010602010b03030403050c0d0f0c0f05040506100f03051905040602040608180607030b01 94
    0x1260340200e0510046a013010b0003007a0f00123810311005404c0a0031104440f1428050314a882c02d14000074980c092a010f040d00460002c0303800000c001441d04807482004000e40840300c03600d01041d8030500340105950f0280464a4900350740d4030300046009034420074406850f83c12980e4030b400801002036010b60010380455580310310109041c01c0c50802070030840e000300b030041854014074807081600d100c1411880e051500c104071140019801180749a0300401040200c0c800c0c20300c90012034100b0424004041e070030701074800f000c420941c01c6820903050755103513802046039200000c14507980344207600002d401907011b03d01410003841c000c5606d001151098029844043c0c1c160f44040484034181c000c128100740d003030018482400d00c1d106196015404580d41240d024000001421120407812260b040545070000902a24800049000d0311440c07604104410b140906100c4000e400c140106000144e400c0007040c0f500c480c500105160741c43d0007018069644401c1820750040c064603070401d06018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 79103086 1250 79101836 79101839
    0x7020d170c2701091502060a1802090708041e0506060d03050c0d0306090b0f1807030626060105010908060114030a0c1205060a050c04050103020d020c0604030f020d03050103080f13 79
    0x11629460290b0510071020081c0b0960034a400240803140300d40c014104c05140354440140403540091010340000540c0030008040c04400726050a50450a0010b50400070f50001d012070070f544103a00c036201d1409003140b200010100d10548034174a0700e15001900c294031010100c1d059162003180c2400c4680719041c800d15109220fa070481c02c150308030100602281d5aaa010030204040e40507d00c0303800340403a00b4207031101d40980050b5804220707441819116803030a00003890b50380254007800240110201d9541e04a080d1681205503140c4da0490740d0260265034000260b95025010080c2950f89130320145c0f049a0810011030151404940203960510921410314081454402114040c3c2550400302c1b50b22089414180c0c5001c82c041e0680d07540c2d40c507260401c0030914041054400f5a5000d2a0159650419003401d0001e40901055540300c0c1c000d00040c40b041540003c05035500740d040d82c00ba922705401d50702056040b94000d10000d05600390420080d04120300303010080400841440e445016a0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 79104336 1250 79103086 79103107
    0xa030809060d060305030309060906070903030c110402040906052b080c0a0209040c1e03050c010c1a090c0a060201050c0412210801050f0607050d0c080d020c0304030201030507020d170c 81
    0xb100c05a10584d0345d90000030038400c101c003041c40880d07408441e00c4000c01d0503091000c2c2c01031511106e844040c0420200b403003000e00300000280c1005502c0300092096440307a49810750306004000c148505c61040c128280480e5800710222030030f0005a0054030078007000035442d200d2142c141e128032108106800381e4042603006a0315440480d0056000c5d002c46002d081c18450700c07050070484911011040e2003001ea04200203200014400d1b1495402e18140301081c40d20301d13003c3c4508070707021742c10200907644c4410440000c1e8002004114000104d4890002c07070780d1880240c0c2200c000380c0c0c003000c407020100824000e0581702c51402600324400c0364462071091a4210b8907500d07a050300071500005000c140100180d107030a5a01401822003161141e207442e04585d206a070b5813460003024403e0140c414112818081c0c0c0ea015143c03401c00031601990740303100780c1401360340341e03401400100d02007840c010214000714070015400030f00d1351458644805042440b0201121080b004140c1c0740e10240401550001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 79105586 1250 79104336 79104341
    0x306060603020d0c020f0703030302180306040501270b0606031b0a0801080105011505030117120a02010605040c03140708060303130f0e0703020a02100506060409050f04110f0a030809060d 82
    0x600481d40d005031038060010601054514800306141154403000c040380341c1030404620300e03041341d516041c0180c1d40ca00125960544940d0844c0090f070500440c0300300014018190000d074a0684a0384040c044c040200e40780c040e0200755030101801040d21000040c0142c2400b900954101184400200344202180c0041019038080950740000404d1130004014404090090318054442e020b25441500c40180b0010103902052060408801c031030354101002e0303079050115840743c405080440703907566030560000e806032000e4403505020300d01c0c1202c500c440708d00c139225107070784203010b00440c0b039194581000885d9071580140c205a4540010080038884031405d9117a03400800c902950720b841549008022041c4103001003107407040c54010003010f40030b903a0114889606240f840000030321921500085440342c06030f03030840607543d4540001e01098040302d05020344510300c2081401d200c10003080501289580390f02c1c41d1500031000081c03e00000e491a000b501032a400039000c0d0782000401c0091070300313 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 79106836 1250 79105586 79105589
    0x1a1201090c0309020d080c0106050402040b0a1b02030708060403090909081801030b060d09060e030c030403020d08040503031308061f0614070b0a090b0f01080607050a1707020607020d0804020d020405060a030606 92
    0x28581c20000c0c200103007d00070f0040740d0052004071421410140b401071030010500c140520030040000006008070b5400408800c60803041e0003030103c83e861500c0e4011555190401c0c2c60640208020100000780355030701d40504854203a2081e11242090305600f101c04a44076108405810300d07445440711180341c1c42d03a40107070546840414001c6188882030070314008461000307042100540041008507007144c000000c48007143e07070545001410b40d03040d04000045000c0e40d004960303d8000001c83c54080b100310520142901d415506552042e00d0740303150030b00c4104805104501303220306200c003000103a00440320b607096202c41d1800546041405e075038846949800300d4003c00b030a580c0e11588400e0003881014158445014000c885c000d505108c07005a0b100c000034401d9040010016000c894148505054418584080096003007401e000c40042d40322601119084010b00c52541c5056005104100050140341c0103007001541680326001d0001030f100040c4202e8004035140000000100144120300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 79108086 1250 79106836 79106843
    0x1c09060b100c081b070308070c03021c0b0703021602040e06090d05030417091f02060106230405060d06050a120b010506070201080f042a1a1201090c0309020d 69
    0x84030800c4004021644025856010030007801d02d1141c00094036201c21901ca080d40d0040c00703400400c105800d2490140c0070b4100030542c80c0c3c045505010007000c0036841d8140d0380300320b40c0012450b03046840b10f40340051070300c0007901d4144140c001c581d8440c0240d0007004c42050004d08080780103110340228046e10014a400701d03195102d2010421009410701050141e50224a0000d256040a4a511142c0080d101105880c402d00040200b90761b9a0795880703907200582807003481800e043c079910103074880341c007442100081513541072810344031020003071491001d5003440000c0d0306042c00c200c01d109950b00580c12540e00755580e054007141c540e8501550a006240d0710b81c241c03514803400d181505100314180e01c0749005190070300c184001030381c116140c982d00c00740001800c48156101d00300440c001c0c45410f45c103880c0ca141002031108111007250050140c802504820309170400c41e03801407045200e42c280342d41c020007070280140b00b00d010603044000303200b14602e004181c0301081d4001a04540c9400c5044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 79109336 1250 79108086 79108091
    0x1506050d031106010e06030a03050d09061a0f060c10050c0d150602071d010e07120606050c0f0d090e04050f010204060801062d0e0616051e01050601090306021c0906 72
    0x11902c4035000c0041c1805080c400c00c4203211420301c1d0010a64030542c07010020705010700801e00011650082c1e102c85101508040103100361001802114541e0b1190f40c031b03aa02440070380e1011003007820810200c1d41e651030010024103600d21090040c50007010050034003411240204448801d00c03141d030050b542c44804150001c1411850050081d16200442e48111020f11a83c4130301c4440708071000c8081e046554080204810783da6449040b40c01c5221880f808151615052000c243d55500101620a0180520031a4044001d0120441c1e0300e480c80e14400380025003006051211072100c600b0710f0b82141c42202150756010048110340d09a8005421450001d070201c00104030701c60f0300c250034040c80380480c04000401c4490074110400070b40c4036113800090002d030100c540800d480305811200e5802900c0804000605103140190321142484c8525088140710a03d0400307014061003414001d0318161100d0311010324503030f0b554003e07400c4040d58010481c41a42d44ca0b55414041c01120342291149100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 79110586 1250 79109336 79109357
    0x4020a030902121e0a170f091e0307050409050607110f010f1a0402070c1a0403050105103f02060403050a1202160b0301050d020a0f090207111503041506050d03 70
    0x94244e0380c0301c1c1d0340505509078800c0301000082620405a64a41640d10705020f90714118040b0040c15441190740507504034580001c032109950075103c0d02c0c20303010012800d07140c007035075200204000c0c1d40140c08050700c03940103040807030726050240312608200496507042d1003224605101203800c444042c1201040c0710b40300e0864400803c502c0c1803c06c03104030212821802c2030103c0d00c64500850543c00b4800a40d00b1150784500241441000e460045074400024801882c1c00381c04881c03910300610032580042100c1c402007944410040c0c0c41c0031281c1c6400210344030b2400c58029092003020041d07099030841400c00010010900a101154100f80546081751118070b00d01c800070320701f40c240c0f1040f1302e00012003101440504408411a030441c0c208658030078030451240000b03503005603a035101c8040100b40c100c00040851068003d01030550103001d4802040852000b8451442501451240e081e03d08100180c0003c41e5411126500d40d880324001880c1c5859202048640c2c0e0184015008504090701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 79111836 1250 79110586 79110613
    0xe102d0b030c04020f031b04090e16060f05070605071b0602090f010914120f0708070305011103010b032d070e09010f05010806060c010b150a080901050f0604020a03090212 75
    0x503050b106103098904510b040d080c0c01c00c0d10307140c1c04003034078024915078550605a0580c07031400988001d002001070070027a40950820b075a6030b078070a8541011040e24075a200042c624007642031728507095002c1d100c080c6080080c2e030f1908001c0a00914510500120f000d4020101204d0182070020520170480141c0d92030030b182c204540540074064075810020010020b200308200700214142c00c1c0c1e410348074003d070440040010360900a0100105601d842514000600d61800161402c1281d020364000c004400074807050f140c2c0352009006002c0d0b071903030410200e0303a001600c441e45003180000c0441d00d11054511812803c000d441030b1442400142111146886441c052020306d004200040d91141c03003600d0480080c3c92000020280c0340718801c007182450b6040e000703410000783d0312401064002c598030034086a000607000805c80b1130010b007600000a074038040500c11107002c5d216441c3c408055540314030800c0701940c04003c051007056140d6200c1c0005842d000c5a121040c01110701410b2002c1402c0ca = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 79113086 1250 79111836 79111843
    0xf12120903090e0a05010b0f0903010b1f08010b03160e0d02040c0905040e0a120809031603020304061d0d11040e060f04051203070807030903030905160f06030e102d0b03 74
    0x8000104481c0f4217801040b58043d071000321242152240741b9203448108a000190040105014050308440c140125070904000d2819201040c0140e4503040100d9888006140b0280070480700b62800000302ca00722014075010305c5e00000d10050003003100b282d41c50640c0c0405d040d5010b1540c101c010401a90301441076103464080d00303e401d04100003c0405030042d8940c072240449050304001840020000309954141c148201d5440c01600114800202a00d2030001d5507a400351144100242d03511490802c1140aa01c2c1a10a001300401c2859003224035202c5110a034007008605500507520307010103080010500009114030b1400b0711100c51450607013811410052400040c440c40e0b002001082105904000303040e0f003100c02403900203210101480c06074010840340c98003801034401d040c410031a258104a5900907945140080070506a41c0d020940c1660707089100000c480e00300d00c0c8000040019270780f1030181e15500e44140009520301c400c907031070800702520521103803586a0403018418241007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 79114336 1250 79113086 79113091
    0x60f0f0e01020c07030f08091002061501031b0f021c0801051305040b0c03130b0103080d06050a21060605150d06060807080a090510020f130f030f12120903090e 70
    0x640294a41165070708501d13140c492501004000f06503296640060218401c01e41d241084060700e544031140c4100c40103551210211212182d240c000038400d90303d03512900070f103542100302c0f000c41d984096000106880d0b81114031640800c5124241059090b4240645c0401187d02c10340c44404685d4109410b00c50403005070901e0564080c246400e1200040b81302c6c66540d07011004050b0b0f1a1680c44040d20000d01e000b01c08006009541316800200902c100c0d10010030343c0b03030a0350710304001d015590000d00249290601c0340390a1460003240084040100d1700e0354490041c8100c0001502070745480c00980c09042d007040e202c0d484080800c20140400141c81000041c2c14141000c442d2071a01c0d00b0b004101903401001504503d40fa100f19604024040000c41c4a03042071030700554840c6001d007030508090300f1415034001c09010b0301c90006525140c68400c40241c1c0c0c1c011348071000101090f2104a071b660801415001004038400380c0344080495841500002886541d074414054605030042c00360310b502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 79115586 1250 79114336 79114361
    0x308030117280b0603060f070f050d05160e040606050301050d05071212080106021b0f061207081617040201030c170103030531031101050417010203010e160503150a03060f0f 76
    0x207409101f00049180c03c40c0364801e11030318140c00700d502298000c8419000b0b500100070050305041c240f1482104c01d1300514010402540c900004074464420031040d50414410140400e03810801401181000114400481e005204440c161a42da016507c18000f030b544055901e0784030000300003402c681c41800180141600e10080034010b1860141200e01103620001500c1070500800c10354490702d54070107481c0081303007030011602640b404240103824440c044030800d8410181038200c5200601030000903101d90022300c0b80c00355541c2c465005600501c00c24007084144003041440b0b0540320003040a85001c0c5101c0d55840c3c2d141e44038000300006c03009907840540900d05a000c440c03d21451604540e008980e0230000c03540d250030304540142c5036403007140c10010b001c0320f20101098105105400171412140c0d805820b60303c80d034520064090f02c44040503220300144041010505c507410b110600c1080c0c1800410a58038140d60780d0b0386030202c40342d0420034550340761160000c00042030039128011401e00c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 79116836 1250 79115586 79115593
    0xf0c010f0b0607050606060702040f1b0f0201020f040e0c16050c18040302060417090607141002090112020304210c05010606051306050d0906020c150a060308030117280b0603 76
    0x94540d542e41e03c03003100821b0a402588003090a0003507540ea41c011011080e04010300f00400c0013100b0909000d1007168282c40701043c244c030007441c3c0c594814800c075500c614640703035000e050606029404640b00400360041407024070500046085820310f034202c140c42032054004001d040d1441d030a05c001c421417880d0080850070729408020100340c000c00e04a074000c1e84a410340c0d88907060f0381c9450b1858002d803c5003e401400c0402d031001040110118101a01c482804a43c103500c50359552000364030540344d01c24009541040b441440208903000303150031500c600342e4040191125203100c0000e8000007a09000036a9510301c00c0c0600074217100340d80182c080c40c80d001e890160500d4058a86c03591600c20309d001c2060018801b43c402555521803800c46078010000e545c3d500c1e422807840d6807a101c42c020b4212900c0c03603d000c201094858400c0404982c0d100e94101e00711ba2030320300c42c9031070300c803503044034074020300030309424121000c086d07549500fa15140c1d0450500042e42e6041607058488010f011078001c0c1d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 79118086 1250 79116836 79116847
    0x13020a0b0d0612080912010e0105090a05010f1802210102070303021b06010506030c0c07030203030301060c170a1205060103231509090606100c0b070504061b0b0402040b04020f0c010f0b06 82
    0xa0080d0212011041e06032846c02c0302c40d4032a501c043c0102468074211505502c0c0c40c0902070020f01c00f05034400080d00410088c0003c4458120a80848901001b41c0044a01200c052001420036401c200400c11621301c0303009100f4a8400c84c1d90a90380920401c41c0000e034001080389190340314090382001507166200501c81903040c04e000c02c03018480503101400e141c1e008a0040e00800c41041804091940901030707a03280d50b594000a400900c940c502101d4400482e03103504049041102501c261b410255100600080b99640440c010140503100504050325422002e5403038140301214108000c1200300540c0c0d41c50030540900d465000d509425100794140c50a0100c10b0400184407a00300348100c1d070003010002e04090680341508459402071002007600c04000b103180d00000a081107074003644bc0c1445450001d921030046040c030b000001c00c0d100c1c0c298041760140c14103900104000f42d01900c018a03001030b0056803000c540143c001340d4400d0391540301400e0031404034000d43c0c1c0b006206071041c0d030602 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 79119336 1250 79118086 79118093
    0x303011703031014130218030607080702030304020108070e030105040f060c050a0e1302070b0a02031501110604060b01030608010f091a0112030806031501090504020f150405060313020a0b0d0612 85
    0x2122a4801c81c1d80b1128090300500c841da90710030040d1005c1d003065808540e2280a0101100258000940c9501c03a00490b80000d814500075203815200b0b20603079001e1442e5030340da907005440912014007400c040010380c514007034031900d0074840d1a0282e8099450202d4044151a00c00140c40c1d2841d110310030420b0a2002d818201d401c100c13541d442d5a0115004000048800c034200003d0165800152160400c42d05115441003294001c42c000d0000e101e11150f4010000c1c0107442c004404d5114040c69030081c80014041013050f4820300d02140305141c04201c4a42d40c00d100c6003540d880440034100d10b60340d085c29004104031502180c00c280c8a54440380310320b600d03008980140f0300ba0b59a0240034864800d0016105540074044401a16079111801800e940c542c60b08900400b01142c049000e4807000c9a1940300c0d1900c1c41c0342001d0300c04085092442c090030f10041c04403603000074215a4003203580c002c0701c0e00182c2d51a0070f010054000540c1864590809544c00da003036805981c00160030640a0b00e40c030010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 79120586 1250 79119336 79119361
    0x4151e050c103309050a0216140f030d0204170f1522060b100804020a060e06090d06140709050a0510120e0d0e18060f03120309030301170303 62
    0x1010460350005002015410f500e0081c000d14182c0c0451003082c128400d030b0654485150015185001c4040145a5600e50380804903c9003403a84070181c2d21081810000405050303203c2c4001c20700070b060315400c0e00c50410603499034200c1543c1500306031b0041800e02150f801e1041030182e44d2143c000801800006c0c2c0d003815100c6281c0d80003900c1c0c64500a0018032800c8210b40031034551009040114480e4415003802c6008043c40c285551048101d003002c5880e00d442501c3c040e0080740c004296281d01e03450144155240180202425080402842600c04c141d4402c401800000c3c094500400e041c01c0e50140220700840080110061154011081c025a154015140e055130800e8612903581c4103114020f89180d0100f80c190f24103542021038100005001080009910005464114848294500b001105410350884e07080400c0e0003800514689424a40744801c040050140c4840e47c0e100900d40b006640201c0c2d400042d580000010482c40f1120750384c108458803864080c50440c100741d018846d6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 79121836 1250 79120586 79120603
    0x603060d03090b070501022511060a0e06030412030605060309032205060d09020123031b07080a081e040b180f01020d0b0405060d0506010306020f04151e050c 69
    0x10019400c0c114201030044810320041c004440d402900c440c4149041400703944185151340180c510b410380c8a1100081d46003000d0450303840080040c0601034030040c050585c016805074000c1003210310031080c9945a40b0000c60045000f48407900c0b8012003000041d00741c92803a4095402403404000f002001c00300441600c0d007441c50818041c18120400051400448168100c40e03807012000030003170000d02d5154010403100740700f07172952281c1c031001c04d2410880800540d0300d030803100340030400102c10440c600210210400209440c9090082d662210000c0303400c0f4528000100703010100340106a03c00d20148d60b6020103d5848441500d0300d9510744030307420005462803512154140c078800420106010103441d0044040c021519900000c1c0814080c003c07120342140110f01c0c0501003011707030a248078400c00945c0c1000090800e6440e50350307050000c1d84001d03030342d0b0341710b040c1880082200120851101301c0c40381c40c1e5481e04640c0288118929120b4164914081481400c0040042000713003c0765000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 79123086 1250 79121836 79121839
    0x130b0a020a1412040603150905060f06030406150b0a0e030102031003030315090f022a12160c03080405040e011a100203040e070305190501030302030904050a0213062606060306 77
    0x9580e400728040b2441c0c80200862100c0615011a010408980c0b5620540ea03400303000c2c0000b203980b503445529504075070003a2002c07504418409d00704503072070401d01c00850b08103108110000700c070b01c044840d07881c0301655504083d505040014020000e29403121807207100302030480086195040c0200100740d00706891100400749520fa05d14003403000d01c075500c00401030500d03820a000904603102500c00039401081800d8621701244010784003c52106c5082503604403030f00050140f94804030110070785411114040d20040a010500400200c1e00c2541c100110301c80c0c0c03802900d4504103020001078a1191040038110780c9009030022084091040180840c01d043d6501050100e18030800c074154411900b0400c80c6001c00e83c140034180d58960301c018410703003c00000001c41e0381ca81d13000801b0341e0700a11026005a000b4041140545441c4d23100c943c2021060354014a0a42c248003034504c040490342c030503008190b610240b03407410b030201c03c00110f0580410002e801949441f00004116020251446 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 79124336 1250 79123086 79123103
    0x11150f0304111809100c023c0a05010209150c1b03010908070c0512030a0504090507110a0308040605010b0f04090939060815040e01020405060a05130b0a020a 69
    0x4415120341c402c0c50400340003003034240c0d100d241c4004d840780c1d1801c03034400e03204030107242c0103003800c055102050803080c07003182d0b50103860050007080180c07081010386041c6a201c002c0080e08000e00b0702082001c40c0001e0f200d0700016840359404400c00c0410030108c0d0f20550800c10030000c14034448004215100544111712000701c58542050100c2d0050250000052134000009074a10a0147c00340c0900101d0b08112a80c921100084110b01d44901800d920400072a20620052100b210503801040c2d000c0c4081c0380c640300300380c1c07840c50360382c81c011010740d041d00032540407424401440a68001d650160101c01c00d8186065840d001818440c0300e2440303200035013980c0f44203c0703082180c8404e0480507020140c00a0304601780e07060003840c11a52840340e101c05880b5100c00010154041c5030000e10843c0d080d0b00300c916082c209020b000291000810580255600300008181540d42c1d0001d0013881c0213941d9080e0702c4880306256075004182c590004c0c84a0350302404004581c650003c1c50108155224488 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 79125586 1250 79124336 79124363
    0x307060c0806011b1209090e0f1b030a120c06020a0503070807090501090608100312020609010b01020a02090103081315050d060509060f0d0804050a0e0603010f0e060a0e0709060311150f0304 83
    0x1c032120346c1c42c0c2e04081070440c10448805981c480004581c4950990902603078000fa442010003d107465003260020f4041d04800030741e1010640440c100c4070081000d00b804002c8030940c2c1d440a089900c1030b400d50b000f00d84040103200940e81e21100e02c95005880d42000310481f410000041c000d60700350312400c1c04000f0003400052502c0800c01c4010000e591008008000921445000e51254012981c0d40d075a0761038410090001e610010301c8601e602d401402e20b02150b42981c48107101c0c0d502058820343c01d603040040006001084081c014440c02265513060703150326480c0239a40075102c03658000e070b210b2260744080c4542986c40e40307d074200800040707500c24405d40c010f1412084500840d444190300c00300020000600304807030780c0300c14468032040700204000c0700b41e41c81c9030701212480c161400417640140c00090b0742c14913a03444891050b82d1003003119130722aa1a101201581d000b030304100c42c04404003c0e04009410100b4040b140c2d803904080c01404c2030840440409680401000604240f801000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 79126836 1250 79125586 79125623
    0x50a1806080a050f060c031603020c010e060a0c0e0a150305090709090606030201091203090501110703020307080307060c020d050901120f150806090f060a020307030e0307060c0806011b 81
    0x500028039414094a0b242d280700d08000d901c44214291411450081400240700c048101c01101c0c030590701c40c8007039485c030304541781d044009400c82c86506085640c2c030603c54460200821000d480344031810000714100307808100c0101000340c842080e50140c443c0c1c12090103d2150540380716144022890001110b541e0204850b10786000741d800406081e00d048070702810312900350030078070649000b0f8a41d1030030b00da41c0d803c06c407006885046020340003412103070081c0119841040c1e0301883c042110211480b00d134407500001d0070410580d0040e1910f500009409080000d5801152010507860000e440180e00000002d4881d100b1004094100241024011601c903655400b9404103c00c03940c04000800d0003803078400c0d10202600039121a407183c02c000030001c0710009482d10040f45094080c040d00d8039071205400280d0005000c2c00305060301c0720300c1244031031010000380103c540070361404100400f207110047c01002002d0704603070401c520b12403103410381410004256811503101c1c0784900c50310107242 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 79128086 1250 79126836 79126841
    0x30902010c11150c07091a01050702240c01090512070c0e07030f0c03020a0306080105060a03020f040e0f0d09050f09071d0a0f03030806030d0c0f1103010203040b07030510050a18 78
    0x29143d500d450804110807408600004550040d1141d172102084000e000c600301ca8071900400190781e001441c01c024410042c1480450902c0c04101005241144c0665108007203141c1c1010b80e1045d0302341c1d0340b0307002c441c00c2c42030801c200201c04003a1090545445015203518030342c00b940b401640c00c622901d0001c140d10920940c4900b1868103011010002500c9040707004000e54031089107040024101a03010036100810b00c10103000311001000440381d546981e00348027103501c50340d801c0c0c3e5001e80c0c0c510150340b591320180802004020f40782c2c084c0080050b103403801b82401b003440e04994065072003000d44103080c1e115680101c0d000314031414071510f0960801801407414403491031881c0c119402000020383c0342c00c44c074420016640f00c1d864030380c21070391043d041c5952540c0d03101c58500011820040400440c13030821100500314010562100c404200c03802103030a99000307a0f0308645c10301305041040011945403007002e4101c41c1940200c0340041c07403d8005039010f4050300904020348007080d0700069118031503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 79129336 1250 79128086 79128109
    0xc0a0c1203050103021306141302070602031f0b070b060d080705010c0207060329010f110d0804060b031504120935030408030a1d041407030b01030902010c11 69
    0x24048a1001034a00c00140034150030f10040380107040a81c4030800340002805080203554042c42406100749402c000c120344021040c0e0ba41005660812440c8045078181c00150b11600c0400e0f4400da001031103209119102d0015404455008800c0c000040001d9492041903040502250241c601d41181e0a2209040c8100d440c0200b4035842e001003d01e110740c0104081c02210782544040004442c0d608502c0107001c0c030100c0f01c0c00e44400408a020240d8000c1031045801c80c103034508a9a60807140c00300c43d2521021941000100d551641044100801d5000b0541441000c3c2c000c1c020000387c2200060130302e40044c02c001c040b12140984c0145c02d0f880391441d0001003242004504040c1d0101543d0a103080b0f02906143d280d500070f094a003804100041103d00b06c440c060019807900d00b07145411a50310712901c03011141892140c42c1d648465a0b24081c3d90080140342410b4005c5042884002c1d048411490515060500b0000c044026070f0300300160001050b081455080300c00384440001e80c4040b0305 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 79130586 1250 79129336 79129343
    0x15060918010c03060e0604090f15060b0c0307120f0e280308030f060a06050409110d020a030b09060312070209100e0405061605030f0109020c0a080c010b15040e0c0a0c 73
    0x2e04140700e150300e905800400807104440922003035610303101c041c4070544001c0140504079054804403440001c1c43d50390721007040781036102c000405d1522402041103132350104010804603807011801c0030a01c80007164202d019a140d003801e0401c0f42c51200b0141c26400030300c81c0140b10703416459400b41005021a10a04000c0d06004901211601d9160400440d0003d403111091002180f000862608060348120141c0f402a01c0341401c003468800540c014060802000c24480400e002038605000140090180500151004034015042c81d0070300c5103500d8010b011a2003540701c0041e202101240804035084240c040d10005159913441004400c040c2d83c90f413100e05448032100411007031003008111140140d141c0e00844100b0545c0348011641400181e030240d416851a40040000350340d141d00412501c541241520001580c03500ca1031115080022010500d035100c0304c0c0b20345149000d00007284880c4644090a040904140c0c50030550b1000820b2940e00160000c0c000480c03501603c1c80c00cc40c10392 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 79131836 1250 79130586 79130591
    0x709080616031d1c020708070e0402190f060c050a05030a0804050d0306060e040b030a020904060c020106091a0114070602030103060b0f010503070c0b070c0b1609081506091801 77
    0x10681112004070700601d001c0d200281c0f900702d9054000146000240652195800802810314840e841034410f40076070f29400c0a61140b6a000205090305001150090808592964031840c2c0b034010700045c03400d044180d00c22001c44510130b201940b6501601781c00e0341c00600e040c1044c00040e14025190155601c03028105100114075a03c95950240a0511981c86441611b0421400c403009905840c11070081c1d4020808018000b04903080581c40035500d03000050884030919080d40104914074000d9400751030090311080907010840d02401020020300340e004003000400f4000f280d0a1020044403041ea0400c040b044d40780340c03000c22140c141c135403c07a0414401c5569507901c0ca055401002040c98081c003500c441821103600b50700850a80744902699202e00000d01403690b24dc000f2000000c0900050040c483d02000105400120355440350312411450461a114030a01030000d0001f0f0344800e10b280d110b403940c1c01c0d00002d10207402d074103d64155054006910b56030b4000c408040c0c041c03e010065807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 79133086 1250 79131836 79131841
    0x30c04032102010e1b130f020c01050708150117070201060803040f030b0a020406050d0903050f0a0203043813150305040303051f0e1509040309060f0302030115050307090806 76
    0x16a01041001c1c112810707002004840c0844200070307210380f4078103210341c07019980c191910341ca410f01d0444000c001d050940009170080300c6401c10401c03030304240c1828071340d03a54403810004810780050394190450840d0305005000c546207000280034010b81240d9a9080c3e161101152145000350400005803c1c900266074455842e40607041d4401094401942c0400c0e000300480c141480520031901940d400b65101460000d0a008101c05406155070840401000300415000390100130050121500d203503010b16662450805a82c0405d034007000b1007041c48246d0341e0551010028180d915080c180d445840c6034540043c4d20070180301c214940c0c840000081442c4038410031903070684c0860b10442c0b1a80301040f04da203600e03c0007003000c40911078107108060211020700507180c0b140442ca520450080c0000303c1d01485401140071200305a80032004511400d905019450300f100c518444a003591a04604540c90000021000c160607078240e0140318000001c150040c0c0700e082654040d1900c0e4040719003a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 79134336 1250 79133086 79133123
    0xe0102070b090609070605121303020a0c060309060605060a02150703060e010306050103050d0c0213020c01091502040602060c0a0c0b060d020a06050d0b0301060b0702190e0412031103040201090308030c0403 90
    0x210b0f0300301c482e40c0c028000c0c0c40003c94028081c0341601c4140c107585401e07201c681d96406c1c240400c40c045403020f80a51040080084c009100c0c020f824000c0c0c2000c1d80d0214000b005407614070240d90568001c6449010207200c100d111a0340000c40016030021326007452215121050207038010719481e001300b04002c1c0d20000100900007181c2182d8104d070310403011500898804101240d5034140150000d6212220256900c8121041e802030f14094103068000201803c40b95200146003400d00c1c0500303581500403030100b080b141c06100c1c2a0740251104215490309402040042000010706401050965860046400c544036450860035499002c0d000d4030f03145c4e48030b20300940f2030781001c0d0034584424100010015030b400c1c103005040c00c80d100c805031281000026420031001c40c464088040a60040c5e510004d0a81040111140924083c00400301207903c510720040a40d00042031010510000300f00b44030041c0d900184c074204a0360001216501d90b10f524081190922442d8400707400741c5d02c500c0128520 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 79135586 1250 79134336 79134343
    0x6040801090f0c050102010c09061805030712030f0206040b06090c07051009020f010c0b01090b06071209090506040504080a0804031e031a12100504020d120e120708100e0102070b09 79
    0x1c143c000c04420940319562001203003640c1c140707021100003a034019401c10425000b110480403907449224100400768030760b404249071240c564400d0031490f00c03200100c014503402c101c034025001400e1024021902d4140c46400da001c101504540c00b40d00c1007070004178000a80400e039111301e03500806944080340002c050758082c10320303540286c0c41020303050841401503016005c904401c0e03520405031601a0310b0080001b008004420b82603401140801804000402d000500f85800d2035540762006040c1c00d00707854800302d0340c0050400380078520300400d2101041d0788034160b500d4488540341560346a88d0b1454115080010107003001410300903507a05011540e09904200398004500708000c401200000401850041550707012103607411004000000c0e00c62034100551040c0060304040a040640e511f1001e00d44490311307100c0000d4200800781d502450446c1d80600a0800a401000751508107810b0381d480e4901704500001d000d9584442c0d0305000003e40507900d0a54012004500b14508424075686 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 79136692 1106 79135586 79135613
    0xb180c03100b030a080f0c120a0504090b0a090f0e1009020d020111120325030905030405310b010212040f06080604142e050612060604080109 62
    0xc606081c006180d081b0003141c0b190381c1e815062a6250410450002280951104001d0300d010036a000c41031300d054641d40c0074001080380304440015038003031450744001a410308240b400718214142c0c0e40000400c03c02081520011074a12500c98100c4115080c002d600400c10b02d001da025511902c1002420043c110885800c0c003403250301010150011a02810081240385507140700e00000024080f0209050509000500807a500c4c00e40f01c1c010341c06414020a240a2416021840c0c0f44190794000c0c01c11108441f0f00c3d000d250608042d100010300c050151088100c4002180007034421503040340c4802035031001003030401800325046480645125480b03903d84a58140c4148a2000d580c013508013003242010312200207407054280700309100d01105001c8070050810803920307000d007110003d001c06052140c0b242d640d64000380d00c50040340c01054456103011f041c141040086080200d = true := by decide +kernel

theorem cover : BRFrame.Cov 78956836 79136692 := by
  have h0 := BRFrame.cov_init 78956836
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78956836 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 78956836 ≤ n) (h2 : n < 79136692) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
