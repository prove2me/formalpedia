-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0233
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:38:12.417454+00:00
-- url     : https://prove2.me/submissions/7054b421-4a37-47c8-8e4b-c7c93d09d71a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 41726623 ≤ n < 41906479 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 41727873 1250 41726623 41726681
    0xf070801150e09070e1005030601050409020c010e0106141201110d0203060a120c0906080f0d030b0609040603050708122502010e030d02010e07060c03080406091a0906060f0a030506041104 82
    0x35280d000400d41c0c201d1003206e00080c00b55824001900c000780464820f101c14412140254090202d14010704000b04240009414403407c44105401640701c101c56402c45080c0ca06040c00d500c130b880000f81000f003001c101d29600c03465043c01080310540501e900040416003959814000320b01801c5014901030105045140c20294400d007403040386122400c0ca400003a0071840414040e40d42540d0b1005080c1091240104a000b00703901038243c2e503c107200b4041c4941c03c1d141c03445641b001c0d511801c02071584504003860b0600c0c1c414500e501000d40d0300b08000365141000c40c403444445662402c5900400d00c0a6440140c4229840e0303600d4a07014400c161034800e1481c2d05400050901440b801911031072a117a1000701c0d001c2c0e0b089400540460071036404180040d0050380022040d5010702444000c1d070b0050b009803201c0c1207003a101c0c4a585d80c0b0503c20320901d40b0b4040045030303485000721000d44480f4035541d41c1944465000380007500760704085130400307603685654001802141507420301110220301c0c4010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 41729123 1250 41727873 41727887
    0xf0d110a0c0201170906070c060f060303051201050607021c0201050708030408070b07050f07031209021203030703060e010e0406091a1006091a19020a06020d060306050f070801150e0907 81
    0x760700041300544410078020103280054010500759001d0030b0346c0e903110a425120250040e2040341e2050342d510350300071480203610810300510b20036600c0c3c035940e4080b007000d034005040c10b800451113100100902c80c0160340310541d215214801490030b05401c00f040c00182c48500074610054030240f8004100003c0050000060034003e00c601240c90044d00c0d40c0e5000c99060040d26a1101d41b40c03010420394000c00c0c0500c4034441c2e500c0c80c20381e000c54120242c0e1b01041c414407420200c003401e0742c1b010041c40343c10350301801200c01a1030000c1c5051200c1d8502504004e00c0f100141c409010159120810720500403006c00c1c5898018140d900400241494803026501c0c0040d445004006280d500340404d02072500001c001030307407165030000c1e4140382c2d050316031a8140ba280c4002a065119141e10700c0c0008803d80040e04050600c01c0c0009110762440c1003100982d4070040522900e0f490003010070182c25000a9200d0540c1c07801c040f503082e0790781030f00d2060b6400c0306021100c0c3c0d400740c0d40904005810b907111032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 41730373 1250 41729123 41729147
    0x10902070209090106060813020d021203070b0109110406030b01230307020c09040c140111060403031b030207050a0b0615070c05010f0c031b0201030f05180f0a080f0d110a 75
    0x700b25500e540d039964041d0899095026403000a580d21011920020034201c0b4042400d000a0112000d08503a42c00201c010104450000e170035040800c40302c1c2444041c0000380d005004007142400003401100920502e482a0701618080c10740d140720f581c115074031801040c10486120041000007014402c5104425081180c00100610502d00220054102580c0341c0307018940c031036910f124890605482030910110001101c0c1000034000921810f42070400c074040c06a4043d440000c1d0f0722123400d000720740d500601500c01083c540100500c00014400140411201e0380042c20981d10fa101c2c030000075651550340302c0b02c2d00c0450300800c154045c4289400038004540090f00d844607101507003081540ca4500d0b906014001c00c0c000c031203109449049065082040c0d205250001c0c0c08074249005404035403003a1480b04070549104010030518408100c455501d0f4108801407103031502d10ba5034070302948070720700c40c0c0e081c01c400100d008891040300340c0144181105c06021562240d0300d0b1540100045850f407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 41731623 1250 41730373 41730379
    0x503060702010606051e09090a06090507050a0f110c03031b0127030e03010b0405070f022a041806020703080a05011505030a02030702210408060109020412170904050109020702 77
    0x2040c035441c014890002201c246440300d0742045403040389448200f2484260307414101d02041503003643c1d40e0714000948a20185000040c0060034100c00d00c0407100000c0954060040400c0f8001c8115004080754421016900d010003403078501008107070521903006400ca802d4807012410040c500c400f104440012544040200150380c185102518200d216040d58114041414181c4010911a140b4403070f0300c40d40138001080c0000c070600443c04480040762780100091681c00d8040e00c60354180704225500703408031003a0b00c40e90720a20410f1407008603180c10324455603032070042e040342e07030903952880702002c0d0402c45c115245c4606060241045501b103a0003164145048000f01e00121203020540241d00941c0d1950f06640c0c4101582d0004d610180498096214074646440c03000480000c443d003032010384100a40341c6280240036403800c1e2040c1c00080d2a64018441801504100100a60505c6d000b102c80800c4885a108a01e09481409041a04142000004104144982c0080c56201d20070303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 41732873 1250 41731623 41731633
    0xa09060510030f02090a0207020a0e0403031d06060415080307080a02070909050c06030a02091e01030e06060906270702160602030c0c120c04020d1d07030c03020103230a060503 77
    0xd4a0800d0480c4090302008080d03c10188004002d0304240c803c503a480440004014500215900005c034131401d1a03200701003401c0e00f201000b0401da45401041d48001e10440c28042d40c50340051419103c49004144900407560f411403104e000c0d905109603c000d0079641d09603503413890981000340785a840200244054440d11100007210943c0703219800144e90402c003d4407032041d00004208040d8030144c002c20015800b807041e40420b80d04e41143c0000109201c035041c0d104c0750000005000e9580c0a80c01e10416004402000f2451300c41c000703d281d110804440c0a442d00740d1206502100810f0794010040c400310280c10860303900c0d00003401132598201d00d03110450f9a5500e003003c0fa624440d840d1080d0a5030040c1102a40d0743c00d218a003038011910310419115010302c1c10300418101e0300003c00c1c041c00790751210310407201d07070b401480943c02e840d5503000500042821506d40400c141524840241096941c800c1100440c1c01c00038140312104480c04240014201101c41c41c0181c43c80f801160300c03c0c007035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 41734123 1250 41732873 41732881
    0x3081201032102030a030218031005070e010e060f160f0303051f080309040b01031d01050117010b060f070804030605010e0402181b09030705030d051b03030609040f1103060a090605 79
    0x401e440c0314070800d141da000311310b4100002d4044003c0d4100e0319030300b5040070180141c21100e942c01e1141018184a03014009244c3c3341c8500000d001e0007903040c01605010214900b03803155180c000480320a01010312a40d96074644041c2c20010106100a015004030300083c0d01008056050300714502071403003007528000c3c03820300c061080d012511074403c800d400d50042080c54090f007440e4101c180d611205040000d800d0015a46a000d90411048680f0850b50744030018000c0c040c80380c04c1003404180100c020400d91740700303001054040c4182c001e90111b40d0400708480040160a0f0200c8001d176600110038001569901c2100c00d11200c26030b8100c0c45105994004040072030341400040c406c412600c2410b0108030a849642c80755405148010782602071039201140c180c504020840c0380007030350341c0c0d8680e41c0c103000c17030f103250182901003400100e54000300700707205c1d05039100e1400c1608039070091400354142c0c50b11b140c026120b450314044203806004030030420103d000360750310074000c49000301d00c10b10a642d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 41735373 1250 41734123 41734163
    0x6031e0601090c260603070306050c09030f1c1d0607030804110d0201020613150c0804020319080405060903030c0706020c01090e010f03080a11010515130903091403070308120103 78
    0x141904406003928000c0350844028003440e485aa08900b011b01981c01c40c94903916280c040e07178401c892501005000080858442c1410080c82488010300301c040e1600c60318107407610800c3d9030484007800422803003410441d03400c00100812010241c00031f16150b034508540c034001e40f6003d800c55040d500003409015418650400100b08074000341c4c1680501455070380d25a0f02c01d12842d4221054a0407800da62818844011034841c840144d80d5075150300b01507240034030426141c002c500429501e200c0181c0550b0000400e24001e440542c0c8086036078586811480c400300380b4500030814100d40328458010000740e283e03004980140780640a0761039001032a01e0744280c3c24090b00070701c5416070300c03078440c01c0c10000f18904c60060090701a540c0f0307043c4009c02040e004c05003505d2049e2028025540700210401c95031a200c02c0c0c0d4941c0b110102014461201141c03400380291f001780c450580c0c1e1001498000e00c07540d50034000f503806141e218201c3c5444005000f86070704840e800b40012104e02d0826640090902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 41736623 1250 41735373 41735387
    0x240a050a0203040b04031d131401170705040903052101090f0e1011070f08090301150b1e0d06030c090b010302070818040603020619021b0102030406030506031e0601090c 74
    0x4d4129402500940b11642c080751441280d50260199485101c03500740c1c1a9107402c524256414400c1012071201d102c0454078035462010380c069420803c2030a005905460007203404011510101c4000448203c2c80c2010b0b5140d125150001509620f0600c049041d100ea02c2c0f07440d810f841e0040c1e010407038100380c0300c000d008a644c1c524440340d240e801089a010403101a402156500c60004125400e00d01d040c0d450701c040c40c0a40c4000c03690b0420104d103c007481e043c240302c0c40d1542ca1000b02a2a1030f903141440340423940c0302d490a6408023442c01c140c0f002c40014020212203030100c2440d02004110340d03034108a51325203c04e000c0c0ca01e841d07050840c912050b602c64001d8503000d9030007044082c0340000c0500c48461001d0150810364100b03072140000005aa00c50026220000d16000f804580318030515000f41802c407100e000501c0143c400c040e59001d66400801c1e0340589100d0f040c00101d0740c541d20300182c40c040501d1a43c000795804580907a02c81c80000c1082c1e412205011402e02c9070340f010a905803051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 41737873 1250 41736623 41736631
    0x303090a05040b0f03031b0d030603030806091008100e0c0a140105070c030f030509040f0c09062d0e0117010513020304020d020904140d0507051c02240a050a0203 71
    0x195400c0e814461882e140d4407448140c10020050036138030900d007002c81e0450f0060460818808010640510030500c18042640a80d200d032038100301d61811654060a03009020f00008d000d082c1e07200015082c00c06540105020f007101808070340f1031600c00310001c0080d24144040000c180541a0748101030b007001900d0100380c89061151042404210703004641c03540007903c042d200141101d4000021411180c06a000c10b4040d44d0380c0d030741e0380704510184001d9a001d1030021001c1f524049422540300c1c2d01c01c9180e000d894047c40d040d010aa40c00b00811000c0d040100034405040180845901c900d0300400803541c004803e8032080e15074a008502000340b00350900c02c030b0b46c101c00c0d2501642c036200c200380c0c0195842880203000c0d440c20010b640101e40410b400700c0d422a440d1300c000d0f854102d180c4040040c08001040b82c9800b614000c0140e45840c2c940304400300611154455140ca205907c0c02800002c14682007610a2040b0b0003018000030744a07001940c00712120740c680390200c1c403145002e008072845 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 41739123 1250 41737873 41737879
    0x4050c0301090b010c1502070c0b030402090103110d05120a030507080c070f0602071a091018080a02010e0a0b0708010504020901320f030a060e07080a0c020c21060105030309 76
    0x440c2c1ca05034209001d0f11140d81418108000340c100c400000388145000350302c1803140600182c035040f4614000e0352404250308588182c01c4203008010060382d80c0640075056a620424560a0f20715200104e442082c0d00580149280a5160206501c8103d180034240941980c0d800780708a072102e07402559032203010b4407140070400302000f0031404158003011a41045200700307001803500b1059141e200e03c4402c09104040003a42041c144509401c0821000508042885040002045e4901e1900058141c030400400d2840045190403186000b9403000304030304002001d5a0a04d9807034a058114030108035400e00c049194440007003000e0501d88284c481c5940c040c2c40c3c0c101450702c0303030350340160200c0991022020001500200b000200301c04025141d40c80b115000b941c0c80e42403080c111000d030703035807900420010424170301082903480d4031640c0c1c0d68001000000011340300c4032440c2c0490402030509182a0018036000d10803541c00c0f4055510072003000c0c0c0350140c460507602c2d0b40402d901e80c400c04d0b07a8940c4c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 41740373 1250 41739123 41739127
    0x4030f02030c0108090604080702030a0602040801020901110c010f110106030206070302100c030614091506040b07060f1505130902060a0903060c020706021b030c150a0f09050306010605160b090708070504050c 91
    0x1f00240e034420040241070b000804461061619a03101001d0740d00c00d81240c0d280381d401181c5210b0558214414100010700d04016100440302c110009045a040f0070010080100c0540e03080d5241b1400c2d8800c0025580151100e41c1d00c07005800c01940d41c0312464012501649040081c00d0101e1080c4949002e0f20b44072030385100c0c819600410412401d401410210300b210402800350001c1d41d03102e000f04000d1006811860b103c0c040c0d0b040c05030841d802d900c4000512400c001d80501c0c1c1c038900c1e600000981e04102c400c4010720010620340e0780101051100290803040000c0c1050060b43c11040e00c00c1182d104040034442804d81c200102d859030010301c41c079409644146030034007002c0c6482d0002c49a448002d02201c030341c5000b680014030113603403c1070910203c1d0000030b0805151580000200070465260800522051611000c00d82d2141c05100f40d0040241c041590244000c25501a08200e900044060320754201007044a4540290b446403501c14490080009210706280c0101032042c8440340c0d91038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 41741623 1250 41740373 41740381
    0x806010603020904150806060301150e01120813122f0105210c030405150103081206040f09060b03010e0a0201020a0b090f03070302060609010504060302030c150c0304030f02030c01080906 82
    0x600650080d201150707005840c0e245c3c0c0c03541d0700d8105090f2402440c8550051595040090905003107030000d034400a88440315900a011140c49100c031241101d40018001c0b00010403130030801c2d56805034891122115000100003e001d0700d21199a00001e40102d500503c00c90421b04142100c45207090b204400d00380780d07a901d609941c01a4042d0015011082c052040040d00c400d80007800c4204440109000314088140000d00c003082040100320f03000034107650a194107507150a2401d006001d0050300d40350000b800604992207036084440644540784081c0808006440c1039005407600c1035099000c0e40c80c02f0613158036844001080c1010075011b801078107406402d0740300c600c80e1030002010340c4c1c400d00c2925290001140d0030001042c034140aa40030b0a41c0d41003000c01c20001c0030f410382c040e901c9181030000900159030085400038907070703a044881c0c00b20107051002c0603545018500451a0b503000100d0000140b00034040807440c001d01c2141581d0844890782d0055500501c00ea401d1101c41d88940009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 41742873 1250 41741623 41741627
    0xd0611030a061e0e0a09060e01290a03050a061e020a02030c0c0405100e0a06080a03090602070605041d06010908030c0106031509050d0c030e03010f060501110d0f050a050c06040501091b08060106 85
    0x14201c1e1a0047c03001048a4201050090075100511000b810501d02100f5200040c0031180c040710560344220391650a60349103440e695503c1c0e41100f0003803d040c1eaa100003510307a038000400c005001c0f440d40000e6450307038007070740000c1e44a030840040d4404a0060109101d1145003922582e40310701214481038170101e040c0480c890348024010070b1144c0309680c4410105890200300050071200d8402c0d41c0b446100e50038010000e00300300321070388860b040c41800d0000b80081801020b030a40205002100b5640650f0b80c8001210a54159840100603000010790825814010b400513030640e80185030f0403a520ba01d041c0c40404854071901d02820a802c61110602818401c03030200d40528000d2400300c841c208100006404c44442c11007185216540b94010802035801c00050121540000041c00c0c801034044005003015030b040e00d1040820200080168800e070082c81500d6681c0296400c0317654600c2d0a00d0094000c2c01003070400d4030791000302441010b161590002000030358401c0405000d45920381281 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 41744123 1250 41742873 41742881
    0xa0c020102010b04020d090c0902030403170a0b1801080d1e0f02151513051003021507060905010606140c030a030213030f050c01031505010206060d0611030a061e0e0a 73
    0x8904554940c2600e8400340d4942c0090540381c40e51060000d0308285928089628898039030000601c039006004100200e41c004071a48441c2d654851140040d61f105408240100106144554007a543c00c0408000344404101c03e4180c51812084400c0d03d821082c0035121010f0027908035030301d01004020312400380d11031141d010407600d09004982c0080081a504e084036130044840d008032a81d81c4800c8641031414180280c04003449280801050a00b2010015040000c0c04040c1c0079105820312100d00501e44011a4521038200c1d204011411041c902140608454808c0000141c05070b408d00c0ba80700d4140003118400d040c414007c61410703800b11000d0303003e50401158081c5200000700d0000c041504104121a0184640054086035880400240884905079030390ba00c940e542420030302140c0d070005003540d0010022100c0d1507420090340307001405440d02c02032104d1580c0e408024001811103a82007203040e2341402c0c01c209840c1404628094104019104140002000d2300201c1d40301c0c41940e00c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 41745373 1250 41744123 41744147
    0x6050f041505090403050c120702010e040902031903020615030c09041518050c0414090a03030b030309032409120406110c09070509090606090d021009031205040305060703110a 77
    0x49280030715956000280d04001c0840301540411000070355244000300c240194058100e81443c09814000703a90002031072148890b4080d8004c40e540c4044e02c042d9a8200040d2090340071300c4c52406050304d9145402034850406a400460744000e204000710784d46004a42c20000410180c0205890350b03450f15001c21074084038500700c0e95aa503403807404d205607041d2034811062a0140c4003c1004048041c14481120000340b0000c1c1c0209030242840341d1400089548141d10342c16281c00300f007515110000904512562005039814490498140c01000703200640307200b00d00d010368224126544044400c1d407281d241e4210800c52403c2080180b0400b07005030032041074800300c0ca040700d4600380360318041043c900381030721743d0320100304042401e004500d420741c2c42503400344060350241d04080c0054003090100802c40b1000340701e4056800c815803e14481ca117403400841d00490703080c01110224102902e15802030100342da03603000300000201d90600901581c0c0070304131101887c80c5448055403084555040d004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 41746623 1250 41745373 41745401
    0x51507031107230406080705040905030409180308010602010c050406080411090a050a15140103110c030301060507020f100c08030a140f010504060e1006080402040204091407020607020106050f04 85
    0x10340c011100354400c02c240b5001c1c01c40500c2006000125070303150910711040d80c284030311442c200603090045010100e141303800c0b60425200412211078629106045004a40000b1601407910f00102c0c80d042c0048841e40c03100f80a44ca500020340d8a40c1800c030b080e01c40c4007000c0e0001c200100420003a10748100e0100340e0142c0a0700d01820760506101c0003c1d881c82060f2503070020b4035140c0090015519a62084400f00d0b1862030b882a005407600004214480020f000716052595030100360b1440f440c0741c0e00b00c0d500b004504040d030340e50f5a110034020705540c0040174240e000f040c02d035103030302d4182c180b5410850a5a01e161614151608182e0360400203900c0148900c10301038881d11813520307194401035090b001d0f26450b1654420766040c2030901045440c01d501c29101000311030148581210146958400c0c1e034000d10340003805a07914000308000c4c4c07080354050308000d8604903450326111020f10816010794129800d40d0455100c040c4100d00382c0c3c030140a07255102d03815440300c041624160303210030404043d04d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 41747873 1250 41746623 41746637
    0x90e060604120507050f0a03020315090a02030316050c06030103050303060f0609060a081806041e0c0e070201020304020a0f061227050a031202041404021c0c170903030105150703 78
    0x10b032400c80368034800c01c14101c0e42da0748070500c10f02071031030708541e801007003001a02d044a03290301d540c0020755202e043c5a404031400c01c00d10042890910140034468a07107402804580c0c3e031b0a28410f049207c0111b03028240c405004000f509030091801c042128105c0e03030084000c600f10f850301810010151407070a88103902142c03c000181480d104c40c4003800e9038000513104c098807880c1c1152041c03040c1515004202c4990041c40400000483e603e090050f0170444403c0e50482d100d0a10740f1450802c407176000301140e299a4000c02c00d200394150001c1d0f2041e032080d03980280441d03480b05809003540c5603004140c0450103494403a000e0402e254003c03040182411520545005041c50810041e18525000c0c1c031390f90009207203c010300d0f41100200418400c100411807419141c46411502007840081441c403454002030034190314003802c0810f030314106001204200800a548000d85a20394042c072002c0c1c0c0c2004d500003d080143d000c81564100c5001400c00c84074154290707100100790b84004800c038103010407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 41749123 1250 41747873 41747879
    0x1050f040c0b0310050406121109070203160503040906090209041503020a060e0402091002071703030403090303050a050c070602030405030d020105040807030507080403200414070c060f060b13050108090d090e060604 94
    0x1540250b03030084c40b110011440d0030085041442e41d03007075580910340c04ac0b54080140401c042d07000003240c01c26000071100782110342d520709e42103096201c0c81d4040d4000c1c03401d1840226510000754000e005185048804020780071000442c0030140c140c074417000c0d50000d40c48034108202030141d006032242d80c80007000186000050340c0020080c8404911410042c0e2180c4000d02002000c40902c48000030044000e40c1149072540c0c00408070700300d0b400014100080891159500f5000380c1c1034a094010b9402075810b1306440d042d0080da07980042c40b0307041c4603100d841000c000241c010f10a03503000b650800c0c81241b500401e5203042c0d440d03500003802101c1c80705007000000041202d00e400011410103544010355444211004c0000381c980300020501c80d50b00310001d0040f201d800c0460400541d9001c0c402140c65400c1e600760a00820943c0c0c000254840002180e108009540d0a40019030754244c1714a1461380320698650f03590034401c03000d44045910824140001594526843d52108005040c0c0e441e20b44c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 41750373 1250 41749123 41749129
    0x80402011718011b03060501090b030403030902010c0f05150604020406080105040213051203120a0c020d0e010905030a051011120a1a2106060301110f030402031e0f01050f040c0b031005 81
    0x4080075145441150544d039003070800d5060141380010030007460042002c030b080c03036803c0c8450b1001410050a05a40744044e40459005078081803032250070441d802c0c9102d055061180e00c40c00c2c645000f071022401ca500041851420303100740c0d0252a01907a901d501b40e8200414040294841c106000c50440308201c00203803070780c3d12104c40781c0c50f9000070007650700d4820560401c045c2c4603004e0074085a15040c074035007040c01680042d03803006131802407826816095040e0b0059801e039130176410142c0c06029600d05502402000143d03240c251605140030885420340501c502d00310b00030001043c0d070260040340860741a0103203410041c80214214000020b8200101c00121081650358024030360301c040c98a00f40d80700d80706100d07045e4420070075002803000031442e075102e41c0307240702d12018205071840c084003140546d01d040204017039003881c80f05a5200d14186481440e40c60b151701200c800e040d802d010014208040b159411401641c0c030a05503c1054100b100103103490308000e000411900304400d0001c1c03659 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 41751623 1250 41750373 41750381
    0xa030806030c0a03030f020c040603020f1c05031b0f0606030c060a0203040b0307031a2413090203180613030c08031e160e1507020603131403031608040201171801 71
    0xd4481e81b210f0138002d880f55006410049810002445103192140410168942006140c20802c00302c0e4440380301d940f400c2c110040c1e0700a00d640038009200116210200c907000034100503100c4c40007808c490305600d41c0d440907982e4450842c5c2c555010b42000e140c020081c00d1090203400e16400c50b00680b410541c0b50002400d40380c000b29011400280c9589408210b00001850f8610780034003555001c5440b000300030303100e41c00e607800910551045070014604002c25072400b65403026040c01c003400d40d80c84c1003451112300c0500f190044007a0724014400496000c1940442a001e035590541b181407440c2038684038990710340c100424035051400080c4090454124020b822441500d00c0154404c400d54810030040064580d0604da41c020201034900011880c005005c0c0c0308229411120540c2e2640d600c03019011440591500801e120000c0520502081011014520508001107081c0306c03012000001c540c050001d0391b0103030215071840750b03406c0c28050082003103922a110304411501d01c0031003c643c508507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 41752873 1250 41751623 41751629
    0xa030b090f250503030c07050f0105070c0902040f0b0c0c04090816050a060507090e010b0711060409060302240a0e0a17070305070f08030f0901170f041208090a030806030c0a 76
    0x103000d8101c0360808030b40d00541d40c8003034142500158100020a1000c5680e00114024a8031880359440300c010702d84e100d04219806141d1181444030707102c2d43c2e900710002a4215000b118400c0c0035000010604e402c0700810b90300caa40d0400f000700a10401002800f00900b10040b00382c9001c6001c10401d4106900c1c0d2684003d018801e1006014480c1c1c00e08103507040f034038080c00490070404403000400030140400503850540740200c80281c1e4400c2c25140140d1000c1c0c030f101e90582c00075000309000842e9620340d84070f8030450380203507848481007100d0309103d0184255455100017608040c001074074040d10603080101150005003e14a0303281c0c48541060500e12104103c400c00d50250f030081c0b0411000744035040080c0300a1000841190400400075164001d0084140c034141021a5100607a84200741d20903100d003102d285a4802d040202d03000c00b580000b12015540f501d14040d090114a124518141c07084a1510142242c0501c03580d080b54400740c05005640c2c90f100321101c440180d0f88071585a070003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 41754123 1250 41752873 41752903
    0xf1e020304081b0321010602120f04170709180305030a180203010e010b01090e010509040807050102280f0c0b06040c09051302030702060f06060301090b010201090c06020c03070b090a030b090f 84
    0x300c80041503042c10711982c0a00121703603030824070010484c2c1a0002921240c107052820415101c07652542582028001d942c040324030a516500c1c82d8800020218031742c420b0b2030040d0000c0c400304d602904515010240d400000703001850404c002100102d2a60040603030041c3c040c90a00071a146400180c2500c07403c008080e0307540d5460410a4080d80c009034504000e0858066200c0315602d08400030b10004070080000e8900c3c6400180482040303400c0d07040b6444000c41d0a100d40d410402c080e010486103002ca18001c001c1895503640400715801280440f0b00e131544290903150340e07070326803007808054184245420280300c0341101c0070030b0a50782c1440c0c2008000890380300507100d00d402c0030000d10b4840301034468810540e402085c00301d1900d07424112419550b114070042a600c24207070040b03004010007000139000200b40320010031141d41c0030600500c400700403006c440340b560b10f500c403600c010b128012400d688008040400c00c00181840a00c3c0d6110300d003002641c680041020600d07060503d40020444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 41755373 1250 41754123 41754127
    0x90b0708150d03050406170c04030807050304090624110604020f01020106030b13050705090903070209060d080304031718030702040513020d0b011508040b070c021c06020309010f1e020304081b03 85
    0x4406c607030282014040ca6940f0807620010700300098244079a2041d404003400703030040040c2d200180328081080303d00404040313004000290780d03415900560b44502d0810316015140030203004645115100d4883c00044403030150041d030b1100c2d42000984030f01500010f06654030b40390004041002403280740d1049070800214440074541c1d00d0700ca8100342058000c1c901c109050001d0140f00d8400000f611500b96040d10980030a484d41b0000404445401c07000811100f030000c104010541e01c51140030700102c48800d014001d456a40c100c04050500d901a0030442d03000703104850151609400050b000503942d80e644050000603008100f002800315410785020482070010000c044009000e03002c00003040c501305199003001c0c1d0b41d800132044041e102d02c00f0441031100d000c040d903813402c3c0407a41105034220a400d0400e035510700407000c0e4104560a20055280407003407081900d00e801401d1100300180344101c0322003a43c0c200d40b8020b400c050000e54001905006d00a503015640840e00d199060100c0155 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 41756623 1250 41755373 41755379
    0x70212040807090b030706020a030809010204050d05010b0901050f0607061d0106060c0c08010b0d080a020c041508071502060106051c0903170a09200301090c03060519090b0708150d030504 82
    0xf20564280703d0100380a40d0100c03400308041070340400c004d4600e962500c0e0480054030f8191507240a8040d580000c0e49c04801602c40404210b8158050440440141e4826955070390760f004110703441581402551300104104802400034145a00198002180010709031508207022069821640103030030080105000b500a2018008010708800c001c200110091001101401c00300d0940c43d2a03c00040803e5800326030025424000d0059026031400644200200712200317003154541034587c480c00c29180504070b00800c0e8420f689411014081207600100081d03440d0403002c0f102503104003880006290010145c1d0441c40d0a802080e00850281c0d50b015140090400801c1c440030000c3c000305142d6140c10450000944501143e030291814081c000b5030202c60300c0b01080c00f502e00d50f0030060908080c44401f0003048450780c096405100390440d0501c6071010401c0308811200380c04000741c042240c0e81d00103400140700d60f085544c4800f465a161480c070550401054075004450012004208049824 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 41757873 1250 41756623 41756639
    0x601141c030f1e1409130c0306090c03020c031b0f030408030a080601031a010315120b04060c020610030204090c0e070801060e04020909041106070212011b03050105090609070212040807 81
    0x14440d07424444450007410f00382c004042c1c01d0420040b0f1044403107502084011259640110300e40014880c040e081c071410211a200400a005901400d0f00305c44c9440d0014000d00e01c00d20a4034419030413540110310f440000f10003400084030000d214582d0340700d05020600302c0356051019000400610008507103500e2141d00c058256000140340301d04045c0341c0f02c51707402c4c00751075100a0702d582007007030800050b03104003181806c9124030300303400c4880210864240c00c170070030085134145071003540106010490520780007012a22228240c6400c2403903294203070140054542607105805042c407820703e5444540d50b8608210758480100c5100c004102000300401625421185000502104482c114980000f0764001020b20002a001030043c0c84071210f42e9100c1d03112a412101d8554009003084100c0054611150103445420203003101040c403800c90189840c007a0003140e05981c401003d416999650360184019203000030807050440c480c060044441c0a0500000c5c800351000c200034000301404e11040d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 41759123 1250 41757873 41757887
    0x11d0a05010b040c0f08070905040c020c040c17150310050c07020f0604050a140409060905070f0e150103050601020c060d090506060a06020706051305040c03050106110105090601141c030f 82
    0x402c5014a040004015046602203122140e114007410204215180d010b801c5070700042c2c0344c1010707821074544503e110b54160009004a9103580c1198180100c4075061000c40344c41c000b0b140b003045039480210201d644002c1c030018581e50543c1c0502110448920101c2650540f2010303560000c644030b0008141c025420005200600b10300c0644089203401d00d8500031650103581880342042407012a02441d82c145d1320740e004211020b400c6201401030050301e0628030f40780c611134468241c2c1310314951400651080b0b102801ca200b40911030b1444400310b0004015009400000c3c011030450090b20700d420120f83d21a4058001c0141003000002d542445203441450040702400142c481c810043c4200112580001c42005a40f0384d03142554030f174a0200800d888180385600700396407250500081e0b403074051703266100030b04940345c2c3d0743c0311116823100b0300403242200d40690310101da9030420801440b850035070304e021128114000d4201908103c880100301c9002e65003003030488c0010281c240080e141c90f80486 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 41760373 1250 41759123 41759141
    0x6040b0406050f0c2d030702010c0915020a0803040303090b0f0702070b070807030f11010f1b0302190503060f0901091b020319140c060f010906080c01050306060705011d0a0501 77
    0x60f0400c078103101c0200c003468001e41e5001400a560580c5c1c3c15100d414110202e25000041408103442c0d042c0b8000c0a4041c0280a201e007001800c0003038009200100c0c00e03402220703595550090404140c40d5165107490750b000034415028540c0b0303021707540005615810114071440d183d04a4180d2400c1c5200024202079240c0d0150602e08800d220070070204510b181100c565503410301300782254200c0c07100213440d00070f0800d6120000d5481c2a000d19000c5495404c600115111814030704c45442030140154104d0040c0981c80c0b080d0341441481c1c5070050f01a50041d0b8000070010320241e514070311500010300038042600501495915410361542c800520341001c5203d841d0307030000c2c40c28100320359515098000646504c0303013005032404580044120b00000c0b80c15003201312095600619000059200c000070031720410030002c2c0f51200000d0081d50100e1000c100314016514185980c41e558204a4182c1114809031115540e03140f0b8910009191218101c201030f040e00904009103560911380d0071184024 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 41761623 1250 41760373 41760391
    0x906020106080c010801050d03030b120102090103200d110c1209030106121208041a0106020a020f01020d0e011101020f03090a060e01020f041215060605070b090309010c022106040b040605 82
    0x30420b9040f9a800034040f9056400907900414009828103044026050301c900d01600040d90208050381500d043d001480d0b114400c2c1c1301840707802d80b4580000c1c20743d011a00300d0321003820280504a84107040e80c00c01a80490074140140c1010740c1d8038103e6041048000da07600c000309001030980d489003000c0c06454002c00c1c8540e800100c0002c01e8a460410300c0f8001d03040c004220140340040c080210710703221540310401078001c003601c960711558041d40d078003800ea4069205000c040b048102d550b100103419107150b0002c1e658401130001e401c005550701400702d1700451855409104682080300103401940c80b45000d08024002d119141c01c0c04412100010072664541c0d00402c40c0c1f400da0b6030104201c804460a070454401640101e00742541d81004180e5032008440c10001e00090050340540903000700c501032528803003141c603200000da5491044a40b15404031b543c0400030005480d0002c001100000a1301444001d070001c60481400c0c5003045500700c403019958805d110a0240a1242c258403201103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 41762873 1250 41761623 41761633
    0x30b120d080a09030c08160804030b0108010f0c0e0f0a08010c051b0f060103022b03050406021002040f03141e030a091707050f04020f030f0f0f07171b0a090602010608 73
    0x144d103008040751a1004050f107910000107442c0714040c6900d150f20201500003809940703c580300d00d440c0104d05400e02ca07000f495800c080302246101d40603c00c4030300d800d030582c4510011030700000a019108c040c100c00c20742c1c000454940012034442c00e00403404800301c141c0d9501d40e210080000c0d1146200c601c43e001c0c189612842400030031040000320700e415280c0440e0505e040d5155284210700c0c0c8680b8418120b000c460b070000e21010590440042c0054072081c0d02a40c059050045c0001304034001e80c41807100740ca5540c0e00410200e50807400d00345001c007000003911021040c81d9118590106000d0120440d507100044051242d903000d0541006401a1400c081103032000c80c0001b03039102010701850f8441c034021040c0e90300968881d8121480502e9424010b5264941001040b92418003101c2000e00030310703d0340000710980b4075240654454001e0b5219512841800c05841c25041401441942c5181e5403002c0780603810190005010001c1d4950303101e501c0941020002425220582d014640310340c09 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 41764123 1250 41762873 41762891
    0x30c01090506160206150604030807030305040b060d0807021212040f0302090726090313090506040b04090f0807020102010204120803040c060815130b090106080103110604050d0204020307030b120d080a 88
    0x1301140564000701090f000d00c83c1500448001107652180e90700040c010200001e888007055016080240b1031800790b41102e04035511241400566940501c1c0100f01c0c1c0010041c3c0e100514100e507240d1250362404046550304407074007d03000e42c42d600580245004041f120420011071800701a129840001351401010201c0011440d403480c0902405580545501c1800079148480400035214464000d081e10380c1da65a407000c5400003000d0030b41d045802079040c150b0748070039410a07003c2d01d43c4469010351408000c09950b140d02005400c10340b4101d0440d50200701c00900e24001030110070314503005520250faa4101840d0200520856520210600c884d88041140c00c00f00424800d20441c0180c46003101012480400c000030980410115405080180042000350b4851485130580340700d03d0a29104002c0d40301005182d0141cbd02c00c0c1984003440c03511820040c245a0065900700f031088c180441e84035840780008903040d84048082420360f100105050383c1303a5114001030340012480740c04101101c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 41765373 1250 41764123 41764127
    0x9030d1a0f010e0f040609020901020105160e0603070e0406090203090f06040507140d05010606030b1005030105092206060b0a09050a0b030402190f08010b0414060a090e030c030c0109050616 83
    0x2803059058148039100030f404000343c4680b00d980603040e1008108110030f03900c17000d4510080d044651203500641c80c041c0051250100b0075004c8040c181540c495101c02c2c0444001c220703c035403004000c00d041050501d100b8a154449009000240036078106c0940c403440c0c50015140b4211016103003ca541c0d1050b420f10007c20750106000702034075004100c021501d9420b5020813021184104020940c1d0310f899000504143d2642c4822000a8102d0304d81c1c00c00d444046080361140028003501c2e5009503000003050313008980e004668040f041300a0a00d0845280c0e40b20482164201d034480c800da05000544c0714186a84005610701602c0c1c100c84e56440b0b07504000c002040d03800300400c001d0003089661100295030170040da414008160030b00781444c03141c7d100c1e03000c02e010703091900741c444c0203071b05041002e081800c80b81e02c1e042c81900040c1c03070780006a00d41742c02480500110f407038184150104111248011100380020201d810610b400400ea0303c1c80b5150140c6000700052684c040f5240500410103000c5d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 41766623 1250 41765373 41765389
    0x30c02150711100c0c0f0503070503150a05040204060302030a030801051212040317070b070504050102011103070c170f130503060705090102030a081f030b16090f09110405060309030d1a 81
    0x82c00540d0911a14400c00c28280d40f10300b07014101800ca008940c5000880c0c44180203500c007a900150b0656850310303600d4040c1907a074640c051081c020780c4460000100c0007200c1d40d0103c0d0f40940010b002280c0503a90f500030908003d000c0c001035000a11400040c40981400f201c0c80000300c80440081c4507034041000784082900542c000200182c0c18160004210400c0006803207a0540118440c0440d0034006800382c160380c41889040c0c00365003080341c0c441c03464101c88281c0c1d104103881d846003a140d1071642c0e10000d02c00480080340603202d0b410b105c11508805004040c0c0450201c00200d0480c85040c401010301e0454014a0030003001010404640c3e140d9001c4145c401000301814070301d85c603482c2c1d500c80000101206c10b41c2407851805200000510046000e4280920040d80001003000d03025402220714034450300604004110800c420801d850307283d840154407542d041d054904240d01c2e0030008080da401175030f070701405903c040b4200c10420300a12440b00d6500f0040d040040c01180c0101180e850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 41767873 1250 41766623 41766653
    0x80304060c030e060712091802070f020f01090b03090c01020c1203070209090307080304030518100504060c08090306100f06030212060f0409020904141e0319110a030c021507 76
    0x10b040c0740c0f04202c42d142c10055603034241d0301100c40341c089882003000400942c11842080c0c606151032500c0700c01840b20748203c030812500300d0394004a90403940c0a102c40380049a2400d03040200a100004c1d150780800d010318022450345024088460800000a1415615540d018400ca512001060004100100f100c0400da41501c9030091a6950601d0310300f1409243c4001c0c001c0f0070000100800c155014005002c3d042240c00d003540c110314401c0602a40b00904003024010071020001405010300549036008064401c045141c60000c4050100307003840c9040d1100c0303005174074008051080005402c03404011300681d260841c2804211040446807035005440980680206110380d0050344668020145094016113000c0590801e49040c03038031f2184100d582c80341d600410400300b0210800b031948200f10420140194180f9003480e1110302109400c07001003050050407507000a1a000074080d4500a50081c0c40b004a6458180180032031002512914000524100310281c001200c0f0311101d005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 41769123 1250 41767873 41767877
    0x10f0501030e030d090302060f010b120c0d020c010603050d090e07020c0d021516020a06050c060402130e0613110904020612041104060b04030c0602060603030a0c0201120204080102090406080304060c03 88
    0x200d003009980d054150f229135240c0c40502400d000c083d600381030300010203c0c0613811400b02c147e1a6039984a9a20160140076085a100e0700340034040b59007481050041c1441d000790301c5005260040807032025003102c2c0036600880b4250043c600600300d4030340107200314004024a850030040c40c648060001d4407850b103c5041e600c070b000c24880860940d01d40d2840030102a0040b15402c1d55803080e01012501503900c80001ca108000303106002c6466807068041d0713a6088040d130010f101070b03141c983c200f0448a04083d01108443e0392420a854250740410455000350742c01122614000a18200a08203428101a9070b0044040c042030000507203600c001c031503860071544060380391501c0300c0c502150030000c80c1c482c00364040e040900200d50002c01c4402001203d2266444401d0603070740c0c0303c060b6201c0c0c00840780c89074036030404d100700c1c4032150081085100462051604018041030394948108a0f00160070a14a9a6002c039240c0d1346404e0a10400300540407010085080c030b03181001c000c114051092000341 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 41770373 1250 41769123 41769131
    0x10020c0a0303052209020315010e0a090b060c03040b1803010908030403050d290901081b06180301091103060f0405030a050c0102041a0304030801060306080d081e0f0907060305010f050103 82
    0xc1079820381c1d045003c21511300f03070000808664803101c40019410954010280d88101c902c140040d60013900c0c11a00010083c0401240510304030201001300688811a0303000f03102080750598200090004001030100c1090f4113464280c100c1c2010003480003201854002c0c7e1500c1104800b0035010000d0701c0d4003544c50314180380e44040c1c608034000601071704020328000304401001d0300d0007030b80246044080308206480318030b0280e0340c40c5242c60b51101c0c407044602d04070880c50145030050510200504c107a080342c0c0c041c800c4d2214901d000c04d003100d0340224217031100f050001c1c80381d03058a8203010380d03900005e182a0300f00d22810b042e01c505441713110b0320700b184003840f40c0020381c0c0744220801c1d016100284109480480032001880050915600441c0c0880c0091100300021403014080d00c1240d0540da01c01c00201f15140e035511050b0781103035018114003028290b040e0541c41c03c0000f518081e101d07007c03807038000d10b007070602466440c0781000390b800a4003032500300387c0140400040309c010503007114001d203004a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 41771623 1250 41770373 41770387
    0x105060d020d020c0f0607030e07120f0302070305030a2a1203050a0b030f01230115080411040219140901080a05040821010503070902160b0601050f1810020c0a030305 73
    0xc0c024880c1e40c2c0b10801318092488034848039180418503038031a4441e42c0f401e001d5481507440054840380c49010b9100381d8454204803030045010045044403180c400d004842404c0c0d101c1c0c59907851508070144030f0000400104060040b0381c1f0009114101d030fa05040c40146014042d900c1d80503480058442204160365500002d07101c1c01d458100645d44c1d000a000c0e2007807102d501303140601900e0044155680c007108150b400b11204111402c05049a07010100c640c0b0302a00303c0b0b012540000058015207012070710b030f810b07400c1c00d65a62000300815050032400d0511010354010140040401544048007810184040d06042e40c0210240c5d6001400d800b00003142c2d036903032400d2046030041c848070300061140155108900040d2594050503200120b0864600320742d25070b0810280d2194030700d01c2c00e0702200040307030300000388180030703155007041050610324101010140da0340302d6a000322300c0e0300c090540003802068050030011020290383c0894800381180c42c40348001320b06040081d100c0241007003000100303d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 41772873 1250 41771623 41771647
    0x20a02191505090f03150115031e0209040b04050105010c06020d02070506100609080304121220010b0f0d0b060607110406030b150301060305070b0c010b04090308010f0e0105060d02 79
    0x100034024511401c00000c41004008216400c143e43c200e01032042e45035005200d1800081060051703000142034000b41e820104035494001c1d80c4210301c1d00b0315444960310222801c28904250414100110050725511208100815160032081503409035152800512517a43d100c4104400c0c46c0c2c00090250b60783c40302c9408000240318842e00603095018031400c0c0310103201143c1c0301c0d104940c82591110641d0344c0703810445860b807180c2d22640308480b00402e55640003407071003020400003c581d82065407050031407030840b0f0201d84903800541f0003655100c83c038132030720b14010b9074001e001c600035078100c01c4148099440e0389160501030403040c030500d404030b941d104010f0ba402c02d0082c1803d0141c400d100e019a2441c10321140042654403240824141c01c2c1c1d4583c6041c140300f50000c5070b410000401003940350140003c056444200c503801c0d0742d500d0f5040c04642d62101d0180d502c600380319603500c40c0c1c15890000201d1510003d500800c03c0115006c00400095031524240c910b0302e4200440143c0c1c4038552622 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 41774123 1250 41772873 41772919
    0xb0109092003010b0903060a0c050703030b0102010b1002071a1903021c150303080108060403080115020313030b010503010c02030408100203130b07030504060b0d020108011809080c0109030e010e01020a02 89
    0x111001c40003000001103801840200074004d01c000980c1160f040da104c0f2480d20040e5480c80c0c52100c000b42040c8614000b1910075080204042e10600000030f00441a2004c946480e0b01040e42c0c03401350703122800030010302c450301ca180241e41010284003401c040c499000f52032140c014414503010107401180803160325040d96807091400c1110802040f4511000102c070004065500c8240c000c9840d142c00059404008a42c0300e2241d941a5030f1091141c2c01c1a180c0c1d40d81221a900342000c501c0240b21400c2e0580381c01103958095401808000392a625000c2050f0a541c1d0384041d68085402c00c0c8020400c0d00c5001904050010700b294015880359a00754041c5d020413404007028100c0404141880206501644220300441c05090140001d0741c0c0c072802e12598640c50900240054500b000401c41095860340d20401d9031810b40d40440c002d805925503104607080000041096507640400000709034000d041c1c01d08601080c202066907004a0001035140c480c6010068003c2038401c0c040000c0070390100c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 41775373 1250 41774123 41774171
    0x6050306040f05070b03040807060f0b040905010930050a230304031d0f010e120109050d080f040c0509090f03042d0e040f0501060f1403010f0b010909 66
    0x108440507460281028540540340c88001e4034107010b00000071480805440c110780c4242d800250b001c0c130b021821b9030760078010100c2c040503040060703076187c4c8801550b4450040300c0d0643c0c001c100100785100c103802e0100304a0802070400003124445206022123080c403c948642c80907040c1070050b202c080300c40382a101c9000e04401c101005896400c07a940e00704044001d14003880c003d6a444c0401403200c040c00108080504c1e00e039a2044403443d02b08000d6104020240c20440081c0055900e07454404940f400e542c808041155a40c2000d514591a160700070b041c00d078020186048010141041e80301e070487d161842c010940500320f03a074005503024a08004603082130445200712995150b1b60340301d00e074415541050038000c09558030030200c0f003840d202641c0340603910410004d90580d2501d40c2d4003032000c07100b030108072100c1d503c842c0005440244040c2e0003000b0100d00041859502d0b8a80170142160411080303100c01c0c92070850314012590307002903c5002d541920300c0c0003640282005440c6503042c0001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 41776623 1250 41775373 41775379
    0xc0b041a010e04150b0f040f090f0506010e1b070b07051b01061e0b030f04020a0306050406020306090708070e010e010c050111090406060c050a1e020306040b0402030c011d0d060605 79
    0x1400000b000b800b5806001c1c40385010308004122900810404000e90384c0e8404810342c4061403018488080c0341c01d5001c021138411b20313000003a0390302a0303540c0c005100340707120303410340f12900000c1c01085460070390341030103a010604000c1c081055180e600c40e01c40900807000c02a2105040758002080140150111420b4403080d0301002000010b140d01ca03800b070f1042d8060715040c07401003481000020f658109a40560b15040f551034150350741d0350114006075600501c140d0b0720803410840000070230718620a0a00490090002580d00c1c60044240100d80c0b001904c60b1081000705030170004001e40c13010310100606824686041c40f2603040004039450b10f804080030344154601080512a0022039006004400b025201440410b1b40e074601034507040700c008405091600f04c052151f00040302c2c01e00b0310311001242000044201d00c650082403508504540895542000c041480154a410440c88035101400d2038458004891691070072030000c1e2880030503026840c180c00702c008001c101c1c0c1058003e01006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 41777873 1250 41776623 41776673
    0xf0c0f0b041e0509040b010501030b1c1502070c0603050403081b0a03090201020c0a090b0a060c03090e06010c0c0902070311010501062007050315040314040f030f1a010b0702030105090105070c0b04 86
    0x5401c01c441200c6c020702ca074a000ca8a01500c03090281000f41e012001110b10780020f184015154a074884140d00c2e071458420301d190b08008000024066140352000303480599000116460030b407902405d90b1001800d808032180000419515a4410304200c84041d41d040c600428010304070310040c1e20b410003c3e4401c1d680303e2030280c0040b031222101d41c00000450000c0f200e4106040d0340e08070649100c4040d1101a0000718107441c00c0c850340e0000d8502680024040c03412400d41c4406840e0640007118503040b0b0030750150005000c40c1030503400800e460030210102c000304086c0d458543e014102400704298080941810010040011001e001c000e00500c00034007034508940c0d1444400c00118130880c3d0440c08038600001c80c05032045120240c5082d144031a90407154141583c45101c5101c20803041244c1c0d0426011800c00b0807590901800d0003060045103a545460700341c4105400e5400081c0001610386c58030303013004903503a4020b02000080c4c0d040214861282c6460070f00921980d24448080710900324 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 41779123 1250 41777873 41777881
    0x2010506011b020609220e10020306030c0904050c0306041110030b09150a08030f0405130213120203030d0e010516020c030c010305040510090b041e05060c0a12090f0c0f0b041e0509 79
    0x1079002444680c0c1c0d0340050701c230144111507030001280025105607825500013580d80225040450255402501540446400041450001c4d103813000840c2c2c100c42c0c1e5442c0410b48442c40c00e0451180303021028504080c0084203420b008160030920080c2184002517600b000b02b4040d4560320b0490b405426290141e998031030001c808031001c1e82c4a4410140100031401c01208100100d10950b0314a0b507285814010441c0340c030380c086040ca0724095099901d03000070850844800300a00c200c98110340c0704000410507140445036000c420308400d841e07400350b4220100e41d0040d55404500010b4684090800207041c0d01d540c02d18034500822007180d0045185070405903018892191280d52190b80315030105510a0302031000c0c441110755140000b40658818008900804a00300203001010f0f40c500d014560f2075076020f140002d45080302e20035940000b40c1345041003800b00d081c1c5c016004c1c0480040c82d480c51441c041c2c40388001c0c800da100b413101d007509480b441903880019400c041c2c000c0800a0052002e410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 41780373 1250 41779123 41779189
    0xb03191503052b050c0705060315060c01050103030906030606200a0804030b010e0a0e03090f1201061805010f050d03030f02070803071106070201050714090a08070602060702010506011b020609 84
    0x10f2901d094030206211801a165641d1150040b545001d20907009410094034100c00e01c42e1940016081d4440300d84002440d0407180c40348000343c8001c03600c04001107030715451802c024142c0601500a0401c050600e00f09004141c1c06c100c000700540403000000c80c00196581d07149003040c0440e00300600300c200c0000c0c00410300046103074281c103851035020010455125168080d085800056503e241c64105019011080c502100d00c089400405001100703149032075050075003100c03d1703030300700204400b000c0100980790100b0788141c50141040c031158040e414105000101d0302d0459560007000c04d0780b86c03940030181002c6501601c0d03c05921004c15070b0ae82c102031102800b50712201007242c909100380000141007501c1405501d000d007071035490b0413584800c540701d0016a50b02001c102508013010100c009060581000400002d00655010700300c80d0800c402d0081c00c0d04d00250449042155130820500c00c01801107181c690994101c0e10107540d9031b2030101180800e400401201c29844401c200070481c54 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 41781623 1250 41780373 41780413
    0x106090801050c120c0d0608030313030806060703020718020415051b010911060d02090907050c0607020a02150c1006081b0604030b010e1b0c070303090b0319150305 72
    0x300500001c0c049941c60f0100054680507000c0e9503480f4408940219a142413480020000c10b4158940801c006888285070b070310f50b41c002d85000c04040c204c3c05120041c10352140f0032542104007211079034035006580c0c030000e650b402c10b401504814041007001c2c00300400c0d1541210010600542e00003080b030000e100c05805500f111406142400403018581c0c0000810f1003103090311903000941301188000341c01400210780046058001d42542081170349142e940d603a45c81e621802c215038a0a170380b1300d24848100d080240c043c0000b003d55106070241001669402da0103110341c08032244054454104410382c1e8500960800800e40981c507040c8041848440441c1841c0c202c0068103e0341401081c0c0000e11090703104030710001e00318110210052011400d00030306550007448025109082600c1141420041d610280401107039602120b030800401d9040540c00c0c00401d01c1d140240d065240c00c2030608600d440113002094038980d00c4184020b5a000d40382568080c1d9084402c840c481d01820344418112 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 41782873 1250 41781623 41781629
    0x2010911060307080c030c040801050c03040201030e34030204090309061d09040f05010b06180a06090302030318150a020703050106080d0207090e030424030507030216020d020a05040203010609 84
    0x11801645001242481402c403406994680d440c2c0ea09995000b072001c0454002030508990107004000000b00d0203001d00925000b40c55085182c0d6803401c09100140031168802c43c024101c5e00885444001c0320846890810f9100001c0d0300c81c0b180d03060904480e81d0312800358200942c400e113001080c42c1495445a1143d0a031a000d4407031004062030407401e80c4030141c020268950045800000400103071404460f101607034400d60003c01d8444085002903204d0b0010300040003694144880303103026141031000c01c0010301c2d0501b4925250750450700402d0302e03403241e00b03002c00c156020100380003555199090720840072401c1c0c0d50101e44848089100075101d144a01c41070b0b8042d07080a4010030101004100e10300c1c4c2c001c16070014242c81d40380080001c00340000110741c44490009220004500001d0003c20040d11601e1020303050401140320003904540c070240580301050700c184a0616199031348400320354911f40403600c0655582840c800182405215004240c11a0011000203116600644a1010707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 41784123 1250 41782873 41782883
    0x1002011d0f0c010507020307031202060702151302011107090501060507062a120e0a030c12090501050906090a0308160b070804030503070f020313060509041a0603160c12020109 77
    0x40c21400318010340c1e65144038501000c1c25001551000203941c0500000e001e214400790582c0c40482d941d4841000d07800c00c00c5202405130308410b0070010500d6040c80341004045c191820f08526007441c942910015825010007030501280f44040c050316201000307542d00408040780207101d01e40c1c45010050190300988801c840150815501c01d65000710061900502c0c440701320b1212404511034401c480343c80c8610700984040e40c0d41e201600d1803000034040400070364007a440b001d05088072440e01514000c41d0325580703000c10403400418405c40c1c2c0d106049a00d0081d045030308030345441d0140001200c500e060351000f4a80b007400500e280c80b221b0800c3e030130700d40140a05175503081030742c81007002c1d42d24080403100100040c1080000074041c50080e401c010a0004c01e20469003000c400b04400000507910750010400704c0e80104071a1050726190003113130102583c264401d21144034000210744140000741c802502d0f10412814043d0385482a2400b030503a58114200000e40a01d80f500a8024110703070b81300b528 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 41785373 1250 41784123 41784161
    0x7081602010b032e0207050c01030506191202090109050f15032a0a170619061509170708031206040213150905010c0510110910050d0e1908030411100201 67
    0x100606032172094400715a000380c003808404501c04011402090005d041c0c5a00c03020100a80503414003580014018014000d01c4501928446c01003088900c0140d00c43c47c0000e0500c020042d410f03411400181d0032295943c00003904042c0d010020f428004851194030442c11503054510a40008000e05071711190203443c200410b54823290441d08444010051001c203512841c04a03c2c0500d140f25002c0c108180010001942a00d41e003500300d24038410700301200010b15089040c4511072113103000a500c00700600c002c00d034540c98240c1141e140e0052032001207160542c47d0004840707440326012941280744421400708269110040c0995681c00c260380d001c0007543c01e24020030194044c0060700384980c3c004000b0700104041c1840d00000c0c241130240001500010301c5184010746442000843c001000e444540e158040c460000c012510172a080007095423001203440410642103a40d080300b950000b0780307242d99a0711424202d1007040d40c1c2d681140c10825003031081001c160b040d44020400040311080c59 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 41786623 1250 41785373 41785453
    0xf03110a05031e0f0c090a0302040e0607020f070f0e0a06080102040315110a080c0a020705040c020705120c1005181503060108061905040b011103030901050f0c0307081602010b03 78
    0x40083d0404032006559810400081000c0e141031901419100b003004100001c51900d07940801c080e036071402400d00b5184c0c0101c0c24401419014840f001280d500b81c1e00411b0250315108002407160220710810b05001c1001d8081245407440f5000701c1d02034480003000795900c0e503407850840c403e030b8207010100400900d00308240d4950030070141203c11483c2503546406082e2100d01520711141c4c00301e9803a0f0b0962240000000d0a515640100c1520103115000ba184940c80c0c0700620020420710041007610303400c0000d0a03280395541d0303111000040107500d8480d44416001c0100c04c40b101c8020046075225407113203a002c102e419001c00840c070494003a42c5200441d01d0f0001800300041c040b0406050b441221407051040b0700b03041c0d209480110051410715040d03568032449605590086e650f5103081d0b51101d0420400001a40e4555001000107107064694a0400704c003c04858005d402400c010313052080d0002c000e4401d400001c0b05000007415242c003260a081040000c601e100070418090301600218 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 41787873 1250 41786623 41786671
    0x5070c090c090605090f0d0309180203091e16030506010914090d030203131704080705060a0203040e0709030501020c06060a0602010b090a0c03090b07050304051e0d0f03110a0503 78
    0x4655101c05611080c81c05801d00320280c0b481d8001409540d0070802c001841150783d640c40c84102c50580c082c1e16411000d9080c429002d4014504045000c005401002845001e81e40000c0000340204001050000a046001d540381004030802422030040716452010081c84004900c85040302c14040003040110213925080014410071180c0841071b800c220602c540d16400f1350011036014149242c10908085640d42d080400740c00840c5411150a001c5818000e07070b4402c110500c081d04081b036882d400c3c0545200001d42d00d2040d80516250280e207c40440c1d5020b015005400185a000000b95100c029480c0410356a1101b1226203100c2e2100c0310700000d2aa0040c4100c80141341c1c040c01044040d91544c0c520390180440070050b0003055984e840c2c0402080c80c140301d040c0a002d40c0d40da015941e0600d800c00b00d15102c0d020381040b21062040004145045c40001c120311030300442d05110b490000c0c0a4026801031091a00419071010b00044a0900326030000085106010200302d171a5110704400c05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 41789123 1250 41787873 41787881
    0x709021c06030807170f0a02070e010e0c0304060f2c060601110703061107020d0c06080703050613050901110a03060e0a050103050c19080d0801090b1816020a0b0705070c09 75
    0x101a0110f0030400c6600301140c0001403035401c4000340003940d89400d02c4421403600d541c0c081c450b18030044c1c2003104103204d04100108d0ae14010a842c04040a081c00c180e1005420391001520040216a6890740340c10015520b8102500e03c0ba0540e01c0008400340101103250381700c80519003000345004a0b8000b80907903014500c07503401840418002c25041c0e00b50360390700004040104518a03c51010700581c80160303180c03503402c4813142c0b0403e03d1654162812201810b44607003d4401070500d824003040103d60303151002000c000c02c0d00c1c5103000c503c68403402000381c01042910341040350f0f44800503084100e00e4154114604861002c036406d0b800d9500c200701601190005c1c0401425604500300c0d0060b1407426a22101001100d04004201e07030f55a071242c5454840d80643c0c0201094440004000000c0c20344509802e141e819030b410340600031000000f01740e01c030700200782880c480c503501500003160f071003000074070314103548808201c0140c2031240000e003280d082500129185103860b0720100707944810f805 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 41790373 1250 41789123 41789129
    0xd0b01030501081209030106080601061e05090d0803070c06050906090c0904020a0504090305040b040806060f040c0f1209060905100c0207031106071703100f05030312060d11030709021c06 82
    0x98025134035081c05101c002d5100e813403150b6156480e1240401c50800920803503000b040c0a03160060a031401d604440d620450404100003885014046180d1903254044804445a40181056034a0b07948180031754181c0390a92000e00300a2a0401b003200090780080c03254007650481080b102c08007900c10400180a104444c001e4008201c0041017010f030a01e500311007405032181c02d0090500d81c940d500c0300c245800c01d83c0442019427005040c130030141400201c0300071040c4241c8040c4044a141c083c094681034a03980c20382c0410034414540141051958010801c082e4841c07001c2c0241c1d0b41d1401c10940d0341034004285000c00b8a0090341c40002400020b00d84212a0302001c040e100384007000800001c0e0f00280300a5610b1000701220604074003584009510640b04241901041410060030201c000d800e5040140285d00420021014010f403041d0790b50f02207411100e1580048052405950011100700031030b0b014403c4200102d4404815000741c5039001006451003162079488841700144ca0141c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 41791623 1250 41790373 41790389
    0x30e011b09050603180609010501030308160507030e01050903010c05040815040b07080c0d060314100509030904090204090803070507030810050604030809010215010b120907050603011502071a0d0b01030501 90
    0x40e000c21060074003001441e40414a403d05e01d180401415007241044c40031203072600c1c82d0f5941d030014020950440809500183c0e500b455012844200802814138805e421014050103c00500344a03280e11a10407035123a0140074000340402c140144001e0f00a0b0424020000c40d4024070950b0203030f40199901c0729108030b070081c0c0c0700a000e4584080960b180d52000c1c04952500b6820001001c19046900407580154481c04640da40c51300780b11900c0d0700301003a44a80c1d00c1100c1c00c4c001400907001c0008144c8001d1482140d0024555160744006401811103c60007403841a01004100200c1e0b0894003500566000352101e04450f40c034071010114401c5603024003031340064140b00501c04110088081c280c080c00c11b004480920423003183d058007910090384400d010000c0000d01e0300c51140212505504101c552005203120740c1000002045400140103400041d440c00da00c0e5603a140c42000385400a10544800910321041c04a1940099000860071040c0f642443c00c008125442441094100c400034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 41792873 1250 41791623 41791637
    0x1303020a14070308130e0708040804091a13050609070507020a0b0a031503140c03010605031504020607150c0306050d0b0a050901060302061204050105071b0b07030e030307030e011b 79
    0x3a80c0712900c1400c0041c0c0414030b03118600c00070001a4001008004260106038070f590028a403c0e07450550620081001081104c00010f1100180720841918181d40c071200000c5140203041041c580c0038100400034582c001100880402d805134541d10160043c2d0080d00c6c0801c1e9550303542001e448134811045c00940148601c04108140b4000c0070140246d807000e8507001c40d07903c070b45190118150026030000d64028041d451000010242040144102e070002d0f40240100361900c00001c2d00c42000e030484c00070000441e000141150b54440c200e500e001d078085400300000147c840202c3c01081100d4480c00400d00e0804007080c5441c0c4008a2030070140d0146000d207179640c3d0100e03188050000548544015902c80c24003000598810300980301e0301d014101d001d40d0503d002c1c14940e00307580c4041c00074028000309800251041200c1041c21300110b030080340c043c0c500d48613440128002d013002c9458000358040030052158070760307040d0440d14506c11443d0080c01002c0c0b10302c03102c622489166010300003007420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 41794123 1250 41792873 41792893
    0x303090503060405100c050706090c081905070504020d021605010e070e0411010e01030b03010e1f06030201020703110f04060308190906051c090501051306050a02090f01110c030f0d08130302 83
    0x1e03a400103803401086c2d1800c0360401c801c5994100581d40c0d0b00300111101254840b00b0310600408000c04c48506218100981041e40141c44172500e07518070780195806039400050813200054250110741c4581c14a82510281881504009000300040100c00802e401050710005d80c49104e003d05601698005102031400c01d80d64005450b81e6408190441c141926112940c40035507080c400ea07003247d41e00102415130b200c20242044c0003804981c600c2180545407100600141c0d80c0040c00c1800e5aa00810100350000d407640040c0341505c1181c003881d80030f03080803000310400000401400c41c9a14410400b62140b040d084151240b0b01103001d000000ae03002d01078600303243c20850228100c091550740018030740e402c54540a09580c0d080b21092000600103a0400400c040d62165551108030000110704061400c030010711805545404241080200850f60400210501841c0b144d40307001800c54034041e80001c0d01b903461308040b54110010a40040008680504018413030036000d81c0359010346517100c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 41795373 1250 41794123 41794153
    0x3060f1801030b06010f050d0e0709020d060905060a0e0610050f030406090201030f0b01080705090a090c020601030210050a0509060c031308060601030c030902031207051207081b010207030e04110705010906060303090503060405 99
    0x41c0090449d10527210b81c1c0c0e000141c80603684003c042c02c01d50000042005800d007020b10050b10700107041030b4010790a01900700500707042c0141c540c2c3c02c03040446243c030456040e00c03022105405441e440c0c2c2980354000040c0300800c0318550044200600c01e03241401401c95000100089440420071540462a10750006000d144030324010202507000604040c4807a444004403021a1044182e00000d64003c5005006601d485e9018240b01c3d681c2e464424580b140004005100d40200761015004080109800c12800014015140c1c0d0410b00341c1e10646560f50b40119582d034101c1913a015001c00e240c1540004038034424024900d41d0398028004000210400a920701d5075449400155894001c01149040d0806410001d00d60540211345c415240c1c90008070901c242d60106c07241c0103660384100207240000c2c5c0c000580212581d0308540000c0c1404030341c1c030160300a03c40c2c2c81d4010001c0d440e0402480c00c11035694072001c2504d0195840c1c55140c0d4440080c103580d400c003070398060000d80c09032440783c00040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 41796623 1250 41795373 41795381
    0x50a030e03010f0207060501030c0b03010b0405041a0306100609081209090405150705031009140403030f0f0606050408060106030c0206040b1e09010e060c09010f0503060f1801030b06010f050d 84
    0x80300150000552001c2c458581d02281c00c6950129042d0313840310010014884640c0844015081450142e440d40d4501013442c4001c0c813680c0b20f8a8003c036104c40907040c2c0d10840e44001c900d8032002174240d0724503140103020740344041c20502600000c01e1342c3c2d04011031128070004034400c02c403c66122417883d00581030100701e80c0103c014000c41d200e10840ca10340807102e00e403104c10f9004000c0c5441c0d081d01c0b42400314074150352481c280c00001c201843e103d18802c80e24140703040550020740500300001c0030901440c41d0030280460144101c40c06080002c00074417190300c00d0042080710806002d9500da41d882e04000c0341075810340011040141d003ca0301280104403111181c41d008004074640705001c2003071203c600685401210240c0650b55200100c840d1440d040c040b1a80c455815003e00345030180c1030b030018041500212404003040b50100c0081c010f6116500c500b1200d003401410610f0442200381c7c0c04190130380900046402c00c6201c5c002c11000d50240c824600f805284da110142080341c03400ca450024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 41797873 1250 41796623 41796647
    0xe030c1209120a05030414040c0e010804030903060606020709230c030901020c011b26010618090608030a020d030203130209190903030c1403040206040e090f0322060c050a03 76
    0xc00c482070216460b00d800c00c40707118028440c1d4040c54661340380c40801040d03401c1c410b4600e0301460414030a6802031b82d202c0c2c824001ca42007400c00900c00d803914203003190b65000c00c0e00001d00c3c1602d001004581c007500016014100c1d09241400c1c0b0200d14251091001d01c44a42981c1d807100c0300100c04107010003201c9010f5070f0700c448028001400c01d130540d401c943c2074840d940c05c1000000d0f09540c0c1540d01e2a4010b044800a186070048582069410701051502a07014818041040200c030010b00d1001d43d20042840141810b1006100301900d400c2150f0b102e0b88200d03186005481580900e20b0140d001b402038070b1049407290128481e11510350207000c0b0700390380141045008945040140074004070fa00c9400c801c1800b13507a000071041907808002d4420741d581171300d40c40368960500402006130b40d003030100d409491070980c4d00441500d40d0410340c1d25140190303550010728000820121001c18080c0740000c0d0480e40da403550740240382c0c2c0d004160341d150a0387c1400b030020303000304400c117020a00441402e407039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 41799123 1250 41797873 41797879
    0xc05060604020f07060c0906090506030601021b040e16082b1b060515121b0d0c080a06020a0905010804050c0409020303090d0b04020f010503160c0c0302060304050c040e030c1209 78
    0x103484e500380d450204640b010704801c4042540000c081c850f4590280402d0302404040c1c48992460401c0e40020f503980b07421603a80c584414034190791007466203958001d20030040c2d40c1c404881a001042c40c003105200440d000f814518458016114080321076a51002e501420100c1500c01c1d400c1010070032070319055035070719008080411100e8140094100c0c400c280c8281800c804010004d4242c8041041b114903000b45440907603c1034085904180310860904442c900c00c6800502905403440c16900b0004135500034011030160707440c841c050008a4008044824007076135248d03040754603803005403003c2d40e007a200601903500420000c4402e06040c0c3c04441c0c11800102100d0420511000103078500c40100b000701c4004601c602404114206203500100c01d01003401d00e0741c203614205080e00c045003550b503100c604003d8442007403410311102d241c80f50040c44c0c000d00400d6a9140600300140e480c3c4a544049000320b1406401008644c404400c0d900c644810781c0242c02000140c4501000c02d4001c080c00c030703038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 41800373 1250 41799123 41799127
    0x91103040b01061b1e15271403030108030307030506030d080a09210f1202210403120507090e060a0503030a12060b040807080607211d060103031e0c05060604020f 71
    0x130214841088100086180000400040c19145015040790400481000e80e06003800703403081c40480c041049080c0344e90b4800c60717980340781d4460620308070048407419510500d001c000b0011542c01c1c80403004500c0f44085441c01c0c4503071b844100a0540e40e01c41d02240c0400200780d040414220080f6420501d95079009441050030301c80568600d9040354280c42d041404a490000600c00458220060a100d022412011030505031104a5000302100c410460102e81440f240010308050207040b402884906501040229240079031f8040c0c04c0014501030f440580e08014005442460001d4840d4180c0324040c000c2c40c10034001940c2562120800346268a11907102d00d408a8480c0301d040c050001403018100800c1c80911f810103031410141d0203419039040001d291780340002145500100c141c0482044400500307640d48585242d40750040c0200303504203008501c000028540c1c4111009030b21410001d411100201c410380540d548400010020529004440060741a1138960701a010420141103114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 41801623 1250 41800373 41800427
    0x112060f050702060601020106240e06130909020f101202032802130e0c0702131112010512010b0f0d020f0d06020c060604090803040f080c1204091103040b0106 70
    0x10068500803202c0600580c0b0000802141d50390901510004100c5098490022000c0c0e030840401d10f911000c1306004d200d0084499841c540f94134003292290448150300d2685d2035100c9030100090412100241d01c1103c0c0c1c140c0ba03944516001035841d400c0079040d201c9648034070102040d0006034000408040240382c0190101010045448a403502204c2c9003100596070110704028000040e030320f8001400348441c08080104003102c200c120f07041c098040750002030110079403040401600104890580c50703c001315182060b00c1500c2e40d0503050304c42c1194080c03c4c0100100d101400c88010301c020035444008170b1000300c01c504120703440700d0903140003034010002d155881d000b08203501d111040c2280c1443d80092540b03060b035800c0c041a500107070200c406120403c06a2030302c81642c08060805030100805280600810005404035500b1007a010141c9140807e00d100340d0f50950824446c429009080103451929480131b4070480e44076540c0490b8607445030f402c0c000200c4e003601c20450080c1580b04005200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 41802873 1250 41801623 41801651
    0x40605060f060c010e06070e01050417030d1803030b030c01051e040503010e06010e01050108011211031606030209010306050402030c030f070522030201020c030703030801050f01090f0303020d08090a0308011206 92
    0x4210600f282000820568038a0794002e11b4400300820700b40401483d01100446a030744142143c040300c984c0d0308003600d18403400c402542144100800441c90615060307545420440b42249002e5050090b1000c01c80947880d0020715441d0004c00034003500160040154540c04074010441d10300b49001140c0c424280b0303403901f000c03c3c21036082003500c2d1500d03031011004106000001400f540540400e20782509154174094500c0c16841d80003070002d0004903c82080b14046c0ca04010600c00a03402c083c0c80c1da122952048003800a5100f994118002810030f5000701e500d007024000c07280115210540f4516590766000000002c0e80b01070031107010403400304017210800c5081d41c11032440b81445a8a07080803480c610029150803d00c1103000d000b6000600208041707600002410f04403201a503008050880c16001212040002d4100c1d1016000004000c410706d031b4006044141c1141c56200c2c40c505844081c0d49a42d0b406190800500203484180140300c003050316a109003145218540128500c50390b0300d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 41804123 1250 41802873 41802877
    0x30603050313080d020703080906031302090f090708030301120807020a030c0801050f01090912110f0304170618030702010c020103022104060b12060f060120070302040f020f03040605060f06 83
    0x1461a6410420307800f0b002c07840090143ca5464011800141840c078503680d502d2081340903020090384103102c080001400d1070311607031506010310790082091060345001e0803241d60009058401442d180316400c0041907a103000400c030303070590320343d1802c400c03843d011aa90454a688901030880c1c00c15161000000025010f025a0b0080c10085002041d03038548424002c0b0004d0f41603100c0402141002d0034030010516003801190782d005146890808880981011071805180da148401d0604c40080c0c0012580d49104050807100c40840513189a0b8640d824440107811014501010f20f4008102200040d0b00426404609510605016040036030b05040d81b0034500326001c1720301c80f0300c070301400700010441d00d80f00d02d044100041307410799100c1a070b4020103980c42100500503401c08007007401184450b8000c0503080391030415040c01e007030945007601038151640507030701c0b0813401641400111113496a1070b00a40d0011000f645110f030859486488130320191038003501d125000004411844815211040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 41805373 1250 41804123 41804137
    0x402041a1c05010b0d020f0904240e01050601020703030801060f0c080d0b01020606010810030605221a01060f0806100e09010801150b0f03010302010f020c031509060a1413030306030503 81
    0x1018128101c1503060490a481c07404818500c42c090810b070000041c0d40c1c06541c24464007056644000554a03803400804030b40d00c0c03180411241c080c1000e816141140c54010000311078144001788150740710980161398400c003500000300820907500c010b0028504c01c00c071400220405240110400c00c040d181c0c1a50755022904010300744d40c41e5180c2c107000d542c04000c0250810002c0c03800d10481d2518501c481c2907e11180030090141c2d40b1080491a00031404050048003900200070b110000c4484c44d141240401103201c520041c2c403003000000e40d05000384004484c00040c1e80360042182c0c3d40c8010801230340c21022003a070502445081c1090a500c5429100c2d01a0802c3c00000807402c800d4030005042481c41c0e842039820344010000c4114032071146041e02c0c110784d03080c00c0c800501e00101b0810707030030500364610084d0144610340c404450030100c081e5032070142d191142610915140c0e4030f031400940d1300487c041c05000b16082c010520410700d40801e550030500900d0300142c5c0d03c1c0c8a5980c50b055600400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 41806623 1250 41805373 41805409
    0xc0a030f121404030c0905070206060604122f030d0c050712050a0b0a0609060b0705100c0909020705030901030e0c03060c0a02010e01050903030601090b1e030411030f0a0c0f0b030402041a 82
    0x3200c1030210380710907c100c82c0c0102c280d000a0609103007400014043d841b481c0690b180c503191400b0b014081104200c0000d0102c0a1301c3c6002000b448040c00e00b00100c404401c01720320a11442e000c4580300c60241001c0d242180d006005040c0403410260b505120034100c0f2000c64843c0709681c0c0c1240452a0014624003402001310041040303450300b990441078505503080001058004c02082001070000036503643e0495525001049103158008140d4252205a001002c0da5000140c07803410402c0c040001c0846907026201000102031080d1169525000310b8019509035005001040010720365038080e14000a80388004200d00000741c4515094450903a0b0041e445c0c0d0010051141c07030b40c4c002084c88050000500c0c030700d0602a0380821000f540b06440c02810800c0c43c0000071030140507000703e4020803018050200d68150030304509199450700d88480c01d6601801c413101c0811042100d11843c8100c13940e440256085481e582c003044020081c00c450104800d003581c09010503501d941c00c40c0f000c000003003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 41807873 1250 41806623 41806643
    0x304020f04022206090b03150f15030a0f111209030c01020a0c051e100e0115030f03030e0303060a03110a0806010803030108100506010c1104090618050c0a030f12140403 74
    0x8581c0f0048900e42200301800050303d000c0c0218045a02902d90000d18a200340c0c0d07101c05401c000c60564000482c403140c008440e5402c08090b4030010000f0350081c03100c01c1c400c1000c20106004142100d4900c958810110070412040210f40c82e2104d003e85c000d04608140d900d003140c40b11043d0708980c0700314040004a07001407403c80c2440006e0108a50b40f2295100b5031094001c1d1354022170b03c0701290a00541d2455403500c01e000700c06801d50220311088807414403039081c540c0300d0501041030800c1c0c5004400003410901409141c41e00030081d0783c000d080c044d007242c80a5045a41d02e0b28004c00340c90410f42c0109210000082401c001c0011074000c04010015550720750400ba50b850134003c5038410380c200a414401807108030390b404114200080d4000f40000c0c00031040b04002070143c0394944000c0c1441c2c1c14404a0300501002006020300c0c40d10490440321500700f49030a024401e09240700c00303040f5505e9166208046124106010401109403511b80b003215002c001021407504180c000b501e8220103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 41809123 1250 41807873 41807917
    0x60f1202030c1516050c0901060e0306070201140106050d09020d06020703020f010204030f0b0c120114011b0507060c170304080909061e01110102090301020d0c0206071407080304020f0402 82
    0x9010b42140e484007962941404a107032107510703183d44501c880145000714002002d0301841401c0c08805040e0314010180003071540c0d1a040140b1280180242034401e000312004950100e00510806003d40110f005044060707107000c90a9400750003c20b18001000d444141c1200160b4459840c0501188508401a1a030305c541c00c0c000e113010280c0e403078200d0580c4100410710205013203501d04080385900c8001c5c400b5507641c0b005030010a015001d50440c1c0700001c50b00100d004040b0f0401c000d64400c0c21b99442c0c415070781c030801381000440200c902900b1134000d13003c00e00560740b0034800c0b9a1202e0040d2040c0000e82c00161560400781c1c0b040790f0655048502041c1c2050a1614030b815a0300090122a55800c0310310403050720380901c0003030084070305011012241d0070014001390152482d0030700c01030003107487e011102d05031409000000400c1005000e8580001c45a83c043d540ea07001c0741c00c22003042b0381003180300d5448504c0c1d43e00c003a000341e9200380139540c4e25805a50701d000818046244d54034101c28500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 41810373 1250 41809123 41809129
    0x30f1b02010605060c060103020d0609120c0b060a061d0d020901030609021507050606040902190b07060c030c050412020114030718080d1b110a0b040311040b01050406030b04060f1202 80
    0x81603400692295208000302c5c0e20700c0500289582c1500c3c3c04a8403010385018903e030010003450009002003250240798425128950080000000b80c2c0c0904050320440c0d590300200901d05905002e02c80c003151800740b03003c3ca00c0a114041c0d0000e00700c0a00090460300c000d03000261941d200b68000c44880d1340340d01d40101103080101a10103801050503615040050aa44864498078014001801150344a064106540d2964040c00a4020724a0401d1080c0e031140100c45155000481c1a1456030400a4084140c2e12911488500708840d07620541064201500c111520300480d41c180e04004a21b00700f07a0311500c42100550103410f15031500190022400c1e51802d000c1034960084c445900580c404a4503d40c0081c000d40e4501c24201c1c0d42031001c14685000c0390300d450808181500300d0715540f00030812030709100080058034000e01e07074030000289a800300401e460100011a002881c1400304001e00c50280d0010800c51900a00209000741c03516a03014007508558012500c6c0b0a2009a907400d5003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 41811623 1250 41810373 41810381
    0x10060b130801060f0315060905090f0c0603090613061103070804030e01020a050d030f061d042001050f03190f0f060e010e010b1b030a02070608070c150c030f1b0201 72
    0xd408024000f02e860158540180c00b00c5103c09040407840d016481d42c010720710b5020b403010b004003210030010b500301030341d0995540d03450411a01c1c0920900041050340d16054007076a100300500c80050030140c1c1c07200800302c100d07224600c0460306552556030b44020001c2080c081c62050405940d0f218481c982810001c1207500d52052003415034011122600c00b04030b01041c0880390362a0f5003400f00b95582ca8030006001000c840e48088800900075801c0030700d141c0c50903041070107139000e545121098940c1e00b0719901000784030700c80b103804542c041000201000219024503880b40405611201044850b42e160003500c0a60780e24450351569108480f801a005110729000380441d100300b10040e60624800c110b0b1920180034800030034001042801850005481d452480340201c2c003501c2c0c6480b40c441010796076108070302460010402c040000392000d0300c104114003150382c0140554004043c0c4080c440020324106001c0401c06440e14242c01c0312820b5030044410110002c1e0690412121040c4001d0850b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 41812873 1250 41811623 41811629
    0x30305150d0309050603090a0507030f030306150801030326070210050903041404020c0304050607030e0a05040b03030304020f030715090f080109120e0402090a030503070510020f1b10060b13 83
    0x14000c6a01c41c000880da102d03001c03105985054540395a681c45d8803001e14a000c050280080c0140304201e8040200a8026510031129110391030a2100d44d480b007400a0300e5800210122000075001030041001c82d126a5002101410003118105035407e41c0d41d07518110f800441c6e4107800341e8090168030495441c2c03031044581c001c440724055401c060404402241401c8010403941c030507500801c00600f946803d004071002041e004080940c0d80c05940381c09400c0c6900c0070700a40c441c49400e0f1000800c7d040c00e0264a0b040e5100601461955823140d00b04103078600b031100792a402d840341c52000318152110a110074000d21003034490000c618502500040604000c3d0400307111641001040000208032051441c214602402c2c04403840c107a40d0003050003806aa000703140d0008004a0010600901000510585000740300f611260480044040c0503482407403500c1100300010811040c12202d00100c0c118070048010540d428500c0380e445400a55036141c03c0203071115030000e545c807000000742d0f03040802 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 41814123 1250 41812873 41812879
    0x70c05060f180402032202060d020307080702010e010212070507050708010513020f0f0303030f0c0c0703110103051302150901050705060406141027021b030901020d0507020a05010309080c01050403030515 89
    0x13441c50304110041b0280c03001d00403c910304200c1e00b04102195a444103460303c001c144003045450f4500f81d14001c14203001510031074003552805007903035001744041c0201c803a00003904c003a80443da100c051003107607541e010841c261194041e494010410540030300400703010303160425a21809046500401111903111200c2d1031040301040c0103c1800c1d00c2c0402a00d0340529190364082c002e6a883da41e030000b0340f25108030f2200034020000c02208002d0710007201c000c041e20030b80e420401070b5101803000900501566019510010b2446031140d205107400040c5803540041c076001d42401d20301d0b80c1e480c0c41c1440c1980c040b0390310390300c5030303070f80c0086201e00020154090058201c0ca80202e00d44180050000300c1106003580101905c80d10081c07400041c0c0490340c0070503452030480c0c500c8203c0b4040035100e4000503020b50050244110f181d4400c1d1140b400d80710040d800400b0011218927000c0150024001b0b0281280c58202c04d1121510b50301084c401d051049010303840218843c40e101450364020801d1800c002e00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 41815373 1250 41814123 41814127
    0x30209040507021f02090312160c0f24090b09030106090f0203061005030f0411010306030b04050109031206030203070504020703270305010506011103030f0c1c06090e030c0d05070c05060f180402 85
    0x21a54009101c0c02c1244d04240515a0744c00344401300d580c004a0300b44054208000f010002800b410303503d840d034084904000e6903140003000c40d01c0203003302003540421000151b1020f02404100303800c03001041e20344030040000075030b1a51645a00c040d210380600c04050141d02104001890604407a1400c5200151030b0403407952031701e01b4046114400c040c002503d040e800c2c4c500b5080c56400395005001440c0c00ac225040a0b18180c41c1c2107018100c044401c400091310020911030621442c01002c0030b0360b6009016084942c1002d0070300009400c18901502084000a8900d0740085c1b9603003c4c4580c40303010035148055908500740a42503c10140c1000e0412008640804120f10301009990308180072400d01c0405459143c08180a0b00940e540c0e1b00010141a4548840c130103140e00020403504000c400348503d9801c40035158882c007500455180c03540114034a114000d1041e8000c109852080102c50b1045840b00086001c0340c01c160400b24004000080d113989030708401c00802c2e00c00c02c0032a0254 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 41816623 1250 41815373 41815387
    0x6080109020a081f09110607050102030703060807120201112805010506030325050a0b09030702193c0b1210150e03010e010203041b080d050a0e01030209040507021f02 73
    0x442909a10f0084ca641d40380c0c0c07400ca040c00c0120150300c1c50a5028001d094030b49940080c03c00381d00030b500c10b5a00da400301703241040c000f5841901203610310407a103610790b40500200c16500152020910240c510a04d40240c2001d4114081d0588920346129005203a06400c0111407078440e0031280701038000da10a500030300c0001c000b5101c50f04107200c060141d01a6000011903864035602d8580c101c030740140b00702c03066070401c0500c103c0040075101550007100d030f44040854a200c003a038969000d009082c01c404a0b200030309451000d44140403040e200711a52410866000d050001c00030a0540001001c14000190303032103d41004c1d5001608800007000c00b5807550326160b030480700c0003c000007401c20f00218050240315541c080d80044070325000d01000350b60700c0c40c161505400950040810046152001d14040b90766000050b119411101c15182d040c90100014015500300f420901281e04068003040035402a48860080a00408454000b4085122100510465043c80340c900002c9144148514 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 41817873 1250 41816623 41816653
    0x9010b040807060c020402090a091b0e030c010f1b0b04030f021f0b010306030c080106030c060513090504081902060906150604050f010c02030a1208150d030e03070906080109020a08 79
    0x4601100e0090829001413507092003c03070041e0080b0464150b000c4241e01c00002c0717020310f0782c00c09a21082c40c01c0e0ba54000c0034002406860010309070060581541c0001415100b0394014800e1500c0b0180d42d040008152074030300400070a9140146040b01e540d8610018402095006162041c0ca20303407600140200288101c0c07100102c0ca1440048092207484083c81c2d903040c0d02913032044010319089401101c02030303241c66000380600420700c03045400c0c0c8289980024010702c00d8080d45c558000382d80742c81030032501d0b02020314003602c1c0242c01640d00b00c10030440202220407c0e05c98840f0b2005035005082c1b1403a01da804203062a000a103001e07159050221000902d0707a4242c226800d41e41d0881d41c6d49502102a00103e40c03050030604000e42500c555031340381003446044600701c1c104030b0f1656100360455075070020888107907240700481e42d00260301800c50000640035158010408d0000b138211034071a542d135002d290598555600801c01079544850710f40550070a04002d102621b40c91004000d520200458 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 41819123 1250 41817873 41817883
    0x90601050d050a0609060b13150c0f02030c060a02061f0605040e1008011404151103010b0702040b1009050f030105040314070609080703080114040b09070f02030705070b070209010b0408 81
    0x103081c00980c0ca2000801260403580650302400c0208010040700341c0300c00c4201016440800d40400520b2000e200040c0103082c1c0604915400145d9910081c4503002d40d120203264403040803ca80c1400740341c0fa1844d207a01c84070098420000990b0040c40d40d810311881e1540d41d00200740601121a50000d0240401904401160100c40c4482c0c0c0c074100642e500740a8218032500740d004085254286080101c605000c107510074001c501400c02c01034001c01c1d50600d5412036040200c0d83e4002403052004010940b000009441d00340d001420100d90b90501100090344070f40b40b80010001f29407100402d008a0174408404020f8131001d800820040c00c0c01c2d10043d06905031095040d418640004400c010414990070084d6071903882064280c80d445d00d45006850444240102d04001040b00a03022542c58075015a00204402612855550701c82c0401201c2c40050032507010300798401000010300195042050b070008010f120207142e25888540304004040f1410ba01203003100c0c0c81803005001c4180d021403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 41820373 1250 41819123 41819137
    0x120109020312070302070e04060c020615030a020d030c020901090203090f12070b07050f07060212070c03080412090806010308090405060306092e1401030312061206051b0304120e09060105 82
    0x1440d40d40f681290702e0124540049178200c002100d591b0414041001100c1e0025000c1e05581c3c0c003503441c40d0f07a80344210aa0300d80110382665040c0e001a510a0150512888044402d0f001c1c1c40d01004944842e00400c1d4a0882070b400002007543c001304111038084140413802024902401500000e00d20802c040124019080050180140e08004c641c00e24011402c807031881200b42121034891820382088030003034101c1c0c007010003603c0e1000c001521051240c048804181d42c9600c0759001030312140c581d40780541f5a1881ca406000da50300c008504e0703000410589009501c2000e0051762351300e000041c03001307880703000c3d0019010341d104000b4032000c854040340c0541c80c0c00100301015149591181152401c00c60300c000600d1440c50800d42004009600d000300703050340e0280e2601420b4842c0e60514004455041c41018512000d142d41480082c4075070f0817094200304002126038501100700d0740004c5550058408813030810320340e1040314a054102c116140da001080f40c45803030500c0c11000103003280c07103910 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 41821623 1250 41820373 41820403
    0xb070201080a0c090e04060504120c12030c0306090612060605060702060a140d05090f0d090b0901050921030406110d0507150e0607020a020301051602070501210203040305091201090203 81
    0x2c3c4041c42603c03404903400105044c00c0703041043d0809080c010300601c0203880079581e0301120445110b110340120341c12000b581e400940383c4800e80c40010101c000302940104101056110070000401c40800d010f020003400955904002e14130051410000301e42065000c5805104103000d141d01507600d1a05035040040281850f610142c1c0c601d00740c100c50311a140d0f0f6201c50900c2d10003403281c400310010303a400b00403400d50100d8821640c003040c1960074003013600c111030f525a4204001c0541e9485000900990100070f4929114146100070400803035955081d045226480800e082200951050071561031b108000c01502c080e00d15008000d080340b040420190100b05000c1e00000e080c800c80d48900150a040c800303807501030411680c000c0d2194601081030380319600700404501525a84c850b990002c0005e50000c040141c9810010344075100c800c10548910308024544201d1805d0300c1c001540715a100e50303201a618440f00c01005008814515800d8050385000340714001a00c00040c2514082108 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 41822873 1250 41821623 41821631
    0x1021c061a0c010f02030c0711090907120201020304030f05030909010f0303080406020912010606120e07050a05010818030301060804140307030804110f03010f090303140906010501050f09040516090b070201080a 92
    0x9000c82d14050440102c0005a1610001c02c20811541101c040c05442e44214100050b80d4200c000b003000b24241955203424a4004c0340e000c10260407a0a101c0c401c0c1407041c01924206030b030300d40716900350b0782c02c00d2006c2d209034000180e603070424545880d1b0a030240989070a04620740741503443c024001c41004000804103a40010701031300701d903107900c0c410300e10f0b5903074070002e0103119122840102058003141a642c40d080c2400b402582c0c210011552030300b41d038405001c05035400d10304170044694510140c07030204000c2200f071001e40b640300e05200441c040e20752512a464a404c291400741850804140701c04841d070002c1c012500002e03803144056070480d400811000c040d840d028000b50000e1200880250703d58a001c202239504c52490f0040c1e40386500030f807000c008101b50440031107a00300c81182c4040d0b05030404070044c803080d03000780080d10000300036252041c203000c2c080d0040f0302242d400795110103004488441e1031924991101155000d0110001c807107060003403c4e130001e00510f4000e4260b212032a11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 41824123 1250 41822873 41822887
    0x501120f111201020a0e0f0411190311120702190b06010e01140d14061c08130f0623040b0405010e06070b0f0405060601090509060103091a0901021c061a 67
    0xa2598009200e4042d000215640c15100c84042c15400304050494050882c4507080a60f0f0320340383c460001c001c903100124610309840c40584210b00e2941c5a0031030241542c41600703200d100355a00207000c0c10002c801e42e01c2034504140c034002e49400404c4608054050710001c03101c0c00070f0880c000041d0003070707070a081003c80b60381e2900050b6480c0449007095440041c0102d80c41e044110942c1101d40400e0394101c0640e42d0f80c96410521481006600607c82066113030b030004000544048010900d801150400c40c01c455294582150101c8403a0300240026884140c003070801c007603100c2b40d4100306070304c035156614052414100100718040d0703100f45811f0207041150014140c44201c11036005640c0078220b02e5251405c610307000486202690180c1d003500c108000506154054000e002c2074460042c225074032580c41c03030011030192401c030b03208840399900c41511b4045c2010215140c5e001e101c5101c000768842000c00291180c00e013403106542840360601c60b040000300c01145000c9105024540d2480c1d171108 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 41825373 1250 41824123 41824129
    0xf020901051b0a060e1b060c030913020c070e040605070309030813050f0d020718050603060a0515030a03030b010f080c030f0405030c0a050c0108010509060a091a06030a0902040501120f11 82
    0x603d0803014140c80c0c203040103002c00c1c0502107600c40c4020010200c0720b1003980200c1c148070b800c6c05180c3c0c2c50042548200100281440e060001103000c01c074461025140120120015041124551041100ca038040307081c002008101d000305940507a59140170406443c0a4030010b102c1d000240000b441040d02c06407043c140401444461100e5580c42c08640402c400c5010095542100303109555400c440c803042c520303120703945004403405a000207004024584507441000010400074041e240ea031681c034907102d030058a083c019441c0e0140a030f18001100d00390702001600d0081d11000800411451104218074110158140c030303005856002e80c039401c4d550b00d1801c039103103100d00c440b1115544104140002004000a1140caa907042a07880340c8441e41c1c1c801c14004408025140dc1d40d021046000601909105a00100001a0b6048502244105000418a0356200f07482d00c00c802507d80d2103140035030415008950040513127500c01c1200d01040d465406200c0a43c900c010301e020300c541c2035102c05503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 41826623 1250 41825373 41825383
    0x2100e03030f04080a050f150105090a0207150b1309050a0803040309030b010e0603070f0b0d0c0e04020d0e0708061b0c0c0603010603050f150303070b060402040306020712030f020901051b 82
    0xa035442c285680701d13290510340f030b41e884070150111181d100754000201a83e101080700e13024a1120600c4072030f01e9003468200092000c004102c400441d0f821311211000c00d000ba05520b1300514030313103c005181d1102000384603900c0300c06200035807003d0809040c500022800140c4020710f42d0040d1000f0b84945551408441e40c8807542d00c05442c0345445000480e10307090400600d4003400007241100c4081e99107030340143e241c1419204641c0ca4410a0100040d508031a81010040052500d481c800d2080c40c3c4002604903001900119020b594880845006040400031714025206080c005c0603245050309407000d00d8912110400c901500c0030580301301200c000c100030182894000c14141c2c403580c4a4034020000c000031210b450400c814007005c03c01c4006c58400c8034001c0a006400381d4170b01007403903d541c07060300c2d4003418158005908010000100b225803002e80303d2240300b4102c0c10380d400c65495000f42900d80e002c03050311103544104800300f1940e8114040726001d14405004660317143c140400e00b401c1c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 41827873 1250 41826623 41826637
    0x20f030a121103090d030c0305150f0a0317040f08030301030203070b1c02041202180403090b18030a0303020c06010b040608160c06090602040501020d08090d050309100906060515030402100e0303 85
    0xb00d2004070034031648580215040001d502a41d60821102d800c00c5402c5056a80580e5621050200c08040031310504080800030b507010800b40c40451038994a0380c03400f146a00c07040c41e240c03a15001260522100c030540c44403000030030300341c00154150b50450700041d442d032a00d441400e08400c0300117400c069090100300c0c05004035150000445d100c0d59189810380708200003a104910808402c0d02c042c544003001b2000d14000c0d5016580c048290b428914100d156a0020008240400c130217030200c0b5032607800f040303c1c080781d030311a68025889181c82c0e82003e20300541a0440102000140001e1004075480b03889039500110142413000c241e1906c04050324080034891000e0201800d20880d6810300c00d041d0020011110f003a403c490304c41026900c101d40c95141542c1e055495000516030018452240b406150060448402c1c0d60000300c07010311020840e01060300403a40141ca8071800c024078581b10328525020301054018514601e4290300080e400982d1380300600500a0901032040a600c0070070a403601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 41829123 1250 41827873 41827901
    0xc0e0709080a0b0a0e030711010f1101090503040602070e0705030a1a130603020a0501020c061b010b100201230108150714070803060405090f0607030c0e1f0807020f030a12 75
    0x180c90a400d0460715075808882440c4e03a40c1c02d02d811540d00382000030454282c81d4000d210000d03900048001103030020222070002c01008a1a140720410120030b22460107100d10440040d80d5031440c2c084040c2c20401c0310f5100051000002d81046180da41000440340c0c400e92903100012800d11003d101c070380107500c02400540080d058901e4544c030415aa112000340c1e1b00841d01404c00b555a9001280d40364072844900760442428006180c10140701d4036188020805d940c0040741d640b01d0100410710103e410050000141c0d11800b0540a0b41015040001c945101e0140c01c0d0240d814904900d1360f13050ba08884800c80004000002c02039442402c0c3c0307a02c13036401221100d0f511b818038104241c1907002940c41c135124a11b000e000c120340d50000540105080d694201810195a80800640080401c60652014894441010202651a000c03010714150551046071a0303102000f1000300f40c41c1004004005650201c201e45000c0d8800000340e1369030b8070701d03460034a80725101d111000024181003d030100b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 41830373 1250 41829123 41829133
    0x12090d060e010b0f040209010e0108040507031e0606140612071701120302060105030615060a02031e0408010c0c170a09030606030501140a0204030c030b04140601090507020c0303070c0e070908 84
    0x45901c030103410950340d4030000c82e0800c00c0366030403d080000324801c0c4050a8003080181c080354690794001c17070390701d82e000b406003040d074604c50790300d48a11003d0a44075248480c4200700e01c0d481000c0084038801c002c05000801400450350282d81c012541c0741c800e1080d0f00480828030303000912204e224141c034500303041c001242c10701c00396500c03c400030800c03400103403c80140c003c0b580045458100080c18231700c62001e290f41040c0c244000d000340f045d55130180200300c0443c00308000001100c0411128090840d00603030100c0c1d5911b01e458807007800c4034901d0020b0380403c8000c0c1c01000c041400c1300c8114001800320707560f0076610344141ea015540710f050703a800240241d04009001007404010f6010514419018000340341503520501c1c1007089201c0c902005120300d41014041c0003003511020b0003603000e485005140c0840010401c1e40340b904100742e010b6540d16440f4000c0200e2190305202c066001002a03000f5820100f035a035400f8054801c1d40280c1e0f814401542c0040c221a00c218241c400501020341030342c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 41831623 1250 41830373 41830391
    0x9030f0f07050307080c0a06030b0105040f120b06030105070f03050703090203060103150b030a08040e07210c0f050903060a050603120d02090301050c0a1b020411120103050c0d0512090d06 82
    0x81d0710741d0028481c681c880c0c00303010350028080707002041e404c4d0728960043c1003c00c060f003400c4040c6d00a01424000c03504203c000e0001048590f101010100607062110308888298200d160049001000600c1540641d0407c000d2003103003030b00840041525400c3e801c02041c280d644410490040c042c4440c065450b01c0f90a0000050005010070341c0c50098440d0018880d0b5203002c0103150703403109100700003840200204010850704002d0010b00d50000290325004c51105c42140b41e21707901c18081c0030801c40c41a914080001f4494003c0322114000496040040c282082080040d4482200600c0d100300540c43e0000a48070341d0742404003a01c80200001c2d00d0b80c440b101c01d00440000c1d0400601c1074025841c00300450703107000b4104142c030b0521074070b07a90359840301d8100d1485080c024040d00701240c2054a60060070a2901d90101610740412074800c07410b025851070504615203201c2250312806008044000ca02180c00482d0f24102d040b0b07070510084d5500760110104d01c03a107009a1000d0040303031501c0100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 41832873 1250 41831623 41831653
    0x1311070f0203070e0402010504120804090501030302240114040f0902090405030304030f0e0d140a0c09090204180b0414030c0102040906060f0306060221040902120f0a06030c030809030f 81
    0x2200e100740240c04644000e070f12914450080182600c010f80841e40600c0100141c00c0070340386403031402d4440c0016905160385c0700d41003419a2400e0700201c0140c1c201448a031202901c0400da080313030500d0b03601000111351500c13240340e01540c10000380c2401261240700b00030303035051184c00c42208183c0c050025401403400741011a01e0350400d44007100000e5424114441c05031040c2c2c0c0000b05c2e51002062000554400d0f0344a008000c44d6110611203030042e40c64807000b1540601c2c2049c014004010041644201841044222030301080301e04030a007003805880c004590565145580160b20800007619030001420540c518041d0600023285503000060110300d400650b0000411a09a82c58010f540e00101400b036041d0b400328003a03400183d10401407541190680d158004401c0305a00d0114078250315645817209a9004516078001c010000d070610405410501410750311040303076070381006880c3c02c540d2954604801d600c405000b00c140401c05400301e60b0144154403400c0780318801c90792044030351440c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 41834123 1250 41832873 41832893
    0x60a091703030f0703020703021504200402070804030f021305090106030209060609010206040201080c040f080106061e0c03080606040506031014040207050c0904050109121101060b0403020d02131107 87
    0x3680a0114040d4549034400030010580703020b042e0b40a160001030b5500c800c00c0b40290803003082a011403044c0f2200c5220a200241c400d80180d01550300d07002c1c4801141840c0d0b45a1081d15200d5000f01d01c1003040c0008a08100162016aa80074103030020342c0d807050000078000044210060702c054600010300421450551020044900c01d445081c21765a0300001c0011500030607000358056000b40c1c00040056211709900f980c003800d00a0040e04054940794009100411a006250325030340d20700c414071003943c018084540c0c400d18540e040b058241280d10003000c18555110080a21030303120081585a0748030826100a85000b408182e101d1400c0d101603680d000103442251036020880650203200d060500803142c101d40c0160041c0000c00d90903062041440c402441075405550319144140080d2034002c041c0c14205480c0d90340d610000c1100c0000782160031311792000081200810041005840d14840c00509a804445004a030314070ba030483d070042d1181900b4510100301c00510141004a440c60f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 41835373 1250 41834123 41834129
    0x3031306020c04050f0a09030908010e030c150c0f03090c060c0607030b1e06030a09020303072a0311060c070906060f1403040b01050907030b040c05040e09010c080114010905060a09 79
    0x400caa0300e034280c4405100495009960ba81701e0011500002040345032681c0002690612a2410f042d00f5039450202500b1501c241030300c3c0c4c240382c20004142c1c0c0703040000c10412680342c800d045900e0690800b06002e544a114003007009a83c044040b0004498580c1841003240c3c1c0728018010030b90300c903c0e50040c0f80e200c8400b100d106011a103031072500c2d4654140400c141c81d081043c04da195041000c00410414107800082044038800c0d101c0a052005880901c007030007000d88121907078100c5800100b280303007034503000e0f410301c02c4a2005201c0400105003c1111b6175a00f56054995a41e82c0c102e200110342011910740201c0b46a50808500061196010070210320744000d65441048000100c00fa0107481d101c00e443c0540001482e00050040e490540081900200141000600100803001190a89211450103000306001040412044600140d03255012684400070030550b00c142c031014007000010f0103450782c44141c00401040e070f039010343e5000c005084001d040c152500e00301d100041043c203080c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 41836623 1250 41835373 41835377
    0xf0b0c0c0607030e07061b0606150908030c070306090f02030d020c1003020c0706030c050409050f04030305070201050420040609020301180b060f03070e0a0302090f0901270b1503031306 81
    0x30010300014401e00c5425545a61a0301428901e86070100440703c03d0680001f640d101180800c2c844001141c922442006200031944140400030b841b0b009000c0c80392507031020929800c00c1210076a42c0c840070640c02c0903294802c900144041c800d05042d0045165050029094403596280503481900011019080d40003103070003020b00e00c50000224140c1c0141c3c855200e041d8400c0106014041c001c1e0003022225a032413414034106a0340e190381030f09803081078940004000c000b009000505926005041d03011103940001e1210b42811307643c60396001401483e42070071690070b0060180f166039503046400184030149080d500c0c1d503102c2d4001030340c1201404841c01460315140c2c0c070041d41d00780720080d69924842d00c43c1840c1156243c184c1500c0b540b008403000c56002820400102c0107903a8880064050440889101c0300c525000d03810508541901e0309130303041c940f12520446254201a1a0a121540d1200e600c61440d121880850b003032841070201c4030340c50b00011841030340148106400104960443d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 41837873 1250 41836623 41836633
    0x71401020a0e09060d080301140303130905100504050f06010c2307050907301404050a1506180b060705060124030605010e010e12060a020408070e070509010c0f0b0c0c 73
    0x401088048056820f00800ba01007d000400c100c81d50003c00010814029080d603103002d0441c070240b021101203400903216aa0394600348031003c04c43c191000082c02060381c0821040c1002c808010400d00003d001d1707810809030801103002c00110000c2c0c0b081030004001c00c0c82c1c0210400698a450f101c0902400340600441e00014003064070408403c500c0c008040402d1100550540300300a140c10700012850700350b030710b6800d1100700500e08200b10744500e000358050080c101251034200d0425007900080c54101d800c001c424402a8006054046520b41e070240006d00008440046035407800f6491018025000e6040001101034020342c14070222024a2078601824010050a4084800f68000c00b0b0010b030126280d00078550140c0800c0c8401d8400404584480e100d09210910384101180c40b10005034001c1410007062a04100e44400b40409000c01c013404d1906030801401070041001c018100310400d5021014000d801d1201c50b40c0c81c6c0c210440906900e0034407218403a65100398940e0300c00d4414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 41839123 1250 41837873 41837881
    0x60b04110403061a090601140702091008010b01090f06120f020307030902090703020c0d141308070801060b070f02060318121206030109020a05010305070201020d060f03020102010c05030714071401020a0e09 90
    0x150384c40040048200400c0000140c44020045440d64200b1304031a5009004002480159444201d035078441c40c10000306216007400d1150660a40ea001d01c032440c148400d01c0f4081c01444155620301045e0b4010786032495426a101004001038002070107907030180c80c8008180140d49a06411454616000759484201d649451404804030f02c00c0803003139000c503000403004400840c858114100c041406a01341810101c4010590050180c3c0b64490507450380003050800850100f8003440000380103440d9001d0a0818a8544200200c0d0403a0300904c115800000122004041e2840d042c04100c01421201403094008218840c0e61010742c035640c50340c4003213000850034a0140034010860381d0142c00f98940390300d001c0066010304030240035001136540a00c031045c1e450032a4843c00d0000c103078100004074201c2c40d5000181c21601c91001d12404c01204000b004542078101040d07400381542c00800340d83d509180d003850703149161083c0300d11a0075400081c002c2101d5a1141d11100071160032121404140c031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 41840373 1250 41839123 41839151
    0x204030b060a03050705090c0f0a02010b0a0b0c070524030c071a28020912070302040c0201020309070b0a050708030103140f0304060f0305061c0b011403010216020409060b0411040306 80
    0x2c0e05110041c040e5001d6003051103a0305141040540200040300e0150808003101d10007800c0c1d400034082100140e54640d461119440c086000e14000c02e0155503d514000d41000300b20344940540c050303d40a9007400019000546205101170b1408503000d0440d902ca0803c454603242c0c661014509407803072510a06882c04c02d19014100c1401545480812103440c980200c9138010391144010843e0b600e03501340000001034640080c640741050111014003802810352040204503410b08110204580c8144100301d1b4070440000d12400303807601244203640300d0011500031512449841e100400c000400b1000004215546071241030700e2a01c0d07801c2c3c6445c041c0e841c0c2d405a03640180c0c031610001488011079001380c1402503001d15042000a0640007401d0f440d804840c00c040044a01254030302c01c44001004403500040350580c04540031002549010680201c0c110549003240f00603114075540d030300076010050a03138840686020060000c0c880043d003401795020680081c4000d407121420607164240d50a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 41841623 1250 41840373 41840389
    0x40608090f0c010c0b070309050102040609030201120b0904030c0606180506011b08040902280c120903030f11100603060c020f0a020915121213060f0804032a060204030b06 75
    0x80b040e9911000340703c180c0c85a500c2020050300090600d982c6000c0c6a011490070700042003d0405510b58607521407951000607c030382004040c0300040d52800400c2c2e1016952007060300d070005d0b0189010813400c0c42070704104008214561201401030070614155041e40c545030403940c800e09003600c6942c11303801c0008a0107090103180701d00400c5400e0400c02408560b6060b8007030202c2d184056603a004400341500c407d40c080080c003508202040d40240d08000308854641c0c881c02d140002d00e055000c1c180703141e802814201080781d0403010304c290000160b00d243d00410105034065480201405001e6032801d158000b00110800040140642c59401042c0800069800d00d916030180642c2c1490f40c8210001030b4080b25030580c00c0d8852851104020105000c01155186881170501e4558900d100351107411030390740c25440581400120300c94004000d40041c0e0095210b82c040c00c201da60035202102501e0030a01003060b103400c3d8807943d00180c0500000b54050070981b880307080b031184540c40380000c002d815 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 41842873 1250 41841623 41841643
    0x50f060315120708010f0212010b0c07151115061509090103060e01060503070b120708010501081501020712030305010801050a05060d141014040203060604050601051b0c0402040608090f 81
    0x111110210054904141800300d0380d450222003a83d000503154000c207400e50b0032510050300c001e81c002c2103580d108414200e1050040c26a140c0d910725004004121a0f2196007511482038184401c0540d0300c4110f0068461401e2521102c041d6440444007180c984190201034800c07901511215002c50320300c8405604644c4400c60041c007100342a803855030b07200c000e86919110040d80d95220800011951010001103025140d00d03865551904800704440c00071000c028141d108001d4844010003150b6040002c240c0c010702e400d1000700c0c2203103041e00140d103441a5507026001d80307940c0d036080c1418940e0503030005058546c03c800030701507900c030f040c4030a06443c400d4848507444015400c1000001d00c502e540a24140c03469030640d0f5101044a403904110703140115a207140e10303e00c00c10403046103818401a5031101044500304002e08022000130000d0081c018101100c02821208410320202040011510b460080042d59a15181c0000408080c5c05a616006d50320614800d00c2400d04041401c540e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 41844123 1250 41842873 41842891
    0xb150f040312050309060a0e1509120f030a0f050705030a02070501110a030c090f0602060f040c050d0f11031b150903030304030207170606030303070807030209030a03020601140105030c0906070812040606050f0603 93
    0x1c02701d2440301e107154840d000d046040c1034860008201d410307281180150011540c642c04207920b03803400010410aaa4402e4128002c445c941410851800d0b00902500e030404403004005840c4c15252600703078010200ca07640701d01240700c041904001247d05070001c02c480c10b013035580c3c102210307038070100c1071025025402040c002d60002d00000c0c1c03000f14030884a0398090701880d589039880f6036820100388101c65424050700e221035469a140c05200da41c010041d4a0101a4010a500e8003800c0c000d030a00b202c07404c0810706c2090f40140b4142200c09050a070b418103030005090b00ea0301c1c101751034040d6445000e172007540f0904403040d00c848442c000108502e449008050090f6196940310b90b01154041002030164007455424000c08400d500c0420094070358501c41c0d00105050750500c0000b041e0b5000b503104190421108200704201c0d0040801550545407080d1840340e00c510b818580310402d40154104403012240d403108000078000c0c0e541101007140c80c1615003468000c00102404032030312007100c81c280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 41845373 1250 41844123 41844133
    0x90507090801091e02032e0c020c0906040209010509040f1d07140d0204112b020c030409110909040f02100302030411010c11060a020102120601030b150f040312050309060a0e 76
    0x2200c00340c240c0b1800c100303840182500c000d41041d02810364820300141d4074a80d070141f007915145840d480b612504c2501d15640c00140042501c2000154a100c0c001301058000e03500822000c5050340103400340c9610b00c1e0020003e0000070300100010004000c410788218900c0302c1c1040154070448041140026903400e1401004051203900c18400701c6282820201e8200d03030340300c600c08441c072000790140902449005134047c1e4602581100c801ea000d103030b811020240e104014000a82c00004120740845a2108000c40c40c3c40310085074100c98040c2605480d005010751003008208500f044071081c9941c400c031241c06102258000481c00c9001c00c0304e00400000380c0300404241580141400c0010341c2c400c240100030200007101150503a00300010b4400540e4012403440c01c4500801806980140c0178a010049080e00800044080c0c10586203200301c0200040c80e101222503101c100c5000e1030300b00c007440c550b00c15203030b1f070007009648119030142440c081c20010502910301400380c0241c0018080c0200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 41846623 1250 41845373 41845403
    0x40305031602060d050934090908040b0406120608011802041d010f06030308090a0203060708090307120c021809030301060302210106020c031e03030f070e030709050709080109 77
    0x9a90070881d4182c1e8010014004004510313401d0184174802d1043d00090024144000400700d200b201c0145003828014030011040c00384e80700c500d0382c141102c840c150045550303c250b05203101d051040d134000d581c00c41030019002c40c60039005030300c440031a01c40030004c001c0346035030324102807c81e03465000d080512001076124a001d4a026081904040310341034005a54070a6016910708441600c2c80410f5881e8071940c0401c00d0640020580764800b4501b40509204907681c0d000035110400100700d40148202d070030118a001ca010819541910703400b40b00e84918000e0340001a024101c1d00200300c0c0b2491444c0107211210241c0c1c904540140074010003182983d081c55025000b80d0002c4c620480014215074012103504108880d160081081e500075100f039a000409140c20040d00305102225021860728140c1d6444002003142c0d449030b0040c0e00b82c43c180d00d54017000c451440d54900b450b0b915104012005c1400c1455138480c030f00522207515022080c541d0b5810403426203542120103000020048115 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 41847873 1250 41846623 41846647
    0x10605010c060b0121051005271f06050301030c050d030f050313020607060b040c0809030301060c11030604050d0201060807050102032d040b0301051005040e1321020a060c0504030503 80
    0x243e81d1141c0c05052049445030203141940391025024410000d064594040c841c0c04050920218043c00b0107446a0000d940c0d0900b030361107001c0c44801716034000c20f9006c000038001200c200700546a00d40078054107000700c2e524000100349800078082039901003c09440040c7d6440c0500d54918860740c182c44440300a01a450281ca85410080c4074a5800c021204607400503600c00c00103102a5200e014006078031002d90f07003444200d580c0b8464800a11070080b0502c000c0ba0000426241181c10910784409100307001e2501003000c0c41070841e80c0c1d8240c40354409110030400041880c5207403040703d90081204503900c6000d995200303040d10030b0714056002081070072030b907a1800da8905800001c03a101d4a004034a2500d51a0042d032007640b00c1c3d0183d10000c80103021514104400c400c0030b1000303242142c2001c0c20001c003042c01c490f01400a05102c0f240342528020000124580c6420366005041000000502d0f48041d45070240c2403c00c4031168a01030b403100041b40510700b55010741c0d41200042d8142039000503c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 41849123 1250 41847873 41847881
    0x80606010f030b01021005040c08100f05090604020a0905060406051201021801080712020903160b041d010e010909020f1905130e03030105100207030f12110601080c01050f04150e0111010605010c06 86
    0x183e642c409d00d1a00440c00c010200034005409901103000104401d50b542d01c03404407440648203d00540180040c4405a59641c6900c0240c0e0061a00051a41c81d4600000c00601d076603800190007910b241c000420502c41076000d41789000c5034007464604c0003002d10045075218800c41d6106e010070446601d801c41c0000c2039020b8448400b015080382c00c03800c0c450f4074641c040000d5900005810348001028040e40050341201c001640222040c80e0407541811941d0751403000500078030a0080c0d0b102c0c290300c190b40e1000000200c038200542484910714a0707018580191859028540c003505644000a0a54409106103501c0381d000f0b00180d410740e401c000400030403443d00c108507411440b80c3c0300080041400304280b10725003442540410046142c4010107041184e4250300a00913401210040000842c0480c0161582009281443d564030410501c0b030781178012500900d140c2c103800e00040a4198100002504184003600c40c01d408003503024543e803d0315014002c1030700103a007668401d00007a4540d08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 41850373 1250 41849123 41849131
    0x1112070303091a0709080102030402100305190501030605060f01050f040311011206060f03050603010b03061605041701020a0305130507030320031c0c020706171005030601080606010f030b01021005 86
    0x600401c10707407942e40354200c0c3c2e818403c407500d0040742681e0a11003d03a4015403218000c3c05a00029421440c00b900011060006148202c041c140c542000612680140300407560740341c4007040400c15540c481c146500100411294a8003400203540c4d4443c1540c09942900ca050790020300c000c1c5040e08696658400406881c13100781800303880c8041d80c146580a0181070300ad8200c03070f0360b082e2603203002000041c20340700040d009a009900d840c0d18410300703440200301c0d258071580d0001c040c10014a110022240e502c03890b88004002c5602e607124624a00b0190002d025590316554140200e84404003209001540311900a0807548511403c00c006802105c4000c510000300a1285d003618840d0001400d651001318184011003031075802c00201445031041044400742c1c1d1004159050070100702404221305900618144508800002d0984030340940c2e1402500026047c0c0b459942c0d034400e420340d82c1b081680e100703001c2000480000ba01e04d100e84503811207804142c0c0148181c0807011220001814050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 41851623 1250 41850373 41850377
    0x501020f012d0612111c15110f0d05190b0307030f05010219020105040b2406070507051206011d060a0b0a0903051e1002030603030906130e040b06040b0111120703 71
    0xba9002540700d9407400e0030200c2c00c5c0500b04a10540e022001001621055007070154030300d180300c0c41c549012a01e8540070340c58543d100c0714001891035107124064010f01400c042c941c0901400034003004903801c15000103004072818040c00a48200c00007050050342c021044094160348078220401c04251840c525001c09070182000500d42480c401d8011030111510b034501303003d42e442e1018002002205401513900c031304684420305100c00d42045400c03c0d0900e40200503c10000030500c802400b805004a100906c002440400b200c2c1903407200c0c50f22803100344a00503c040d440300e100e501c031495240c0301c0751155a0041008107041d00302605030200d900301282c080104505410040300285040000107410000106108640c0155120181c070b000c1800b000c0340d92050040c01481440d8038004140c0d0741100342140c0c81601c801b15400c01c42003070100b40e03100e0540c0d08441801d100c18400010007640c020141a6001d000004034180152a04030850603001060b601c0b4000341c0e03880000d0640070300445417080c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 41852873 1250 41851623 41851631
    0x3120604053c0109060e0601021203060d110603010f0806070507050c01080a020c1002031602030c070303080c0c06010f06031404020a05090a02130e090f0f03070201052506060501020f012d 82
    0x40b8681d4003020360260032005545540b80d82c18050502c4c40715101c1c0d40060709200524009590704e80b00042804040d06d164001c000786c41204080003910b40c20300009000141c800f0381c4070b683d80c2a40d03086640c030601c0783c03d680d0301860700441d0500c1e11031000c076014903402070300500e50720056000450740514014001a0155428444282900303402d001c02d8800301744541025031241030005a482c0e000800001c0c80f01590301c10016480300100c0480d800d012260941000030303680e0380c0d490105169116010640d4014001c0300004079000840302d030780e44140d50f4a40d8042241c111880311141640d042503034040d500240b80e26040043c1c0c07401c1100345910800c0541c02500704a58504403505200083d0881c001003c000010042d008600b041a440400c26440040c000d83d000d100c0c0503500d03840b4049020f81000000a02845029909610002007508010703108045e0307100d83c00c0140003003280c3d0141c64010301840d1054001c90605025181c4034031500b1182c03000c4503521401d030602c2c100d0818001c0ca502074036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 41854123 1250 41852873 41852971
    0xe0a0309030813030f0c0f090209130504050f06130c0b040303021e100f0618090201080a09020103061a070302070803030106050d090507090504080408070b180d0203010b120312060405 80
    0xc802d01400161045030070418450410802c02e006031fa0a800118480781b05014260040c2d0341c80381d40001d00c41002200241685941c00c0035800e2102e4010108074034840c0e8800d2041080c20343ca02038215a00a1603042d00b40c0361290000f070014400c500c40500181e005040040e448005070b88409452806c260407160150560350b220002d03101e4030603909800c555141400c21490021a010000c4580b00f41410070a0f0445a8006080108042c11002d0b80c02d07620305a240459000303902c4080078100b881c5254006121044c4029526884040102d0050050724000034442d01d002043d40c0c141c48a80e21f0301800e00541d4022000184912602550036105980000400440c01d1082c0e074001d42c0544c1007030b599507042132422443c00c01d032640002450201004440c540c0c40c08005041c047d603c0407281c4a14142c4107000007809800000342903944405e800b28100c040c104000014443c03110880c40186050343c401007000300f00c41c0100c540d000c3d003071380d14010943e0041c98013500d44900c02000694048002c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 41855373 1250 41854123 41854133
    0x50705070b090a0b07030606030e07030201051c0209040501090f1a09150a090501060302030115020d02030702040e0c04050a020c070609030f080f12010b0418022107030914060a0e0a030903081303 85
    0x1c011703140240425661602808042d62602442031151100c00051800358955030009120f403180848410a016041d00c074840d0b17450302d64044550041c0d000b00140134551b11030350014010184028128843e41c90700121017003900800002d1f48400e42c000300a05241c4c0e540c401c0502c0e08140b45c100c04c80c0d02c203490400100c0c400c1a54802d060282c966940e0041e103a40c10040c01a203000d5441c0c42c400159880f10740c5011126500100301e07003c03107605403004940d44c41da10bd43c151810043e1a00c1e984d0050400c001c00502102540c05003200e410800200d44100b039944c80241c03002a10742c00003030407442595138950b02064041000b02415084210081d2030600d440c400c0c81c1d000c5d4001e0f0000381c04014002420402c0340e01500c0e2003c0c100c00300203005c614007868004060040c4041c04c0342c030744070050210f0000e8100381c001d5201441058109800308442c44440c04c03040d032114021a2860901490a0101d07480300c0c8000030300c46034650745078650703c0010341151111200350700405000c2c0302c0c44040e4400840050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 41856623 1250 41855373 41855393
    0x601060e1302031f170303150f060304030201090c05040c08010e04030504080d171014130618020903010c0215040303051f0303050a03200405060708040914100504050705070b090a 78
    0x150380001c004815101692100c180307001580c5c00700e0005840d00b85194002d10000c01225007004035122220410080400400d0405000c0c1007190307400304012007080103068064101e4040584a550035290145e00e40080200700c40842c162000003c0c4a40010700401018804294010f0301a0802e50700306651495802d10b0111106042d000080702d4842c0c40740c41072905280160400300741100090a6420000382c60b1140b84161380042c0b140e100c0d40548640024168408000f5100c1d428010303d9081c0c8140305034020b58000c2c0880f600a42c68016040c03d0103201050802c000d1801c003042c0e04a545076a2011070281401900440f601c03541c1d2070342c0aa095600a11107030081d072083d110030351618100c0b4009401c44045046c1c0c4040340d03038044100802440700b40100d130140c0d6000c03141b664548065040005142c09150001050a03140081c131072001000014001d200e543c1e40711140b41c61039100c00520040d540266000e50110340c040c441480040d42840712954480341c00310868030b8400c0b041d15014006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 41857873 1250 41856623 41856631
    0x40c0504060305150c09010c110a15020705031c091a041d0603010e010c020309010302070507080109110909070605030c0a020c130c02010b030c0604031b0305030a0306050a05010806030601060e130203 87
    0x1651001c100d0099604c0c003a241d265200e400d20016508068002001800c1910410700080013110208021040359480409500c041c0c810449503c0c030443d46014013a5403640c00b4004c2c54840e124110304001c059001c20020b8100350324136034424007428588800465040405200040038240a21020035a100000c410007000054441c030380d010f07030500390b0a142c2103607041030104c042a410043e03502e03e107940001c200d0300700010a181c01640c5400504105040004a401400295082003407090a010f0700e09140d405500e0102c80345080c503202d0ba0040d544e2140b481c402d12011981c00e200061020070340340041d1000050700e005a407400d41107000042c1c100406803170390592295944a00344a4035a0922410982c0c10059000341891190b603400600d281c0a03901c00142030181c143d00520081c0300003900440115404022680c0711155010041d02504280c05958019012200e0001c1c1640c417a0024600503c0c020340900420713428604104d070310f045c40b20840d0b50400b00810034150b900d28148011885 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 41859123 1250 41857873 41857883
    0x1c020304090506060a080c03060a0e0103080304050d08070f050d060905130c050a35060c0c0606090c0d05150d0c0f0b09010207141305010b0c010615050f03040c05040603 74
    0x18035410850000201c4101a1000707000e54828030911846a070850804c41e0003e0344100440d480750b940c24001030801e07040e0341000701c01d1a1388400001c100020800514010740c815815100e03500b01085c1d0440d81c104089036000006140c5400d146c071054082d4006051040413260041000341d16040c02c001510401c0d00c480100305180f0f02410b09118120f20114082e01040790000e400c24645901420085018602c244811038801c0303001e194080c5090030000300c110000250782071842e19200c280b500d5040702d44458810b0090350001005850114a0750303114101e004d1a2905083c40d031840320008100041810100d90548080d41c0304903514005001c0c0c2180c440c1d41d001011508001e503c4070300c458583c2c4640b050010034000315074141e0b000310303880042c0e50240c44a40c2482c1e0310b610002c1e00c414940003d407860645441e0000c40c0c0c02062800070580c0000c020004d00640b070f91082c21000412030f1103078880026500b030154007402004a001144c20034010402030800380e498070009012100140c2c0304441d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 41860373 1250 41859123 41859127
    0x40c17100513030f03050105061b0304030b07110609010513030c0c0503030c07062a0b090a0807060b0f01182303070b0915130303050a0512041202190c05010302030601021c0203 77
    0xc209644900c00e00c003804c00d185411701044d45070401041e09801981c0003011003004d04021403044100410540d002560010b002040b03900303000001a040031011686e03030324031380540c0307000034080481402100d0003002e00010103082541d89031402c0b265a24642d408461403050143c00007090381e401c001074811500c201c07000d080320a10700240940b1900e078000d40c40020020110035489028107403104075982d140c0240c4410540d61320110031509005901500805101011032004180500d030307881008180020f80d075450100c044c100064420480001205c162140c0c030401c24406000450617020460b40c00503c01c0c8400f082503000a41401b5154100511001000c10314100038a0041d110309801e003031948d4140c0c40e2014040d071111130080c6c20f00028051180c0080d403010b0141c401c8007180c4c500311503500a024181010f00e40580d158000050341c074018450801d54000649900048944032940b03d50891034842ca400e0054001c2d41005003a41e055000717442a41400e0310501a1100300d11b000c540c007440e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 41861623 1250 41860373 41860411
    0x11a01020d03050c0708070212060c0306040e0613150b030303010308030403030b0a03050d030903090306180203011a06091504030206131a07050a02130b060a0207030515040c171005 79
    0xa1911410760810300c00c240c288001e001d002c8403030404980040d500110750740c2d600d0003d800803826603501c0309070403081c0740724200c10851503180a002641c098841100c041c0400c41d400d45000b540c1d0003058a0214030f08100c0016440020100e0214040f2040c119201045680f901d0f00081e042d90801da10507220740e42d000040000300f640c10301c502226104103c600780c000364110f4a42c1d0360383c1e4040d000c587c410715955810060501d40100201001107500100601c5080300101c4948224915260304a00942c03c0c141840c040088070300302c40040d09009020b590900070b000c001c2005510061043c0b05010300100404070250f12080d0003480a203011030381030720a4500e4125490116415030312622071009080c0b110074000790002c82c030344c144a0b4040b9001d05100301e00d412002c0043c0f5062480c66484030b000a4043c42c00c5401003201000c41340502c0a0360015070541107104120441218003d205002d0000705100b10400220400820301125080b1405003043c5604041142c5043e980c0314508000d4840c1c903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 41862873 1250 41861623 41861627
    0x303020604060b0a0b040603050403090b0a11060703290a0e0708010608060a030309090e10060f0501031109090c03070513030b15010f02030a05300f1f14060c011a01 72
    0x85040c110068925445080c58117161550900880c0944010552110080b9003031600c1269442d02600d41c40074525690f100e02040507109236048e1103c100c060080c8400034170701038040d04c2041c07020404a000e424004034020140e151010b030003030034140d0051642e000481c00b25078a1820390710440d640d844040c4294103240c0080e0003482c00510031845200b900e0020301c0040d80c414032031011600b4446001c505040c0c00b40d82541443d031101c42211100f45030100009410408040341740440d042030320704000720245145180e405210741034045400007000d80c04250032980795401580e1010f070500d404d500f000b03620529021072035056401599408030400c24403410b81c0610407403c0000409003407080c1c0b14281010065201d02070b200c1401c060107008140010041c0851802819220700c20060450001341e40000b17003031000066407443c032008410800907441114803550400028200304132000541c2c60f24038101d03007010202c034141d901f101f000d001500494801f400707609212072412040100c414000c41c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 41864123 1250 41862873 41862881
    0x60e0a0519020304020f0418140601061107030807030f02030d050103050c0405010608070f20060f090c0d0807060507090302030610060e040605010e091b0f0703020d0e1c060e010204030302060406 85
    0x968054034410428840180d86410040203002e00030b0b6070210f03e100c8c454404003140c61251320050400811041c14060ba03600c0415518103079803060701c54188024160112982c1e03541c01740002802036000300600c50109010703640b0082c1c020128030403030340780c003800300030203002e40c0d4081e801110143d020301c8480c000c034949030080d01d0242c205450b112b0301601c6c0c111001082e440c0348640d000280802d15040345450044c61041040108544044603a0340c200901580b010b000c0880c3c48021600036400004894640001c50440241c0c01507400c50a002640d102c00340108006407429007440701100c8000016101802240d200340b00c28600303e038800c0d107041c101811050403008058451454200300340030503a089059002801400c2c5c0700c0b2841c2d070703603502c20710803100b018040c1803003c800e070100d15464161001130003000030703c3c825420b4910014110f42e06072140200341100550050050300484165032503c503515211038098100400d9000b82d03070646508a9000382c00c00e0380141c000350100801d2008a0003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 41865373 1250 41864123 41864161
    0x703020f010f05040b1303121a04110909070807020c0a090203090c06040b070609060b0901170708031207120902060408100e0708030319090611071b0e07030906060e0a05 74
    0x100344014a82691405501d105c01001011815041c0705040700b03061160601d22000301000c0300802c44195080c481c0b81c1900740c482c510764032841c2001c00130304150014005541e8407100160510342291a040c6081d81c0545000b44030400314031a1040301866503039140c10440080c4560000141e480c10b00100c0c40e4107101000c107100340242030810082000030600000c594010703030049c0c0001802c0c101c80c504800a070140840d8907610521440c00415030b00900d0f44842095082c06088403040e9640e05074654503030096104030000703012403000040000f4000c00024a01c40e600010020b1350201550003e10a5007154008418640c41001490b12600d81842218120500c1400808406107024440c55603480014001d400c13107100c2200c0058840f0b002e81100d026954842c03028490040e50001441168200c40415940c0714910214125030302442d148081c01c0d05c0c2d110002d014140d6131040d041d000762144c0c40c1c0498985035501e41c001190940c00070180d00441500342c011480f07041800b10144c0c041003682d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 41866623 1250 41865373 41865401
    0x9040b0916050a12060212040515090a03120b030309040905010b0a12050a1205070b0106170708060d140709020c1605030319140f030405010504021c0206030406020f040b0703020f01 79
    0x81e007880070f035031107900202c00c031484151100d02810701494030a020380155491820061800814001004404150102400c0100149204550700c4084050740c3d64004140900804c3c14040001520b04458010849124003c1e08480c81c008079000850304496015800f55126503441aa0186901c2d2482035000200a850035024205510341c40702500c601c080c50004041e400e260310360703074107040c040c50030344121036004085402030350382d100c0008c0d1500c3d10802c1c02c03100c0d4a40d0785000419444c058500c25000f1440603140c0540350005546105007041d58009203082b80c418442e000640042c180001c000d8090820040c1110100111000041c27003429045a0f200b500180204500c4c180500c001c05001c4040c0c0ca806242100c607810320101c2d40c8103055030060200d10000c204020311805411540c001e85c400c1c0c66416114581e5180c1d40c24a0f0b05180000b94446000c10100740030038096000342c801400c1c150f82d04c0e03190a07642c400d540c0c490750100303c04801581000c000400b8a11081c400e50900ba00c00d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 41867873 1250 41866623 41866663
    0x3150f090f03190201090221070509010e040311030913090b0105060c0d05090a030212010b0f030102040f12050c0a030f0c06020303060d030c0302010608060c0d0f0b010c150b09040b09 80
    0x15400094072409543e00d41d500120500584500c0300e4800d40004490f141c0160030701d00c0401141c04031004c540704c1011101e010340f0803070500207210f0410064a904894210b466407a071a1280c0d5002c641181da0021a15241e101c10b20130003203c0c0c0d45041d40403a80c0c0da0b0a070700020f80d104242c0380c00382d00007205901191250f2028052035100b0000400c15001e5075666141c4159544a020002440b464040c0c0010350005546041824034010540c04070070b105e4000c80755407a0040001003090300740e210380d00400181d07048003601080002903091110204070b01c00d00c1501e010341040004a0140c0e001903009940411050190f04140f008103070103000903081d00e1010f58a1403a0280120ba02c020360300030000c0030400c00840901c10303d4401c1d8130120141c072049003954050700744002e02c482c00c3d802c8184e40c0d4800d94540300c091410b68001c5c1c4211184a0750684030718100000d2510343d4032110300c8103444071618a44941c502c4600e0303940c81c040c45108912940706820141840142146401c8241d0b04004803c420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 41869123 1250 41867873 41867893
    0x109140a141204150210060303082e0909020604080a030512090f0604020909100f0f0638070803010905150301150e0a0608030403290c090402030c0903150f09 69
    0x80b4100c8080c0c0b0913180c1007080203181034000328030304400d10400d1002a0b161004c08002c1580c0841c146004a8400141c0e1107000850000d440c101c011031001304500762140c030400c00941140b40c01000045000501c2141426900e0f20500e05041c0ea006080f00011000204450f6032044500155002070710240113195541c01400303176540d22200940041d00c12200c540008083c040108100c981d030a8041c80140050b2150442d4038000d08944590984d0305811711001007111344030300c1008c503044003c1040b6401c03c100161442c403007000303a01d0403089015804200320800b040042c80154000c0c48124400549841c1655007214444581009507111380d0408400280c0d0b41680382e08001030741da00150901e195120850300c00010040c9501c40b81c0c403400045000000e0090120102c0e603050411f5544240388072805c014030700c00d100201c90007100d10400b44904071080c1001d501940d48241c075040054544980c0710002072034082c84101d8601040a0041002004a8103c4805070040c1140c030040c00300d030784 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 41870373 1250 41869123 41869153
    0x915050708041121011d07150e0402160b0c07030305010b030c2215050c1006080d18180209040b01030c02030a03020723160b0708041401020109140a14 66
    0x2002c040c50303a00c181040540680109414102e03c4d0b03007850458000c0104407011440110b200325501664034460150350000030b40031500c6001c2490111582d41c40010000310001044000d40080c0540b4400b91a079102803400100d10000240c0030306080001070740c950599180090644405800c01c5c1c080b0042030080c03085c1c58813880c01341d400006142c200d218003007025140048410449078070004806200ca0000003e182e081401040300700c040c1001ea415145e02e00400304180c5003244500d40e840e501401c2c005c07020b184501c0faa0508040c00001c0c0000c800e90740e9800c446106020780014450700d5001803018041d24040c4a5a81c1c1030787e003820288940e00103100003a441e8020030304141d0900d50001041010010b07081c0204060320320003914010010b0f801c4507195521140715000c0584006030700004507400d0111070a4408460388446010310f040e00740190340c40390082c0140d140307040d903490b51065000035203450401050341036094020400c22546041c0480d140b48004060718842c0c01c000c24480000d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 41871623 1250 41870373 41870393
    0x703080403082e05040e010902031c03110a08011d04030e1e040c020a030207121115090406060201020d0c08011a0a020a0b07090509070e0904031101020706091505070804 74
    0x207805040400301c40e0786800c15054007501000c5044908144200e0045542c1c860340c11400903290300740e9007000034440c01002142259240507004e540341d030040443d5102806070310b001884807035551802069a2000c09601e1201d034001494010214030114010300103440c1e018010040c02c29054401c0c0502d003040d4902070065004103900600400c03000b65004502c1486100d03207030a241018004001d0742d0302280009448494090f0114014001e4940001d1464004544000c009812030400301e0000c009c6c0d410403698071f0541100881101050002543c00c2e0703110b1150600403c5035400260ba280032202044044900e00d001050922062100502003a262051541c0702645e000c140c0310740d503004848043c2c1c83c00c100141c00407c05400c0400f042075065200700c19408460b0181c0785a030380385e00c601c141034401180e45105142c122400c0000100440e120383c021105d445059000107241c27a4041e03c0d540103840038040c09071041c04116440402008040c450550b00248621745500c05041c0b0317a44550b918 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 41872873 1250 41871623 41871631
    0xa030e0d12030203090708030301030506010302011e09060c020a090510030b07030e07141c060b100c0803070c060608030a05180307030213050601180e180105070e150d110c060903070308 81
    0x2d540840016246002005136102414180d0110707600c961756450550340d00c40c403d01040380000c1c150700760041c40d40042146580b1480303803601c61408003414100112554180e105050781e000c400b18400045520461044501441d0401c01e1945018210b040244c04001c002c0c00d030350100b5103040d200c2e41d2482c00201d4818281c50144030548540e100310000607548540b48001c1c800300c40410302c1181c042010b994000d0300904c02c00ea81d80000061803d83c240c41d242020b05014242c1d400070400509003074410004144c1041c4240e4002450f1900c480105180d074210303c1c83c83c00401c000050115401070388205800724440b0480084c519a4196800b041302139138a5503848600f261a803000c00e18513030282c0250185a000c14031280f82c8580e41d601405034019040d0b950504582c401484503a902d00306000b624403c0d20285c40d070000f10f0038640141310311610a5210700500e910103201080d61a40c0c64000c18000001104c020398460100303000860418001800c01034899004104840020343c0084e4103681c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 41874123 1250 41872873 41872877
    0x20f0a0201050705010917030411030105010b0703031d030409020903011503050c01050c01110d02040611010c051602040b060f0408061f1403100e01020d0b01030b0f06070819020a030e0d12 82
    0x841c0f07501d02d8442e0160540c400e00030708070440f491030007a180a941e009103100d540550381030155444c5440a00d1b00b29a405e02602920181c100022404640241c03c0301c1c0842d40c1c400d4801ea0001d00c11315000d82140c000e90441c140094000803100080e2800f402120601e00e2030038650b9006c83c0c46c554907155250500c820300d41c10b200f00462500d10100d0298040a1300e0310100d00050350f91032039003034544020341c4180120700100c0c1c0d90b030048001021052040c0d41c0b100340300303845075071071300e400106102204007126800300e17480768a585c40b50b100c0b5100d14003c0c105482d20311a05944071410451803e043c1400205074900c0e480c5604d0641c44c411050024480c00c50b0341400003510384483d08408a170805140d03649044429050a5403110110415030080030b8240900350100500103141004500b034841088403540d03c44c0060010031401d01d402c02c01400c05601c2a40341514144002e14054101d010f1814080090f801407000d01061680010480c500e010040356001c2c4000d41c180d58500194034040308040c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 41875373 1250 41874123 41874127
    0x2901080903070b040c180216060e0703020d060f0b0303030403020a0807020111030a1805011107030605060f090901150515070609022805030106090c020703080304020627030c01020f0a020105 83
    0x24844041c03084a580c41e8220440001600d8a0305141d00703082c040b031151034817000700c403001c0d410815042d1090751014021f80d8500c280b10055504c801000d081d003541c5c2c3c10304a025041c0000f00594400948424681c45175501042c0307280c800078464100c0e2040c100c07044c0a9002001040300017a804520071102c1503000c16080c0e02c5058a0004840340c0600d0701900c51b5a200c001031000215401002904000603001d000000b495100c40c01101e2080d510b450350315140c1d200710320501c0082e03110340065502440103402498200c01e0b00b40060342c50b02069440e00700d6a551018640104a82e100300c50001d0841915004949100c0c2143d07541a44900c0001518403540d44542200b1991a044000c1074800c040819a080000d25031180c45424100e00c00d891203586010400249040c05014a490302140b0f500640b001903d1a2100280b135400100101e0344402d040040341a0560104620a1a0400030441d0301210341d03000d050510b8082c0e40e0760700c10b06651009402c051902c8000844507000c90782860255 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 41876623 1250 41875373 41875381
    0xf03070b0703080408072f010e0102030a080a2a091d010308070c03021002030d05010f0503070303080a0906060905060301051005031c0c080c1f05040506010b0f07020405041104290108 80
    0x40c11b020301a8024001c0e101513070a075142d040c05541040001c251106010303541042a001502c94002c03081c00103016820602541c10007500807a112903022580d0758001c1600c81b00304072000300c00b07030308a0b034a00312020040426100d111b901007a0100584019240f030385440c0c00004124a510780144001031100e60001601ca0410680c42c0c0740034015a030180142d2103640325600003039145d4108010592050345018000070303002044200700012100d000d00588225801d5480441c4c5845008107040760301354a4503c0c54002540c0c500c211001003411074000152070924000b00f50a5a40c040d0124143c0f0b0030450f07090007141d03000b0400903a500620007108a007021580c10640741120390480c00b5080b150080780718041500049030030340e450500441c080304c8813903050500b24100d500c240c501a04c240c2c05280148812041c3c4c9006046403044070340f205051111640c00601a1103044404948001d4130307517041c171a1418240182c0103203000700d00700c0d5084005c4440c0e070210f80700d041b030414604000d114170200b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 41877873 1250 41876623 41876633
    0x10f03140307050a0c17030f0f1b0a15061e050603060f0d05030304060e060708010504050414010207060605040b0a18050406060807032402041d0612070e01050f03070b07030804 77
    0x100ca81941c8070041d42d0400750780d03041040e114150351180386d0000f01d40c1c90305100c0c20030010088588404804907030750b08050f0302c100603910036004a14403090203509294039200c50310b000c02440d194107200c0c0d900c84200a00c141d030218281d806942c041000318000402c40846414080036403000d032501034481580b03c0e503a00c03000034601c050013901585c00441c5101c8030000d018002c4010751103a4052201844181e2150a003982d440c502150250001a01c0380e00522241c902a00150f8005001c0c0e4403005600e001030540314220b0303002403800c944507079035200b081040b4107080c055803c080b007048072100300d0986814124100b10084084080403036603140001402c00206501c500b025007201c90803108559213034a8440e800e21000c61503196086034040709550360340240d0080300c4c2a941d6860006400d503d118000c91104400681480c0c0d0180441c0304021400c04200554401482c12461201c041d5142009100c00001c450541d40c3c02508448010301c002c40c4030f482250013259040c039060b101c981e038500b41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 41879123 1250 41877873 41877877
    0x80402130f020f1806040e010905070903060203160915051b0a0501020c0312011202130209040905010203100e0603070303081306060b0a09050112050603100902030109020405070f080106020303010f031403 89
    0x29079519803001c01d508500316000c402410380490080340745400c0030b51050070480303980501d2103002c0c041e10702c3d840180023000c09500b0035604010241003245142d5220f40d104426a0402c03520300500301c216003169805158010741c40001040c07440305040700c14440382c000030218810054000c000450300711071541340c40c108008030042c26421a00840d00c0344104203c4a8403a4421b072482d10f00c444114001081d6108081c0c2103d04066005200d2a8115080b00742c03040030350080f444c1c1c1d13540039903914550404140280025440391604848a44520b41410110f020b8100041c0056000307500c01c0c0c0b010700000c1c1d008000c06030010f0003440611f0325070545107400c0024040300c0d000059400008174030ba289140c0c0003212201640ea003600c0343d1013070102d03840522080380d000b2204140d0503031221049400000c40c5a1211a6180c000350000c900c0401c19000714050740c0f0241d450f00c001a080641c107980c100d900980705805009a0700c0039600d51b501d84440c130f1010019500023300b1030304040001c0e4402c243d007081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 41880373 1250 41879123 41879141
    0x30c01091412150403080106080a02040503030a0804081e19020a08071b03060e030405130c020a0204020d2316081003081b0d030e0d0c05071e03050303011203030b04090308040213 78
    0x41d0f01061842c3c540f130700a114030800e00c100c002040707800001c03810301c20650081d41c1c2643c802400942c10050142800c42d1102c50280081e2741114080101002d01c42a0110000208210118007075031002d50324002c401c074442c442d401200715000b500e0140006200d100c200c844040d004a4501d02c0025001c0c81e64407440825070000b0701030352900007014100d0030040040c0044990441da501c2c0215652661441500c0da003c00d204016001000c0ca200103250981c0030340059035591070000b403c007064106484c4010341388260781d49640c0c0e0050400c011101e030001022041e52080c6040511801d04858031041140180030023421031001058000030f1b48860004680e00c00900011030704804100303400a030040c0300004000030540600c4c014a00d00d03d014400c0402025448402032924034905010403e55041100b600c4582c1d0014200000200e402000514040c1c0a4a102004c64045a141c060102c03800e0410700c0c0d001e242881e0724180800e030030290240d40190161082100b18900c24801401000812 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 41881623 1250 41880373 41880403
    0xa0c030209120a060b01050906070b070306170105010905070c0b0f040609150c08061906030911090115030e0a020a030201050711040c090f0803030610110703080d0902030c01091412 79
    0x440c0c001044001000d0150500556080107817481107001102d8920801280c84c0d0005001c0000c8030000e00c00800d4a64880710300d00c1d000403043d03141c0c64800c407600b080a031b49070480d80d101e0006000b8160ad920490390000500e040c60096005195a0030154244c020030318604054100c0000f002c0c0141071b08007100752548102d05000c1180c00c0b164000080c40400800400210168002299402e00c00e0502003079205050300410034a1070950110b0290100a90480c6d9004120300e0f00303400703a29450340083c085c110301d5010440d820764102004084a100b0120040d155221801ca00003585400344a142a2502864880e90340c54903400c10048000600026075089881e0400503074696500c4600c034070540d00140d00e84860b06656044a80d81d82c0819200c0c10741c04203035044c0d0501ca49005501c0c003121044044180d9030021340d40e48840c80345411580613000103e89616140d421840c1c18455005400801d007010408141002c0b0b0381a0720780f1710400c101d40a80c02c95905841400390030800c4140c101c280d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 41882873 1250 41881623 41881639
    0x801060b04060e090a061d07020d0215010504090f1b0501120b09070302031f0329061f0c0c08010203010f09050f1801020403150c02010605010903030503160509030a0f02030c0301090b0a0c030209 85
    0x147d4452020702104071101001070040c0c5456403510f03407011500700f10380c031400200b000c00c0e139082204110040100c0702d000c0f1140788402c1c1210000541342420018110259000c44022516260024001c0c0850302504a0950f01d0401600c4840d81c0e130b180313119040341c86803500503284e80d5620040010031989805800c0c121800640c004104030340f00b1404a1130645002e540c201a0034038050300000c0c0700f0f05503409540400b50409080c803400c2c000310300d0040e070911440c040d903082e000340c0c540c01e092a03080d4125054994000005104030150401d03840b004000c01e400820072454400840c0c0d112090244c001580105002c1c404501507400350141c1e80910340020342d0700000f40300e00035440000c0004604031400341d42001d40010300c82d809100e242c02102c0c3c054894a280d640c6142c0c3c1d5404040400071107201b0f1200610901c4880d071001c1054100719403060310b0915901041d80100352420a1030009075100740c0c1001e401c0d2000841000000d03400c400c0d003440200c3c2c0782e0380e503005c00d8000c0c0c00340c060955040444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 41884123 1250 41882873 41882909
    0x50f01060305192609091015260606041517060406030507060f021c02031c0e0a080903070506131505040b07030c032003040801060b04060e090a06 64
    0x19840002124890002c071a04121100804805015036420180004440d9146482460f40300740b50b000c41004ca54841c01d1509501500160200d5800d840701d01c1002c4012106100c00824000c42c2c4140c050350f8180b07100c2900e400134150450601c035480020f0040901000700340d807a10754001b5500940641da01002e918203004000828509201441130302a00301e0501241d168103107885418260b0350803401074003090f030400340d09403146500f6601031030440c4913a5034801c3c84258038440c0d01101569582c09199145a44e840c1c510300c50240080d007420030703450004070785050038000540802c4164403800c01c03511180c18200080c00d01d011343d8041500700b5070005000c1080c881c1c9000c204169824200441c004000005c4100e07040c0c001c03406214071000c41004210086030044480304c0e15140700313141050301c5480e07140c145103181c28014080f1559a001040c1408544400e0080780c002c3c1c01d855030140e00306480e004005000202c100d03c1c0b00c0c0110f0f00e410201d045240741e40c22142c00780514410000d0407080e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 41885373 1250 41884123 41884153
    0x90d021807050a020105180d0f05070209010b0408010e010606020d0c060e15090d030902090a05040204020705010c111e070512070e011508070503060d060b03030d0f020409060803070f1502040305 85
    0x4060040f0100551070040010003d9500284030003c03400c2841c01441c92001b481e405880340344d043e01c0e9003024454140100c0005a82d641c1945010b0252681c0306510707540351000141c00e550601d1844401030b41806002e000050740080e682507080d0503031a090301242d0080c00d10703138001c116400c1503042ca801000d4400c50410b004946090047d0004800c5905500240750100d048803080d030f1000b135004c070422003c2030342c1170350980000d508a4001030005140c107411303030f880710708560942c1c11900c0446c040b49a0a1103600b42404800c0390401160030141c1605030b40c400180d150150741c01114411000c540b13290214440c00c1010b14050094a0400030441d6100c030480480301402100702d500080c01040003c01c1d65201c1c4c2c003070340e01408016003035403025600c81d0381300409807442c001503a41610003031060440b0166140503441d840280030300010f0340c1c1c43c10203101c6015200941c00c0840260300803c14800056212a08101140d030041480040105000034510186c411640003900c1c5224040c850040c00d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 41886623 1250 41885373 41885377
    0x11b02040f2004031e02012c011101020405130c030e0a0302070911040501200f1b030d03050702030304030e0a180c08010e090309010e04020906030f040b07020a08090d02180705 77
    0x12119401860282e2966880341d0810f101d41d0000078010004203c003007074183c4c0c44980c078032400ca105040000c01c080402000182440d800880d070aa5074009086c0c64007296044881100c0085852009602e040d007020b000c11030b0b0844514030400425541c001d11040c45200782e02c03901d05884250141c030359210003810020f507111114060306d40c4951a0688545000300e82d80202c404403401a142c01100c660400000040751941c03481484190049480c22403980b03d007802803400c6c22580c0c0ca62036903590201750505281020491014080c50306d46002d11003025000030950754029450700d40203d9800d0b410000c1110b40030594420601c03c007500b512000780c0d0b15150040d9480b207800d075480c0e2603941c1ea5803011106510040e034031000341d50810814100b1075441107070140d1002c0d1303010380050315002012000c2030160703104640220074015240c0a1000304440f12500a0300160b0b10700c018003000061392100f00080c46001c0900c0d21941c9408410701c11500d51520b14501809080054a04e0b841c2c10b09000c0c2c0b40b5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 41887873 1250 41886623 41886641
    0x1003030315030f08090406090c0f0e06030f0c0f070c03140115053609010c020d0201020901080604051305010e010c0e0102070803040b090a1809020f06090f011b02040f 73
    0xc01d080c4880c04806140360112941100c1d041100b0b0300039441c2649503409070782c0c07101607502c1d00140c4a0790046844a00381c000e4021403450f55481c01c0709801d81d00340040065418510300307442500d041080c0070601c540019201c0d080301201701040e55940b1606010800361041c95002841e40040490000c01e2001c00c076010f241142a850081c00065403082c61191010124010942c1c40a40400c685540310b600d903204500c802d4003003084007281055200c850300c04003011030340300b04160b44032072a420859a041c040300c01e58400764002942005284070000c6c00a01e0002d052501441d6603800090404860000007080306400c00d008120401018150502030001c030454400480d4900750720b841c2c103500c00210038040350041c001650030141072298466845e80704030f070410fa20200030302c400305030304082a4074540e200d08030302400581031400d441030050340c000004005100712000d2000a51030b44800c11000307800d040918201403070b0000d009024060f0100344001941251034078070b06032580d080c980d00c50224 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 41889123 1250 41887873 41887877
    0x100f060e010b070c060305070c0b0c091002031309020d0b06131a0903030d0b0f0a120501050f04030c030c15060e0402040506030604080703032003041203060b16020d060212100303 78
    0x245070380754001d040c0380c2d1180f400000c001d044422810030603584a540547c1d0000d0413032034621201c5503136803035802c040042034030020388540c00081c000465151550301003102a00318005107091481c915440c0706408054820284a15000110300d1540300c1313154425110104001c00741d03610341010805454804000b1b0040f008400e403900f0210f6944504102603414140f0000c3c01103203010400c1074110064214218055001800496018202e03a03a07910504080c04405102c119801e2990900f9801d40c1d901804807030303114242c0c00511020961003014140502d4041c01c1070220342d01540350200e5529040d00c05050124900f082c0414840d065205541c01580212824007050310b880d41096182d200c25140100880c10800c00c0c00d001900940148a0700e00c1020105c140a240380c01400d07030164402c03036013200c0304103030250b0104002d9090300c1000d02070700350074074198100300076080300c00701c00c95001c00068403400d0020a00f03c108017070341d01100c08200b12650f4850071401c040c10060324003c0f9034001200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 41890373 1250 41889123 41889149
    0x20c040f0506030a0224071b0e0103110d0302070503031803060c03060603040f0c090504030f020114040203071e0f0806010302100e090703091406010f06090602160504020a02100f06 79
    0x404140c80c0a114040c01c2c009003d400650800c0d4200700303040090790620880d40e05640a0300400c4031004d8040c00b02c050061468808082241229580708541303900100c0342d05c05410018004500701028811842c0320564084400c0030640c24164500034050f03110304c0d0315200004610746805202c180c2003481c14010307012a8490f49400483c02083d002c2141d0f5290080014400074010900300046101540d000792800c0e25401d03200e4145000340e91040b40d00b83e0100e14140d025200301c1d64248220301d211b030382c45041c0c250503080c035500107178480724940f00c1c00e1401310505004100c080700c4683c80782c008104a0800507189640d8681d0703c1d883d503400b44010b074480c0c0b89414a5000c440c2c09120595202800107294148c550303074002c07082d0002d100c65003050320070a0590540c000d11030001c010380d82c0604060209400f40b00c0c945200200115480e03003007031003150016030300c00000c43d401c80500d8003600d100700e8002d40c495400000407464071b016054a0701b20141815402849042d04da070002c42503842c07a40c0c59803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 41891623 1250 41890373 41890391
    0x1091e05030909073513020105070609060522031409011404080a0303050c0a020a02150d18050c010c0201020a0204091b1701060f05030307030e0406090f0516090602120307021507020c04 81
    0x51800405102040c00c0c0e001000a04011b80b00078448122a105050a0b8105843c0c0c0e00c0b44404c481031000101c038480cce80c8038184403c6000c104010070070f00114980310000030038113580052002428001c10409510045064240da0380201895001903048003074468403185e0300e604055542d440b0340819000f00f40340c0400300d00114442021203c01c0b50030380e0010300134102aa400d1085030100b8100003503100405100f007890b150034900822004400300e0a0030344291100e0305000303080601510703803e418804485070540041c0d0b004920140c640b90100c0b00054900da40c0e04007614405040b03401d404a0789500d89001c209121409042c296201290008010540e141c00140c100300c8698080c13240d150b401801200c001900c201e416140c000006000450074070395070002d210941d2154002c080a20341c13140c0070070500c1c1105241b2009900c10300d15201100601c0c040300a0344484003000040800500000018003460007040351101c181c03120110b41410b46862b2000070f4a402186203910700c1941001e00034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 41892873 1250 41891623 41891687
    0xa0812070c0b040305070c0902030c130608010609050d02040f05090307030201061a070b0a0b130903030b0a050604030f03020a0b040308011409090c01030207030905030d0504050a0801091e0503090907 87
    0x6082030340441c0600d15030f100d076101610103803c0118112402d510401003c214030469001441c025030751543c0498680c030b4003035148900c0100b2a0081001c1002e020010002107500c482180f0480345d081d01e0003006096540045005001c6803601c06200ba8104803d1084200e400002401014001e038000c00000382c60710510302440c0650012116441e000307019800c040340110071400e0708203c107000c0c0002c925103140701080040c1b9541d0143c81089554448940038503406025101c1030040444118004d01c1c18100080d00ca402030380005051040d9010301441094000c00951920640015014030a46440e190080000c6024065070510400c2d0401d0b0540340d042401c0c490b40654a000301038840c50901100440003504280010750402c0b0b50080c00240680342403021030400c1c906561250780e20390820301801072103600d80d40031942c3c41e8900130f650030216629040303250060749010081c950550060a1141c594010342002681c0001204188000c2e150032000f075106071587c0007000040c2011407429 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 41894123 1250 41892873 41892887
    0x803180a11040c020a020306040b09070509010f0b09010212030405011e0504120f0e040614010201061706010e0a0b181803070302060105060307032304020f0a03020102030a120e0a081207 81
    0xa11214010300700a40a02d45070700710440d54000c51048030224401c980000c0d203400c105507410342d01d10311800141b003011a81804208046c100c19203050040b54581808454416618420098042404542035880341c1c420300040059100b40c2e0b88680e2241440c1c14203500801030700e0b144441a54400b001c10710502d400f801064400c540003002c40c00740d0106590709603015404030b200c0108100350180558800d607100d109200c09080c00c5030f000410520204000381c00c44055800441408100c0c401401640d88001496070544004440c440b44a0b142e5000650245c10002d00450380203520900b5101a00c5414202501c65100d0101103170300b01103030503002038680c0715114000d401070b08010f006000300d0402000454020b0b105290008030130039071451480160744285001e80c1204c1110007400150300d0040c07d1030244900458000048a19550010750b880c814040c640c070034807c9031241054419240c0d0301041c850303044142591400c8559140140c2580d202512245035042d845000c501e41e2031040b01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 41895373 1250 41894123 41894143
    0xc050a03060b040507091805090106050d03020f0d02191e080a0c0c0b0301050a03020409110a06091e06080a05070908100c170c0901081f0605030601030e210901050705010207080318 79
    0x5914a481c0d039240200030090000241409d52130340d00c0d000c0014158846070314400103140281c0c050081e0441c0e03001a1800d01e03082004180440d8014038034011021030250444845d550320442c81e008201d0804260340004200080190012030003260b0805030580114145d0300003489608000001a01d0350443d40c0c207404280650303500b0001400b418030050802d6801015540d003d19001c0072008140400a905180103030004000210100003c22a200c20700d8051008003c410144000c802e042c548010500d0038000c0a04820540f55404507200c540108140c4025018407804c0da42c08182c0c504e008800350a5150040000804052414500114000d0800d000782008070b0202d1510540c4801110305620141007410a820751400d09002070181c401075200400807500c419459160010000d022201c08003540301c6a40c1115000c43c1ca0091988079180d52030040d071030001d4440240c40b004950a001e01c0030020702c1d03984001190814004041d02840c458051800c06001002c1e401ca18180c071010250 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 41896623 1250 41895373 41895389
    0x509070f080f04030509010c020a0b0403050a02010807021209040b06070203011b0905180103020420030a0902090a1b050f0c060a09020f03191509080a0c0309060311160c050a03060b04050709 83
    0x20143c101b2640c4112507507039055000070300040c096500d44204600c582d101d80d0044a90380d100f82204001c55801920701e56100005001410790701d0307004410145e80740700c1c43c418a4480c070b03510700c0207225940e01c0100307403005550060001c03c41c50032000140b0b1300c2d003200414041d010806031840080c41d4501000c0d0204a84d2003828480c2103179103503509100c041c24034034000d00d001c500b0030440d141484410790082e51050079550030100d051503540c014000001009008a40803604020100b0300310f90320b1001c0b0401ea078030f640c42c000d035407603440704c0d95842e060050880c0070311280500c0062081c0c20034160011440c26008807030003219404040c08241d82d031480d00c6202503040c0340d510302c4140400c09008191303010400c0580081035004503503442c541a0b40c4443d4204021943c00051401030540c440e40301000340050742010083c94281000b03003205401010b85140300116104188410082d011a529006200140c0180d0610b03844c0c0c5014030151062103c840e009610701800a40c100d4802d0101408940002c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 41897873 1250 41896623 41896627
    0xf0f03070b03180a0803010302090a0b09070e030f030a0201060305120705100b04020708070506071103030106090506030a150e07031109061611150d060803030403051b070509070f080f040305 83
    0x10800070000c1d0002004034070b40000806250080c80c0c003d00114030b9481c07062040c0c668a604501c104a50030001400c5016840c0c40d15603450a11780343c2640c5181c028240c1e043c05200082c84000192408251500090312800041484809613030150007000581e0b10030426945c0d0b58202000c425940c0c000c26101034001e502460f600f40040c0030a80c400d41060f803001c0d1002d4640003080c2c60301641544603001c210740d1a40000200080154001004e2908100a0028610319403504500a04030b010342c1c00747e184209800030214004401d69070002c3d102c003884044440139580e4910320001e184c04100d0782d10000ca8244011030340603c04140442e4007003000100610f0401c00b0003a441e400444d000c0d003044891008a2195501644c1c0d0001481c0c980e40550860956a0100b0002e020031390b07a00d60302c0480c140e4000d1042c03000003038001d4190340c0b440110a114010b4800f0541c401803a25000ea800039400c60405801d0040055004501c00b107000200d8460880b182c0b01c37407207078520241044034003800084007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 41899123 1250 41897873 41897879
    0x4021306080414070f090c090602030a2a080306100801060801030b04060914010506010201110405090109020715060b0d0b030604050c04050705091207050102010c0c0c0506090414150f0f0307 83
    0xd4050140c0140c002c1d9800501900d5141c66149005145e030000482d03410f21140800113042a4000d00d40e0200d164540044140c4c500785000e5905c0c0110904041408460403151544a240300180124154020980c0001c112681040030b11a441660020700580702842100001800f58403403504031160b50f03480300c40c02c0c1c2c03840d19910240321002d801102c10a480700c0f00c810104400c020071816031010280002590f00b0003400280c210350358128065070480781488100003540d503a800f10750468140310b60142c1c0d6141a440c000c84c65141a0394900078040ca012404a4508000d0000c3e03d0952050300007009550601005c1581e03a000842e0b0041c03640d400000808a2414650003040e0400a141400e83c10100c00f000014502c1408411000320707031740040001c01c869039090090110581282c1031001d4821111340390403409400302d01605016000001c1d41c0510764a807a44400002c51082c1000800b1b1306000759000100324403048600d2098150301412282407a01e611841605c140080007061085e103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 41900373 1250 41899123 41899127
    0xa0905090405030d1107020306040c060905150915090306090604022418010915170f13170702150714030c0c09041407060504090e0102090105040303050c0a021c0302060604021306 78
    0x9151710507185905119403801a1401c001c03403402035201c1c00d009a0400c1c10800010a15100c5500580c030440d06038044018040449048841003903007500c100580e600c00b160034040501c110064607801d40314103010007020800104406002c0c034802c80b80403a412102943e480604003902c1000c2d050060100040021945844102c1140143c1030514035000c0707694201d032010f040044c400c0c0c94040307850f0002520400303e04031100d9905c058040c6d4800000e04094410801d401e841400041180d10300c0c0450002c6410140c0c15070b002c4982c018010480310580d08845001e50700a40000c507007071009045581c1c60150701000f0303a004000c40c4001003481c01c0d00340d0100b102c811005003099407801d41e50404448104000d0010074050210741e01c40f2550303949000311000881e0300b40c2403040300f41d0348140600c28450307a104003114126601803030015150800520400c2c101640300c48000e50180851002c5101d8807121441020200d010741c080c1e401a55076401448168462130151b09042c0d002c0950a2240368 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 41901623 1250 41900373 41900381
    0xc06120b060a09060e0d051c0507050105010b041511250506040b120a0608070510030e01050721050c03040f031b050a020a060c020a0b09190b0a0905090405030d 70
    0x1414010000c00d00151080100740154405040100040c501d4803091000039049184000c01440a4890351130190890302c5541c1c540340c03084101003000c0c00ca092072180301d038460420b4810884d0040c000b00034559403031b080811561701a200e060302243d02d080041034007a004d440d590b9a120403010142880b403440300104e03120152130f04401a401600c842020a0a854810150000d01a20b2038800e41c0c9003c0e01e101c14040382001400d07287c0550800300240f0a280003c140001250301c00c2d41e0b005400110380b9016170240400303a0420915602c0c1500700000d040d8055001c0c800820401015401d104c40030850006840085501e134000550030004600040e03414507448258a01900c0c00416900080b81803c0d136a245001e0f0a031381c01d83c800e104001c1949800307070401006011302d041c19a9000081e9000c0765290049108880038880d010643d03002035151020350003820f0151810302c091046e1250f02640e850741040c80c613040052800c8a02040f01e0904d07403017050207a5000b030015401c11200320140c1005e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 41902873 1250 41901623 41901647
    0x90c02010603050303090c120303070507020d030c0204090c03020405010906060230030c0403051902011224030c1a07150f11070f05010c031e090c05030703030203030a050c070c06 78
    0x40d9a10340001002c00c001344041c501616401c400b51408100304004c0012009504141005075041001441300702600310040f29911f56061f04c042c61190b0283c1002c0d2182c9205140180d0803904003071400c030400600b55100010b1b00d100304c604110f16625102104100c41190044201603070003000e40c049034102c1c2e0400004004a00030000408908210541c94140c0041e20f46502c02c0c0710204040c0308000c0144400c018078032042a04c04840d05503600000c18810f81c906413240d60315520070030041300755050050400e0598094032650650f6a0301d00d00400c2c0041a881202c0528001850451341d07007125a049039541500444800c01700b00c408108000100855501240d000e642c5481554408042d400540800e40c0106481099000c5030f0600b5420354800e6286081011f04e0000090790405401000c00d10000f43c040380041c000d4850320381a04d40e444036402c200e515102303107480041010740c008002d41c82807049500510060b25504058041406402c60050114140a40600401c1d1148510440c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 41904123 1250 41902873 41902877
    0x90e04060e1507030b060304020a06050304060b0306010b0d05060915060c070519060305072a0302030708121f050a061101021603080604140c090103090201050705030c010614010810090c 81
    0x11000c01d41540a1030300040d22000c02c1c400702c42a0800040760303058460b00ca203610007541d68074910300c0e007030340012030507034141c02401c09000300403001c01c0500609502036000b20f80007a0440f400c40d43c65802802194100440c861080f03801e05002414a00b80140c00601031000b188005821030707408010000b090b003200c03051401500c44d100000946507101c4468004641005085401d000d0a100b00201920002803c82040c0400000b0103914400c90013090703001407034030f0502441040001d00d8200c0c01d5100380d080c00f40c8a0700f030220b0702140c0040c002014a008000003182d5400788400401d028044484a11070b4650007492003408201c428062005825128030b140001803614a8000020018284011003a40060390440411a031402c10780300d9807000b848800c0980281d480d0101c00440355114004807241055207840320501103901440c00d695a0503806000d4036101c5d519009103500038036262069040f0200c10003c0300760907501a031604c900842101a8480c016810701f00410050f0500b041d00b02e003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 41905373 1250 41904123 41904131
    0x70603050c27090c0c07031103070e040b06120a0b06090709080a1202070602011812090b0423040209010203070b06031006060306180c0c1203090204061401080702010c090e0406 77
    0x52603410036000c2c0074016008140d5001c42d51401c0c050100e040c40080c00c90b52115402c00015405981c00224081102d41c81034602c44580041c1c40400d04000580d8030076248003c440c8180020000d10b204028441d100c282d4410601c043e004440d40c1d594480100080c00391030109011420743d042001c103103940700301d250038100d0a00c0d564400640c58481e0300301041e100c0140071406000b03095414400400207010500c001c4c085104d84058045460000300d00040c080d2155220b100200c90280ca420b10040280f80c48450301c540e80d5103440c11900c0c90b0120303180b1010100054843c030601c0d05109036000004123900960411501d540c801c41001c1c0c0c040e2090b5414801e2807809400038800f17002d040082c102035a0302055043ca400030fa2110150060301c141821801c10a841040d02d500154114100340c001c07850a08c841070500c4250002c4c480c110010350014180344002c15803c94100417140c10580c2a80e03034040d1580c500d41c0032400c03500c04103000d00025065020401220711106501500140921800a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 41906479 1106 41905373 41905387
    0x6140a1a040506220e03070c090608012003090709020f0a0216060f050a0908010606030b030606010801030203060705070201120507030506011404140111010b03070605090a05030f070603050c 83
    0x10b80f040c401c9100e141302c001c0c041e42028920701c5001003600d81c1e914150500042c00920380c0104464181041c1c0c0003d80702105114030f030108002044040d0740700d003007003400311166800175001c0003e510601c840440c43d41c04a1000304100e0301400300c20742e42c580880341d029080c82030400c0c207441585200d07074040113001d41001c42e000c002c0e829450100d0341c40c040d44409848042c141e400480d41c07903207065000f15031641c1544c4042106d4104a045a4040e650750700111070240c0240030017900341d04414040343e40107014101401c2010320506040c014601c82584940807100c08840c4030000a84030b006012155802c0802181107091b0011480e04d4141480c5004840070450320300703203040103044000d2942e118000c4d8441c8048103801400d4600165a90394014076540100c01075610401d080d03503002419103800507072040c010011310058001586017036800d070010100100604c0303c80404000c02 = true := by decide +kernel

theorem cover : BRFrame.Cov 41726623 41906479 := by
  have h0 := BRFrame.cov_init 41726623
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41726623 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 41726623 ≤ n) (h2 : n < 41906479) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
