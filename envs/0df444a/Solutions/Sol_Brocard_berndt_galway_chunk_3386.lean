-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3386
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:30:44.600095+00:00
-- url     : https://prove2.me/submissions/f73b78f3-8e29-4ced-9d1b-1b524c6f5293

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 608812949 ≤ n < 608992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 608814199 1250 608812949 608813011
    0x203010f14120a06020301210b040822060c06061401020c120106031a15010f0203030103020907140c0c090c13030b0c1e0903011b08060f03101a1002010203070503040605 74
    0x6138a07a41c000014008100900c1b440300c550002e0705600d0805080b40d5840701ea00e03940c00b070409080c0c9a404a41141500381460b03e203a90548854000c400c015600c0101520784154988105c0780c40d030500d0408620001d400d0b022020481d4160f000f00f0070001040140040c050354004902440e54841c0d0021001c682084059000c021450310342c05e60310718107090f116040c0310b04130f06018100300302c000c940c440b20f9074000305172410f49030100d81300340107038603405410f0707480030710500c1921003081c00410100c02ca100081010110b02000ba152500c6981e101880c0c2ea096115031400c0c828000400c40c420700105003c011420341c00088070341c01c9071400305a5456000024140410001184800140443d2500b004c4c000e014000c580010010a031910740b460203059460000c2030301d40180d0082c20400401e81c0e003041211141c1c5400001002030400041c1001c603200243c181d85070064210892034001c0d1031051084910800180d0785140c119115655003201620001c0c000d0005c0320b40700100c80d00c1224442c0214 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 608815449 1250 608814199 608814203
    0xd030e040204030f1b0509010b0c070e090f12031003080f04050301140106021b0f01030e1005090705031903080c03150306010b07060509062401110a0f05060a0203010f14120a 76
    0xc250306049180064040d0044a010300d082010030804110716140e200040c0c0c192227881a03195110603000c40c03540d2401307000b07501075192030490780c1c14802144400b148854500b1100015158088144a848111031005941035020b00d00b041d1000c0022904000180c48000e414905091070103030f440c0002070a55416514604822190174010040581c0410100180c03080c20b00c5908403006000c00080c102d03082c800d10041c103268070380c40f5050070040c05221a010340d085e030520800250800e04c9180f960381415002d0349000b0b00c10001c80480c145a403412a10b0700b198150380780d00d119600c0d610004460740002e040e112150303144484880d200d40e0140202e6010b042c0312140f450312109103007014401c1c0ca13030240c40445241c11400070700094007100e200c401c00510994084119030300f0302d1001250b00203241d03d030000c078074000e2601440030003404040b230701c0311207004204a40c1e254551004410403807100b845404103070b1110300420850480c0141280001402c01091841c03070700540703084581060800402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 608816699 1250 608815449 608815463
    0x3090105091c05071e150e0f0c03030a200601030506060405280b0105070209090307030f0f091202060d0c0c120c030206060409020406030f050a0b01050904020603060d030e04020403 79
    0xc01079150410000c01d440100040c03091001c01110307460140c2280308001014001c00c41c01c041041c41c03060400e100340711840d4054000d0014494411080e4001c1c41d8021098550340a070002c11003140c80005030041048600801a502d403115a039400e603810310172002d04a92156042c00d0b040400300c0d00340480d900a6010318090040e5213441000c02080f40d4004100c0480c0c0d0526400c080c07d0b00e60101c004009034044984002246402c07000141c1d040d0240d800000d6100c080b103001c0200104001c4064143c0901c00d48415130000702e114410b42c2ca802030301706d00100095940b10104041c01080006004060015140c60b103132015880311441a19550452070700445d04014802d4108490010001c0d4100390600d881003e211095600944030740028041b14491619a1424800d5544070b50002c1d00540d4840700b0681c9800781c81c41e082e502e0300b80240040e520340a07040000035a0303040158607640710391b0303001f0f0180e440e44c0d03222801c0016010042c0c04c00c0c3c7c03c105581451142d6521184000c0000e5070254034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 608817949 1250 608816699 608816701
    0x1a012019051b01050a08070807021c02030405130b06160609081209160b040e0c04080f15060f010e040c0c02040507111002040806160e0a030305042405030c091503090105 74
    0x48100b2603203200660340c1048420402848800da111480303d0704800d082c90a0303c2540c0b80d0450407854042488108801e80707401c4040c0081c096000001801181c400b40c130401050034810340018201c1d0071045805410480402c1510384400c54500740380a500d114140020b4034403103d848440003500080e0002441c040c16600340b00c0d04000c104045a820840c00308218009030801c0241d0a10340500c0c840c180301510501c021031074200c40710f802c0d170f00038082d0181194400d48a0390691940e480b0750000d2480600c06050206056060030849100325803810784410310018000410301c4010011903400c40100300f0400d08450040c2c3e614010303a409002290356141d0032406406501303041402c00f068680d4007030710412040150f07000c00b05501e50300004500400000c0c011008051318880c81c8a0764103544042000c20110403d5000b0018005a8546c1c9a2000716243c071050408001007404032014045030b400e000060400001000600c030b01c1d01c01801c407000441c000306101602d41c01c16102c296999440f54 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 608819199 1250 608817949 608817973
    0x5040510021230060a05040c021e0c1e0306040b060607021e030f01050907140d0602030a020d0b0301020c0a11060f07150b18072d090303031a01201905 66
    0x84402159000c10200415882c1000030000d48190803a109050042380c6552020544900900c070b000000301d0a144100e0b929844041c0c070781d03140d015045600f4442c25803092a82e88200303200c0ba0303082d0000000b038010413242e100c0c0c1c1c8640c08200c0c0c000340b1581d0700a1003000002c0068076101030a0a00003166000810340b1351502c000c260501061280a9141e689010100582d4060009050003100c90590549c07000c0f204070030205a03c25030b889800780c40180000188000024190b0080c01d07001140c840030054055540101400e13480f60b8849144c45501c28030282001c207021002c03006400000502c500d14106100c0d146813815041000241d818944c86984004251a0750152136254182100c40b0740a007540d03c5010503c840d8041c000c1008c108500d000042032002200b041007a020000300e1203000111100f40c004c0140b08140170480001e41000c00c501c18814041102d0826a6416152281c50328441c91010820070b01301050101107119481a10702c0031402c0315a03c100d618001c4003d4910446aa = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 608820449 1250 608819199 608819257
    0x5060703181d0f0a0902030a11010807031e050709081f0e06040308010909050a300302161b050d200105040b07140a05070b180907050405100212 63
    0x640d2000440c91642c031006004482c00d010050791040d1002d43c6800c840c0c036900b45040013400c0c0344100075003500c2140700200910564030101d0302c0340c40c0300344ea403001d0300d61b070f000400c034150f031a003810401d244400656016512030040d0040c0764420054070700045290b640d00151071500c44460100c05094822004400c15015140900751403140404003e010606007681c0c0101035250512540c11a00d40e600351100030441e050221041c0c050704901d2051044010218614000c006540d08600800f000000c2c42c150034002d0095400c483c60080b010211942d0036100e4001151040f14030180201c2048000f04907a518030020005060080c0403142810074030083c4061840d00030031203d4180b041c1480f0401520403d02c0c100c9041d2030b44092541c070941d580d100301c10b1074480a104010b0140c0a405c0000c03d43c5884c0c071020302156010b1181c1e650305824403005000c10f04c03c00f41e444000241c401c02051181d03041400c1c401d11000f0071841182e450b10481102c5082c0c58101102e010128203c941d4019010b448c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 608821699 1250 608820449 608820497
    0xb0c0c06060d030806060d0e0a080d050907060207121b061e050304020919150b030702190b0f0c040b0f040e0f2404021e310905060a05060703 62
    0x603128004510080c1d100134000000040c549441240005113000a604144c2c000c6031039000c8040882c0c0c0c18803c6494070012940044207d03044441c0b50030001810460300203070090455150360050421982000b66101c03c45c032601c48240c0c0c06140e040f141c14008402c550036040200300c02d60780c4003130615803602c07071061912071040d40504000b0240f0901000da940c11500503000111141d0a0514800b170a55040103004200107512042d0006000059112400f10065129440c5642a01c0070300c51b10000d01500d0041c005070103041c841003040090f410310f1802d4140d941020000560761304081d07503504281c01c0c82e440740390300c0c01004801007410452a5001e0340303032742d41024400a00e200a4139109152201003034031081030008841094000303100540f11a8111842c88220341010410300d41c2070f0031002200ea000d180100d02a005244a40241c0c56483c0c13020380d0010107100030040800e281c00b8811014044c080d002c180d01c0340380c1e070100190365900c1c03800a00342c0304e03c81d480d03070313030414009501d583d1000e92 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 608822949 1250 608821699 608821711
    0xf02160f0f05010f05030f0a1806090303060f0b040302060702040b090c0702090c040627052106060d0827060a12050f15011103040b030c0d0e15070c03020a0b0c0c06 72
    0x1c8002403900b943d0040300b03890340700c90101f01c200c00c0707640c136a400480601418611904c10641e02c03041e0605000d255000580780318040c0e00c083c0005039881e155416000d46a01c2520308043d01808180300514280c2c0041a08900041000c01c0c010008400554400c03800d85500c1000d040c001559030441c20290780780b581c0501201c25084c00c262078070401804121883c000b0085890000d0b1180700041c0100100b0306c0070b000041c1100d071208100700b040e0645030604005541c1c0a11030030000400905d485a0b40380c001a6002040d94200500c2e82090b000e044008040c0c08007414103c5007100c170316186c40b0054299081644e42d012044000c0501c00b404548c4084c00081000044000300070001908200b400d038910001e19215000781031481780203095006d1500281082c1074000148546640ba0784003600200903100020841c46010024443e03a46201014032441d004100c0006110640281c0f10151500d02038015650812002c1d910030a094008544503a11040c001c6080a0029420002903900c00303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 608824199 1250 608822949 608822957
    0x313080c060a180b0c03090f071e0801060605040509040507030206030a02120f090705220903020a03020d020705130c0509040c12060503070b072607060f14040b06010f02160f0f0501 79
    0x201e0b164640a0221380f00a005100c0900700101040078540c08001159034010000107444086455003401c1101013140c41d50b02e04180441310022980c82c10611601c81203400b43e413030342494185004184407090703200a009407a240602c0c0c10000158030354400440c4104511000140d0f5201a050071011310703803003d032201d04c00c00307074000403c111110000382d0541560b004a5510915215042d00040394200d000280040325090401f0002056000120006803038829001c4d55440354000301c04907900d1510740b03c2d0550064540000c01400c0d00582c0c00a0500c4010b40f4042d4604062100410b080d5144480d170400000d0600e4050200e000b4580b0134500074003021000b03800410720703001c000820f034001c3c00d8001c0c0c0701c0c018000c10490303030954a110040740c40400056598566600b401c0c00c200030311080c617000503007500380905000c01140e02c0c0b0343c0e036105035031000400c440341d110400111a01000550302509502c940c4d118104801c0545448400500d121201c44605c6070078809400c2100c2c090741d100758140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 608825449 1250 608824199 608824241
    0x270c0108061503090c150c0c040b031011040801051f05060f07080a090305010c030e100b01110607050c0615011d061c0204080f030702010903110114071109011703040302060313080c060a 81
    0x14001054a294108c0304950200c2c5094060f0f0000b810007400c0304c01c0620107894980c500350b2944500d400341c01103400400c001c1295030f071036942c0040c41c00069500c40410303401004090100b480d08801412020011440541c03d00700c80760b0342c9900ca0b910880040e00410240482041004024014540340d0181c516040c40740d03c811848160343c4001e141051000203440d07524908080c0d104982550b10740602c13101b00c4d01181424a00900b05074802d480300340003405084005900d40c84412a09400120103944504d03000f003500f01906180b0305100341c140c1d0300840400031400c600c100842c801c2c01c040c2e443c031030041e60396190040c0c1d54a0000380d8021808181c02c02e00c130080150703070045050801c07640c00c40356490000040b900100e40010000e0348005540d070b80843c0110a2000e0300da580400b204042d0340c0340c0203690700da00900f80300d81c03c04110076906510800062005041c840090b5400c00c212100c0d03071140c040d0035551000660480304195403150310401c104110955503011725600764aa1000745106 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 608826699 1250 608825449 608825467
    0x12414120a0e0d2c0a0e090f1c03050a0b03011506030f0506060708030a0e0303070f1826030702030708010b1302030c04090e0a050a0605270c0108061503090c15 70
    0x12154602e424606000c0039401e114a120101e00d00a500a0358000c05505e00b003a291030002c090b00341c040d250041a481005841d00004400107200344040b800d0741f800100040e440741c03080300904001098400b580e515613403034560680f402d014003400e203110740800317150306400c014006040307622080c0702000550524090040548600c4101d4a4503900070019640d00e80d43d940da90005410080652a5035100000030405041e038083d0a9a14807003103507880d15580820b0609010700b501c035500034024201c902e010007103000711980003078030504c031007010642381016903c1c0c0000342003c0895216880d265107606e0a51a80e1400800031000c5101f100021411810540180c100500403402040f03011680c1e8030440310300000401145100b983e11008482029081c1d2810f00050a03007039441d04c000203464489505078581400d5900100705201008194210025004485004c0041d12440d0010070b0072400d0806d6243e9000118420183c400c000c16810b80d001d001c1c8402100e01d00e400700c2c0360305424050104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 608827949 1250 608826699 608826707
    0x1020d090e130c1a0304110405061e1207080d08070804030207030b13060218130b0310090f050a0c060e01090b1c0b03030406080402100305012414120a0e0d 68
    0x24016604042c80b42e00c80c6041e14000b8079220803a08501510181d003030507811000f034500c0c000e5214510031500f06014140c541c0601043d602c080d552580c5c800180d0310400c12504131f603030014040b40c0c00184a041840c016520442c2040000d8000d16416005901c801c202e07242c1081c00507410544500d0a14018035194400944405140c0401040d08012501140c0d0740c4030070760403818103150000001c56841004110440318001104203e90054141441c0044c010015220700d004925003d0003424005070900b030154024a04818110351b065030f2815944d0100d41c00704900509a4840e18a070080d90f41086809003003a5091040941041010502488011151001d852011a040c6400780d01c2c8021000c604015090700d018054041c800882d000130382c10392000000f030046000b9901105100d5040c50102e00b5610240901c103189560001994070340300070b07034810009040d914507211550700704000e0422003aa00500501d0074603401c04003801356440f49881254201d02c080320040001e400e000c2c401034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 608829199 1250 608827949 608827951
    0xe070501110a081305100e0a0e01050d06090510050403081f060c110f030f01020d0b0d05030a0f0c060f0b010f08070e0d11060d0c09080307081b03070f0b0601020d090e 73
    0xf03262040c00308055038001422030400000d44801400d80001d000386800c01480c03400320300c1142d880303846213600001e40c024100340802d041c1c4001511608000a036501c0d000060213030850112850700c1071003d90b40d566a018401d45005512940d220700003420281d4000030b01d600754600582040b55006420407045401800d4134900f075921040d000c0f400b1210070000388100e40341d0328000b41c040c0190440140c0400043d80180115441075004001c1c0100c2e00d0288450986c00c100300401c0e0340d004000300e6413443e0090607400007a003141d02d4401802c0440b075607036405403114102c06102d40780d125850742d0960b60304003c542d0001145481d0a40003440d003050010170b980c070310034582401000340d95140d00601c202180c41200098015180320b686040781d4240c40d00500c0c0d0070b2040400075140560224514401104481908c0e0700111500c1c10411840144105540b40201004151100300034030070000d074951291282050141618559a2504400181c20032006030b110703008006641c54140b0450740f00911032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 608830449 1250 608829199 608829203
    0x603070e1509131b090c090f06050c121216170f09030d112d0307080709030b10030302121e0906040b040806100b1812070f03060e070501110a 62
    0x1921141d201c03c101c01c0c07050645280090540c03000029040300da100420401012034002c80010801c40303504103800c6400046030700501030502c88010007005000c0c8200d000c1c1030082d20b214244c0d250f03000084410340c0319600209260b90620740e41d80411000c2009041c2d0182c503480c840c1001c0d12220010001103102000c01071580682400041c00b103a120541041615601c44032141c00b00b10a0410b40003000c401e4005034034000080c0964181d00d000084810809045880d4041c142c0c2e0550310f4000003680d20b184002c2035201004500c03580040442c00d19050341d0b024225022010b900f840c210300340241003031600c1c2c0c011294860100521200e4115000180c001c0b01610304015132180c54443c0041c00314480c980c0315000405020401141005004c0740090041010b030708289040303551140c1c1c40f055030064060401810487c5125909a03040466801001b00c2000f4141c40c0030985800813140882c015801c1030b1a259500e0542c20840c0740200a0b80c0081c1000b402c203e00640b420740da20301c0cad654048842c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 608831699 1250 608830449 608830459
    0x140d060512012414130f0c1e140409050901110f030f07090b0f0d150314070801060308120402030c040609090b0105040501030b0c0a031b0e011727071d0603070e15 71
    0x240302c40051700e54007010461039200310900c08060714050040248242d04400c99020707011011045981340200907000001100101440c18a490100094010000188522155501da01c0800c00e1240040000d18400181001d0113443c0e0411880045043e6401070800051017541d000c148452602d00b000e9800380103000c5c0c90035aa81503c0c000030005400300310000d640703559031043c021041050f0810403c0701c1c0b44003881150155a40c40100500f07807100c0f0f00c006422448100007a0322410b82107404690f0150003d4111954a451a40800d00310344003a0700282e2001e55400d008000c01c0050300c0200c1c014203044406100c2035045803640003060703001520309001e0900019100201500070b400207419010700b00500310a84904980250458200e032f40164000345103515400400d420400b001c5016424051182c1d6080c1403048200d115603851005509103480744000c0001d0000d101c04200d03040d0074034504044105d041403001e0610307000864000203020b641c0e003001c02030320b0391207403000c14a50542124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 608832949 1250 608831699 608831719
    0x3061712190e0d0b041e030c02040c050c0a0605070e01260712050c0a110a2001270311010f0e0108060a0918020102100c140d060512012414 61
    0x40e02c4011854038010380040c2070003010014803281d5000c030b91050780a40383d60361243c2021041092074442e6220000c1c00b203a107440e8804007604041d441030819840e54200310740792214a41c402850300514a5085030a1900c0701c04001d40243e024140d03a03161142030812170820307050210b134662046507580501c6090540440022400341c49800302d40400c152000080050342081111402503521008408001c569618038942d100880000d180641c5900690340f40d9000410b400c0810040929545040c1000f08006a4010b03583c07019203040c01c0408515080910030b03103146000c0016030a1051100c2c10b005980100c1c01869030000300b0300e201507000b441d00b8415550742400080030f040b181e4102a001030716083c030740a03244401080d141c4006000b602150902e1652459104c123548140d9030702000101e4040506050301a40340281c490141e4800002c1000390302c0e0b90100740441d84038803005213285e450f200f40d148500210348400300500e01c100d2814124034280f2201d1200800309252490182204c15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 608834199 1250 608832949 608832997
    0x21030f030a060302060705060103050d11030a0804020301020f1303021201021c3204031e020a23010e070e0a1a120c0312041403010c080c0c0a050d03061712 68
    0x540b040003d141e00800c80c07a1104441c0c101107a69220902040302d2500c1031500044007180150f083c211040c40341001549000d140c1e100031104800d004d80205d80543d005d110201d401a096005846038800e80c19200f5072461540c01000031040c4d1103284603241d41d1040042602071078072203000060322401d100d030124a00c1d200d44200040034040160f001a404034141010161100d2200d643c0c1c041c3d80030b5905e44a05900741440900401d00341c1c0b83d0003000d82e10401c150030000c0c844850400d0008400004a100c00e01e849030000e00b5200041c40811460f04584005d0080c42e400c0300302c0d41c4c2c12140303c0c0800c01c040c1c6d9100031802c00000550f48010b02c60101381c890311002880812285400080203025640034030903690036101c040c0c000d40140d840015980d845101142414031458800784000d40d140921500c03400e104481700d070301411100c050340c000d8952a201240080107201030542c195600000da032441c1452100d14100c13581c3c030305902c0344c00025240c40e81c2c0c1808000c2c0c820380001c411021000102c56 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 608835449 1250 608834199 608834201
    0xc04020702060304200405010e0708100e2d010306090210030e070e131a060a050906090703090f0b040302281a1017030d0b0108010f030b07051b06040221030f030a 71
    0x2400b105c1e40c07041c24507001113548024401098040c1d4240d8541d103c0c951501d022100c0f003042c0030300807210540000000514856459a07010038103540c19000000c1c0140c1d2403400072040e45098209845a90310303440050110704140c1d80d4148209046d00d01000101054040b2545815051003807040700150f0b08085540c006030385001817512079100e410b002d911940c4041070780a00c50301b110f19611031030070020000303854100b4040b401d02c206d1000b17003500c2c126540ea82081e0002c0842c014151a2030070700b21a0400041c0711400d0081c0036038000e8008081c403900299003401014080804107402c44a2a5840743c0001c0801c121300c0b04072108417112014070340d60b10343c00b020103050130350101c0c42844909500c40c403c05808001400031200030002480085400801503030908406e1043c0300c401c420100041000c581d071050241c2d080082440e0103490100042802500c11075080c01c42001e5400000c01c1c40f007140703025101140700740d40040840e00300c44150954140c5900030400420044000003002440441032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 608836699 1250 608835449 608835503
    0x20901030e0a0c080c0414060d140a2418021323091e071710050103030305181b060d0605060f0703110712020409020d061107050c04020702060304 64
    0x1d08202c81d070700071160801d0100350030b0621a446042c002c6401442c3c150919026075a403400d22101a2201911a0400d005007890804019205941c13100b4050010880a2100e103003882e000f0984501440501c2c0c100005a100a03403250034414544402015805518030a501400d40c04032114103490248509a401400242091050340191140ba20b45041e441c41110740c0681f0800003280d115060107541070603070f041c0340315003990b45500c9907608002c148043d0340c2030100204402c007505c542000800c480b0342660402c1e00100d01007500d03002080703040ca0441e10301d00c0c200d9a46c14020400c00d0721010b00809a680e200d988035000c2d03200021146010f04a64001c00b00030480504a10384c0c9210140803a0f00c941c212100440015880801e54034080400250305410b54140c6182c1405245d4a582000020b107042d000485c1c01020511314100480e03143d03c18041d01c5c00440d80703d180c2c0c4464514203141006c4100b994548103034410311000c070143c2c44481c1038942c82075010080780040120515890a8510 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 608837949 1250 608836699 608836721
    0x90c0f060d0902090c0c0c060c060f04050f1608010c090e06040905011d030a1209020619020c04060602010e10091e030203121302010e18070e010e040207080c070e090304030602090103 80
    0xc0c4c003805120349002550002d12010041c1426610f0705846081002100e1240184101c1c06a0003040031a1190300f00001040d00303e80b00d1b2003240e03c040c0100c0781841c101401d002240c621500680b0080011203400e00821843e00b030145130120b0700c241045058000c1804c0038000a00465a0f405070b801000001d40c000a008904d41800941b22164140050fa0340e0780000700d40700005003020880442155a400340352403040d8014000ca04059656103910302d0302da24081103808611039003401a04c0b0761220320a4201528880d40085500171100d1455850141d4010301c60f20f04920740710b14813000c2520568000003801e1084450b003220102401d00303d01e075000310404421340581000034401c40f17840c0035068002c502d1013a00c03041d9991908008120b0100f60300107800400040c4000065030042c414031203000c0481050600d0301111400d080442d04a0308020001c59840ba80082d4408401c0800c2202c00000c0500c002c1c1c40220703190031502c0316142e0240788001018150045010809607009030080c08001d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 608839199 1250 608837949 608837959
    0x60f0203071a18060408091314131b06120c050f040b030609250c0201090b131809030c0602130e280506011b050a0f0b0a05090c0f060d0902 61
    0x461802d034400003415090f11106003c00800c43c444002007008681c0500c00c54001098605000308482800000350b41c60b080080031540d81c00003104103a405003400c0f401120005402055504940b43c2021100130305a10040445c060280c1005400d07881442000b40c00c0c01c0200c08030702e800003000141c0c2e8602402178610001a00480c02044501d0141e01561040b08211071007007007501c4040c808181404400b016010035004c15140c148070310701600c10b07141d405106250501c003207560f840c400c1c441c6400030705004460b03a191031420004003810450114616035410380411403d0001e5030098803a07543c42100520441d000f1424989a054030340030308008200589208000c2c1c03408180e031081182031300a130381d984813130b104070303405201c48413807141a201d260103071203898441d41000c07680d004044040a0484d900d120341c0e4601c2001488254201c2e404070b100e04e40b40f203610308160b1065000c4e55802429040654000c6900d034555540b041c1c088407180340240c889986e43c0140c55081d40140408060194001e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 608840449 1250 608839199 608839223
    0x8060903130605040609060e0f1c11030c010801060f030f050411131a060d060b070c030b07020f1b030f0106030c050f041107060506030f10060315020703020601060f020307 75
    0x9000110040c5841104201424462a12514252264080d6004060000f101500b080c040c039030040703480715914000184004130004413480054035141c40d8212381340010b41d15101c01d6040285810b406144840110050001061000b00003800c4420500c158400c10600106170700420b40640d0201c0040e81284809201c1440c0500700744810b580d481101501521041100710480c007003901c43c17500c00302c0d69025051080d00e00c203c20808560420880c001c6802d64034035000550701d100100a009880c070883c2030001e242d1a40c113210b0044203008007014103641108000521040c008215400b0550590300f1104c1e10185c4003011074581801419250607642c6401808424031460070039110803581c04079091401c00c80f500040c40203403811691080151b083c01d00ca0800098a0703500a1a44030f07030041c08552200d15802201c0703103070140031511156034076514002401840910340c4866980c40e1889415844c08455950096548005218450410141424514246100b401100e01190700045aa124 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 608841699 1250 608840449 608840461
    0x40206031e071e180302060d02040f03110301140702030306040504171c0509010c1b0615151211070f05030c0304080601180b010507030e06090d050606210c13060806 72
    0x80d082d07442940c0103821850f40b80c4206464410845520107101c0d4003e440c01452640d420310416810444140d40619001d200c041040e0740c52000d1400210f0040707010340d981c1c1641c2400d0500711804800b503811024824010401800d030004100ea40084041c0e9000840b80d85c0d90802c50003002502e46e0300240d032000003452101d1031080d1040c0307540c801c2d4101c03001c01c40e584551700000c0c00c84484220302c0340805e07000910080c404003120060968030380100000318180102c0c011040e02d00000360803150408110002078020b081d40280034a0703061500d000c04225810174410307000041d0041000041c2582d564104103410040140700b680c01000b501c6c02100d450740d40740c1440b25210703402405043d030300c0e900c0080e801280c030700c2a0045682d0740d001a15581c9c989016520102c0d0012681c0c0f08464011074200b14510107600c2d0f00002e0362447e809003014201604010302001940782d40c000c212000c07050090006041e10b403000c14980c0f40c44400311a00403040082d440403001906041d400704005004000070040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 608842949 1250 608841699 608841707
    0x121e071205032d0403080610140c0717070602100207030912020a0b0d0e19030906121506030501030201120b030705062803090b0c04080c06030406020c0d050a090902040e040206031e07 80
    0xf000713034465102c00e02e55582c2d0106111900aa2038256000182e000145101040c400402080d00c0c4441009894429844140e40132042c3c280e80848812913000e0401004000d90600105c1c448000c59a015490000745442c020800d000a00036510307003081540c04c803021982c400510380000c00001e007602d6122424084640c005004c0c1003920f00c030ba40030342800504400810414840100c1d89621841510760078203104440341c050600304180211780d500c2c008143c0201c83c080d0b0b440181a155400b0603998110320004001082115040100340d04020100030b4640c0c01040c5807060310010b40720180c03222201e0100f219510003042490701042004c44a100c040769241d0821440d0a024606d0107006488400440303031944528840c410359508054401000340c608080259002801140b0260501c810340c410310307007440d449144020114000040d80400513400c4a6014024500c82808500b05032400c1f502c0020407030000c00080c0304d880008000381c29503c214500340400b10f6450080d814502d04943c000d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 608844199 1250 608842949 608842951
    0x90302040b061c0b031603050d03020901110a3f0e04060b03010e06031905030403060504110618120304051e01210b04051014010f030e121e071205032d 66
    0xd4004d00170400e41403504400010224103c82c4e01030000c09c004e0203031803070840003034118064450410503400c41641604a04004040708603006540854002103c03114000e0304aa0b00c000c400c800340b015201841a04156031000c031186031550a225040c11490f4000030b0041c42d1342d4202000d000e101100200e01d00c1c0c6030b042c09a04c10201901100c8000c4450501c042403480c0c0300d48000c19a500c02c00c001c1c40015070607001142c100d44104448900c0004000c000340702a00038400e00345845098080400b01d902d410300d030b05100e400c0d030080036500d05414400480c142c001c44049a036100442424982e001d41d20407842805540c1c1c110307100582f40b10300b0707514070409801901036141c421410200410321035021001c00c1800c65403604040c034144081e25006490f800800c2c82d00d5030903d55030f43c64980c0391a405011074004041d00807500703a92501c5228030100e0b20314404c0019845c1010911041000612000f030300d255000c80b03030501c81d803255078402599140e080c802405220007090682011107801c01d8007601 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 608845449 1250 608844199 608844221
    0x10807050c070810110708030c090a0b070503121503102f0403110103020909180c030607090302010813030818101404032c040c0302040e0c0a110706090302040b061c 72
    0x40c02444041701c200c0b91503000300302020344020f1003040800c0b40d201907900240035248014040e00e420590f129480e0015400241096940d6040014110000c800403c0103561001040d01034056018005000c2643c41c034030691003606c0c0c01e6540241c284030080c0c0205c0c90503900c4600c0c1c03036884241541045000c55822070f00c03084502080c3c580f0b08108642c040c0c02030700e1040001404801480d0740c0c10324003141003ca050000301e424000c0042ca94000d40f810b001d018864411601d9450300c00d491440010034900e0000c1c000360000d418104100700107544515031681121811180d101e581324403c1c403013070811498402e483c00a501d0045006c5507030000440441c801c6000380c845403410f1b00002d4023940c02c0070034a00a280d01031441410b40f000e074a03169104044250103840d005083c20b44402030b0f82c05901c4107a6000f03600340070110b03122806503481941d401c0c1c01046800070f0a040d514140780a4188001c5010082c840c0e600c80c1d020700501e8554070301350b60070310102166111144800214600c01030182d0000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 608846699 1250 608845449 608845451
    0x30c020f010c0c0305030a0b1305010f0605071a0c040e070207050111030c0c04050c07061404050606010219150e0d0915090e01090b04060b030f190c050702010807050c070810 76
    0x144903101041071042d41030b6410152290380b215021990112459070005103202e800c60303039883c01e13007043e500e4a80e800c200044a1910000e410f5042420032040b117010780e800b42c0c08101e010042a40040c4104c0c40d5804008464640c41140d621180d503a415540038a42003a2880c10410080000d04c0d0760004495040710f4080e00c0e40c420101d410030303c0c82c0e12813042010f5110568864100403080381440d0b441a07034018100d003019401c0c031259503200e206488804c00e030240030380080e40a100134040140030031a0414000d0000708461a5071034541c0d103400100f800003800e62201c1c4100d605030203a25030003d0350060031150541c0c2c0c2100150b1009072240007140200c042807041c09030080b0302c103805039241c507065801c550048142a8a815040d0001d0400c5000207078111345c68110000d181d050481c0038501407540c00104055500d044058980320300e1901c00e110f03502c40d040420002140b500304041341d003895020f20341070410743c1e61081d003615140300b1055012094400c3c60f01c001060440815461105d20090350 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 608847949 1250 608846699 608846713
    0x712050a031505090f06130207080c07050d0210030906021306021605090712051803040e01090b060306220e0d090509011403071806050a06050d0506010f020c010c02150703030c02 78
    0x100e0b0b03000d81101c40c00382a03048840800814520040001c10aa02c5100181060f014030398840781352082ea08040c2088450070300100d07254a40c00720510454001d0282038404490405070768001600413240c1005a078241a40da16504d4240140ca0301280d1030703500c4051403c00220743c5e489000350364003078070300c042846454502404101458030740c810b640100394940c0c40040320101241500300038400941400d1281d45400302003600100184042c0004200444c0b0f0121a503141c84001c90030740e030700c2072065489140c08008018180d07481c1403000c038108445c24081d843d10107a0115503001000d000d40100782c14415684e1030001194032a407090705880c010b8441d0726132a603980d00360340c0c9160310340d0038810741c15000603400b401880140168161141e82c8100c011568581e1400410700d01da01c0b81e00400b0005000040c0d82030680007500406400a00030700e0420540c4c913504100a4490b091070a00c1c0d4100f007a07041c2e40b00c0655441c2460030b55910003d060444d80e0f028070b0300e400f40082502403004005801081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 608849199 1250 608847949 608847971
    0x1e150a0507091a09180118090201080105040b0a230a0b0403021c0f0203010905010b011709190201090b030705040501110606010806060f0d02040e0907150503040b0c1209160b09240712050a03 83
    0x400340c40c0070627a0684801103164200401c201c0170f0008403c8184d0406d0100303100049408a1500781c280d42000c23107055681746c1420105120350748080340c00202442030204030400060300d517158fc99082a2005415191281084ca0508000014414040d40c99801c04109205008041d0301c0400b00d60426202d0407000c1d8030081c0d8000c07118000321a8200780e0f412113a5048100f06c01c446804d940544140b42440310307982c07500850280754105030359440c00180042000c3c132195030841d00d20b81030b07841060006e0849142c03c50000b02031a000801c050f016040110702d04101c10000001e58050300c03400c07501176440c1c80c1c50343e0815084000458240e14540f0501030001140c2560260b01c8005095030780da810710756074440d1a039030203094003e000506060800c00520400417082180103018800c00005040340c0030f051070390f0701d0451950b60090720b903c640401041c40b05503a00b140815083e8160007407a4440300e04190201200d009105000d4251801d8064513803126604c0070051900401d00d0f10f003000350700c8902c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 608850449 1250 608849199 608849201
    0x1805011b02060307031b090305120304330906020706180f06020a09031703091507020d0c06060e070503010305210a111e150a0507091a09180118 63
    0x15454100ea09040425005800c1c4040156030081840c280810745840a841110080d0380301000c06001801c0440d09201f000380034460800c2c003c9481075810b0845c00c194981107502d014142d500810101340c0c078141510300340728155098590958000070031283e4a00c0c24080007079031124008841c854580031032008401a03a04410f2401504110103841006040d600c0714001c0d07009040350014420900e0b0000002954071603022000c514698050344c407400c0c0001c1c00da180210500b202c80d907032080c0108021610b07078001400245810286040c0c11042010f0911900a19080c0c10240c0c0001d03843c81040041e40c5c01500a504807441030040304c200301d504c1c103d406c400303c0c101506520420b00400040700301c248500d1036600048002010784040c4092226000c5d18000703003000b00d07070f6960003d11004140c840700001159104480060a0086107005c180003030070120b0502030004150320035030009401207804002c1e00d6240c0c20280c10701010a0b9800e0b40484140005d2251400d40b803203c0f601c25009402c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 608851699 1250 608850449 608850467
    0x6010b0421050a170408030f0a08090d1d04020f03100302180118020c19060e07050f030d11070f0f0e220209090c090f070201140403050a080a1b180501 66
    0x600500348007003071559821000c01640396041140e130028400450401020b00003050050812814a9503a5030125005000120002c14800b600d4010312412101960415800501201c030650800074400203400007500a0050100b51402c10340003104206c0028120f4401d8400d4078001ca40030880304407000c094492860342405035420903010580909142e1046401525000444105a944d4488046e002c5070110f000c804c0180e0b442034591031807091418050040ca40908802e461110070b08070700401003a80c0f14068000c100412034050600352072104140a134801134040c3c2d10075850016505c0c0f582e107850000e00e00034110242c0c7c042c0d000c03400c0c1000690600307a4018402d449080c101e54142c003080200c0780014071041041c0150340201505a480840d4035108003000c0d01034121074203225030000d00f1500300b00c2d41070401e45040c10501010039081030607035078041c0c00c2c0e160100301e46d030305c00d005503019158118104110f560206803d1042580000d14051490b640d1070b80b00075043d580354011604921 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 608852949 1250 608851699 608851703
    0x50303010e180724050d02030406050613090c18141f090b010804110a081005160c031706010c020d06021c0209010e0103090c05120d03050603010c2c0306010b0421 71
    0x41c00b11400b48201e50101d444d03d84907034242035080240000350041079074000c860407079499607240c0820000b0300d8546035142040c0d40140e420404130724250b558003000c00f40b81c095800c0349500303503503503812081c265007204a444800d4030f0924010b00b800042121801d81c54040000704003040c1c0b40c00324804e01e0301d00c104454580142e4803118070342c849440b444400d01c0e42006031900200d1a50011603814400c20100402240d00d0000245610342848861a00402150250f040207031011180300825406405d104800d81c0e0780c07a024140c1c1e100c8400590701000c90040080d0081c004826a40a008540d0f014100c0d1902c511450361a01da602c0302050200e1003050804c81c01325403c00d00c1803109520941c0320b100b09610542c405640070380c9610010b0b0380c109220140c2d00716544244d00040b10345516015042c2c10041c2940248080e59020b0703401b4003602001405c1740b5609000045880a2901100300c1036800703140075081c0e56143d42c40c0c0346514400e50050240c0d080201014010341c25141e0120083c01900e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 608854199 1250 608852949 608852969
    0xa1d07180509090106080715031503020315090307062d11030106031a0d08130b120103060b06120408030106030c051e0906070606093606020a020109050303010e1807 72
    0x39042078208205040c0140c03d0580540d84c030b00c40405e24405c2080302c2d2000d0902c1c02462900c3c445a03401c010165108045d9017410f520500c03900b080140c40011f1141d52600509000001680c1c0d004021031840c01baa46028048030f081140540d002c0c2c203100c0e0211151150004816024410b8010040c2522001ca40d000c481c0c400c20401048010f12aa020181540b4060001543d03c110b22001401503910b000c416514600d00080030001c490303014441c10b00030642e020780a03090909903c0b1952107180c0c14800541401d40700ca408a0315a0798820440f00c0d800d10050b0700000c2402d2600306030109030001d00900c004285404190b0b80018008c0342aa0000394183e01c800049209540000788540c22070b402d0550803003014812000001c9c190f020b030001402000c5000907409440d0818240c034150640d042c03400481118009000005c40050030718406504140003507550301c1110000c0f801002542030103402030102000100e6114010902c0310300403600050581d06000d2107280403521010140300e030130b41d64 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 608855449 1250 608854199 608854247
    0x6051f05040b03100515031507030c02150a0f09021c0b060411160302070b0c06070f0804050c040b062203020301060b0f03040f0215030703141605040509060f0a1d07 72
    0x801d254200360fa11501b46000c40302041902d8011034500b0000d5008091040703100070820040b0784e4907100340000384415100074407028064030044840440d0140c4021000c039219034600124120301d412011a4a5028000c800c06408a00e20307032440700b104da20101c5400e02d484001c034801d0310345402584083c40c0c05007640780c03030002290035008031594030400803000d5002c0d0440000b00b20130000e02404ca031540a0020700b00c1d52030825002082802031142502c1841541411301000c00d43c005a041c44082080e1000120305444000041c06805400030f10b00140360801d60107903079644103900c45402c40707109a00a07c80141c507045000114050304004403a900300900000b404522401c2c07e03030070070301d00207030580704003c4804c042401c4940c81220a140880e441d0322800b5140241c15058503440843c0d007402e618460102c80d0010082e219a100703c0d072082c0101c00c045015551904404149134200074401506d0555918501c0310060100940c0c00d0312030a0301001072903090151a110103142c00f284444001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 608856699 1250 608855449 608855473
    0x109020a0306091b030b190605130806040804030b1906120204050f0103020916032c0d090303052a010608010b03060705040b03240301060f0f1a040b031306051f05040b03 74
    0x60850400407580203ea80c0103c90000d0743c56011032000c1c20852703407081e0355049521804d0803540c3d020740c01510154090390420022070b0039007040d030702500e82c41070144000c0e80fa000c0314110f260100c0020349000c9440c0c07180004800449000343e02840d03100391014002ca07a22480c141c49070500905c0046e40056281001072180c3c903d00c82a4a44d11a1904000440210705095040000c5242504a03079401505180c4e0405120400048511079541c0c07511005072070441d0707801005409108070030700007904500f1548000030250717038800c00350b135224000820295907616119400b034041c00c510507000f8090403001c5403203c3d2241c4116020f071008540c40c907142d61944010540c07011b0001801c1e440c0c5641000c280005a42c0a0184c40000c0c01065000c1c0815401d014080c8009111688040d04404107011013000000c42d100645044408208182d51240e1b201e44d210780d050700b1120340040c416494a001c024410304e140c1090562428810a4900320944800502080754144030140d40e00d640500700540c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 608857949 1250 608856699 608856701
    0x13081e19020103020c150c0904140910020a0201060b2124060f120411011409091303090305070801050907170a17042313020306010f0c08040e0109020a0306091b03 71
    0x4803001030344c030440b8900055080d001b9501e0380144c034014610000040c2c200524030381800703290084e0354031413010303445402c042619a84e10010007600c64003498000c100003400c03600070b50002d80241f410890856a41d491005803d56603110341c549250b0441400d07021894100e25085800804006120710b01c941826001c01c000082c2c0201c0501c0c408464100050100320050040c0140110300c40c6c1018645020514009040f809191010b40e0f0440c2c01401581d0f0345035075111110780c00100060002280c1c141a050803102080981c1001d4254031502c0b0f8002074110055010070320411390041515403060f00c0756419142e90580001006090f032000b03000901090141a5501c409500003129074640b9660780111700000002070340882e8207001440c0a60036904146131400c51100b5440011450b510708440041c00302c17030f924041c503003c21004184000811003024201c1d0050055400e42640d150782da1250b81001e5800340e031902002a0429900042c0d400304c0e802001c54000d140542c1e50310728842d0389400c82c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 608859199 1250 608857949 608857957
    0x30c050a030f020405060c0c0103050603120706090c09180605090a020607030e040b0a09020a0e0a081e0f0a0b0919080d020a0c0b0a0b091609030f0813081e1902010302 73
    0x61260b581c20400042e00c1c6d07a424008210040d4400d02800a02d0362583c00981182c0005146c54003a4010595829100c41b51808445026900105c0000c0c0203606051006180744550030a41140340f078482c0014481c58021b1486842901c101002d101596038055070540318405004000c0d040b202c144041c0001a025101e80d07084520b01410005694420000064100540b80d100d901000da0014030301e001164450180d00000c041510300b408201e1070b100f0142d50b03e400705401e826113104000c5041006020901c00007070308200180454a580005040031200321034250340b009100e1254840d86500007d4500c40c80d81c0c05900491102d00300a50810441d021b540040d074000c00300403800400724009640c000380c80d40942e04d09a80068407032884410321044520150400020301c50211a105045500c030202400fa48d501a0808e85510814500304001d80202040a80106880600491040c20006664045105a2030350481182d01d1006c402e4a8480e011200e030b480c01d4400d0204000755000b50002c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 608860449 1250 608859199 608859221
    0xf0601211a030d030908310609080f03070206120709090204081f0b0f040c0c0609080d060618060e120102030403271d1f12020a090b090f0a11041410030c050a03 70
    0x280b51f03082d500c140541210703001500540003007202100c7c00e01c00b1711410481b0a040500710801185045001d07000583c080c011000010381c1500d030100002c072802c1c400d04c40c1000500c1004400c0d5160303a2168502070322040da118540d45c480d01000701902e8038160342d00425106000260483c01100c1140051001400d0410300003002d00030f200180c000021030743e1260040250095a8654445003960000c4050340c07280c0e0701000800200c102c200b881c041c00c60340e0101c00c1710b41c0c1d400c0c03d0000503400c03c041007001008a0807528207500c044208001d0507040265030710050101b0503014030038141d5000c03070440c2468030f00078485911180c41c01c0d0410b1070011464503800c608102400b080c041000ca40348038002c07a140e001075800546071400d2000b103040c5041c1038400b5123000364090000c4003580022420420f00205806454800c071004500c80034042d40c41200c2d104032008280b0750700c60f22401021859110181218040ca03041074a82e40690311a220300c88104110350b50741480c0c0325010500320060031002e008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 608861699 1250 608860449 608860507
    0x2202011e02100606082502071a0c01110f070204020906090303070311070b12070e1207090b12010209100503250903060e01050f0601211a030d030908 65
    0x225000d04281522061000031599009200004142c0390480035140706502c0a0705004c80c0c0418000c1042c054104810040c403000c1c9000c9480d40c2e044400ca2a04003a98003148001043d410125401002480100400c0000700c00a02c42406042d2102120344201088001401d000340700361401032600c0d030020001002c0092500e4144200c840c0040d0441d444908102c001c41c52158401072101c1040c44000d0017000bd0311001400c208126020707002015004100c901000400d5000904a540b58499900d02610200841e09502e884e50440e07001444100261441002c1060061100c0ca005008407042c1000c0507200c130110b0340c0025426a0340350400307041000e00c40415004044a007e14030009116070302595199080c031403035030502208031102001c549c409a4141410480701c131780c103005410f0300800203203800a1048040f201c500740c680c1183e5000035100e03042171241804041038052200300706404900303481c105c111804040e800c0b10010032000b05440f10a11000f0820141101c048400d1911810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 608862949 1250 608861699 608861717
    0x50d080c1b06190c0b090102031006020606060a111c02070501090f24050d090b0402100f0e100903141b09070804061a0402030708041b0b03190e0d030903020d08220201 73
    0x20790080401c5c4100c44002c0c16a501004202e40c8850034620b040c0186214000380c4a50f0400d0350104076140f088101d42c03020301ca00110b1086400d9800c000c280b2103060040640302c0700200300b510081d150795061107081c0c00140588404120141c1c0d081c0d50004880074007071401110062a084401168452010402030000c00e1042030101d111034003801d0141445800c1880c0289824030401082a140b141c4500400219025924000b80c000d00800e031174100031a84883c00101c100011262002c258100034800d10004510114101000501d11888041921440c003401064403e208088604540080c00030724890007203400b0039a0780c1e0101c06034442d60364501a4070720391180481d090b81c4c42520700c600084e0a42c4200024048000c02c0c070800490700c01e0501c0c980514100c202011400060542e91101c2820194141c21844580c440084503014a050754042c3c445240c1c0940201129070003580580a00d0075460162885130b000503110344115840590134003003406030112100803401c0d0803030500800c42 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 608864199 1250 608862949 608862953
    0x903031d1516111f11040806190b0d0b042105120c0403171b010e0d05090a05030609100f0b010503040f03030906020d021c020304030c0b0a06050d080c1b06190c 70
    0x800203120301c503000005055007a0340c3c2c880180480c1c41e520f2120020450500042c030400b0404180141c0100c55086140d04851200c91014000e05842b0480c0d50700c600152080420850f85e030110521460141540810a40b000c3c2e0396a44400c1c0e21008080c00070f003040010005040000c600035030811200c10301c0600703054a036030b608194000010040d00790400c000c40c41e0038240e10104212906100100000d001c2c0c40c114112841e5030301081e0040000f449401306080f0090380780d084002c00203004c02411503150b81403040c07030180c84030180321a8110b65800c0440300c000c4a440340c0506a201c41060313450300d2940d0381e80d4540040c03070018100110109902c0c1c00c0000b0200781e0900107081500300c10300f0010b0751a28000110800920f4000c03414000500520402c80401e8002d80503a400e04c1e0030040c40a660364442500070001c0c40907030091a401852480d40d50103100c0840f002d0200c40b213615088607030040f201c040c12060b04440c418465803143c1c00700700f400240e01c03004040c40760300c40303480c102075074484029 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 608865449 1250 608864199 608864203
    0x30c19020f0703032007050121020702030a030306050102060c09150706140a050907091e090203070f060807090e090601030311010b06040b0703140a0806040c09090903031d151611 78
    0x1d50081c4c0000c0c0b41050128861600c50300003038001c00460340180146460f044c00030300f600d0f06200d0094081d8a001240c0070758442d0f960100c90324a940202640c405440e0b030b1501a00610880c09054010300c00d410001c0c1000e07984100300d40310385d40300801d0b40c1c14110414440ba06c00c3c1c0c1c880b120441c1c4144d2074481c50100790000c0c20301d007401640e0400300854146408800c142c03800c90340e030303001d06803e42c200040c904000c40410020901401c809501085100e000c0c00428a01500c550180d005080903203000200c0d1540210024065091079640103803c030365511080641c01000c2c2c503151340c1904100d00400029004070301c440e109020301c0c0004a40c00c4000c1000440f5600f2651005c200c8010002d080d200f0158040d0110841c07110501344607081464840c4000e04459004021a00031680c0d1182800700c0c034062005c540041c0042c0c80c003400341d0030807454010050600e5500072030005402c010800d007001c02c0480d01602e6030b0058a0b1140c0750b030740c0b44030040b8041c2c0f50254000040c403042c064081d28010007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 608866699 1250 608865449 608865463
    0x408031501030902270601020a0c150513140f04060302060a030e160f082b030f0906020f1306050c100f0b0a12140c0d0b04030e090a090204050c030c19020f 68
    0x44001245c1c20352000310404065440c0003050f40381150019a4408006140d401a58007a14500c000c407441c2c1c0b0324a00020390b464030a121142c10b0b0903442c0080003515801030b00d00c0741e181c92019200020014005424001130725101e003c0294010024841013001c05c9c442d40c42039000e100018111907084910080d4074a2042c510380201c941c06e01034100c14010502c00b0404280b400b098414580030070000c9088500c1100805800314080545074038000e05004004c0c0c100320301264100341c085658089801c1b0410300f681c00050501c1d1913000e90400003400602510a0322500710b5050040c06040404040000c010a441c00685100b2541c030741025525485120180010305001004070b03003400072a00309407a081000e0031750080c142e801450300c80b01c0c0303840d00c016108605034480f9450015032164a070649425001600b01d6403c8500a000c1281c40c120301c0e0090380403c0c0c000d0340d0400c80e0351a40c000c1042070703201c1140d004403e4841007140c10000388166a92405500092060703503a2028020700c0740c0d0418503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 608867949 1250 608866699 608866729
    0x317070e12010b041112010608130c060c030e040e2104090c020102070507080703050309042d1505190e091e010506040501050d0507030602030c040b1b150408031501030902 75
    0x255598403070704a400d15101d80341441c40042082400c0840141014070005014001c00040001e00301c045008240c882b400d035200607034003034882d1031200d86401d4001c0500700b04001c15800620400c50b00310391410302d4440c3c019070103030a40107071001c0110010f00c0b540051340d00070507000c1c84008100020b4180c41901c100011009182d0001da9101c2c01c50400e50714000c5aa00980069000f4010400c00641e0000454503545403d0310003045a40b2101d5040811f0300c010700700030b800390030591041002d8112130350001c00440340f1641c08403041ca88a1041c041c0c4440084d11258200e04490014400903580301c1c00e807a80811080101e80103100c0d44000340511260800d070004190303440d03070140001840d050207454094002540d01100844031a214266661120710020303100a03400800318070100e1101080710050040d14645540d10f084460000c003100c4944495410207028165441191555503c040750085400c400b88a082d6101e50b510b001415a420503024107155450800100507207900c418040101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 608869199 1250 608867949 608867951
    0xc021c12091119120209060f040924151403070b0a09030203010b06071e1110090f060e010f030213120602030f0c0c280611031005030a0317070e1201 65
    0x1034030b03141441226502c4031100346031005030100a0100c65043c006141e02e0030740440b02e1480305d40b640c070042000d110300781800c0c0d5041420071030000103002c1c150410405003426084544c0750100300c1d0b0340304800c490642d03000051084005d01c04100000300c44c004c0348100031000381910451940c40c803603c105984660800d01c085506440c08009501e070030301c920012214113031601460001640d880955170801c1c0c1c07195006c8040302c05d01d003000703000004004c2c500541020300781d200c2c84d1000c0100900000744a1251004032200301c0c07408030380f0703030300c40d01480c0a0f00c501a150070910a10810041d0301a41010844a51030078424000045c800501294013001502032180180d507405c0003009003120362001000454031103000c12488000140001c0d210003e40040310107000300c0d210600542c0340c0300d900d000c1c01928183c02d0042441c8000070070300046004503c04040c08060326915014180c42c1d00ba200000383c0801d041041500111103054045a40035a0502d46006081c0c0e003140000d01d040310400ba4a4400e07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 608870449 1250 608869199 608869223
    0xa080c0108040813290a0e120c040501080a0506060a21110418050c011817030909070503160e060a0509030f0a080d06090515060714010e06190c021c1209 67
    0x91000c0c01005c00000000035452421003a4100a400d40303001d500c601e40900c1542d900c1d0903040350103001e4a400108020414042541d40d000380c19515000114142e41900541002c102c0b5440c018222004840030481e05104c01c42c0e80d0311800000c0c0201710300a84c1c0d0050306140c003c0d2280d80741e22642c0c29000c07007101030300c551900b01d0511602d00211012201c0c1171107607148194081001100e0b4840031030756940e1416234954051400e10b8114020390441a03000300200c0309100c1c00c0d40d003040240d841400e504264107400c00307084400725100598840e900d07402100410084103142d03c10001810f030060b0240807240030b000b1b40c160340ea15154003035a0595190b00040b8031310038030080c40d000f00c400a00a40b0018030540c10500400280c0059000c00a0f104500c00036501003003010510340380e400408188002c1061085c113203800c940303413101240c050080124229080c102c1508500c1f58008800f80c1d40d004007000d410072440b41d00003040400c800001d0240200c401344460050340284068503200c0c00400c680 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 608871699 1250 608870449 608870489
    0x3030807170720060f460b010207060507120c02031006090b010207180e1e0703030305130f03080603070803040605040e01080a080a08060f0a0303080f060a080c0108040813 75
    0x2500c0388480600000340c00c4801802104042c17540c030244c1180040c070001a4242d01d1340701c48280001034204000c1d19001a40b04403d4201c880c030115501200c1000043c080f80e0074907401280c4441e114025540071910a0060001040d10941c01610044450034032180800240e0002484c2c8103c181011034980e03100c00050100c4d180314000e00111110a00080c0000c0c0c0c2486503c2100381031442100084603a500c04100c01c1050130069a00103c90021014050114000103203403554021700040d00403034181000b040d491505805007840e4160406205580160540d80c00c913000700d0b000d407215034184204000802d0000d0709000800003003504d5181d180d56980390031082d10b0382035016400080503800000d02d510101c2c061504403076a482903460119002e6842400040c00319a004103400d402034003410000c0201500041c00c0ca00840b181001c02c00355076a0b00007082048142c50261038a150410000b000ca15401003540d9500144204259800c0101fa00720818036075032664014900c008003919580a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 608872949 1250 608871699 608871737
    0x10b04022b150303030e120a11070e01050609060d0b041503020102061e010b031803070b04060f0b030c01030f0b0616021203040602031204080c1002091503040c030308071707 76
    0x41d030182400d4203000700d1540e08a100d800181e640710107428541c5174000e41904a409010070b04601c4800700b81c85440701001c1400421549020041d10083d225404010078200c0340204154100c1d00010101441c00d010764080c80001c1d00b00108102034140c41d0300360a40155901e000303412040345118840780055146000080c41c040d40504a903590494036001d40440340000110a03055920000c40d1a0f83c036102c410002485590740e060200c80750001007419401c10002000d068082e0f805064184040344045001c0340807580f0705004142d240d0f001e217080f444194083c0c1c0045a89504c5481c00045a0031041d012030141e038812001d080d0210482070b820700461038080301c040700c03140c0700c60300440c101030410801a51b02e11424100c05502080320ac001800c1024407030841d0301c0829030400f80c402c40422a25100060b4005500c3d07203124140000308204080441c2050b68416604038401c224100d2854034107075512000540f0b10300400c0403880303180c044d150802c0440c41c080c81d01c6c0e44c0c07690704003c00c030369a4034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 608874199 1250 608872949 608873017
    0x1080d0e0d05060f0a0b09090d05031008120301091410051219051e0f1015120b160302070209010902030703021209073b0c221d01030302070314010b0402 67
    0x544500400030a1008e111030014069120341a40c1c00c000303960b0344034250b04c3d00e900c9044d548042828420384d07900402234250603002d18100c401544052020a200f8590582d001ca42110802c0c3d145c265401d0400503807511784040f60003921400240d641e040c03081b6046400c030303030107a80040d10a540031503400b4251000212083d10704680b040040e08401c0c01c445030701da84950049030064100f948031642c0042d10508082d440004101d071003040d40000c915440d0102c400c503800c80d20302010050300b03041441481d000c2e00848a801da401803044d0603603820021403400075003003c1c2c0400d0415500703101414500c03140e1501c442c01181c600004021340e80c03404101100d4000310f10740710071040c54058100022500271212100d440480e070402c411140c0c0d0b42140050301405103500302d41681000c2000d4900b1482252044400e440041c100214540050075180484031428070005006031f000c44420030100344256a581214004100041001c100c4980010140d070003d068032445001e00384102c002c1003440030060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 608875449 1250 608874199 608874221
    0x90e01150f050117041505070c0c0b0a0f03110f040f03170412080a021018051005011505160f0602030718080601060f1e0203090306010e01080d0e0d05060f0a 69
    0x2428003418034000900403007402081c1d002d510400c1000c10200604e40303400ca46d80140c140420811450a02401018070b00481c030162142e41420001085400e00003085800c0c0b040c035500d89101000b0b407814200c0c004c001c0001104030001c03040c4408048035100c48004e00007071411918805106081d42025408a07440c01c9107032805003400c200c02c00c01e29070351040d03c0001c150800040ba8440c0359010f8240d091040f800704101c2c80138500901b01e610a0303000d040d0060000d01400480340e02c00c00030044101100d400380038403105c0740348032515480c5041c030585c020072100c10b006644034008040c42d40c4500e12003400110444800703030088100700d040f41d8021006071000c654200010452880c0045a40c0c4a40c410b004040c04c0018042008054a0190684200111088440c050340224004000752a508034800c01d52003400346d00300006003008030068407416998198041c05080e148a40c2c151100034141e84650b400150080c410404500d0503c0410f208110780d028030000b521305001e0006c1225101d0200c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 608876699 1250 608875449 608875469
    0xd020306010b030f0a09150c020c1f02120708030411060705010c050406080a02270406051e1f08010e04020121050a271704030807120e0405010b07021504090e0115 71
    0x80214100c2c0207081d017401c91007c0f0014131504800e00880c2001c8001d4446a0440c10142100000e4051400c0c0800705027070035400d94006042c031100701d900394490401e01405001c02031000c1804101d0741403032a64004401800e0f286070011641d105030079030715464003560100360081001c04c126500140029441750304e20f0b20452524991202084882c1070041c51441c00e000110400c0c81c194039640d0121000e000c00501034880d19510f03e98070131a02d40f440003c40d002d2418420f84003046c070804d86404100301101d45034009103a0070520380c070b020010010001c2c0c0c100f2800000888215501448080b0002035907600400c40b0701e840700e40b01d13040ea08240803010803007100401101108041c1c1b2003110106520096014200c0c01103100f07a9180c0c043c0f0f42004e0004100015580204004984801b181d1421500c84000b00c040b0242080f04564091240f5009001e04100180c01490b0081c1d0007603241404ca1803040c100783d02d91200b4411540e040d5901c19040e0b40d121010641d031111a02844000c10710604 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 608877949 1250 608876699 608876711
    0x24010f0806070f050c34050a0e040609080a172d040c0b0f120f01050a050f01030f15060215090c01050f0403120e1e01021b0d020306010b030f0a 63
    0x480c0555541d030081c040c6080010b100d03548000c641c03240f0110b0707030819801d80480d6240c0c03014099a0352002c4003886da00019400394885a10503104240c0d85c0b104842000b0461500c1c1464400300c2ca110740750040003100d0490350b03408044001940c40c40a170521003141c1d561a00700e0f0480702e0b241d8801060140c411341200054403810b6808030040c03502d0400d108a150300304506507d0361f2801480403205904042c0240700c02183c404040340380100904502d12005480c402640c0b41c901480e000c0007428000e90b80c001d40711031000d00003414800c0f1581c003132200c103140000340280c4480120048941100070040b4180c1801d10070815654100080000c2e01b602c6542c02e001070030000346103a652001c4400d10ba06004020804605100306041600c00960b040140001c098904060040c4a000c408401d14412004043c4041c0c488807282c0f0b0801e070913501038005008e05a8144a001a04104031440340c0e40065404007950040e00c082c44828020070591000940343d041200402c10281c20041045144510b00a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 608879199 1250 608877949 608877959
    0x14041104060f051605010e0d090e0f060d050105070201050712181202031c0b151326011e14100302271801110a09031205040824010f 58
    0x542214111466410140016800402d0a80d200c1c05060070103220844c221141c90188007043d00082010081402030700c80643d6411410b650720f04446c000c140380d43c11000000f8a0000c64440e419810100c0101160140c10041e034a40d800e40e00304907034840060b51140305205102c0e0b082003800782c1e54002000700784514010310042c00004402940d010303201c014541d8424203c1c500a0045030340001150183e2042c50200f01c0c16080a001440440d50290a07024040c0301500c4885007614098181c100d0703c140c0c02440c0c003400200c040c07196801c41c000d00b00020b0207180034031424454003141800303107484066411400d01c0844220b66032410841000303510070040000c1807885280140559504442481c551034558541c20082e201c549070800384400750f002400459044002098442c0b440b00f4000d00c0070400400580b0320383e0040c1c40b01e183c04510820400e20000c0e0465078680d10520003443c0050810ba61384c5942854801d2407141c600e0f405180002941c0820400c4d5803190160401000d9000c0981c548 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 608880449 1250 608879199 608879231
    0x110307030f23090609040e0f010605101706040905282013051320030115140f0f0901060512070306181a09011707081603030f050702040f0203011404 65
    0xb0260f9118801c0042c14195554030750740161001001d6404881d000300c131050140307009180c01d0040d0b070311a43d012040805d070640304000d41c0242d00d4801c100780b0101d45a15040c440030384944a421101d9014458034049001c40d0b41c01040d080ba03d51041d149211803d5060481004c00040c00b0382c0c0d54004548032500c0c1e00e4036080c507030100d11410020700007000e81d20804401c00780340c3e00b4a030080c000107404219403d624443c40804850f00c60840003003098a0310b00011410801c1d2901c074400007111805c01c244403c0c54214190078424a020307080c8418052082d00284504000f6003148000c680c0118941d00961050300314207034001903078201002007904221810f242c9a8240014085c000e803039030f080f404944a41e1040103071070140546083c032256115901c0c108602d5414441c0812803081390400200c10400140c0c45080300400e5040340d00032070454038100e17070003840e41f05400c043c05001c03c08200107868a129000c0943c3c0c11850043c0c80754100324500a01c0000e0f6400b1902c21824445000e002c0045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 608881699 1250 608880449 608880457
    0x40501031d1f090b0a06150f0e1011030f0403121706220e06060103150f060c240207030e27060d080f040f1a0301060f110307030f23 58
    0x1628614080c0351410340010b00c041c20440c80020016a0300a06000320030b1256004802034a6000c8015200d078011168111100e14190912100043c0402e51111541c144028059461001d91600c1046c1400c007040c0546598040c0c50001003035800001d00700244000c3c1c0e0101300080640d40f81484030840c0382204504948006002148240210352041410418071000b05414095001c800d00200b846440c403da101c0e24101c3d4030314042804c003014005281e03c003042c041e09079405880c10034900c40c100502100d42000d06101101c40c0380d40c4040909118981c101c000d883c031a0000e40150b0f8505040c0b0700280001328000b442401201c0d60244031055607032034a9900c070507030300c030540c4030106540d4440014003210703400c080945128000144917440c444500d0080081d2036907000e1f60038429650300f40c0104030000440414025800074001407000754410301c080349410210f40f07000e089480990302c1e6541194450402100480c0100d044810f0755900504d08044a0f00712282901d600c2000390200101845 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 608882949 1250 608881699 608881723
    0x1103030601051810030501060e0a06120b04061703070623161e0507051b1509150c060a0c0809030a14210a0b090705041e150302040501031d 61
    0x30011900910442040b140d000c0001c43c0104a40d0302182a6000500280028016100050910b00406101e82070448500007160340c07a9a40c0da0600c5502d40ca200002c10401ca0b0300da500c261100c80c0050034828800720342d5500704070741d8007440e039405840c94904202ca410048003000400c2450b8070380c0701e40b490b0501d42503000e070840420442e0110501e030112241200031402c1c03c2000c040313684c000c2006a000d005001e54a2240f001c961880d123100c20000c481c0b0454802d00745d0b100c030072030307400720310168445003d07152900d4082c003082e072a88541180418540c00107610000f1079404030f010485178660a001c0c14086448608101c030039410882c940e151603101c1d21741c0200a0002c40e10b4031100e800c203c0c070221860004050003114500403240107e40140400781d5850700074906100c1d2041841c6084401c00b4041c60590304ca0910b40b61815a0103603a11003074400300b540210501070000740301d03000e900000f8540700e402e40d4016641c2d0300300790000d41207032604407094619070071041e0342035000040043c0c0600450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 608884199 1250 608882949 608882957
    0x603230f1b1903081605010b030307080f0708041206090b1302131d120c0f0c0f0d020301020702092a0304150b031c0302070b071130040e060f011103030601 68
    0x442070801c2c100756208a90f10003030080800141c00b850740021500e0300d01c00288a01c0003030004102280406a91340a030078400b40c110241003001184600b0400010b2204a10940c0b0781c83c00c195581c40d1080c1008510403066440c0d6031544000010042040c04441e440070007004a11900030054000c951780d403140041a4038807655511039008100107070460469103406107021100500e0b08554000d685412840f5201654468044c0340c100c6144045803403181030b88064500744521400000b04400507a030b0756800d0f41c041d542082440c000d600ca40c10458800c4983d02810b00c0e000ca003d8000d43e490440c0f40800d50010f2005109103c00103210448aa900c2d18450174042207652607100002c1c00d09070035200d2601c3d40d141c0408113202e03098254025204003406890f0400c001d642e80003095840d0301600d644281c40d074007c0c21885103c01000450320808407002c0c07501492110404070f540c1c00c140d0141e0801e86c529040c00b03080045901d4182819107101000386000807924005c4286103a8a02010b01424144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 608885449 1250 608884199 608884219
    0x4050a020c1b0a0f0b130602031602060a03180309051e0306060f030f070909110f031504150614040e0a021c1109010b030f01060f0207030b0a0603230f1b 67
    0x250f0302e4804000161840c000c1ca50b00c0c060780c1317040c114000e501000d00f0103410000e06a00003110360020041c0c07982504036406191080b13202e5401c001c0581d011980f40d01c18141e451400c0e030380c0d2500100380480c02600c02d03111181020700f040100080c80d03030b219180e00300400c0140c41140c0b0035200403612603000002540d01046c0728503403c000a040c2501d01e8922941403080c25070008041c0c210781c00084129028100b601080c1c900c100600001044a20985e901a44a070144040d400601040c09a015000e406a10015105901c401042d60060382c440c240050080760b01200340c1ca072030f111f00030907140000001e00400d501a0301007480452103040340082d181030440c090b030038042100800f04290303a000304840c0c000d684680c42c1140c150401e803804451101e42400200d41e041c003860410f0507020030764006051a0b451a51928902000240519003150b1502c00c0080059014511001d0010030b107000d18001c424208541860140c000c0d48030078090740594084c81c520020000c01e00c549040a407900980 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 608886699 1250 608885449 608885503
    0x5070b0a09020909160614040621051509090105010f0b0d110a17090a26090303040b250807080a0c0f05060612060f060f01110a1104050a020c 62
    0xd010340700020350040b010034200034010f2004180500c444d484c2c1c0f6294080c054607404100c600c3d801c030030301d0700b410740000304810f00c0054010014000349081c0b540d4810095000301c91301105a0301c0a59401d0003601c1c0d442c20b404c90900d0b101c00402e07400049080208240d6140030302c8501070940c1071081c1a044440010798103c80c800304c0e08054451080182d00c86e5640ca0018801000082281503125500b5072a07004903015801c04541481515049080b44211118400744003004000c5070303108111032081001141c03040e80307052000d00014410701024980f140a02d841c040c0b80c00401215400c0114a124030020000320017905031048140c000c0d81454580e44e01d458117442d4407a0102010301a041c507005104204000080c155200d40c2c005c0d9122003210041d43e052564075001910071040f5481800c00080701820984a440d42003841403410b48454003144c12a1400d1080209096401000041c10013a090806000d5a0f40000540c0802c600d441c420300007180e100c02260300c852001c61260300305998 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 608887949 1250 608886699 608886701
    0x1214180f0d05010504110f0618040e07081c09060801180b150d1b1706040b06071506090c0c1a07030209032b030209031509030403060f0b0307090c05070b0a 68
    0x241c0e5011000300242c1c20503090840c489800d014090748510030700008106142001030aa4216140c0400d003003540d00c2002042201400340d101c420505440f84a6000400315000c100d04802003034004404445140c4034074000745061a0794002c00148550440100403007030321021020b4443d050203000144202005001800740060210300030541c0c1001328008245200c1c9030311042e01d60f80c00c0252507075844c07100c000075500e0199001e2210f03658588040003030103a09060b01715031081407008051030f19003c525030300d032201412014468030100d0340e0b824051040214030300c5922030240303441c14551002e090320340d10224188030100c5008600f0114201080c00103000b50151082000c009003590f00321501014042104400846100da00185014a00c085d40340203200325603c1500c05009420140c40d50000031454200140a001d010700c000c020000105a1902c54040e81c0701d90308402090b01d41c407078400c01d89010354980007042c0040c03030a044902c4e002e400401f200d04280d84298110810764078005900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 608889199 1250 608887949 608887969
    0x323070510172809050c182202090114190902090a050f0d030f050d090326190b0d020d29060609061c06031214180f 51
    0x35000849055005422600b081c0d1090802d4004668040030395181c0301c0c0c40c240105100f5000c4031040604034035610950050700300c1010b4a00540855801300c2890022605801b004200c400342d07059070000f4443c0020a51542c83d070800d801c0c008640304c03584c040d000500c003420107214a039600706811017408015141c0440d40c000c030140d94075142d40ba5075902c1091402940c030058545124081c24100411285044142c0c0c500004014103007010087c059981503d551070802c070404244442482281741d503520038003076a000d180c881c1c0d982d1256105d200c10b42401004819041c506502880001c100f11851881c032041c2c02030710711045c04518048041d01142c00010108006500840c46040e0310f800d101480620564104005141e500c000000480c0000f5541c800c1d03c240d548101d003002a041180742c00000360070351800c1115450404100014614101c0310164400c49070800000240720202e5080201d074030680b21506589840d11429078241c000e0080c0c1000603601c607038050f114898140d15800c2e520 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 608890449 1250 608889199 608889209
    0xb04030c410f0a0302160504020c030f0310030b04210302070b0a05061201050406020a0e06040b0d0b01200106080d02030901080402060c0a080c061504021812011b180906032307 77
    0x1442c3c0c0f10b900e6040080d154a05100c07051200502140001050700f818400c80306484403100245003809403c1100c040f441c0c4c8040c0001c030f4800382021001c40410184441c440c0180c0c407940881c110b0103000701c90b083c1e141c0c1034030800600385031044c001540440c0c1405581070348060b062000090940d031380000924080000c1000d01c15942ca007030100010020030b40d006150780d0509450b42c904880103181004200c0c8101c2c0603500c1c09010034401c1c2d00b100342854000355688101410f00ca40034000810100b0521032031814078446980d1076080401005506002100120200d44050b600d440d4030400083d00590b00504002d0244600140c503800309003040c001000c450794000c056540c0c55a403698002d586070f10585414095090358054500349103440d20850b0f5582c03490501c41c908a0b10214104681e00e114222405019521442c6400380d105192606400c0c544c0d042c1c07902c0b500d80d4a900d01401c0c071782460350048840b59207080400c1c008100c3c02d20b50300e82c10a1101018404000c58100070f6030808016600c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 608891699 1250 608890449 608890453
    0x1207082401090902071109010e060303040b0d09080a030b1306050f0d0503070209040c1d070806010305070c020a15080c12040206070503040e01181428090b04030c410f 73
    0x400305c100800324503d50140d14045a0303144199881382e100c4001d900c0300b6a0f2041e0305a100f080100301440392900680046030f0203100024403a00161030f15111940b1910030b200010b0303941c2d5820941441d1184000640342c4210000b00b10700e40c180008144140d00c04030b54548201c0518000200300310b030400844402640c060041801803d1a2620f40b21500702c40c01106852651440101c0c4840c4109118520441c072950f600002900c0e1280154000c03c0090700030402c02c52039000f010701580350080d03824002e208001a075041c95400360300c01401100080e04c400c00705d500c1001582400020300c06c090313800540485181e5691800c03481d02515500c038690180c42d01d16100c000000790503d06550030401425414030600c8241b800320807280c40e1102c1112041451807080c0ca014100f040d06056019020002c40400a0300300c45541724044d2090044801710001002c02e080c40c0204007010072109042550203403419115480908040e60f4000e80e64081050602042103540c203104042100d040701c0b03031003501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 608892949 1250 608891699 608891707
    0x190f0204120b040b0906040b010e061804200a080c15040e0f01090c02030c120d1e091217010513020f0304060b0415030503040909060e0d03021207082401090902 70
    0x6001200b40d0011501541c0c030a05810016450241c00b1904a20a66005000403140d03802c10500303031140c0c800681410b801c00404038000d0201e004104180c1e004501407080c03800d640304149840491841c00020b0b0318018000510f0420031003800040c80340c1d0340c0c002110000116030000517480300f81d001c0c5074003c0070042c5080e0103000c0b0301c01402682e6810b03a020a2014000360f854050140d80d280b0400c101c4000d640d010386582d40035403d107003016201001106c3c00104200d0a6941d910b00310b10b03050414008040d13541e011240c02c01200d4403000d0044102c6060500454040c0340b20026a14014441c0710300800e042c0054a034801a583e0403a002140b0b4001100e1326070034281802c00080c500c22500c0c601079403400c8401c441c0b000001080c182200d600100452810703007040100300151410300000c031480d41c1c0382c0694540305a0144111b41c40c11015550058031580343d2034105000c444090310303070740c10b000b852802d110041c0c40c40d1412880780c01d218800755201200300c030012541c188081c0d00c8400304d01e00c042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 608894199 1250 608892949 608892953
    0x507080703030905160521030f0d06150207081504020f06030f071706060403110d0b0c070507060f0903080a12110c01050c0306091602120d02040914190f020412 70
    0x150203007010f01e0181c805c94441c20450383d2141044030b0701c3c2c05100e611051009100641d500c1380030a25403802c1d201e005a908104200c559006983c1007501115515910f4003001d1004600402a04e5200900c1d072004102e2280ba1001c241c2d142c21040d00f4108050b1060000074095413105138075600001c101500c0345969241807031054000f03020640d05480068220600c2801e03c1140800040c0103410003048185094a182d45e00c0748141c03100004107401100ba8030384100815050303025140300d0080c41d80c942e5510020303440e00f00d092406c00d070000707824400007001c000f040a80c4909000140c990114403541e0b1100d84034400c0d21a800401001500182004207048178110010003805958515000900c402e0b02ca00c00d000069020448055412540c034400040a88240c805001005c1d161401607900f10175101000203400d5001c1034413010580d1700014200414411445a20141c04411a40320b0560401d0841c7d20b4155000d030801701515034a1f18984401c0403d030303604503001080d01c2c070512a1410228 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 608895449 1250 608894199 608894201
    0x6070f0c0513020c0d110705100e100f1b030813060e0607021606020f030306150f0301080d09121203110f0c0a020f030a032c060a0801030b060604030201020a060b01050708070303 78
    0x5002c000b080340101c03a03292240c5d13405034401c454403d854001504046003840e00380084031504010356420480c1c021080c02c4142c850000e24203404010b559040041101d00001801c04180355544141c00442d141d0344d6804240d000040c103800c10010f407030390300405120b030070310b0009441c00c2d030f20300c960500622043c054525000a194200780d003041c03d5150070075694850580e25425200501d980359041080041c8280c980030807010122001070120034141703c0c40c01d4040c84140c000345c003c1401940410351500c00396401c0001a0300402826200380392004003a03444e14950b0041c105010180754848600300c5180100c00c0585582d0541d0f040455107440c1c4804000b80e80c1d22041106902882804c40d00c66980c1c02e010910480c165016101c001241c80b29807440042c6091030700507858920640d1000501550f200001070400150950b9103000e01c0d41135080c0400c00c81d1029020340d07c210b10030001000140d0300826020074a0360800341c005001c0c404080107075118465964021702c41e0400040c408201901 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 608896699 1250 608895449 608895457
    0x11512021317070b0d09080f07060504030305060d050a020d080903010915050a0b0a03030509060d0603110406060302180f030114091b031603060903020a021207031104020906070f0c051302 82
    0x1030b14012150980101e01040d46500340d83c0103011800c1c204002d000b80c1c00707640d0341004000e5480340020520302400107071082e8450b0840b01c0c04540103900c0b1802e100030305a042c003075142c101d80c00716141c860440003681c8a555802035114000c0c0100d1030314448200b444031440c181c84080350040d000f88000350b0300c0d1030648a10310580625041c8541f4050120f1005001441003461150000d80b80074502400e5450a0f078054001e00205540030b64200031511080d1f0040c06007800551151603000019080c030310801080d076a098000504262050280c59400e500c041ca001c03452010640d82c031103030140c0c0c1e40b003c680036040310b064079880e24000000348081c004000960b40040003d0800e0042004991001c140e12905940340500e120b9031a00400d20220701c04d9404400c55601c00d00413140e242086901003500c45100004403509070b00082410010f010b07501604130b41c01842100d04603c0e0802300c030005100743c01484c1010f0841c003860203043d400c020324200a000a81001059403281109020205000e980 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 608897949 1250 608896699 608896709
    0x1b0f08010c0215060109030221030f09032e0e01061214061506030a0e011b11010b031501210602120105040e03070302120d06050607080901020d0c0b0115120213 70
    0x4209498051050f94000569026030780513540c03c06103038619020820a06d11a07140e40d0b0744018100d200420100f8100000d00e8042080000303241c0301c11418040609202d2a0403618012501404a060509280100c48817240364983c40000e90b140b441d5100500504070358200201d40303c000d000e00410301503920802c805e046155400c03140340341da901118069100b0103141442d00301d107082c00411220000b680201d14840d0007500000b075811580f000c1d000c00b40061410036804030307110000a442e8800d084c02510780301c0381c0a5006010f280000c24900513003071b00500c200784003c5041001800380d51220070241000542000d4155100c041403003808026850038030a0601c01e901d040e0b00c00040c404040240e904c45501900030317000c1e404a107298070346d541e40a651103241c05d541da110081900c1c2e68100c083c2c40c4140c081c45e4020b4544513803100180c584902c910000c0f051203001000c2e1800034885074041b07415511541e201e551a10043c900036200c0c202d41804440e50076002240b041415140d000c048000c0720 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 608899199 1250 608897949 608897953
    0x1308030d060f06020d0f110a0b06090a2a020f03043206070b1b07081306020111220302060408160605030601020a0b090c03010e07060f03060605071b0f08010c02 70
    0x9950302e4040c00c0c007580e5031046402681003003000300c240d039008848884002e0f40c81c1c148440b1400260356400d09040100104541c0d484108003488490708124103002c1e40410003081c01c008100c181d04102031480813036020607044645420042103454800c0c480c2280c810141d0080701d4640b5100e600f1884c10319803c0b02c030b030708400d90a0b40c1c1c81010307a41c1c4803031a18800300c000341c0024030f0605c0d41d443d80c0310413a1000b03010f841c0c1860300400c0020f02e104104014400c9502a40c686901d9019003e00081444941e0b40554216030500c0c03000700e4480012000c41c0e224026540c10342c0c10340c1490100204104a00d0f60001e0b5100d103010800244103003001c0b038141c4040e43c0d03526030021074645904041d2150b0000342d500c0c5005130f02c60100d000c00552007516094110401d5403ca8100e0040341002a007500e03210500540c032604448020000e403604281e4090108035141000c2c09520304000d8024114006c4010241412080305906501c40f90075a0050b801b030a150660301c810390351030b080c4c40c0340a0500b05031200018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 608900449 1250 608899199 608899211
    0x6061706160819020d0e0d0201020d20030601180816030b0703140c0c030409050705120903030f0a0f021902010c09061404060e1302030907030c0905090705151308030d 73
    0x802e2082c5642841506030700e0001c000603240c00d030300c07100035001107a506404d25540c611000b82d03c0d038208406038000c0140d0340003590702c04040107c041681c20705018800c3c2031300c01d942c5c804103108000701a80d0340b01c3d1017032a01c5c4075001056000e01c0d611204640c00807646000b0840d6a4a940b44000061000c1c1c0b80101c680d6082034480c402c0c01c40031600181c2000c580d501e11780011a460441c8031000b0020a91000e08403400d054450b01944222003041d100c0ea00840d0000a601c0120001d200c000d940c41491a000b45081d80f424501c400108140205008045960703840010682016541920301c044042600c211003503070743d100d0181c000c007a0805d1f4400801c502c4140092050f10400011411407104000300782072614111007070b10344035401c00d06c4540c00303010300d460301c0414011031000c0c6115000c054010803a440c03a604040c040d80c0956005000118106000c00200d20000245142100e01c2aa00304400780c2d000424088140201d081120342e01c40c10f0400022081030000c003906032080381d107500b0014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 608901699 1250 608900449 608900491
    0x14030901110c030c040c1211070501050f150103090303060b03161b170304061107051501320f06130f09020a0c030c02011403040f110f011b06061706 65
    0x142d40d140d1004542d1640c4078440803202d50509030810804500c1500b810218004483e10440a680010b070241c10520008200c64060040c02d005032900080c218401050908020030124156654010002c1c10b00d615a0282002c151080d4421001000c427146081d80b203003007200304041201c0f00614030b4000507107015901407a0302856010114415407000c0191080071a200717035650107400042054a82c903640c0c3c041820200031140007000d9a9110f8800341c03240070122800b0710050745041e08420300350b800543c19200c00107031054411444074944050492055030b45c1d8000303490b840c070043d0a1a089440800d103501513460f00c0794028140c0f070107140011380032600c03a0105000c90141902c03048c00100c0c82004000071a01507030b24214040c2c01894200e42c0561001103241c66a030080c2c03811210101034812407024024406d081c505813881c01c0b43d8040409540d980020304a1200c40c0f00250300840c00445941008402e52102005201c050143d40001d60900482d41d101d8408440e52a82511000700800c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 608902949 1250 608901699 608901703
    0x20102070f08030702131b090e15010503041103100c0e0306011706070f0c02030d0804111504150c0b0703091203061d0711070e1f0b07060e07031403090111 68
    0x9030385450b03000b5030070300155800b00000300c0d402449000381d065480b94209266078814180c0c01c410f480c0c1e51200705903580b900076a502c2e0000f005110407101400215903c0690b03a03c041202e03005a008000c60a140c0032a8001901b40740340c0c44403605100303103010000c0e00815001a403007809500c045040d1007039686c1c0d8841041c0c806425031a81da91a801800006a92901070900400441e0310361900078500d9240303601091030070b030640f480309000c40c18000c100003c0006a5000b1050350505840c0c0a40b6821225694005802a4004c4054a030f1403c1146407280e44a030307490080c134940003401002d803403d2804d0f0290042180c2002610b17030414203090340700114024042e07141141c050110220800d01e402800800500307014201100700495040d040e80303544000c01800000e071080c0e5446001c81e06184c13002140384408003040c1c81745a6813605081041d440808103a98002e6006040460420500e403070341804c02070941c100504500041000d8100711900002402484000f80c07111880e031141c006a0799 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 608904199 1250 608902949 608902979
    0x621020702150703021905070f0b0a02120904021303060c03060e10060e0609120115080a0312090804080a120e01030501051e041b031a240f070c030303020702010207 72
    0x41d41100b01003100003802110380300107009940c020300c1a10041408461620b514804065003514642d105640c10310512800302d0403280145030812000d1300d07090300702e81d01948440c02040e64091403000032615100c10b840f50740440d1a03a414600c1d4400c0c1d400d0b12482c0280c0100303204015000003030316003203012404103c00c48407030340110034080b4000403880c901101191070360981601517801c00c0f014010340c0000d84500d17004820b0111020b0000c10001c00008000600c1016588004019401901c107580820f4020903107462901042d80d0208900700b96090103001441164445031a07881414010002c2c855050756505c0b4000301a03507111202404d403801101552028080c907540144d8081c81420045003600c540500e82602030004100310b040140d4500d04000d1140c440b6010039261003040031480030f440303d8140307004c0c0b0403240a401c1c8182c209403030b844120060010001c500000506c2d0301103074401c6003a9030566601100300b0300015200d140040194100403400c9000d03105010020541c524000550 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 608905449 1250 608904199 608904203
    0x1a01030213090201050f07050d27031b0807060203040603050f1e0601020f010203071713051903020709091a06040c02061501031b0206090d050c030304030e040e010606210207 76
    0x5078045014030000b00103034401203051013801c110103046040101c3c0504402c0b8054400780c150ba0541141c0030f0304405525480322414103003d1162451150960425400d0341d40002c0c034500c894203080c1083e101e20042c0d802903180c61003000000141540e0010080055400665091040740c561540303640c00114180c80d081041001c036035015100c1012a80541e60114051045443c010b1040c3c3c0303014220b90003607542000088186107058688042c070345581e170304225840480d102c0c19000e9110152030741c5034980d5416841d4103403c504428148204140000b600d10078008004803130b403e10701254440ca2020244680101c1c1c00006903c0349014852102d002019401410541c0d4a2110206019480100032410b02d5a0303030480c884a50140b0410440b090f065400a00e0541426070501d850071031048901c0e420444204000718504202000b6a81c0090381803e05200203005c003c001030182101d20801112503290100005049074407840e500169444007004d80f40040740029100e091388204400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 608906699 1250 608905449 608905459
    0x6070f0c030e010509011704050d1b08180a030b0106030f05010504021e09190e0105030f0a050a02010c14060f15010e06160809060f03090706080f060d0611161a010302 73
    0x280e51055000c4c40c002c1201c4001491b00760b500031000c070f03118601858161402d46195001e2840560310903003104803440d4000c80344503003550483c920740e1202c08074400ca0460607054105c41040c01c2d01c0da19080384440c081d55115106101075a15002c00400170075060035904415410440001041e04040c8204d5098020442001d507800d04112076aa00c55404041c80b1a0030a240d00302c0001700c0100311121138090174030070400302540d5243c08109440c0011414807201030350001c507512800940c000840003062030313083c2020791031407919082149446031340c911060140d01404080140003180c1e0b43c0614880c00001c0d826081c000744038001192085481d1000c503030804400c00c22010641c04c0003c621007030070711400783c00c0d1034007480b200494020742024100103400381c0302105000e5032020510400e4050b102c28a0502c0a03031410a400e2220640701604480c09880d400d8443c1c418085990080c0700688801001c480d900d54032802c0001d0083c100600c156030100981e4020700b4440790440d44c1c0f0f0304036500102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 608907949 1250 608906699 608906717
    0x150e060c19030e1603080c06061f030c051902010903020607180506031f03031206080a110409060b100f030509030414101b030305040b06030f030a0e0a1706070f0c03 72
    0x78058008000305048048188038118405049060070302c031002c05103109680300c54441c110a00358520703000020b00014800c80860440e00c900584c80100c0d001a00d555240114020a0003072060f10030b440343c90410003000b054804d07600c4103140c0540218143d28030960848030365607030322034045030581e000048618250420042c100510301c0c0c60305c05150003141302c1d100b6907901e65540c07041d5004442254411408585c0700d402c0c01d038034121345102e00001043d19402400c00c5821a54a41200554414003184507655400401d001c0c0082c581c800707442c407040a4404007010072400006072044101c850a02e00107800c0c00d0000e03e1740b01d40803064808852145414205508543c010032000d20b100c414403101700b1080082480c00c402038100501c814078002c0d14000f41d40c1c242400c00f18810200145500c1c003a5114003042000d030320340041181c1c220034161400e007048425240c0007a0890a007603000c1d040c800a0b502c2e6004c1041004540280030b41a152a28008001c140c00c0c1640c40a48080002e40841d0f042d0b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 608909199 1250 608907949 608907997
    0x906011e0e04140603060106020f0a1e051f0b060909040f02060d020307120b03031204061e090503120105011403060105180306070909060801062102040603150e060c 72
    0x100081101411410800041907410000c00c080302c0f1000480c001c10030700740301445640c2c1000d211407400751006202a16030240c13650b04c1c460f62404541401407842d00c01c1421b03040b080303c5005c030340c50303c1c40d50200c107441e000c040c41e080d03480b1703000c211001007031002e4940062030381c49242120464000440140c0503035004d0399183c940b04160b17401388900382e82214080100a02480301840190302c500b09980b900694001c421180c1400c44012944160084d881000700c2040d2a040749049640142e0106000c00c00c1174400800904034400c4944180c081418149658200300e03021000e8070f0340c540c106845142d90380c0c2c3c45004460503030141c26011800c2d1002c0001c2003595210f08002d14906082c8800399690514400101e45410412502a03001401d101c1040c480b01a09025036030040010900a102240c01c4c08032010340c898228246185034440072455030110748484e00008003c5811200680c28800c00b203e844001c1d0944010b094154041e442c0010103255090058400139042c943e218802c440d281 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 608910449 1250 608909199 608909237
    0x4180f1512020f19030302010e0705060403030e040507050c0a0b1503070e010306020702011808030d0615200a0501090b0a0c081e04060b030322150507120c2f090601 72
    0x7100030f15800200203038040d0003440300c60105200030340c401d6000082c0c0e0b105240045082c89901e81040d44207002c01c00041004c268004503c4444401c01ca80c006520744404105990358403668010701c20350301410090030207018081030914401c00492540407002440c503002c041c0c65109074020b251128000340c0041c4082181503000c1c0000c18810f043c41000a139441481d4865500981c1c4040c0300e9a1001800751401c0d0b8140c003851004020ba483d15401004800c0b1b00a0088100942180d09100602e8910070f2183d0040080811a9410100030040003280c1e05100c2c1241404032118800c040c01d03d0102d02a0303c0c07150030141c1c41840d010403c4013401100d02103107800b000018100b07035034040e185c0350030b446c0d155000d100a003040e044011494020b0f500140300f0880701c480a40c0110881001040c003081110b400500301c038544e030f03440403a40307520307211258054503002000600a480403c2e0700b007014271b40c4280c4668012b064800315440c081121040d80c00c2020a4400311002c90008414010035803035440381c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 608911699 1250 608910449 608910469
    0xc030b030c0f151303050303040b0108100c140d0f0f060614190c082b140417030702160b0405013209030a0203030c10051602150c04180f151202 63
    0x20b007001313840711a07960340c41c0c4a1860308161402e40d40840ba0303100402a40f90100080010304084940c00d1007101c1c1d42281c0a041c81c0000c0019005107140003405030361000f141d5100c0038100400000801c03d407220301c0130107801001c06026200100b9a0f0740c4000c0a52484281500c80750078840c0b01c00d082c42c818000d1b08030390880302c5a2003155402c0c07003404080580c0200b0b4070000b10a4101021a140c5c01d480c001c144404d5545802911000700854018480403509508005911054595926a1300d44801c81c0492624680d030040c003040c0780301c050001c51440c0341c1c41c0051044600076610604880c81540c00e4000005c00d1660800c0b40c142101c81920041c084c0c640505902c06001341a503495040980201c0d0855128048130045078100c1c100300c0c011020240700383c1c0e811001c0300e02170b500f28425a68002c0c1d038402c01d1a0041d400e0466001c0001c8803c0d916070104d074042c01060000c2c9070303c03400c2404400e01400ea42064501c140b13040000e2152548905010722048072078110009c41c0500040c3c0a000c10541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 608912949 1250 608911699 608911717
    0x105070b010b07170307030f06051009120c050a030b061503010503060601111f05011a0a020d05181507030201050a0b0f040f060b0f0a021011180d05010c030b030c0f15 73
    0x80180401c9404220131405035114400a45000c0b030392000442080040fa0826049148180d203c0c02c2490042580581603800f50fa03005030060000324100c0c1042060700b51544d2040c0c1d40300c1074154004c0104030340f5207846405440c054480d0000401021010221070000f40915905503004500041d920340c424140814610128001c0d02c006001c0c1011590385001d014010a05844d2074500402c880843c038040d4903a001007614500f81007000c07002c0029141c038908112141004001700300340c0c1c0388540d00c0c0081d008107200204801d21003014003004070815006001c00346e01551914001606081351070154011003040203080c00c295241c1007003008010042c0782084016155584000b269940301d58008010602c290b010403a15030344c200000a00d44203620045044050034091001c5040d603400060369070f14554031940518412002c0d000c81c82c0c84205c9480981690301b043d48880d03103c0e4059000340403040e015416101b080b501401807100030f2858604864010707000c28840742c810300f1000041e050f00c0c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 608914199 1250 608912949 608912963
    0x90810181b03060515031e0c09100b0403120f09060906050a12020a050910031416030b030607030f0b01080f04080903070b070503030115080f01152c0f0105070b010b07 73
    0xd502c0782c490b40d00302c0300704450180f100b551004240500746010010f54601841010840c8281d158200c4a103840750b00f40f80046000e00032203c08034904240021800014002e88800551225a203081c0103142e8074180010300c010803002c18820007400d1144070035006540481d100c854116181120403100c075444852401d041141d140255085600e981c0010051000140e03106903c513075290082007030406440f44400e09051418200340b41401420524951041181c0f15070208442070300e0054009c3d002c400d000c0ea41c0b40c026981080074803a0903901000740400006001c0140d01c60800c01514061000e403000107030802036030b000400046e05c01000b0558010003070f003514205641ca0f03400d940b2582100c0ea080705c05800110050000c06000350800210f0f01c07035032a1100e040d0504010f40c2c00fa004040c060b81c030300054407d0700d942e0317558024000414a0401c1c1d045c8071040c000010800110746070804401d521500903113142c420103600c2003050300c42040d0040c0748140e03103900e89210200e1540c41440119201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 608915449 1250 608914199 608914253
    0x90a020706180c0803131a070218010e07050f19020c0603010e1f05061b010236030a201804080901020c1c030804021201020a09081018 59
    0x40c0c480c09444040d142d200c911070040085441c003d240a0b2071070304040410b600a0050000892110040000700c4500308201032080301c9041d580700740c501c034031400030b5000210058500e0071400010342241c100d07451150307400800d880b480070407070341413146400503944a04103008907046914800c0c42c90315007980e940103d5001c0e00041000c0785041e08241d0000c0c115181020401401003040c80042134032a0004401d903a6050800d400a02180505010300c1c003200000800d1720051602507040720302c0c00300e55580d40c16031100d50020200503051014032015003508203101e4071180f030900003410744480381d2260004680901d202c4044015000259100707500213400e00007400c0c0103885c10320740c90080c4e020715001a514070b000800689030003140d43c85280182c2140c9003041c441e106803225282100da0603d0028200d49490000032950f248071904034610b03500c00114520300f03642000710359041326134480540e0540084110108210303803481480d202d0a003068840d503c001451038254650074650002aa0740c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 608916699 1250 608915449 608915453
    0x106270510020d021b013501140a0e040b0f0403050d0c050705010c0e1e0604050a0e0105090c0c06160c05010e0d0225060305060109090c0509120f0a02090a0207 70
    0x9500400d94540c0035800c12410789800f144d0500c009000c600703443c040b1500c01504880000e049140c00f200d100b2260300e0740354981400c4040f041c071242c1c44184520003840d15507121625601c01c0382c001d1181c0b6208142e12400065103403801280d01e0310481e0003030921240d943c1d500801146220006200320308019041040c092030546a204d031a1600c0e401e507980540351409071410703034211588411002f060000a06036406140d4481c05001040800f0028058640c000400850698000d07600020345c0004d08490110303e00001529090417542c04a5108083d40c0b988070054101d40b2038040741c4405a00420002440b5800400811802c012180340600401000b03848144c00c4030801902c01d2003681090400c4480c003907041100700051050041e4a020481041d60714100c510428401c050525480320002013050f8050391380b94001740a0000c0500c080940e803032000707100b944000c2d00d95200d404038440040d143d28000807115140c40d0320f10010985240b140c0c08010f1001c100501900d4625000c000c1140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 608917949 1250 608916699 608916709
    0x1d060d0903090f1d010803160303020a021e0109051c050a08061c060603020907050a02030d05060a030c030b10120b0406320108060f090718140c091801062705 69
    0x10042c2403a180520448440341c0b0780c04400201031384200e596507c2031040d1941c421a4840030300000c0d9041c200107a075200c1c0c0080607410124620001501d00d40c9400d04044080010341080142510542c25035041c0c3d002c1018081902005008160010ba0113201c00e0761502e00035441203400c00e800821064a40056200d1a4001c9510f81401c5a071562101d4041046003001c075503054000c2100d050080c2007804080d002503170b9004011860801c5602c030360200f5510b803078090040c0091a00820840c1c07600e6140d06001c0709014003a51340010f060036503880020a000092010790f861070340702c0c000704140c0d1a0b0741c075004040c0400d00d125141d4844140501d81c480c5200030700c1d03a103243c1000742442d042034bc0f4114584e0f05080740207000050402c1b4400401034016400314044044d9481c111050341e05484240d080002440082c40c04a4010400014091082171102c0508480d1000700d03404240c0622110700e0482200c000c4c4204000b03d18128208107410810290348189803108115600d0350a5403580054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 608919199 1250 608917949 608917979
    0x2406011e0f020319021e060c07170f130e010e01150302130f0810060e0606070209130813030b09010912050903010b0a06030501260a060c03020d05070206071d060d090309 74
    0x1005a40030080410f07404c103403106d80d410007141102c040e0905107050389051100d0f110300280103040d850310100b184c51001845090350b0204e15101c00407910f441c071324000c41306d0710452805803032a1840c4407000003076024140d84065049e91900018032540340094201640a07400941107001c5640c0d15070004a00b00d03292801203c0141200301c020421405504260400c6418a03000103240003d60000c000f500c1c4c03521411100389540c1034510306002c0d510503444002800710080024914a000500f43c85030701c03827080c0140103503402034041180603111481c00e10300325440c3d50002480d2100c2488070b5001140290084d001850024001040034004a800108644c1360b5800c48408a6075810042c0b200c1003494a0525200280c02d00e0108040c0444081d150b030343e81590300040150703449403404601548650155040c8040c298001d00042c109080040c3d1203540c115600c0300064000c4601c881c3c00d081c150b41c0e6000d14040501491b240180e03148450003e060103480903800c2c88084a00007841c800012054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 608920449 1250 608919199 608919247
    0x5040f0f031e0315140d111c26030702071e1206020a020d180b07080405180f0a090b040206070201051209061006030b01200f2406011e0f0203 62
    0xd5046440801030110003142c5c200b910381c0c51141c0c0c084c1c07566407151a24482e043c0d42180d1a0903113102114001044c0c140d15903800c60300044070440460421130301e00c0c10a10820304090800441ca00c0781c08071000a4001141c446006034002d04042201441604481300702100b858054480c058030342c102c0303620039080348600700c0300c9035030000781c80e0344156060103210380380842c620301945021500d0113800b4080816000b0341d04078210000c6e0b20410410208100c7e002080043d0901011061603a90725000070011119181c540f058540000c89540c694400d0343c0d605648184042655140c40e0240100358026000c100e041c000100f01c0e0040c00055080490b100d00c04243c0240041c0c034000180181c6481c3c103500000a160034082660102d82e0041d556800c00041c803a030713030810300329540c2016261068100c0403500705d008544a42c455400440010180e50380c00d420011130b5900e4031801100d81000005000021007048084846c5591065030791140c0c400c5148100c03420514024840b02840d2003e40e10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 608921699 1250 608920449 608920451
    0x813030e0402072319141903020a060f05091e0a0b01030f0314030f0c07060b04020a02070504051006020a02060c28290c070c09020d060503060a05040f0f031e03 70
    0x240142120f102a041e0300d842004c40d0151804010b9991070b0381620380d0b41d20000f0642c55004402003102641000240301510b07003060760b03c04408003410040d469a100410640303a8600340210440c40345c809009860003001204028005104517803041a000c070b6085003d11240d0044100c001e01203012400064069030182444490010721441d01605c0e01808d600301031000c400030b004100c5082d18518116a002c1c00026105070b48403880c0c0307440801080201c14295110303101140700d842c45680040c402080c1c5605840800c116101e0031100c16680f0b900340300751b80040c0c0c843e181030710050a160018041c2c18001000715001c075040c4400d05040c00000a442c10403092146502105000160307050710000200c1d81c1d09142142d65905800c425600010400d03045001d0010740350041106c000082001021809404c54844010054520203408248103d501c80e1080d14003103540e01c0c0703039031084600a030317070001043d01c810007240e03907440c428458030005030144101c00980c9001466010000204044c02e0b6034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 608922949 1250 608921699 608921723
    0xc030605121c081005040c02030702030115090e0f06060d020612010902070b0c0307141303050f211821010903030507020f010c091205030c0708030a0f0f0813030e040207 74
    0x34040c0b4400301500d40000070003900710140314242040d0201c48080d5a07080d20040350310f920ba07180a0780b4520401c02c000b5015132803c510700000255000c007030030959180440c1031018098100c5101e0391207548581d411100e800032000f007141860316903c09007200c3d1018120030f08201202c0e203111441c2201360320480f0351179000170344001044040d80c0d4040e844581c1441c01425070a00c004000d0000c91850350340c002240000070000344207118040c41e6002154000c00321480c0030b90300c105180c2c84030080d210708403940100302c0303403281c009060505640045115007007407051380003c0c0c01008103062000c0300c3e5417401d00c1c40141e03520f401c040c00e0062034016806030328081681d0500c21402803800005491058281e490028040c0d0000c0d8000d10201c11540c10071042903110b9400e0800908600c07a8030354910700c07032185203c001110540440034104c4001680c0f2485284c0191500541e411340385040c00340300060300040040c0799440d0860009501ca030003441d102c0c0c4c007182c40701c0104080740d0110034292010b441801c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 608924199 1250 608922949 608922973
    0x50402030d05041202090a020f13080d0f05030c070303180b06090a06060507080d0f0e06011e0f060c060b100e030606030a020f0d06150b0712021b01030c03060512 71
    0x4000940300301e0030719010386414904001c0c02494000524001e120ba881800461140c8a0300d806540c0b54003590074442e651121001282e02c0c2048291080b02624065503400358441c42c001e0002450701140760316003d01d1075130b41c103042400b103900000d403c406040d5981d00043d2400c5100c01d078400c4151140320152940d0030030004021080200411100c1450300b444001e0090b01d40c00015907a81c503900001d030580b01d044501c2c1d0709020b005000100403940d07240080c002d900920005680c1d04aa08000e403040c50840904480d845030b038802c0c000d685d81c204070001c040060030300c03d802481c0e185028810000d14101d900700000c40503508072a07034000080d03680341000d01c02e20f414001e65402c42001c80c014004d69100354049280700198800c9a8442c01500000c0070510808d500410540c0400c4440008095140c00451906400c841808d6a5002070903881010107800050103108058220042903080d43c1040c00440c080c2078102d00c000201507d070030000034a911210351b5420b0055800d006002200e00c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 608925449 1250 608924199 608924203
    0x120f04090b0a0503120d0e01020a08071202070c21050706090504060b0711010806031c0807080a0c08011710181e08030604150e040506070815031f0b060a0305040203 72
    0x5030801500c01c403000d40e01000a540c0020717480701000840790744c954640c2c0004400c00d0081c40140176035205e0b540001040345003d030b88003410328401c00a41c0c0312081e40c540c08400382030481c01108001000203601030414080382c00b0300c1c1034590f1101014801c084042a41d0742e25941000d145900050101740b4081b4203010519060045001030301d100701403981404495200c1054420f54000c800341880946000b041d0741d510b080c00500c1c0d901c400034180e01e240c2e000008000300701820444403540042c420002140340082d4600501e5100d013141d0f0b42e9002e00b81d0800c02c500504140841c00e402c1d081c82060b800d19041e81e2580140401d1005041109940302498180840d030143d020070501006222900c184001548100589030804400c0d98002a144c00c0c0600c1c0c060030303129a40011202d04000c9003000100700300010890303c11a25507403040419200c33140b050320008200c2620390781c544c012000300c0705890103032018012056501c3e080400c4900a94000c540c0550001d03600301700081d260000c01c000d600302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 608926699 1250 608925449 608925461
    0x6021c0902120109050c040b060909010f060306050402030705030f060a080f0715030501080a11010201111612030b0105070312090c1203020f0d0e0103050402010e130903030b0301180b09120f0409 85
    0x1501c2c001d004114180e074a0a07205d20b5152030041c410796484004608680301d0100340c8050316006801a822075858500d940002162072060000081c101040414141094026030b8001e413241e440303182c11a1258204003003501030060405400c50074a035400907003104100040f60746051601c02400655003008070781920703268992201001d05040c20700400080b00001442107206410039601c1064410010040313000d4030402c0c0750304401503004510440316113a014140640380703100380000c841f154040d030b0b41a030035200d0807000140451020700c40540032a0040c403103036404030854040061510081c3c0d6a8400d001c5507a0852110340e503440d21a0740401d90100082c001c0702d1101c3c8014054184503043c018100702c4050380844c1096100e6012604690003500c2100d08844010040301d000c0c061507680070f0040010250a400003070400b80030b001e4a04040c440d07851603800164850801d8191234680081240303003c1c0c000074452181e0980121f4a86a51000d0a15019464151641c881c5000c55400a80749 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 608927949 1250 608926699 608926729
    0x50d0209220222030c05010825030b130605060f07080403050703030e010215060307051210050103060c1202041d1e0411010e010503060a06081003050f0a0203070f030b060103020706021c0902 83
    0x4403401044c40811022000f12080340c509280240060380e401031107003404101918a41c42c11a0b0480e00005080e0f0942c010207050881516103201d00f2030100040c9054a495104958014104024071014110040000c1c80407600400d103880c9019560340c0c48078a8440749a0007035000454131900841c1da0742c0d050041e000c924825000a40752030411000088d15449580714203481284030140503a5511400d0090716602c0007004070401c03035580e41f4102040036050101c08031002603400c54402d055080ca9109407415982080303040140800003641d605440c241c00303880c2040c2007058880340d05000c01407003489031082d403140303a000c412051010300141c020b000201c802c50602c20309000b0030070540c490030182411034a8a00d0302c0019900c0d110081c80c04a5101d40000c0c1c414044c924021491180000e0740c11901803081d02102c0c965542e40c2c41d204019109400300501c5004a60049413581d8401c0d0060705d582401494014500458043c9008030300700000a0004007640304c05100d800d502e0700c0034001481034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 608929199 1250 608927949 608928007
    0x14031006110313140a120b012c010302040207050c19090501050906011d19080109050f0303040c03030c031715041109030304030b1b040806100b040501050d02092202 72
    0x211a183c0c12200d8403840c0501445019100344000096503000e03014001409240d034260001e00c40f80c102114096405d000e0686800c4c6540c0c11540c03441d01c0200e48101ca0b40c00001c1d003082e142d00303543c2000083c2d481840c050742c5c1c40c441d8441400302c6503110050804a80c1c0c86201c1c804da044c0c900714089099500c1640101c0c03140c0c41c1a0104000c50740c00415000886000c448064289c692220005050001c0d23700c2c2441e0048400f8008500382c00154440c00320107000d101100e0058200c07420043e5a840700303c400505d001f0711042c040000a00404218034014400d0030b0011425851041140c500d60040341c40420012810b040e60700e040c10140b10786032918201010651400c66440c0100c0d07030302c3c859484001c15812400c0d000404000050388840c400d01d01c022402c3e0340d5566142001e271b03580d003400d0300c4030000758103280000510b1100d6042200d0441e001a112182040d0340c00070140001d4006020741600b0519040e81088136911668490300c1c50f000703440b00184c846054600d0445000070341c071000f134420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 608930449 1250 608929199 608929207
    0x706020f0414040204031707060f0f0209090114031f0b1903030f09030206190309020303070f0c120c06082e090f02120a09170c0703110907080a020901140310061103 72
    0x2040014100c0910701c1f0103042c686a8400d40745c50f002000340100c101504480e4945075800c410b0203c10740040c408004216801e05080e40c90b0301031455800d0b604c0391b4413507240c0d101007041503512075a1448800c00c100b560000064495000d8081400a15014005000880c20903820700c109500117694144991080c54152070b1581181c1c08280c951048081d072066494612180c100b00b240b080d0040c8440c10343c0502644c1e01c60707100f880c0951100c082c2035000c43d014034201101182c801c0b280000940036030380000a051103a40340ca070069501c1c40c000380c440311a0001c20004c00210b06c07030400c107100c51000c0c0081d0807002140b50601200498840c444282051401045000410045104556082107c5190000b8034a4203032500c06101c8440d600300120385540031503d080508400f0960b9000c49002c2e070f009001c68014842080410030040758410007107407502011600c3d0003450740c0504011101070501c540c46800321201080c9a07001154103c03403c00c1800d00602549500007150005104504019810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 608931699 1250 608930449 608930453
    0x3050a140105010e040e160503060f0c180d05061e340203070b10210f26180f0409080409090201030209040513140c150c01020706020f041404020403 65
    0x100e00341841282d04201d140110415613030b440f54099402000340c401200c408000e4001c7d0042d24040c1ca215061181c00b2b841d0018007210174441c0c6591160056401d81440e02d89110710207201c80009406441d00042080070103000a80200525402808413094482281d110116400f032440346c001c4c12444c00e03100703011264a0b40c0c2c4c41c485401c200380228a00105100840c040128514003507010050300071030a003001c2c8414488121110410341d10301c110380304106441184405151030b55050010151104003000d400890790190300060000403403c1010501c40000c0303052a21a080b00c2455000e000748620000c500385496940c0f1710f9111000d4409026001050310f405503603001c0c0b44100c0c00c0c02911440e000c0c045a2203907048458000004004008034100140800c08904900c00100c85886010203003034a99200080d800050840c01440c5c4890b00c00703800c46002594100e511203500d20364080c80400001841070025040e4401e04904290300c0c1d500c1c10a501c0c0e0109102c0180b90300540c03041200f400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 608932949 1250 608931699 608931731
    0x2150a0605120c09162f0102040b18010810030f020a0504020f0424020a1202030f0a0f03230601030903030b040c020f0634050c01050a05240a0e0c070c1503050a 70
    0x1061903103885074800891b8405040b2507000d85d440c1c1c0050510b500c009004075240301800003070b001101c460391580c4455688500195011901600c412504d40340c15602000041c001301500c546162000c0d164010250381c501c089400d0741c10600c1d200c518000b020400f40a0410792a050303104034440300035a401a0040b0000c080c2d11102018000f4001408042140c2c41c041c2c000c0080b220786012010b20603550b592a9076000b05492983d490000000b420004140da180189040c81019039134081a482c036940c8400d80158000e00501c24100c0130b06403a08084003a960707803841030081c1c0d540303183c0181c0200500c0c0c034205401d1100083c4603289003080c0130040400c03840b000704070884000a08140c84440c80b0368420a54042c052861045415070a08003004915070490300b0140c0a504001e1040e6030b04071b808070f0540b80713429800030165041000c08404002a841c8503240c1504190040d410b0751909406071a01d016403074044d048079448203c0b05001c940c0311903052003455030058140900700130840c2ca1100c482 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 608934199 1250 608932949 608932967
    0x30103081213240c0302030721060513050a060e090c1504090c39020f2101020a0216030b06010f120e070503011b02150a0605120c0916 59
    0x1150411000040d120100307014040c2e070040c0c009030400001607201582907040c500700a62403004904120350f03c00114083d000f81d034010007c689030101c903007558403a4502003854044401200360340b07440c80081c458803145003011245108900102e554a071050f8104152030311030348021200200c07103041001d0200e0210301250700b400c04503144100162010000f01c80c601903500b110107050315199111100b19049400d405c0c13082c0c0313006124001990ba889210b24514482081c5007600c00b0500c1d01d902c014604503800c50140c2000030845452031940040c143d1204401030000c03040d50394005103581d60542c0400c40c2007a0381141c90003100303000e4203540c0c40c1c0300403040c0a010503051044401d4001840c1d400f4a210240c1d0500c2c0e90010070030810014004c2c0d644481501c03c26010b540f03001509540700100003040e18100c05290000d05031140503002c40700c0d4200000740b103290410790310314011030180d0b00e41c540a02c10300e003d54018145101e421007004090700001c0d102c640c21a80f181c001d10310f81c50308a44c0ca0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 608935449 1250 608934199 608934217
    0x6091b080709090209240d15120311031b06150406150516050d020c0f04060b16060b10031409011b0e0f12160918110103020d0603230303010308 63
    0x9a01e85d62000046400072821860541060000d20982e50101038400090090071428030f200388400c10301000c1d4800e030f18825000740d01c41240107114000129015810580c103128040c000c891402e1502450050354442114042c8003a802030303000e0003400b0100251549154030100c604114242c98086803000c0c0c00306090240742032090104917103c118424011403400340c0d0704003060b5080780c980d1480081d203070820444514407072803503181d2000c0030b424180b1900c016034200801e80ea14080038413001c264440881e0408a41e100e48907950078443d40c0390a0000c0309900d0082e01e011464110702e031055040e803500149000850380c54444448810f025083c5510b148550f10700345401c2040b00c038400303c0c02c01700ba150426500401080501122039400180a51440b441c682810b00c280d03407100c1c040e9041d144503d4600007000c5510303078000c01180e200711541a07030b944141801807034801804e1082c03050710300c00d13070050342c1030f0408810707a4140001507600000401810000307145150306568642210340144011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 608936699 1250 608935449 608935451
    0x1124041d010e0c1e0918060310110702040b12100f0b011b032f03041e030b07121409060106020f01060501170402030102040f0306090507050d080306012106091b08070909 74
    0x521074000e0b13a0031080391111403015220070022080420805444c45064880351b0007440f4007001c00300070302d0340c1d4031402c400f042c2240501440c100d019020800a401c0885005a00000d152204850080104821403100050090114102404400707200c11035034102c41480c14402c3c1407000c110388111340458504602d502d4201062209000c0340310140c2c410f507040c80c2210400c004420702c01d6000001010b8070071200030025403100d4441007030302c8000200c1302d4800244030a400001042c800d80c0104040e45400c5191480040c0340c6003c0307100350350026021780755203150350402401130112560501101d00000d0010340240007242c03609000a00001404400c3c0000740140000b0600b159001e404581c000c090f0503902c20105500d178140791004080540049905208a51000945050071051110255000794559046540303400040d80c02c001c854103141900002d00c40780c000b902c07804e0701c42c840c050200070100042d081020b503601c601a0691401400c14007401000708014258400c1921044c0e41118178 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 608937949 1250 608936699 608936737
    0x9360708061009081c050c03040306050115050922091e0309170c120a050303100e0604050c031303110708070f0f05030703020d050106051518010c1124041d010e0c 71
    0x1b1a43e50081d050320344154080003500105010444c1c2045050341c4040c446401182000181501c6901c01c491030301e0340041101b03001441e184c01040913030020380600702e004920078413541c0e034042031003150303200b600300192075803580c5010306510150813000b410108c004e1503a041301d42812030f82c1e00c4008d032009c80c0c4502840400703074800110510450101c250b202d8100d981b20308103019161508012405407444444500000031158940b5005460082012000442c51501c2d4803c10750b03115009460f095062090000800c0700d04802004414000d013401783c081d102c0141041d608007810351655001c01c181c01802d00301804035a0700498400200c0340c3c110b0b80d5074000c1600e07203000c40c090301281d40442d52003644810030f00310b481d82000060140d08a0407140c51141d140c2e001c01500c90600140740940601c04103581c14900c0d04112400b10880d4146000b41203402e407000c011140b0b20342c8503400c03004081c06854003c408400d205143d41d4050304210702c1c031030001d140c004c1c040c80d040d0103040c1c101a5a03181d107036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 608939199 1250 608937949 608938003
    0x160801170309040504032d080a0f18080d0f141f03080f07120c2d08030c070b0609130f030504090e150702030936070806100908 56
    0x10407200d0b00d03600508140110702d050f00300940018641d201d186112030701044402d0000c101c1641c1060720260f2030319801c4607030b181c1e6511035000b00b84c1c112062902c4d070355408104200140d00d151703e440c001d01c510b17607803a034510330742c1004000e0b00c103060440c0b080f550410340030204210b41c0070b08260780301d1901c0c1030760154880f5407540c2d40150b101070f42c4050030800c0000b43c0340401826807401061038a00807440303020300007076241e02150303400302188000d05540030300e00c06054a00030010420444030046880e540c881071641c1c50b400e5956000780c40c0d0b5000004000340720000c00984da646180d01c05d0048079016894a011404034211401e9030100410400404260318105801801601c01411500e80204000f1291880c03070b0f6a681d07800354000481c0800c03c0005013505100008440c0001000b50800e0f0040c0c80c2d102c0b030321031306c540b40900040410810380c1c00c5c1201007240c4090548640c0342e55075840c507141800000d200780203040005120030080c4241060055640c005074170350712049814103083c0481406 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 608940449 1250 608939199 608939203
    0x904020d06110406030b090f09150a0b0a0e0f011202011403040c1a0c0f030c030d02090307080d120c09051e0102011103010b041a031303080408090a0909050616080117 73
    0x3501c2da000c4040c00101c0e020131600c1e40350380a00c0320903006071041d0310301d910750301e1504000f581d00300e8940c3d40d0307a844211580300011130601c6540e04000092004200d44507440300242c001841608060103d844000c1000001104000b041c3d004003100c0d440000c50784100e8000800404074900c40100c005400030100741000800b40c424030042100c1c2081481c20100d601e001c0f8559400306601d1942c2e44615019610071400100450361100b40110095261400303003c07005000c2d4000720700181d0305000780c00000403002000d02c4000d91464255843d00c00005100311b004040f51241c9001504000104005019948a10400080090140304144055039038000102d001d40f403c0b4100b000c2441005c40001030410420000e002a100384800450881c041805445940d000480b02840c41814094464010a0164501d20b820901407142549404031034400b00710409525441010450b41c0c2c2e03822241486401d00c207903600109a803180c80328500c0440d600030301000060281d02c000d00e0301c403090f0a05042007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 608941699 1250 608940449 608940461
    0x903020a09020705011b2f010e07050126010608090a120809101a06030c0c070b0a0305090a0f02040209040915091205040b0307030b0609031b1302090904020d06 70
    0x10051a03a09160744036512100a5007115000716180d43c01d0810490b8182c1002070309460107400d03650340540840c0c2c41208008072508a00301e9154803026003089040301c0000b07014480d843c1032010f0003811000e160400051410501603400d07601100b080d03d8003024081c2000d00d03141150602e24045a894407030841043c10965090401001010781c0080400c0c45904a00d456200c3c03680d180a4a4413031303130405098070503138000c4181d40c03520949900d003000e00f0b0710700b020103150480d0801003464108070203c03038058908001a0091081510045071080d00c695042c051554415129006420781c1929588d64607031440d0000c00c001d100396000300300c01c20191182da000300e02042d0030406600007020544807600082142000a0364481c1416204a080c0d0b07004400700c804540148144602d99030b0b9501c1c044004111144880d903000d8010002901299001c103c0c44043e10941d050344840c8580350420020314a14112030300001d00c1c0140629601c951350408690352194060b03482800c10216440e04c00001c0031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 608942949 1250 608941699 608941703
    0xf271017150109090b010e0709050901180c090b030a0b061e0705060601030c170604060b03041a091c051606140a11070807020d02030c0406171c0c0b070903 68
    0xc01180c8401068001580d2414000120010300d6940d886600100a59a24907005010307801e648004001e1030b0030100722180d0001740d6240481c5020b0301d40c00002d01d408000e91040ba01000c0c0000c0d100c100104501c1130300c446c880c103803e001d280c09141c081d10701c2030b80c00000c2c0b0840f54a03944003420050780c0c07035038012514040190000c16000315410300350100030303400204050b03d20f881038100045040d4041c1c450181c1c080c284d40c540206600340000c4410040000410140d0802c2d21901c0020701922414040c5004600c10481100392200c000100102e01d04001c100c0981030384800d80240c100750a041004551070003518000d903980e1a25020841d070f40e446040010041c510700211341900f503000b43c401c7d42c0100748a10b0103020f80302e8100c2c5650f42c9030141601c081d118010811410006184c00782100240600c06820350f002d0581040c0001c04803140c80c2d00014001841d0703805401e0700710050000b241d00c103900e0b55003100540d0461311700034801e41c0036490080ca9016140b003c2010343e40208103d0300216 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 608944199 1250 608942949 608942969
    0x31518030e0a03060f0903021501030b13050111040902090f0102070501050a0c2f0102120f12190903050408190c060509060f0703022404021827060103020f2710 70
    0x3040303c2505c01c010403032500150014011050540001001020681d049903000880d201050f1189000c4090101d03201000321015036846141d4607002500300b016000600c0020340042c0c944e0018420300c0001451100444d046404c4a281441a1b0f80c1240c142c8500c00e03414034054940011918206440e040002c00d811705150840000300c0d0710203650b04040b980201e081c0d080d40c0d101d40c682d5035128000d000c0c0c80f203580b10700c3c401030121440d90245544001d900410b898201f41c8411061540f03c8200d500007007040d4001600002c4c18005000100515803101c61800d9440055107004d844034511075609000d02020014002148070b010341e90141a101e10144032000c0a41c1d030711552a029660703580410000c4505003101d54140310201c0d80c40f070814442c50f0098110452060400c07180780c1540310017086100284080454218505002c201800e43d5a40000092000e5415801000040b404580bc00380c40b6801d843d101041407400d10104482d2105044055051515103030b07030f005030561080d00024000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 608945449 1250 608944199 608944211
    0xf060f060504140406020d09051b0103060b0a05090d020a030803070c060501081b09060109080304230609371701050112031e14030a1514030c06070213020a0504031518030e0a0306 78
    0x50034030b682c0562b40c0d0030980b0104200c0c4da640003150300b2406030342a4000481c005120b800401c0c1050781c640900c00340700800207041ca47d00c0381d542038210341056031203d001841d061400c004100c200d12803540540401002480c491a07002c00110982d50103000182c00340f6092801b154080e40a110b005010303225520a40340c0701c540f6600049044803c1d042d038a9940c2404240008803410a5400c40301c44030300141140e40356110312540c00e89a006441d031001c03070101e4116004000b401c0e0104841025040c20680040100207403040c0c14207540040e00001811400ca10b95000000e4022806c1d554000c00c00140b0301080c041c4035400d45031440c41c0000140c3d83c50000040010000841e4000e42034409509a0040f07020307120014201c244e103150400e00e4065010540e54841880c04c00b01604025100824502c0764082482c0900c00f42d03002a103c007000305201290034400c105c0f10001d01c60050311802e40800c110ba040c1c0c802d2034203126081d013006e424020704c04c20054a684400046201070f50f00035506000d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 608946699 1250 608945449 608945473
    0x2040e0102070b0f040302100b090601030515060a090602070509130f050f01090311010e07080304090e10140702240a111605070f170c090705070f060f060504140406020d0905 76
    0x384130320444c0c01310300501412035643c00d9045144102c03030180360042c1114540342d9440c070041d0000c01010385800d800c840e000d140203005a8403c0020421500d07983e4542100c1c5181080c06460407555400140c4104469410403c60445c0146000300c55904400d2200880c84c3c10305240303051802d0000c1510302d55090840c04018141c0160215804080c0013008102102104001300d40b02c4055005a400301c1e041000b08000c60001a00200c4002c1d885200f0b8442084200c90540c00325002420340e48080039648041111280d014044007041402141140441e601211900b034200301c0000e01101141c2d0361400b80f080800b0186c426600c0705428203a0103550000f103414656036544c1c0c40d10039185543c0030320070041846c8685546590034560484000c041000725481040500080101040d041040500003440130460104103d41d40314003501000136011381481e0820309680080d04200c8c052810924042a225024150705900076000500103846e00c40400c60000500000034000c1c14034400c1966400e6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 608947949 1250 608946699 608946721
    0x801081b120303252105101206090506010503070f1512230105010e031b0d0b07030b03010612080702010c020f03011401050f03010e0d0f1e020a020a05190302040e0102070b 75
    0x49004c80764120124214048100f210304a4500041d069200c00030080b40117090310640100d9001604607146032016512000300491480c00c80b0800d5900c0f684903c0304000340501071040c00d015000640c00782c45594280741d0007150740c0c2c0c2d0b1740c8220015035008800f0135040700e10a00c1411000324420034140459070044c0c41c03408802c05c62410a841c24207480000084a600a991a01117840c016000c1c0c21300c08441c0c4104003182c020003001a8000003041000f00008141b5280c2c140708030700c00d4600140340001541490b00315502608941441180f160100e408a0075180544145d01e509282c44000078841e0710100320280e40080926405600308404214155440d80b44607042e070b00d007503418400c0504440201800d80320b298003034082540107030305e84a414034424041e00d243c8131081d082c0300d2501c1010b81d901260480c204100c1e280141c0005400c0780862501c9032801c402441d04a840d00e080c0314041e80207108450700c2e480001d101c0c0d6130701d00d800521403c01b90107a4000303030f8015039103090138a00215468 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 608949199 1250 608947949 608947981
    0x90203090312071803020f0d1208070306060206010e0c0306041e020a080606031b1b0706080105010e0307080706031a04141e0c0307140d050108100c0801081b120303 72
    0x1086450510b0018580e144075030301801c40c101e003250b138000381d140c91074081c051000d2485c0c1c02c00d9003082d2003108032004161103486600c1d00250980e1344103254a0076000c000e04450490304014115008a0010080c400314402c2043c3c002c0401099940d41e5100c1c080040c1c001c0002000c43c4541050b0a410881d240740194090110041151601c500700c1d66403004018642c4002c4448401c0008042c0203000c80d0700f1f0810141c0b10040812149000e01584058124602070f507582c400c4c4002008000140b003a968410801804184150000c00256040c8101251036038010300078101096500d40f00300d0002d65280304900c10508c8041d2080220700c504c5101b89441ea81d00b11407504222081c007580701c000d4203030f0780b00c4039102d2007407450441c0c115140c40100b101c01c1c08002d800110701034401e00060081165503c6218024032501c00203240c0b841d08113440d10240c03461606100244021500101300140010800a5280000241c19042c846014001480d04400d22100110318030001c0100005070f81030038080c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 608950449 1250 608949199 608949217
    0x1404061d0313060e0d06150314062a0f070b06091b0d0b0a0e0702010501140a1a070f0b150411090f010e150c011e0506090705130902030903 61
    0x14540005603141065a24803548003003007518200e022007042000d1255800a0645200a0440d649410b050b1140820b5440c0c44000e00882c1d00140360810411010304203000440031402c001c1d10b070710b2400803104400d2581d0141d0301c19441d24403200f114044854542202c0440d40c03513807a02a20f561507414805078840c0e0848405024500d14000f00350041340803188009482c0c0503c1d83c162a01c00114402c4026100a41c096500114503000200302e552511401c01c2c49081581d0002030598036005240b4460280301c0d03501406028050000d02c612590080c105a0405070405083e5a854803850304682003800d0002c06000b1004d1403051000e05910781140810001049409100008681c0c0c41c0c50300500c648410503030b0001030000070103842c0d401000361030400c81c8014400c200880c1e52200401613603100900001050b592030041c4030b80b40d6412015011042055a010031080c0340000200d4500180984801d00740f0034080350256885905a408002078920402c0541d01c81c01d0415034155260030103000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 608951699 1250 608950449 608950481
    0x3281109100207030b28060e0f0f010807051e0d050f0c01180509040f0206130306050c09030703080f090307030b0612010e060a11070c060503010305150105010c15140406 74
    0x441e1149031000942d241a03d801034122020fa85a24089064400c1010101c008001c03e02c03100002440d407900c43d443c02000d4041500c040d61030a60a1608882401070400280d22922001841625030010703950043d1030058070309200c03501c172200b0300000c00c940c03220782e0603409461042807004004021030700607520b0843c0350031500400c5214005440b1065009184440c0d40c0e02484100000c0c075101002d250420302601d035280c0d140c2502c0d000700f030030380c0e0241006400c947c0410a0400402589204542d881810450b070942861203900029031a02a28400a01000c03404112150700e10846002c840c03414000808031030401d542ea1801c4020070804441080c82441080e001080001d4180164101000b803640500300c075a40c0c43c9101c2c1c00400904a1588000a061000a0010703c1c094041405828151101754503036145240c0145401200342ca599890144c05004000e640d810004000c11660702c50005815484240215002030140b500403840740e4501c0414001402440d0340003070702d0000e0b8070349 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 608952949 1250 608951699 608951719
    0xf09130f0b03071706040215090d0629030a06020a050f18040f15170111280f050301030b180d0c03110106030305030c0c01020906031f06031103281109 66
    0x551030846213120a01e40c00316000000024010314250510852136108512024141426000460800f800000d0111000d550743c00150a030f0a0fa2004682030442d000308803010031809801c0800d40f98071b42018002d20040e00450b003080c44c14040c0d8180c49000400018550316805008180d98010009080d82ca000d14580401500112058090282502c40200d4030070245843d050189600340d003802210704042d5680d60f00c103102d980d100d03401822044019103480328085503c910030200c01c1c18000c070a03824040c0b42d06e041b018880c6c1020a480c11079401004040c450742d40c112030704000d070303c10265255441c0907108012220941000c0c45450f424007070340c0c0700c2c03413a00c0b517100c0742030f080380c15902000e004100144002842040042c0c000c00400302c1d000c00241c100742062010600c25007040c0c035985460451510400d071002c000600580042020f1b10741480340fa0b48000c41d09040740300c080d01040041c81e200030030800502a0707120b6007880c6813045004000320743d41848032005075003220000c13512841c4000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 608954199 1250 608952949 608952959
    0x10621020a06081e0603030f0a1706010903050d0f030b10020d030e030406140c100c020f0d231303050d0509031203012105120a0507050c10050f09130f0b0307 69
    0x3d6a01d500c0b030840c1041ca54440c840a81c40307400298401042d540d03061208211514451107404044c0101569640b80d00c100030071944804544d4030310041c0300e14104007030740104101080c000220700500350b085040640c1c2d07000d02e106049028000c03942445400c5405000085440c580c0010380e8a545151541c042055040000c0701a807280710710320130302c4001540810300947c40d071140401845da43c002034080754422070f000c5031194181d0f0062500040960461281c0c905495001d01c1030391840c003241d10f003041c00751403100070580070b00513494002e004a240203c0c1c01c19103000c03000c003c00040e541180465660381c460351b034002c0807507009101e428064066020b501071081e01c0082582e041e540311010302601e080058090401c0c00568001c10341e018896064003403ca1006034000702859070165460343d0ba00d020f142002d61a03e044029024042d509500b500051264400256401e980f414a885a60362884100203108100c1284003000510f181503901903580c0050384c003000500200760160fa60080e075074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 608955449 1250 608954199 608954207
    0x1e090d1e05190b070c1406071d0f0f130902190e07030605031b031609020409060503030903031209070e07030c08090c03060c0309070513020a020f2803031b0c030206010b0f120702010621020a06 84
    0x70002c001c2e0084a0958942807510b00284100c0d481c01e0cc1c03c1c6e0014140200d42c0000310140c90340900d4201e02c1412607801d00013038803400106a800385043c1000c1c07040780e107444003107541c80111410070400c80e00d4400343e856080d0780610184400280d107844c9003450b5611900c40c2002036200e4850507514515202c030004075410701200f501c4181c0b0b4010051410a100d030076500c10300034002052040507004411000c601042c0590407240101c8060750009070030721901102030001203020703050350001d030310031030303155000e507800051003680860344100c05034881e280d2009861429455800c03044d440011420058107031003540c2d01a1607600a02e07130880d4130101003954216110340604800c450034035164100e00445480d000b40d00b1204601c28074001481c0070844041007400d440400c80c00f00040c02c41d042d074030281a03040181c0c90140881111083c9000807401c2d01d09d449204100040c0400d044410010780b12900030b40c410382c01410800c402d402d07a0a44070703846480314402181c0403481940182004240e032441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 608956699 1250 608955449 608955469
    0x6050f1f0b0f030c0c0d08070806040e0a020d0c05040e0f060717070c110607060506130219110f1f0c0201021e090d1e05190b070c1406071d 61
    0x40407020900d009800445901d0543c0010441e02c1c1e202c90810645450302810000300f81c1550b400e9a4046450401c1500140200006005c55200e80e040040034000244082040d01440f83d040322450102200c0b458001c807a1201c079803089901c2840c11412510340800480c802142141a5040d1040c82c1d03240602910715209807200a507a0301c06050009051034000c28241846c0da00849050b00ca21100500142013a8001c400449800e0b45031020711100d410300401d840300080101d1070640c03c1048560201144850301d41084041250070540340058803c09d104a04400290109440310282803503045031205403100c4903842942e1620088401d21841842960240c0c0700e80d45000200d01c3d0140c0504034160840f5405230b81c007900c41041040054150442040e03080701d5080c170300246008909205051240b40150b22080d003800d144040006252003580c680d100c070f1203040444403120b00b41001800c4180b4480b00311864403604080c80301c015084110303100e000403040c4072200010b4446081c4001d100b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 608957949 1250 608956699 608956709
    0x906050c03070f05030a0219120b0307080c01140909010b13060801050a030609031b050c01120b090103060203090304080a03171608040605130f060c081315021606050f1f 74
    0x40500388020b80c80d1080c13000310341010368003a005d414000c4202c0c01d0401040c1c050312003000b10f04001c6014a044096015801c40c640d0100c01800b103043c6490742d0301e074840002682007810400d0f5070b110070006200303d80c02c0d00c3e280340010b084a0401d6864422200055008146000840307155480008015200d0100b19050350340240016110504d583d94481c09480910004c03424018481241401400d2500b9000500750242c4020501c149007040090074509040003956410381c18411010220345510f0381690450b0717881302005a032580c0f40f000303c500b14042d6030000c034000c1c0191080e03902810340c04003401801c103c1405941c84140c03a800b00c07804000c210118514040b58030f0800090200e106548144c0e801017040d10800206403140d40c032028450f8000200329042555500c1610744103138008a4694000c1c10004044142d4115490300030041200c0f041880f10b941e00001d4084141d10707405900d1800076070040080c0410700300010006d84030901255a601c41080782d0700d0b50ba03101481303004014200c0d8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 608959199 1250 608957949 608957957
    0x150c170103240f18020111190206070501060e010b04090506010309122d03050117010b011704080403080c0d020105071805120c030313150e06190311030a0906050c0307 73
    0x1d1084201c000e440b0094240030208079551103e4100900d11400350303982e01e80304201013804104d071a01c0090025501540d091125520101400c2c1c51900300398800302186030103c4985848562503e001400742c80c40e5080002e0381d203070002c00020101580030240044e20420f02d41030180e40d840300011411075004500141c400402030656200c09070140c06d01c4c840b085a0340702c0121141c00c818034980d003071103079003244480001e984000400c000300080c10100081803a10000f44200c14002c40020941d000810100c643c90030703003502060401440100700c80055620850f100e40311508450403540320307509045180701550805002500c020710561181b81d50300034010218040b6030400701840810b0705402241c85142c3718070020030320595400c20180c501180744a001480c5ca42c00e216a886444804a041c402800b600565101c2c0543d602c0d0140d4805600f2900070106149121900b02d0152100c50600e1491410008c14040d10b007081c0d07001143c6072030080d1424015920b52940720320451004030768030000a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 608960449 1250 608959199 608959223
    0x305190b0601030915060b0d0612050a0210091806031a07080a020d020c0307050a0524070e0d0204090b06030d080f0403051b06010621020304200a03150c170103 70
    0x2d43c080d500c2000340c1130044d06011540340c604c40d0101c0031178070980c1040d103000301c1c0412000d01642050080a01400074191070800c0c0c0801c0380e6400f80d452520420013803140c8000cd1682e07291600ca900c0c600001e001d1110101c54851810003100001c1070a808107882080c000c800310615481c06c0d2400c44c0c000c80b007030b41c0d650b01240c0e00c07030203098001d4001a41c0419016001c101c04602c0710001c10281120720b0040d0040c00f40c0100507c2e06900e41401c0c6100c0c0030f1458800740501403100209601c41f075026030706007048000e400401c80000c0c90322005030fa00951007454905c403103040c050411a6a482030f501541210006440c200c020f03100c211048031416006006040000c000902c52406000d001000c142101c008005d40d402040c1484000d800442c00100c0600c0c44a01c003901c0c10303100c03440c80c0780144011469070a01c0d40b205502000f1a000280c1d90141940c0000100d840e41c8012400450b0082e000c0010304640c0c404850181400c80003542c0001e0000c001c450000c4132000b0a181201da01c90f44030a08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 608961699 1250 608960449 608960461
    0x5331509060a08070c1b0906062f12040e06030106051206070c060603051608010c030204050a1206180f03030b0d0f060b01110114100f230a030609110111070f0e060a09060608010305190b 81
    0x1e007072a03203952b06680307004080c00300301c68192450141010f0442d4210003413207440c260051608607150b6500083c410403007001c22004800b00820400d8020440d45840d400c01001c4e400d091010300342179800205288a07100c24082d5580179102c001b070076035080d00300174018503404410403400da0250b80101c642c410201e107010450300d001e041b04440410703c68072012840780000c1e1003a400e010321640341965803080040e500320400d903240c424034110750305c216584880d00a1584980c680309048003402001a40d6079007040b11079071b004005841440c0c500c1002030201c0340b024442070b12081ca003074502d0a1140502003001c11003010b8216207105071a044c0a030121004624512800e12604840b60b042e0401581c401c00f0000c1945405911411802007003d042c62407118400100700e902c1c13a910140003034200900500602401004041c110745400d415102c00d600c40c80c0004500d90345d01d900945e8242c2c544000014003580044025040f240600c00744d448014a1550f1240030540025000700035008001c00030300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 608962949 1250 608961699 608961767
    0x10e0105040506070c0e160908161517090c04140103021012200301050127050f010e03030d15080a03021005331509060a08070c1b090606 60
    0x20b1428001c080e1540103968584886d41c00322815910000c0c840380c50903e4041c07041e0030110000007800b0400041c006503c949891501e209010b010f400101d50380141e4680c40141b050700308407928070321031440e800c040c00c18607215a039440220369118040c40c2054040d5040300d82455400b81240d80140518541c42c107240c0c07045a0440c4001490f003100380c0c3c1c1b00d124195048180d9419025141e0401445036654142030014250100324548031403000c1800e03100300503010b0f0344000801114000c3c0c9140f40403114a10060b03421850b10051150107120108030320300f01040c140c0240c4400d1340405005004192212503c50f04c2e600221070150259000004166161000e0380c012540610350340200100d80c50584028240f1540100c1c40041e01d548554a030b0909140001648200c0641c0300f03501031800c0b000b1000719000f8000e50703900405200380580011807490085401c58002a448121081030301d0310b14a10341e000a01500610303c6007032804501090542c0680628200c0c466200c2c00d01a040c03198a607100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 608964199 1250 608962949 608962957
    0x6040809010e010c0c0617130f0b15040e010203010e0105030a1a100305011b020f010b01091202040e070602031e07030804020918010e100e0c0105042d030605060f010e0105040506 78
    0x10f0304000c00c1d1946140400c0d107074401540500720b1956560f0703420340da00e805081c44041c05031603d40340e90307110380a01c800a400086001c88903680034282e01c80c10ba0741c080c1180382100d40500c03042d800c181410031595003440d06500550582f00340e030048052598a88003803640e10901c0791002040000ca64220810800d8003805840d0702001c0c031140701c00c03a2510303991a1803c3d222010310403520b015288215a40040d018880341c814015950b000f001402c054000003001d00d1060310922107401c8a042c00d05041d501c0c0c40e0031400503892070f84121580143c6e5858025031300e501c04038400034851a08034840500c0c140d61011615050b8041da07940038140c4540c0c0030810110760240c484107603225100a00c0d03007030358403e0003500c02500098014008414456003a40252081e81200d110117800c02c25040d015aa0440d0642e003d48040942c0b003801c1400f030110240e1001109502442341b028a10340001c204842501310301c2c031a501c1030720340c07040c0d07240c4240c010358907449601d00c4107000c05c00c144400d000c142800f5000d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 608965449 1250 608964199 608964227
    0x203130f050a02120c040c0e150309120403030f0306120b0103060b12010609140604200a050d020706020301170601030203071505070f050705090108061006120219050c0d020604080901 80
    0x40c0d040100b107540015189210040c00d64490740241d010749050f482c00e881040c0340030941e420000540356442c0c2c00a0002c46210724241c4a40d2408000720f9000b49080107111201301c48501200d6560342c403810060181c00c0b403c0141e000280c10184042055000d0248102520b688001d14204590840d0740c1c0e500509030b0030301b0494000d65400385d0408010002d01450340140380c04040000c641da505040c0c0b284c4480000c1c0654040e5040c041145e074080141c030782000e681070704078030b0194031403024010454051094011400440c0e0000c51203a00b4030106500450403203003c0050040c50078100d4400903219a02440080c1d0700d42c000071801c120501c080c103550104d904c81031070500e290114691383c84646514182c0140c0d4141c3c406001480f080c140035040d14090003007840102003a01c1e100d0140b060000c3d10340030360810031080d0703020303800903140036015910540203450182c8a100c0e03100c0c2006120380c110900c2c00c1d890f40b15820981da00540081902030003107800034110b901d409118801920701091a10360 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 608966699 1250 608965449 608965453
    0x106020325021c052407020f062406070c030b19090b0106080c040b120f070504120201050a0c050f0c0f0a050d06090c1505190905030a0b040c05120703150203130f05 72
    0x1710038011880e0420b00c2c034a0321307000011036800d41030205009251001c00c0c15000510380c04031060018a0301d02d00c129802d20341c50303c0b082500b54400c00c00440c095005444d0020542c00c05e103503000c0100111b0015032845920415020442051030002d41420b460aa0001601c11040b5a00500c1a18403d5041c180d0001c1140c1500d403034607075603244001c40e070762001d14500c2011080ca01444040800300c02c82e690071503810314146007031904000c0d60b03544600c403690009051240000782860708174003c01565402ca0340040035102c3d402c410711046611000941859482000e88a44a00c280d180000c00d00c015210040c106403480221a5509402015000c1098a11005d0106c00042c0d002043c80e4034031513a400ca690b129100d18108041c1c503541d010b0f41142e141482803a070818025503c0001c1e02001041e0494600c00c0c030350701d580c1400c40e40d0f031015030016908130846c20070b502c0030030100040000880c0d120b075005a20710807084802d50304900061340c01c5503500d02050421008030300900c4050701100d000e802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 608967949 1250 608966699 608966713
    0x2012a080624030901060506070b01120f12020105180d090501050c010b040e150c0901120f150f080f060601090324060e190507020607031505090106020325021c05 71
    0x590100b80841014040b900b82d1000420040640300a0040714000c0105440e0207041c4085603580c2041008140120b07a44a0030040406051108080c0034084c403030342004203000c000c204010f0003400790400b103030758140c042d101c2070414240034400202c01c001120240e449401d040d0500004482035070015000500320b64885400700712980d0307288520900341d0040d500805644840048a84078000700910500d15480148012031040e6000107021040712000700001a901030740174240001800701c40342520b40000c0000300801e41070300c6c00700407000303492000303048a10903444440010380c0d6045c11a40c0c076000a074030900c00c00000d03403c008a5481c042401d0b0401541540c00c005803012107401c1e500801400107942c041c80443ca1182c00d1600984043c0e4000303206519017284042c1d40d03007101505039000c040e910000c90038010800d4040901030705005240e03100c80c1d60b454500945e02e030400c070b085030303500c03450f20138580483c0024103425000f8683c05014000d020b003903409100050840d6000554650141031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 608969199 1250 608967949 608967979
    0x13020c2e0c140f0408060112080f0a03090c0f080c040b1f05040806070305071409010921150c20100207031b05150702190b180303070f02012a0806 64
    0x1034007405203024000c00807a04d9a02d003940942c500103041c1d0100d0380c0224030443e01c1021400500840d0701090340040d010b9500c5046440490040074509805005010185e00200d0b401c1024003096003110411011201c401040c6030400048030a1300113401d500459170082c03805407110302d004d112040e001a040041c28544d0b140707612406c202080f100740340000e43d03032400c1104698002c1e250b41e041000c8a1012401c1041500010740b0040150040740010502a0130b9180d9051543c5400d402c2d030750341315011042a0b5100d50b41c00d000b80881c41b500001103007220902174421521050200e4100c2509002000321080c00d402d410001e600c81d078000e030100000303050038020750409080c85540311441280104030b80244a803038004003401c0580783c0402c41d081070500106010040c84800314907500500c031820103440c0c4c42c00300c03e034100344070440380003601011080200c240c0d005081c21003520a150000c4c04800d50844514504191640f0310cc43c3c1980004108002c2038030400425500403006080d48120703001403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 608970449 1250 608969199 608969237
    0xa12060c05090d0506060a0e01060e0f0307090c020c040614030a0b0a06091a1815041d0d1808030415050304052107110406050f130b13020c2e0c 63
    0x807120a54180c3c0c0032501b8041c0d50b04104402c0001441e401001c0e101d154100100200800d03407040c07403103101d40c611940104545d6028007890000b0301c0100c0c1300f00940784442c10041d48804820000a11a134a030040008042000c44c00c0701c078610304000c0150640381250303500c0c03411200010741803200f110350f9114046a0b400c81031107003265048115a0350004c0c410705804006e032804030141d6864900d204a018450341c0b14543c516404950000c680c00700300517030245820303550f607410345280d10b1036481401d003140c14254028074034070020800c9140ca44442c07500c400c210781e074910032881202d400400c1e241200c03062034400c20156410034844c2090399148283c010141e101d0900707201c03640c81001e400083c90810004445203d0f038051034142d4007444140d160800240880703004054072402403d02d26105940c0b21542e52003040d13081c100a0480c03004641c681c0c103204c020740110544106038420b0140344003003002c2018110302441034080c0303043e82020042c2002e00c0a046600702c81410b220f002c2c50040150340d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 608971699 1250 608970449 608970469
    0x609060c03020705010513030926010204060c021804050705010309050a06111903091250070b010302130e030708070b061c060519020a0207050f0a12060c0509 69
    0x10659025031500d006007095821104003512000b84070744600700b07c0c030000743c1112600007106e0300b9004a6259040c2200e000c035000c506259030800e04e5100040105c1d44540210071041d11500984002090940146004069110517240902203034031098040105610036085075650a01c28020741380c0100095036000c0941d050380031240401c18000c1103984401c410711301d11720b115010f030349024003c1207031070b0b00c6544c60004040015000c01c600d06c07000e41c1c119003d000411801e43c03404100344403140b034a40e040c42001880b0301d88440340118100f1600d50441800000d94194640000c110403a81c0d00e107034200540d12200c1c00c6da088075292166000e0558120900241441d41c1c011021a5521805450100c1c01c059004121921500d40d0102c960303002013141c100f1880c0103a01c0b140c00103036030315240ea0b201000c2d003001d01c40e03606441c000a10034003050b80c04540304003150030640340c10404020f19030030006694000e025076881e0006840c0e405020484903040000305404905200d89000b00e5540400e0359801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 608972949 1250 608971699 608971721
    0xd060f0c02060a0510030308060d26030105191536030c0905220203150712050601020607050a1215030f05100903051602130609060602011107020306070c060906 70
    0x40791040141d5030895000f130f90351100f00c22601c0010135066a401030080b07030001e082c45c1e010b018604000320402014001d94801d0f001c140b0712032001a11131055001c200d60090164901520041c02e130310700c0038640e410642003554240050522000110602124019036240c0410b92008043d1188503c14026420381c8602d280c0541d0000103690840c100100c1c15055035000c0f8180c81e161508100c80d28100100641e010761074141e503141c0181141c000640307410031001160380301d40403c8092060b040e4001c0000090441c3e1200c0901c601d84c1c81e20010f80e21918200d8940300803500410855002c2d5114080c020070605ca00f010001d004080c1703914008031251113400485925416803d10014032104101c914204201003030244801c80709130358020502c0c0105c1d0361014400d1108801c0c1021507840b043d170940b20001c80a810040e0300d0392990f103540901071314810040035510b060038800c0070f40181ca040f542007035006001401c80f612846011101c034020020b00760307074059403a404500062424010707442902 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 608974199 1250 608972949 608972953
    0x6010e0a090617070e011401180503150906070c0503041701060b07260a0e0907110a05030901091403120c0f010c0906030609090f0212010e0106031b0806070e0d060f0c02 74
    0x407100500d491504c600382c0c01030036000041c0001080a064004002100d5400a10785a4a25008603150340c0e0114204d4010755418054400d404170515003060343c0b18031844202c01290a82c0c1c44c2c644050741c04501c0070002070b0031500104030034000010380880015040319220000900c0300ea032031503103403442d41108200b03d4034800503100c40603a00143d0035a10002e4084400c025181c141d1010000d40516506540d45010301614030001e54114082c0c84580703402d5201d80151036000d0b40728600346480340e103c80c08082c08507417603010200d00c009a400c3c085030b110101070020070300e10756010300c5064030780c1084520701034038070499140d41400c1300d0a0040d001020311340c1d29901d164a017000006000d9424603080050428038100041c4003140f07d050030000d2043d010740b00140d03881b1114180901420009646240741d40c00c181e4000100100c49000209010780400d402c0d95040d01d81440316100c079402c0e03407001d0008450301c0e00c502407481d000d050318445c503101d440c0c00501600e825911506036028205c0356409a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 608975449 1250 608974199 608974229
    0x6080702210304051213122a05150909061318030203120f0903090d050c190e060609061803100f02090307080c222a0f030c0806010e0a0906 61
    0x101007280b130203850505a2414146443c0c41b2401051502c070744103074250403140c2d90300082803089080a06e00d048409000d1149030039100100300c000c03115107201e01d5004030460307181603000d400d0400035601880da000344003250700d4032043d00700700300584045c00c45100d0950f6940d1010f0070f50b01c10015081920300c2500619200c40d90b500703141c000076400600c0d55103800d100380104055200d020084509051048402039209101402c5c041d00e010000981c00c0d800060341e14844003800407c8040800f111341c08154808590307119070074003025014503900c3d0368000d9010300c200303070441111626851a620000e400c40c3c0e071035143c140070001611807640d04015415800518098207080a0002e00003030311132000180491204000856407800300a8280f00c002c00400365a85200c13440703508a011614600c801c0e031413041000b01c0c0400f0b0300710b41c0c0340d40c0400402c070301d0710600200c2c6002c0d006100c61021940c4408220355074600040d40d11a0500380c40d0f9038403e85110000c10348212501c1410040e00c2100d010000c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 608976699 1250 608975449 608975453
    0x5090f06042403060b03010b1b030d02071104110301050d0510050a0b0906010810061b02060c010c02101e0c030213080105010501090602010e1011040305060109020a0305060f010906080702210304 85
    0x1915200304480406040131000d0120480703c90449046a120030229640e524150300151030a034442480003025000001d01801c0d4031031203030060200f580c041d00b81e01116006420410040700da12001136002c3d0002070004010900d040200e41c070344c8034010780c207945c032046405201000302c80d42210407481040d511800b500c1e10381000c41c0d00e907511a8080c24000410f0411284141045c141ca00ca0181004003c20126044517841c0030a101040e501520350f0340c4890710340a0050107050280307036140c014031400301301c1904000103001b803129403500e41040811088510074503c0203014455505814540c00304580c5180d162a0b01800b40100614800020b113941040d0004048205513840102160304000452021000200e00a41040d03144a40000d00302c40b0186640e0403030190fa800904107001e60400007900140c5a001043d02c603042c0d640c204078aa4030a070420840c503114002c818005401e01c103040c0282402090900d400107031900440e200004540d411a424410011340c1a03641c050100078001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 608977949 1250 608976699 608976749
    0x70e0a06150e0d060b0102010608061014060a0e0402030a1410090c02030906250506091f020705100b01050c0d050d0b0609011b030507080a110705091605090f0604 71
    0x1041d0001c1c0e1418010703902c0e016001034038240f000400904116a605109041d5a000354080c41c0105940800d0716500d1801c003144841d6443c2d00c1c403654003404100d2441301c08034981103013221520b1045407210411000c4a4003800000d410051408919560303880350441c0d080584c0b903440d849081c040381001c9244d0f0811202000ba00c4001c0c00840a650040c8080c114943d2150151118040c090009214400d030407601e6612030078542801411070b000b01c60601141210129001c008918820300001c0079100c081c51550032481346440140080c1c004d007010041c0350740250032007503515805140050900b170200314558203284040e01c010340441e60008001008803124011400490340071640b41d424110041c0c0040e055500ca0f070341d4588203c0c4030007891000c1500400594881d55080318000341c0340d003003031380c03000d4546c0c0794480303442c1c0c41c0780b045110000e0381d450036038000b034840d081030000402c0600049105640c42d40006136840e501280344d051030b035203a444010142000304200c00c06110b408000a0041e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 608979199 1250 608977949 608977979
    0xa230d0b0114031504270b04030305060612190b120312010509010b0a080711010216051507051b031c061e06020706120906061403013803070e0a06 64
    0x4000503003071041152500030807003120718484c0103a8011407440600c0c1014a224562910280125414900004280506201480d2043e84a600c04010301d0b1100b10070000540540701406940c00c001e5070010384a0700c45524500e401805d01b400102c0e94492050000e03800d4029051031640540c40030450412002900060500625096680011550601c030b003a07051442074034100000c1c403a2010205c0c040510440c2020b002e4000d120007151501400480c2d84282c2032422410f6132076220310401c0140c4803161042d298020091629491720300803400c081c844000540d10441c240318007047c400c441d03204200c01c0e1380c40f400422140d0006441410203042071400c01c10316030141085001c83c41c1c20b102c84c980001d501c8058a25a0900040c07035401581120701502480c0001015542805000a82210302c020101e41c030070300460003804103e4400014a0441100e401090808080300c14400d00c40c1c521031003c264607007006401d07030364120b894010030401d182055940042860f43c9400400032502e0b280300a03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 608980449 1250 608979199 608979227
    0x1b0a05060708150f03030711130e0102032d06041802060d020a08010602120304030e210a030f0228141b03010b101205100510031509050c0a230d0b01 65
    0x801c084c07005040c0401d58a01403044002c0907a00e03200076000190760340b020070240e07081e42160140400c509122440340030b1b41091b03034940e01d4404400b00e0021211000c0b007400ca01c8000926028820b5910700c030401000d001c000202d004002c01c0c100041c805600c400c001084500b4580f00b000d0b0b95900039001c018002f60050b8001d0007103400c10740741c83c41c000044904503600a5010315100c1c1344240360700c001a0466a200300302d06c9215140d000000962040800e00b09003160098031030103040b00316000d090f0f0725441c4518100114240500c01e180000011466407031010b40103440214070300981001d00d600d408030440309022002e01d800d1109031700d46404d000c0c3c1d001c5014240c4a808591184000190005403601c10b02c02440c0d4654000581c180c100703413854001010010091810002409006070041c0342c29125900107048000780030030642d07400c3c0542070044130070b8011180703806011842140d44890202085c1191511004040648440040607250300c0c0c1102c0000190403041c0400906040070110039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 608981699 1250 608980449 608980459
    0x40f0b151201060f0503010b0a021207030815010e03030406081b071b1e0e0a0f3902030304080a02010603050a031110050106091203110607030b18010b1b0a0506070815 73
    0x100701809a111094074111002300040b15180d401c001d800f82d003040d020b10380814500c100407071b803d0140f641c002d220b41c1c007840c0c1500c070261440d0360040044581c2c1308041002601940200000c00c004c610460040340c1c41228030181064a904000f140881640840c1003a68020b14040c400d02602403c0c503071b504010005921421001d0b4401c500241c00f107044c2c0d1245e544d1a107000070000c0c51601c010780004400042e1380c0030420403001c5a003090030b401c0491840d101124030000d0701c102840807925240d45a0400c032a002541965119601d03022203a00083c9040d0841d500c80d00c00100050f82041200d0031140300c1c2c1c4070120344c0c01d001040d403854032403142c0c407040c04c450900740100311003500300c00034038140d41162841c0c846960b0541019a0007803400c401c120030f98031a200c100001250306502903002c41908a60504020f014451130031a101c03002c0c02002441d2200300442d9042144013203c04c4d22410b42d131340c25140d0840d62a10b4003410840111401c0011071131250410003002c2c14182040c002c0541120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 608982949 1250 608981699 608981717
    0x130e19020c0601030f0515070917010e1914030a020723010e13140f18060f0f0a1d0a05010506040e030708131707050103051311040f0b15120106 63
    0x24102d81da0103040c0b00160425102c8091081802401d100100d01d07030300b401c0b91341410b43c10681001086070890307206256a2002c885410341d070382001809000044c10b5418010244552040c91400014202d004219102d0007012461401c46c603052014100007010342e0054003000e03140520080210095505025182400d41840e0f111a1381081105403a54020396106001c00146401031004002d0120448201d034613210030461020348940d00188620324514a02d444e8032502c800c507075a03845040d01d000010f45042000250404882408076038010301c0d444010404071094681840a25192a00d01e4225001003800c041172282c240101504000280c03003c1001707180c00c043c140d8403400303500e4000784196000140980c4040a41c1081005029106005281f4a05180c003240d40c814040c03250700e001c2400c0a000440c9007400088980c80150015046000d4041c0e0004110003000501600314803240d9510051070707941c841c405100381420794194011b6850305d0000340c50040c0b00050303000c9420405d10710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 608984199 1250 608982949 608982967
    0x102011d191403120402030706140a0c1703010b0304020a05030325061b0f02011415040906110313050f030315011d10030903030f052406130e1902 64
    0x38803072000d04100d403580c21210801d2411541c200c4210b00c0401c0b0500c404549404090850f1010328016072084040302c802d0790b6030b060251b4041604c201002c1ea101c030b0510035001514014107608000d0f42c0314000c03240c00c00030448500c1510741c000380c11128481401200308821424281c2c4404081c0100300c00450424082c1802086001d42015841c0c120b90001c40140003000619000b641c4072812015510b4101940420001c2c41d00e4400d5a0102c019070800d40c0300603500640c00c125074051010b81c80301307162088064080c00084c20700c1c140c2c00c44201e03a40380011214980080b020310f02642c140400b50600e5600d504025241c5103000c002d0103001e03003041091020303442c103640c0403545040003030030001101d480842246400039621008160445e100301000c621700c5074168000c4090500c0b13074030100081008a41010100c401c111b603c503088103851003c4906001601c1c10011944100030b1a080c40c185400910540d00440c50f406182c803081000c0c00d12202ea4580d0014010b0700300401000c504100600e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 608985449 1250 608984199 608984203
    0x9090c2309010b090d20030607091202060f0c120301080d0212090405190f15060e150c0106050310021315090e04150e151b1c0b0d060603020102011d 65
    0x41c41011043c00c030001d440030441c1c86428809180703540141084446040007424949221206080d81b84a801804001790105002e00c4480b01521008031b2110314a24980d030a00035681c3c001880700005c12428448a04649010416810b161028060441d26940741441051a0140c90002031080d03401c170708440184072000500340d4420f904201da0114850b02c41400440300540c3d8400425110307410704444041c001c40542150029611a051860185031b40355800c48810b11840e9070168410300034840c4040050780c1202a03d080001c400c000503500e42d541001920304060009118803050700410420b00e5131029600304130003011080e0004203040d181e80b00c01058a50700e401600c10b1901e122001c6803c4c800c00101545070f20320380303401c1045502c1950600c2ca41d1820841032a0b150380343c080e00002c10385006d4050894049001c944c842d801c0c083c00c080c050407148500c2410490070795640050354072940e030351041803241a02400001030010b01350b000090039101c080c1c049a05400d584020300c1101000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 608986699 1250 608985449 608985451
    0x50a031107210206040503060a050f010e06180603010f06180c030624050f0406030902030c011e050d09020904031205060d021e0d060e032503050702120709090c2309 72
    0x307002d0624080c1c039079501c005040c500490304100d400d8400c24040000010f07081d48014005c5100900700541d981e038035540500c940b803044031602c9e040201d486010928058a034003054120000500101e00c3c143d1180c4808201c40c020381c01070340820711084140758045000e20034100380040358270b0b044c0400ca09007119548442240768060503041030300441401c0e454443c0302601c0c6c002c421801d0b9550342c0c0d9900c0790002d0280807d039030264440c0c000da03002a0200e40c090b851080d200306070031a0030407140040040070740d0207403c216400c2c0c501d02e81358030314000140c1c1c89249840c41188242c4030440c01c191842060400c845000705050b000c1c1050182c0c140c0940e48140f0158241c2517144c3c4901000030006c80070030651080000c0c0101040d0400000020040300440906083c41d0424407140706035080102680e10110800710190105200701311190150510840c0700325040803405c2102c2400713a036a01441e00300e400c0303402e06581041c0c8103002800307460095022a404200c0501e4260010000b01c0300240c21208 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 608987949 1250 608986699 608986739
    0x61b3503193603091d0403020d1806050f070b04030810060207050f09041509111002010908030c07050703050d020a2a090b28031b080a060c050c0307050a031107 70
    0x142c02581000c061007500d1440142203c1e00980800b10420220503164990aa40c00c40240c000e90201030082ea1003200101105c0440e1445441d0b11498844242c3e4194002014148200c2003000b400000c03801c10400c203805107110ba55000e40c2e920f003800b030111200449130840400c641066000300a42e6542900480341e5500450360201c003a1540d2a002642e41500d201841c0300505040452080c0320481185011440042da0480031004000303000302d00700c4603100c1004101c1c15050000c0b40c0482c07840000b60081e684120112007041e504c035214540743c88102045940141d1004120108109160090b03140c40700d210700e00000c070803000a0180300680702a02548056990b80c0001c5015980e0b01c1010079140f410380d00c041d07a1005440e0040540602c140d01003031700c200042200c0720301d04041d90b000100c01c40d0f00c00800ba0552400a45d20724000d410b100580740e00b001001e1082d086003290500082c00100c0c0310b00002d28030b54a80d03140c00307040c041507031140c146280c020754002c0161464030440d01040303030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 608989199 1250 608987949 608988041
    0x3020103060e0f07050901120e0607120c1b06180605011401030b090a051b0f070507060903030207030b09030f030f040b01090b0a1a0d020c07061b350319 67
    0x700d000001251223165100e26003014908251140411210100c2d00360701403000c0740e48500181c95801c1e620f205581c20f01180800048004442d40801010400780880c00c510583d008070b030441c000182d002440319880c1058442a030745100400c1200520310b01010982428281884000300610006240b10750003081c542655485100048180340002d86004005d111348000f203440f48030303540100c4125085000b04807000e11441c6004550203000b00c2d4000f04030382e4158010030300d1605595030002460070241841801d4801031100d98074032402007026612810804010400380c1c542820a0002c89106074811640c40d0b1419080c000c80d9103d822a51003503904807601c0595030034504016481c42d1042000044516102080c0500c0c0b14001080b00021560290b071503400b0700380701d80500051500300c05001443d03424400719048001c070020b4480007603851441515141c0004040724048981d00848500c641c103490450100f000b11110700c41c603480030071503c0c4146205100569040e05608030400c04000070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 608990449 1250 608989199 608989207
    0x8071208070605060a05041b0e030f031c06081e19151a0402070614160207060f030b030d02030c01272303040305010605121b01050309010608010e060103020103060e0f0705 75
    0x2030b00d8a06a400083c000a00104400a00c1e490040100c0c0c400c9100180003030074000c00e1500d81d03e000101001a90b0440c000b4601d40140d00d3700c0d0b1552001406000c1190540f01c4900244110041c003135400502e0440c1c0300b51580c01c520b940000c6c01c084801c01d034900140010f009880c0464140300300a40c2d481d000103000101361042005010005600c03046c0554803d000044c202c04114283c0c0003440314a00100031000152240d0407140c500c142d000445400503405003c08014403031059681d0300ca540f40600b000201508440040b074140410b0700305050240c3d0000070140040c1609108002c410511b8202400181c08400000403c500000c0c5024200845180086140c040c100c0e0b12042480c2900088a5075955070345003841c040c0038107120b2540303e0101c0d00031400e1345040119102c401504146207810b20401d50800644240e00003418a1701d2566940d0004900044244a428043c1000000614403985144001026100b50b40c004491412852090200082c00807108941050346810620740f5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 608991699 1250 608990449 608990461
    0x150906090e12090f091806010503030703270506070b07120c0509090405011116020103141303080c0903030f090f030102131514120f100f0501200f0708071208070605 72
    0x1144c8030012040354001c0340041030040e00411052005031120b2000b06650641e0b0f038030f90425031a0300800c5006804504c644030300c9502441c2c01c103d482420401c010100e80a9501d03800810140e070404801140c001120000b48040650010002c1000c1e0000102c1484105155100144940900104d040c058030108010408000007034020701e01c00e070030080c40d4640715002000c00d44040c5820708000c0c2c0c00b0a1811649050040100d625280320300d50240620a074014665000c844c0400010000180803000b44544041a54103100600c11a0100380301c0c03a4880d12110b00700010740c120903624600c2603204101c8041d8011901c4101000c84501e40341001d0140c5030010180e07400c0c0044050116000400110208112504004240030304107600b90248665074041201e841d405090298241c0780080c4c1c4820070880d0f02c10907502000425952242180c0ca045110044c0340c4407211022004e42c1d0441d160038001100100040b01c01012005c03c1058905465201d00c1a14419000007070105520b0710700081c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 608992805 1106 608991699 608991709
    0x605010804031b02010c05100204031a0f0f1b07080301090f2021011202010219150903031407210e0c01051c150906090e1209 55
    0x62083d00300003458080c8503440d20101c1c10819004581710001700140001511103132120009070300d1390f040d49010110082c02101085100203002c08001885c008884e6480e00400d07015082807103a21744079041600c9080003070030380400d03110010700c4d8410407200d6402103048408102082040c180681d140606a030b9410b0002507a00e815015400c800320040401804000d880b0403015005590400340580301210992003440080c242801c420b05658062025004140b541e6814081c6040c0950314502e03003001140d402c0517003980c1d0344181010503002c0d50000c200c98514071f402802614120300001c000c001810b980c42c010b10316146042004120034010b50010b544100080c00c9162301c4480112541c2e0014281d415203100b040d0041035000704a032084402c2c9031840ca41d00d425550801c8205800d654080d07005418603481c0c512011895100424405c0e174416031401031507030f160400e0b40090 = true := by decide +kernel

theorem cover : BRFrame.Cov 608812949 608992805 := by
  have h0 := BRFrame.cov_init 608812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 608812949 ≤ n) (h2 : n < 608992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
